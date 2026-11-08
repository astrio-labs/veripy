"""Effect lowering is generic and preserves borrowed writes on failing paths."""

import json
from dataclasses import dataclass, field
from pathlib import Path

import pytest

from veripy.backends.dafny.driver import verify_dafny_file
from veripy.backends.dafny.encoder import EncodeError
from veripy.backends.dafny.native_heap import DafnyHeapBackend
from veripy.frontend.extract import parse_source

SCHEMA = {
    "types": {
        "Entry": {"fields": {"seen": "bool", "count": "int", "events": "list[str]"}}
    }
}


def source(body, *, name="admit", schema=SCHEMA):
    return (
        "# heap-schema: "
        + json.dumps(schema)
        + f"\n#@ verified\ndef {name}(retained: dict[str, Entry], shard: dict[str, Entry]) -> None:\n"
        + body
    )


def encode(text):
    return DafnyHeapBackend().encode(
        text, parse_source(text), module_name="fresh_example", proof_lemmas=[]
    )


def prove(text, tmp_path):
    result = encode(text)
    path = tmp_path / "heap.dfy"
    path.write_text(result.dafny_source)
    return verify_dafny_file(path, result.line_map)


@pytest.mark.requires_prover("dafny")
def test_fresh_noncandidate_validate_then_accumulate(tmp_path):
    text = source(
        """    pending: dict[str, Entry] = {}
    entries: list[tuple[Entry, Entry]] = []
    for key, value in shard.items():
        if key not in retained:
            pending[key] = value
            continue
        prior = retained[key]
        assert prior.count == value.count
        entries.append((prior, value))
    retained.update(pending)
    for prior, value in entries:
        prior.seen |= value.seen
        prior.events.extend(value.events)
""",
        name="combine_telemetry",
    )

    # This is also executable Python with a fresh passive model, not only an
    # effect fixture whose unresolved annotation names never run.
    @dataclass
    class Entry:
        seen: bool = False
        count: int = 0
        events: list[str] = field(default_factory=list)

    namespace = {"Entry": Entry}
    exec(compile(text, str(tmp_path / "combine.py"), "exec"), namespace)
    original = Entry(events=["prior"])
    incoming = Entry(seen=True, events=["next"])
    retained, shard = {"existing": original}, {"existing": incoming, "new": Entry()}
    namespace["combine_telemetry"](retained, shard)
    assert retained["existing"] is original and retained["new"] is shard["new"]
    assert original.seen and original.events == ["prior", "next"]
    assert incoming.events == ["next"]

    result = prove(text, tmp_path)
    assert result.ok, result.raw
    assert "1 verified, 0 errors" in result.raw
    assert encode(text).dafny_source == encode(text).dafny_source


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "write",
    [
        "prior.seen = value.seen",
        "prior.seen |= value.seen",
        "value.seen |= prior.seen",
        "alias = prior\n        alias.events.extend(value.events)",
        "wrapper = [prior]\n        wrapper[0].events.extend(value.events)",
        "pending: dict[str, Entry] = {}\n        retained.update(pending)",
    ],
)
def test_borrowed_write_before_later_rejection_fails_proof(write, tmp_path):
    # Updating even an abstract empty map emits a conservative write event.
    body = (
        "    for key, value in shard.items():\n        prior = retained[key]\n        "
        + write
        + "\n        assert prior.count == value.count\n"
    )
    result = prove(source(body), tmp_path)
    assert not result.ok
    assert result.error is None
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "body",
    [
        """    pending: dict[str, Entry] = {}
    for key, value in shard.items():
        if key not in shard:
            pending[key] = value
    retained.update(pending)
""",
        """    pending: dict[str, Entry] = {}
    for key, value in shard.items():
        if key not in retained:
            key: str = "occupied"
            pending[key] = value
    retained.update(pending)
""",
        """    pending: dict[str, Entry] = {}
    pending.update(shard)
    retained.update(pending)
""",
        """    pending: dict[str, Entry] = {}
    wrapper = [pending]
    for key, value in shard.items():
        pending[key] = value
    retained.update(wrapper[0])
""",
        """    local: list[str] = []
    alias = local
    for key, value in shard.items():
        alias.extend(local)
        alias = value.events
    assert False
""",
    ],
)
def test_capabilities_and_loop_aliases_are_conservative(body, tmp_path):
    result = prove(source(body), tmp_path)
    assert not result.ok and result.error is None, result.raw


@pytest.mark.parametrize(
    "body",
    [
        "    callback(retained)\n",
        "    [value.events.clear() for value in shard.values()]\n",
        "    try:\n        assert False\n    except AssertionError:\n        retained.update(shard)\n",
        "    for key, value in shard.items():\n        value.count |= value.count\n",
    ],
)
def test_unknown_effects_and_nonboolean_or_fail_closed(body):
    with pytest.raises(EncodeError):
        encode(source(body))


def test_no_contract_or_empty_target_is_not_verification():
    with pytest.raises(EncodeError):
        encode("#@ verified\ndef f() -> None:\n    pass\n")
    with pytest.raises(ValueError, match="nonempty"):
        encode(
            "# heap-schema: " + json.dumps(SCHEMA) + "\ndef f() -> None:\n    pass\n"
        )


@pytest.mark.parametrize(
    "shadow",
    [
        "def zip(): pass\n",
        "from other import zip\n",
        "import other as zip\n",
        "zip = 1\n",
    ],
)
def test_builtin_zip_shadowing_fails_closed(shadow):
    with pytest.raises(EncodeError, match="shadows builtin zip"):
        encode(shadow + source("    pass\n"))


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "body",
    [
        "    raise AssertionError() from retained.update(shard)\n",
        "    assert False, f\"{0:{retained.update(shard) or ''}}\"\n",
    ],
)
def test_exception_causes_and_nested_format_specs_preserve_hidden_writes(
    body, tmp_path
):
    result = prove(source(body), tmp_path)
    assert not result.ok and result.error is None, result.raw
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "insertion", ["wrapper.append(retained)", "wrapper.extend([retained])"]
)
def test_borrowed_container_insertions_update_local_wrapper_provenance(
    insertion, tmp_path
):
    text = source(
        "    pending: dict[str, Entry] = {}\n    wrapper = [pending]\n    "
        + insertion
        + "\n    for alias in wrapper:\n        alias.update(shard)\n    assert False\n"
    )
    result = prove(text, tmp_path)
    assert not result.ok and result.error is None, result.raw
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


OPTIONAL_SCHEMA = {
    "types": {
        "Entry": {
            "fields": {
                "count": "int",
                "events": "list[str]",
                "candidate": "Entry | None",
            }
        }
    }
}


@dataclass
class OptionalEntry:
    count: int = 0
    events: list[str] = field(default_factory=list)
    candidate: "OptionalEntry | None" = None


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "read,error",
    [
        # Reading a field through an optional receiver raises AttributeError.
        ("label = value.candidate.count", AttributeError),
        # Any format specification can raise for the formatted primitive.
        ('label = f"{value.count:bad}"', ValueError),
    ],
)
def test_failing_reads_after_borrowed_writes_fail_proof(read, error, tmp_path):
    text = source(
        '    for key, value in shard.items():\n        value.events.append("changed")\n        '
        + read
        + "\n",
        schema=OPTIONAL_SCHEMA,
    )
    namespace = {"Entry": OptionalEntry}
    exec(compile(text, str(tmp_path / "late_read.py"), "exec"), namespace)
    changed = OptionalEntry()
    with pytest.raises(error):
        namespace["admit"]({}, {"one": changed})
    assert changed.events == ["changed"]
    result = prove(text, tmp_path)
    assert not result.ok and result.error is None, result.raw
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "read",
    ["label = value.candidate.count", 'label = f"{value.count}"'],
)
def test_nonfailing_reads_after_borrowed_writes_still_prove(read, tmp_path):
    schema = json.loads(
        json.dumps(OPTIONAL_SCHEMA).replace('"Entry | None"', '"Entry"')
    )
    text = source(
        '    for key, value in shard.items():\n        value.events.append("changed")\n        '
        + read
        + "\n",
        schema=schema,
    )
    result = prove(text, tmp_path)
    assert result.ok, result.raw


def test_opaque_metadata_formatting_does_not_assume_python_callbacks_pure():
    schema = {"types": {"Entry": {"fields": {"metadata": "opaque"}}}}
    with pytest.raises(EncodeError, match="formatting requires exact primitive"):
        encode(
            source(
                '    for key, value in shard.items():\n        assert False, f"{value.metadata}"\n',
                schema=schema,
            )
        )


def test_wildcard_import_cannot_hide_builtin_replacement():
    with pytest.raises(EncodeError, match="wildcard import"):
        encode("from unknown import *\n" + source("    pass\n"))


@pytest.mark.requires_prover("dafny")
def test_strict_zip_iteration_failure_occurs_after_prior_writes(tmp_path):
    text = source("""    for key, value in zip(retained.keys(), shard.values(), strict=True):
        value.seen |= True
""")

    # Native Python writes one borrowed entry before the unequal zip rejects.
    @dataclass
    class Entry:
        seen: bool = False
        count: int = 0
        events: list[str] = field(default_factory=list)

    namespace = {"Entry": Entry}
    exec(compile(text, str(tmp_path / "zip.py"), "exec"), namespace)
    changed = Entry()
    with pytest.raises(ValueError):
        namespace["admit"]({"one": Entry(), "two": Entry()}, {"one": changed})
    assert changed.seen
    result = prove(text, tmp_path)
    assert not result.ok and result.error is None, result.raw
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


@pytest.mark.requires_prover("dafny")
@pytest.mark.parametrize(
    "body",
    [
        """    for key, events in retained.items():
        retained.setdefault("inserted", []).append("seen")
""",
        """    for key, events in retained.items():
        key: str = "inserted"
        retained.setdefault(key, []).append("seen")
""",
    ],
)
def test_dictionary_iterator_invalidation_is_a_postwrite_exit(body, tmp_path):
    text = source(body).replace("dict[str, Entry]", "dict[str, list[str]]")
    namespace = {}
    exec(compile(text, str(tmp_path / "dict_iteration.py"), "exec"), namespace)
    retained = {"existing": []}
    with pytest.raises(RuntimeError):
        namespace["admit"](retained, {})
    assert "inserted" in retained
    result = prove(text, tmp_path)
    assert not result.ok and result.error is None, result.raw
    assert any("assertion" in d.message for d in result.diagnostics), result.raw


@pytest.mark.requires_prover("dafny")
def test_current_key_setdefault_does_not_invalidate_an_aliased_iterator(tmp_path):
    text = source("""    for key, events in shard.items():
        retained.setdefault(key, []).extend(events)
""").replace("dict[str, Entry]", "dict[str, list[str]]")
    namespace = {}
    exec(compile(text, str(tmp_path / "list_merge.py"), "exec"), namespace)
    retained = {"existing": ["prior"]}
    old = retained["existing"]
    namespace["admit"](retained, {"existing": ["next"], "new": ["new"]})
    assert retained == {"existing": ["prior", "next"], "new": ["new"]}
    assert retained["existing"] is old
    result = prove(text, tmp_path)
    assert result.ok, result.raw
