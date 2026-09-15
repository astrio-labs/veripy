"""Tool requirements for integration checks, without hiding pure unit tests."""
import shutil

import pytest


def pytest_collection_modifyitems(items):
    for item in items:
        requirement = item.get_closest_marker("requires_prover")
        if requirement is None:
            continue
        backends = requirement.args
        if not backends:
            callspec = getattr(item, "callspec", None)
            if callspec is None or "backend" not in callspec.params:
                raise pytest.UsageError("requires_prover needs names or a backend parameter")
            backends = (callspec.params["backend"],)
        tools = {"dafny" if str(name).startswith("dafny") else name for name in backends}
        if not tools <= {"dafny", "lean"}:
            raise pytest.UsageError(f"Unknown required prover in {item.nodeid}")
        missing = sorted(tool for tool in tools if shutil.which(tool) is None)
        if missing:
            item.add_marker(pytest.mark.skip(reason="Required prover unavailable: " + ", ".join(missing)))
