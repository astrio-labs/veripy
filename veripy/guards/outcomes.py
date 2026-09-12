"""Explicit opt-in guards for the experimental dafny-outcomes backend.

Proof establishment remains a separate step. The original function executes
unchanged; error postconditions observe the ValueError class, then re-raise the
same exception. Configuration drift fails at the boundary.
"""
from __future__ import annotations

import ast
import functools
import hashlib
import inspect
import sys
import unicodedata

from ..frontend.records import record_schemas
from .emitter import GuardGenError, _descriptor, _reject_reserved_names
from .runtime import guard_value, copy_value, PreconditionError, PostconditionError
from ..frontend.parse import rewrite_old


def _make_guard(island, descriptors, requires, ensures, unicode_version, digit_limit, record_types=None, result_default=None):
    signature = inspect.signature(island)
    requires = tuple(compile(e, "<outcome requires>", "eval") for e in requires)
    ensures = tuple(compile(e, "<outcome ensures>", "eval") for e in ensures)

    def decimal_valid(text):
        try:
            int(text)
            return True
        except ValueError:
            return False

    @functools.wraps(island)
    def guarded(*args, **kwargs):
        if unicodedata.unidata_version != unicode_version or sys.get_int_max_str_digits() != digit_limit:
            raise PreconditionError(island.__name__, "decimal model configuration changed")
        bound = signature.bind(*args, **kwargs)
        bound.apply_defaults()
        values = {n: guard_value(v, descriptors[n], function=island.__name__, param=n, record_types=record_types)
                  for n, v in bound.arguments.items()}
        env = dict(island.__globals__)
        env.update(values)
        env.update(decimal_valid=decimal_valid, prod=__import__("math").prod, math=__import__("math"), sys=sys)
        for requirement in requires:
            try:
                ok = bool(eval(requirement, env))
            except Exception as exc:
                raise PreconditionError(island.__name__, "requires evaluation failed") from exc
            if not ok:
                raise PreconditionError(island.__name__, "requires failed")
        bound.arguments.update({n: copy_value(v, descriptors[n], record_types=record_types) for n, v in values.items()})

        def check(result, error):
            def raised(name=None):
                if name is None:return isinstance(error,BaseException)
                cls=island.__globals__.get(name, ValueError if name=="ValueError" else Exception if name=="Exception" else None)
                return cls is not None and isinstance(error,cls)
            env.update(result=result, raised=raised)
            for post in ensures:
                try:
                    ok = bool(eval(post, env))
                except Exception as exc:
                    raise PostconditionError(island.__name__, "outcome ensures evaluation failed") from exc
                if not ok:
                    raise PostconditionError(island.__name__, "outcome ensures failed")

        try:
            result = island(*bound.args, **bound.kwargs)
        except ValueError as error:
            check([] if result_default is None else result_default, error)
            raise
        check(result, False)
        return result
    return guarded


def emit_outcome_guarded(source, specs, src_name, *, check_ensures=False, proof_lemmas=frozenset()):
    from ..backends.dafny.outcomes import encode_outcomes
    # Enforce the outcome fragment, even when the optional runtime ensures
    # checks are disabled. This does not claim that the proof has passed.
    encode_outcomes(source, specs, module_name=src_name, proof_lemmas=proof_lemmas)
    module = ast.parse(source)
    _reject_reserved_names(module)
    if "# ---- VERIPY ISLAND" in source:
        raise GuardGenError("island sentinel text is reserved")
    from ..backends.dafny.environment import resolve_for_encoder
    environment = resolve_for_encoder(module)
    functions = {(n.name, n.lineno): n for n in environment.module.body if isinstance(n, ast.FunctionDef)}
    records = record_schemas(module)
    wrappers = []
    for spec in specs.functions:
        fn = functions[(spec.name, spec.lineno)]
        descriptors = {a.arg: _descriptor(a.annotation, a, records)
                       for a in (*fn.args.posonlyargs, *fn.args.args, *fn.args.kwonlyargs)}
        requirements = tuple(c.desugared for c in spec.by_kind("requires"))
        postconditions = tuple(rewrite_old(c.desugared, "{name}") for c in spec.by_kind("ensures")) if check_ensures else ()
        default = {"str": "", "int": 0, "bool": False}.get(fn.returns.id) if isinstance(fn.returns, ast.Name) else None
        wrappers.append(f"{fn.name} = _veripy_make_guard({fn.name}, {descriptors!r}, {requirements!r}, "
                        f"{postconditions!r}, {unicodedata.unidata_version!r}, {sys.get_int_max_str_digits()}, "
                        + "{" + ", ".join(f"{name!r}: {name}" for name in records) + "}" + (f", result_default={default!r}" if default is not None else "") + ")\n")
    from ..backends.dafny.environment import resolve_for_encoder
    environment = resolve_for_encoder(module)
    environment_guards = ""
    if environment.values:
        environment_guards = ("from veripy.backends.dafny.environment import guard_environment as _veripy_guard_environment\n"
                              + f"_veripy_module_values = {environment.values!r}\n"
                              + "".join(f"{spec.name} = _veripy_guard_environment({spec.name}, _veripy_module_values)\n" for spec in specs.functions))
    from ..backends.dafny.unicode_strings import guard_code
    environment_guards += guard_code(module, specs)
    from ..backends.dafny.regex_strings import guard_code as regex_guard_code
    environment_guards += regex_guard_code(module, specs)
    from ..backends.dafny.declarations import guard_code as declarations_guard_code
    environment_guards += declarations_guard_code(module, specs)
    digest = hashlib.sha256(source.rstrip("\n").encode()).hexdigest()
    return (
        "# ---- VERIPY ISLAND BEGIN (verbatim copy of the admitted source) ----\n"
        + source.rstrip("\n") + "\n# ---- VERIPY ISLAND END ----\n"
        + "from veripy.guards.outcomes import _make_guard as _veripy_make_guard\n"
        + f"_VERIPY_ISLAND_SHA256 = {digest!r}\n"
        + environment_guards + "".join(wrappers)
    )
