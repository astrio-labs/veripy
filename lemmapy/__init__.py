"""LemmaPy: verify a typed Python fragment.

**The embedding surface is `lemmapy.api`** — one import path, deliberately:

    from lemmapy import api
    api.verify(path, workdir)

The package root does NOT re-export those functions, and that is a
decision rather than an omission. `lemmapy.repair` is already a submodule,
so a root-level `repair` function would be silently replaced by the module
the moment anything imported it — `lemmapy.repair(...)` would be a
function or a module depending on import ORDER, which is the worst kind of
API. Exporting some names but not the colliding one would be worse still:
a host cannot be expected to remember which is which.

Everything outside `lemmapy.api` is internal and may be reshaped without
notice. Payload shapes and the failure vocabulary live in
docs/AGENT-INTERFACE.md, versioned by `api.toolchain_info()`.
"""
