# Verify Python, one component at a time

VeriPy connects Python implementations to explicit contracts and checked proofs. Write annotations as `#@` comments, keep the executable Python body, and ask Dafny or Lean to verify the admitted model. When the implementation changes, a separate compatibility check can compare the two versions.

```python
#@ ensures result == x + 1
def increment(x: int) -> int:
    return x + 1
```

**New to verification?** Start with [installation](installation.md), then work through [your first proof](first-proof.md). You will prove a contract, introduce a bug, and interpret the failure.

**Adding VeriPy to an existing project?** Read [Python boundaries](boundaries.md) before selecting a component. Then follow [compare two versions](compatibility.md).

![VeriPy verification workflow](../assets/veripy-workflow.png)

## What you write

- Python type annotations describe the admitted values.
- Preconditions describe when a function may be called.
- Postconditions describe what it must return.
- Loop invariants and checked proof sidecars help establish those claims.

Developers or agents can author these annotations. Verification checks the resulting obligations, not the author's identity. Specifications still need review to establish that they express the intended requirement.

## What a proof establishes

A successful result establishes the generated theorem under its preconditions and modeled environment. VeriPy supports selected Python fragments. Its frontend translation and semantic models remain trusted software, and a component proof is not a proof of its entire repository.

CPython ignores `#@` comments. Runtime enforcement requires an explicitly generated wrapper. See [trust and guarantees](../ASSURANCE-ARGUMENT.md) and [supported fragments](../SUPPORTED-FRAGMENTS.md).

## Choose a path

| Your goal | Start with |
| --- | --- |
| Learn specifications | [Contracts and values](contracts.md) |
| Verify a loop | [Loops and invariants](loops.md) |
| Supply a supporting lemma | [Proof support](proof-support.md) |
| Check an update | [Compatibility tutorial](compatibility.md) |
| Integrate an agent | [Structured API and repair](../AGENT-INTERFACE.md) |
| Explore real projects | [Case studies](case-studies.md) |
