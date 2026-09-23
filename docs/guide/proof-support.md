# Proof support

A correct implementation may need facts that the backend cannot discover automatically. VeriPy allows checked auxiliary proofs beside the Python file.

## A Dafny lemma

Save this Python source as `identity.py`.

```python title="identity.py"
#@ ensures result == x
def identity(x: int) -> int:
    #@ proof Identity(x)
    return x
```

Create its adjacent sidecar.

```dafny title="identity.proofs.dfy"
lemma Identity(x: int)
  ensures x == x
{}
```

```sh
veripy verify identity.py --time-limit 30 --outdir build/identity
```

This lemma is deliberately trivial so you can see the file relationship. Real lemmas typically establish facts about arithmetic, sequences or recursive specifications. The proof hook does not execute in CPython.

Sidecars cannot replace the executable function or introduce unchecked assumptions. Their declarations must pass the admission policy and their obligations must verify.

## Lean support

Lean support lives in `identity.proofs.lean`, with syntax and hooks admitted by the Lean backend. Dafny lemmas cannot be copied into that file unchanged. See the [Lean reference](../LEAN.md) for the proof boundary and axiom audit.

## Working with an agent

Give the agent the intended contract, admitted source, selected backend and verifier feedback. Review changes to the contract separately from proof changes. Weakening a postcondition can make verification succeed while discarding the requirement.

The [agent interface](../AGENT-INTERFACE.md) documents structured results and proof repair. A generated proof must pass the same checks as a handwritten proof.
