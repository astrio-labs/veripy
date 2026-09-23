# Understanding results

Read admission, typing, proof and execution evidence separately. Each answers a different question.

| Observation | Meaning | Next action |
| --- | --- | --- |
| Typing error | The source did not pass the CLI's typing gate | Fix or explicitly prepare the typing environment |
| Admission or encoding error | The chosen backend cannot model this program or specification | Inspect the unsupported construct and backend coverage |
| Verified / structured `ok` | Generated proof obligations were discharged | Review the contract and its modeled scope |
| Failed proof | The backend did not establish the contract | Check for a bug, missing invariant or supporting lemma |
| Timeout or tool error | Verification did not complete normally | Check installation, logs and resource limits |
| Runtime counterexample | An execution violated the checked property | Reproduce the recorded input and inspect the observation |

The structured API has detailed statuses and failure records. See the [API reference](../AGENT-INTERFACE.md) rather than treating these explanatory labels as an exhaustive schema.

## Keep the evidence

Keep generated models, logs, source hashes and environment information when you need a reproducible result. Use fresh directories for distinct compatibility runs. Avoid committing generated output to the source tree.

## Avoid overinterpreting success

A weak postcondition can be easy to prove and still miss the intended behavior. Contradictory preconditions can make a conditional guarantee vacuous. Passing finite tests does not prove a universal contract. Proof of a translated model still depends on the translation boundary.

For compatibility, the named verdicts are `proved-compatible`, `behavioral-difference`, `unsupported` and `inconclusive`. Read [compare two versions](compatibility.md) for their context.
