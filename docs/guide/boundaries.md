# Python boundaries

Start with a small component whose inputs, dependencies and observations you can state precisely. VeriPy does not accept arbitrary Python simply because it has type hints.

## Verified code called from ordinary Python

A proof assumes an admitted input domain and preconditions. Ordinary Python callers can violate them unless the boundary enforces them. Generate and use supported runtime guards when you need entry checks. Guards are not installed automatically at every call site.

## Verified code calling other code

Dependencies must resolve through admitted implementations or explicit semantic models. An arbitrary import, callback or native extension does not acquire a proof because the caller is verified. The dependency model belongs to the trusted environment and must match the code used in deployment.

## Mutation and identity

Python objects can share mutable state. A value-based backend model cannot silently replace those alias relationships. Admission restricts mutation and aliasing, and the specialized buffer backend requires an explicit policy.

## Exceptions and observations

The outcome backend supports selected modeled exception classes. A proof of the exception outcome does not necessarily cover its message, traceback or class-object identity. Resource exhaustion and concurrent mutation are outside the current general component guarantee.

## A practical selection process

1. Choose one function with explicit input and output types.
2. Identify its constants, helper calls, imports and mutable objects.
3. Write the required behavior and accepted input domain.
4. Check the selected backend's admission before investing in proof support.
5. Retain proof artifacts and native checks with the environment that produced them.

The [supported fragments](../SUPPORTED-FRAGMENTS.md), [semantics](../SEMANTICS.md) and [assurance argument](../ASSURANCE-ARGUMENT.md) provide the detailed boundaries.
