# Component semantics

This document describes source-to-model correspondence obligations for the
maintained fragments. It is an implementation-level argument, not a mechanized
compiler-correctness theorem. Backend acceptance, runtime correspondence and
specification adequacy must be assessed separately.

The [supported-fragment matrix](SUPPORTED-FRAGMENTS.md) identifies evaluated
inputs. [Architecture](ARCHITECTURE.md) describes the pipeline, and the
[assurance argument](ASSURANCE-ARGUMENT.md) defines its trust obligations.

## Values, states and observations

| Python value | Model interpretation | Boundary |
| --- | --- | --- |
| Exact `int` and `bool` | Mathematical integers and booleans | `bool` is not admitted as an arbitrary integer argument |
| Exact `str` | Sequence of characters or code points | Dafny string scopes use Unicode scalars; Lean represents Python code points including surrogates |
| Lists and fixed tuples | Value sequences and products | Owned mutation or read-only access under the admitted alias discipline |
| Optional values | Explicit absence or a value | Absence is distinct from zero, false and empty strings |
| Closed frozen records | Declared field snapshots | Stable reads and supported nested fields; no arbitrary object behavior |
| Exact `bytearray` | Mutable byte-valued array in `dafny-buffers` | Explicit disjointness or permitted argument aliasing |

A local state maps names to modeled values. Ownership and alias facts are
additional admission conditions. The value model permits mutation only where
another live alias cannot observe a different Python state. The buffer model
instead retains declared identity relationships and compares current and entry
contents. The two mutation policies are not interchangeable.

The observation boundary includes normal return values, explicitly modeled
exception classes and declared buffer observations. Object identity, traceback
identity, unmodeled exception messages, resource use, concurrency and external
side effects are not implied observations.

## Core expression and statement rules

Write `s |- e => v` for expression evaluation and `s |- statement => outcome`
for a statement. Outcomes distinguish continuation, return, loop control and
modeled errors. Error propagation and short-circuit evaluation must preserve
Python order wherever the selected backend admits the expression.

| Construct | Correspondence requirement |
| --- | --- |
| `n // d`, `n % d` | For nonzero `d`, quotient is floor division and remainder is `n - d * floor(n/d)`, including negative divisors. Dafny uses its Python-specific helpers; Lean uses `Int.fdiv` and `Int.fmod`. |
| Indexing | Negative indices add the sequence length. Access still requires an index in range, or a modeled error where supported. |
| Slicing | Normalize bounds according to Python. Unit slices clamp bounds; stepped slices are admitted only in the backend's supported forms. |
| Assignment and unpacking | Evaluate the right side before rebinding targets, preserving tuple simultaneity and target evaluation order. |
| Indexed augmented assignment | Read and check the target before the right side. This differs from ordinary assignment. |
| List construction and append | Preserve element order. Value updates model Python mutation only under the ownership rules. |
| `for` loops | Evaluate iterable/bounds at entry. Snapshot lowering requires that mutation cannot change the observed iteration. |
| `break` and `continue` | Affect the enclosing loop. A desugared `for` advances its hidden cursor on `continue`. |
| `while` | Check loop invariants at the modeled heads and exits, with a decreasing measure where required. |
| Boolean expressions and quantifiers | Preserve lazy evaluation and well-formedness. Logical folding of a generator requires totality on the evaluated domain or explicit safety obligations. |
| Sorting and search | Only registered element/key forms are admitted. Arbitrary Python callbacks and comparison methods are not modeled. |
| Walrus assignment | Preserve when the binding occurs. Hoisting across a skipped expression is invalid and rejected in unsupported positions. |
| `assert` | In the ordinary Dafny fragment, discharge an obligation that the assertion cannot fail on admitted inputs. |

Purity alone does not justify eager evaluation of a partial expression.
For example, a skipped division must not introduce a spurious Python execution
or hide a division error. Backends use restricted total forms, checked evaluation
or rejection to preserve this distinction.

## Safety and modeled exceptions

In the ordinary `dafny` fragment, partial operations generate proof obligations.
A successful proof rules out those encoded error transitions under the contract.
This statement does not extend to `dafny-outcomes` or Lean functions whose
contracts deliberately allow exceptions.

`dafny-outcomes` carries explicit exception tags through supported statements and
helper calls. Declared subclasses and admitted ordered handlers participate in
that model. `raised()` observes an exceptional outcome; `raised("ClassName")`
observes the declared class and its subclasses. Lean's imperative model uses
checked exceptional computations, including the restricted custom hierarchy
and handler forms exercised by the stdnum validation closure.

Some admitted expression shapes differ between backends. For example, restricted
`%c` formatting requires a one-character string proof in the Dafny outcome
encoding, while Lean can preserve the formatting `TypeError`. Exact messages,
causes, traceback identity and arbitrary exception handling remain outside scope.
See [Lean](LEAN.md) and [specifications](SPEC-GRAMMAR.md).

## Helper composition and dependencies

The scalar composition argument begins with a closed, acyclic graph of specified
functions. Every callee body and contract is checked. For each call, admission
validates Python parameter binding, evaluates positional and keyword expressions
in source order into temporaries, and then supplies arguments in formal order.
Earlier operands must be captured before later calls when evaluation could fail.
A caller must establish the callee precondition and may use its checked
postcondition after the call. Spec expressions do not execute arbitrary helpers.

For this restricted core, induction over a topological ordering of the call
graph reduces a caller's obligation to its checked callees and local translation.
Fresh names must avoid capture, and all implementation bodies and auxiliary
lemmas must pass before the combined proof is reported as successful. A false
callee contract cannot be accepted merely because it makes the caller easy to
prove. Call-site diagnostics identify the original source location.

The original scalar argument excluded defaults, records, mutable inputs and
cross-module linking. Current extensions require additional correspondence
obligations rather than inheriting that argument automatically.

- The resolver admits bounded module constants and explicit dependency models.
  It does not run arbitrary imported initialization to learn specifications.
- Supported immutable literal defaults and keyword-only arguments require exact
  binding and type checks. Compatibility additionally checks matching defaults.
- Read-only sequence and record helpers require stable snapshots. Returning a
  sequence conservatively invalidates caller ownership where it may alias an
  argument, preventing later mutation justified only by value semantics.
- Closed record fields and borrowed sequences cannot be mutated as if they were
  fresh local allocations. The [SGLang](../case_studies/sglang/SEMANTICS.md) and
  [PyTorch](../case_studies/pytorch/SEMANTICS.md) notes describe the selected boundaries.
- The admitted lazy `all/any(map(predicate, text))` pattern uses an explicitly
  specified local predicate with a total literal-membership body and no
  precondition. It does not permit arbitrary higher-order calls.

Bindings and dependency state must remain stable during execution. Runtime
checks cover implemented conditions but do not lock the Python import system
or prevent concurrent mutation of arbitrary external state.

## Strings and pinned Python behavior

Decimal conversion depends on the host Python Unicode tables and integer-string
conversion limit. The paired research environment is Python 3.12.2, Unicode
15.0.0 and a 4,300-digit limit. Changing these can change generated models.
The supported direct string-to-integer assignment evaluates conversion before
committing the target, including on failure. The CPython parser's contract
models its actual acceptance and field values, including signed and Unicode
conversion, rather than claiming strict ISO-time or clock-range validation.

Dafny's registered Unicode and regex models cover selected languages and
operations, not an arbitrary regex interpreter. Regex match objects do not gain
Python structural equality through the encoding. Selected prefix/suffix calls
support positional integer bounds and literal affix tuples. Positive starts
are not clamped, so an empty affix can fail beyond the string's end. Explicit
`None` bounds, keyword bounds and arbitrary tuple expressions remain unsupported
in that extension.

The percent-decoding extension models ASCII input to a closed
`urllib.parse.unquote` dependency using ASCII, US-ASCII, UTF-8 or ISO-8859-1
replacement decoding. Registered charset captures establish facts needed by
subsequent calls. Guards check implemented transitive dependency conditions.
Arbitrary codecs, custom error handlers and concurrent dependency mutation are
outside scope. The full legacy dictionary-header parser remains unresolved.

## Loops and buffer mutation

The CPython parser extension admits restricted exact unrolling of small literal
`range` loops and a separately checked first-iteration peeling pattern. In the
latter, annotations apply to the remaining loop. These are restrictions on
admitted source shapes, not arbitrary bounds on input values. Early breaks and
final cursor values remain part of the correspondence obligation.

`dafny-buffers` requires a declared alias policy for exact bytearray arguments.
`disjoint_buffers()` requires distinct arguments. An explicit permitted pair
may alias or be distinct, while other pairs remain distinct. Guards check the
original identities before mutation. Specifications observe current contents
through `buffer("name")` and entry contents through `old_buffer("name")`.
A proof under this policy is not a compatibility theorem for arbitrary shared
buffers. The historical PyPNG product boundary remains unsupported.

## Conditional preservation argument

Let `P` be an admitted component, `E(P)` its encoded model, `D` the declared
input domain and `R` the relation between their initial states. The intended
argument requires that initialization establishes `R`, each admitted transition
preserves the appropriate state/observation relation, source specifications
match the checked formulas, and the backend checks all obligations.

Under these conditions, a proof of the model's contract implies the corresponding
Python observations satisfy the source contract on `D`. A termination claim
additionally depends on the discharged termination obligations and excludes the
recorded resource and asynchronous failures. This correspondence is not proved
end to end for the implementation. A generated guard or a passing finite replay
does not by itself establish it.

Compatibility adds a relational obligation. The new version must admit every
old-domain input and preserve the selected return and exception observations.
Record products relate matching schemas by value snapshots. Buffer aliasing and
other unmodeled observations cannot be inferred from snapshot equality. See
[callable compatibility](CALLABLE-COMPATIBILITY.md).

## Evidence and remaining obligations

| Area | Maintained controls |
| --- | --- |
| Admission, source extraction and binding | [Frontend tests](../tests/frontend) |
| Arithmetic, strings, regex, evaluation order and buffers | [Fragment tests](../tests/fragments) |
| Dafny translation and proof driver | [Dafny tests](../tests/dafny) |
| Lean translation, exceptions, execution and axiom audit | [Lean tests](../tests/lean) |
| Helper, record and relational domain preservation | [Compatibility tests](../tests/compatibility) |
| Guard generation and runtime checks | [Guard tests](../tests/guards), [runtime tests](../tests/runtime) |
| Pinned component and native evidence | [Case studies](../case_studies/README.md), [evaluation](EVALUATION.md) |

These controls include rejection tests, counterexamples, finite comparisons and
backend proofs. They are not interchangeable evidence or a mechanized simulation
proof. The archived earlier scalar argument and rule catalog remain available
in the [documentation history](RESEARCH-ARCHIVES.md#documentation-history).
