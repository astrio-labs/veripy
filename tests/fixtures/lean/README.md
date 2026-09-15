# Lean regression input

`is_prime_sqrt.py` and its Lean sidecar preserve the square-root trial-division
regression from upstream revision `db953b2aca22d88de4446618063c47dfb2ade165`,
originally under `benchmark/tasks/is_prime/`. They exercise the compiler's strict
loop matcher and checked proof completion. This is a test fixture, not an
additional case study or a restored benchmark harness.
