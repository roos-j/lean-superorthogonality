# Error report

Timestamped discrepancies between the formalization and its source.

No discrepancies recorded yet.

## 2026-09-11T21:25-04:00

No discrepancy. Recording one deliberate, non-mathematical departure for traceability:
Section 2 of the source defines `C(N)` as a supremum over all families over all measure
spaces satisfying (1.2). That is a proper class in Lean, so the formalization uses the
supremum over unimodular phase changes of the single family under consideration. The
bootstrap argument is unaffected, because the proof only ever applies (1.2) and (2.1) to
phase changes of the given family. No statement of Theorem 1.1 is changed by this.

## 2026-09-11T21:54-04:00

Documented change of proof route, no change of statement or constant. Section 2 of the
source applies Minkowski's integral inequality twice: after (2.6) to pass the kernel
representation (2.7) through the `L^2` norm, and on page 9 to bound
`|| |sum f_n|^2 - S^2 ||_2` by `int |K| ||V(theta)||_2 dtheta`. The pinned Mathlib has no
continuous-form Minkowski integral inequality.

Both uses are replaced by the equivalent elementary argument: Cauchy-Schwarz in `theta`
against the weight `|K|`, followed by Tonelli for nonnegative functions. Concretely, from
`|W(x)| <= int_0^1 |K| |P_N(theta)(x)| dtheta` one gets
`|W(x)|^2 <= A_N int_0^1 |K(theta)| |P_N(theta)(x)|^2 dtheta`, and swapping the order of
integration gives exactly the bound `A_N^2 M^2 ||S||_4^2` that Minkowski would give. The
constants are identical to the source's, so (2.8) and page 9 are unaffected. The planned
reusable prerequisite file `Auto/MinkowskiIntegralInequality.lean` is therefore not needed
and was never created.
