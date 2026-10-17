/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
This file was assembled by Codex from the human-written files `Defs.lean`, `Theorems.lean`.
No comments were added by Codex.
-/
module

public import Mathlib

/-!
# Challenge file for Comparator
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set Complex SchwartzMap Function FourierTransform
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

@[inherit_doc EuclideanSpace]
scoped notation:max "ℝ^" n:max => EuclideanSpace ℝ (Fin n)

/-- Square-function associated with the family of functions `f` -/
def sqfct (f : ι → α → ℂ) (x : α) := (∑' j, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹

namespace CDW

variable [LinearOrder ι]

/-- The notion of superorthogonality from Thm. 1.1 of Cushman–Demeter–Wu, arXiv:2609.13105v1 -/
structure Superorthogonal (f : ι → α → ℂ) : Prop where
  measurable : ∀ j, Measurable (f j)
  integrable : ∀ i j k l, i < j → j < k → k < l →
    Integrable (fun x ↦ f i x * f j x * conj (f k x) * conj (f l x)) μ ∧
    Integrable (fun x ↦ f i x * f l x * conj (f j x) * conj (f k x)) μ
  superorthogonal : ∀ i j k l, i < j → j < k → k < l →
    ∫ x, f i x * f j x * conj (f k x) * conj (f l x) ∂μ = 0 ∧
    ∫ x, f i x * f l x * conj (f j x) * conj (f k x) ∂μ = 0

/-- The conic sectors from Thm. 1.4  of Cushman–Demeter–Wu, arXiv:2609.13105v1

**Implementation note:** We let `j` run from `0` to `N - 1` instead of from `1` to `N`.
-/
def conic_sector {N : ℕ} (j : Fin N) : Set ℝ^3 :=
  { ξ | ∃ r t u : ℝ, r ∈ Icc 1 2 ∧ t ∈ Icc (j / (N : ℝ)) ((j + 1) / (N : ℝ)) ∧
    |u| ≤ (N : ℝ) ^ (-2 : ℤ) ∧ ξ 0 = r ∧ ξ 1 = r * t ∧ ξ 2 = r * t ^ 2 + u }

/-- Theorem 1.1 of Cushman–Demeter–Wu, arXiv:2609.13105v1.
We give an explicit absolute constant `C = 33`. -/
theorem sqfct_estimate_of_superorthogonal {N : ℕ} {f : Fin N → α → ℂ}
    (hf : Superorthogonal μ f) (hf' : ∀ j, MemLp (f j) 4 μ) :
    eLpNorm (∑ j, f j) 4 μ ≤ ENNReal.ofReal (33 * (1 + Real.log N) ^ 2) * eLpNorm (sqfct f) 4 μ := by
  sorry

/--
Theorem 1.4 of Cushman–Demeter–Wu, arXiv:2609.13105v1.
We give an explicit absolute constant `C = 46`. -/
theorem cone_sqfct_estimate {N : ℕ} {f : Fin N → 𝓢(ℝ^3, ℂ)}
    (hf : ∀ j, support (fourier (f j)) ⊆ conic_sector j) :
    eLpNorm (∑ j, f j) 4 volume ≤
      ENNReal.ofReal (46 * (1 + Real.log N) ^ ((1 : ℝ) / 4)) *
        eLpNorm (sqfct (fun j x ↦ f j x)) 4 volume := by
  sorry

end CDW
end Superorthogonal
end
