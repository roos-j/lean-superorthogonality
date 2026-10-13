/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanSuperorthogonality.Defs

import LeanSuperorthogonality.Auto.MainTheorem
import LeanSuperorthogonality.Auto.PointwiseEstimate
import LeanSuperorthogonality.Auto.Theorems

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set Complex SchwartzMap Function FourierTransform
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*}
variable {r : ℕ}

namespace CDW

/-- Theorem 1.1 of Cushman–Demeter–Wu, arXiv:2609.13105v1.

**Implementation notes:** We include the vacuous case `N = 0`.
Note that both sides of the inequality are automatically members of `L^4(μ)`
under the given hypotheses so junk values are avoided when `N ≥ 1`.
We give an explicit absolute constant `C = 33`. -/
theorem sqfct_estimate_of_superorthogonal {N : ℕ} {f : Fin N → α → ℂ}
    (hf : Superorthogonal μ f) (hf' : ∀ j, MemLp (f j) 4 μ) :
    eLpNorm (∑ j, f j) 4 μ ≤ ENNReal.ofReal (33 * (1 + Real.log N) ^ 2) * eLpNorm (sqfct f) 4 μ :=
  Auto.sqfct_estimate_of_superorthogonal μ hf hf'

/--
Theorem 1.4 of Cushman–Demeter–Wu, arXiv:2609.13105v1.

**Implementation note:** We include the trivial/vacuous cases `N = 0,1`.
We give an explicit absolute constant `C = 46`. -/
theorem cone_sqfct_estimate {N : ℕ} {f : Fin N → 𝓢(ℝ^3, ℂ)}
    (hf : ∀ j, support (fourier (f j)) ⊆ conic_sector j) :
    eLpNorm (∑ j, f j) 4 volume ≤
      ENNReal.ofReal (46 * (1 + Real.log N) ^ ((1 : ℝ) / 4)) *
        eLpNorm (sqfct (fun j x ↦ f j x)) 4 volume :=
  Auto.cone_sqfct_estimate hf

end CDW

section GPRY

open GPRY

/-- Theorem 1 of arXiv:2212.08956 for the special case of finite index sets. -/
theorem sqfct_estimate_of_type_iv_superorthogonal_finite [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  :=
  Auto.sqfct_estimate_of_type_iv_superorthogonal_finite μ hr hf hsq

/-- Theorem 1 of arXiv:2212.08956 -/
theorem sqfct_estimate_of_type_iv_superorthogonal [Countable ι]
    [Fact (1 ≤ (2 * (r : ENNReal)))] (hr : 1 ≤ r)
    {f : ι → Lp ℂ (2 * r) μ} (hf : TypeIVSuperorthogonal μ (fun i ↦ f i) r)
    (hsum : ∀ᵐ x ∂μ, Summable fun j ↦ ‖f j x‖ ^ 2)
    (hsq : MemLp (sqfct <| fun i ↦ f i) (2 * r) μ) :
    Summable f ∧ ENNReal.ofReal ‖∑' j, f j‖ ≤ C r * eLpNorm (sqfct <| fun i ↦ f i) (2 * r) μ  :=
  Auto.sqfct_estimate_of_type_iv_superorthogonal μ hr hf hsum hsq

variable [Countable ι]
variable {k : ℕ}

/-- Proposition 2 from arXiv:2212.08956.
This is the key pointwise estimate used in the proof of the main theorem. -/
theorem pointwise_estimate (hk : 2 ≤ k) (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      (((k)! - 1 : ENNReal) * (B hk a) ^ 2 * (max (A hk a) (B hk a)) ^ (k - 2)) :=
  Auto.pointwise_estimate hk a ha

end GPRY

end Superorthogonal

end
