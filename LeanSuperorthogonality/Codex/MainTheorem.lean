/-
The code in namespace `Codex` was machine generated.
-/
module

public import LeanSuperorthogonality.Defs

import LeanSuperorthogonality.PointwiseEstimate

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

variable {r : ℕ}

namespace Codex

#check pointwise_estimate

protected theorem sqfct_estimate_of_type_iv_superorthogonal {f : ι → α → ℂ}
    (hf : type_iv_superorthogonal μ f r) :
    eLpNorm (fun x ↦ ∑' j, f j x) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  := by
  sorry

end Codex

end Superorthogonal

end
