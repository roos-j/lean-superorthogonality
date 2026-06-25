/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import LeanSuperorthogonality.Defs

import LeanSuperorthogonality.Codex.MainTheorem

-- import LeanSuperorthogonality.Codex.PointwiseEstimate

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set Complex
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

variable {r : ℕ}

open Codex (sqfct_estimate_of_type_iv_superorthogonal_finite) in
/-- Theorem 1 of arXiv:2212.08956 for the special case of finite index sets. -/
theorem sqfct_estimate_of_type_iv_superorthogonal_finite [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  :=
  Codex.sqfct_estimate_of_type_iv_superorthogonal_finite μ hr hf hsq

end Superorthogonal

end
