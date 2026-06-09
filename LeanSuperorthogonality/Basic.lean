import Mathlib

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasureSpace α]
variable (μ : Measure α := by volume_tac)

variable {ι : Type*} [Countable ι]

variable {r : ℕ}

def all_distinct (j : Fin (2 * r) → ι) := ∀ i i', i ≠ i' → j i ≠ j i'

def type_iv_superorthogonal (f : ι → α → ℂ) (r : ℕ) :=
    ∀ j : Fin (2 * r) → ι, all_distinct j → ∫ x, ∏ i, f (j i) x ∂μ = 0

def sqfct (f : ι → α → ℂ) (x : α) := (∑' j, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹

theorem sqfct_estimate_of_type_iv_superorthogonal {f : ι → α → ℂ}
    (hf : type_iv_superorthogonal μ f r) : MemLp (sqfct f) (2 * r) μ := by
    sorry

end
