/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
module

public import Mathlib

/-!
Formalizing arXiv:2212.08956
-/

@[expose] public noncomputable section

namespace Superorthogonal

open MeasureTheory Nat Set

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)
variable {ι : Type*} [Countable ι]

local instance : MeasurableSpace ι := ⊤
local instance : MeasureSpace ι where
  volume := Measure.count

variable {r : ℕ}

def all_distinct (k : ℕ) (j : Fin k → ι) := ∀ i i', i ≠ i' → j i ≠ j i'

def type_iv_superorthogonal (f : ι → α → ℂ) (r : ℕ) :=
    ∀ j : Fin (2 * r) → ι, all_distinct (2 * r) j → ∫ x, ∏ i, f (j i) x ∂μ = 0

def sqfct (f : ι → α → ℂ) (x : α) := (∑' j, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹

-- (hf': MemLp (sqfct f) (2 * r) μ)

section PointwiseEstimate

private abbrev s (a : ι → ℂ) := ∑' j, a j

private abbrev set_all_distinct (k : ℕ) : Set (Fin k → ι) := fun j ↦ all_distinct k j

variable {k : ℕ}

private abbrev Q (a : Fin k → ι → ℂ) := ∑' j : Fin k → ι,
  indicator (set_all_distinct k) (fun j ↦ ∏ i, a i (j i)) j

private abbrev A (hk : 2 ≤ k) (a : Fin k → ι → ℂ) := ENNReal.ofReal <|
  (Finset.univ.image fun i ↦ ‖s (a i)‖).max' ⟨‖s (a ⟨0, zero_lt_of_lt hk⟩)‖, by simp⟩

private abbrev B (hk : 2 ≤ k) (a : Fin k → ι → ℂ) := (Finset.univ.image
  fun i ↦ eLpNorm (a i) 2).max' ⟨eLpNorm (a ⟨0, zero_lt_of_lt hk⟩) 2, by simp⟩

private theorem pointwise_estimate (hk : 2 ≤ k) (a : Fin k → ι → ℂ) (ha : ∀ i, Summable (fun j ↦ ‖a i j‖)) :
    ‖Q a - ∏ i, s (a i)‖ₑ ≤
      (((k)! - 1 : ENNReal) * (B hk a) ^ 2 * (max (A hk a) (B hk a)) ^ (k - 2)) := by
  sorry

end PointwiseEstimate

def C (r : ℕ) : ENNReal := match r with
  | 1 => 1
  | r => 2 ^ ((2: ℝ)⁻¹) * ((2 * r)! - 1) ^ ((2 : ℝ)⁻¹)

theorem sqfct_estimate_of_type_iv_superorthogonal {f : ι → α → ℂ}
    (hf : type_iv_superorthogonal μ f r) :
    eLpNorm (fun x ↦ ∑' j, f j x) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  := by
  sorry

end Superorthogonal

end
