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

private abbrev pointwiseFamily (f : ι → α → ℂ) (r : ℕ) (x : α) :
    Fin (2 * r) → ι → ℂ :=
  fun i j ↦ if i < r then f j x else star (f j x)

omit [MeasurableSpace α] [Countable ι] in
private lemma summable_norm_pointwiseFamily [Finite ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    ∀ i : Fin (2 * r), Summable fun j : ι ↦ ‖pointwiseFamily f r x i j‖ := by
  letI := Fintype.ofFinite ι
  intro i
  exact Summable.of_finite

omit [MeasurableSpace α] in
private lemma pointwise_estimate_conjugated [Finite ι] (f : ι → α → ℂ)
    (hr : 1 ≤ r) (x : α) :
    ‖Q (pointwiseFamily f r x) - ∏ i, s (pointwiseFamily f r x i)‖ₑ ≤
      (((2 * r)! - 1 : ENNReal) * (B (k := 2 * r) (by omega) (pointwiseFamily f r x)) ^ 2 *
        (max (A (k := 2 * r) (by omega) (pointwiseFamily f r x))
          (B (k := 2 * r) (by omega) (pointwiseFamily f r x))) ^ (2 * r - 2)) := by
  exact pointwise_estimate (k := 2 * r) (by omega) (pointwiseFamily f r x)
    (summable_norm_pointwiseFamily f r x)

omit [MeasurableSpace α] [Countable ι] in
private lemma tsum_fintype_apply [Fintype ι] (f : ι → α → ℂ) (x : α) :
    (∑' j, f j) x = ∑ j : ι, f j x := by
  simp [tsum_fintype]

omit [MeasurableSpace α] [Countable ι] in
private lemma s_pointwiseFamily_eq [Fintype ι] (f : ι → α → ℂ) (r : ℕ) (x : α)
    (i : Fin (2 * r)) :
    ‖s (pointwiseFamily f r x i)‖ = ‖(∑' j, f j) x‖ := by
  by_cases hi : i < r
  · simp [s, pointwiseFamily, hi, tsum_fintype_apply]
  · have hstar :
        (∑ j : ι, (starRingEnd ℂ) (f j x)) = (starRingEnd ℂ) (∑ j : ι, f j x) := by
      exact (map_sum (starRingEnd ℂ) (fun j : ι ↦ f j x) Finset.univ).symm
    simp [s, pointwiseFamily, hi, tsum_fintype_apply]
    rw [hstar]
    simpa using norm_star (∑ j : ι, f j x)

omit [MeasurableSpace α] [Countable ι] in
private lemma A_pointwiseFamily [Fintype ι] (f : ι → α → ℂ) (hr : 1 ≤ r) (x : α) :
    A (k := 2 * r) (by omega) (pointwiseFamily f r x) = ‖(∑' j, f j) x‖ₑ := by
  classical
  unfold A
  let T : Finset ℝ := Finset.univ.image fun i ↦ ‖s (pointwiseFamily f r x i)‖
  rw [← ofReal_norm]
  change ENNReal.ofReal (T.max' _) = ENNReal.ofReal ‖(∑' j, f j) x‖
  congr 1
  apply le_antisymm
  · rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact le_of_eq (s_pointwiseFamily_eq f r x i)
  · let i0 : Fin (2 * r) := ⟨0, by omega⟩
    calc
      ‖(∑' j, f j) x‖ = ‖s (pointwiseFamily f r x i0)‖ := by
        rw [s_pointwiseFamily_eq]
      _ ≤ T.max' _ := by
        have hmem : ‖s (pointwiseFamily f r x i0)‖ ∈ T := by
          change ‖s (pointwiseFamily f r x i0)‖ ∈
            (Finset.univ.image fun i : Fin (2 * r) ↦ ‖s (pointwiseFamily f r x i)‖)
          exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
        exact Finset.le_max' T _ hmem

omit [Countable ι] in
private lemma eLpNorm_count_two_fintype [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] (a : ι → ℂ) :
    eLpNorm a 2 (Measure.count : Measure ι) =
      ENNReal.ofReal ((∑ j : ι, ‖a j‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [lintegral_count, tsum_fintype]
  have hsum_nonneg : 0 ≤ ∑ j : ι, ‖a j‖ ^ 2 := by
    exact Finset.sum_nonneg fun j _ ↦ sq_nonneg ‖a j‖
  have hsum :
      (∑ j : ι, ‖a j‖ₑ ^ (2 : ENNReal).toReal) =
        ENNReal.ofReal (∑ j : ι, ‖a j‖ ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (a j))
        (by norm_num : 0 ≤ (2 : ENNReal).toReal)]
      congr 1
      norm_num
    · intro j hj
      exact sq_nonneg ‖a j‖
  rw [hsum]
  rw [show 1 / (2 : ENNReal).toReal = (2 : ℝ)⁻¹ by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg hsum_nonneg (by norm_num : 0 ≤ (2 : ℝ)⁻¹)]

omit [MeasurableSpace α] [Countable ι] in
private lemma sqfct_fintype [Fintype ι] (f : ι → α → ℂ) (x : α) :
    sqfct f x = ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
  simp [sqfct, tsum_fintype]

omit [MeasurableSpace α] [Countable ι] in
private lemma B_pointwiseFamily [Fintype ι] (f : ι → α → ℂ) (hr : 1 ≤ r) (x : α) :
    B (k := 2 * r) (by omega) (pointwiseFamily f r x) = ENNReal.ofReal (sqfct f x) := by
  letI : MeasurableSpace ι := ⊤
  letI : MeasureSpace ι := { volume := Measure.count }
  haveI : MeasurableSingletonClass ι := ⟨fun _ ↦ trivial⟩
  unfold B
  rw [sqfct_fintype]
  let T : Finset ENNReal :=
    Finset.univ.image fun i ↦ eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι)
  have hcoord (i : Fin (2 * r)) :
      eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι) =
        ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹) := by
    by_cases hi : i < r
    · have hfun : pointwiseFamily f r x i = fun j : ι ↦ f j x := by
        funext j
        simp [pointwiseFamily, hi]
      rw [hfun]
      exact eLpNorm_count_two_fintype (a := fun j : ι ↦ f j x)
    · have hfun : pointwiseFamily f r x i = fun j : ι ↦ star (f j x) := by
        funext j
        simp [pointwiseFamily, hi]
      rw [hfun]
      simpa using eLpNorm_count_two_fintype (a := fun j : ι ↦ star (f j x))
  change T.max' _ = ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹)
  apply le_antisymm
  · rw [Finset.max'_le_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, _, rfl⟩
    exact le_of_eq (hcoord i)
  · let i0 : Fin (2 * r) := ⟨0, by omega⟩
    calc
      ENNReal.ofReal ((∑ j : ι, ‖f j x‖ ^ 2) ^ (2 : ℝ)⁻¹)
          = eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) := by
        rw [hcoord]
      _ ≤ T.max' _ := by
        have hmem :
            eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) ∈ T := by
          change eLpNorm (pointwiseFamily f r x i0) 2 (Measure.count : Measure ι) ∈
            (Finset.univ.image fun i : Fin (2 * r) ↦
              eLpNorm (pointwiseFamily f r x i) 2 (Measure.count : Measure ι))
          exact Finset.mem_image.mpr ⟨i0, Finset.mem_univ i0, rfl⟩
        exact Finset.le_max' T _ hmem

omit [MeasurableSpace α] [Countable ι] in
private lemma enorm_prod_s_pointwiseFamily [Fintype ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    ‖∏ i : Fin (2 * r), s (pointwiseFamily f r x i)‖ₑ =
      ‖(∑' j, f j) x‖ₑ ^ (2 * r) := by
  rw [← ofReal_norm, norm_prod]
  have hprod :
      (∏ i : Fin (2 * r), ‖s (pointwiseFamily f r x i)‖) =
        ‖(∑' j, f j) x‖ ^ (2 * r) := by
    simp_rw [s_pointwiseFamily_eq f r x]
    simp
  rw [hprod, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

omit [MeasurableSpace α] [Countable ι] in
private lemma s_pointwiseFamily_eq_ite [Fintype ι] (f : ι → α → ℂ) (r : ℕ) (x : α)
    (i : Fin (2 * r)) :
    s (pointwiseFamily f r x i) =
      if i < r then (∑' j, f j) x else star ((∑' j, f j) x) := by
  by_cases hi : i < r
  · simp [s, pointwiseFamily, hi, tsum_fintype_apply]
  · have hstar :
        (∑ j : ι, (starRingEnd ℂ) (f j x)) = (starRingEnd ℂ) (∑ j : ι, f j x) := by
      exact (map_sum (starRingEnd ℂ) (fun j : ι ↦ f j x) Finset.univ).symm
    rw [if_neg hi]
    calc
      s (pointwiseFamily f r x i) = ∑ j : ι, (starRingEnd ℂ) (f j x) := by
        simp [s, pointwiseFamily, hi, tsum_fintype]
      _ = (starRingEnd ℂ) (∑ j : ι, f j x) := hstar
      _ = star ((∑' j, f j) x) := by
        rw [tsum_fintype_apply]
        rfl

omit [MeasurableSpace α] [Countable ι] in
private lemma prod_s_pointwiseFamily_eq_ofReal_norm_pow [Fintype ι] (f : ι → α → ℂ)
    (r : ℕ) (x : α) :
    (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
      (‖(∑' j, f j) x‖ ^ (2 * r) : ℂ) := by
  let z : ℂ := (∑' j, f j) x
  have hsplit :
      (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
        (∏ n ∈ Finset.range (2 * r), if n < r then z else star z) := by
    rw [Finset.prod_fin_eq_prod_range]
    apply Finset.prod_congr rfl
    intro n hn
    have hnlt : n < 2 * r := by simpa using hn
    rw [dif_pos hnlt]
    rw [s_pointwiseFamily_eq_ite f r x ⟨n, hnlt⟩]
  rw [hsplit]
  have htwo : 2 * r = r + r := by omega
  rw [htwo, Finset.prod_range_add]
  have hleft :
      (∏ x ∈ Finset.range r, if x < r then z else star z) = z ^ r := by
    calc
      (∏ x ∈ Finset.range r, if x < r then z else star z)
          = ∏ _x ∈ Finset.range r, z := by
            apply Finset.prod_congr rfl
            intro x hx
            rw [if_pos (Finset.mem_range.mp hx)]
      _ = z ^ r := by
            rw [Finset.prod_const, Finset.card_range]
  have hright :
      (∏ x ∈ Finset.range r, if r + x < r then z else star z) = (star z) ^ r := by
    calc
      (∏ x ∈ Finset.range r, if r + x < r then z else star z)
          = ∏ _x ∈ Finset.range r, star z := by
            apply Finset.prod_congr rfl
            intro x hx
            have hnot : ¬ r + x < r := Nat.not_lt_of_ge (Nat.le_add_right r x)
            rw [if_neg hnot]
      _ = (star z) ^ r := by
            rw [Finset.prod_const, Finset.card_range]
  rw [hleft, hright, ← mul_pow]
  rw [show z * star z = ((‖z‖ : ℝ) : ℂ) ^ 2 by simpa using Complex.mul_conj' z]
  rw [← pow_mul]
  rw [htwo]

omit [MeasurableSpace α] in
private lemma pointwise_bound_sqfct [Finite ι] (f : ι → α → ℂ)
    (hr : 1 ≤ r) (x : α) :
    ‖Q (pointwiseFamily f r x) - ∏ i, s (pointwiseFamily f r x i)‖ₑ ≤
      (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) := by
  letI := Fintype.ofFinite ι
  simpa [A_pointwiseFamily f hr x, B_pointwiseFamily f hr x] using
    pointwise_estimate_conjugated f hr x

omit [MeasurableSpace α] [Countable ι] in
private lemma Q_pointwiseFamily_eq_finsum [Fintype ι] (f : ι → α → ℂ) (r : ℕ) (x : α) :
    Q (pointwiseFamily f r x) =
      ∑ j : Fin (2 * r) → ι,
        indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j := by
  classical
  rw [Q, tsum_fintype]

omit [Countable ι] in
private lemma integrable_Q_summand {f : ι → α → ℂ} (hf : TypeIVSuperorthogonal μ f r)
    (j : Fin (2 * r) → ι) :
    Integrable (fun x ↦ indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j) μ := by
  classical
  by_cases hdist : j ∈ set_all_distinct (2 * r)
  · simpa [Set.indicator, hdist, set_all_distinct] using hf.integrable_cprod j hdist
  · simp [hdist]

omit [Countable ι] in
private lemma integral_Q_pointwiseFamily_eq_zero [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    ∫ x, Q (pointwiseFamily f r x) ∂μ = 0 := by
  classical
  letI := Fintype.ofFinite ι
  have hfun :
      (fun x ↦ Q (pointwiseFamily f r x)) =
        fun x ↦ ∑ j : Fin (2 * r) → ι,
          indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j := by
    funext x
    exact Q_pointwiseFamily_eq_finsum f r x
  rw [show (∫ x, Q (pointwiseFamily f r x) ∂μ) =
      ∫ x, (∑ j : Fin (2 * r) → ι,
          indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j) ∂μ by rw [hfun]]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_eq_zero
    intro j hj
    by_cases hdist : j ∈ set_all_distinct (2 * r)
    · simpa [Set.indicator, hdist, set_all_distinct] using hf.superorthogonal j hdist
    · simp [hdist]
  · intro j hj
    exact integrable_Q_summand (μ := μ) hf j

omit [Countable ι] in
private lemma integrable_Q_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    Integrable (fun x ↦ Q (pointwiseFamily f r x)) μ := by
  classical
  letI := Fintype.ofFinite ι
  rw [show (fun x ↦ Q (pointwiseFamily f r x)) =
      fun x ↦ ∑ j : Fin (2 * r) → ι,
        indicator (set_all_distinct (2 * r)) (fun j ↦ cprod f j x) j by
    funext x
    exact Q_pointwiseFamily_eq_finsum f r x]
  exact integrable_finsetSum Finset.univ fun j _ ↦ integrable_Q_summand (μ := μ) hf j

omit [MeasurableSpace α] [Countable ι] in
private lemma sqfct_nonneg [Fintype ι] (f : ι → α → ℂ) (x : α) :
    0 ≤ sqfct f x := by
  rw [sqfct_fintype]
  positivity

omit [MeasurableSpace α] [Countable ι] in
private lemma norm_le_sqfct [Fintype ι] (f : ι → α → ℂ) (j : ι) (x : α) :
    ‖f j x‖ ≤ sqfct f x := by
  rw [sqfct_fintype]
  have hsum_nonneg : 0 ≤ ∑ k : ι, ‖f k x‖ ^ 2 := by
    exact Finset.sum_nonneg fun k _ ↦ sq_nonneg ‖f k x‖
  rw [show (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ by rfl]
  rw [Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hsum_nonneg (by norm_num : (0 : ℝ) < 2)]
  simpa using Finset.single_le_sum (fun k _ ↦ sq_nonneg ‖f k x‖) (Finset.mem_univ j)

omit [Countable ι] in
private lemma aestronglyMeasurable_tsum_finite [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) :
    AEStronglyMeasurable (∑' j, f j) μ := by
  letI := Fintype.ofFinite ι
  rw [show (∑' j, f j) = ∑ j : ι, f j by
    funext x
    simpa only [Finset.sum_apply] using tsum_fintype_apply f x]
  exact Finset.aestronglyMeasurable_sum _ fun j _ ↦ (hf.measurable j).aestronglyMeasurable

omit [Countable ι] in
private lemma memLp_component_of_sqfct [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) (j : ι) :
    MemLp (f j) (2 * r) μ := by
  letI := Fintype.ofFinite ι
  exact hsq.of_le (hf.measurable j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ by
      simpa [Real.norm_of_nonneg (sqfct_nonneg f x)] using norm_le_sqfct f j x)

omit [Countable ι] in
private lemma memLp_tsum_of_sqfct [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    MemLp (∑' j, f j) (2 * r) μ := by
  letI := Fintype.ofFinite ι
  rw [show (∑' j, f j) = ∑ j : ι, f j by
    funext x
    simpa only [Finset.sum_apply] using tsum_fintype_apply f x]
  exact memLp_finsetSum' Finset.univ fun j _ ↦ memLp_component_of_sqfct (μ := μ) hf hsq j

omit [Countable ι] in
private lemma integrable_prod_s_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    Integrable (fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) μ := by
  letI := Fintype.ofFinite ι
  rw [show (fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) =
      fun x ↦ (‖(∑' j, f j) x‖ ^ (2 * r) : ℂ) by
    funext x
    exact prod_s_pointwiseFamily_eq_ofReal_norm_pow f r x]
  have hF : MemLp (∑' j, f j) (↑(2 * r) : ENNReal) μ := by
    simpa [Nat.cast_mul] using memLp_tsum_of_sqfct (μ := μ) hf hsq
  simpa [Complex.ofReal_pow] using
    Integrable.ofReal (𝕜 := ℂ) (hF.integrable_norm_pow (by omega : 2 * r ≠ 0))

omit [Countable ι] in
private lemma enorm_integral_prod_s_pointwiseFamily [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    ‖∫ x, (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) ∂μ‖ₑ =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  let F : α → ℂ := ∑' j, f j
  have hF : MemLp F (↑(2 * r) : ENNReal) μ := by
    simpa [F, Nat.cast_mul] using memLp_tsum_of_sqfct (μ := μ) hf hsq
  have hpow_int : Integrable (fun x ↦ ‖F x‖ ^ (2 * r)) μ :=
    hF.integrable_norm_pow (by omega : 2 * r ≠ 0)
  have hpow_nonneg : 0 ≤ᵐ[μ] fun x ↦ ‖F x‖ ^ (2 * r) :=
    Filter.Eventually.of_forall fun x ↦ pow_nonneg (norm_nonneg _) _
  calc
    ‖∫ x, (∏ i : Fin (2 * r), s (pointwiseFamily f r x i)) ∂μ‖ₑ
        = ‖∫ x, ((‖F x‖ : ℂ) ^ (2 * r)) ∂μ‖ₑ := by
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            simpa [F, tsum_fintype_apply] using prod_s_pointwiseFamily_eq_ofReal_norm_pow f r x
    _ = ‖((∫ x, ‖F x‖ ^ (2 * r) ∂μ : ℝ) : ℂ)‖ₑ := by
          congr 1
          rw [show (∫ x, ((‖F x‖ : ℂ) ^ (2 * r)) ∂μ) =
              ∫ x, ((‖F x‖ ^ (2 * r) : ℝ) : ℂ) ∂μ by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              simp [Complex.ofReal_pow]]
          rw [integral_complex_ofReal]
    _ = ENNReal.ofReal (∫ x, ‖F x‖ ^ (2 * r) ∂μ) := by
          rw [← ofReal_norm]
          rw [Complex.norm_of_nonneg (MeasureTheory.integral_nonneg fun x ↦
            pow_nonneg (norm_nonneg (F x)) _)]
    _ = ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ (2 * r)) ∂μ := by
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hpow_int hpow_nonneg
    _ = ∫⁻ x, ‖F x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            calc
              ENNReal.ofReal (‖F x‖ ^ (2 * r)) = ENNReal.ofReal ‖F x‖ ^ (2 * r) := by
                rw [ENNReal.ofReal_pow (norm_nonneg _)]
              _ = ‖F x‖ₑ ^ (2 * r) := by
                rw [ofReal_norm]
              _ = ‖F x‖ₑ ^ ((2 * r : ℕ) : ℝ) := by
                rw [ENNReal.rpow_natCast]

private lemma lintegral_sum_norm_pow_le_pointwise_bound [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ) ≤
      ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ := by
  letI := Fintype.ofFinite ι
  let P : α → ℂ := fun x ↦ ∏ i : Fin (2 * r), s (pointwiseFamily f r x i)
  let R : α → ℂ := fun x ↦ Q (pointwiseFamily f r x)
  have hRint : Integrable R μ := by
    simpa [R] using integrable_Q_pointwiseFamily (μ := μ) (r := r) hf
  have hPint : Integrable P μ := by
    simpa [P] using integrable_prod_s_pointwiseFamily (μ := μ) (r := r) hr hf hsq
  have hRzero : ∫ x, R x ∂μ = 0 := by
    simpa [R] using integral_Q_pointwiseFamily_eq_zero (μ := μ) (r := r) hf
  have hdiff : ∫ x, R x - P x ∂μ = - ∫ x, P x ∂μ := by
    rw [integral_sub hRint hPint, hRzero, zero_sub]
  calc
    (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ)
        = ‖∫ x, P x ∂μ‖ₑ := by
          rw [enorm_integral_prod_s_pointwiseFamily (μ := μ) (r := r) hr hf hsq]
    _ = ‖∫ x, R x - P x ∂μ‖ₑ := by
          rw [hdiff]
          simp
    _ ≤ ∫⁻ x, ‖R x - P x‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm (fun x ↦ R x - P x)
    _ ≤ ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ := by
          apply lintegral_mono
          intro x
          simpa [R, P] using pointwise_bound_sqfct f hr x

private lemma eLpNorm_tsum_pow_eq_lintegral [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  have hcast : (2 * r : ENNReal) = ((2 * r : NNReal) : ENNReal) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  simpa [Nat.cast_mul] using
    eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := (∑' j, f j)) (p := (2 * r : NNReal))
      (by exact_mod_cast (by omega : 2 * r ≠ 0))

private lemma eLpNorm_sqfct_pow_eq_lintegral [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) :
    eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) ∂μ := by
  letI := Fintype.ofFinite ι
  have hcast : (2 * r : ENNReal) = ((2 * r : NNReal) : ENNReal) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  calc
    eLpNorm (sqfct f) ↑(2 * (r : NNReal)) μ ^ ((2 * r : ℕ) : ℝ)
        = ∫⁻ x, ‖sqfct f x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          simpa [Nat.cast_mul] using
            eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := sqfct f) (p := (2 * r : NNReal))
              (by exact_mod_cast (by omega : 2 * r ≠ 0))
    _ = ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            have hbase : ‖sqfct f x‖ₑ = ENNReal.ofReal (sqfct f x) := by
              rw [← ofReal_norm, Real.norm_of_nonneg (sqfct_nonneg f x)]
            change ‖sqfct f x‖ₑ ^ ((2 * r : ℕ) : ℝ) =
              (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ)
            rw [hbase]

private lemma eLpNorm_tsum_pow_eq_lintegral_nat [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ := by
  rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) hr hf hsq]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) =
      ‖(∑' j, f j) x‖ₑ ^ (2 * r)
    exact ENNReal.rpow_natCast _ (2 * r)

private lemma eLpNorm_sqfct_pow_eq_lintegral_nat [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) :
    eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) =
      ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ := by
  rw [eLpNorm_sqfct_pow_eq_lintegral (μ := μ) (f := f) hr]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change (ENNReal.ofReal (sqfct f x)) ^ ((2 * r : ℕ) : ℝ) =
      (ENNReal.ofReal (sqfct f x)) ^ (2 * r)
    exact ENNReal.rpow_natCast _ (2 * r)

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_sq_mul_max_pow_le (hr : 1 ≤ r) (a b K : ENNReal) :
    K * b ^ 2 * (max a b) ^ (2 * r - 2) ≤
      K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
  by_cases h : a ≤ b
  · rw [max_eq_right h]
    calc
      K * b ^ 2 * b ^ (2 * r - 2) = K * b ^ (2 * r) := by
        rw [mul_assoc, ← pow_add]
        congr 2
        omega
      _ ≤ K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
        gcongr
        exact (le_self_add : b ^ (2 * r) ≤ b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2))
  · have hbale : b ≤ a := le_of_not_ge h
    rw [max_eq_left hbale]
    calc
      K * b ^ 2 * a ^ (2 * r - 2) = K * (b ^ 2 * a ^ (2 * r - 2)) := by
        rw [mul_assoc]
      _ ≤ K * (b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2)) := by
        gcongr
        exact (le_add_self : b ^ 2 * a ^ (2 * r - 2) ≤
          b ^ (2 * r) + b ^ 2 * a ^ (2 * r - 2))

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_pow_two_mul_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ (2 * r)) ^ (1 / (r : ℝ)) = x ^ 2 := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 / (r : ℝ)) = 2 by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    rw [Nat.cast_mul]
    field_simp [hr0]
    norm_num]
  exact ENNReal.rpow_natCast x 2

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_pow_two_mul_one_sub_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ (2 * r)) ^ (1 - 1 / (r : ℝ)) = x ^ (2 * r - 2) := by
  rw [← ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 - 1 / (r : ℝ)) = ((2 * r - 2 : ℕ) : ℝ) by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hcast : ((2 * r - 2 : ℕ) : ℝ) = (2 : ℝ) * r - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r)]
      norm_num [Nat.cast_mul]
    rw [hcast]
    rw [Nat.cast_mul]
    field_simp [hr0]
    ring]
  exact ENNReal.rpow_natCast x (2 * r - 2)

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_rpow_two_mul_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ ((2 * r : ℕ) : ℝ)) ^ (1 / (r : ℝ)) = x ^ 2 := by
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 / (r : ℝ)) = 2 by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    rw [Nat.cast_mul]
    field_simp [hr0]
    norm_num]
  exact ENNReal.rpow_natCast x 2

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_rpow_two_mul_one_sub_inv (hr : 1 ≤ r) (x : ENNReal) :
    (x ^ ((2 * r : ℕ) : ℝ)) ^ (1 - 1 / (r : ℝ)) = x ^ (2 * r - 2) := by
  rw [← ENNReal.rpow_mul]
  rw [show ((2 * r : ℕ) : ℝ) * (1 - 1 / (r : ℝ)) = ((2 * r - 2 : ℕ) : ℝ) by
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
    have hcast : ((2 * r - 2 : ℕ) : ℝ) = (2 : ℝ) * r - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * r)]
      norm_num [Nat.cast_mul]
    rw [hcast]
    rw [Nat.cast_mul]
    field_simp [hr0]
    ring]
  exact ENNReal.rpow_natCast x (2 * r - 2)

private lemma lintegral_pointwise_bound_le_split [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ) ≤
      ((2 * r)! - 1 : ENNReal) *
        ((∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) +
          ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
            ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) := by
  letI := Fintype.ofFinite ι
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  let S : α → ENNReal := fun x ↦ ENNReal.ofReal (sqfct f x)
  let A : α → ENNReal := fun x ↦ ‖(∑' j, f j) x‖ₑ
  have hSae : AEMeasurable S μ := hsq.aemeasurable.ennreal_ofReal
  have hAae : AEMeasurable A μ :=
    (aestronglyMeasurable_tsum_finite (μ := μ) hf).aemeasurable.enorm
  have hsplit_ae :
      AEMeasurable (fun x ↦ S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2)) μ :=
    (hSae.pow_const (2 * r)).add ((hSae.pow_const 2).mul (hAae.pow_const (2 * r - 2)))
  calc
    (∫⁻ x, K * S x ^ 2 * (max (A x) (S x)) ^ (2 * r - 2) ∂μ)
        ≤ ∫⁻ x, K * (S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2)) ∂μ := by
          apply lintegral_mono
          intro x
          exact ennreal_sq_mul_max_pow_le hr (A x) (S x) K
    _ = K * ∫⁻ x, S x ^ (2 * r) + S x ^ 2 * A x ^ (2 * r - 2) ∂μ := by
          rw [lintegral_const_mul'' K hsplit_ae]
    _ = K * ((∫⁻ x, S x ^ (2 * r) ∂μ) +
          ∫⁻ x, S x ^ 2 * A x ^ (2 * r - 2) ∂μ) := by
          rw [lintegral_add_left' (hSae.pow_const (2 * r))]

private lemma lintegral_mixed_le_lintegral_powers [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) ≤
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
        (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) := by
  letI := Fintype.ofFinite ι
  let S : α → ENNReal := fun x ↦ ENNReal.ofReal (sqfct f x)
  let A : α → ENNReal := fun x ↦ ‖(∑' j, f j) x‖ₑ
  have hSae : AEMeasurable S μ := hsq.aemeasurable.ennreal_ofReal
  have hAae : AEMeasurable A μ :=
    (aestronglyMeasurable_tsum_finite (μ := μ) hf).aemeasurable.enorm
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hp : 0 ≤ 1 / (r : ℝ) := by positivity
  have hq : 0 ≤ 1 - 1 / (r : ℝ) := by
    have hinvle : 1 / (r : ℝ) ≤ 1 := by
      simpa [one_div] using (inv_le_one_of_one_le₀ hrR)
    linarith
  have hpq : 1 / (r : ℝ) + (1 - 1 / (r : ℝ)) = 1 := by ring
  have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
    (f := fun x ↦ S x ^ (2 * r)) (g := fun x ↦ A x ^ (2 * r))
    (hSae.pow_const (2 * r)) (hAae.pow_const (2 * r)) hp hq hpq
  calc
    (∫⁻ x, S x ^ 2 * A x ^ (2 * r - 2) ∂μ)
        = ∫⁻ x, (S x ^ (2 * r)) ^ (1 / (r : ℝ)) *
            (A x ^ (2 * r)) ^ (1 - 1 / (r : ℝ)) ∂μ := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change S x ^ 2 * A x ^ (2 * r - 2) =
              (S x ^ (2 * r)) ^ (1 / (r : ℝ)) *
                (A x ^ (2 * r)) ^ (1 - 1 / (r : ℝ))
            rw [ennreal_pow_two_mul_inv hr (S x), ennreal_pow_two_mul_one_sub_inv hr (A x)]
    _ ≤ (∫⁻ x, S x ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
        (∫⁻ x, A x ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) := hholder

private lemma eLpNorm_tsum_power_le [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) ≤
      ((2 * r)! - 1 : ENNReal) *
        (eLpNorm (sqfct f) (2 * r) μ ^ ((2 * r : ℕ) : ℝ) +
          eLpNorm (sqfct f) (2 * r) μ ^ 2 *
            eLpNorm (∑' j, f j) (2 * r) μ ^ (2 * r - 2)) := by
  letI := Fintype.ofFinite ι
  let N : ENNReal := eLpNorm (∑' j, f j) (2 * r) μ
  let M : ENNReal := eLpNorm (sqfct f) (2 * r) μ
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  have hmixed :
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) ≤
      M ^ 2 * N ^ (2 * r - 2) := by
    calc
      (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
        ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ)
          ≤ (∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) ^ (1 / (r : ℝ)) *
              (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ (2 * r) ∂μ) ^ (1 - 1 / (r : ℝ)) :=
            lintegral_mixed_le_lintegral_powers (μ := μ) hr hf hsq
      _ = (M ^ ((2 * r : ℕ) : ℝ)) ^ (1 / (r : ℝ)) *
            (N ^ ((2 * r : ℕ) : ℝ)) ^ (1 - 1 / (r : ℝ)) := by
            rw [← eLpNorm_sqfct_pow_eq_lintegral_nat (μ := μ) (f := f) hr]
            rw [← eLpNorm_tsum_pow_eq_lintegral_nat (μ := μ) hr hf hsq]
      _ = M ^ 2 * N ^ (2 * r - 2) := by
            rw [ennreal_rpow_two_mul_inv hr M, ennreal_rpow_two_mul_one_sub_inv hr N]
  calc
    eLpNorm (∑' j, f j) (2 * r) μ ^ ((2 * r : ℕ) : ℝ)
        = ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * r : ℕ) : ℝ) ∂μ := by
          rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) hr hf hsq]
    _ ≤ ∫⁻ x, (((2 * r)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
        (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * r - 2)) ∂μ :=
          lintegral_sum_norm_pow_le_pointwise_bound (μ := μ) hr hf hsq
    _ ≤ K * ((∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ (2 * r) ∂μ) +
          ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ 2 *
            ‖(∑' j, f j) x‖ₑ ^ (2 * r - 2) ∂μ) := by
          simpa [K] using lintegral_pointwise_bound_le_split (μ := μ) hr hf hsq
    _ ≤ K * (M ^ ((2 * r : ℕ) : ℝ) + M ^ 2 * N ^ (2 * r - 2)) := by
          gcongr
          · rw [← eLpNorm_sqfct_pow_eq_lintegral_nat (μ := μ) (f := f) hr]

omit [MeasurableSpace α] [Countable ι] in
private lemma C_sq_of_two_le (hr : 2 ≤ r) :
    C r ^ 2 = (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
  have hrne : r ≠ 1 := by omega
  simp [C, hrne]
  rw [mul_pow]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show ((2 : ℝ)⁻¹) * ((2 : ℕ) : ℝ) = 1 by norm_num]
  rw [ENNReal.rpow_one]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show ((2 : ℝ)⁻¹) * ((2 : ℕ) : ℝ) = 1 by norm_num]
  rw [ENNReal.rpow_one]

omit [MeasurableSpace α] [Countable ι] in
private lemma one_le_two_mul_factorial_sub_one (hr : 2 ≤ r) :
    (1 : ENNReal) ≤ (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
  have hnat : 1 ≤ (2 * r)! - 1 := by
    have hfact : 1 < (2 * r)! := by
      rw [Nat.one_lt_factorial]
      omega
    omega
  have hK : (1 : ENNReal) ≤ (((2 * r)! - 1 : ℕ) : ENNReal) := by
    exact_mod_cast hnat
  calc
    (1 : ENNReal) ≤ (((2 * r)! - 1 : ℕ) : ENNReal) := hK
    _ ≤ (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
      have hmul : (1 : ENNReal) * (((2 * r)! - 1 : ENNReal)) ≤
          (2 : ENNReal) * (((2 * r)! - 1 : ENNReal)) := by
        gcongr
        norm_num
      simpa using hmul

omit [MeasurableSpace α] [Countable ι] in
private lemma ennreal_absorb_sqfct (hr : 2 ≤ r) {N M : ENNReal} (hNtop : N ≠ ⊤)
    (hpow : N ^ ((2 * r : ℕ) : ℝ) ≤
      (((2 * r)! - 1 : ENNReal) *
        (M ^ ((2 * r : ℕ) : ℝ) + M ^ 2 * N ^ (2 * r - 2)))) :
    N ≤ C r * M := by
  let K : ENNReal := ((2 * r)! - 1 : ENNReal)
  have hr1 : 1 ≤ r := le_trans (by norm_num : 1 ≤ 2) hr
  have hp2 : 2 * r = 2 + (2 * r - 2) := by omega
  have hNpow_nat :
      N ^ (2 * r) ≤ K * (M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)) := by
    simpa only [K, ENNReal.rpow_natCast] using hpow
  have hsq : N ^ 2 ≤ (2 : ENNReal) * K * M ^ 2 := by
    by_cases hNM : N ≤ M
    · calc
        N ^ 2 ≤ M ^ 2 := by gcongr
        _ ≤ ((2 : ENNReal) * K) * M ^ 2 := by
          have hcoef : (1 : ENNReal) ≤ (2 : ENNReal) * K := by
            simpa [K] using one_le_two_mul_factorial_sub_one hr
          calc
            M ^ 2 = (1 : ENNReal) * M ^ 2 := by rw [one_mul]
            _ ≤ ((2 : ENNReal) * K) * M ^ 2 := by
              exact mul_le_mul_right' hcoef (M ^ 2)
        _ = (2 : ENNReal) * K * M ^ 2 := by rw [mul_assoc]
    · have hMN : M ≤ N := le_of_not_ge hNM
      have hNpos : N ≠ 0 := by
        exact ne_of_gt (lt_of_le_of_lt bot_le (lt_of_not_ge hNM))
      have hfac_ne0 : N ^ (2 * r - 2) ≠ 0 := ENNReal.pow_ne_zero hNpos _
      have hfac_ne_top : N ^ (2 * r - 2) ≠ ⊤ := ENNReal.pow_ne_top hNtop
      have hMpow_le : M ^ (2 * r) ≤ M ^ 2 * N ^ (2 * r - 2) := by
        calc
          M ^ (2 * r) = M ^ 2 * M ^ (2 * r - 2) := by
            rw [← pow_add]
            congr 1
          _ ≤ M ^ 2 * N ^ (2 * r - 2) := by
            gcongr
      have hsum_le :
          M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2) ≤
            (2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2)) := by
        calc
          M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)
              ≤ M ^ 2 * N ^ (2 * r - 2) + M ^ 2 * N ^ (2 * r - 2) := by
                gcongr
          _ = (2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2)) := by
                simp [two_mul]
      have hmain :
          N ^ (2 * r) ≤ ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
        calc
          N ^ (2 * r) ≤ K * (M ^ (2 * r) + M ^ 2 * N ^ (2 * r - 2)) := hNpow_nat
          _ ≤ K * ((2 : ENNReal) * (M ^ 2 * N ^ (2 * r - 2))) := by
            gcongr
          _ = ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
            ring
      have hmain' : N ^ 2 * N ^ (2 * r - 2) ≤
          ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := by
        calc
          N ^ 2 * N ^ (2 * r - 2) = N ^ (2 * r) := by
            rw [← pow_add]
            congr 1
            omega
          _ ≤ ((2 : ENNReal) * K * M ^ 2) * N ^ (2 * r - 2) := hmain
      exact (ENNReal.mul_le_mul_iff_left hfac_ne0 hfac_ne_top).mp hmain'
  apply (ENNReal.pow_le_pow_left_iff (n := 2) two_ne_zero).mp
  calc
    N ^ 2 ≤ (2 : ENNReal) * K * M ^ 2 := hsq
    _ = (C r * M) ^ 2 := by
      rw [mul_pow, C_sq_of_two_le hr]

private lemma eLpNorm_tsum_le_sqfct_of_one [Finite ι] {f : ι → α → ℂ}
    (hf : TypeIVSuperorthogonal μ f 1) (hsq : MemLp (sqfct f) 2 μ) :
    eLpNorm (∑' j, f j) 2 μ ≤ eLpNorm (sqfct f) 2 μ := by
  letI := Fintype.ofFinite ι
  have htwoone : (2 * ((1 : ℕ) : ENNReal)) = (2 : ENNReal) := by norm_num
  have hsq' : MemLp (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ := by
    simpa [htwoone] using hsq
  have hpoint :
      (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ) ≤
        ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
    calc
      (∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ)
          ≤ ∫⁻ x, (((2 * 1)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
              (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ (2 * 1 - 2)) ∂μ :=
            lintegral_sum_norm_pow_le_pointwise_bound (μ := μ) (r := 1) (by norm_num) hf hsq'
      _ = ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall fun x ↦ by
              let Sx := ENNReal.ofReal (sqfct f x)
              change (((2 * 1)! - 1 : ENNReal) * (ENNReal.ofReal (sqfct f x)) ^ 2 *
                (max ‖(∑' j, f j) x‖ₑ (ENNReal.ofReal (sqfct f x))) ^ 0) =
                  (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ)
              have hcoeff : (((2 * 1)! - 1 : ENNReal)) = 1 := by
                change ((2 : ENNReal) - 1) = 1
                exact ENNReal.sub_eq_of_eq_add (by norm_num) (by norm_num)
              rw [hcoeff]
              simp
  have hpow :
      eLpNorm (∑' j, f j) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) ≤
        eLpNorm (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) := by
    calc
      eLpNorm (∑' j, f j) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ)
          = ∫⁻ x, ‖(∑' j, f j) x‖ₑ ^ ((2 * 1 : ℕ) : ℝ) ∂μ := by
            rw [eLpNorm_tsum_pow_eq_lintegral (μ := μ) (r := 1) (by norm_num) hf hsq']
      _ ≤ ∫⁻ x, (ENNReal.ofReal (sqfct f x)) ^ ((2 * 1 : ℕ) : ℝ) ∂μ := hpoint
      _ = eLpNorm (sqfct f) (2 * ((1 : ℕ) : ENNReal)) μ ^ ((2 * 1 : ℕ) : ℝ) := by
            rw [← eLpNorm_sqfct_pow_eq_lintegral (μ := μ) (f := f) (r := 1) (by norm_num)]
  have hle := (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < ((2 * 1 : ℕ) : ℝ))).mp hpow
  simpa [htwoone] using hle

theorem sqfct_estimate_of_type_iv_superorthogonal_finite [Finite ι] {f : ι → α → ℂ}
    (hr : 1 ≤ r) (hf : TypeIVSuperorthogonal μ f r) (hsq : MemLp (sqfct f) (2 * r) μ) :
    eLpNorm (∑' j, f j) (2 * r) μ ≤ C r * eLpNorm (sqfct f) (2 * r) μ  := by
  letI := Fintype.ofFinite ι
  by_cases h1 : r = 1
  · subst r
    have hsq1 : MemLp (sqfct f) 2 μ := by
      simpa using hsq
    simpa [C] using eLpNorm_tsum_le_sqfct_of_one (μ := μ) (f := f) hf hsq1
  · have hr2 : 2 ≤ r := by omega
    have hNtop : eLpNorm (∑' j, f j) (2 * r) μ ≠ ⊤ :=
      (memLp_tsum_of_sqfct (μ := μ) hf hsq).eLpNorm_lt_top.ne
    exact ennreal_absorb_sqfct (r := r) hr2 hNtop
      (eLpNorm_tsum_power_le (μ := μ) hr hf hsq)

end Codex

end Superorthogonal

end
