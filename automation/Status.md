# Status

Format: `status | exact source location | brief mathematical step | ISO 8601 timestamp`.

## Main theorem overview (not an execution order)

complete | Theorem 1.1 | ordered-superorthogonality `L^4` reverse square function inequality, PROVED as `Auto.cdw_theorem_1_1` in `Auto/CDW.lean` with the explicit absolute constant 33 | 2026-09-11T22:46-04:00
complete | Theorem 1.4 | sharp `(1+log N)^{1/4}` reverse square function estimate for the equal-width cone partition, PROVED as `Auto.cdw_theorem_1_4` in `Auto/GWZ.lean` with the explicit absolute constant `cdwConst = (1331 (1 + 4 psiL1 sqrt 14)^2)^{1/4}` | 2026-09-12T01:47-04:00

## Reusable prerequisites

None. Minkowski's integral inequality was expected to be needed and a dedicated file was
planned for it; the proof route was changed to Cauchy-Schwarz in `theta` plus Tonelli,
which needs no new reusable theorem. See `ErrorReport.md` for the entry recording this.

## Theorem 1.1 proof ledger (`Auto/CDW.lean`)

complete | Sec. 2, (2.2) | define truncated Hilbert kernel `K(theta) = -2 sum_{n<N} sin(2 pi n theta)` | 2026-09-11T21:15-04:00
complete | Lemma 2.1, (2.3) | `int_0^1 K(theta) e(n theta) dtheta = -i sgn(n)` for `|n| < N` | 2026-09-11T21:15-04:00
complete | Lemma 2.1, (2.4) | `A_N = int_0^1 |K| << 1 + log N` via `|K| <= 2 min{N, 1/|sin(pi theta)|}` | 2026-09-11T21:15-04:00
complete | Sec. 2, C(N) | best constant `M = bestConst` as the supremum of `||sum c_n f_n||_4` over unimodular `c`; nonempty and bounded by `sqrt N * ||S||_4` (`phaseNorms_bddAbove`), with `le_bestConst` | 2026-09-11T22:23-04:00
complete | Sec. 2, (2.1) | `||P_N(theta)||_4 <= M` is `nrm4_phaseSum_le`; truncated `P_m` are not needed | 2026-09-11T22:23-04:00
complete | Lemma 2.2, quartic identity | `a_ij a_kl + a_ik a_jl + a_il a_jk = Re(f_i f_l conj(f_j f_k) - f_i f_j conj(f_k f_l))`, as `imForm_quartic` | 2026-09-11T21:25-04:00
complete | Lemma 2.2, row sums | `R_i = Im[conj(f_i)(sum_{j<i} f_j - sum_{j>i} f_j)]` and `R_i^2 <= |f_i|^2 |sum_{j<i} f_j - sum_{j>i} f_j|^2`, as `rowSum_eq_im` and `sq_rowSum_le` | 2026-09-11T21:25-04:00
complete | Lemma 2.2, pair-counting identity | `distSum = (sum_i R_i)^2 - 4 sum_i R_i^2 + 2 sum_{i,j} G_ij^2`, as `distSum_eq`; proved by inclusion-exclusion on the two removed indices (`sum_disjoint_pairs`), NOT by grouping quadruples into four-element index sets | 2026-09-11T21:52-04:00
complete | Lemma 2.2, quadruple regrouping | `3 distSum = sum over distinct quadruples of the pairing sum` by reindexing (`three_mul_distSum`), and the pairing sum of every distinct quadruple integrates to zero (`integral_pairingSum_eq_zero`), hence `integral_distSum_eq_zero` | 2026-09-11T21:52-04:00
complete | Lemma 2.2, (2.6) | `||V||_2^2 <= 4 int sum_i R_i^2`, as `integral_sq_bigV_le`; the pointwise step `R_i^2 <= |f_i|^2 |sum_{j<i} f_j - sum_{j>i} f_j|^2` is `sq_rowSum_le` | 2026-09-11T21:52-04:00
complete | Lemma 2.2, (2.7) | `W_m = -i int_0^1 K(theta) e(-m theta) P_N(theta) dtheta`, as `signedSum_eq_integral`; the pointwise consequence `|W_m| <= int_0^1 |K| |P_N(theta)|` is `norm_signedSum_le` | 2026-09-11T22:00-04:00
complete | Lemma 2.2, (2.8) | `||V||_2^2 <= 4 A_N^2 M^2 ||S||_4^2`, as `estimate_2_8` | 2026-09-11T22:23-04:00
complete | Sec. 2, page 9 identity | `int_0^1 K(theta) V(theta) dtheta = |sum f_n|^2 - S^2`, as `integral_kernel_bigVphase`; `V(theta) = bigV` of the phase-changed family, and the recovery step `int_0^1 K(theta) Im(e(k theta) z) dtheta = -sgn(k) Re z` is `integral_kernel_mul_im` | 2026-09-11T22:29-04:00
complete | Sec. 2, page 9 bound | `|| |sum f_n|^2 - S^2 ||_2 <= 2 A_N^2 M ||S||_4`, as `page9_bound`; obtained by pairing `H` against itself through the kernel (`page9_swap`) and Cauchy-Schwarz in `x`, rather than by Minkowski | 2026-09-11T22:46-04:00
complete | Sec. 2, phase invariance | `orderedSuperorthogonal_phaseChange`, `nrmS_phaseChange`, `bestConst_phaseChange` | 2026-09-11T22:46-04:00
complete | Corollary 2.3, (2.10) | `||V||_2^2 <= 4 ||S||_4^4` under the extra cancellation (2.9), as `corollary_2_3` in `Auto/CDW.lean`; hypothesis (2.9) is the structure `ExtraCancellation` | 2026-09-11T22:51-04:00
complete | Theorem 1.1 | `bestConst_sq_le` (`M^2 <= T^2 + 2 A_N^2 M T`), `bestConst_le` (`M <= (1 + 2 A_N^2) T`), and `cdw_theorem_1_1` | 2026-09-11T22:46-04:00

## Theorem 1.4 proof ledger (`Auto/GWZ.lean`)

Dependency closure read off Sections 3 and 4.3; rows will be refined when Theorem 1.1 is

Reuse survey of the sibling repository `../lean-spherical` (user-authorized; note it pins
Lean/Mathlib `v4.33.0-rc1` against this project's `v4.31.0-rc2`, so copied code may need
small adaptations, and this project's pins must not be changed):

- `LeanSpherical/Auto/LpSpaceFacts.lean` - `L^p` duality by simple-test pairing, `L^4`
  interpolation between `L^2` and `L^infinity`, `enorm_integral_mul_le_eLpNorm_two_mul`.
  Directly relevant to the `L^4`/`L^2` bookkeeping in Lemma 2.2 and Theorem 1.1.
- `LeanSpherical/Auto/LittlewoodPaley.lean`, `RadialFourierTransform.lean`,
  `MikhlinHormander.lean` - Schwartz/Fourier groundwork.
- `LeanSpherical/Auto/Spherical/MSSBase.lean`, `MSS.lean`, `MSSKakeya.lean` - half-wave
  operators, dyadic bandpass cutoffs (`lpCutoffs`), light-ray kernels and Kakeya-type
  estimates in `Euclidean 2`; the closest existing analogue of the cone geometry needed in
  Sections 3 and 4.

closed and Section 3 is read in full.

complete | Sec. 3.1, (3.1)-(3.2) | `det3`, `conePt`, `D3`, `D3_eq`, `D3_lower_bound` (`D_3 >= 2 h^2 (t_3 - t_1)`) and `det3_conePt_pos`, in `Auto/GWZ.lean` | 2026-09-11T23:00-04:00
complete | Sec. 3.2 | `forbidden_pairing_add_add` and `forbidden_pairing_outer_inner`; the rank/kernel argument of the source is replaced by applying `det3` directly to the relation, which kills the right-hand side and leaves a sum of two positive determinants | 2026-09-11T23:00-04:00
not started | Lemma 3.1 | separated intervals verify the ordered cancellation (1.2) | 2026-09-11T20:55-04:00
complete | Lemma 3.1, Fourier step | `support_fourier_schwartzMul_subset`: the Fourier support of a product of Schwartz functions lies in the Minkowski sum of the supports, via Mathlib's `SchwartzMap.fourier_convolution` and `support_convolution_subset` | 2026-09-11T23:11-04:00
complete | Lemma 3.1, Plancherel step | `integral_mul_conj_eq_zero_of_disjoint` and `integral_prod_mul_conj_prod_eq_zero` | 2026-09-11T23:11-04:00
complete | Lemma 3.1, sectors | `coneSector`, `disjoint_coneSector_add_add`, `disjoint_coneSector_outer_inner` | 2026-09-11T23:11-04:00
complete | Lemma 3.1 | `lemma_3_1`, and `orderedSuperorthogonal_of_coneSector` packaging it as the hypothesis (1.2) of Theorem 1.1, so `cdw_theorem_1_1` applies to cone-sector Schwartz families verbatim | 2026-09-11T23:11-04:00
complete | Lemma 3.2 | `capSector` (3.5), `abs_Qform_le_of_mem_sub_self` (3.7), `Qform_bounds_of_mem_sub` (3.8) and `disjoint_capSector_sub` (3.9) | 2026-09-11T23:21-04:00
complete | Lemma 3.3 | `capInterval`, `Eband`, `sub_capSector_subset_Eband` (the inclusion `Sigma_s subset E_s`), `disjoint_Eband` (bands four apart are disjoint) and `card_le_of_mem_Eband` (3.11) | 2026-09-11T23:21-04:00
complete | Lemma 4.1 | `psi` with `support_psi_subset` and `sum_psi_eq_one` ((4.1)); `Kker_eq_tsum_psiPer` (Poisson); `lintegral_periodization_le`; `fourierInv_dilate` and `lintegral_enorm_psiPer_eq` (scale invariance); conclusion `lintegral_enorm_Kker_le`: `int^-_{Ioc 0 1} ||K_s||_e <= int^- ||psiPer 0||_e`, a constant independent of `s` | 2026-09-12T00:05-04:00
complete | Lemma 4.2 | `nrm2_bigU_le`: `||U_s||_2 <= 2 psiL1 ||S||_4^2`, uniformly in the scale `s`. Route: pair `U_s` against itself through `K_s` using (4.2) and `swap_weight_bigVphase`, Cauchy-Schwarz in `x`, and the loss-free `||V(theta)||_2 <= 2 ||S||_4^2` of Corollary 2.3 | 2026-09-12T01:47-04:00
complete | Sec. 4.3, scale orthogonality | `sub_capSector_subset_Eband_of_psi` and `integral_bigU_mul_conj_bigU_eq_zero`: `U_s` and `U_{s'}` pair to zero when `|s - s'| >= 4`, by (3.8)/(3.11) and the quadruple expansion; this is the physical-space substitute for Plancherel at each frequency | 2026-09-12T01:47-04:00
complete | Sec. 4.3, (4.1) | `bigUfull`, `sum_bigU_eq_bigUfull` (the `L` dyadic pieces add up to `U`) and `bigH_eq_two_re_bigUfull` (`H = 2 Re U`) | 2026-09-12T01:47-04:00
complete | Sec. 4.3, `||U||_2` | `integral_normSq_sum_bigU_le`: `||U||_2^2 <= 7 L (2 psiL1 ||S||_4^2)^2`, the almost-orthogonal sum; the constant is 7 (the number of `s'` with `|s - s'| <= 3`) where the source gets 4 | 2026-09-12T01:47-04:00
complete | Sec. 4.3, one class | `nrm4_sq_le_capFamily`: for `M` equal caps in arithmetic progression with gap `11w` and `M <= 2^n`, `||sum f_m||_4^2 <= (1 + 4 psiL1 sqrt(7(n+1))) ||S||_4^2` | 2026-09-12T01:47-04:00
complete | Sec. 4.3, residue classes | `classSize`, `sum_residue_class`, `sum_split_residues`, `padSchwartz`, `sum_split_padSchwartz`: the index set splits into eleven arithmetic progressions | 2026-09-12T01:47-04:00
complete | Sec. 4.3, (1.7) | `pow4_sum_le_of_capPartition` (dyadic form) and `cdw_theorem_1_4`: `||sum f_j||_4 <= cdwConst (1 + log N)^{1/4} ||S||_4` for the canonical equal-width partition, PROVED in `Auto/GWZ.lean` | 2026-09-12T01:47-04:00

## Verification record

ok | full build | `lake build` succeeds (8576 jobs); `Auto/CDW.lean` 3192 lines and `Auto/GWZ.lean` 2344 lines, both placeholder-free and warning-free. `LeanSuperorthogonality.lean` now audits `Auto.cdw_theorem_1_1` and `Auto.cdw_theorem_1_4`: both depend only on propext, Classical.choice, Quot.sound. The remaining `sorry` warning in the build is in the repository's pre-existing `Challenge.lean`, which is out of scope and untouched | 2026-09-12T01:47-04:00

## Continuation notes

The counting branch of Lemma 2.2 is closed. The route actually used is simpler than the
fibre bijection first envisaged and is recorded here so it is not undone:

- `sum_disjoint_pairs` states inclusion-exclusion for an arbitrary symmetric form `G` with
  vanishing diagonal. Removing the two outer indices from the inner double sum gives
  `Tot(i,j) = U - 2 R_i - 2 R_j + 2 G_ij`, and multiplying by `G_ij` and summing yields
  `distSum = U^2 - 4 sum R_i^2 + 2 sum G_ij^2` with no case analysis on quadruple patterns.
- The vanishing `int distSum = 0` comes from averaging: reindexing the four nested sums by
  the transpositions `(2 3)` and `(2 4)` shows `distSum` equals each of the three pairing
  sums, so `3 distSum` is the sum of `pairingSum` over distinct quadruples. `pairingSum` is
  built from the symmetric form and is therefore invariant under every permutation of the
  quadruple, which reduces `int pairingSum = 0` to the sorted case `i < j < k < l`, where it
  is the quartic identity together with (1.2).

Next work item: the eleven-residue-class recombination that finishes Theorem 1.4.

## 2026-09-12T01:33-04:00 -- Lemma 4.2 and most of Section 4.3 are proved

`lake build` passes (8576 jobs); `CDW.lean` and `GWZ.lean` are sorry-free and warning-free.
New declarations, in dependency order:

  CDW.lean
    integral_weight_bigVphase_eq      the weighted pairing against iV(theta) as a finite
                                      trigonometric sum (the exported form of `houter`)
    continuous_weight_kernel_pairing  hence continuity of theta |-> K(theta) * pairing
    aestronglyMeasurable_finsetSumReal, aestronglyMeasurable_bigV
    nrm4_sq_le_nrm2_bigH              ||sum f||_4^2 <= ||S||_4^2 + ||H||_2  (first half of
                                      the old `nrm4_sq_le`, isolated for reuse)
    nrm2_mono                         monotonicity of the L^2 norm under |a| <= b

  GWZ.lean
    aestronglyMeasurable_bigU
    nrm2_bigU_le                      **Lemma 4.2**: ||U_s||_2 <= 2 psiL1 ||S||_4^2,
                                      uniformly in the scale s
    disjoint_add_of_disjoint_sub'     general crossed form of the sum/difference exchange
    sub_capSector_subset_Eband_of_psi a psi-selected pair sits in the band E_s of (3.8)
    integral_bigU_mul_conj_bigU_eq_zero   **scale orthogonality**: U_s _|_ U_{s'} when
                                      s + 4 <= s'  (this is (3.11) in action)
    bigUfull, sum_bigU_eq_bigUfull    (4.1): the L dyadic pieces add up to U
    bigH_eq_two_re_bigUfull           H = 2 Re U
    integrable_bigU_mul_conj_bigU, integrable_normSq_sum_bigU
    norm_integral_bigU_mul_conj_bigU_le
    integral_normSq_sum_bigU_le       ||U||_2^2 <= 7 L (2 psiL1 ||S||_4^2)^2
    nrm4_sq_le_capFamily              **Theorem 1.4 for one residue class**:
                                      ||sum f_m||_4^2 <= (1 + 4 psiL1 sqrt(7(n+1))) ||S||_4^2
                                      for M caps in arithmetic progression with gap 11w and
                                      M <= 2^n

Route notes, so they are not re-derived:

- Plancherel on the U side is NOT used. The manuscript squares the Fourier side and applies
  Cauchy-Schwarz at each frequency; instead the almost-orthogonality is taken directly in
  physical space, since `integral_mul_conj_eq_zero_of_disjoint` already turns disjoint
  Fourier supports into a vanishing pairing. This gives the constant 7 (the number of s'
  with |s - s'| <= 3) where the manuscript gets 4; only the absolute constant changes.
- The U_s x U_{s'} pairing is expanded into a QUADRUPLE finite sum and each term is killed
  by `integral_prod_mul_conj_prod_eq_zero`, rearranging
  (f_i conj f_j)(conj f_k f_l) = (f_i f_l) conj(f_j f_k) so the SUM sets Sigma_i + Sigma_l
  and Sigma_k + Sigma_j are what must be disjoint; `disjoint_add_of_disjoint_sub'` converts
  the band disjointness of the DIFFERENCE sets into exactly that.
- The manuscript's `||sum f||_4^4 <= 2||S||_4^4 + 8||U||_2^2` is replaced by the sharper and
  already available `nrm4_sq_le_nrm2_bigH` plus `H = 2 Re U`, which needs no extra constant.

Remaining for Theorem 1.4 (Section 4.3 tail):

  1. Combinatorial: `sum_filter_mod_eq`, the identification of the residue class
     {j < N : j % 11 = r} with an arithmetic progression indexed by Fin ((N-r+10)/11).
  2. `sum_j f_j = sum_{r<11} sum_{m} f (r + 11 m)` and the matching cap-center identity
     c j = (j + 1/2)/N, so that within a class c_{m'} - c_m = 11 * (1/N) * (m' - m).
  3. Recombination WITHOUT Minkowski in L^4: pointwise
     ||sum_{r<11} G_r||^4 <= 11^3 sum_r ||G_r||^4  and  sum_r S_r^4 <= S^4 pointwise,
     hence nrm4(sum f)^4 <= 11^3 (1 + 4 psiL1 sqrt(7L))^2 nrmS^4.
  4. Choose n = clog 2 N so that N <= 2^n and n + 1 <= C (1 + log N); conclude (1.7).

Everything Lemma 4.2 needs is now in place:

  bigU_eq_integral           U_s = int_0^1 K_s(theta) i V(theta) dtheta            (4.2)
  swap_weight_bigVphase      the interchange, for ANY weight W and continuous kernel
  integral_sq_bigVphase_le_of_extra   int |V(theta)|^2 <= 4 ||S||_4^4, uniform in theta
  KkerL1_le                  A_s = int_0^1 |K_s| <= psiL1, an absolute constant

`swap_weight_bigVphase` is the reusable form of the page-9 pattern: because `i V(theta)` is a
finite trigonometric sum (`I_mul_bigVphase_eq`), pairing a weight against it and swapping the
two integrals needs only linearity, never Fubini, so `mu` stays arbitrary. Signature:

  swap_weight_bigVphase (W : alpha -> C) (Kf : R -> C) (hKf : Continuous Kf)
      (hint : forall i j, Integrable (fun x => W x * (f i x * conj (f j x))) mu) :
    int_x W x * (int_0^1 Kf theta * (I * V(theta,x))) dmu
      = int_0^1 Kf theta * (int_x W x * (I * V(theta,x)) dmu)

The remaining assembly, taking `W = conj . bigU f s` and `Kf = Kker s`:

  1. `int_X |U_s|^2 = int_X conj(U_s) U_s`, and by (4.2) the right factor is the theta
     integral, so `swap_weight_bigVphase` turns it into
     `int_0^1 K_s(theta) (int_X conj(U_s) i V(theta) dmu) dtheta`.
  2. Cauchy-Schwarz in `x`: `|int_X conj(U_s) i V(theta)| <= ||U_s||_2 ||V(theta)||_2`
     (note `|i V| = |V|`), and `||V(theta)||_2 <= 2 ||S||_4^2` uniformly.
  3. Hence `||U_s||_2^2 <= A_s * ||U_s||_2 * 2 ||S||_4^2`, so
     `||U_s||_2 <= 2 A_s ||S||_4^2 <= 2 psiL1 ||S||_4^2`.
  Integrability side condition for step 1: `bigU` is a finite sum of `f_a conj(f_b)`, so
  `conj(bigU) * (f_i conj(f_j))` is a finite sum of quadruple products - use
  `integrable_quadruple` from CDW.lean.

Then Section 4.3 as planned below.

Design decisions recorded so they are not re-derived:

- The source's `C(N)` is a supremum over all admissible families over all measure spaces,
  which is not a set in Lean. It is replaced by the supremum `M` of the `L^4` norms of
  `sum_n c_n f_n` over unimodular `c`, for the fixed family. That is a genuine bounded set
  of reals, bounded above by `sqrt N` times the `L^4` norm of the square function via
  `norm_sum_le_sqrt_mul_sqFun`. See the entry in `ErrorReport.md`.
- With that choice the bootstrap reads `M^2 <= T^2 + 2 A_N^2 M T` where `T` is the `L^4`
  norm of the square function, giving `M <= (1 + 2 A_N^2) T` with no division, so the
  degenerate case `T = 0` needs no separate treatment.
- `A_N <= 4 (1 + log N)` is `hilbertKernelL1_le`, so the final constant will be
  `1 + 2 * 16 * (1 + log N)^2 <= 33 (1 + log N)^2`.
- Truncated sums `P_m` for `m < N` are not needed anywhere.


## 2026-09-12T01:47-04:00 -- both targets are proved

Theorem 1.1 (`Auto.cdw_theorem_1_1`) and Theorem 1.4 (`Auto.cdw_theorem_1_4`) are complete,
sorry-free, warning-free, and axiom-clean. The recurring 15-minute wake-up was deleted at
this point, since every in-scope target is proved and `lake build` passes.

Declarations added in the final stretch, in dependency order:

  CDW.lean
    integral_weight_bigVphase_eq, continuous_weight_kernel_pairing
    aestronglyMeasurable_finsetSumReal, aestronglyMeasurable_bigV
    integrable_mul_of_sq, continuous_bigVphase_of
    nrm4_sq_le_nrm2_bigH, nrm2_mono

  GWZ.lean
    aestronglyMeasurable_bigU, nrm2_bigU_le                      (Lemma 4.2)
    disjoint_add_of_disjoint_sub', sub_capSector_subset_Eband_of_psi,
      integral_bigU_mul_conj_bigU_eq_zero                        (scale orthogonality)
    bigUfull, sum_bigU_eq_bigUfull, bigH_eq_two_re_bigUfull      (4.1)
    integrable_bigU_mul_conj_bigU, integrable_normSq_sum_bigU,
      norm_integral_bigU_mul_conj_bigU_le, integral_normSq_sum_bigU_le
    nrm4_sq_le_capFamily                                         (one residue class)
    classSize, mem_classSize, sum_residue_class, sum_split_residues,
      padSchwartz, padSchwartz_of_lt, padSchwartz_coe, sum_split_padSchwartz
    cdwConst, clog_succ_le, pow4_sum_le_of_capPartition, cdw_theorem_1_4

Route decisions taken in Section 4.3, recorded so they are not re-derived:

- No Plancherel on the `U` side. The source squares the Fourier transform and applies
  Cauchy-Schwarz at each frequency; here the almost-orthogonality is taken directly in
  physical space through `integral_mul_conj_eq_zero_of_disjoint`, which already converts
  disjoint Fourier supports into a vanishing pairing. Constant 7 instead of 4.
- The `U_s` x `U_{s'}` pairing is expanded into a quadruple finite sum; each term is killed
  by rearranging `(f_i conj f_j)(conj f_k f_l) = (f_i f_l) conj(f_j f_k)` so that the SUM
  sets must be disjoint, and `disjoint_add_of_disjoint_sub'` converts the band disjointness
  of the DIFFERENCE sets into exactly that.
- `||sum f||_4^4 <= 2||S||_4^4 + 8||U||_2^2` of the source is replaced by the already
  available `nrm4_sq_le_nrm2_bigH` together with `H = 2 Re U`, which costs no constant.
- Minkowski's inequality in `L^4` is avoided in the eleven-class recombination: the
  pointwise Jensen bound `(sum_{r<11} t_r)^4 <= 11^3 sum_r t_r^4`
  (`pow_sum_div_card_le_sum_pow`) plus the pointwise `sum_r S_r^4 <= S^4` suffice, so the
  whole argument stays inside the elementary `pow4`/`nrmS` vocabulary of `CDW.lean`.
- `L = 1 + clog 2 N` and `clog_succ_le` gives `L <= 2 (1 + log N)` from
  `2^(clog - 1) < N` and `log 2 > 1/2`.

Out of scope and deliberately not formalized: Corollary 1.3, Theorem 1.5, Proposition 4.3
(sharpness, Subsection 4.4), and Remarks 1.2/4.4.

## Theorems.lean API bridge

complete | Theorems.lean, CDW square-function estimate | Identify square functions and L4 norms, then apply cdw_theorem_1_1 with the exact public hypotheses | 2026-10-12T20:32:52.5954918-04:00


Verification (2026-10-12T20:32:52.5954918-04:00): lake env lean LeanSuperorthogonality/Auto/Theorems.lean passes; Auto.sqfct_estimate_of_superorthogonal uses only propext, Classical.choice, Quot.sound. Full build was attempted during development and failed on a bridge error subsequently fixed. Final validation is scoped to the Auto module per the user's correction; no final full-build success is claimed. All task edits to Lean files outside Auto/ were reverted.


## Cone estimate API bridge

complete | Theorems.lean, cone_sqfct_estimate | Bound the analytic constant numerically by 46 | 2026-10-12T21:11:56.2293626-04:00
complete | Theorems.lean, cone_sqfct_estimate | Identify conic sectors and L4 norms, handle N = 0,1, apply numerical estimate | 2026-10-12T21:15:36.2080774-04:00


Verification (2026-10-12T21:15:36.2080774-04:00): lake build LeanSuperorthogonality.Auto.Theorems passes without warnings. Auto.cdwConst_le_46 and Auto.cone_sqfct_estimate depend only on propext, Classical.choice, Quot.sound; the earlier square-function theorem remains axiom-clean. The numerical proof uses psiL1 <= 7/2 from cutoff energies 3/2 and 96 and weighted Cauchy-Schwarz with Plancherel. Full lake build is blocked by existing imports of the absent LeanSuperorthogonality/PointwiseEstimate.lean and LeanSuperorthogonality/MainTheorem.lean in the root module and Solution.lean. Those files were left untouched per the user's scope restriction. All Lean edits for this request are in Auto/Theorems.lean.


Verification (2026-10-12T21:58:56.8099425-04:00): Updated Solution.lean import and documentation to LeanSuperorthogonality.Theorems under explicit user authorization. Full lake build passes (8576 jobs), resolving the prior missing-import blocker. Challenge.lean retains its intentional sorry. Changes are uncommitted.


Branch separation (2026-10-12T22:05:35.5128775-04:00): palomar-gpry preserves the five GPRY submission files at 7e475c5. Master removes them and their Lake targets; README points to the dedicated branch. Full lake build passes (8572 jobs). No branches pushed.

Toolchain verification (2026-10-12T22:25:18.5515505-04:00): Lean and Mathlib upgraded together to v4.35.0-rc4 on master. Full lake build passes (9028 jobs). All four public root theorem axiom checks, plus Auto.sqfct_estimate_of_superorthogonal, Auto.cdwConst_le_46 and Auto.cone_sqfct_estimate, use only propext, Classical.choice and Quot.sound. Compatibility edits are confined to Auto/CDW.lean, Auto/PointwiseEstimate.lean, Auto/MainTheorem.lean and Auto/Theorems.lean. Public theorem statements are unchanged; private square-function integral identities now take the existing MemLp hypothesis to provide measurability required by Mathlib. Deprecation and linter warnings remain. No commit or push performed.
