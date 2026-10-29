import DGRHS.Gaussian.PeriodicRieszTruncatedLaplace
import DGRHS.Gaussian.PeriodicStrictCutoffParseval
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2

/-!
Packet P9d, unit 1 (part 3): the `L²` remainder of the heat-shift truncation on the torus,
the periodic form of `eq:fetaL2Rate` / `eq:centeredFetaL2Rate` (TeX Step 2 of Proposition 5.5).
Spectrally `‖g - g_τ‖² = A_s² Σ_{k≠0} ‖k‖^{2(s-d)} (1 - e^{-τ‖k‖²})²`.

The heat-shift family has `‖g - g_τ‖_{L²}² ≲ τ^{(d-2s)/2}` exactly when `d - 2s < 4`;
for `d - 2s > 4` the second-order saturation `≲ τ²` is the true size (not an artefact of the proof).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology lp
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration DGRHS.Periodic.RealifiedStrictCutoff
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Low-frequency lattice sums for every exponent `e > -d`. -/
lemma periodicFrequency_low_sum_le_general (e : ℝ) (he : -(Fintype.card ι : ℝ) < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K →
      ∑' k : PeriodicFrequency ι, (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ e else 0) ≤ C * K ^ (e + (Fintype.card ι : ℝ)) := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos (α := ι)
  set e' : ℝ := min e (-d / 2) with he'
  have he'1 : e' ≤ e := min_le_left _ _
  have he'2 : e' ≤ -d / 2 := min_le_right _ _
  have he'3 : -d < e' := lt_min he (by linarith)
  obtain ⟨C, hC0, hC⟩ := periodicFrequency_low_sum_le (ι := ι) (e' + d) (by linarith) (by linarith)
  refine ⟨C, hC0, fun K hK => ?_⟩
  have hKpos : 0 < K := by linarith
  have hfin : Set.Finite {k : PeriodicFrequency ι | ‖periodicFrequencyVector k‖ ≤ K} :=
    finite_periodicFrequency_norm_le K hKpos.le
  have hs1 : Summable (fun k : PeriodicFrequency ι => if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ e else 0) := by
    apply summable_of_hasFiniteSupport
    apply hfin.subset
    intro k hk
    by_contra hnot
    apply hk
    simp only
    rw [ite_eq_right]
    intro h; exact hnot h.2
  have hs2 : Summable (fun k : PeriodicFrequency ι => if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ (e' + d - d) else 0) := by
    apply summable_of_hasFiniteSupport
    apply hfin.subset
    intro k hk
    by_contra hnot
    apply hk
    simp only
    rw [ite_eq_right]
    intro h; exact hnot h.2
  have hle : ∀ k : PeriodicFrequency ι, (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ e else 0) ≤
      K ^ (e - e') * (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ (e' + d - d) else 0) := by
    intro k
    by_cases h : k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K
    · rw [ite_eq_left h, ite_eq_left h]
      have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector h.1
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      have hsplit : ‖periodicFrequencyVector k‖ ^ e =
          ‖periodicFrequencyVector k‖ ^ (e - e') * ‖periodicFrequencyVector k‖ ^ (e' + d - d) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [hsplit]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hpos.le _)
      exact Real.rpow_le_rpow hpos.le h.2 (by linarith)
    · rw [ite_eq_right h, ite_eq_right h]; simp
  calc _ ≤ ∑' k : PeriodicFrequency ι, K ^ (e - e') * (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ (e' + d - d) else 0) := hs1.tsum_le_tsum hle (hs2.mul_left _)
    _ = K ^ (e - e') * ∑' k : PeriodicFrequency ι, (if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
        ‖periodicFrequencyVector k‖ ^ (e' + d - d) else 0) := tsum_mul_left
    _ ≤ K ^ (e - e') * (C * K ^ (e' + d)) :=
        mul_le_mul_of_nonneg_left (hC K hK) (Real.rpow_nonneg hKpos.le _)
    _ = C * K ^ (e + d) := by
        rw [← mul_assoc, mul_comm (K ^ (e - e')) C, mul_assoc, ← Real.rpow_add hKpos]
        congr 2; ring

/-- Real kernel of the remainder `g - g_τ`. -/
def periodicRieszRemainder (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    PeriodicTorus ι → ℝ := fun x => periodicRieszKernel s hs2 x - periodicRieszMellinGreen s τ x

lemma periodicRieszRemainder_memLp (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    MemLp (periodicRieszRemainder s τ hs2) 2 (periodicHaar ι) :=
  (periodicRieszKernel_memLp s hs2).sub (periodicRieszMellinGreen_memLp s τ hs2 hτ)

lemma periodicRieszRemainder_stronglyMeasurable (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    StronglyMeasurable (periodicRieszRemainder s τ hs2) :=
  (periodicRieszKernel_stronglyMeasurable s hs2).sub
    (periodicRieszMellinGreen_measurable (ι := ι) s τ).stronglyMeasurable

/-- Parseval identity for the remainder. -/
theorem periodicRieszRemainder_integral_sq_eq (s τ : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hτ : 0 ≤ τ) :
    ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι =
      (periodicRieszFourierAmplitude ι s) ^ 2 * ∑' k : PeriodicFrequency ι,
        ‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) *
          (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2 := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have hg := periodicRieszRemainder_memLp s τ hs2 hτ
  set F : Lp ℂ 2 (periodicHaar ι) := periodicRieszL2 s hs2 - periodicRieszHeatL2 s τ hs2 hτ with hF
  set g : Lp ℝ 2 (periodicHaar ι) := hg.toLp (periodicRieszRemainder s τ hs2) with hgdef
  have hc : realToComplexL2 g = F := by
    apply Lp.ext
    filter_upwards [realToComplexL2_coe_ae g, hg.coeFn_toLp, periodicRieszKernel_coe_ae s hs2,
      periodicRieszMellinGreen_coe_ae_heatL2 s τ hs2 hτ, Lp.coeFn_sub (periodicRieszL2 s hs2)
        (periodicRieszHeatL2 s τ hs2 hτ)] with x h1 h2 h3 h4 h5
    rw [h1]
    have : g x = periodicRieszRemainder s τ hs2 x := h2
    rw [this, hF, h5]
    simp only [Pi.sub_apply, periodicRieszRemainder, Complex.ofReal_sub, h3, h4]
  calc ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι
      = ‖g‖ ^ 2 := (DGRHS.Kernel.norm_toLp_sq hg).symm
    _ = ‖F‖ ^ 2 := by rw [← hc, realToComplexL2_norm]
    _ = ∑' k : PeriodicFrequency ι, ‖UnitAddTorus.mFourierCoeff F k‖ ^ 2 :=
        norm_sq_eq_tsum_fourierCoeff _
    _ = ∑' k : PeriodicFrequency ι, (periodicRieszFourierAmplitude ι s) ^ 2 *
          (‖periodicFrequencyVector k‖ ^ (2 * (s - (Fintype.card ι : ℝ))) *
            (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2) := by
        apply tsum_congr
        intro k
        have hco : UnitAddTorus.mFourierCoeff F k =
            UnitAddTorus.mFourierCoeff (periodicRieszL2 s hs2) k -
              UnitAddTorus.mFourierCoeff (periodicRieszHeatL2 s τ hs2 hτ) k := by
          rw [← periodicFourierBasis_repr, ← periodicFourierBasis_repr,
            ← periodicFourierBasis_repr, hF, map_sub]
          rfl
        rw [hco, periodicRieszL2_fourierCoeff, periodicRieszHeatL2_fourierCoeff]
        unfold periodicRieszHeatFourierCoeff
        have : periodicRieszFourierCoeff s k -
            (Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) : ℂ) * periodicRieszFourierCoeff s k =
            ((1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) : ℝ) : ℂ) *
              periodicRieszFourierCoeff s k := by push_cast; try ring
        rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
          norm_periodicRieszFourierCoeff_sq s hsd k]
        ring
    _ = _ := by rw [← tsum_mul_left]


lemma one_sub_exp_neg_sq_le_sq (x : ℝ) (hx : 0 ≤ x) : (1 - Real.exp (-x)) ^ 2 ≤ x ^ 2 := by
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : 0 ≤ 1 - Real.exp (-x) := by linarith
  nlinarith

lemma one_sub_exp_neg_sq_le_one (x : ℝ) (hx : 0 ≤ x) : (1 - Real.exp (-x)) ^ 2 ≤ 1 := by
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h4 : 0 < Real.exp (-x) := Real.exp_pos _
  nlinarith

/-- The remainder `‖g - g_τ‖²_{L²(Haar)} ≲ τ^{(d-2s)/2}` when `d - 2s < 4` (sharp). -/
theorem periodicRieszRemainder_integral_sq_le_sharp (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hd4 : (Fintype.card ι : ℝ) - 2 * s < 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤
        C * τ ^ (((Fintype.card ι : ℝ) - 2 * s) / 2) := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos (α := ι)
  obtain ⟨C1, hC1, hlow⟩ := periodicFrequency_low_sum_le_general (ι := ι) (2 * (s - d) + 4)
    (by linarith)
  obtain ⟨C2, hC2, hhigh⟩ := periodicFrequency_tail_sum_le (ι := ι) s hs2
  set A := periodicRieszFourierAmplitude ι s with hA
  refine ⟨A ^ 2 * (C1 + C2), by positivity, ?_⟩
  intro τ hτ hτ1
  set K : ℝ := τ ^ (-(1 / 2 : ℝ)) with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  have hKpos : 0 < K := by linarith
  let low : PeriodicFrequency ι → ℝ := fun k =>
    if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then
      ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4) else 0
  let high : PeriodicFrequency ι → ℝ := fun k =>
    if K < ‖periodicFrequencyVector k‖ then ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) else 0
  have hlow_sum : Summable low := by
    apply summable_of_hasFiniteSupport
    apply (finite_periodicFrequency_norm_le (ι := ι) K hKpos.le).subset
    intro k hk
    by_contra hnot
    apply hk
    simp only [low]
    rw [ite_eq_right]
    intro h; exact hnot h.2
  have hr : 2 * (s - d) < -d := by linarith
  have hhigh_nn : ∀ k, 0 ≤ high k := fun k => by
    simp only [high]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hhigh_sum : Summable high := by
    refine (summable_periodicFrequency_rpow (ι := ι) _ hr).of_nonneg_of_le hhigh_nn (fun k => ?_)
    simp only [high]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (norm_nonneg _) _
  have hlow_nn : ∀ k, 0 ≤ low k := fun k => by
    simp only [low]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hterm : ∀ k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2 ≤ τ ^ 2 * low k + high k := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp only [periodicFrequencyVector_zero, norm_zero, neg_zero, mul_zero, zero_mul, Real.exp_zero,
        sub_self, ne_eq, not_true_eq_false, false_and, ite_false, low, high, sq]
      simp
      have := hlow_nn 0; have := hhigh_nn 0
      positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      have hx : 0 ≤ ‖periodicFrequencyVector k‖ ^ 2 * τ := by positivity
      have hpn : 0 ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) := Real.rpow_nonneg hpos.le _
      by_cases hkK : ‖periodicFrequencyVector k‖ ≤ K
      · have hlk : low k = ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4) := by
          simp only [low]; rw [ite_eq_left ⟨hk, hkK⟩]
        have hhk : high k = 0 := by simp only [high]; rw [ite_eq_right (not_lt.mpr hkK)]
        rw [hlk, hhk, add_zero]
        have hb := one_sub_exp_neg_sq_le_sq _ hx
        calc ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
              (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2
            ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) * (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ 2 :=
              mul_le_mul_of_nonneg_left hb hpn
          _ = τ ^ 2 * ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4) := by
              rw [Real.rpow_add hpos, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
              ring
      · have hKk : K < ‖periodicFrequencyVector k‖ := lt_of_not_ge hkK
        have hlk : low k = 0 := by simp only [low]; rw [ite_eq_right]; intro h; exact hkK h.2
        have hhk : high k = ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) := by
          simp only [high]; rw [ite_eq_left hKk]
        rw [hlk, hhk, mul_zero, zero_add]
        have hb := one_sub_exp_neg_sq_le_one _ hx
        calc _ ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) * 1 :=
              mul_le_mul_of_nonneg_left hb hpn
          _ = _ := mul_one _
  have hsumL : Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2) := by
    refine (summable_periodicFrequency_rpow (ι := ι) _ hr).of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
    · have hx : 0 ≤ ‖periodicFrequencyVector k‖ ^ 2 * τ := by positivity
      calc _ ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) * 1 :=
            mul_le_mul_of_nonneg_left (one_sub_exp_neg_sq_le_one _ hx) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = _ := mul_one _
  have hR : Summable (fun k => τ ^ 2 * low k + high k) := (hlow_sum.mul_left _).add hhigh_sum
  have h1 := hsumL.tsum_le_tsum hterm hR
  have hL : ∑' k, low k ≤ C1 * K ^ (2 * (s - d) + 4 + d) := hlow K hK1
  have hH : ∑' k, high k ≤ C2 * K ^ (2 * s - d) := hhigh K hK1
  have hKe1 : τ ^ 2 * K ^ (2 * (s - d) + 4 + d) = τ ^ ((d - 2 * s) / 2) := by
    rw [hK, ← Real.rpow_mul hτ.le, show (τ ^ 2 : ℝ) = τ ^ (2 : ℝ) by norm_num,
      ← Real.rpow_add hτ]
    congr 1; ring
  have hKe2 : K ^ (2 * s - d) = τ ^ ((d - 2 * s) / 2) := by
    rw [hK, ← Real.rpow_mul hτ.le]; congr 1; ring
  have hsum2 : ∑' k : PeriodicFrequency ι, (τ ^ 2 * low k + high k) ≤
      (C1 + C2) * τ ^ ((d - 2 * s) / 2) := by
    calc _ = τ ^ 2 * ∑' k, low k + ∑' k, high k := by
          rw [(hlow_sum.mul_left (τ ^ 2)).tsum_add hhigh_sum, tsum_mul_left]
      _ ≤ τ ^ 2 * (C1 * K ^ (2 * (s - d) + 4 + d)) + C2 * K ^ (2 * s - d) :=
          add_le_add (mul_le_mul_of_nonneg_left hL (sq_nonneg _)) hH
      _ = (C1 + C2) * τ ^ ((d - 2 * s) / 2) := by
          rw [show τ ^ 2 * (C1 * K ^ (2 * (s - d) + 4 + d)) =
            C1 * (τ ^ 2 * K ^ (2 * (s - d) + 4 + d)) by ring, hKe1, hKe2]; ring
  have hEq := periodicRieszRemainder_integral_sq_eq s τ hs2 hτ.le
  rw [hEq]
  calc A ^ 2 * ∑' k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
        (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2
      ≤ A ^ 2 * ((C1 + C2) * τ ^ ((d - 2 * s) / 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans hsum2) (sq_nonneg _)
    _ = _ := by ring


/-- Second-order saturation of the heat shift: `‖g - g_τ‖² ≲ τ²` when `d - 2s > 4`. -/
theorem periodicRieszRemainder_integral_sq_le_saturated (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hd4 : 4 < (Fintype.card ι : ℝ) - 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ 2 := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  set A := periodicRieszFourierAmplitude ι s with hA
  have hr : 2 * (s - d) + 4 < -d := by linarith
  have hsum : Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4)) :=
    summable_periodicFrequency_rpow (ι := ι) _ hr
  refine ⟨A ^ 2 * ∑' k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4),
    mul_nonneg (sq_nonneg _) (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro τ hτ
  have hterm : ∀ k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2 ≤
      τ ^ 2 * ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
      positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      have hx : 0 ≤ ‖periodicFrequencyVector k‖ ^ 2 * τ := by positivity
      have hpn : 0 ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) := Real.rpow_nonneg hpos.le _
      calc _ ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) * (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ 2 :=
            mul_le_mul_of_nonneg_left (one_sub_exp_neg_sq_le_sq _ hx) hpn
        _ = _ := by
            rw [Real.rpow_add hpos, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            ring
  have hsumL : Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2) :=
    (hsum.mul_left (τ ^ 2)).of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)) hterm
  rw [periodicRieszRemainder_integral_sq_eq s τ hs2 hτ.le]
  calc _ ≤ A ^ 2 * ∑' k : PeriodicFrequency ι, τ ^ 2 * ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 4) :=
        mul_le_mul_of_nonneg_left (hsumL.tsum_le_tsum hterm (hsum.mul_left _)) (sq_nonneg _)
    _ = _ := by rw [tsum_mul_left]; ring


lemma norm_le_sqrt_mul_rpow (n C t θ : ℝ) (hn : 0 ≤ n) (hC : 0 ≤ C) (ht : 0 < t)
    (h : n ^ 2 ≤ C * t ^ θ) : n ≤ Real.sqrt C * t ^ (θ / 2) := by
  have h1 : (Real.sqrt C * t ^ (θ / 2)) ^ 2 = C * t ^ θ := by
    rw [mul_pow, Real.sq_sqrt hC, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 2; push_cast; ring
  have h2 : 0 ≤ Real.sqrt C * t ^ (θ / 2) := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg ht.le _)
  exact abs_le_of_sq_le_sq' (by rw [h1]; exact h) h2 |>.2

/-- Centered `L²(μ⊗μ)` residual `‖h̃ - h̃_τ‖` from the Haar remainder bound (torus form of
`eq:centeredFetaL2Rate`, first inequality; Hoeffding centering is bounded by 4 and the
bounded density by `M`). -/
theorem periodicRieszResidual_of_remainder (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
        (hq : MemLp (periodicTruncCentered (periodicCappedDensityMeasure ρ) s τ) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))),
      ‖(hh.sub hq).toLp (fun p => hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
          periodicTruncCentered (periodicCappedDensityMeasure ρ) s τ p)‖ ≤ A * τ ^ (θ / 2) := by
  obtain ⟨C, hC0, hC⟩ := hrem
  refine ⟨4 * M * Real.sqrt C, by positivity, ?_⟩
  intro τ hτ hτ1 hh hq
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hg := periodicRieszRemainder_memLp s τ hs2 hτ.le
  have hgm := periodicRieszRemainder_stronglyMeasurable (ι := ι) s τ hs2
  have hWint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszKernel s hs2 (p.1 - p.2)) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hVint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszTruncKernel s τ (p.1 - p.2)) (μ.prod μ) := by
    apply periodicDensityPair_integrable_of_haar ρ M hρ _
    exact ((periodicPositiveFourierKernel_continuous _
      (periodicRieszTruncCoeff_nonneg (ι := ι) s τ hs0 hs2)
      (periodicRieszTruncCoeff_summable (ι := ι) s τ hs0 hs2 hτ)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  have hsub := ae_hoeffdingCentered_sub μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (p.1 - p.2))
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszTruncKernel s τ (p.1 - p.2))
    hWint hVint
  have hgreen := periodicDensity_pair_ae_of_haar ρ
    (fun x => periodicRieszMellinGreen s τ x = periodicRieszTruncKernel s τ x)
    (periodicRieszMellinGreen_ae_truncKernel s τ hs0 hs2 hτ)
  have hWV : ((fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (p.1 - p.2)) -
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszTruncKernel s τ (p.1 - p.2)))
      =ᵐ[μ.prod μ] (fun p => periodicRieszRemainder s τ hs2 (p.1 - p.2)) := by
    filter_upwards [hgreen] with p hp
    simp only [Pi.sub_apply, periodicRieszRemainder]
    rw [hp]
  have hcong := ae_hoeffdingCentered_congr μ _ _ hWV
  have hae : (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
      periodicTruncCentered μ s τ p) =ᵐ[μ.prod μ]
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicRieszRemainder s τ hs2 (x - y)) p.1 p.2) := by
    filter_upwards [hsub, hcong] with p h1 h2
    have h3 : hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicRieszRemainder s τ hs2 (q.1 - q.2)) p =
        DGRHS.centeredKernel μ (fun x y => periodicRieszRemainder s τ hs2 (x - y)) p.1 p.2 := rfl
    rw [← h3, ← h2, h1]
    rfl
  have hcM := periodicCenteredPair_memLp_of_density_cap ρ M hρ _ hgm hg
  have hnorm := periodicCenteredPair_norm_le_of_density_cap ρ M hM hρ _ hgm hg
  have key : (hh.sub hq).toLp (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
      periodicTruncCentered μ s τ p) = hcM.toLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicRieszRemainder s τ hs2 (x - y)) p.1 p.2) :=
    MemLp.toLp_congr _ _ hae
  rw [key]
  refine hnorm.trans ?_
  have hn2 : ‖hg.toLp (periodicRieszRemainder s τ hs2)‖ ^ 2 ≤ C * τ ^ θ := by
    rw [DGRHS.Kernel.norm_toLp_sq hg]
    exact hC τ hτ hτ1
  have hb := norm_le_sqrt_mul_rpow _ C τ θ (norm_nonneg _) hC0 hτ hn2
  calc 4 * M * ‖hg.toLp (periodicRieszRemainder s τ hs2)‖
      ≤ 4 * M * (Real.sqrt C * τ ^ (θ / 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end DGRHS.Periodic
