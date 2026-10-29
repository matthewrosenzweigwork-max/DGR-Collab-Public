import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Stieltjes
import DGPS.FiniteN.OrderedOriginHardyFIN036
import DGPS.FiniteN.OrderedInnerHardyFIN037
import DGPS.FiniteN.OrderedTailHardyFIN038
import DGPS.Analysis.OneDimensionalHardy

/-!
# FIN039: ordered radial uniform LSI

For every `κ > 2` the ordered radial law `σ_N` (density `r e^{-N U(r)} / Z_N` on `(0, ∞)`) obeys
a logarithmic Sobolev inequality with a constant independent of `N ≥ 1`, a radial Poincare
inequality with half that constant, and has uniformly bounded first and second moments.

The proof anchors the three region estimates (origin, inner well, full right tail) at `r0`,
proves the right-tail estimate for every real `N ≥ 1` and the left-tail estimate for every
`N ≥ 1` (FIN036/FIN037 beyond the particle threshold, a crude origin bound below it), moves
the anchor to a median with an elementary half-mass argument, and applies the median
logarithmic-Hardy criterion (FIN007) and the resistance Poincare inequality (FIN006).
-/

open MeasureTheory Set Filter
open scoped Interval

namespace DGPS.FiniteN

/-- Normalized ordered radial density. -/
noncomputable def orderedRadialDensity_FIN039 (κ r0 N r : ℝ) : ℝ :=
  orderedRadialWeight_FIN035 κ r0 N r / orderedRadialZ_FIN035 κ r0 N

theorem orderedRadialDensity_pos_FIN039 {κ r0 N r : ℝ}
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) (hr : 0 < r) :
    0 < orderedRadialDensity_FIN039 κ r0 N r := by
  unfold orderedRadialDensity_FIN039 orderedRadialWeight_FIN035
  simp only [hr, ↓reduceIte]
  exact div_pos (mul_pos hr (Real.exp_pos _)) hZ

theorem orderedRadialDensity_continuousOn_FIN039 (κ r0 N : ℝ) :
    ContinuousOn (orderedRadialDensity_FIN039 κ r0 N) (Ioi 0) := by
  have h := ((orderedRadialWeight_continuousOn_FIN035 κ r0 N).mono
    Ioi_subset_Ici_self).div_const (orderedRadialZ_FIN035 κ r0 N)
  refine h.congr fun r hr => ?_
  have hr' : 0 < r := hr
  unfold orderedRadialDensity_FIN039 orderedRadialWeight_FIN035
  simp only [hr', ↓reduceIte]

theorem orderedRadialLaw_eq_densityMeasure_FIN039 (κ r0 N : ℝ) :
    orderedRadialLaw_FIN035 κ r0 N =
      densityMeasure (Ioi 0) (orderedRadialDensity_FIN039 κ r0 N) := by
  unfold densityMeasure orderedRadialLaw_FIN035
  rw [← restrict_withDensity measurableSet_Ioi]
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  have hm : Measurable (fun r => ENNReal.ofReal (orderedRadialDensity_FIN039 κ r0 N r)) :=
    ((orderedRadialWeight_measurable_FIN035 κ r0 N).div_const _).ennreal_ofReal
  rw [ae_withDensity_iff hm]
  refine Eventually.of_forall fun r hr => ?_
  by_contra h
  apply hr
  have h0 : orderedRadialWeight_FIN035 κ r0 N r = 0 := by
    have h' : ¬ 0 < r := h
    unfold orderedRadialWeight_FIN035
    simp only [h', ↓reduceIte]
  show ENNReal.ofReal (orderedRadialDensity_FIN039 κ r0 N r) = 0
  rw [orderedRadialDensity_FIN039, h0]
  simp


theorem tailLogWeight_le_one_FIN039 {t : ℝ} (ht : 0 ≤ t) : tailLogWeight t ≤ 1 := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [tailLogWeight]
  · unfold tailLogWeight
    have h1 := Real.log_le_sub_one_of_pos (x := 1 + 1 / t) (by positivity)
    have : t * Real.log (1 + 1 / t) ≤ t * (1 / t) := by
      apply mul_le_mul_of_nonneg_left _ h.le
      linarith
    rwa [mul_one_div_cancel h.ne'] at this

theorem tailLogWeight_ge_third_FIN039 {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) :
    1 / 3 ≤ tailLogWeight t := by
  have ht : 0 < t := by linarith
  unfold tailLogWeight
  have h3 : 1 ≤ 1 / t := by rw [le_div_iff₀ ht]; linarith
  have h4 : Real.log 2 ≤ Real.log (1 + 1 / t) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h5 := Real.log_two_gt_d9
  nlinarith

theorem toReal_le_one_FIN039 (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : Set ℝ) :
    (μ s).toReal ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := s))
  simpa using this

theorem anchor_shift_right_FIN039 {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a m H x : ℝ} (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (hgi : ∀ u v, 0 < u → 0 < v → IntervalIntegrable g volume u v)
    (ha : 0 < a) (hm : 0 < m) (hH : 0 ≤ H)
    (hR : ∀ y, a < y → tailLogWeight (μ (Ici y)).toReal * ∫ t in a..y, g t ≤ H)
    (hx : m < x) :
    tailLogWeight (μ (Ici x)).toReal * ∫ t in m..x, g t ≤ H + |∫ t in a..m, g t| := by
  have hxpos : 0 < x := hm.trans hx
  have hw0 : 0 ≤ tailLogWeight (μ (Ici x)).toReal := tailLogWeight_nonneg ENNReal.toReal_nonneg
  have hw1 : tailLogWeight (μ (Ici x)).toReal ≤ 1 :=
    tailLogWeight_le_one_FIN039 ENNReal.toReal_nonneg
  have hRx := hR x
  generalize tailLogWeight (μ (Ici x)).toReal = w at hw0 hw1 hRx ⊢
  have hnn : ∀ u v, 0 < u → u ≤ v → 0 ≤ ∫ t in u..v, g t := fun u v hu huv =>
    intervalIntegral.integral_nonneg huv fun t ht => hg0 t (hu.trans_le ht.1)
  rcases le_or_gt a m with ham | hma
  · have hax : a < x := lt_of_le_of_lt ham hx
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgi a m ha hm) (hgi m x hm hxpos)
    have h1 : ∫ t in m..x, g t ≤ ∫ t in a..x, g t := by
      have := hnn a m ha ham; linarith
    have := mul_le_mul_of_nonneg_left h1 hw0
    have := hRx hax
    have := abs_nonneg (∫ t in a..m, g t)
    linarith
  · have habs : |∫ t in a..m, g t| = ∫ t in m..a, g t := by
      rw [intervalIntegral.integral_symm, abs_neg]
      exact abs_of_nonneg (hnn m a hm hma.le)
    rw [habs]
    rcases lt_or_ge a x with hax | hxa
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hgi m a hm ha) (hgi a x ha hxpos)
      rw [← hsplit, mul_add]
      have h1 : w * ∫ t in m..a, g t ≤ ∫ t in m..a, g t :=
        mul_le_of_le_one_left (hnn m a hm hma.le) hw1
      have h2 := hRx hax
      linarith
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hgi m x hm hxpos) (hgi x a hxpos ha)
      have h1 : ∫ t in m..x, g t ≤ ∫ t in m..a, g t := by
        have := hnn x a hxpos hxa; linarith
      have h2 : w * ∫ t in m..x, g t ≤ ∫ t in m..x, g t :=
        mul_le_of_le_one_left (hnn m x hm hx.le) hw1
      linarith

theorem anchor_shift_left_FIN039 {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a m H x : ℝ} (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (hgi : ∀ u v, 0 < u → 0 < v → IntervalIntegrable g volume u v)
    (ha : 0 < a) (hm : 0 < m) (hH : 0 ≤ H)
    (hL : ∀ y, 0 < y → y < a → tailLogWeight (μ (Iic y)).toReal * ∫ t in y..a, g t ≤ H)
    (hx0 : 0 < x) (hx : x < m) :
    tailLogWeight (μ (Iic x)).toReal * ∫ t in x..m, g t ≤ H + |∫ t in a..m, g t| := by
  have hw0 : 0 ≤ tailLogWeight (μ (Iic x)).toReal := tailLogWeight_nonneg ENNReal.toReal_nonneg
  have hw1 : tailLogWeight (μ (Iic x)).toReal ≤ 1 :=
    tailLogWeight_le_one_FIN039 ENNReal.toReal_nonneg
  have hLx := hL x hx0
  generalize tailLogWeight (μ (Iic x)).toReal = w at hw0 hw1 hLx ⊢
  have hnn : ∀ u v, 0 < u → u ≤ v → 0 ≤ ∫ t in u..v, g t := fun u v hu huv =>
    intervalIntegral.integral_nonneg huv fun t ht => hg0 t (hu.trans_le ht.1)
  rcases le_or_gt m a with hma | ham
  · have hxa : x < a := lt_of_lt_of_le hx hma
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hgi x m hx0 hm) (hgi m a hm ha)
    have h1 : ∫ t in x..m, g t ≤ ∫ t in x..a, g t := by
      have := hnn m a hm hma; linarith
    have := mul_le_mul_of_nonneg_left h1 hw0
    have := hLx hxa
    have := abs_nonneg (∫ t in a..m, g t)
    linarith
  · have habs : |∫ t in a..m, g t| = ∫ t in a..m, g t := abs_of_nonneg (hnn a m ha ham.le)
    rw [habs]
    rcases lt_or_ge x a with hxa | hax
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hgi x a hx0 ha) (hgi a m ha hm)
      rw [← hsplit, mul_add]
      have h1 : w * ∫ t in a..m, g t ≤ ∫ t in a..m, g t :=
        mul_le_of_le_one_left (hnn a m ha ham.le) hw1
      have h2 := hLx hxa
      linarith
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hgi a x ha hx0) (hgi x m hx0 hm)
      have h1 : ∫ t in x..m, g t ≤ ∫ t in a..m, g t := by
        have := hnn a x ha hax; linarith
      have h2 : w * ∫ t in x..m, g t ≤ ∫ t in x..m, g t :=
        mul_le_of_le_one_left (hnn x m hx0 hx.le) hw1
      linarith

theorem anchor_shift_size_FIN039 {μ : Measure ℝ} [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    {a m H : ℝ} (hg0 : ∀ t, 0 < t → 0 ≤ g t)
    (ha : 0 < a) (hm : 0 < m) (hH : 0 ≤ H)
    (hR : ∀ y, a < y → tailLogWeight (μ (Ici y)).toReal * ∫ t in a..y, g t ≤ H)
    (hL : ∀ y, 0 < y → y < a → tailLogWeight (μ (Iic y)).toReal * ∫ t in y..a, g t ≤ H)
    (hmR : 1 / 2 ≤ (μ (Ici m)).toReal) (hmL : 1 / 2 ≤ (μ (Iic m)).toReal) :
    |∫ t in a..m, g t| ≤ 3 * H := by
  have hnn : ∀ u v, 0 < u → u ≤ v → 0 ≤ ∫ t in u..v, g t := fun u v hu huv =>
    intervalIntegral.integral_nonneg huv fun t ht => hg0 t (hu.trans_le ht.1)
  rcases lt_trichotomy a m with ham | rfl | hma
  · rw [abs_of_nonneg (hnn a m ha ham.le)]
    have h := hR m ham
    have h3 := tailLogWeight_ge_third_FIN039 hmR (toReal_le_one_FIN039 μ _)
    have hI := hnn a m ha ham.le
    nlinarith
  · simp only [intervalIntegral.integral_same, abs_zero]
    linarith
  · rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonneg (hnn m a hm hma.le)]
    have h := hL m hm hma
    have h3 := tailLogWeight_ge_third_FIN039 hmL (toReal_le_one_FIN039 μ _)
    have hI := hnn m a hm hma.le
    nlinarith

theorem ordered_good_lsi_poincare_FIN039 {p : ℝ → ℝ} {a H m : ℝ}
    [IsProbabilityMeasure (densityMeasure (Ioi 0) p)]
    (hp : ContinuousOn p (Ioi 0)) (hp0 : ∀ x ∈ Ioi (0 : ℝ), 0 < p x)
    (ha : 0 < a) (hH : 0 ≤ H)
    (hR : ∀ y, a < y → tailLogWeight (densityMeasure (Ioi 0) p (Ici y)).toReal *
      ∫ t in a..y, (p t)⁻¹ ≤ H)
    (hL : ∀ y, 0 < y → y < a → tailLogWeight (densityMeasure (Ioi 0) p (Iic y)).toReal *
      ∫ t in y..a, (p t)⁻¹ ≤ H)
    (hm : 0 < m)
    (hmed₁ : 1 / 2 ≤ (densityMeasure (Ioi 0) p (Iic m)).toReal)
    (hmed₂ : 1 / 2 ≤ (densityMeasure (Ioi 0) p (Ici m)).toReal)
    {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Ioi (0 : ℝ), ∀ y ∈ Ioi (0 : ℝ), f y - f x = ∫ t in x..y, f' t)
    (hf' : LocallyIntegrableOn f' (Ioi 0) volume)
    (hE : Integrable (fun x => f' x ^ 2) (densityMeasure (Ioi 0) p)) :
    homogeneousEntropy (densityMeasure (Ioi 0) p) (fun x => f x ^ 2) ≤
      ENNReal.ofReal (800 * H * ∫ x, f' x ^ 2 ∂(densityMeasure (Ioi 0) p)) ∧
    ProbabilityTheory.variance f (densityMeasure (Ioi 0) p) ≤
      16 * H * ∫ x, f' x ^ 2 ∂(densityMeasure (Ioi 0) p) := by
  set μ := densityMeasure (Ioi 0) p with hμ
  have hIo : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hIc : (Ioi (0 : ℝ)).OrdConnected := ordConnected_Ioi
  have hmI : m ∈ Ioi (0 : ℝ) := hm
  have hg0 : ∀ t, 0 < t → 0 ≤ (p t)⁻¹ := fun t ht => (inv_pos.2 (hp0 t ht)).le
  have hgi : ∀ u v, 0 < u → 0 < v → IntervalIntegrable (fun t => (p t)⁻¹) volume u v := by
    intro u v hu hv
    refine ContinuousOn.intervalIntegrable ?_
    have hsub : uIcc u v ⊆ Ioi 0 := by
      intro t ht
      rcases Set.mem_uIcc.1 ht with h | h
      · exact lt_of_lt_of_le hu h.1
      · exact lt_of_lt_of_le hv h.1
    exact ContinuousOn.inv₀ (hp.mono hsub) (fun t ht => (hp0 t (hsub ht)).ne')
  have hS := anchor_shift_size_FIN039 (μ := μ) hg0 ha hm hH hR hL hmed₂ hmed₁
  have hBR : ∀ x, m < x → tailLogWeight (μ (Ici x)).toReal * ∫ t in m..x, (p t)⁻¹ ≤ 4 * H := by
    intro x hx
    have := anchor_shift_right_FIN039 (μ := μ) hg0 hgi ha hm hH hR hx
    linarith
  have hBL : ∀ x, 0 < x → x < m →
      tailLogWeight (μ (Iic x)).toReal * ∫ t in x..m, (p t)⁻¹ ≤ 4 * H := by
    intro x hx0 hx
    have := anchor_shift_left_FIN039 (μ := μ) hg0 hgi ha hm hH hL hx0 hx
    linarith
  have hBp : BddAbove ((fun x => tailLogWeight (μ (Ici x)).toReal *
      ∫ t in m..x, (p t)⁻¹) '' (Ioi 0 ∩ Ioi m)) := by
    refine ⟨4 * H, ?_⟩
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact hBR x hx
  have hBm : BddAbove ((fun x => tailLogWeight (μ (Iic x)).toReal *
      ∫ t in x..m, (p t)⁻¹) '' (Ioi 0 ∩ Iio m)) := by
    refine ⟨4 * H, ?_⟩
    rintro _ ⟨x, ⟨hx0, hx⟩, rfl⟩
    exact hBL x hx0 hx
  have hRlog : rightLogResistanceConstant (Ioi 0) p m ≤ 4 * H := by
    refine Real.sSup_le ?_ (by linarith)
    rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
    exact hBR x hx
  have hLlog : leftLogResistanceConstant (Ioi 0) p m ≤ 4 * H := by
    refine Real.sSup_le ?_ (by linarith)
    rintro _ ⟨x, ⟨hx0, hx⟩, rfl⟩
    exact hBL x hx0 hx
  have hE0 : 0 ≤ ∫ x, f' x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  constructor
  · have := median_logarithmic_hardy_lsi_criterion (I := Ioi 0) (p := p) (m := m)
      (f := f) (f' := f') hIo hIc hmI hp hp0 hmed₁ hmed₂ hBp hBm hf hf' hE
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have h := mul_le_mul_of_nonneg_right (max_le hRlog hLlog) hE0
    nlinarith
  · have hBp' : BddAbove ((fun x => (μ (Ici x)).toReal * ∫ t in m..x, (p t)⁻¹) ''
        (Ioi 0 ∩ Ioi m)) := by
      refine ⟨4 * H, ?_⟩
      rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
      have hW : 0 ≤ ∫ t in m..x, (p t)⁻¹ :=
        intervalIntegral.integral_nonneg hx.le fun t ht => hg0 t (hm.trans_le ht.1)
      have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Ici_le_half hx hmed₁)
      exact (mul_le_mul_of_nonneg_right h2 hW).trans (hBR x hx)
    have hBm' : BddAbove ((fun x => (μ (Iic x)).toReal * ∫ t in x..m, (p t)⁻¹) ''
        (Ioi 0 ∩ Iio m)) := by
      refine ⟨4 * H, ?_⟩
      rintro _ ⟨x, ⟨hx0, hx⟩, rfl⟩
      have hW : 0 ≤ ∫ t in x..m, (p t)⁻¹ :=
        intervalIntegral.integral_nonneg hx.le fun t ht => hg0 t (hx0.trans_le ht.1)
      have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Iic_le_half hx hmed₂)
      exact (mul_le_mul_of_nonneg_right h2 hW).trans (hBL x hx0 hx)
    have hP := (anchored_half_line_resistance_poincare (I := Ioi 0) (p := p) (a := m)
      hIo hIc hmI hp hp0 hBp' hBm' hf hf' hE).2.2.2
    have hRR : rightResistanceConstant (Ioi 0) p m ≤ 4 * H := by
      refine Real.sSup_le ?_ (by linarith)
      rintro _ ⟨x, ⟨_, hx⟩, rfl⟩
      have hW : 0 ≤ ∫ t in m..x, (p t)⁻¹ :=
        intervalIntegral.integral_nonneg hx.le fun t ht => hg0 t (hm.trans_le ht.1)
      have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Ici_le_half hx hmed₁)
      exact (mul_le_mul_of_nonneg_right h2 hW).trans (hBR x hx)
    have hLL : leftResistanceConstant (Ioi 0) p m ≤ 4 * H := by
      refine Real.sSup_le ?_ (by linarith)
      rintro _ ⟨x, ⟨hx0, hx⟩, rfl⟩
      have hW : 0 ≤ ∫ t in x..m, (p t)⁻¹ :=
        intervalIntegral.integral_nonneg hx.le fun t ht => hg0 t (hx0.trans_le ht.1)
      have h2 := self_le_tailLogWeight ENNReal.toReal_nonneg (toReal_Iic_le_half hx hmed₂)
      exact (mul_le_mul_of_nonneg_right h2 hW).trans (hBL x hx0 hx)
    have h := mul_le_mul_of_nonneg_right (max_le hRR hLL) hE0
    refine hP.trans ?_
    nlinarith

open Topology ProbabilityTheory in
/-- Every probability measure on `ℝ` has a median. -/
theorem exists_median_FIN039 (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ m : ℝ, 1 / 2 ≤ μ.real (Iic m) ∧ 1 / 2 ≤ μ.real (Ici m) := by
  set F := cdf μ with hF
  have hmono : Monotone F := monotone_cdf μ
  have hS : ∃ x, 1 / 2 ≤ F x := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually
      (eventually_ge_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
    exact ⟨x, hx⟩
  obtain ⟨b, hb⟩ := (eventually_atBot.1 ((tendsto_cdf_atBot μ).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))))
  set S : Set ℝ := {x | 1 / 2 ≤ F x} with hSdef
  have hSbdd : BddBelow S := ⟨b, fun x hx => by
    by_contra h
    have := hb x (le_of_lt (not_le.1 h))
    exact absurd hx (not_le.2 this)⟩
  have hSne : S.Nonempty := hS
  set m := sInf S with hm
  have hmS : 1 / 2 ≤ F m := by
    have hev : ∀ᶠ x in 𝓝[>] m, 1 / 2 ≤ F x := by
      filter_upwards [self_mem_nhdsWithin (s := Ioi m) (a := m)] with x hx
      obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hSne (show sInf S < x from hx)
      exact hs.trans (hmono hsx.le)
    have ht : Tendsto F (𝓝[>] m) (𝓝 (F m)) :=
      ((cdf μ).right_continuous m).mono Ioi_subset_Ici_self |>.tendsto
    exact ge_of_tendsto ht hev
  have hlt : ∀ x < m, F x < 1 / 2 := by
    intro x hx
    by_contra h
    exact absurd (csInf_le hSbdd (not_lt.1 h)) (not_le.2 hx)
  refine ⟨m, ?_, ?_⟩
  · rw [← cdf_eq_real]; exact hmS
  · have hleft : Function.leftLim (cdf μ) m ≤ 1 / 2 := by
      have ht := (hmono.tendsto_leftLim m)
      refine le_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin (s := Iio m) (a := m)] with x hx
      exact (hlt x hx).le
    have h1 := (cdf μ).measure_Ici (tendsto_cdf_atTop μ) m
    rw [measure_cdf] at h1
    rw [Measure.real, h1, ENNReal.toReal_ofReal (by
      have := (hmono.leftLim_le (le_refl m)).trans (cdf_le_one μ m); linarith)]
    linarith

theorem log_one_add_le_two_sqrt_FIN039 {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1 + u) ≤ 2 * Real.sqrt u := by
  have h1 : Real.sqrt (1 + u) ≤ 1 + Real.sqrt u := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg u]
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by linarith : 0 < 1 + u))
  rw [Real.log_sqrt (by linarith)] at h2
  linarith

theorem tailLogWeight_le_two_sqrt_FIN039 {t : ℝ} (ht : 0 ≤ t) :
    tailLogWeight t ≤ 2 * Real.sqrt t := by
  rcases ht.eq_or_lt with h | h
  · subst h; simp [tailLogWeight]
  · unfold tailLogWeight
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 h
    have h1 := log_one_add_le_two_sqrt_FIN039 (u := 1 / t) (by positivity)
    rw [Real.sqrt_div' _ h.le, Real.sqrt_one] at h1
    have h2 : t * Real.log (1 + 1 / t) ≤ t * (2 * (1 / Real.sqrt t)) :=
      mul_le_mul_of_nonneg_left h1 h.le
    refine h2.trans (le_of_eq ?_)
    have : t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt h.le).symm
    field_simp
    nlinarith [this]

/-- Crude mass bound near the origin: the density is at most `r` for any `N ≥ 0`. -/
theorem orderedMass_Iic_le_FIN039 {κ r0 N y : ℝ}
    (hU0 : ∀ r, 0 ≤ r → 0 ≤ radialU_orad κ r0 r) (hN : 0 ≤ N) (hy : 0 ≤ y)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N)) :
    (∫ r in Iic y, orderedRadialWeight_FIN035 κ r0 N r) ≤ y ^ 2 / 2 := by
  have hind : Integrable ((Icc 0 y).indicator (fun r : ℝ => r)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact continuous_id.integrableOn_Icc
  have hle : ∀ r ∈ Iic y, orderedRadialWeight_FIN035 κ r0 N r ≤
      (Icc 0 y).indicator (fun r : ℝ => r) r := by
    intro r hr
    by_cases h0 : 0 < r
    · have hry : r ∈ Icc 0 y := ⟨h0.le, hr⟩
      rw [indicator_of_mem hry]
      unfold orderedRadialWeight_FIN035
      simp only [h0, ↓reduceIte]
      have : Real.exp (-N * radialU_orad κ r0 r) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hU0 r h0.le
        nlinarith
      nlinarith
    · have h' : ¬ 0 < r := h0
      have : orderedRadialWeight_FIN035 κ r0 N r = 0 := by
        unfold orderedRadialWeight_FIN035
        simp only [h', ↓reduceIte]
      rw [this]
      exact indicator_nonneg (fun s hs => hs.1) r
  calc (∫ r in Iic y, orderedRadialWeight_FIN035 κ r0 N r)
      ≤ ∫ r in Iic y, (Icc 0 y).indicator (fun r : ℝ => r) r :=
        setIntegral_mono_on hi.integrableOn hind.integrableOn measurableSet_Iic hle
    _ = ∫ r in Iic y ∩ Icc 0 y, r := setIntegral_indicator measurableSet_Icc
    _ = ∫ r in Icc 0 y, r := by
        rw [inter_eq_right.2 (fun r hr => hr.2)]
    _ = y ^ 2 / 2 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy]
        simp

/-- Crude left product bound, valid for every `0 < N ≤ N0` (not uniform in `N0`). -/
theorem orderedLeft_crude_product_FIN039 {κ r0 N N0 C y B : ℝ}
    (hr0 : 0 < r0) (hC : 0 ≤ C)
    (hU0 : ∀ r, 0 ≤ r → 0 ≤ radialU_orad κ r0 r)
    (hUC : ∀ r, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2)
    (hN : 0 < N) (hNN : N ≤ N0) (hy : 0 < y) (hyr : y ≤ r0)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N))
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) (hZB : orderedRadialZ_FIN035 κ r0 N ≤ B) :
    (orderedRadialLaw_FIN035 κ r0 N).real (Iic y) *
      (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
        orderedRadialZ_FIN035 κ r0 N)) *
      Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 N).real (Iic y)) ≤
      Real.sqrt (2 * B) * Real.exp (N0 * (C * r0 ^ 2)) * r0 := by
  set Z := orderedRadialZ_FIN035 κ r0 N with hZdef
  set T := (orderedRadialLaw_FIN035 κ r0 N).real (Iic y) with hT
  set E := Real.exp (N0 * (C * r0 ^ 2)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hTmass : T = (∫ r in Iic y, orderedRadialWeight_FIN035 κ r0 N r) / Z :=
    orderedRadialLaw_mass_FIN035 hi hZ measurableSet_Iic
  have hT0 : 0 ≤ T := by
    rw [hTmass]
    exact div_nonneg (setIntegral_nonneg measurableSet_Iic
      (fun r _ => orderedRadialWeight_nonneg_FIN035 _ _ _ _)) hZ.le
  have hTle : T ≤ y ^ 2 / 2 / Z := by
    rw [hTmass]
    exact div_le_div_of_nonneg_right (orderedMass_Iic_le_FIN039 hU0 hN.le hy.le hi) hZ.le
  have hs2 : 0 < Real.sqrt (2 * Z) := Real.sqrt_pos.2 (by positivity)
  have hs2sq : Real.sqrt (2 * Z) ^ 2 = 2 * Z := Real.sq_sqrt (by positivity)
  have hsT : Real.sqrt T ≤ y / Real.sqrt (2 * Z) := by
    have h1 : Real.sqrt T ≤ Real.sqrt (y ^ 2 / (2 * Z)) := by
      apply Real.sqrt_le_sqrt
      calc T ≤ y ^ 2 / 2 / Z := hTle
        _ = y ^ 2 / (2 * Z) := by field_simp
    rwa [Real.sqrt_div' _ (by positivity : 0 ≤ 2 * Z), Real.sqrt_sq hy.le] at h1
  -- resistance bound
  have hrec : ∀ r ∈ Icc y r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z) ≤ Z * E / y := by
    intro r hr
    have hrpos : 0 < r := hy.trans_le hr.1
    rw [orderedOrigin_reciprocal_value_FIN036 hrpos hZ]
    have hUr : radialU_orad κ r0 r ≤ C * r0 ^ 2 := by
      refine (hUC r hrpos.le).trans (mul_le_mul_of_nonneg_left ?_ hC)
      nlinarith [hr.2, hrpos]
    have hexp : Real.exp (N * radialU_orad κ r0 r) ≤ E := by
      apply Real.exp_le_exp.2
      have h1 := hU0 r hrpos.le
      have : N * radialU_orad κ r0 r ≤ N0 * radialU_orad κ r0 r :=
        mul_le_mul_of_nonneg_right hNN h1
      have h2 : N0 * radialU_orad κ r0 r ≤ N0 * (C * r0 ^ 2) :=
        mul_le_mul_of_nonneg_left hUr (hN.le.trans hNN)
      linarith
    calc Z * (Real.exp (N * radialU_orad κ r0 r) / r)
        ≤ Z * (E / y) := by
          apply mul_le_mul_of_nonneg_left _ hZ.le
          exact div_le_div₀ hEpos.le hexp hy hr.1
      _ = Z * E / y := by ring
  have hint := orderedOrigin_reciprocal_integrable_FIN036 hy hyr hZ
    (κ := κ) (r0 := r0) (N := N)
  have hJ0 : 0 ≤ ∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z) := by
    apply intervalIntegral.integral_nonneg hyr
    intro r hr
    have hrpos : 0 < r := hy.trans_le hr.1
    rw [orderedOrigin_reciprocal_value_FIN036 hrpos hZ]
    positivity
  have hJ : (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z)) ≤
      Z * E * r0 / y := by
    calc (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z))
        ≤ ∫ r in y..r0, Z * E / y := by
          apply intervalIntegral.integral_mono_on hyr hint intervalIntegrable_const
          exact hrec
      _ = (r0 - y) * (Z * E / y) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ r0 * (Z * E / y) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Z * E * r0 / y := by ring
  -- assemble
  have hprod : T * (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z)) *
      Real.log (1 + 1 / T) =
      (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z)) * tailLogWeight T := by
    unfold tailLogWeight; ring
  rw [hprod]
  have htw := tailLogWeight_le_two_sqrt_FIN039 hT0
  have htw' : tailLogWeight T ≤ 2 * (y / Real.sqrt (2 * Z)) := by
    have := mul_le_mul_of_nonneg_left hsT (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hTW0 : 0 ≤ tailLogWeight T := by
    unfold tailLogWeight
    exact mul_nonneg hT0 (Real.log_nonneg (by
      have : 0 ≤ 1 / T := by positivity
      linarith))
  have hfin : (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 N r / Z)) *
      tailLogWeight T ≤ (Z * E * r0 / y) * (2 * (y / Real.sqrt (2 * Z))) := by
    apply mul_le_mul hJ htw' hTW0 (by positivity)
  refine hfin.trans ?_
  have heq : (Z * E * r0 / y) * (2 * (y / Real.sqrt (2 * Z))) =
      Real.sqrt (2 * Z) * E * r0 := by
    field_simp
    nlinarith [hs2sq, Real.sq_sqrt (show 0 ≤ Z * 2 by positivity)]
  rw [heq]
  have : Real.sqrt (2 * Z) ≤ Real.sqrt (2 * B) := Real.sqrt_le_sqrt (by linarith)
  have hr0E : 0 ≤ E * r0 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right this hr0E]


/-- Basic all-`N ≥ 1` facts: normalization, partition-function bounds and moments. -/
theorem ordered_basic_allN_FIN039 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    (∀ r : ℝ, 0 < r → r = κ * DGPS.Circle.BesselMoments.besselRatio r → r = r0) ∧
    ∃ C Bn M : ℝ, 0 ≤ C ∧ 0 < Bn ∧ 0 < M ∧
      (∀ r : ℝ, 0 ≤ r → 0 ≤ radialU_orad κ r0 r) ∧
      (∀ r : ℝ, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2) ∧
      ∀ N : ℝ, 1 ≤ N →
        IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 N) ∧
        0 < orderedRadialZ_FIN035 κ r0 N ∧
        orderedRadialZ_FIN035 κ r0 N ≤ Bn ∧
        Integrable (orderedRadialWeight_FIN035 κ r0 N) ∧
        (∀ j : ℕ, j ≤ 2 →
          Integrable (fun r : ℝ => r ^ j) (orderedRadialLaw_FIN035 κ r0 N) ∧
          (∫ r, r ^ j ∂orderedRadialLaw_FIN035 κ r0 N) ≤ M) := by
  obtain ⟨r0, hr0, hroot, huniq, -, -, -, -, -, -, -⟩ := ordered_radial_well_geometry hκ
  obtain ⟨c, C, hc, hcC, horigin, hwell, hquad⟩ := well_estimates_orad hκ hr0 hroot
  have hC : 0 ≤ C := hc.le.trans hcC
  obtain ⟨Bn, hBn, hBnu⟩ : ∃ Bn : ℝ, 0 < Bn ∧ ∫ u, orderedEnvelope_FIN035 r0 c u ≤ Bn :=
    ⟨max (∫ u, orderedEnvelope_FIN035 r0 c u) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      le_max_left _ _⟩
  refine ⟨r0, hr0, hroot, huniq, C, Bn, Bn * Real.exp C / r0, hC, hBn, by positivity,
    fun r hr => (mul_nonneg hc.le (sq_nonneg _)).trans (hquad r hr).1,
    fun r hr => (hquad r hr).2, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hs1 : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hZl := orderedRadialZ_lower_FIN035 hr0 hc hC hs1 (fun r hr => (hquad r hr).1)
    (fun r hr => (hquad r hr).2)
  have hZu0 := orderedRadialZ_upper_FIN035 hr0 hc hs1 (fun r hr => (hquad r hr).1)
  rw [Real.sq_sqrt hNpos.le] at hZl hZu0
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 N :=
    (div_pos (mul_pos hr0 (Real.exp_pos _)) hs).trans_le hZl
  have hZu : orderedRadialZ_FIN035 κ r0 N ≤ Bn := by
    refine hZu0.trans ((div_le_div_of_nonneg_right hBnu hs.le).trans ?_)
    exact div_le_self hBn.le hs1
  have hi2 : Integrable (orderedRadialWeight_FIN035 κ r0 (Real.sqrt N ^ 2)) :=
    orderedRadialWeight_integrable_FIN035 hr0 hc hs1 (fun r hr => (hquad r hr).1)
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 N) := by
    simpa only [Real.sq_sqrt hNpos.le] using hi2
  refine ⟨orderedRadialLaw_probability_FIN035 hi hZ, hZ, hZu, hi, ?_⟩
  intro j hj
  obtain ⟨hij, hbound⟩ := orderedRawMoment_upper_FIN035 hr0 hc hs1
    (fun r hr => (hquad r hr).1) j hj
  rw [Real.sq_sqrt hNpos.le] at hij hbound
  refine ⟨orderedRadialLaw_integrable_FIN035 hZ _ hij, ?_⟩
  rw [orderedRadialLaw_integral_FIN035 hZ]
  -- (∫ r^j w) / Z ≤ Bn e^C / r0
  have h1 : (∫ r, r ^ j * orderedRadialWeight_FIN035 κ r0 N r) ≤ Bn / Real.sqrt N := by
    rw [le_div_iff₀ hs]
    nlinarith [hbound, hBnu]
  have hZl' : r0 * Real.exp (-C) / Real.sqrt N ≤ orderedRadialZ_FIN035 κ r0 N := hZl
  rw [div_le_div_iff₀ hZ hr0]
  have h2 : (∫ r, r ^ j * orderedRadialWeight_FIN035 κ r0 N r) * r0 ≤
      Bn / Real.sqrt N * r0 := mul_le_mul_of_nonneg_right h1 hr0.le
  have h3 : Bn * Real.exp C * orderedRadialZ_FIN035 κ r0 N ≥
      Bn * Real.exp C * (r0 * Real.exp (-C) / Real.sqrt N) :=
    mul_le_mul_of_nonneg_left hZl' (by positivity)
  have h4 : Bn * Real.exp C * (r0 * Real.exp (-C) / Real.sqrt N) = Bn / Real.sqrt N * r0 := by
    rw [Real.exp_neg]
    field_simp
  linarith


/-- The full left tail for every positive integer `N`: FIN036/FIN037 beyond the particle
threshold, and the crude origin bound below it. -/
theorem ordered_left_tail_allN_FIN039 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ H : ℝ, 0 < H ∧ ∀ N : ℕ+, ∀ y : ℝ, 0 < y → y < r0 →
      IntervalIntegrable (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
        orderedRadialZ_FIN035 κ r0 (N : ℝ))) volume y r0 ∧
      (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic y) *
        (∫ r in y..r0, 1 / (orderedRadialWeight_FIN035 κ r0 (N : ℝ) r /
          orderedRadialZ_FIN035 κ r0 (N : ℝ))) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 (N : ℝ)).real (Iic y)) ≤ H := by
  obtain ⟨r0, hr0, hroot, huniq, -, -, -, -, -, -, -⟩ := ordered_radial_well_geometry hκ
  obtain ⟨r1, hr1, hroot1, A1, B1, D1, H1, Km, Dm, N36,
    hA1, hB1, hD1, hH1, hKm, hDm, hN36, h36⟩ := ordered_origin_logarithmic_hardy_product hκ
  have e1 : r1 = r0 := huniq r1 hr1 hroot1
  subst e1
  obtain ⟨r2, hr2, hroot2, A2, B2, R2, H2, Q2, K2, D2, N37,
    hA2, hB2, hR2, hH2, hQ2, hK2, hD2, hN37, h37⟩ :=
    ordered_inner_well_logarithmic_hardy_product hκ
  have e2 : r2 = r1 := huniq r2 hr2 hroot2
  subst e2
  obtain ⟨r3, hr3, hroot3, huniq3, C, Bn, M, hC, hBn, hM, hU0, hUC, hbasic⟩ :=
    ordered_basic_allN_FIN039 hκ
  have e3 : r3 = r2 := huniq r3 hr3 hroot3
  subst e3
  let N0 := max N36 N37
  let H := max (max H1 Q2) (Real.sqrt (2 * Bn) * Real.exp (N0 * (C * r3 ^ 2)) * r3)
  have hN0 : 0 < N0 := hN36.trans_le (le_max_left _ _)
  have hHpos : 0 < H := lt_of_lt_of_le (lt_of_lt_of_le hH1 (le_max_left _ _))
    (le_max_left _ _)
  refine ⟨r3, hr3, hroot3, H, hHpos, ?_⟩
  intro N y hy hyr
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  obtain ⟨hprob, hZ, hZB, hi, -⟩ := hbasic (N : ℝ) hN1
  by_cases hNN : (N : ℝ) < N0
  · -- crude regime
    refine ⟨orderedOrigin_reciprocal_integrable_FIN036 hy hyr.le hZ, ?_⟩
    refine (orderedLeft_crude_product_FIN039 hr3 hC hU0 hUC hNpos hNN.le hy hyr.le hi hZ hZB).trans ?_
    exact (le_max_right _ _)
  · have hNN' : N0 ≤ (N : ℝ) := not_lt.1 hNN
    by_cases hya : y ≤ r3 / 2
    · obtain ⟨-, -, -, hII, -, -, -, -, -, hhardy, -, -, hEq⟩ :=
        (h36 N ((le_max_left _ _).trans hNN')).1 y hy hya
      exact ⟨hII, hEq.trans_le (hhardy.trans ((le_max_left _ _).trans (le_max_left _ _)))⟩
    · have hym : y ∈ Icc (r3 / 2) r3 := ⟨(not_le.1 hya).le, hyr.le⟩
      obtain ⟨-, -, -, hx, -⟩ := h37 N ((le_max_right _ _).trans hNN')
      obtain ⟨-, -, -, -, -, -, -, -, -, hII, -, -, -, hhardy⟩ := hx y hym
      refine ⟨hII, hhardy.trans ?_⟩
      have : Q2 / (N : ℝ) ≤ Q2 := div_le_self hQ2.le hN1
      exact this.trans ((le_max_right _ _).trans (le_max_left _ _))

theorem ordered_right_tail_allN_FIN039 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    (∀ r : ℝ, 0 < r → r = κ * DGPS.Circle.BesselMoments.besselRatio r → r = r0) ∧
    ∃ Q : ℝ, 0 < Q ∧ ∀ N : ℝ, 1 ≤ N →
      IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 N) ∧
      0 < orderedRadialZ_FIN035 κ r0 N ∧
      Integrable (orderedRadialWeight_FIN035 κ r0 N) ∧
      ∀ x : ℝ, r0 ≤ x →
        IntervalIntegrable (fun r => 1 / (orderedRadialWeight_FIN035 κ r0 N r /
          orderedRadialZ_FIN035 κ r0 N)) volume r0 x ∧
        (orderedRadialLaw_FIN035 κ r0 N).real (Ici x) *
          (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
            orderedRadialZ_FIN035 κ r0 N)) *
          Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 N).real (Ici x)) ≤ Q / N := by
  obtain ⟨r0, hr0, hroot, huniq, -, -, -, -, -, -, -⟩ := ordered_radial_well_geometry hκ
  obtain ⟨c, C, hc, hcC, horigin, hwell, hquad⟩ := well_estimates_orad hκ hr0 hroot
  obtain ⟨Bn, hBn, hBnu⟩ : ∃ Bn : ℝ, 0 < Bn ∧ ∫ u, orderedEnvelope_FIN035 r0 c u ≤ Bn :=
    ⟨max (∫ u, orderedEnvelope_FIN035 r0 c u) 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      le_max_left _ _⟩
  have hC : 0 ≤ C := hc.le.trans hcC
  have hf0 : radialDpsi_orad κ r0 = 0 := by
    unfold radialDpsi_orad
    have hκ0 : κ ≠ 0 := by linarith
    have : r0 / κ = DGPS.Circle.BesselMoments.besselRatio r0 :=
      (div_eq_iff hκ0).2 (by nlinarith [hroot])
    linarith
  have hlow : ∀ t, r0 ≤ t → c * (t - r0) ≤ radialDpsi_orad κ t := by
    intro t ht
    rcases ht.eq_or_lt with h | h
    · subst t
      rw [hf0]
      simp
    · obtain ⟨hl, -, -, hpos⟩ := hwell t (by linarith)
      rw [abs_of_pos (sub_pos.mpr h), abs_of_pos (hpos h)] at hl
      exact hl
  have hup : ∀ t, r0 ≤ t → radialDpsi_orad κ t ≤ (t - r0) / 2 :=
    fun t ht => orderedTail_dpsi_upper_FIN038 hκ hr0 hroot ht
  let A := Real.exp (-1)
  let B := Real.exp (c / 2) * (2 / c + 4 / (c ^ 2 * r0))
  let R := (2 * (r0 + 1) * (1 + 1 / (3 * c / 8) + 2 / (3 * c / 8) ^ 2) / r0) +
    2 * (1 + 4 / c)
  let H := 1 + Real.log (1 + Bn * Real.exp 1 / r0) + C
  let Q := B * R * (H + 1)
  have hA : 0 < A := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hH : 0 < H := by
    have hl : 0 ≤ Real.log (1 + Bn * Real.exp 1 / r0) :=
      Real.log_nonneg (by have : 0 < Bn * Real.exp 1 / r0 := by positivity
                          linarith)
    dsimp [H]
    linarith
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨r0, hr0, hroot, huniq, Q, hQ, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN
  have hs1 : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hZl := orderedRadialZ_lower_FIN035 hr0 hc hC hs1 (fun r hr => (hquad r hr).1)
    (fun r hr => (hquad r hr).2)
  have hZu0 := orderedRadialZ_upper_FIN035 hr0 hc hs1 (fun r hr => (hquad r hr).1)
  rw [Real.sq_sqrt hNpos.le] at hZl hZu0
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 N :=
    (div_pos (mul_pos hr0 (Real.exp_pos _)) hs).trans_le hZl
  have hZu : orderedRadialZ_FIN035 κ r0 N ≤ Bn / Real.sqrt N :=
    hZu0.trans (div_le_div_of_nonneg_right hBnu hs.le)
  have hi2 : Integrable (orderedRadialWeight_FIN035 κ r0 (Real.sqrt N ^ 2)) :=
    orderedRadialWeight_integrable_FIN035 hr0 hc hs1 (fun r hr => (hquad r hr).1)
  have hi : Integrable (orderedRadialWeight_FIN035 κ r0 N) := by
    simpa only [Real.sq_sqrt hNpos.le] using hi2
  refine ⟨orderedRadialLaw_probability_FIN035 hi hZ, hZ, hi, ?_⟩
  intro x hx
  let s := Real.sqrt N
  let q := s * (x - r0)
  let T := orderedTailMass_FIN038 κ r0 N x
  let J := orderedTailResistance_FIN038 κ r0 N x
  have hxpos : 0 < x := hr0.trans_le hx
  have hq : 0 ≤ q := mul_nonneg hs.le (sub_nonneg.mpr hx)
  have hs2 : s ^ 2 = N := Real.sq_sqrt hNpos.le
  have hTl0 := orderedTail_lower_FIN038 hr0 hs1 hx hup hi2
  have hTu0 := orderedTail_upper_FIN038 hr0 hc hs1 hx hlow hi2
  have hJu0 := orderedTailResistance_upper_FIN038 hr0 hc hs1 hx hlow
  have hTlN : A * (x * (Real.exp (-N * radialU_orad κ r0 x) /
      (s * (1 + q)))) ≤ T := by
    rwa [hs2] at hTl0
  have hTuN : T ≤ B * (x * (Real.exp (-N * radialU_orad κ r0 x) /
      (s * (1 + q)))) := by
    rwa [hs2] at hTu0
  have hJuN : J ≤ R * (Real.exp (N * radialU_orad κ r0 x) /
      (x * (s * (1 + q)))) := by
    rwa [hs2] at hJu0
  have hTl : (x * A) * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) ≤ T := by
    rw [hs2]
    have h := hTlN
    rw [← mul_assoc, mul_comm A x] at h
    exact h
  have hTu : T ≤ (B * x) * (Real.exp (-(s ^ 2) * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    rw [hs2]
    have h := hTuN
    rw [← mul_assoc] at h
    exact h
  have hJu : J ≤ (R / x) * (Real.exp (s ^ 2 * radialU_orad κ r0 x) /
      (s * (1 + q))) := by
    rw [hs2]
    refine hJuN.trans (le_of_eq ?_)
    field_simp
  have hden : 0 < s * (1 + q) := by positivity
  have hTpos : 0 < T :=
    (mul_pos hA (mul_pos hxpos (div_pos (Real.exp_pos _) (by positivity)))).trans_le hTlN
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg hx
    intro r hr
    exact div_nonneg (Real.exp_pos _).le (by linarith [hr.1])
  have hU : s ^ 2 * radialU_orad κ r0 x ≤ C * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left (hquad x hxpos.le).2 (sq_nonneg s)
    calc
      s ^ 2 * radialU_orad κ r0 x ≤ s ^ 2 * (C * (x - r0) ^ 2) := this
      _ = C * q ^ 2 := by dsimp [q]; ring
  have hlog0 := orderedInner_log_bound_FIN037 (A := x * A) (mul_pos hxpos hA) hBn hC hs hq
    hZ hZu hTl hU
  have hlogstep : Real.log (1 + Bn / (x * A)) ≤ Real.log (1 + Bn * Real.exp 1 / r0) := by
    apply Real.log_le_log (by have : 0 < Bn / (x * A) := by positivity
                              linarith)
    have : Bn / (x * A) = Bn * Real.exp 1 / x := by
      dsimp [A]
      rw [Real.exp_neg]
      field_simp
    rw [this]
    have h2 : Bn * Real.exp 1 / x ≤ Bn * Real.exp 1 / r0 :=
      div_le_div_of_nonneg_left (by positivity) hr0 hx
    linarith
  have hlog : Real.log (1 + orderedRadialZ_FIN035 κ r0 N / T) ≤
      H * (1 + q ^ 2) + Real.log (1 + q) := by
    have hq2 : 0 ≤ 1 + q ^ 2 := by positivity
    have hcoef : 1 + Real.log (1 + Bn / (x * A)) + C ≤ H := by
      dsimp [H]; linarith
    calc
      Real.log (1 + orderedRadialZ_FIN035 κ r0 N / T)
          ≤ (1 + Real.log (1 + Bn / (x * A)) + C) * (1 + q ^ 2) + Real.log (1 + q) :=
        hlog0
      _ ≤ H * (1 + q ^ 2) + Real.log (1 + q) := by
        have := mul_le_mul_of_nonneg_right hcoef hq2
        linarith
  have hhardy := orderedInner_hardy_algebra_FIN037 (mul_pos hB hxpos).le
    (div_pos hR hxpos).le hH.le hs hq hTpos hJ hZ hTu hJu hlog
  have hxR : B * x * (R / x) = B * R := by field_simp
  have hhprod : T * J ≤ B * R / (N * (1 + q) ^ 2) := by
    have h := hhardy.1
    rw [hxR, hs2] at h
    exact h
  have hrawhardy : T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 N / T) ≤
      Q / N := by
    have h := hhardy.2
    rw [hxR, hs2] at h
    exact h
  have hxi : IntervalIntegrable
      (fun r => Real.exp (N * radialU_orad κ r0 r) / r) volume r0 x :=
    orderedResistance_integrable_FIN035 hr0 hxpos
  have hlaw := orderedTailMass_law_FIN038 (κ := κ) (r0 := r0) (N := N) hxpos hi hZ
  have hnormalized := orderedTail_normalized_resistance_FIN038 (κ := κ) (N := N)
    hr0 hx hZ
  have hcancel :
      (orderedRadialLaw_FIN035 κ r0 N).real (Ici x) *
        (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
          orderedRadialZ_FIN035 κ r0 N)) = T * J := by
    rw [hlaw, hnormalized.2]
    change (T / orderedRadialZ_FIN035 κ r0 N) *
      (orderedRadialZ_FIN035 κ r0 N * J) = T * J
    field_simp [hZ.ne']
  have hlognormalized :
      Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 N).real (Ici x)) =
        Real.log (1 + orderedRadialZ_FIN035 κ r0 N / T) := by
    rw [hlaw]
    congr 1
    change 1 + 1 / (T / orderedRadialZ_FIN035 κ r0 N) =
      1 + orderedRadialZ_FIN035 κ r0 N / T
    field_simp [hTpos.ne', hZ.ne']
  have hnormalizedproduct :
      (orderedRadialLaw_FIN035 κ r0 N).real (Ici x) *
        (∫ r in r0..x, 1 / (orderedRadialWeight_FIN035 κ r0 N r /
          orderedRadialZ_FIN035 κ r0 N)) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r0 N).real (Ici x)) =
          T * J * Real.log (1 + orderedRadialZ_FIN035 κ r0 N / T) := by
    rw [hcancel, hlognormalized]
  have hnormalizedhardy := hnormalizedproduct.le.trans hrawhardy
  exact ⟨hnormalized.1, hnormalizedhardy⟩

/-- A median of the radial law is positive, since the law lives on `(0, ∞)`. -/
theorem densityMeasure_Iic_eq_zero_FIN039 {p : ℝ → ℝ} {m : ℝ} (hm : m ≤ 0) :
    densityMeasure (Ioi 0) p (Iic m) = 0 := by
  have hac : densityMeasure (Ioi 0) p ≪ volume.restrict (Ioi (0 : ℝ)) :=
    withDensity_absolutelyContinuous _ _
  apply hac
  rw [Measure.restrict_apply measurableSet_Iic]
  have : Iic m ∩ Ioi (0 : ℝ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false, not_and, not_lt]
    intro hx
    exact hx.trans hm
  rw [this, measure_empty]

/-- FIN039: uniform (in the particle number `N ≥ 1`) logarithmic Sobolev inequality for the
ordered radial law `σ_N`, with the radial Poincaré constant at most half the LSI constant, and
uniformly bounded first and second moments. The test class is the locally absolutely
continuous functions on `(0, ∞)` (`F y - F x = ∫ₓʸ F'` with `F'` locally integrable) whose
derivative is square integrable for `σ_N`. -/
theorem ordered_radial_uniform_lsi {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * DGPS.Circle.BesselMoments.besselRatio r0 ∧
    ∃ L M : ℝ, 0 < L ∧ 0 < M ∧ ∀ N : ℕ+,
      IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
      (∀ f f' : ℝ → ℝ,
        (∀ x ∈ Ioi (0 : ℝ), ∀ y ∈ Ioi (0 : ℝ), f y - f x = ∫ t in x..y, f' t) →
        LocallyIntegrableOn f' (Ioi 0) volume →
        Integrable (fun x => f' x ^ 2) (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) →
        homogeneousEntropy (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) (fun x => f x ^ 2) ≤
          ENNReal.ofReal (L * ∫ x, f' x ^ 2 ∂orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        ProbabilityTheory.variance f (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ≤
          (L / 2) * ∫ x, f' x ^ 2 ∂orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
      (∀ j : ℕ, j ≤ 2 →
        Integrable (fun r : ℝ => r ^ j) (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        (∫ r, r ^ j ∂orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ≤ M) := by
  obtain ⟨r0, hr0, hroot, huniq, Q, hQ, hRt⟩ := ordered_right_tail_allN_FIN039 hκ
  obtain ⟨r1, hr1, hroot1, H, hH, hLt⟩ := ordered_left_tail_allN_FIN039 hκ
  have e1 : r1 = r0 := huniq r1 hr1 hroot1
  subst e1
  obtain ⟨r3, hr3, hroot3, huniq3, C, Bn, M, hC, hBn, hM, hU0, hUC, hbasic⟩ :=
    ordered_basic_allN_FIN039 hκ
  have e3 : r3 = r1 := huniq r3 hr3 hroot3
  subst e3
  let Hs := max Q H
  have hHs : 0 < Hs := lt_of_lt_of_le hQ (le_max_left _ _)
  refine ⟨r3, hr3, hroot3, 800 * Hs, M, by positivity, hM, ?_⟩
  intro N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  obtain ⟨hprob, hZ, -, hi, hmom⟩ := hbasic (N : ℝ) hN1
  obtain ⟨-, -, -, hRN⟩ := hRt (N : ℝ) hN1
  refine ⟨hprob, ?_, hmom⟩
  intro f f' hf hf' hE
  have hlaw := orderedRadialLaw_eq_densityMeasure_FIN039 κ r3 (N : ℝ)
  set p := orderedRadialDensity_FIN039 κ r3 (N : ℝ) with hp
  rw [hlaw] at hprob hE ⊢
  have hpc := orderedRadialDensity_continuousOn_FIN039 κ r3 (N : ℝ)
  have hp0 : ∀ x ∈ Ioi (0 : ℝ), 0 < p x := fun x hx => orderedRadialDensity_pos_FIN039 hZ hx
  have hinv : (fun t => (p t)⁻¹) =
      fun t => 1 / (orderedRadialWeight_FIN035 κ r3 (N : ℝ) t /
        orderedRadialZ_FIN035 κ r3 (N : ℝ)) := by
    funext t
    simp only [hp, orderedRadialDensity_FIN039, one_div]
  have hrealR : ∀ S : Set ℝ, (densityMeasure (Ioi 0) p S).toReal =
      (orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real S := by
    intro S
    rw [hlaw]
    rfl
  obtain ⟨m, hm1, hm2⟩ := exists_median_FIN039 (densityMeasure (Ioi 0) p)
  have hmpos : 0 < m := by
    by_contra h
    have h0 := densityMeasure_Iic_eq_zero_FIN039 (p := p) (not_lt.1 h)
    have : (1 / 2 : ℝ) ≤ 0 := by
      have := hm1
      simp only [Measure.real, h0, ENNReal.toReal_zero] at this
      exact this
    linarith
  have hQN : Q / (N : ℝ) ≤ Q := div_le_self hQ.le hN1
  have key := ordered_good_lsi_poincare_FIN039 (p := p) (a := r3) (H := Hs) (m := m) hpc hp0 hr3
    hHs.le ?_ ?_ hmpos hm1 hm2 hf hf' hE
  · obtain ⟨hent, hvar⟩ := key
    refine ⟨?_, ?_⟩
    · convert hent using 3
    · have hE0 : 0 ≤ ∫ x, f' x ^ 2 ∂densityMeasure (Ioi 0) p :=
        integral_nonneg (fun x => sq_nonneg _)
      have := mul_le_mul_of_nonneg_right (by linarith : 16 * Hs ≤ 800 * Hs / 2) hE0
      linarith
  · intro y hy
    obtain ⟨-, hprod⟩ := hRN y hy.le
    rw [hrealR, hinv]
    have heq : tailLogWeight ((orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Ici y)) *
        (∫ t in r3..y, 1 / (orderedRadialWeight_FIN035 κ r3 (N : ℝ) t /
          orderedRadialZ_FIN035 κ r3 (N : ℝ))) =
        (orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Ici y) *
        (∫ t in r3..y, 1 / (orderedRadialWeight_FIN035 κ r3 (N : ℝ) t /
          orderedRadialZ_FIN035 κ r3 (N : ℝ))) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Ici y)) := by
      unfold tailLogWeight; ring
    rw [heq]
    exact (hprod.trans hQN).trans (le_max_left _ _)
  · intro y hy hya
    obtain ⟨-, hprod⟩ := hLt N y hy hya
    rw [hrealR, hinv]
    have heq : tailLogWeight ((orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Iic y)) *
        (∫ t in y..r3, 1 / (orderedRadialWeight_FIN035 κ r3 (N : ℝ) t /
          orderedRadialZ_FIN035 κ r3 (N : ℝ))) =
        (orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Iic y) *
        (∫ t in y..r3, 1 / (orderedRadialWeight_FIN035 κ r3 (N : ℝ) t /
          orderedRadialZ_FIN035 κ r3 (N : ℝ))) *
        Real.log (1 + 1 / (orderedRadialLaw_FIN035 κ r3 (N : ℝ)).real (Iic y)) := by
      unfold tailLogWeight; ring
    rw [heq]
    exact hprod.trans (le_max_right _ _)

end DGPS.FiniteN
