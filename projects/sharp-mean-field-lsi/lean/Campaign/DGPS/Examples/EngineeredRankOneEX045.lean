import DGPS.Examples.EngineeredRankOneEX044
import DGPS.Examples.EngineeredCentralLSI

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization
open DGPS.Circle.StationaryFlux

namespace DGPS.Examples.EngineeredRankOneEX045

/-- Periodization of a function supported in `(-π/2, π/2)`: its value at the representative
of `θ` in `(-π, π]`. -/
noncomputable def perTest_EX045 (ψ : ℝ → ℝ) (θ : AngCircle) : ℝ :=
  ψ ((AddCircle.equivIoc (2 * π) (-π) θ : Ioc (-π) (-π + 2 * π)) : ℝ)

lemma perTest_coe_EX045 (ψ : ℝ → ℝ) {s : ℝ} (hs : s ∈ Ioc (-π) π) :
    perTest_EX045 ψ (s : AngCircle) = ψ s := by
  unfold perTest_EX045
  have hs' : s ∈ Ioc (-π) (-π + 2 * π) := by
    constructor
    · exact hs.1
    · linarith [hs.2]
  rw [AddCircle.equivIoc_coe_of_mem (p := 2 * π) (a := -π) hs']

lemma perTest_periodic_EX045 (ψ : ℝ → ℝ) :
    Function.Periodic (fun s : ℝ => perTest_EX045 ψ (s : AngCircle)) (2 * π) := by
  intro s
  simp only [AddCircle.coe_add_period]

lemma vanish_EX045 {ψ : ℝ → ℝ} (hts : tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2)) {t : ℝ}
    (ht : π / 2 ≤ |t|) : ψ t = 0 ∧ deriv ψ t = 0 := by
  have hn : t ∉ tsupport ψ := fun h => by
    have := hts h
    rw [mem_Ioo, ← abs_lt] at this
    linarith [this]
  exact ⟨image_eq_zero_of_notMem_tsupport hn,
    image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))⟩

lemma perTest_local_EX045 {ψ : ℝ → ℝ}
    (hs : ∀ t, π / 2 ≤ |t| → ψ t = 0) : ∀ s : ℝ, |s| < 3 * π / 2 →
      perTest_EX045 ψ (s : AngCircle) = ψ (s - 2 * π) + ψ s + ψ (s + 2 * π) := by
  have hper := perTest_periodic_EX045 ψ
  have hpi := Real.pi_pos
  intro s hs3
  rw [abs_lt] at hs3
  by_cases h1 : s ∈ Ioc (-π) π
  · have e : perTest_EX045 ψ (s : AngCircle) = ψ s := perTest_coe_EX045 ψ h1
    rw [e, hs (s - 2 * π) (by rw [abs_of_neg (by linarith [h1.2])]; linarith [h1.2]),
      hs (s + 2 * π) (by rw [abs_of_pos (by linarith [h1.1])]; linarith [h1.1])]
    ring
  · rw [mem_Ioc, not_and_or, not_lt, not_le] at h1
    rcases h1 with h1 | h1
    · have e : perTest_EX045 ψ (s : AngCircle) = ψ (s + 2 * π) := by
        have e2 : perTest_EX045 ψ (s : AngCircle) = perTest_EX045 ψ ((s + 2 * π : ℝ) : AngCircle) :=
          (hper s).symm
        rw [e2]
        exact perTest_coe_EX045 ψ ⟨by linarith, by linarith⟩
      rw [e, hs s (by rw [abs_of_neg (by linarith)]; linarith),
        hs (s - 2 * π) (by rw [abs_of_neg (by linarith)]; linarith)]
      ring
    · have e : perTest_EX045 ψ (s : AngCircle) = ψ (s - 2 * π) := by
        have e1 : perTest_EX045 ψ (s : AngCircle) = perTest_EX045 ψ ((s - 2 * π : ℝ) : AngCircle) := by
          have := hper (s - 2 * π)
          rw [sub_add_cancel] at this
          exact this
        rw [e1]
        exact perTest_coe_EX045 ψ ⟨by linarith, by linarith⟩
      rw [e, hs s (by rw [abs_of_pos (by linarith)]; linarith),
        hs (s + 2 * π) (by rw [abs_of_pos (by linarith)]; linarith)]
      ring

lemma contDiff_perTest_EX045 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : ∀ t, π / 2 ≤ |t| → ψ t = 0) : IsSmoothAngular (perTest_EX045 ψ) := by
  unfold IsSmoothAngular
  have hper := perTest_periodic_EX045 ψ
  have hpi := Real.pi_pos
  have hL := perTest_local_EX045 hs
  have hLs : ContDiff ℝ ∞ (fun s : ℝ => ψ (s - 2 * π) + ψ s + ψ (s + 2 * π)) := by
    have h1 : ContDiff ℝ ∞ (fun s : ℝ => ψ (s - 2 * π)) :=
      hψ.comp (contDiff_id.sub contDiff_const)
    have h3 : ContDiff ℝ ∞ (fun s : ℝ => ψ (s + 2 * π)) :=
      hψ.comp (contDiff_id.add contDiff_const)
    exact (h1.add hψ).add h3
  rw [contDiff_iff_contDiffAt]
  intro s0
  set k : ℤ := round (s0 / (2 * π)) with hk
  have hr : |s0 / (2 * π) - k| ≤ 1 / 2 := abs_sub_round (s0 / (2 * π))
  have hb : |s0 - k * (2 * π)| ≤ π := by
    have : s0 - k * (2 * π) = (s0 / (2 * π) - k) * (2 * π) := by field_simp
    rw [this, abs_mul, abs_of_pos (by positivity : 0 < 2 * π)]
    nlinarith [abs_nonneg (s0 / (2 * π) - k)]
  have hca : ContDiffAt ℝ ∞ (fun s : ℝ => ψ ((s - k * (2 * π)) - 2 * π) +
      ψ (s - k * (2 * π)) + ψ ((s - k * (2 * π)) + 2 * π)) s0 :=
    (hLs.comp (contDiff_id.sub contDiff_const)).contDiffAt
  refine hca.congr_of_eventuallyEq ?_
  have hopen : IsOpen {s : ℝ | |s - k * (2 * π)| < 3 * π / 2} :=
    isOpen_lt (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds (show |s0 - k * (2 * π)| < 3 * π / 2 by linarith)] with s hs'
  have : perTest_EX045 ψ (s : AngCircle) = perTest_EX045 ψ ((s - k * (2 * π) : ℝ) : AngCircle) :=
    (hper.sub_int_mul_eq k).symm
  rw [this]
  exact hL _ hs'

/-- On `[-π, π]` the periodization agrees with `ψ` together with its derivative. -/
lemma lift_perTest_deriv_EX045 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hts : tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2)) {t : ℝ} (ht : t ∈ Icc (-π) π) :
    perTest_EX045 ψ (t : AngCircle) = ψ t ∧
      deriv (lift (perTest_EX045 ψ)) t = deriv ψ t := by
  have hpi := Real.pi_pos
  have hs : ∀ t, π / 2 ≤ |t| → ψ t = 0 := fun t h => (vanish_EX045 hts h).1
  have hL := perTest_local_EX045 hs
  have habs : |t| ≤ π := abs_le.mpr ⟨ht.1, ht.2⟩
  have hv1 : ψ (t - 2 * π) = 0 := hs _ (by
    rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])
  have hv3 : ψ (t + 2 * π) = 0 := hs _ (by
    rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1])
  have d1 : deriv ψ (t - 2 * π) = 0 := (vanish_EX045 hts (by
    rw [abs_of_neg (by linarith [ht.2])]; linarith [ht.2])).2
  have d3 : deriv ψ (t + 2 * π) = 0 := (vanish_EX045 hts (by
    rw [abs_of_pos (by linarith [ht.1])]; linarith [ht.1])).2
  refine ⟨?_, ?_⟩
  · rw [hL t (by linarith), hv1, hv3]; ring
  · have hopen : IsOpen {s : ℝ | |s| < 3 * π / 2} := isOpen_lt (by fun_prop) continuous_const
    have heq : lift (perTest_EX045 ψ) =ᶠ[𝓝 t]
        (fun s : ℝ => ψ (s - 2 * π) + ψ s + ψ (s + 2 * π)) := by
      filter_upwards [hopen.mem_nhds (show |t| < 3 * π / 2 by linarith)] with s hs'
      exact hL s hs'
    rw [heq.deriv_eq]
    have hd : Differentiable ℝ ψ := hψ.differentiable (by simp)
    have h1 : HasDerivAt (fun s : ℝ => ψ (s - 2 * π)) (deriv ψ (t - 2 * π)) t := by
      have := (hd (t - 2 * π)).hasDerivAt.comp_sub_const t (2 * π)
      exact this
    have h3 : HasDerivAt (fun s : ℝ => ψ (s + 2 * π)) (deriv ψ (t + 2 * π)) t := by
      have := (hd (t + 2 * π)).hasDerivAt.comp_add_const t (2 * π)
      exact this
    have h2 : HasDerivAt ψ (deriv ψ t) t := (hd t).hasDerivAt
    have := (h1.add h2).add h3
    have e : deriv (fun s : ℝ => ψ (s - 2 * π) + ψ s + ψ (s + 2 * π)) t =
        deriv ψ (t - 2 * π) + deriv ψ t + deriv ψ (t + 2 * π) := this.deriv
    rw [e, d1, d3]; ring

lemma cut_EX045 {F : ℝ → ℝ} (hz : ∀ t, π / 2 ≤ |t| → |t| ≤ π → F t = 0) :
    ∫ t in (-π)..π, F t = ∫ t in (-(π / 2))..(π / 2), F t := by
  have hpi := Real.pi_pos
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc ?_ ?_
  · intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro x hx
    have hxI : -π < x ∧ x ≤ π := hx.1
    have hxn : ¬ (-(π / 2) < x ∧ x ≤ π / 2) := hx.2
    apply hz
    · by_contra hlt
      rw [not_le, abs_lt] at hlt
      exact hxn ⟨hlt.1, hlt.2.le⟩
    · exact abs_le.mpr ⟨hxI.1.le, hxI.2⟩

/-- Circle weak derivative identity transported to the central interval. -/
lemma weak_interval_EX045 {u g : AngCircle → ℝ} (hw : IsAngularWeakDeriv u g)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hts : tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2)) :
    (∫ t in (-(π / 2))..(π / 2), u (t : AngCircle) * deriv ψ t) =
      -(∫ t in (-(π / 2))..(π / 2), g (t : AngCircle) * ψ t) := by
  have hpi := Real.pi_pos
  have hs : ∀ t, π / 2 ≤ |t| → ψ t = 0 := fun t h => (vanish_EX045 hts h).1
  have hd : ∀ t, π / 2 ≤ |t| → deriv ψ t = 0 := fun t h => (vanish_EX045 hts h).2
  have hib := hw.ibp (perTest_EX045 ψ) (contDiff_perTest_EX045 hψ hs)
  rw [DGPS.Examples.EngineeredRankOne.integral_angHaar_eq_interval,
    DGPS.Examples.EngineeredRankOne.integral_angHaar_eq_interval] at hib
  have h1 : ∫ t in (-π)..π, u (t : AngCircle) * angDeriv (perTest_EX045 ψ) (t : AngCircle) =
      ∫ t in (-π)..π, u (t : AngCircle) * deriv ψ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    beta_reduce
    rw [angDeriv_coe, (lift_perTest_deriv_EX045 hψ hts ht).2]
  have h2 : ∫ t in (-π)..π, g (t : AngCircle) * perTest_EX045 ψ (t : AngCircle) =
      ∫ t in (-π)..π, g (t : AngCircle) * ψ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    beta_reduce
    rw [(lift_perTest_deriv_EX045 hψ hts ht).1]
  rw [h1, h2] at hib
  have hc1 := cut_EX045 (F := fun t => u (t : AngCircle) * deriv ψ t) (fun t ht _ => by
    simp only [hd t ht, mul_zero])
  have hc2 := cut_EX045 (F := fun t => g (t : AngCircle) * ψ t) (fun t ht _ => by
    simp only [hs t ht, mul_zero])
  rw [hc1, hc2] at hib
  have hne : (2 * π)⁻¹ ≠ 0 := by positivity
  have : (2 * π)⁻¹ * (∫ t in (-(π / 2))..(π / 2), u (t : AngCircle) * deriv ψ t) =
      (2 * π)⁻¹ * (-(∫ t in (-(π / 2))..(π / 2), g (t : AngCircle) * ψ t)) := by
    rw [hib]; ring
  exact mul_left_cancel₀ hne this


open DGPS.Examples DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredGroundState
  DGPS.Examples.EngineeredHardy DGPS.Models DGPS.Examples.EngineeredRankOneEX042
  DGPS.Examples.EngineeredRankOneEX044

lemma muOf_le_EX045 {q : AngCircle → ℝ} (hc : Continuous q) (hp : ∀ θ, 0 < q θ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ muOf q ≤ c • (volume.restrict (Ioc (-π) (-π + 2 * π))) := by
  obtain ⟨m, M, hm, hmM⟩ := exists_bounds_hardy hc hp
  refine ⟨ENNReal.ofReal (M / (2 * π)), ENNReal.ofReal_ne_top, ?_⟩
  unfold muOf DGPS.FiniteN.densityMeasure
  have hpi := Real.pi_pos
  calc (volume.restrict (Ioo (-π) π)).withDensity (fun x => ENNReal.ofReal (pOf q x))
      ≤ (volume.restrict (Ioo (-π) π)).withDensity (fun _ => ENNReal.ofReal (M / (2 * π))) := by
        apply withDensity_mono
        refine Eventually.of_forall fun x => ?_
        apply ENNReal.ofReal_le_ofReal
        unfold pOf
        exact div_le_div_of_nonneg_right (hmM _).2 (by positivity)
    _ = ENNReal.ofReal (M / (2 * π)) • (volume.restrict (Ioo (-π) π)) := withDensity_const _
    _ ≤ ENNReal.ofReal (M / (2 * π)) • (volume.restrict (Ioc (-π) (-π + 2 * π))) := by
        gcongr
        exact Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc le_rfl (by linarith))

lemma memLp_circle_interval_EX045 {w : AngCircle → ℝ} {p : ℝ≥0∞} (hw : MemLp w p angHaar) :
    MemLp (fun t : ℝ => w (t : AngCircle)) p (volume.restrict (Ioc (-π) (-π + 2 * π))) := by
  have hv : MemLp w p (volume : Measure AngCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact hw.smul_measure ENNReal.ofReal_ne_top
  exact hv.comp_measurePreserving (AddCircle.measurePreserving_mk (2 * π) (-π))

lemma memLp_central_EX045 (h : ℝ) (hh : 0 < h) {w : AngCircle → ℝ} {p : ℝ≥0∞}
    (hw : MemLp w p angHaar) :
    MemLp (fun t : ℝ => w (t : AngCircle)) p (centralProbability_EX040 h hh : Measure ℝ) := by
  have hd := hardyData_qAng hh
  obtain ⟨c, hc, hle⟩ := muOf_le_EX045 hd.cont hd.pos
  have h1 := (memLp_circle_interval_EX045 hw).of_measure_le_smul hc hle
  have h2 : MemLp (fun t : ℝ => w (t : AngCircle)) p (centralRawMeasure_EX040 h) :=
    h1.mono_measure (central_raw_measure_le_EX040 h)
  rw [central_probability_coe_EX040 h hh]
  exact h2.smul_measure (by simp)


lemma intervalIntegrable_circle_EX045 {F : AngCircle → ℝ} (hF : Integrable F angHaar) :
    IntervalIntegrable (fun t : ℝ => F (t : AngCircle)) volume (-π) π := by
  have hpi := Real.pi_pos
  have hv : Integrable F (volume : Measure AngCircle) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact hF.smul_measure ENNReal.ofReal_ne_top
  have h1 := (AddCircle.measurePreserving_mk (2 * π) (-π)).integrable_comp_of_integrable hv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have e : -π + 2 * π = π := by ring
  rw [e] at h1
  exact h1

lemma central_integral_le_EX045 (h : ℝ) (hh : 0 < h) {F : AngCircle → ℝ}
    (hF0 : ∀ θ, 0 ≤ F θ) (hF : Integrable (fun θ => qAng h θ * F θ) angHaar) :
    ∫ t, F (t : AngCircle) ∂(centralProbability_EX040 h hh : Measure ℝ) ≤
      ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ * ∫ θ, qAng h θ * F θ ∂angHaar := by
  have hpi := Real.pi_pos
  have hq := (hardyData_qAng hh).pos
  have hm := central_mass_pos_EX040 h hh
  rw [central_probability_integral_q_EX040 h hh,
    DGPS.Examples.EngineeredRankOne.integral_angHaar_eq_interval]
  have hI := intervalIntegrable_circle_EX045 (F := fun θ => qAng h θ * F θ) hF
  have hI' : IntervalIntegrable (fun t : ℝ => F (t : AngCircle) * qAng h (t : AngCircle))
      volume (-π) π := hI.congr (fun t _ => mul_comm _ _)
  have hmono : ∫ x in -(π / 2)..π / 2, F (x : AngCircle) * qAng h (x : AngCircle) ≤
      ∫ x in (-π)..π, F (x : AngCircle) * qAng h (x : AngCircle) :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun t => mul_nonneg (hF0 _) (hq _).le) hI'
  have e : ∫ x in (-π)..π, qAng h (x : AngCircle) * F (x : AngCircle) =
      ∫ x in (-π)..π, F (x : AngCircle) * qAng h (x : AngCircle) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  rw [e]
  unfold centralNormFactor_EX040
  have hc : 0 ≤ ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ / (2 * π) := by positivity
  calc ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ / (2 * π) *
        ∫ x in -(π / 2)..π / 2, F (x : AngCircle) * qAng h (x : AngCircle)
      ≤ ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ / (2 * π) *
        ∫ x in (-π)..π, F (x : AngCircle) * qAng h (x : AngCircle) :=
        mul_le_mul_of_nonneg_left hmono hc
    _ = _ := by ring

lemma central_integral_eq_EX045 (h : ℝ) (hh : 0 < h) {G : AngCircle → ℝ}
    (hz : ∀ t : ℝ, π / 2 ≤ |t| → |t| ≤ π → G (t : AngCircle) = 0) :
    ∫ θ, qAng h θ * G θ ∂angHaar =
      ((centralFiniteMeasure_EX040 h hh).mass : ℝ) *
        ∫ t, G (t : AngCircle) ∂(centralProbability_EX040 h hh : Measure ℝ) := by
  have hm := central_mass_pos_EX040 h hh
  rw [central_probability_integral_q_EX040 h hh,
    DGPS.Examples.EngineeredRankOne.integral_angHaar_eq_interval]
  have hc := cut_EX045 (F := fun t : ℝ => qAng h (t : AngCircle) * G (t : AngCircle))
    (fun t ht1 ht2 => by simp only [hz t ht1 ht2, mul_zero])
  rw [hc]
  have e : ∫ x in -(π / 2)..π / 2, qAng h (x : AngCircle) * G (x : AngCircle) =
      ∫ x in -(π / 2)..π / 2, G (x : AngCircle) * qAng h (x : AngCircle) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  rw [e]
  unfold centralNormFactor_EX040
  field_simp


lemma xlog_le_EX045 {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) :
    x * Real.log (2 + x) ≤ x * (Real.log (2 + n) + 1) + DGPS.entropyIntegrand n x := by
  have hθ := DGPS.entropyIntegrand_nonneg hn hx
  by_cases hxn : x ≤ n
  · have h1 : Real.log (2 + x) ≤ Real.log (2 + n) :=
      Real.log_le_log (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 hx]
  · rw [not_le] at hxn
    have hxp : 0 < x := lt_trans hn hxn
    have h1 : Real.log (2 + x) - Real.log (2 + n) ≤ Real.log x - Real.log n := by
      rw [← Real.log_div (by linarith) (by linarith), ← Real.log_div hxp.ne' hn.ne']
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by linarith) hn]
      nlinarith
    have h2 : DGPS.entropyIntegrand n x = x * (Real.log x - Real.log n) - x + n := by
      unfold DGPS.entropyIntegrand
      rw [Real.log_div hxp.ne' hn.ne']
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    nlinarith

lemma entropy_log_int_EX045 {P : Measure ℝ} [IsProbabilityMeasure P] {x : ℝ → ℝ}
    (hx0 : ∀ t, 0 ≤ x t) (hxm : AEMeasurable x P) (hxi : Integrable x P) {e : ℝ} (he0 : 0 ≤ e)
    (he : DGPS.homogeneousEntropy P x ≤ ENNReal.ofReal e) :
    Integrable (fun t => x t * Real.log (2 + x t)) P ∧
      ∫ t, x t * Real.log (2 + x t) ∂P ≤
        e + (∫ t, x t ∂P) * (Real.log (2 + ∫ t, x t ∂P) + 1) := by
  have hn0 : 0 ≤ ∫ t, x t ∂P := integral_nonneg hx0
  have hmeas : AEStronglyMeasurable (fun t => x t * Real.log (2 + x t)) P :=
    (hxm.mul (hxm.const_add 2).log).aestronglyMeasurable
  rcases hn0.eq_or_lt with h0 | hpos
  · have hz : x =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg hx0 hxi).mp h0.symm
    have hz2 : (fun t => x t * Real.log (2 + x t)) =ᵐ[P] 0 := by
      filter_upwards [hz] with t ht
      simp [ht]
    refine ⟨(integrable_zero _ _ _).congr hz2.symm, ?_⟩
    rw [integral_congr_ae hz2, ← h0]
    simp [he0]
  · set n := ∫ t, x t ∂P with hn
    have he' := he
    rw [DGPS.homogeneousEntropy_of_integral_ne_zero hpos.ne', ← hn] at he'
    have hθ0 : ∀ t, 0 ≤ DGPS.entropyIntegrand n (x t) := fun t =>
      DGPS.entropyIntegrand_nonneg hpos (hx0 t)
    have hθm : AEMeasurable (fun t => DGPS.entropyIntegrand n (x t)) P := by
      unfold DGPS.entropyIntegrand
      fun_prop
    have hθi : Integrable (fun t => DGPS.entropyIntegrand n (x t)) P := by
      refine ⟨hθm.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hθ0)]
      exact lt_of_le_of_lt he' ENNReal.ofReal_lt_top
    have hθint : ∫ t, DGPS.entropyIntegrand n (x t) ∂P ≤ e := by
      have := ofReal_integral_eq_lintegral_ofReal hθi (Eventually.of_forall hθ0)
      exact (ENNReal.ofReal_le_ofReal_iff he0).mp (this.trans_le he')
    have hG : Integrable (fun t => x t * (Real.log (2 + n) + 1) +
        DGPS.entropyIntegrand n (x t)) P := (hxi.mul_const _).add hθi
    have hint : Integrable (fun t => x t * Real.log (2 + x t)) P := by
      refine Integrable.mono' hG hmeas (Eventually.of_forall fun t => ?_)
      have hlog : 0 ≤ Real.log (2 + x t) := Real.log_nonneg (by linarith [hx0 t])
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hx0 t) hlog)]
      exact xlog_le_EX045 (hx0 t) hpos
    refine ⟨hint, ?_⟩
    calc ∫ t, x t * Real.log (2 + x t) ∂P
        ≤ ∫ t, (x t * (Real.log (2 + n) + 1) + DGPS.entropyIntegrand n (x t)) ∂P :=
          integral_mono hint hG fun t => xlog_le_EX045 (hx0 t) hpos
      _ = n * (Real.log (2 + n) + 1) + ∫ t, DGPS.entropyIntegrand n (x t) ∂P := by
          rw [integral_add (hxi.mul_const _) hθi, integral_mul_const]
      _ ≤ _ := by linarith



lemma mass_lower_EX045 : ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 2 ≤ h → ∀ hh : 0 < h,
    1 - C / h ≤ ((centralFiniteMeasure_EX040 h hh).mass : ℝ) := by
  obtain ⟨c, C, hc, hC, H⟩ := engineered_normalization_and_rare_mass_bounds
  refine ⟨C, hC, fun h h2 hh => ?_⟩
  have hI := (H h h2).2.2
  have hpi := Real.pi_pos
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hh
  have hqi : Integrable (qAng h) angHaar := integrable_angHaar_of_continuous cq
  have hmeas : MeasurableSet {θ : AngCircle | Uang θ < 1} :=
    measurableSet_lt continuous_Uang.measurable measurable_const
  set G : AngCircle → ℝ := {θ : AngCircle | Uang θ < 1}.indicator (fun _ => 1) with hG
  have hz : ∀ t : ℝ, π / 2 ≤ |t| → |t| ≤ π → G (t : AngCircle) = 0 := by
    intro t ht1 ht2
    have hc : Real.cos t ≤ 0 := by
      rw [← Real.cos_abs]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le ht1 (by linarith)
    have : ¬ (Uang (t : AngCircle) < 1) := by
      rw [Uang_coe_eq]; linarith
    simp [hG, this]
  have hE := central_integral_eq_EX045 h hh hz
  have hP1 : ∫ t, G (t : AngCircle) ∂(centralProbability_EX040 h hh : Measure ℝ) = 1 := by
    have hae : ∀ᵐ t : ℝ ∂(centralProbability_EX040 h hh : Measure ℝ), G (t : AngCircle) = 1 :=
      central_probability_ae_EX040 h hh (p := fun t => G (t : AngCircle) = 1) (Eventually.of_forall fun t ht => by
        have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ht
        have : Uang (t : AngCircle) < 1 := by rw [Uang_coe_eq]; linarith
        simp [hG, this])
    rw [integral_congr_ae hae]
    simp
  rw [hP1, mul_one] at hE
  have hqG : (fun θ => qAng h θ * G θ) = {θ : AngCircle | Uang θ < 1}.indicator (qAng h) := by
    funext θ
    by_cases hU : Uang θ < 1
    · simp [hG, hU]
    · simp [hG, hU]
  have hqGi : Integrable (fun θ => qAng h θ * G θ) angHaar := by
    rw [hqG]; exact hqi.indicator hmeas
  have hexpi : Integrable (fun θ => Real.exp (2 * h * Uang θ) * qAng h θ) angHaar :=
    integrable_angHaar_of_continuous
      ((Real.continuous_exp.comp (continuous_const.mul continuous_Uang)).mul cq)
  have h3 : ∫ θ, qAng h θ ∂angHaar ≤ ∫ θ, (qAng h θ * G θ +
      Real.exp (-2 * h) * (Real.exp (2 * h * Uang θ) * qAng h θ)) ∂angHaar := by
    refine integral_mono hqi (hqGi.add (hexpi.const_mul _)) fun θ => ?_
    have hq := qAng_pos h hh θ
    by_cases hU : Uang θ < 1
    · simp only [hG, Set.indicator_of_mem (show θ ∈ {θ : AngCircle | Uang θ < 1} from hU)]
      have : 0 ≤ Real.exp (-2 * h) * (Real.exp (2 * h * Uang θ) * qAng h θ) := by positivity
      linarith
    · simp only [hG, Set.indicator_of_notMem (show θ ∉ {θ : AngCircle | Uang θ < 1} from hU)]
      have h1 : 1 ≤ Real.exp (-2 * h) * Real.exp (2 * h * Uang θ) := by
        rw [← Real.exp_add]; apply Real.one_le_exp
        nlinarith [not_lt.mp hU]
      nlinarith
  rw [integral_add hqGi (hexpi.const_mul _), integral_const_mul, integral_qAng h hh, hE] at h3
  have h4 : Real.exp (-2 * h) * ∫ θ, Real.exp (2 * h * Uang θ) * qAng h θ ∂angHaar ≤ C / h := by
    calc _ ≤ Real.exp (-2 * h) * (C * Real.exp (2 * h) / h) :=
          mul_le_mul_of_nonneg_left hI (Real.exp_pos _).le
      _ = C / h := by
          have : Real.exp (-2 * h) * Real.exp (2 * h) = 1 := by
            rw [← Real.exp_add]; simp
          calc Real.exp (-2 * h) * (C * Real.exp (2 * h) / h)
              = (Real.exp (-2 * h) * Real.exp (2 * h)) * C / h := by ring
            _ = C / h := by rw [this, one_mul]
  linarith

lemma cutoff_exists_EX045 : ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧
    tsupport χ ⊆ Ioo (-(π / 2)) (π / 2) ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧
    (∀ t, |t| ≤ π / 3 → χ t = 1) ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv χ t| ≤ B := by
  have hpi := Real.pi_pos
  let b : ContDiffBump (0 : ℝ) := ⟨π / 3, 5 * π / 12, by positivity, by linarith⟩
  have hc : ContDiff ℝ ∞ (b : ℝ → ℝ) := b.contDiff
  have hcs : HasCompactSupport (b : ℝ → ℝ) := b.hasCompactSupport
  have hd : Continuous (deriv (b : ℝ → ℝ)) := hc.continuous_deriv (by simp)
  have hdc : HasCompactSupport (deriv (b : ℝ → ℝ)) := hcs.deriv
  obtain ⟨B, hB⟩ := hd.bounded_above_of_compact_support hdc
  refine ⟨b, hc, ?_, fun t => ⟨b.nonneg, b.le_one⟩, fun t ht => ?_, max B 0, le_max_right _ _,
    fun t => ?_⟩
  · rw [b.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have : (5 * π / 12 : ℝ) = b.rOut := rfl
    rw [mem_Ioo, ← abs_lt]
    linarith
  · exact b.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact ht.trans (le_refl _))
  · have := hB t
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)



lemma ii_mul_EX045 {F : AngCircle → ℝ} (hF : Integrable F angHaar) {c : ℝ → ℝ}
    (hc : Continuous c) :
    IntervalIntegrable (fun t : ℝ => c t * F (t : AngCircle)) volume (-(π / 2)) (π / 2) := by
  have hpi := Real.pi_pos
  have h1 := intervalIntegrable_circle_EX045 hF
  have h2 : IntervalIntegrable (fun t : ℝ => F (t : AngCircle)) volume (-(π / 2)) (π / 2) :=
    h1.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith) (by linarith))
  exact h2.continuousOn_mul hc.continuousOn

lemma cut_weak_EX045 {g g' : AngCircle → ℝ} (hw : IsAngularWeakDeriv g g') {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2)) :
    (∫ x in -(π / 2)..π / 2, (χ x * g (x : AngCircle)) * deriv ψ x) =
      -(∫ x in -(π / 2)..π / 2,
        (deriv χ x * g (x : AngCircle) + χ x * g' (x : AngCircle)) * ψ x) := by
  have hg1 : Integrable g angHaar := hw.memLp.integrable (by norm_num)
  have hg1' : Integrable g' angHaar := hw.memLp_deriv.integrable (by norm_num)
  have hχ' : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hχc : Continuous χ := hχ.continuous
  have hψc : Continuous ψ := hψ.continuous
  have hcp : ContDiff ℝ ∞ (fun x => χ x * ψ x) := hχ.mul hψ
  have hts : tsupport (fun x => χ x * ψ x) ⊆ Ioo (-(π / 2)) (π / 2) :=
    (tsupport_mul_subset_right (f := χ) (g := ψ)).trans hψs
  have hweak := weak_interval_EX045 hw hcp hts
  have hdm : ∀ x, deriv (fun x => χ x * ψ x) x = deriv χ x * ψ x + χ x * deriv ψ x := fun x =>
    deriv_mul (hχ.differentiable (by simp) x) (hψ.differentiable (by simp) x)
  simp only [hdm] at hweak
  have hpi := Real.pi_pos
  have I1 : IntervalIntegrable (fun t : ℝ => (deriv χ t * ψ t) * g (t : AngCircle)) volume
      (-(π / 2)) (π / 2) := ii_mul_EX045 hg1 (c := fun t => deriv χ t * ψ t) (hχ'.mul hψc)
  have I2 : IntervalIntegrable (fun t : ℝ => (χ t * deriv ψ t) * g (t : AngCircle)) volume
      (-(π / 2)) (π / 2) := ii_mul_EX045 hg1 (c := fun t => χ t * deriv ψ t) (hχc.mul hψ')
  have I3 : IntervalIntegrable (fun t : ℝ => (χ t * ψ t) * g' (t : AngCircle)) volume
      (-(π / 2)) (π / 2) := ii_mul_EX045 hg1' (c := fun t => χ t * ψ t) (hχc.mul hψc)
  have e1 : (∫ t in -(π / 2)..π / 2, g (t : AngCircle) * (deriv χ t * ψ t + χ t * deriv ψ t)) =
      (∫ t in -(π / 2)..π / 2, (deriv χ t * ψ t) * g (t : AngCircle)) +
      ∫ t in -(π / 2)..π / 2, (χ t * deriv ψ t) * g (t : AngCircle) := by
    rw [← intervalIntegral.integral_add I1 I2]
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  have e2 : (∫ t in -(π / 2)..π / 2, g' (t : AngCircle) * (χ t * ψ t)) =
      ∫ t in -(π / 2)..π / 2, (χ t * ψ t) * g' (t : AngCircle) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  have e3 : (∫ t in -(π / 2)..π / 2, (χ t * g (t : AngCircle)) * deriv ψ t) =
      ∫ t in -(π / 2)..π / 2, (χ t * deriv ψ t) * g (t : AngCircle) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  have e4 : (∫ t in -(π / 2)..π / 2,
        (deriv χ t * g (t : AngCircle) + χ t * g' (t : AngCircle)) * ψ t) =
      (∫ t in -(π / 2)..π / 2, (deriv χ t * ψ t) * g (t : AngCircle)) +
      ∫ t in -(π / 2)..π / 2, (χ t * ψ t) * g' (t : AngCircle) := by
    rw [← intervalIntegral.integral_add I1 I3]
    apply intervalIntegral.integral_congr
    intro t _
    simp only; ring
  rw [e3, e4]
  rw [e1, e2] at hweak
  linarith

lemma memLp_cut_EX045 (h : ℝ) (hh : 0 < h) {g g' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv g g') {χ : ℝ → ℝ} (hχc : Continuous χ) (hχ' : Continuous (deriv χ))
    (h01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) {B : ℝ} (hB : ∀ t, |deriv χ t| ≤ B) :
    MemLp (fun t : ℝ => χ t * g (t : AngCircle)) 2
        (centralProbability_EX040 h hh : Measure ℝ) ∧
      MemLp (fun t : ℝ => deriv χ t * g (t : AngCircle) + χ t * g' (t : AngCircle)) 2
        (centralProbability_EX040 h hh : Measure ℝ) := by
  have hg := memLp_central_EX045 h hh hw.memLp
  have hg' := memLp_central_EX045 h hh hw.memLp_deriv
  have hgm := hg.aestronglyMeasurable
  have hgm' := hg'.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · refine hg.of_le_mul (c := 1) (hχc.aestronglyMeasurable.mul hgm)
      (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul,
      abs_of_nonneg (h01 t).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (h01 t).2
  · have p1 : MemLp (fun t : ℝ => deriv χ t * g (t : AngCircle)) 2
        (centralProbability_EX040 h hh : Measure ℝ) := by
      refine hg.of_le_mul (c := B) (hχ'.aestronglyMeasurable.mul hgm)
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB t) (abs_nonneg _)
    have p2 : MemLp (fun t : ℝ => χ t * g' (t : AngCircle)) 2
        (centralProbability_EX040 h hh : Measure ℝ) := by
      refine hg'.of_le_mul (c := 1) (hχc.aestronglyMeasurable.mul hgm')
        (Eventually.of_forall fun t => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul,
        abs_of_nonneg (h01 t).1]
      exact mul_le_of_le_one_left (abs_nonneg _) (h01 t).2
    exact p1.add p2



lemma interval_cmp_EX045 (h : ℝ) (hh : 0 < h) {f : AngCircle → ℝ} (hf0 : ∀ θ, 0 ≤ f θ)
    {χ : ℝ → ℝ} (hχ1 : ∀ t, |t| ≤ π / 3 → χ t = 1)
    (hFi : Integrable (fun t : ℝ => (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2)))
      (centralProbability_EX040 h hh : Measure ℝ)) :
    ∫ θ, {θ : AngCircle | Uang θ ≤ 1 / 2}.indicator (fun θ => qAng h θ *
      (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) θ ∂angHaar ≤
    9 * ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2))
      ∂(centralProbability_EX040 h hh : Measure ℝ) := by
  have hpi := Real.pi_pos
  have hq := (hardyData_qAng hh).pos
  have hm := central_mass_pos_EX040 h hh
  have hm1 := central_mass_le_one_EX040 h hh
  set F : ℝ → ℝ := fun t => (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2)) with hF
  have hF0 : ∀ t, 0 ≤ F t := fun t => by
    have : 0 ≤ Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2) :=
      Real.log_nonneg (by nlinarith [sq_nonneg (χ t * (f (t : AngCircle) - 1))])
    exact mul_nonneg (sq_nonneg _) (by linarith)
  set L : AngCircle → ℝ := fun θ => {θ : AngCircle | Uang θ ≤ 1 / 2}.indicator
    (fun θ => qAng h θ * (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) θ with hL
  have hL0 : ∀ θ, 0 ≤ L θ := by
    intro θ
    by_cases hθ : θ ∈ {θ : AngCircle | Uang θ ≤ 1 / 2}
    · simp only [hL, Set.indicator_of_mem hθ]
      exact mul_nonneg (hq θ).le (phi_nonneg_ex044 (sq_nonneg _))
    · simp only [hL]
      rw [Set.indicator_of_notMem hθ]
  have hz : ∀ t : ℝ, π / 2 ≤ |t| → |t| ≤ π → L (t : AngCircle) = 0 := by
    intro t h1 h2
    have hc : Real.cos t ≤ 0 := by
      rw [← Real.cos_abs]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le h1 (by linarith)
    have hn : (t : AngCircle) ∉ {θ : AngCircle | Uang θ ≤ 1 / 2} := by
      intro hmem
      have hmem' : Uang (t : AngCircle) ≤ 1 / 2 := hmem
      rw [Uang_coe_eq] at hmem'
      linarith
    simp only [hL]
    rw [Set.indicator_of_notMem hn]
  have hint : IntervalIntegrable (fun t => F t * qAng h (t : AngCircle)) volume
      (-(π / 2)) (π / 2) := central_integrable_weighted_EX040 h hh hFi
  have hmain : ∫ t in -(π / 2)..π / 2, L (t : AngCircle) ≤
      ∫ t in -(π / 2)..π / 2, 9 * (F t * qAng h (t : AngCircle)) := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    refine integral_mono_of_nonneg ?_
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp (hint.const_mul 9)) ?_
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t _ => hL0 _)
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      by_cases hA : (t : AngCircle) ∈ {θ : AngCircle | Uang θ ≤ 1 / 2}
      · have hcos : 1 / 2 ≤ Real.cos t := by
          have hA' : Uang (t : AngCircle) ≤ 1 / 2 := hA
          rw [Uang_coe_eq] at hA'
          linarith
        have habs : |t| ≤ π / 3 := by
          by_contra hlt
          rw [not_le] at hlt
          have ht2 : |t| ≤ π / 2 := abs_le.mpr ⟨ht.1.le, ht.2⟩
          have : Real.cos |t| < Real.cos (π / 3) :=
            Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hlt
          rw [Real.cos_abs, Real.cos_pi_div_three] at this
          linarith
        have hχt := hχ1 t habs
        have hle := mul_le_mul_of_nonneg_left (phi_le_ex044 (hf0 (t : AngCircle)))
          (hq (t : AngCircle)).le
        show L (t : AngCircle) ≤ 9 * (F t * qAng h (t : AngCircle))
        simp only [hL, Set.indicator_of_mem hA, hF, hχt, one_mul]
        nlinarith [hle]
      · have : L (t : AngCircle) = 0 := by
          simp only [hL]
          rw [Set.indicator_of_notMem hA]
        show L (t : AngCircle) ≤ 9 * (F t * qAng h (t : AngCircle))
        rw [this]
        exact mul_nonneg (by norm_num) (mul_nonneg (hF0 t) (hq _).le)
  have hI : 0 ≤ ∫ t in -(π / 2)..π / 2, F t * qAng h (t : AngCircle) :=
    intervalIntegral.integral_nonneg (by linarith) fun t _ => mul_nonneg (hF0 t) (hq _).le
  have hinv : 1 ≤ ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ := by
    rw [one_le_inv_iff₀]
    exact ⟨hm, hm1⟩
  have hkey : ∫ θ, L θ ∂angHaar ≤ 9 * ∫ t, F t ∂(centralProbability_EX040 h hh : Measure ℝ) := by
    rw [integral_angHaar_eq_interval, cut_EX045 hz]
    refine le_trans (mul_le_mul_of_nonneg_left hmain (by positivity)) ?_
    rw [intervalIntegral.integral_const_mul, central_probability_integral_q_EX040 h hh F]
    unfold centralNormFactor_EX040
    set I := ∫ t in -(π / 2)..π / 2, F t * qAng h (t : AngCircle) with hIdef
    have hJ : 0 ≤ (2 * π)⁻¹ * I := by positivity
    have e1 : ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ / (2 * π) * I =
        ((centralFiniteMeasure_EX040 h hh).mass : ℝ)⁻¹ * ((2 * π)⁻¹ * I) := by ring
    have e2 : (2 * π)⁻¹ * (9 * I) = 9 * ((2 * π)⁻¹ * I) := by ring
    rw [e1, e2]
    nlinarith [mul_le_mul_of_nonneg_right hinv hJ]
  exact hkey



lemma core_EX045 (K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ C h1 : ℝ, 0 < C ∧ 2 ≤ h1 ∧ ∀ h : ℝ, h1 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) → ∀ N E : ℝ,
      N = ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar →
      E = ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar → N ≤ K0 →
      ∫ θ, {θ : AngCircle | Uang θ ≤ 1 / 2}.indicator (fun θ => qAng h θ *
        (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) θ ∂angHaar ≤ C * (N + E / h) := by
  obtain ⟨C40, h40, hC40, hh40, H40⟩ := central_conditional_lsi_for_engineered_law
  obtain ⟨Cm, hCm, Hm⟩ := mass_lower_EX045
  obtain ⟨χ, hχ, -, h01, hχ1, B, hB0, hB⟩ := cutoff_exists_EX045
  have hχc : Continuous χ := hχ.continuous
  have hχ' : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hlogK : 0 ≤ Real.log (2 + 2 * K0) := Real.log_nonneg (by linarith)
  obtain ⟨c1, hc1⟩ : ∃ c : ℝ, c = 2 + 2 * (Real.log (2 + 2 * K0) + 1) + 4 * C40 * B ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℝ, c = 4 * C40 := ⟨_, rfl⟩
  have hc1p : 0 < c1 := by
    have : 0 ≤ C40 * B ^ 2 := mul_nonneg hC40.le (sq_nonneg _)
    rw [hc1]; nlinarith
  have hc2p : 0 < c2 := by rw [hc2]; linarith
  refine ⟨9 * (c1 + c2), max (max h40 2) (2 * Cm), by positivity,
    le_max_of_le_left (le_max_right _ _), ?_⟩
  intro h h1h f f' hw hf0 N E hN hE hNK
  have hp2 : 2 ≤ h := le_trans (le_max_of_le_left (le_max_right _ _)) h1h
  have hp : 0 < h := by linarith
  have h40h : h40 ≤ h := le_trans (le_max_of_le_left (le_max_left _ _)) h1h
  have hCmh : 2 * Cm ≤ h := le_trans (le_max_right _ _) h1h
  have hmlow := Hm h hp2 hp
  have hm := central_mass_pos_EX040 h hp
  have hmhalf : 1 / 2 ≤ ((centralFiniteMeasure_EX040 h hp).mass : ℝ) := by
    have : Cm / h ≤ 1 / 2 := by
      rw [div_le_iff₀ hp]; linarith
    linarith
  have hinv : ((centralFiniteMeasure_EX040 h hp).mass : ℝ)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hm (by norm_num)]
    norm_num
    linarith
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hp
  have hg : IsAngularWeakDeriv (fun θ => f θ - 1) f' := by
    have := isWeakDeriv_sub_ex042 hw (isWeakDeriv_const_ex042 1)
    simpa using this
  have hN0 : 0 ≤ N := by
    rw [hN]; exact integral_nonneg fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _)
  have hE0 : 0 ≤ E := by
    rw [hE]; exact integral_nonneg fun θ => mul_nonneg (qAng_pos h hp θ).le (sq_nonneg _)
  have hM := memLp_cut_EX045 h hp hg hχc hχ' h01 hB
  have hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (-(π / 2)) (π / 2) →
      (∫ x in -(π / 2)..π / 2, (χ x * (f (x : AngCircle) - 1)) * deriv ψ x) =
        -(∫ x in -(π / 2)..π / 2,
          (deriv χ x * (f (x : AngCircle) - 1) + χ x * f' (x : AngCircle)) * ψ x) :=
    fun ψ hψ _ hψs => cut_weak_EX045 hg hχ hψ hψs
  have hEnt := H40 h hp h40h _ _ hM.1 hM.2 hweak
  have hG2 : MemLp (fun t : ℝ => f (t : AngCircle) - 1) 2
      (centralProbability_EX040 h hp : Measure ℝ) := memLp_central_EX045 h hp hg.memLp
  have hF2 : MemLp (fun t : ℝ => f' (t : AngCircle)) 2
      (centralProbability_EX040 h hp : Measure ℝ) := memLp_central_EX045 h hp hw.memLp_deriv
  have i1 : Integrable (fun t : ℝ => (f (t : AngCircle) - 1) ^ 2)
      (centralProbability_EX040 h hp : Measure ℝ) := hG2.integrable_sq
  have i2 : Integrable (fun t : ℝ => f' (t : AngCircle) ^ 2)
      (centralProbability_EX040 h hp : Measure ℝ) := hF2.integrable_sq
  have iN : ∫ t, (f (t : AngCircle) - 1) ^ 2 ∂(centralProbability_EX040 h hp : Measure ℝ) ≤
      2 * N := by
    have := central_integral_le_EX045 h hp (F := fun θ => (f θ - 1) ^ 2)
      (fun θ => sq_nonneg _) (integrable_w_g2_ex044 cq hg.memLp)
    beta_reduce at this
    rw [← hN] at this
    exact this.trans (mul_le_mul_of_nonneg_right hinv hN0)
  have iE : ∫ t, f' (t : AngCircle) ^ 2 ∂(centralProbability_EX040 h hp : Measure ℝ) ≤
      2 * E := by
    have := central_integral_le_EX045 h hp (F := fun θ => f' θ ^ 2)
      (fun θ => sq_nonneg _) (integrable_w_g2_ex044 cq hw.memLp_deriv)
    beta_reduce at this
    rw [← hE] at this
    exact this.trans (mul_le_mul_of_nonneg_right hinv hE0)
  have hdd : ∫ t, (deriv χ t * (f (t : AngCircle) - 1) + χ t * f' (t : AngCircle)) ^ 2
      ∂(centralProbability_EX040 h hp : Measure ℝ) ≤ 4 * B ^ 2 * N + 4 * E := by
    have i3 : Integrable (fun t : ℝ =>
        (deriv χ t * (f (t : AngCircle) - 1) + χ t * f' (t : AngCircle)) ^ 2)
        (centralProbability_EX040 h hp : Measure ℝ) := hM.2.integrable_sq
    have i4 := (i1.const_mul (2 * B ^ 2)).add (i2.const_mul 2)
    calc _ ≤ ∫ t, (2 * B ^ 2 * (f (t : AngCircle) - 1) ^ 2 + 2 * f' (t : AngCircle) ^ 2)
          ∂(centralProbability_EX040 h hp : Measure ℝ) := by
          refine integral_mono i3 i4 fun t => ?_
          have hb : deriv χ t ^ 2 ≤ B ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
            rwa [sq_abs] at this
          have hc : χ t ^ 2 ≤ 1 := by
            have := h01 t
            nlinarith [this.1, this.2]
          nlinarith [sq_nonneg (deriv χ t * (f (t : AngCircle) - 1) - χ t * f' (t : AngCircle)),
            mul_le_mul_of_nonneg_right hb (sq_nonneg (f (t : AngCircle) - 1)),
            mul_le_mul_of_nonneg_right hc (sq_nonneg (f' (t : AngCircle)))]
      _ = 2 * B ^ 2 * ∫ t, (f (t : AngCircle) - 1) ^ 2
            ∂(centralProbability_EX040 h hp : Measure ℝ) +
          2 * ∫ t, f' (t : AngCircle) ^ 2 ∂(centralProbability_EX040 h hp : Measure ℝ) := by
          rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * B ^ 2 * (2 * N) + 2 * (2 * E) := by
          have := mul_le_mul_of_nonneg_left iN (by positivity : (0 : ℝ) ≤ 2 * B ^ 2)
          linarith
      _ = 4 * B ^ 2 * N + 4 * E := by ring
  have hEn0 : 0 ≤ (C40 / h) * (4 * B ^ 2 * N + 4 * E) :=
    mul_nonneg (div_nonneg hC40.le hp.le)
      (add_nonneg (mul_nonneg (by positivity) hN0) (by linarith))
  have hEnt' : DGPS.homogeneousEntropy (centralProbability_EX040 h hp : Measure ℝ)
      (fun x => (χ x * (f (x : AngCircle) - 1)) ^ 2) ≤
      ENNReal.ofReal ((C40 / h) * (4 * B ^ 2 * N + 4 * E)) :=
    hEnt.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hdd (div_nonneg hC40.le hp.le)))
  have hxi : Integrable (fun t : ℝ => (χ t * (f (t : AngCircle) - 1)) ^ 2)
      (centralProbability_EX040 h hp : Measure ℝ) := hM.1.integrable_sq
  obtain ⟨hLi, hLle⟩ := entropy_log_int_EX045
    (P := (centralProbability_EX040 h hp : Measure ℝ))
    (x := fun t => (χ t * (f (t : AngCircle) - 1)) ^ 2)
    (fun t => sq_nonneg _) hxi.aemeasurable hxi hEn0 hEnt'
  have hn_le : ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2
      ∂(centralProbability_EX040 h hp : Measure ℝ) ≤ 2 * N := by
    refine le_trans (integral_mono hxi i1 fun t => ?_) iN
    have := h01 t
    have hc : χ t ^ 2 ≤ 1 := by nlinarith [this.1, this.2]
    calc (χ t * (f (t : AngCircle) - 1)) ^ 2 = χ t ^ 2 * (f (t : AngCircle) - 1) ^ 2 := by ring
      _ ≤ 1 * (f (t : AngCircle) - 1) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = _ := one_mul _
  have hn0 : 0 ≤ ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2
      ∂(centralProbability_EX040 h hp : Measure ℝ) := integral_nonneg fun t => sq_nonneg _
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2
      ∂(centralProbability_EX040 h hp : Measure ℝ) := ⟨_, rfl⟩
  rw [← hn] at hn_le hn0 hLle
  have hnlog : n * (Real.log (2 + n) + 1) ≤ 2 * N * (Real.log (2 + 2 * K0) + 1) := by
    have h1 : Real.log (2 + n) ≤ Real.log (2 + 2 * K0) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : 0 ≤ Real.log (2 + n) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + n by linarith)
      linarith
    calc n * (Real.log (2 + n) + 1) ≤ (2 * N) * (Real.log (2 + n) + 1) :=
          mul_le_mul_of_nonneg_right hn_le h2
      _ ≤ 2 * N * (Real.log (2 + 2 * K0) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hFi : Integrable (fun t : ℝ => (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2)))
      (centralProbability_EX040 h hp : Measure ℝ) := by
    refine (hxi.add hLi).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]; ring
  have hFint : ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2))
      ∂(centralProbability_EX040 h hp : Measure ℝ) =
      n + ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2 *
        Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2)
        ∂(centralProbability_EX040 h hp : Measure ℝ) := by
    rw [hn, ← integral_add hxi hLi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; ring
  have he : (C40 / h) * (4 * B ^ 2 * N + 4 * E) ≤ 4 * C40 * B ^ 2 * N + c2 * (E / h) := by
    have h1 : N / h ≤ N := div_le_self hN0 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * C40 * B ^ 2)
    have h3 : (C40 / h) * (4 * B ^ 2 * N + 4 * E) =
        4 * C40 * B ^ 2 * (N / h) + c2 * (E / h) := by rw [hc2]; ring
    rw [h3]; linarith
  have hFle : ∫ t, (χ t * (f (t : AngCircle) - 1)) ^ 2 *
      (1 + Real.log (2 + (χ t * (f (t : AngCircle) - 1)) ^ 2))
      ∂(centralProbability_EX040 h hp : Measure ℝ) ≤ c1 * N + c2 * (E / h) := by
    rw [hFint]
    have : c1 * N = 2 * N + 2 * N * (Real.log (2 + 2 * K0) + 1) + 4 * C40 * B ^ 2 * N := by
      rw [hc1]; ring
    linarith
  have hcmp := interval_cmp_EX045 h hp hf0 hχ1 hFi
  have hE'0 : 0 ≤ E / h := div_nonneg hE0 hp.le
  have hfin : c1 * N + c2 * (E / h) ≤ (c1 + c2) * (N + E / h) := by
    have a := mul_nonneg hc2p.le hN0
    have b := mul_nonneg hc1p.le hE'0
    linarith
  exact hcmp.trans (le_trans (mul_le_mul_of_nonneg_left (hFle.trans hfin) (by norm_num))
    (le_of_eq (by ring)))



lemma entropy_eq_EX045 (h : ℝ) (hp : 0 < h) {f : AngCircle → ℝ} (hfm : AEMeasurable f angHaar)
    (hnorm : ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1) :
    relativeEntropy (densityRef h f) (engineeredReference h) =
      ∫⁻ x, ENNReal.ofReal (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
        - f (angEquiv x) ^ 2 + 1) ∂engineeredReference h := by
  have : IsProbabilityMeasure (engineeredReference h) :=
    DGPS.Examples.engineeredReference_isProbability h hp
  have hvm : AEMeasurable (fun x => f (angEquiv x) ^ 2) (engineeredReference h) :=
    aemeasurable_ref h (hfm.pow_const 2)
  have hre := relativeEntropy_withDensity (P := engineeredReference h)
    (v := fun x => f (angEquiv x) ^ 2) (Eventually.of_forall fun x => sq_nonneg _) hvm
  unfold densityRef
  rw [hre, entropy_mass_one hnorm]



lemma main_EX045 :
    ∃ C h0 : ℝ, 0 < C ∧ 2 ≤ h0 ∧ ∀ h : ℝ, h0 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      ∀ T : ℝ, T = (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      (T ≤ 1 →
        IntegrableOn (fun x : Torus 1 => f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
          - f (angEquiv x) ^ 2 + 1) {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2}
          (engineeredReference h) ∧
        ∫ x in {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ C * T) ∧
      relativeEntropy (densityRef h f) (engineeredReference h) ≤ ENNReal.ofReal (C * T) := by
  obtain ⟨K, hK, H42⟩ := engineered_small_t_l2_and_sup_controls
  obtain ⟨C41, hC41, H41⟩ := engineered_large_t_entropy_regime
  obtain ⟨C44, hC44, H44⟩ := engineered_antipodal_tail_cancellation
  obtain ⟨Cc, h1, hCc, hh1, Hc⟩ := core_EX045 K hK.le
  refine ⟨Cc * (K + 1) + C44 + C41, h1, by positivity, hh1, ?_⟩
  intro h hh f f' hw hf0 hnorm T hT
  have hh2 : 2 ≤ h := le_trans hh1 hh
  have hp : 0 < h := by linarith
  have hP : IsProbabilityMeasure (engineeredReference h) := engineeredReference_isProbability h hp
  have hfm : AEMeasurable f angHaar := hw.memLp.aestronglyMeasurable.aemeasurable
  have hE0 : 0 ≤ ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h :=
    integral_nonneg fun _ => sq_nonneg _
  have hT0 : 0 ≤ T := by
    rw [hT]; positivity
  have cq : Continuous (qAng h) := EngineeredGroundState.continuous_qAng h hp
  by_cases hT1 : T ≤ 1
  · -- small regime
    obtain ⟨N, hN⟩ : ∃ N : ℝ, N = ∫ x, (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h :=
      ⟨_, rfl⟩
    obtain ⟨-, -, hN3, hsupR, -⟩ := H42 h hh2 f f' hw hf0 hnorm T N hT hT1 hN
    have hNc : N = ∫ θ, qAng h θ * (f θ - 1) ^ 2 ∂angHaar :=
      hN.trans (integral_ref_ent h hp (fun θ => (f θ - 1) ^ 2))
    have hE_ref : ∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h =
        ∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar := integral_ref_ent h hp (fun θ => f' θ ^ 2)
    have hEh : (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h ≤ T := by
      rw [← hE_ref]; rw [hT]
      nlinarith [sq_nonneg (∫ x, Eang h (angEquiv x) ∂densityRef h f)]
    have hNK : N ≤ K := by nlinarith
    have hcore := Hc h hh f f' hw hf0 N (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) hNc rfl hNK
    have hcore' : ∫ θ, {θ : AngCircle | Uang θ ≤ 1 / 2}.indicator (fun θ => qAng h θ *
        (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) θ ∂angHaar ≤ Cc * (K + 1) * T := by
      refine hcore.trans ?_
      have : N + (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h ≤ (K + 1) * T := by nlinarith
      calc Cc * (N + (∫ θ, qAng h θ * f' θ ^ 2 ∂angHaar) / h) ≤ Cc * ((K + 1) * T) :=
            mul_le_mul_of_nonneg_left this hCc.le
        _ = _ := by ring
    have hS0 : 0 ≤ K * (h * Real.exp (2 * h) * T) := by positivity
    obtain ⟨phi_int, hgT_int, phi_set⟩ := phi_torus_ex044 h hp hfm hf0 hS0
      (hsupR.mono fun x hx => by simpa [mul_assoc] using hx)
    have eA : ∫ x in {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h =
        ∫ θ, {θ : AngCircle | Uang θ ≤ 1 / 2}.indicator (fun θ => qAng h θ *
          (f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)) θ ∂angHaar :=
      set_ref_ex044 h hp (measurableSet_le continuous_Uang.measurable measurable_const)
        (fun θ => f θ ^ 2 * Real.log (f θ ^ 2) - f θ ^ 2 + 1)
    have hCle : Cc * (K + 1) ≤ Cc * (K + 1) + C44 + C41 := by linarith
    have hA : ∫ x in {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ (Cc * (K + 1) + C44 + C41) * T :=
      eA.trans_le (hcore'.trans (mul_le_mul_of_nonneg_right hCle hT0))
    refine ⟨fun _ => ⟨phi_int.integrableOn, hA⟩, ?_⟩
    -- entropy
    have hent := entropy_eq_EX045 h hp hfm hnorm
    have hnn : ∀ x : Torus 1, 0 ≤ f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
        - f (angEquiv x) ^ 2 + 1 := fun x => phi_nonneg_ex044 (sq_nonneg _)
    rw [hent, ← ofReal_integral_eq_lintegral_ofReal phi_int (Eventually.of_forall hnn)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hAm : MeasurableSet {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2} :=
      angEquiv.measurable (measurableSet_le continuous_Uang.measurable measurable_const)
    have hsplit := integral_add_compl hAm phi_int
    have hsub : {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2}ᶜ ⊆
        {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)} := by
      intro x hx
      have : ¬ Uang (angEquiv x) ≤ 1 / 2 := hx
      exact (not_le.1 this).le
    have hcompl : ∫ x in {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2}ᶜ,
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h :=
      setIntegral_mono_set phi_int.integrableOn (Eventually.of_forall hnn)
        hsub.eventuallyLE
    have hΩ : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ C44 * T := by
      rcases hT0.eq_or_lt with h0 | hpos
      · -- T = 0
        have hgΩ : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
            (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ N := by
          rw [hN]
          exact setIntegral_le_integral hgT_int (Eventually.of_forall fun x => sq_nonneg _)
        have hN0 : N ≤ 0 := by rw [← h0] at hN3; simpa using hN3
        have hgΩ0 : ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
            (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ 0 := hgΩ.trans hN0
        have h2 := phi_set (1 + Real.log (2 + K * (h * Real.exp (2 * h) * T))) le_rfl
        have hM : 0 ≤ 9 * (1 + Real.log (2 + K * (h * Real.exp (2 * h) * T))) := by
          have : 0 ≤ Real.log (2 + K * (h * Real.exp (2 * h) * T)) :=
            Real.log_nonneg (by linarith)
          positivity
        have : 9 * (1 + Real.log (2 + K * (h * Real.exp (2 * h) * T))) *
            ∫ x in {x : Torus 1 | 1 / 2 ≤ Uang (angEquiv x)},
              (f (angEquiv x) - 1) ^ 2 ∂engineeredReference h ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hM hgΩ0
        rw [← h0]
        linarith
      · obtain ⟨-, -, -, -, hΩ⟩ := H44 h hh2 f f' hw hf0 hnorm T N hpos hT hT1 hN
        exact hΩ.2
    have hΩ' := hcompl.trans hΩ
    have : (∫ x, f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1
        ∂engineeredReference h) ≤ (Cc * (K + 1) + C44 + C41) * T := by
      rw [← hsplit]
      nlinarith
    exact this
  · have hT1' : 1 ≤ T := (not_le.1 hT1).le
    refine ⟨fun h' => absurd h' hT1, ?_⟩
    have h41 := H41 h hh2 f f' hw hf0 hnorm (by rw [← hT]; exact hT1')
    rw [← hT] at h41
    refine h41.trans (ENNReal.ofReal_le_ofReal ?_)
    have : C41 ≤ Cc * (K + 1) + C44 + C41 := by
      have : 0 ≤ Cc * (K + 1) := by positivity
      linarith
    exact mul_le_mul_of_nonneg_right this hT0


end DGPS.Examples.EngineeredRankOneEX045

namespace DGPS.Examples

open DGPS.Models DGPS.Examples.EngineeredRankOne DGPS.Circle.AngularNormalization

/-- EX045: engineered central entropy completion.  For `T ≤ 1` the integral of
`Φ(f²) = f² log f² - f² + 1` over `{U ≤ 1/2}` is at most `C T`; together with EX041 and EX044 the
relative entropy satisfies `H(ρ|μ_h) ≤ C T` with `T = I/(4h)-type energy term + ρ(E_h)²`, uniformly
for `h ≥ h0`. -/
theorem engineered_central_entropy_completion :
    ∃ C h0 : ℝ, 0 < C ∧ 2 ≤ h0 ∧ ∀ h : ℝ, h0 ≤ h → ∀ f f' : AngCircle → ℝ,
      IsAngularWeakDeriv f f' → (∀ θ, 0 ≤ f θ) →
      ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 →
      ∀ T : ℝ, T = (∫ x, f' (angEquiv x) ^ 2 ∂engineeredReference h) / h +
        (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2 →
      (T ≤ 1 →
        MeasureTheory.IntegrableOn
          (fun x : Torus 1 => f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2)
            - f (angEquiv x) ^ 2 + 1) {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2}
          (engineeredReference h) ∧
        ∫ x in {x : Torus 1 | Uang (angEquiv x) ≤ 1 / 2},
          (f (angEquiv x) ^ 2 * Real.log (f (angEquiv x) ^ 2) - f (angEquiv x) ^ 2 + 1)
          ∂engineeredReference h ≤ C * T) ∧
      relativeEntropy (densityRef h f) (engineeredReference h) ≤ ENNReal.ofReal (C * T) :=
  DGPS.Examples.EngineeredRankOneEX045.main_EX045

end DGPS.Examples
