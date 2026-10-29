import DGPS.Examples.RoughBoundary.Feature
import DGPS.Examples.RoughBoundary.SpikesNowhereL2

/-!
# Every nonzero direction is rough (RUF007)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` sections 1.5 and 8.4.

For `L > 0`, `ε ≠ 0`, a nonempty open interval `J ⊂ ℝ` and `a ≠ 0` in `ℝ²`, the phase derivative
`θ'`, the feature derivative `U' = 2π θ' J U` and the directional derivative `a · U'` all fail
to be square integrable on `J` (derivatives read on the real line, as in RUF005).
-/

open MeasureTheory Set
open scoped Real

namespace DGPS.Examples.RoughBoundary.Feature

open DGPS.Examples.RoughBoundary.Spikes (hSum hMean pt)

/-- Rescaling the variable by `6` transports `L²` membership on an interval. -/
lemma memLp_scale {F : ℝ → ℝ} {c d : ℝ}
    (h : MemLp (fun x => F (6 * x)) 2 (volume.restrict (Ioo c d))) :
    MemLp F 2 (volume.restrict (Ioo (6 * c) (6 * d))) := by
  have h6 : (6 : ℝ) ≠ 0 := by norm_num
  let e := MeasurableEquiv.mulLeft₀ (6 : ℝ) h6
  have he : MeasurableEmbedding (fun x : ℝ => 6 * x) := e.measurableEmbedding
  have hmap : Measure.map (fun x : ℝ => 6 * x) volume = ENNReal.ofReal |(6 : ℝ)⁻¹| • volume :=
    Real.map_volume_mul_left h6
  have hpre : (fun x : ℝ => 6 * x) ⁻¹' Ioo (6 * c) (6 * d) = Ioo c d := by
    ext x; simp
  have hvol : volume.restrict (Ioo (6 * c) (6 * d)) =
      ENNReal.ofReal 6 • Measure.map (fun x : ℝ => 6 * x) (volume.restrict (Ioo c d)) := by
    have hr := he.restrict_map volume (Ioo (6 * c) (6 * d))
    rw [hpre, hmap] at hr
    rw [← hr, Measure.restrict_smul, smul_smul]
    have : ENNReal.ofReal 6 * ENNReal.ofReal |(6 : ℝ)⁻¹| = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num), abs_of_pos (by norm_num)]
      norm_num
    rw [this, one_smul]
  rw [hvol]
  refine MemLp.smul_measure ?_ ENNReal.ofReal_ne_top
  exact (he.memLp_map_measure_iff).2 h

lemma measurable_dtheta (L ε : ℝ) : Measurable (dtheta L ε) := by
  have h1 : Measurable fun x : ℝ => Qdens L (2 * x) :=
    ((continuous_qdens L).comp (continuous_const.mul continuous_id)).measurable
  have h2 : Measurable fun x : ℝ => hSum (pt (6 * x)) :=
    Spikes.hSum_meas.comp (Spikes.measurable_pt.comp (measurable_const.mul measurable_id))
  unfold dtheta
  exact (measurable_const.mul h1).add (measurable_const.mul (h2.sub measurable_const))

/-- Step 1: `θ'` is not square integrable on any nonempty bounded open interval. -/
lemma dtheta_not_memLp {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) {c d : ℝ} (hcd : c < d) :
    ¬ MemLp (dtheta L ε) 2 (volume.restrict (Ioo c d)) := by
  intro hmem
  set d' := min d (c + 1 / 6) with hd'
  have hcd' : c < d' := lt_min hcd (by linarith)
  have hsub : Ioo c d' ⊆ Ioo c d := Ioo_subset_Ioo_right (min_le_left _ _)
  have hmem' : MemLp (dtheta L ε) 2 (volume.restrict (Ioo c d')) :=
    hmem.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hQ : MemLp (fun x : ℝ => 2 * Qdens L (2 * x)) 2 (volume.restrict (Ioo c d')) := by
    refine MemLp.of_bound (measurable_const.mul
        ((continuous_qdens L).comp (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
      (2 * (Real.exp L / Zpart L)) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_pos (mul_pos two_pos (qdens_pos hL _))]
      exact mul_le_mul_of_nonneg_left (qdens_le hL _) two_pos.le
  have hf : MemLp (fun x : ℝ => hSum (pt (6 * x)) - hMean) 2 (volume.restrict (Ioo c d')) := by
    have := (hmem'.sub hQ).const_mul (1 / (6 * ε))
    refine this.ae_eq (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply, dtheta_eq, Spikes.fLine]
    field_simp
    ring
  have := memLp_scale (F := fun t => hSum (pt t) - hMean) hf
  exact (Spikes.nowhere_local_square_integrability (a := 6 * c) (b := 6 * d')
    (by linarith) (by have := min_le_right d (c + 1 / 6); linarith)).2.2.2.2.2 this

/-- The a.e. derivative `U' = 2π θ' J U` of the feature on the real line. -/
noncomputable def Uder (L ε x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  (2 * π * dtheta L ε x) • Jrot (Ureal L ε x)

lemma norm_Uder (L ε x : ℝ) : ‖Uder L ε x‖ = 2 * π * ‖dtheta L ε x‖ := by
  unfold Uder
  rw [norm_smul, norm_Jrot, norm_Ureal, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π), Real.norm_eq_abs]

lemma inner_Jrot_Ureal (L ε x : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ a (Jrot (Ureal L ε x)) =
      a 1 * Real.cos (2 * π * theta L ε x) - a 0 * Real.sin (2 * π * theta L ε x) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, Jrot, dotProduct]
  ring

lemma continuous_dirCoef (L ε : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    Continuous fun x => inner ℝ a (Jrot (Ureal L ε x)) := by
  simp only [inner_Jrot_Ureal]
  have := continuous_theta L ε
  fun_prop

/-- Step 2: the projection coefficient does not vanish identically on any interval. -/
lemma exists_dirCoef_ne {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) {c d : ℝ} (hcd : c < d)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ≠ 0) :
    ∃ x ∈ Ioo c d, inner ℝ a (Jrot (Ureal L ε x)) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  -- θ is not constant on the interval
  have hnc : ∃ x1 ∈ Ioo c d, ∃ x2 ∈ Ioo c d, theta L ε x1 ≠ theta L ε x2 := by
    by_contra hc
    push Not at hc
    have hz : dtheta L ε =ᵐ[volume.restrict (Ioo c d)] 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [ae_hasDerivAt_theta L ε] with x hx hxm
      have hev : theta L ε =ᶠ[nhds x] fun _ => theta L ε x := by
        filter_upwards [isOpen_Ioo.mem_nhds hxm] with y hy using hc y hy x hxm
      have h0 : HasDerivAt (theta L ε) 0 x := (hasDerivAt_const x (theta L ε x)).congr_of_eventuallyEq hev
      exact hx.unique h0
    exact dtheta_not_memLp hL hε hcd (MemLp.zero.ae_eq hz.symm)
  obtain ⟨x1, hx1, x2, hx2, hne⟩ := hnc
  set Δ := theta L ε x2 - theta L ε x1 with hΔ
  have hΔ0 : Δ ≠ 0 := sub_ne_zero.2 hne.symm
  set t := 1 / max 1 (4 * |Δ|) with ht
  have hm : 0 < max 1 (4 * |Δ|) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hm]; exact le_max_left _ _
  have htΔ : |t * Δ| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos ht0, ht, one_div, inv_mul_le_iff₀ hm]
    have : 4 * |Δ| ≤ max 1 (4 * |Δ|) := le_max_right _ _
    linarith
  have hmem : theta L ε x1 + t * Δ ∈ uIcc (theta L ε x1) (theta L ε x2) := by
    rw [Set.mem_uIcc]
    rcases lt_or_gt_of_ne hΔ0 with h | h
    · right; constructor <;> nlinarith
    · left; constructor <;> nlinarith
  obtain ⟨x', hx', hθx'⟩ := intermediate_value_uIcc
    ((continuous_theta L ε).continuousOn (s := uIcc x1 x2)) hmem
  have hx'm : x' ∈ Ioo c d := (isPreconnected_Ioo.ordConnected.uIcc_subset hx1 hx2) hx'
  have h1 := hcon x1 hx1
  have h2 := hcon x' hx'm
  rw [inner_Jrot_Ureal] at h1 h2
  set A := 2 * π * theta L ε x1
  set B := 2 * π * theta L ε x'
  have hBA : B - A = 2 * π * (t * Δ) := by
    simp only [A, B]; rw [hθx']; ring
  have hk : Real.sin (B - A) = 0 := by
    have hb : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
      by_contra hh
      push Not at hh
      apply ha
      ext i; fin_cases i <;> simp [hh.1, hh.2]
    rw [Real.sin_sub]
    have e1 : a 1 * (Real.sin B * Real.cos A - Real.cos B * Real.sin A) = 0 := by
      linear_combination (Real.sin B) * h1 - (Real.sin A) * h2
    have e0 : a 0 * (Real.sin B * Real.cos A - Real.cos B * Real.sin A) = 0 := by
      linear_combination (Real.cos B) * h1 - (Real.cos A) * h2
    rcases hb with hb | hb
    · exact (mul_eq_zero.1 e0).resolve_left hb
    · exact (mul_eq_zero.1 e1).resolve_left hb
  have hlt : |B - A| ≤ π / 2 := by
    rw [hBA, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [Real.pi_pos]
  have hpos : B - A ≠ 0 := by
    rw [hBA]
    exact mul_ne_zero (by positivity) (mul_ne_zero ht0.ne' hΔ0)
  have := (Real.sin_eq_zero_iff_of_lt_of_lt (x := B - A) (by linarith [abs_le.1 hlt |>.1, Real.pi_pos])
    (by linarith [abs_le.1 hlt |>.2, Real.pi_pos])).1 hk
  exact hpos this

/-- Step 3: a subinterval on which the projection coefficient is bounded away from zero. -/
lemma exists_subinterval_dirCoef {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) {c d : ℝ} (hcd : c < d)
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ≠ 0) :
    ∃ c' d' η : ℝ, c ≤ c' ∧ c' < d' ∧ d' ≤ d ∧ 0 < η ∧
      ∀ x ∈ Ioo c' d', η ≤ |inner ℝ a (Jrot (Ureal L ε x))| := by
  obtain ⟨x0, hx0, hne⟩ := exists_dirCoef_ne hL hε hcd ha
  set η := |inner ℝ a (Jrot (Ureal L ε x0))| / 2 with hη
  have hη0 : 0 < η := by positivity
  have hS : {x | η < |inner ℝ a (Jrot (Ureal L ε x))|} ∈ nhds x0 :=
    (isOpen_lt continuous_const (continuous_dirCoef L ε a).abs).mem_nhds (by simp only [Set.mem_ofPred_eq]; linarith [abs_pos.2 hne])
  have hT : {x | η < |inner ℝ a (Jrot (Ureal L ε x))|} ∩ Ioo c d ∈ nhds x0 :=
    Filter.inter_mem hS (isOpen_Ioo.mem_nhds hx0)
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hT
  refine ⟨max l c, min u d, η, le_max_right _ _, ?_, min_le_right _ _, hη0, fun x hx => ?_⟩
  · exact max_lt (lt_min (hl.trans hu) (hl.trans hx0.2)) (lt_min (hx0.1.trans hu) hcd)
  · have : x ∈ Ioo l u := ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    exact (hsub this).1.le

/-- **RUF007.** For every `L > 0`, `ε ≠ 0`, nonempty open `J ⊂ ℝ` (in particular every nonempty
open interval) and nonzero direction `a ∈ ℝ²`: `θ'`, `U' = 2π θ' J U` and `a · U'` are not in
`L²(J)`. -/
theorem every_nonzero_direction_is_rough {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) (hne : J.Nonempty) {a : EuclideanSpace ℝ (Fin 2)} (ha : a ≠ 0) :
    ¬ MemLp (dtheta L ε) 2 (volume.restrict J) ∧
    ¬ MemLp (fun x => (2 * π * dtheta L ε x) • Jrot (Ureal L ε x)) 2 (volume.restrict J) ∧
    ¬ MemLp (fun x => inner ℝ a ((2 * π * dtheta L ε x) • Jrot (Ureal L ε x))) 2
      (volume.restrict J) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJ x hx
  rw [Real.ball_eq_Ioo] at hball
  have hcd : x - r < x + r := by linarith
  have hmono : volume.restrict (Ioo (x - r) (x + r)) ≤ volume.restrict J :=
    Measure.restrict_mono hball le_rfl
  have hpi : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
  refine ⟨fun h => dtheta_not_memLp hL hε hcd (h.mono_measure hmono), fun h => ?_, fun h => ?_⟩
  · refine dtheta_not_memLp hL hε hcd ((h.mono_measure hmono).of_le_mul
      (c := 1) (measurable_dtheta L ε).aestronglyMeasurable (ae_of_all _ fun y => ?_))
    have := norm_Uder L ε y
    simp only [Uder] at this
    rw [this]
    nlinarith [norm_nonneg (dtheta L ε y)]
  · obtain ⟨c', d', η, hc, hcd', hd, hη, hbd⟩ := exists_subinterval_dirCoef hL hε hcd ha
    have hsub : Ioo c' d' ⊆ J := (Ioo_subset_Ioo hc hd).trans hball
    have hmono' : volume.restrict (Ioo c' d') ≤ volume.restrict J := Measure.restrict_mono hsub le_rfl
    have hg := h.mono_measure hmono'
    refine dtheta_not_memLp hL hε hcd' (hg.of_le_mul (c := 1 / (2 * π * η))
      (measurable_dtheta L ε).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun y hy => ?_)))
    have hb := hbd y hy
    rw [inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [abs_nonneg (dtheta L ε y), Real.pi_pos, mul_le_mul_of_nonneg_left hb
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) (abs_nonneg (dtheta L ε y)))]

end DGPS.Examples.RoughBoundary.Feature
