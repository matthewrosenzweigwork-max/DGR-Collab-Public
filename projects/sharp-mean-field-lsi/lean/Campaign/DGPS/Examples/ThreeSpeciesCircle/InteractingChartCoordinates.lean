import DGPS.Examples.ThreeSpeciesCircle.InteractingLocalUniqueness

/-! Deterministic coordinates and genuine neighborhood entry on the EXISTING
full C2-Holder chart. All radii are chosen at fixed h and fixed retained graph
neighborhoods, before epsilon or any chart/minimizer. -/

noncomputable section
open Filter Topology Set Metric
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

def interactingChartCos : PeriodicC2_STR02969 →L[ℝ] ℝ :=
  (2 : ℝ) • c2Data_STR02969.pairCLM Real.cos Real.continuous_cos Real.abs_cos_le_one

def interactingChartSin : PeriodicC2_STR02969 →L[ℝ] ℝ :=
  (2 : ℝ) • c2Data_STR02969.pairCLM Real.sin Real.continuous_sin Real.abs_sin_le_one

def interactingChartRemainder : PeriodicC2_STR02969 →L[ℝ] PeriodicC2_STR02969 :=
  ContinuousLinearMap.id ℝ PeriodicC2_STR02969 -
    interactingChartCos.smulRight cosC2_STR02915 - interactingChartSin.smulRight sinC2_STR02915

private theorem remainder_val (u : PeriodicC2_STR02969) (t : ℝ) :
    (interactingChartRemainder u).val t = u.val t -
      interactingChartCos u * Real.cos t - interactingChartSin u * Real.sin t := rfl

/-- Zero mean is the only constraint needed to recover the actual E complement. -/
def interactingChartComplement (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val = 0) :
    E_STR02969 :=
  ⟨interactingChartRemainder u, (c2Data_STR02969.mem_sub_iff _).mpr (by
    have he : (interactingChartRemainder u).val = projP_STR02953 u.val := by
      funext t
      rw [remainder_val]
      change u.val t - 2 * pair_STR02953 Real.cos u.val * Real.cos t -
        2 * pair_STR02953 Real.sin u.val * Real.sin t = _
      simp only [projP_STR02953, hm, sub_zero]
    change InE_STR02901 (interactingChartRemainder u).val
    rw [he]
    exact projP_inE_STR02955 u.isC2.2.1.continuous)⟩

/-- Exact full-chart reconstruction, with its original mean-zero log gauge. -/
theorem interactingChart_reconstruct (u : PeriodicC2_STR02969) (hm : meanT_STR02901 u.val = 0) :
    interactingChartCos u • cosC2_STR02915 + interactingChartSin u • sinC2_STR02915 +
      (interactingChartComplement u hm : PeriodicC2_STR02969) = u := by
  apply Subtype.ext
  funext t
  change interactingChartCos u * Real.cos t + interactingChartSin u * Real.sin t +
    (interactingChartRemainder u).val t = u.val t
  rw [remainder_val]
  ring

/-- The original bounded Fourier functionals recover exactly the retained
amplitudes and complement at every admissible seed. -/
theorem interactingChart_seed_coordinates (a b : ℝ) (w : E_STR02969) :
    let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
    interactingChartCos u = a ∧ interactingChartSin u = b ∧
      interactingChartRemainder u = (w : PeriodicC2_STR02969) := by
  let u := a • cosC2_STR02915 + b • sinC2_STR02915 + (w : PeriodicC2_STR02969)
  have hw : InE_STR02901 (w : PeriodicC2_STR02969).val :=
    (c2Data_STR02969.mem_sub_iff _).mp w.property
  have ht := meanT_uT_STR02924 a b (w : PeriodicC2_STR02969).isC2.2.1.continuous hw
  have ha : interactingChartCos u = a := by
    change 2 * meanT_STR02901 (fun t => u.val t * Real.cos t) = a
    change 2 * meanT_STR02901 (fun t => uT_STR02901 a b (w : PeriodicC2_STR02969).val t * Real.cos t) = a
    rw [ht.2.1]
    ring
  have hb : interactingChartSin u = b := by
    change 2 * meanT_STR02901 (fun t => u.val t * Real.sin t) = b
    change 2 * meanT_STR02901 (fun t => uT_STR02901 a b (w : PeriodicC2_STR02969).val t * Real.sin t) = b
    rw [ht.2.2]
    ring
  refine ⟨ha, hb, ?_⟩
  apply Subtype.ext
  funext t
  change (interactingChartRemainder u).val t = (w : PeriodicC2_STR02969).val t
  rw [remainder_val, ha, hb]
  change a * Real.cos t + b * Real.sin t + (w : PeriodicC2_STR02969).val t -
    a * Real.cos t - b * Real.sin t = (w : PeriodicC2_STR02969).val t
  ring

/-- The precise fixed linear-map norm controls complement distances in the
same full C2-Holder norm; no weaker topology is substituted. -/
theorem interactingChartRemainder_dist_bound (u v : PeriodicC2_STR02969) :
    ‖interactingChartRemainder u - interactingChartRemainder v‖ ≤
      ‖interactingChartRemainder‖ * ‖u - v‖ := by
  rw [← map_sub]
  exact interactingChartRemainder.le_opNorm (u - v)

/-- Fixed-h chart/rate nearness gives genuine membership in ONE retained U,V
and reduced ball. The factual norm-nearness inputs are later supplied by the
actual every-minimizer capture argument. No desired entry is a premise. -/
theorem interactingChart_coordinate_neighborhood_entry (h : ℝ) (hh : h ≠ 0)
    (z0 : Fin 3 → ℝ) (w0 : E_STR02969)
    (U : Set (ℝ × ℝ × ℝ × ℝ)) (hU : IsOpen U)
    (hp0 : (0, h * z0 0, h * z0 1, h ^ 2 * z0 2) ∈ U)
    (V : Set E_STR02969) (hV : IsOpen V) (hw0 : w0 ∈ V) (r : ℝ) (hr : 0 < r) :
    let seed := (h * z0 0) • cosC2_STR02915 + (h * z0 1) • sinC2_STR02915 +
      (w0 : PeriodicC2_STR02969)
    ∃ η : ℝ, 0 < η ∧ ∀ (ε γ : ℝ) (u : PeriodicC2_STR02969)
      (hm : meanT_STR02901 u.val = 0),
      |ε| < η → ‖u - seed‖ < η → |γ - h ^ 2 * z0 2| < η →
      let z : Fin 3 → ℝ := ![interactingChartCos u / h, interactingChartSin u / h, γ / h ^ 2]
      (ε, h * z 0, h * z 1, h ^ 2 * z 2) ∈ U ∧
        interactingChartComplement u hm ∈ V ∧ (ε, z) ∈ ball ((0 : ℝ), z0) r := by
  let seed := (h * z0 0) • cosC2_STR02915 + (h * z0 1) • sinC2_STR02915 +
    (w0 : PeriodicC2_STR02969)
  let x0 : ℝ × PeriodicC2_STR02969 × ℝ := (0, seed, h ^ 2 * z0 2)
  let p : (ℝ × PeriodicC2_STR02969 × ℝ) → ℝ × ℝ × ℝ × ℝ :=
    fun x => (x.1, interactingChartCos x.2.1, interactingChartSin x.2.1, x.2.2)
  let z : (ℝ × PeriodicC2_STR02969 × ℝ) → (Fin 3 → ℝ) :=
    fun x => ![interactingChartCos x.2.1 / h, interactingChartSin x.2.1 / h, x.2.2 / h ^ 2]
  have hp : Continuous p := by dsimp only [p]; fun_prop
  have hz : Continuous z := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp only [z] <;> fun_prop
  have hc := interactingChart_seed_coordinates (h * z0 0) (h * z0 1) w0
  have hpseed : p x0 ∈ U := by
    change (0, interactingChartCos seed, interactingChartSin seed, h ^ 2 * z0 2) ∈ U
    rw [hc.1, hc.2.1]
    exact hp0
  have hzseed : z x0 = z0 := by
    ext i
    fin_cases i
    · change interactingChartCos seed / h = z0 0
      rw [hc.1]
      field_simp [hh]
    · change interactingChartSin seed / h = z0 1
      rw [hc.2.1]
      field_simp [hh]
    · change (h ^ 2 * z0 2) / h ^ 2 = z0 2
      field_simp [hh]
  obtain ⟨d, hd, hdV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hw0)
  have hpEv : ∀ᶠ x in 𝓝 x0, p x ∈ U := hp.continuousAt.eventually_mem (hU.mem_nhds hpseed)
  have hzEv : ∀ᶠ x in 𝓝 x0, (x.1, z x) ∈ ball ((0 : ℝ), z0) r :=
    (continuous_fst.prodMk hz).continuousAt.eventually_mem (by
      simpa only [x0, hzseed] using ball_mem_nhds ((0 : ℝ), z0) hr)
  have hwc : Continuous (fun x : ℝ × PeriodicC2_STR02969 × ℝ =>
      dist (interactingChartRemainder x.2.1) (w0 : PeriodicC2_STR02969)) :=
    (interactingChartRemainder.continuous.comp (continuous_fst.comp continuous_snd)).dist continuous_const
  have hwEv : ∀ᶠ x in 𝓝 x0,
      dist (interactingChartRemainder x.2.1) (w0 : PeriodicC2_STR02969) < d :=
    (hwc.continuousAt (x := x0)).eventually (gt_mem_nhds (show
      dist (interactingChartRemainder seed) (w0 : PeriodicC2_STR02969) < d from by
        rw [hc.2.2, dist_self]
        exact hd))
  obtain ⟨η, hη, hηall⟩ := Metric.eventually_nhds_iff.mp (hpEv.and (hzEv.and hwEv))
  refine ⟨η, hη, fun ε γ u hm hε hu hγ => ?_⟩
  have hx : dist (ε, u, γ) x0 < η := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_lt (by simpa only [x0, Real.dist_eq, sub_zero] using hε)
      (max_lt (by simpa only [x0, dist_eq_norm] using hu)
        (by simpa only [x0, Real.dist_eq] using hγ))
  obtain ⟨hpU, hzB, hwB⟩ := hηall hx
  have hpEq : (ε, h * z (ε, u, γ) 0, h * z (ε, u, γ) 1, h ^ 2 * z (ε, u, γ) 2) =
      p (ε, u, γ) := by
    change (ε, h * (interactingChartCos u / h), h * (interactingChartSin u / h),
      h ^ 2 * (γ / h ^ 2)) = (ε, interactingChartCos u, interactingChartSin u, γ)
    congr 1 <;> field_simp [hh]
  refine ⟨by rw [hpEq]; exact hpU, ?_, hzB⟩
  apply hdV
  change dist (interactingChartRemainder u) (w0 : PeriodicC2_STR02969) < d
  exact hwB

end DGPS.Examples.ThreeSpeciesCircle
