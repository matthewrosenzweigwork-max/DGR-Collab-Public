import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Frontier.STR029.T04

/-! Uniform angular H1 bounds for the actual unscaled amplitude tangents of the
retained range graph. The constants are derived from its smoothness near zero. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029 DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem angularH1_le_c2 (T : PeriodicC2_STR02969) :
    normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) ≤ 2 * ‖T‖ ^ 2 := by
  have hv (t : ℝ) : |T.val t| ≤ ‖T‖ :=
    ((bdd_parts_STR02969 T.isC2).1.abs_le_supNorm t).trans
      (le_c2Norm_STR02969 T.val).1
  have hd (t : ℝ) : |deriv T.val t| ≤ ‖T‖ :=
    ((bdd_parts_STR02969 T.isC2).2.1.abs_le_supNorm t).trans
      (le_c2Norm_STR02969 T.val).2.1
  rw [normInt_eq_STR02935]
  apply (normInt_bounds_STR02904
    ((T.isC2.2.2.1.continuous.pow 2).add (T.isC2.2.1.continuous.pow 2))
    (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _)) ?_).2
  intro t
  have h1 := pow_le_pow_left₀ (abs_nonneg _) (hv t) 2
  have h2 := pow_le_pow_left₀ (abs_nonneg _) (hd t) 2
  simp only [sq_abs] at h1 h2
  change deriv T.val t ^ 2 + T.val t ^ 2 ≤ 2 * ‖T‖ ^ 2
  linarith

private def amplitudeEmbedding : (ℝ × ℝ) →L[ℝ] Par_STR02916 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)))

private theorem amplitudeEmbedding_norm (v : ℝ × ℝ) :
    ‖amplitudeEmbedding v‖ = ‖v‖ := by
  simp [amplitudeEmbedding, Prod.norm_def]

/-- One uniform bound for every actual amplitude tangent of the same retained
graph, on a common parameter interval and before all branches and directions. -/
theorem ordinaryRoot_amplitude_tangent_bound (D : OrdinaryRootGraphData) :
    ∃ K δ : ℝ, 0 < K ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, |h| < δ → ∀ j : Fin 3, ∀ v : ℝ × ℝ,
        let T := fderiv ℝ (Lamp_STR02956 D.ψ (h, h ^ 2 * D.Z j h 2))
          (h * D.Z j h 0, h * D.Z j h 1) v
        normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) ≤
          K ^ 2 * (v.1 ^ 2 + v.2 ^ 2) := by
  let L : Par_STR02916 → PeriodicC2_STR02969 := fun p =>
    p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 +
      ((D.ψ p : E_STR02969) : PeriodicC2_STR02969)
  have hLC : ContDiffOn ℝ ∞ L D.U := by
    have hlin : ContDiff ℝ ∞ (fun p : Par_STR02916 =>
        p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915) :=
      (contDiff_fst.smul contDiff_const).add
        ((contDiff_fst.comp contDiff_snd).smul contDiff_const)
    exact hlin.contDiffOn.add (E_STR02969.subtypeL.contDiff.comp_contDiffOn D.smoothψ)
  have hL0 : ContDiffAt ℝ ∞ L 0 := hLC.contDiffAt (D.openU.mem_nhds D.zero_memU)
  have hDF : ContinuousAt (fderiv ℝ L) 0 :=
    (hL0.fderiv_right (m := 1) (by simp)).continuousAt
  let C : ℝ := ‖fderiv ℝ L 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : ∀ᶠ p in 𝓝 (0 : Par_STR02916), ‖fderiv ℝ L p‖ < C :=
    hDF.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  have hpath (j : Fin 3) :
      Tendsto (fun h : ℝ => ptPar_STR02923 h (D.Z j h)) (𝓝 0) (𝓝 0) := by
    have hZ : ContinuousAt (D.Z j) 0 :=
      (D.smoothZ j).continuousOn.continuousAt
        (Ioo_mem_nhds (by linarith [D.radius_pos]) D.radius_pos)
    have hz0 := (continuous_apply 0).continuousAt.comp hZ
    have hz1 := (continuous_apply 1).continuousAt.comp hZ
    have hz2 := (continuous_apply 2).continuousAt.comp hZ
    have hp : ContinuousAt (fun h : ℝ => ptPar_STR02923 h (D.Z j h)) 0 := by
      unfold ptPar_STR02923
      fun_prop
    have hz : ptPar_STR02923 0 (D.Z j 0) = (0 : Par_STR02916) := by
      change ((0 * D.Z j 0 0, 0 * D.Z j 0 1, 0, 0 ^ 2 * D.Z j 0 2) :
        Par_STR02916) = (0, 0, 0, 0)
      simp
    have ht := hp.tendsto
    rw [hz] at ht
    exact ht
  have hev : ∀ᶠ h : ℝ in 𝓝 0,
      ∀ j : Fin 3, ‖fderiv ℝ L (ptPar_STR02923 h (D.Z j h))‖ < C :=
    Filter.eventually_all.2 fun j => (hpath j).eventually hb
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
  let δ := min D.radius ε
  have hδ : 0 < δ := lt_min D.radius_pos hε
  refine ⟨2 * C, δ, by positivity, hδ, min_le_left _ _, fun h hh j v => ?_⟩
  have hhr : h ∈ Ioo (-D.radius) D.radius :=
    abs_lt.mp (hh.trans_le (min_le_left _ _))
  have hpoint := D.branch_memU j h hhr
  have hLp : DifferentiableAt ℝ L (ptPar_STR02923 h (D.Z j h)) :=
    (hLC.contDiffAt (D.openU.mem_nhds hpoint)).differentiableAt (by simp)
  let θ : ℝ × ℝ := (h, h ^ 2 * D.Z j h 2)
  let x : ℝ × ℝ := (h * D.Z j h 0, h * D.Z j h 1)
  have hI : HasFDerivAt (iota_STR02956 θ) amplitudeEmbedding x := by
    exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.prodMk
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.prodMk
        ((hasFDerivAt_const θ.1 x).prodMk (hasFDerivAt_const θ.2 x)))
  have hLamp : Lamp_STR02956 D.ψ θ = L ∘ iota_STR02956 θ := rfl
  have hD : fderiv ℝ (Lamp_STR02956 D.ψ θ) x =
      (fderiv ℝ L (ptPar_STR02923 h (D.Z j h))).comp amplitudeEmbedding := by
    rw [hLamp, fderiv_comp x hLp hI.differentiableAt, hI.fderiv]
    rfl
  have hbpath : ‖fderiv ℝ L (ptPar_STR02923 h (D.Z j h))‖ ≤ C :=
    (hεb (by rw [Real.dist_eq, sub_zero]; exact hh.trans_le (min_le_right _ _)) j).le
  let T := fderiv ℝ (Lamp_STR02956 D.ψ θ) x v
  have hT : ‖T‖ ≤ C * ‖v‖ := by
    dsimp only [T]
    rw [hD, ContinuousLinearMap.comp_apply]
    exact ((fderiv ℝ L _).le_opNorm _).trans
      (by rw [amplitudeEmbedding_norm]; exact mul_le_mul_of_nonneg_right hbpath (norm_nonneg _))
  have hTsq := pow_le_pow_left₀ (norm_nonneg _) hT 2
  have hv : ‖v‖ ^ 2 ≤ v.1 ^ 2 + v.2 ^ 2 := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    rcases le_total |v.1| |v.2| with hv |hv
    · rw [max_eq_right hv, sq_abs]
      nlinarith [sq_nonneg v.1]
    · rw [max_eq_left hv, sq_abs]
      nlinarith [sq_nonneg v.2]
  change normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) ≤ _
  calc
    _ ≤ 2 * ‖T‖ ^ 2 := angularH1_le_c2 T
    _ ≤ 2 * (C * ‖v‖) ^ 2 := by linarith
    _ ≤ (2 * C) ^ 2 * (v.1 ^ 2 + v.2 ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hv),
        mul_nonneg (sq_nonneg C) (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))]

end DGPS.Examples.ThreeSpeciesCircle
