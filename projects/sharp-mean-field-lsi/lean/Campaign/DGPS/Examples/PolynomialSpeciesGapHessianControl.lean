import DGPS.Examples.PolynomialSpeciesReducedGap

/-! Uniform local control of the ACTUAL partial amplitude Hessian, jointly in
both independent reference parameters and the rate parameter. Smoothness of the
same graph produces the control; no Hessian bound is assumed. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Theta := (ℝ × ℝ) × ℝ
private abbrev Amp := ℝ × ℝ
private abbrev Joint := Theta × Amp

/-- The actual reduced gap's amplitude Hessian, with all other parameters free. -/
def polynomialReducedGapHessian (ψ : PolynomialRangeParameters → E_STR02969)
    (z : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ z.1)) z.2

private def jointMap (z : Joint) : PolynomialRangeParameters := polynomialGapSlice z.1 z.2

private theorem jointMap_smooth : ContDiff ℝ ∞ jointMap := by
  exact contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk
    (contDiff_fst.fst.prodMk contDiff_fst.snd))

private theorem jointMap_zero : jointMap 0 = 0 := by ext <;> rfl

private def fixedGap (x : (ℝ × ℝ) × PeriodicC2_STR02969) : ℝ :=
  polynomialRangeGap x.1 x.2
private theorem fixedGap_smooth : ContDiff ℝ ∞ fixedGap := polynomialRangeGap_smooth
private def jointGapInput (ψ : PolynomialRangeParameters → E_STR02969) (z : Joint) :
    (ℝ × ℝ) × PeriodicC2_STR02969 := (z.1.1, polynomialGapLift ψ z.1 z.2)
private theorem jointGap_eq (ψ : PolynomialRangeParameters → E_STR02969) :
    (fun z : Joint => polynomialReducedGap ψ z.1 z.2) = fixedGap ∘ jointGapInput ψ := rfl

private theorem joint_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (fun z : Joint => polynomialReducedGap ψ z.1 z.2) (jointMap ⁻¹' U) := by
  let W := jointMap ⁻¹' U
  have hΦ : ContDiffOn ℝ ∞ (fun z : Joint => ψ (jointMap z)) W :=
    hψ.comp jointMap_smooth.contDiffOn (fun _ hz => hz)
  have hE := E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ
  have hlin : ContDiff ℝ ∞ (fun z : Joint =>
      z.2.1 • cosC2_STR02915 + z.2.2 • sinC2_STR02915) :=
    (contDiff_snd.fst.smul contDiff_const).add (contDiff_snd.snd.smul contDiff_const)
  have hLift : ContDiffOn ℝ ∞ (fun z : Joint => polynomialGapLift ψ z.1 z.2) W :=
    hlin.contDiffOn.add hE
  have hp : ContDiffOn ℝ ∞ (fun z : Joint =>
      (z.1.1, polynomialGapLift ψ z.1 z.2)) W := contDiff_fst.fst.contDiffOn.prodMk hLift
  change ContDiffOn ℝ ∞ (jointGapInput ψ) W at hp
  rw [jointGap_eq]
  exact fixedGap_smooth.comp_contDiffOn hp

/-- Genuine joint regularity of the partial amplitude Hessian near the origin. -/
theorem polynomialReducedGapHessian_smooth_at_zero {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffAt ℝ ∞ (polynomialReducedGapHessian ψ) 0 := by
  have hW : IsOpen (jointMap ⁻¹' U) := hU.preimage jointMap_smooth.continuous
  have h0W : (0 : Joint) ∈ jointMap ⁻¹' U := by
    change jointMap 0 ∈ U
    rw [jointMap_zero]
    exact h0U
  have hJ : ContDiffAt ℝ ∞ (fun z : Joint => polynomialReducedGap ψ z.1 z.2) 0 :=
    (joint_smooth hψ).contDiffAt (hW.mem_nhds h0W)
  let q := fun z : Joint × Amp => (z.1.1, z.2)
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have hq0 : q (0 : Joint × Amp) = 0 := by ext <;> rfl
  have hF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Joint) (y : Amp) => polynomialReducedGap ψ z.1 y)) (0, 0) := by
    have h := hJ.comp (0 : Joint × Amp) hq.contDiffAt
    have he : (Function.uncurry (fun (z : Joint) (y : Amp) => polynomialReducedGap ψ z.1 y)) =
        (fun z : Joint × Amp => polynomialReducedGap ψ z.1.1 z.2) := rfl
    rw [he]
    convert h using 1 <;> rfl
  have hD : ContDiffAt ℝ ∞ (fun z : Joint =>
      fderiv ℝ (polynomialReducedGap ψ z.1) z.2) 0 :=
    ContDiffAt.fderiv hF contDiffAt_snd (by simp)
  have hDF : ContDiffAt ℝ ∞
      (Function.uncurry (fun (z : Joint) (y : Amp) =>
        fderiv ℝ (polynomialReducedGap ψ z.1) y)) (0, 0) := by
    have h := hD.comp (0 : Joint × Amp) hq.contDiffAt
    have he : (Function.uncurry (fun (z : Joint) (y : Amp) =>
        fderiv ℝ (polynomialReducedGap ψ z.1) y)) =
        (fun z : Joint × Amp => fderiv ℝ (polynomialReducedGap ψ z.1.1) z.2) := rfl
    rw [he]
    convert h using 1 <;> rfl
  exact ContDiffAt.fderiv hDF contDiffAt_snd (by simp)

/-- The radius and constant are chosen BEFORE all small amplitudes, fields and
rate parameters. Their hypotheses are only actual produced graph facts. -/
theorem polynomialReducedGapHessian_lipschitz {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      (∀ z : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ), ‖z‖ < δ → polynomialGapSlice z.1 z.2 ∈ U) ∧
      ∀ z : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ), ‖z‖ < δ →
        ‖polynomialReducedGapHessian ψ z - polynomialReducedGapHessian ψ 0‖ ≤ K * ‖z‖ := by
  have hc : ContDiffAt ℝ 1 (polynomialReducedGapHessian ψ) 0 :=
    (polynomialReducedGapHessian_smooth_at_zero hU h0U hψ).of_le (by simp)
  obtain ⟨K, t, ht, hLip⟩ := hc.exists_lipschitzOnWith
  have hW : IsOpen (jointMap ⁻¹' U) := hU.preimage jointMap_smooth.continuous
  have h0W : (0 : Joint) ∈ jointMap ⁻¹' U := by
    change jointMap 0 ∈ U
    rw [jointMap_zero]
    exact h0U
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht (hW.mem_nhds h0W))
  refine ⟨δ, K, hδ, K.coe_nonneg, ?_, ?_⟩
  · intro z hz
    exact (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hz)).2
  · intro z hz
    have hz' : z ∈ Metric.ball (0 : Joint) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have h0' : (0 : Joint) ∈ Metric.ball (0 : Joint) δ := by
      simpa only [Metric.mem_ball, dist_self] using hδ
    have h := hLip.dist_le_mul z (hball hz').1 0 (hball h0').1
    simpa only [dist_eq_norm, sub_zero] using h

end DGPS.Examples.PolynomialSpecies
