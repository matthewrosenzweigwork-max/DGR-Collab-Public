import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel
import DGPS.Variational.EquilibriumGibbs
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap
import DGPS.Frontier.STR029.T32
import DGPS.Lipschitz.T01ConditionalMeanField

/-!
# Exact full-domain finite-family deficit for the elementary interacting model

All forces are the actual weak drift of `modelData`. The reference minimizer is identified
from the generic minimizing Gibbs law and the proved circle stationary uniqueness.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The unscaled centered interaction potential, determined by the three actual moments. -/
noncomputable def elementaryKernelMean (h : ℝ) (ν : Measure (Torus 1)) (x : Torus 1) : ℝ :=
  kAlpha * (momC h ν * featureC h x + momS h ν * featureS h x) -
    kBeta * (momB h ν * featureB h x)

theorem isSmooth_elementaryKernelMean (h : ℝ) (ν : Measure (Torus 1)) :
    IsSmoothPeriodic (elementaryKernelMean h ν) := by
  unfold IsSmoothPeriodic elementaryKernelMean
  exact (contDiff_const.mul ((contDiff_const.mul (smooth_featureC h)).add
    (contDiff_const.mul (smooth_featureS h)))).sub
      (contDiff_const.mul (contDiff_const.mul (smooth_featureB h)))

theorem integral_kernelK_eq_mean (h : ℝ) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] (x : Torus 1) :
    (∫ y, kernelK h x y ∂ν) = elementaryKernelMean h ν x := by
  have heq : (fun y => kernelK h x y) = fun y =>
      (kAlpha * featureC h x) * featureC h y +
      (kAlpha * featureS h x) * featureS h y +
      (-kBeta * featureB h x) * featureB h y + 0 := by
    funext y
    unfold kernelK
    ring
  rw [heq, integral_affine3]
  unfold elementaryKernelMean
  ring

/-- The diagonal gauge contributes only a spatially constant term to the true potential. -/
theorem elementary_equilibriumPotential (h ε : ℝ) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] (x : Torus 1) :
    DGPS.Lipschitz.equilibriumPotential (modelData h ε) ν x = driftPot h ε ν x -
      ε / 2 * ∫ y, kernelK h y y ∂ν := by
  have iK : Integrable (fun y => kernelK h x y) ν :=
    ((continuous_kernelK h).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have iD : Integrable (fun y => kernelK h y y) ν :=
    (continuous_kernelK_diag h).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold DGPS.Lipschitz.equilibriumPotential DGPS.Lipschitz.interactionConvolution
  change modelV h ε x + ∫ y, modelW h ε x y ∂ν = _
  have hW : ∀ y, modelW h ε x y =
      ε * (kernelK h x y - kernelK h x x / 2 - kernelK h y y / 2) := by
    intro y
    unfold modelW
    ring
  simp_rw [hW]
  unfold modelV
  have hc : (∫ _ : Torus 1, kernelK h x x / 2 ∂ν) = kernelK h x x / 2 := by simp
  have ic : Integrable (fun _ : Torus 1 => kernelK h x x / 2) ν := integrable_const _
  have iKC : Integrable (fun y => kernelK h x y - kernelK h x x / 2) ν := iK.sub ic
  have iD2 : Integrable (fun y => kernelK h y y / 2) ν := iD.div_const 2
  rw [integral_const_mul, integral_sub iKC iD2, integral_sub iK ic,
    hc, integral_div, integral_kernelK_eq_mean]
  unfold driftPot elementaryKernelMean
  ring

/-- The generic Gibbs measure is exactly the circle Gibbs measure already used by
`elementaryModel_uniqueStationary`; the two potentials differ by a constant only. -/
theorem elementary_gibbsMeasure (h ε : ℝ) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] :
    DGPS.Lipschitz.gibbsMeasure (modelData h ε) ν = gibbsMeasure (driftPot h ε ν) := by
  let c := ε / 2 * ∫ y, kernelK h y y ∂ν
  have he : ∀ x, Real.exp (-DGPS.Lipschitz.equilibriumPotential (modelData h ε) ν x) =
      Real.exp c * Real.exp (-driftPot h ε ν x) := by
    intro x
    rw [elementary_equilibriumPotential]
    change Real.exp (-(driftPot h ε ν x - c)) = _
    rw [show -(driftPot h ε ν x - c) = c + -driftPot h ε ν x by ring, Real.exp_add]
  have hZ : DGPS.Lipschitz.gibbsPartition (modelData h ε) ν =
      Real.exp c * gibbsZ (driftPot h ε ν) := by
    unfold DGPS.Lipschitz.gibbsPartition gibbsZ
    simp_rw [he]
    exact integral_const_mul _ _
  rw [DGPS.Lipschitz.gibbsMeasure_eq_withDensity]
  apply congrArg ((haar 1).withDensity)
  funext x
  congr 1
  change Real.exp (-DGPS.Lipschitz.equilibriumPotential (modelData h ε) ν x) /
    DGPS.Lipschitz.gibbsPartition (modelData h ε) ν =
      Real.exp (-driftPot h ε ν x) / gibbsZ (driftPot h ε ν)
  rw [he, hZ]
  exact mul_div_mul_left _ _ (Real.exp_pos c).ne'

/-- The actual reference probability minimizes the actual interacting free energy. -/
theorem elementaryModel_reference_minimizer {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) :
    freeEnergy (modelData h ε) (refProb hh) = freeEnergyMinimum (modelData h ε) := by
  obtain ⟨ν, hν⟩ := freeEnergy_minimum_exists (modelData h ε)
  have hg := DGPS.Lipschitz.minimizer_eq_gibbs (modelData h ε) ν (fun τ => by
    rw [hν]
    exact iInf_le _ τ)
  rw [elementary_gibbsMeasure] at hg
  have hs := (stationary_iff_gibbs h ε ν).mpr hg
  have heq := (elementaryModel_uniqueStationary hh hε hεmax ν).mp hs
  rwa [heq] at hν

/-- The actual quadratic kernel moment, without any generator/kernel commutation. -/
noncomputable def elementaryQ (h : ℝ) (ν : Measure (Torus 1)) : ℝ :=
  ∫ x, elementaryKernelMean h ν x ∂ν

theorem elementaryQ_moments (h : ℝ) (ν : Measure (Torus 1))
    [IsProbabilityMeasure ν] :
    elementaryQ h ν = kAlpha * (momC h ν ^ 2 + momS h ν ^ 2) - kBeta * momB h ν ^ 2 := by
  unfold elementaryQ
  have heq : elementaryKernelMean h ν = fun x =>
      (kAlpha * momC h ν) * featureC h x + (kAlpha * momS h ν) * featureS h x +
      (-kBeta * momB h ν) * featureB h x + 0 := by
    funext x
    unfold elementaryKernelMean
    ring
  rw [heq, integral_affine3]
  ring

theorem elementary_centeredCorrection {h : ℝ} (hh : 0 < h) (ε : ℝ)
    (ν : ProbabilityMeasure (Torus 1)) :
    DGPS.Lipschitz.t01CenteredCorrection (modelData h ε) (refProb hh) ν =
      ε / 2 * elementaryQ h (ν : Measure (Torus 1)) := by
  unfold DGPS.Lipschitz.t01CenteredCorrection
  change (1 / 2 : ℝ) * (∫ p, DGPS.centeredKernel (modelData h ε) (refProb hh) p.1 p.2
    ∂((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1)))) = _
  simp_rw [centeredKernel_model hh ε]
  rw [integral_const_mul,
    integral_prod _ ((continuous_kernelK h).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp_rw [integral_kernelK_eq_mean]
  unfold elementaryQ
  ring

/-- Exact full-domain finite-family gap at the actual interacting minimizer. -/
theorem elementaryModel_speciesGap_expansion {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (F : SpeciesFamily 1) :
    (speciesGap (modelData h ε) F : ℝ) =
      (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) +
        ε / 2 * elementaryQ h (densityMeasure (barycenter F) : Measure (Torus 1)) := by
  have hmin := elementaryModel_reference_minimizer hh hε hεmax
  have hg := (DGPS.Lipschitz.speciesGap_eq_reference_entropy_correction (modelData h ε) hmin F).2
  rw [elementary_centeredCorrection hh ε] at hg
  exact hg

/-- Physical derivative of the actual unscaled interaction potential. -/
noncomputable def elementaryKprime (h : ℝ) (ν : Measure (Torus 1)) : Torus 1 → ℝ :=
  coordPartial 0 (elementaryKernelMean h ν)

/-- The physical reference generator applied to the actual kernel potential. -/
noncomputable def elementaryAK (h : ℝ) (ν : Measure (Torus 1)) (x : Torus 1) : ℝ :=
  -coordPartial 0 (elementaryKprime h ν) x - sigT h x * elementaryKprime h ν x

theorem continuous_elementaryAK (h : ℝ) (ν : Measure (Torus 1)) :
    Continuous (elementaryAK h ν) := by
  exact (((isSmooth_elementaryKernelMean h ν).isSmoothPeriodic_coordPartial 0).continuous_coordPartial 0).neg.sub
    ((continuous_sigT h).mul ((isSmooth_elementaryKernelMean h ν).continuous_coordPartial 0))

/-- Every genuine weak-drift provider has the exact actual mean-field force. -/
theorem elementary_force_coord (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (τ : AbsoluteDensity 1) :
    (fun x => b.force τ x 0) =ᵐ[haar 1] fun x =>
      -logScore h x + ε * elementaryKprime h (densityMeasure τ) x := by
  let gl := weakGradient (fun x => Real.log ((ordinaryReference h).density x))
    ((ordinaryReference h).memH1_log (ordinaryReference_lip h))
  have hl := isWeakGradient_weakGradient ((ordinaryReference h).memH1_log (ordinaryReference_lip h))
  have hk := (isSmooth_elementaryKernelMean h (densityMeasure τ)).isWeakGradient
  let c := -Real.log (besselI 0 h) - ε / 2 *
    ∫ y, kernelK h y y ∂(densityMeasure τ : Measure (Torus 1))
  have hg : IsWeakGradient (interactionPotential (modelData h ε) τ)
      (fun x => (-1 : ℝ) • gl x + ε • smoothGrad (elementaryKernelMean h (densityMeasure τ)) x) := by
    have hh := ((hl.smul (-1)).add (hk.smul ε)).add (isWeakGradient_const (d := 1) c)
    refine hh.congr_ae (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => by simp [gl])
    change -1 * Real.log (referenceDensity h x) + ε * elementaryKernelMean h (densityMeasure τ) x + c = _
    have hlog : Real.log (referenceDensity h x) = h * cosHarm 3 x - Real.log (besselI 0 h) := by
      unfold referenceDensity
      rw [Real.log_div (Real.exp_pos _).ne' besselI_zero_pos.ne', Real.log_exp]
    change _ = DGPS.Lipschitz.equilibriumPotential (modelData h ε) (densityMeasure τ) x
    rw [elementary_equilibriumPotential, hlog]
    unfold driftPot elementaryKernelMean c
    ring
  have hg1 : IsWeakGradientLp 1 (interactionPotential (modelData h ε) τ)
      (fun x => (-1 : ℝ) • gl x + ε • smoothGrad (elementaryKernelMean h (densityMeasure τ)) x) :=
    ⟨hg.memLp.mono_exponent one_le_two, hg.memLp_grad.mono_exponent one_le_two, hg.ibp⟩
  have heq := b.ae_eq_of_isWeakGradient τ hg1
  filter_upwards [heq] with x hx
  have hx0 := congrArg (fun v : Tangent 1 => v 0) hx
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_mul, one_mul,
    smoothGrad_apply, gl, logScore, elementaryKprime] using hx0

private theorem elementary_integrable_density_mul (ρ : AbsoluteDensity 1)
    {f : Torus 1 → ℝ} (hf : Continuous f) : Integrable (fun x => ρ.density x * f x) (haar 1) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ρ.integrable_density.mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun x => hM x (Set.mem_univ x))

private theorem elementary_cross_term (h : ℝ) (ρ τ : AbsoluteDensity 1) :
    (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
      ρ.sqrt x * elementaryKprime h (densityMeasure τ) x ∂haar 1) =
    ∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1 := by
  let k := elementaryKprime h (densityMeasure τ)
  have hk : IsSmoothPeriodic k := (isSmooth_elementaryKernelMean h (densityMeasure τ)).isSmoothPeriodic_coordPartial 0
  have hρ := isWeakGradient_weakGradient ρ.sqrt_mem
  have huK : MemLp (fun x => ρ.sqrt x * k x) 2 (haar 1) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hk.continuous_torus.continuousOn
    exact ρ.memLp_sqrt.of_le_mul (c := M)
      (ρ.memLp_sqrt.aestronglyMeasurable.mul hk.continuous_torus.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ρ.sqrt x| * |k x| ≤ |ρ.sqrt x| * M :=
            mul_le_mul_of_nonneg_left (hM x (Set.mem_univ x)) (abs_nonneg _)
          _ = M * ‖ρ.sqrt x‖ := by rw [Real.norm_eq_abs]; ring)
  let L := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 * (ρ.sqrt x * k x)
  let B := fun x => (ρ.sqrt x * logScore h x) * (ρ.sqrt x * k x)
  have hL : Integrable L (haar 1) := ((memLp_coord hρ.memLp_grad 0).const_mul 2).integrable_mul huK
  have hB : Integrable B (haar 1) := (memLp_mul_logScore h ρ.memLp_sqrt).integrable_mul huK
  have hd := (hρ.mul_one_dim hρ).ibp k hk 0
  have hD : (∫ x, ρ.density x * coordPartial 0 k x ∂haar 1) = -∫ x, L x ∂haar 1 := by
    convert hd using 1
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp only [AbsoluteDensity.density, pow_two]
    · congr 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [L]
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
  have hpt : (fun x => (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
      ρ.sqrt x * k x) = fun x => L x - B x := by
    funext x
    dsimp only [L, B]
    ring
  rw [hpt, integral_sub hL hB]
  have hAk : (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) =
      -(∫ x, ρ.density x * coordPartial 0 k x ∂haar 1) - ∫ x, B x ∂haar 1 := by
    have hiD := elementary_integrable_density_mul ρ (hk.continuous_coordPartial 0)
    calc
      (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) =
          ∫ x, -(ρ.density x * coordPartial 0 k x) - B x ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [logScore_ae_eq h] with x hx
        dsimp only [elementaryAK, B, AbsoluteDensity.density]
        rw [hx]
        ring
      _ = (∫ x, -(ρ.density x * coordPartial 0 k x) ∂haar 1) - ∫ x, B x ∂haar 1 :=
        integral_sub (show Integrable (fun x => -(ρ.density x * coordPartial 0 k x)) (haar 1) from hiD.neg) hB
      _ = _ := by rw [integral_neg]
  rw [hD] at hAk
  linarith

/-- Exact current square-root dissipation against an arbitrary absolute barycenter. -/
theorem elementaryModel_oneSpecies_dissipation (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (ρ τ : AbsoluteDensity 1) :
    (∫⁻ x, ENNReal.ofReal (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x +
      ρ.sqrt x • b.force τ x‖ ^ 2) ∂haar 1) =
    ENNReal.ofReal ((ordinaryFisher h ρ).toReal +
      2 * ε * (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
      ε ^ 2 * (∫ x, ρ.density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1)) ∧
    0 ≤ (ordinaryFisher h ρ).toReal +
      2 * ε * (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
      ε ^ 2 * (∫ x, ρ.density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1) := by
  let S := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x
  let k := elementaryKprime h (densityMeasure τ)
  let U := fun x => ρ.sqrt x * k x
  have hρ := isWeakGradient_weakGradient ρ.sqrt_mem
  have hS : MemLp S 2 (haar 1) :=
    ((memLp_coord hρ.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h ρ.memLp_sqrt)
  have hk : Continuous k := (isSmooth_elementaryKernelMean h (densityMeasure τ)).continuous_coordPartial 0
  have hU : MemLp U 2 (haar 1) := by
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hk.continuousOn
    exact ρ.memLp_sqrt.of_le_mul (c := M)
      (ρ.memLp_sqrt.aestronglyMeasurable.mul hk.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |ρ.sqrt x| * |k x| ≤ |ρ.sqrt x| * M :=
            mul_le_mul_of_nonneg_left (hM x (Set.mem_univ x)) (abs_nonneg _)
          _ = M * ‖ρ.sqrt x‖ := by rw [Real.norm_eq_abs]; ring)
  have hpt : ∀ᵐ x ∂haar 1,
      ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2 =
        (S x + ε * U x) ^ 2 := by
    filter_upwards [elementary_force_coord h ε b τ] with x hx
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx,
      Real.norm_eq_abs, sq_abs]
    dsimp only [S, U, k]
    congr 1
    ring
  have hval : (∫ x, (S x + ε * U x) ^ 2 ∂haar 1) =
      (ordinaryFisher h ρ).toReal +
      2 * ε * (∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
      ε ^ 2 * (∫ x, ρ.density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1) := by
    have hsq : (fun x => (S x + ε * U x) ^ 2) =
        fun x => S x ^ 2 + 2 * ε * (S x * U x) + ε ^ 2 * U x ^ 2 := by
      funext x
      ring
    have hCross : Integrable (fun x => 2 * ε * (S x * U x)) (haar 1) :=
      (hS.integrable_mul hU).const_mul (2 * ε)
    have hSum : Integrable (fun x => S x ^ 2 + 2 * ε * (S x * U x)) (haar 1) :=
      hS.integrable_sq.add hCross
    rw [hsq, integral_add hSum (hU.integrable_sq.const_mul (ε ^ 2)),
      integral_add hS.integrable_sq hCross, integral_const_mul, integral_const_mul]
    have hI : (ordinaryFisher h ρ).toReal = ∫ x, S x ^ 2 ∂haar 1 := by
      rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    rw [← hI]
    have hcross : (∫ x, S x * U x ∂haar 1) =
        ∫ x, ρ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1 := by
      convert elementary_cross_term h ρ τ using 1
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [S, U, k]
      ring
    rw [hcross]
    congr 1
    congr 1
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp only [U, k, AbsoluteDensity.density]
    ring
  have hENN : (fun x => ENNReal.ofReal (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x +
      ρ.sqrt x • b.force τ x‖ ^ 2)) =ᵐ[haar 1] fun x => ENNReal.ofReal ((S x + ε * U x) ^ 2) := by
    filter_upwards [hpt] with x hx
    rw [hx]
  have hSqI : Integrable (fun x => (S x + ε * U x) ^ 2) (haar 1) :=
    (hS.add (hU.const_mul ε)).integrable_sq
  refine ⟨?_, ?_⟩
  · rw [lintegral_congr_ae hENN,
      ← ofReal_integral_eq_lintegral_ofReal hSqI
        (Eventually.of_forall fun _ => sq_nonneg _), hval]
  · rw [← hval]
    exact integral_nonneg fun _ => sq_nonneg _

/-- Both finite-family correction moments depend only on the actual barycenter. -/
noncomputable def elementaryJ (h : ℝ) (τ : AbsoluteDensity 1) : ℝ :=
  ∫ x, τ.density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1

noncomputable def elementaryC (h a : ℝ) (τ : AbsoluteDensity 1) : ℝ :=
  2 * (∫ x, τ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) -
    a * elementaryQ h (densityMeasure τ)

theorem elementaryJ_nonneg (h : ℝ) (τ : AbsoluteDensity 1) : 0 ≤ elementaryJ h τ :=
  integral_nonneg fun x => mul_nonneg (τ.density_nonneg x) (sq_nonneg _)

/-- Full-domain finite-family dissipation, with finiteness proved rather than imposed. -/
theorem elementaryModel_speciesDissipation_expansion (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1) :
    speciesDissipation (modelData h ε) b F ≠ ⊤ ∧
    (speciesDissipation (modelData h ε) b F).toReal =
      (∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal) +
      2 * ε * (∫ x, (barycenter F).density x *
        elementaryAK h (densityMeasure (barycenter F)) x ∂haar 1) +
      ε ^ 2 * elementaryJ h (barycenter F) := by
  let τ := barycenter F
  let X := fun s : Fin F.count => (ordinaryFisher h (F.density s)).toReal +
      2 * ε * (∫ x, (F.density s).density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
      ε ^ 2 * (∫ x, (F.density s).density x * (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1)
  have hX0 : ∀ s, 0 ≤ X s := fun s =>
    (elementaryModel_oneSpecies_dissipation h ε b (F.density s) τ).2
  have hsum (g : Torus 1 → ℝ) (hg : Continuous g) :
      (∑ s, F.weight s * ∫ x, (F.density s).density x * g x ∂haar 1) =
        ∫ x, τ.density x * g x ∂haar 1 := by
    have hh := Structural.budget_integral_barycenter F hg
    simp_rw [Structural.budget_integral_densityMeasure] at hh
    exact hh.symm
  have hX : (∑ s, F.weight s * X s) =
      (∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal) +
      2 * ε * (∫ x, τ.density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
      ε ^ 2 * elementaryJ h τ := by
    have hp : ∀ s : Fin F.count, F.weight s * X s =
        F.weight s * (ordinaryFisher h (F.density s)).toReal +
        (2 * ε) * (F.weight s * ∫ x, (F.density s).density x * elementaryAK h (densityMeasure τ) x ∂haar 1) +
        ε ^ 2 * (F.weight s * ∫ x, (F.density s).density x *
          (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂haar 1) := by
      intro s
      dsimp only [X]
      ring
    simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hSq := hsum (fun x => (elementaryKprime h (densityMeasure τ) x) ^ 2)
      (((isSmooth_elementaryKernelMean h _).continuous_coordPartial 0).pow 2)
    rw [hsum _ (continuous_elementaryAK h _), hSq]
    rfl
  have hD : speciesDissipation (modelData h ε) b F =
      ENNReal.ofReal (∑ s, F.weight s * X s) := by
    unfold speciesDissipation
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hX0 s)]
    apply Finset.sum_congr rfl
    intro s hs
    rw [ENNReal.ofReal_mul (F.weight_nonneg s)]
    congr 1
    exact (elementaryModel_oneSpecies_dissipation h ε b (F.density s) τ).1
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hD, ENNReal.toReal_ofReal (Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) (hX0 s)), hX]

/-- The ordinary part of the deficit is nonnegative on EVERY absolute H1 density. -/
theorem elementary_ordinary_deficit_nonneg (h : ℝ) (ρ : AbsoluteDensity 1) :
    0 ≤ (ordinaryFisher h ρ).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  by_cases hH : ordinaryEntropy h ρ = 0
  · simp only [hH, ENNReal.toReal_zero, mul_zero, sub_zero]
    exact ENNReal.toReal_nonneg
  have hpos : 0 < ordinaryEntropy h ρ := pos_iff_ne_zero.mpr hH
  have hle : ordinaryLSRate (ordinaryReference h) ≤ str025_quot h ρ := by
    have hi : (⨅ σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ}, str025_quot h σ.1) ≤
        str025_quot h ρ :=
      iInf_le (fun σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ} => str025_quot h σ.1) ⟨ρ, hpos⟩
    exact (DGPS.Frontier.STR029.ordinaryLSRate_eq_abs_inf_STR02932 h).le.trans hi
  have hleR := ENNReal.toReal_mono (DGPS.Frontier.STR029.quot_ne_top_STR02932 h ρ hpos) hle
  change _ ≤ (ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ)).toReal at hleR
  rw [ENNReal.toReal_div, ENNReal.toReal_mul] at hleR
  norm_num only [ENNReal.toReal_ofNat] at hleR
  have hHpos : 0 < (ordinaryEntropy h ρ).toReal :=
    ENNReal.toReal_pos hH (str025_entropy_ne_top h ρ)
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * (ordinaryEntropy h ρ).toReal)).mp hleR
  linarith

/-- STR033's exact finite-species deficit identity for the actual canonical model.
There is no species-count, weight, positivity-of-density or finite-dissipation restriction. -/
theorem elementaryModel_exactDeficitExpansion {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1) :
    let a := (ordinaryLSRate (ordinaryReference h)).toReal
    let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
    let D0 := ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * a * (ordinaryEntropy h (F.density s)).toReal)
    0 ≤ D0 ∧ 0 ≤ elementaryJ h (barycenter F) ∧
    speciesDissipation (modelData h ε) b F ≠ ⊤ ∧
    2 * (speciesGap (modelData h ε) F : ℝ) =
      2 * E + ε * elementaryQ h (densityMeasure (barycenter F)) ∧
    (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) =
      D0 + ε * elementaryC h a (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) := by
  dsimp only
  obtain ⟨hDfinite, hD⟩ := elementaryModel_speciesDissipation_expansion h ε b F
  have hG := elementaryModel_speciesGap_expansion hh hε hεmax F
  refine ⟨Finset.sum_nonneg (fun s _ => mul_nonneg (F.weight_nonneg s)
    (elementary_ordinary_deficit_nonneg h (F.density s))),
    elementaryJ_nonneg h _, hDfinite, by rw [hG]; ring, ?_⟩
  rw [hD, hG]
  have hD0 : (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (F.density s)).toReal)) =
      (∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal) -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal *
          ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [hD0]
  unfold elementaryC
  ring

end DGPS.Examples.ThreeSpeciesCircle
