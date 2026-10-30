import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Variational.LocalGaussianEndpoint
import DGPS.Variational.SpeciesGap
import DGPS.Variational.WeightedScoreInformation
import DGPS.Basic.SquareRootHeatRecovery
import DGPS.Examples.ThreeSpeciesCircle.ElementaryModel

/-!
# Relative binary splits on the original absolute-density domain

The base density may vanish. Only the bounded smooth relative multiplier is
strictly positive. The barycenter is identified by its actual probability law;
the drift at that barycenter is identified a.e. by weak-gradient uniqueness.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace DGPS.Examples.PolynomialSpecies

open DGPS.PositiveRankOne

/-- The actual absolute density `(1+t*psi)*sigma`. -/
def relativeSplitDensity (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) : AbsoluteDensity 1 where
  sqrt := fun x => Real.sqrt (1 + t * ψ x) * σ.sqrt x
  sqrt_mem := by
    have hs : IsSmoothPeriodic (fun x => Real.sqrt (1 + t * ψ x)) :=
      DGPS.Lipschitz.isSmoothPeriodic_sqrt (contDiff_const.add (contDiff_const.mul hψ)) hpos
    exact ⟨_, DGPS.LocalGaussianEndpoint.mul_smooth_H1 hs
      (isWeakGradient_weakGradient σ.sqrt_mem)⟩
  sqrt_nonneg := by
    filter_upwards [σ.sqrt_nonneg] with x hx
    exact mul_nonneg (Real.sqrt_nonneg _) hx
  mass_one := by
    have hi : Integrable (fun x => σ.density x * ψ x) (haar 1) := by
      have hh := DGPS.LocalGaussianEndpoint.integrable_cont_mul' hψ.continuous_torus
        σ.integrable_density
      simpa only [mul_comm] using hh
    have hzero : ∫ x, σ.density x * ψ x ∂haar 1 = 0 := by
      rw [← RankOneModel.integral_densityMeasure]
      exact hmean
    have he : (fun x => (Real.sqrt (1 + t * ψ x) * σ.sqrt x) ^ 2) =
        fun x => σ.density x + t * (σ.density x * ψ x) := by
      funext x
      rw [mul_pow, Real.sq_sqrt (hpos x).le]
      unfold AbsoluteDensity.density
      ring
    rw [he, integral_add σ.integrable_density (hi.const_mul t), integral_const_mul,
      σ.integral_density, hzero, mul_zero, add_zero]

theorem relativeSplitDensity_density (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) (x : Torus 1) :
    (relativeSplitDensity σ ψ hψ hmean t hpos).density x = σ.density x * (1 + t * ψ x) := by
  change (Real.sqrt (1 + t * ψ x) * σ.sqrt x) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt (hpos x).le]
  unfold AbsoluteDensity.density
  ring

/-- The actual equal-weight positive and negative relative tilts. -/
def binaryRelativeSplit (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    SpeciesFamily 1 :=
  SpeciesFamily.twoSpecies (1 / 2) (by norm_num) (by norm_num)
    (relativeSplitDensity σ ψ hψ hmean t hplus)
    (relativeSplitDensity σ ψ hψ hmean (-t) hminus)

theorem binaryRelativeSplit_barycenter_density (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x)
    (x : Torus 1) :
    (barycenter (binaryRelativeSplit σ ψ hψ hmean t hplus hminus)).density x = σ.density x := by
  rw [SpeciesFamily.barycenter_density_eq_sum]
  change (∑ s : Fin 2, (if s.val = 0 then (1 / 2 : ℝ) else 1 - 1 / 2) *
    (if s.val = 0 then relativeSplitDensity σ ψ hψ hmean t hplus
      else relativeSplitDensity σ ψ hψ hmean (-t) hminus).density x) = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte,
    relativeSplitDensity_density]
  ring

theorem binaryRelativeSplit_barycenter (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    densityMeasure (barycenter (binaryRelativeSplit σ ψ hψ hmean t hplus hminus)) =
      densityMeasure σ := by
  apply Subtype.ext
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => congrArg ENNReal.ofReal
    (binaryRelativeSplit_barycenter_density σ ψ hψ hmean t hplus hminus x)

/-- Equality of the barycenter law identifies the weak drift only a.e. -/
theorem binaryRelativeSplit_force (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    b.force (barycenter (binaryRelativeSplit σ ψ hψ hmean t hplus hminus)) =ᵐ[haar 1]
      b.force σ := by
  apply b.ae_eq_of_isWeakGradient
  have hp : interactionPotential A (barycenter (binaryRelativeSplit σ ψ hψ hmean t hplus hminus)) =
      interactionPotential A σ := by
    unfold interactionPotential
    rw [binaryRelativeSplit_barycenter]
  rw [hp]
  exact b.weak_gradient σ

private theorem scalarGap_of_law_eq (A : InteractionData 1) {ρ σ : AbsoluteDensity 1}
    (h : densityMeasure ρ = densityMeasure σ) : scalarGap A ρ = scalarGap A σ := by
  apply NNReal.eq
  rw [coe_scalarGap, coe_scalarGap]
  congr 1
  apply EReal.coe_injective
  rw [coe_densityFreeEnergy, coe_densityFreeEnergy, h]

/-- Exact gap increase: the mean of the two genuine species-to-base entropies. -/
theorem binaryRelativeSplit_gap (A : InteractionData 1) (σ : AbsoluteDensity 1)
    (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    (speciesGap A (binaryRelativeSplit σ ψ hψ hmean t hplus hminus) : ℝ) =
      (scalarGap A σ : ℝ) + (1 / 2) *
        ((relativeEntropy (densityMeasure (relativeSplitDensity σ ψ hψ hmean t hplus) : Measure (Torus 1))
          (densityMeasure σ : Measure (Torus 1))).toReal +
        (relativeEntropy (densityMeasure (relativeSplitDensity σ ψ hψ hmean (-t) hminus) : Measure (Torus 1))
          (densityMeasure σ : Measure (Torus 1))).toReal) := by
  rw [SpeciesFamily.speciesGap_decomposition,
    scalarGap_of_law_eq A (binaryRelativeSplit_barycenter σ ψ hψ hmean t hplus hminus),
    binaryRelativeSplit_barycenter]
  change (scalarGap A σ : ℝ) + (∑ s : Fin 2,
    (if s.val = 0 then (1 / 2 : ℝ) else 1 - 1 / 2) *
      (relativeEntropy (densityMeasure (if s.val = 0 then relativeSplitDensity σ ψ hψ hmean t hplus
        else relativeSplitDensity σ ψ hψ hmean (-t) hminus) : Measure (Torus 1))
        (densityMeasure σ : Measure (Torus 1))).toReal) = _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte]
  ring

/-- Both signs are admissible on one neighborhood chosen after the fixed tangent. -/
theorem eventually_binaryRelativeSplit_positive (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) :
    ∀ᶠ t : ℝ in 𝓝 0, (∀ x, 0 < 1 + t * ψ x) ∧ (∀ x, 0 < 1 + (-t) * ψ x) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.continuous_torus.continuousOn
  have ht : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const B
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
  have hsmall (x : Torus 1) : |t * ψ x| < 1 := by
    rw [abs_mul]
    have hnorm : |ψ x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)
    exact (mul_le_mul_of_nonneg_left hnorm (abs_nonneg t)).trans_lt ht
  constructor <;> intro x
  · linarith [(abs_lt.mp (hsmall x)).1]
  · have hx := (abs_lt.mp (hsmall x)).2
    nlinarith


/-- The constructed species is exactly a change of density against the base law. -/
theorem relativeSplitDensity_measure (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) :
    (densityMeasure (relativeSplitDensity σ ψ hψ hmean t hpos) : Measure (Torus 1)) =
      (densityMeasure σ : Measure (Torus 1)).withDensity
        (fun x => ENNReal.ofReal (1 + t * ψ x)) := by
  change (haar 1).withDensity (fun x => ENNReal.ofReal
      ((relativeSplitDensity σ ψ hψ hmean t hpos).density x)) =
    ((haar 1).withDensity (fun x => ENNReal.ofReal (σ.density x))).withDensity _
  have htilt : Measurable (fun x : Torus 1 => 1 + t * ψ x) :=
    measurable_const.add (measurable_const.mul hψ.continuous_torus.measurable)
  rw [← withDensity_mul₀
    (σ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    htilt.ennreal_ofReal.aemeasurable]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((relativeSplitDensity σ ψ hψ hmean t hpos).density x) =
      ENNReal.ofReal (σ.density x) * ENNReal.ofReal (1 + t * ψ x)
    rw [relativeSplitDensity_density, ENNReal.ofReal_mul (σ.density_nonneg x)]

/-- The relative entropy is the finite actual KL-integrand integral. -/
theorem relativeSplitDensity_entropy (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) :
    relativeEntropy (densityMeasure (relativeSplitDensity σ ψ hψ hmean t hpos) : Measure (Torus 1))
      (densityMeasure σ : Measure (Torus 1)) = ENNReal.ofReal
        (∫ x, InformationTheory.klFun (1 + t * ψ x) ∂(densityMeasure σ : Measure (Torus 1))) := by
  have hm : ∫ x, 1 + t * ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 1 := by
    rw [integral_add (integrable_const _)
      ((hψ.continuous_torus.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul t), integral_const_mul, hmean]
    simp
  have hi : Integrable (fun x => InformationTheory.klFun (1 + t * ψ x))
      (densityMeasure σ : Measure (Torus 1)) :=
    (InformationTheory.continuous_klFun.comp (continuous_const.add
      (continuous_const.mul hψ.continuous_torus))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [relativeSplitDensity_measure, relativeEntropy_withDensity
    (Eventually.of_forall fun x => (hpos x).le)
    ((measurable_const.add (measurable_const.mul hψ.continuous_torus.measurable)).aemeasurable),
    homogeneousEntropy_eq_lintegral_klFun (by rw [hm]; exact one_ne_zero), hm]
  simp only [div_one, one_mul]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => InformationTheory.klFun_nonneg (hpos x).le)).symm

private theorem splitFactor_gradient (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) (x : Torus 1) :
    smoothGrad (fun y => Real.sqrt (1 + t * ψ y)) x =
      (t / (2 * Real.sqrt (1 + t * ψ x))) • smoothGrad ψ x := by
  have hlin : IsSmoothPeriodic (fun y => 1 + t * ψ y) :=
    contDiff_const.add (contDiff_const.mul hψ)
  have hd : DifferentiableAt ℝ (ψ ∘ torusLift) (SharpLSI.secT x) :=
    (hψ.differentiable (by simp)) _
  have hder (j : Fin 1) : coordPartial j (fun y => 1 + t * ψ y) x = t * coordPartial j ψ x := by
    unfold coordPartial
    rw [show ((fun y => 1 + t * ψ y) ∘ torusLift) =
      (fun z => 1 + t * (ψ ∘ torusLift) z) from rfl, fderiv_const_add, fderiv_const_mul hd]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ext j
  simp only [smoothGrad_apply, PiLp.smul_apply, smul_eq_mul]
  rw [DGPS.Lipschitz.coordPartial_sqrt hlin hpos, hder]
  ring

private theorem split_information (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hpos : ∀ x, 0 < 1 + t * ψ x) (F : SpeciesFamily 1) (s : Fin F.count)
    (hb : ∀ x, (barycenter F).density x = σ.density x)
    (hs : F.density s = relativeSplitDensity σ ψ hψ hmean t hpos) :
    F.scoreInformation s = ∫⁻ x, ENNReal.ofReal
      (t ^ 2 * σ.density x * ‖smoothGrad ψ x‖ ^ 2 / (1 + t * ψ x)) ∂haar 1 := by
  have hr : (barycenter F).sqrt =ᵐ[haar 1] σ.sqrt :=
    AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq (Eventually.of_forall hb)
  have hg : F.barycenterWeakGrad =ᵐ[haar 1] weakGradient σ.sqrt σ.sqrt_mem :=
    ((F.isWeakGradient_barycenterWeakGrad).congr_ae hr (EventuallyEq.refl _ _)).ae_eq
      (isWeakGradient_weakGradient σ.sqrt_mem)
  have ha : IsSmoothPeriodic (fun x => Real.sqrt (1 + t * ψ x)) :=
    DGPS.Lipschitz.isSmoothPeriodic_sqrt (contDiff_const.add (contDiff_const.mul hψ)) hpos
  have hw : IsWeakGradient (F.density s).sqrt
      (fun x => σ.sqrt x • smoothGrad (fun y => Real.sqrt (1 + t * ψ y)) x +
        Real.sqrt (1 + t * ψ x) • weakGradient σ.sqrt σ.sqrt_mem x) := by
    rw [hs]
    exact DGPS.LocalGaussianEndpoint.mul_smooth_H1 ha
      (isWeakGradient_weakGradient σ.sqrt_mem)
  have hgs := (F.isWeakGradient_sqrtGradient s).ae_eq hw
  unfold SpeciesFamily.scoreInformation
  apply lintegral_congr_ae
  filter_upwards [hr, hg, hgs, weakGradient_zero_on_zero_set σ.sqrt_mem] with x hrx hgx hgsx hz
  have hsc : F.score x = (2 * (σ.sqrt x)⁻¹) • weakGradient σ.sqrt σ.sqrt_mem x := by
    rw [SpeciesFamily.score_eq, hrx]
    exact congrArg ((2 * (σ.sqrt x)⁻¹) • ·) hgx
  have hdiff : F.scoreDifference s x =
      (t * σ.sqrt x / Real.sqrt (1 + t * ψ x)) • smoothGrad ψ x := by
    unfold SpeciesFamily.scoreDifference
    rw [hgsx, hsc, hs, splitFactor_gradient ψ hψ t hpos x]
    change (2 : ℝ) • (σ.sqrt x • ((t / (2 * Real.sqrt (1 + t * ψ x))) • smoothGrad ψ x) +
      Real.sqrt (1 + t * ψ x) • weakGradient σ.sqrt σ.sqrt_mem x) -
      (Real.sqrt (1 + t * ψ x) * σ.sqrt x) •
        ((2 * (σ.sqrt x)⁻¹) • weakGradient σ.sqrt σ.sqrt_mem x) = _
    by_cases hu : σ.sqrt x = 0
    · simp [hu, hz hu]
    · ext j
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [hu, (Real.sqrt_pos.2 (hpos x)).ne']
      <;> ring
  rw [hdiff]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, sq_abs, div_pow, mul_pow]
  rw [Real.sq_sqrt (hpos x).le]
  unfold AbsoluteDensity.density
  ring

private theorem scalarDissipation_of_density_eq (A : InteractionData 1) (b : AbsoluteDrift A)
    {ρ σ : AbsoluteDensity 1} (he : ∀ x, ρ.density x = σ.density x) :
    scalarDissipation A b ρ = scalarDissipation A b σ := by
  have hr := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq (Eventually.of_forall he)
  have hm : densityMeasure ρ = densityMeasure σ := by
    apply Subtype.ext
    apply withDensity_congr_ae
    exact Eventually.of_forall fun x => congrArg ENNReal.ofReal (he x)
  have hf : b.force ρ =ᵐ[haar 1] b.force σ := b.ae_eq_of_isWeakGradient _ (by
    have hp : interactionPotential A ρ = interactionPotential A σ := by
      unfold interactionPotential
      rw [hm]
    rw [hp]
    exact b.weak_gradient σ)
  have hg := ((isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hr
    (EventuallyEq.refl _ _)).ae_eq (isWeakGradient_weakGradient σ.sqrt_mem)
  unfold scalarDissipation scalarScore
  apply lintegral_congr_ae
  filter_upwards [hr, hf, hg] with x hx hf hg
  rw [hx, hf, hg]

/-- Exact dissipation identity, valid even when the base dissipation is infinite. -/
theorem binaryRelativeSplit_dissipation (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    speciesDissipation A b (binaryRelativeSplit σ ψ hψ hmean t hplus hminus) =
      scalarDissipation A b σ + ENNReal.ofReal (t ^ 2 *
        ∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)
          ∂(densityMeasure σ : Measure (Torus 1))) := by
  let F := binaryRelativeSplit σ ψ hψ hmean t hplus hminus
  have hb : ∀ x, (barycenter F).density x = σ.density x :=
    binaryRelativeSplit_barycenter_density σ ψ hψ hmean t hplus hminus
  have hi0 := split_information σ ψ hψ hmean t hplus F (0 : Fin 2) hb (by rfl)
  have hi1 := split_information σ ψ hψ hmean (-t) hminus F (1 : Fin 2) hb (by rfl)
  have hden (x : Torus 1) : 0 < 1 - t ^ 2 * ψ x ^ 2 := by
    have hh := mul_pos (hplus x) (hminus x)
    nlinarith
  have hc : Continuous (fun x => ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)) :=
    (hψ.continuous_smoothGrad.norm.pow 2).div
      (continuous_const.sub (continuous_const.mul (hψ.continuous_torus.pow 2)))
      (fun x => (hden x).ne')
  have hi : Integrable (fun x => σ.density x *
      (‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2))) (haar 1) := by
    simpa only [mul_comm] using DGPS.LocalGaussianEndpoint.integrable_cont_mul' hc σ.integrable_density
  have hnonneg (x : Torus 1) : 0 ≤ σ.density x *
      (‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)) :=
    mul_nonneg (σ.density_nonneg x) (div_nonneg (sq_nonneg _) (hden x).le)
  have hsum : ∑ s, ENNReal.ofReal (F.weight s) * F.scoreInformation s =
      ENNReal.ofReal (t ^ 2 * ∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)
        ∂(densityMeasure σ : Measure (Torus 1))) := by
    change (∑ s : Fin 2, ENNReal.ofReal (if s.val = 0 then (1 / 2 : ℝ) else 1 - 1 / 2) *
      F.scoreInformation s) = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, one_ne_zero, ↓reduceIte]
    rw [hi0, hi1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm : AEMeasurable (fun x => ENNReal.ofReal (1 / 2 : ℝ) *
        ENNReal.ofReal (t ^ 2 * σ.density x * ‖smoothGrad ψ x‖ ^ 2 / (1 + t * ψ x))) (haar 1) :=
      ((σ.integrable_density.aestronglyMeasurable.aemeasurable.const_mul (t ^ 2)).mul
        (hψ.continuous_smoothGrad.norm.pow 2).measurable.aemeasurable |>.div
        (measurable_const.add (measurable_const.mul hψ.continuous_torus.measurable)).aemeasurable).ennreal_ofReal.const_mul _
    rw [← lintegral_add_left' hm, RankOneModel.integral_densityMeasure, ← integral_const_mul]
    rw [ofReal_integral_eq_lintegral_ofReal (hi.const_mul (t ^ 2))
      (Eventually.of_forall fun x => mul_nonneg (sq_nonneg t) (hnonneg x))]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun x => by
      change ENNReal.ofReal (1 / 2 : ℝ) *
          ENNReal.ofReal (t ^ 2 * σ.density x * ‖smoothGrad ψ x‖ ^ 2 / (1 + t * ψ x)) +
        ENNReal.ofReal (1 - 1 / 2 : ℝ) *
          ENNReal.ofReal ((-t) ^ 2 * σ.density x * ‖smoothGrad ψ x‖ ^ 2 / (1 + (-t) * ψ x)) =
        ENNReal.ofReal (t ^ 2 * (σ.density x * (‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2))))
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2),
        ← ENNReal.ofReal_add
          (mul_nonneg (by norm_num) (div_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg t) (σ.density_nonneg x)) (sq_nonneg _)) (hplus x).le))
          (mul_nonneg (by norm_num) (div_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg (-t)) (σ.density_nonneg x)) (sq_nonneg _)) (hminus x).le))]
      congr 1
      have hmne : 1 - t * ψ x ≠ 0 := by
        simpa only [neg_mul, sub_eq_add_neg] using (hminus x).ne'
      simp only [neg_sq, neg_mul, ← sub_eq_add_neg]
      field_simp [(hplus x).ne', hmne, (hden x).ne']
      <;> ring
  rw [SpeciesFamily.speciesDissipation_decomposition, scalarDissipation_of_density_eq A b hb, hsum]


private theorem binary_kl_lower {z M : ℝ} (hM : 0 < M)
    (hp : 0 ≤ 1 + z) (hm : 0 ≤ 1 - z) (hpM : 1 + z ≤ M) (hmM : 1 - z ≤ M) :
    z ^ 2 / (2 * M) ≤ (InformationTheory.klFun (1 + z) + InformationTheory.klFun (1 - z)) / 2 := by
  have hc := (ThreeSpeciesCircle.klFun_sub_sq_convexOn hM).2
    (x := 1 + z) (y := 1 - z) ⟨hp, hpM⟩ ⟨hm, hmM⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have he : (1 / 2 : ℝ) * (1 + z) + (1 / 2 : ℝ) * (1 - z) = 1 := by ring
  simp only [smul_eq_mul, he, InformationTheory.klFun_one] at hc
  have hid : (1 / 2 : ℝ) * (InformationTheory.klFun (1 + z) - (1 / (2 * M)) * (1 + z) ^ 2) +
      (1 / 2 : ℝ) * (InformationTheory.klFun (1 - z) - (1 / (2 * M)) * (1 - z) ^ 2) -
      (0 - (1 / (2 * M)) * 1 ^ 2) =
      (InformationTheory.klFun (1 + z) + InformationTheory.klFun (1 - z)) / 2 - z ^ 2 / (2 * M) := by
    field_simp [hM.ne']
    <;> ring
  have hn := sub_nonneg.mpr hc
  rw [hid] at hn
  exact sub_nonneg.mp hn

/-- A quantitative entropy increase sufficient for the sharp local criterion. -/
theorem binaryRelativeSplit_gap_lower (A : InteractionData 1) (σ : AbsoluteDensity 1)
    (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hvar : ∫ x, ψ x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, |ψ x| ≤ B)
    (t : ℝ) (hplus : ∀ x, 0 < 1 + t * ψ x) (hminus : ∀ x, 0 < 1 + (-t) * ψ x) :
    (scalarGap A σ : ℝ) + t ^ 2 / (2 * (1 + |t| * B)) ≤
      (speciesGap A (binaryRelativeSplit σ ψ hψ hmean t hplus hminus) : ℝ) := by
  let μ := (densityMeasure σ : Measure (Torus 1))
  have hM : 0 < 1 + |t| * B := by positivity
  have hi (r : ℝ) : Integrable (fun x => InformationTheory.klFun (1 + r * ψ x)) μ :=
    (InformationTheory.continuous_klFun.comp (continuous_const.add
      (continuous_const.mul hψ.continuous_torus))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hn (r : ℝ) (hp : ∀ x, 0 < 1 + r * ψ x) :
      0 ≤ ∫ x, InformationTheory.klFun (1 + r * ψ x) ∂μ :=
    integral_nonneg fun x => InformationTheory.klFun_nonneg (hp x).le
  rw [binaryRelativeSplit_gap, relativeSplitDensity_entropy, relativeSplitDensity_entropy,
    ENNReal.toReal_ofReal (hn t hplus), ENNReal.toReal_ofReal (hn (-t) hminus)]
  refine add_le_add le_rfl ?_
  have hpt (x : Torus 1) :
      (t * ψ x) ^ 2 / (2 * (1 + |t| * B)) ≤
        (InformationTheory.klFun (1 + t * ψ x) + InformationTheory.klFun (1 + (-t) * ψ x)) / 2 := by
    have hz : |t * ψ x| ≤ |t| * B := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)
    have hp : 0 ≤ 1 + t * ψ x := (hplus x).le
    have hm : 0 ≤ 1 - t * ψ x := by simpa only [neg_mul, sub_eq_add_neg] using (hminus x).le
    have hl := binary_kl_lower hM hp hm
      (by linarith [(abs_le.mp hz).2]) (by linarith [(abs_le.mp hz).1])
    simpa only [neg_mul, sub_eq_add_neg] using hl
  have hsq : Integrable (fun x => (t * ψ x) ^ 2 / (2 * (1 + |t| * B))) μ :=
    ((continuous_const.mul hψ.continuous_torus).pow 2 |>.div_const _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hl := integral_mono hsq (((hi t).add (hi (-t))).div_const 2) hpt
  have he : (∫ x, (t * ψ x) ^ 2 / (2 * (1 + |t| * B)) ∂μ) =
      t ^ 2 / (2 * (1 + |t| * B)) := by
    simp_rw [mul_pow]
    rw [integral_div, integral_const_mul, hvar, mul_one]
  have he2 : (∫ x, (InformationTheory.klFun (1 + t * ψ x) +
      InformationTheory.klFun (1 + (-t) * ψ x)) / 2 ∂μ) =
      ((∫ x, InformationTheory.klFun (1 + t * ψ x) ∂μ) +
        (∫ x, InformationTheory.klFun (1 + (-t) * ψ x) ∂μ)) / 2 := by
    rw [integral_div, integral_add (hi t) (hi (-t))]
  simp only [Pi.add_apply] at hl
  rw [he, he2] at hl
  linarith

private theorem split_energy_bound (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ)
    (hψ : IsSmoothPeriodic ψ) {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, |ψ x| ≤ B)
    (ht : |t| * B < 1) :
    (∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)
      ∂(densityMeasure σ : Measure (Torus 1))) ≤
      (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) /
        (1 - (|t| * B) ^ 2) := by
  have hq0 : 0 ≤ |t| * B := mul_nonneg (abs_nonneg t) hB0
  have hden0 : 0 < 1 - (|t| * B) ^ 2 := by nlinarith
  have hsq (x : Torus 1) : t ^ 2 * ψ x ^ 2 ≤ (|t| * B) ^ 2 := by
    have hh : ψ x ^ 2 ≤ B ^ 2 := by
      have := (abs_le.mp (hB x))
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg t)
    simpa only [mul_pow, sq_abs] using hm
  have hden (x : Torus 1) : 0 < 1 - t ^ 2 * ψ x ^ 2 := by linarith [hsq x]
  have hc : Continuous (fun x => ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)) :=
    (hψ.continuous_smoothGrad.norm.pow 2).div
      (continuous_const.sub (continuous_const.mul (hψ.continuous_torus.pow 2)))
      (fun x => (hden x).ne')
  have hi := hc.integrable_of_hasCompactSupport (μ := (densityMeasure σ : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have hi' := ((hψ.continuous_smoothGrad.norm.pow 2).div_const (1 - (|t| * B) ^ 2)).integrable_of_hasCompactSupport
    (μ := (densityMeasure σ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hle : (∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)
      ∂(densityMeasure σ : Measure (Torus 1))) ≤
      ∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - (|t| * B) ^ 2)
        ∂(densityMeasure σ : Measure (Torus 1)) := by
    apply integral_mono hi hi'
    intro x
    exact div_le_div_of_nonneg_left (sq_nonneg _) hden0 (by linarith [hsq x])
  simpa only [integral_div] using hle

private theorem quotient_of_finite {D : ℝ≥0∞} {G : ℝ≥0} (hD : D ≠ ⊤) (hG : 0 < G) :
    ENNReal.ofReal (D.toReal / (2 * (G : ℝ))) = D / (2 * (G : ℝ≥0∞)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact mul_pos (by norm_num) hG),
    ENNReal.ofReal_toReal hD, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

/-- The conditional variational descent lemma, on the original absolute domain.
It assumes neither an optimizer nor an eigenfunction conclusion. The tangent
criterion and finiteness of the actual base dissipation are explicit. -/
theorem binaryRelativeSplit_strict_improvement (A : InteractionData 1) (b : AbsoluteDrift A)
    (σ : AbsoluteDensity 1) (ψ : Torus 1 → ℝ) (hψ : IsSmoothPeriodic ψ)
    (hmean : ∫ x, ψ x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (hvar : ∫ x, ψ x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1)
    (hG : 0 < scalarGap A σ) (hD : scalarDissipation A b σ ≠ ⊤)
    (hmargin : (∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) <
      (scalarDissipation A b σ).toReal / (2 * (scalarGap A σ : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      ∃ hplus : ∀ x, 0 < 1 + t * ψ x,
      ∃ hminus : ∀ x, 0 < 1 + (-t) * ψ x,
        let F := binaryRelativeSplit σ ψ hψ hmean t hplus hminus
        densityMeasure (barycenter F) = densityMeasure σ ∧
        0 < speciesGap A F ∧ speciesDissipation A b F ≠ ⊤ ∧
          speciesQuotient A b F < scalarQuotient A b σ := by
  let E := ∫ x, ‖smoothGrad ψ x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let R := (scalarDissipation A b σ).toReal / (2 * (scalarGap A σ : ℝ))
  have hE : 0 ≤ E := integral_nonneg fun x => sq_nonneg _
  have hR : 0 < R := hE.trans_lt hmargin
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.continuous_torus.continuousOn
  have hB' (x : Torus 1) : |ψ x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)
  have hB0 : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hB' 0)
  have hq : Tendsto (fun t : ℝ => |t| * B) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const B
  have hthreshold : 0 < (R - E) / R := div_pos (sub_pos.mpr hmargin) hR
  have hgood : ∀ᶠ t : ℝ in 𝓝 0,
      |t| * B < 1 ∧ |t| * B < (R - E) / R ∧
      (∀ x, 0 < 1 + t * ψ x) ∧ (∀ x, 0 < 1 + (-t) * ψ x) := by
    filter_upwards [hq.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hq.eventually (gt_mem_nhds hthreshold), eventually_binaryRelativeSplit_positive ψ hψ]
      with t ht hr hp
    exact ⟨ht, hr, hp.1, hp.2⟩
  obtain ⟨δ, hδ, hδprop⟩ := Metric.eventually_nhds_iff.1 hgood
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  obtain ⟨ht, hrt, hp, hm⟩ := hδprop (by simpa only [Real.dist_eq, sub_zero] using htδ)
  refine ⟨hp, hm, ?_⟩
  let F := binaryRelativeSplit σ ψ hψ hmean t hp hm
  have hgap := binaryRelativeSplit_gap_lower A σ ψ hψ hmean hvar hB0 hB' t hp hm
  have hGt : 0 < speciesGap A F := by
    change (0 : ℝ) < (speciesGap A F : ℝ)
    have hh : 0 ≤ t ^ 2 / (2 * (1 + |t| * B)) := by positivity
    exact lt_of_lt_of_le (show (0 : ℝ) < (scalarGap A σ : ℝ) + t ^ 2 / (2 * (1 + |t| * B)) by
      exact add_pos_of_pos_of_nonneg hG hh) hgap
  let J := ∫ x, ‖smoothGrad ψ x‖ ^ 2 / (1 - t ^ 2 * ψ x ^ 2)
    ∂(densityMeasure σ : Measure (Torus 1))
  have hq0 : 0 ≤ |t| * B := mul_nonneg (abs_nonneg t) hB0
  have h1q : 0 < 1 - |t| * B := sub_pos.mpr ht
  have hplusq : 0 < 1 + |t| * B := by positivity
  have hden : 0 < 1 - (|t| * B) ^ 2 := by nlinarith
  have hJ0 : 0 ≤ J := integral_nonneg fun x => div_nonneg (sq_nonneg _) (by
    have hh := mul_pos (hp x) (hm x)
    nlinarith)
  have hJ := split_energy_bound σ ψ hψ hB0 hB' ht
  have hJR : J < R / (1 + |t| * B) := by
    have he : E < R * (1 - |t| * B) := by
      have hrt' := (lt_div_iff₀ hR).1 hrt
      nlinarith
    have hstrict : E / (1 - (|t| * B) ^ 2) < R / (1 + |t| * B) := by
      rw [div_lt_div_iff₀ hden hplusq]
      have hh := mul_lt_mul_of_pos_right he hplusq
      nlinarith
    exact hJ.trans_lt hstrict
  have hdt : speciesDissipation A b F = scalarDissipation A b σ + ENNReal.ofReal (t ^ 2 * J) :=
    binaryRelativeSplit_dissipation A b σ ψ hψ hmean t hp hm
  have hDt : speciesDissipation A b F ≠ ⊤ := by
    rw [hdt]
    exact ENNReal.add_ne_top.mpr ⟨hD, ENNReal.ofReal_ne_top⟩
  have hdtR : (speciesDissipation A b F).toReal = (scalarDissipation A b σ).toReal + t ^ 2 * J := by
    rw [hdt, ENNReal.toReal_add hD ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg t) hJ0)]
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero (abs_pos.mp ht0)
  have hDbase : (scalarDissipation A b σ).toReal = 2 * R * (scalarGap A σ : ℝ) := by
    dsimp only [R]
    field_simp [ne_of_gt (show (0 : ℝ) < (scalarGap A σ : ℝ) from hG)]
  have hcross : (speciesDissipation A b F).toReal < 2 * R * (speciesGap A F : ℝ) := by
    rw [hdtR]
    calc _ < (scalarDissipation A b σ).toReal + t ^ 2 * (R / (1 + |t| * B)) :=
        add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left hJR ht2)
      _ = 2 * R * ((scalarGap A σ : ℝ) + t ^ 2 / (2 * (1 + |t| * B))) := by
        rw [hDbase]
        field_simp
        <;> ring
      _ ≤ 2 * R * (speciesGap A F : ℝ) := mul_le_mul_of_nonneg_left hgap (by positivity)
  have hreal : (speciesDissipation A b F).toReal / (2 * (speciesGap A F : ℝ)) < R := by
    have hGtReal : (0 : ℝ) < (speciesGap A F : ℝ) := hGt
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hGtReal)).2
    nlinarith [hcross]
  refine ⟨binaryRelativeSplit_barycenter σ ψ hψ hmean t hp hm, hGt, hDt, ?_⟩
  unfold speciesQuotient scalarQuotient
  rw [← quotient_of_finite hDt hGt, ← quotient_of_finite hD hG]
  exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hreal, hR⟩

end DGPS.Examples.PolynomialSpecies
