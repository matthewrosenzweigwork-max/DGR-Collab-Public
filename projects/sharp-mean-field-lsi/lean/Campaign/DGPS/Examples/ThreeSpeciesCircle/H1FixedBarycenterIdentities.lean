import DGPS.Examples.ThreeSpeciesCircle.H1FixedBarycenterSplit

/-! Exact entropy and score identities for the genuine finite H1 split. These
identities precede the second-order limit and keep the actual weak gradients. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem relativeH1SplitDensity_gradient (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) :
    IsWeakGradient (relativeH1SplitDensity σ g G hg hgc hm t hp).sqrt
      (fun x => σ.sqrt x • ((t / (2 * Real.sqrt (1 + t * g x))) • G x) +
        Real.sqrt (1 + t * g x) • weakGradient σ.sqrt σ.sqrt_mem x) := by
  have hlin := (isWeakGradient_const (d := 1) 1).add (hg.smul t)
  have hs := continuousH1_sqrt_gradient hlin
    (continuous_const.add (continuous_const.mul hgc)) hp
  have hs' : IsWeakGradient (fun x => Real.sqrt (1 + t * g x))
      (fun x => (t / (2 * Real.sqrt (1 + t * g x))) • G x) := by
    refine hs.congr_ae (Eventually.of_forall fun _ => rfl)
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.zero_apply, zero_add, smul_smul, div_eq_mul_inv, mul_comm]
  exact hs'.mul_one_dim (isWeakGradient_weakGradient σ.sqrt_mem)

theorem relativeH1SplitDensity_measure (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) :
    (densityMeasure (relativeH1SplitDensity σ g G hg hgc hm t hp) : Measure (Torus 1)) =
      (densityMeasure σ : Measure (Torus 1)).withDensity
        (fun x => ENNReal.ofReal (1 + t * g x)) := by
  change (haar 1).withDensity (fun x => ENNReal.ofReal
      ((relativeH1SplitDensity σ g G hg hgc hm t hp).density x)) =
    ((haar 1).withDensity (fun x => ENNReal.ofReal (σ.density x))).withDensity _
  have htilt : Measurable (fun x : Torus 1 => 1 + t * g x) :=
    measurable_const.add (measurable_const.mul hgc.measurable)
  rw [← withDensity_mul₀
    (σ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    htilt.ennreal_ofReal.aemeasurable]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((relativeH1SplitDensity σ g G hg hgc hm t hp).density x) =
      ENNReal.ofReal (σ.density x) * ENNReal.ofReal (1 + t * g x)
    rw [relativeH1SplitDensity_density, ENNReal.ofReal_mul (σ.density_nonneg x)]

theorem relativeH1SplitDensity_entropy (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) :
    relativeEntropy (densityMeasure (relativeH1SplitDensity σ g G hg hgc hm t hp) : Measure (Torus 1))
      (densityMeasure σ : Measure (Torus 1)) =
      ENNReal.ofReal (∫ x, InformationTheory.klFun (1 + t * g x)
        ∂(densityMeasure σ : Measure (Torus 1))) := by
  have hmass : ∫ x, 1 + t * g x ∂(densityMeasure σ : Measure (Torus 1)) = 1 := by
    rw [integral_add (integrable_const _)
      ((hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul t),
      integral_const_mul, hm]
    simp
  have hi : Integrable (fun x => InformationTheory.klFun (1 + t * g x))
      (densityMeasure σ : Measure (Torus 1)) :=
    (InformationTheory.continuous_klFun.comp
      (continuous_const.add (continuous_const.mul hgc))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [relativeH1SplitDensity_measure, relativeEntropy_withDensity
    (Eventually.of_forall fun x => (hp x).le)
    ((measurable_const.add (measurable_const.mul hgc.measurable)).aemeasurable),
    homogeneousEntropy_eq_lintegral_klFun (by rw [hmass]; exact one_ne_zero), hmass]
  simp only [div_one, one_mul]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => InformationTheory.klFun_nonneg (hp x).le)).symm

/-- Exact information of one original H1 relative tilt in any actual family
whose barycenter density is the base density. Zero sets of the base are allowed. -/
theorem relativeH1SplitDensity_scoreInformation (σ : AbsoluteDensity 1) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hgc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ x, 0 < 1 + t * g x) (F : SpeciesFamily 1) (s : Fin F.count)
    (hb : ∀ x, (barycenter F).density x = σ.density x)
    (hs : F.density s = relativeH1SplitDensity σ g G hg hgc hm t hp) :
    F.scoreInformation s = ∫⁻ x, ENNReal.ofReal
      (t ^ 2 * σ.density x * ‖G x‖ ^ 2 / (1 + t * g x)) ∂haar 1 := by
  have hr : (barycenter F).sqrt =ᵐ[haar 1] σ.sqrt :=
    AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq (Eventually.of_forall hb)
  have hbg : F.barycenterWeakGrad =ᵐ[haar 1] weakGradient σ.sqrt σ.sqrt_mem :=
    ((F.isWeakGradient_barycenterWeakGrad).congr_ae hr (EventuallyEq.refl _ _)).ae_eq
      (isWeakGradient_weakGradient σ.sqrt_mem)
  have hw : IsWeakGradient (F.density s).sqrt
      (fun x => σ.sqrt x • ((t / (2 * Real.sqrt (1 + t * g x))) • G x) +
        Real.sqrt (1 + t * g x) • weakGradient σ.sqrt σ.sqrt_mem x) := by
    rw [hs]
    exact relativeH1SplitDensity_gradient σ g G hg hgc hm t hp
  have hsg := (F.isWeakGradient_sqrtGradient s).ae_eq hw
  unfold SpeciesFamily.scoreInformation
  apply lintegral_congr_ae
  filter_upwards [hr, hbg, hsg, weakGradient_zero_on_zero_set σ.sqrt_mem]
    with x hrx hbgx hsgx hz
  have hsc : F.score x = (2 * (σ.sqrt x)⁻¹) • weakGradient σ.sqrt σ.sqrt_mem x := by
    rw [SpeciesFamily.score_eq, hrx]
    exact congrArg ((2 * (σ.sqrt x)⁻¹) • ·) hbgx
  have hdiff : F.scoreDifference s x =
      (t * σ.sqrt x / Real.sqrt (1 + t * g x)) • G x := by
    unfold SpeciesFamily.scoreDifference
    rw [hsgx, hsc, hs]
    change (2 : ℝ) • (σ.sqrt x • ((t / (2 * Real.sqrt (1 + t * g x))) • G x) +
      Real.sqrt (1 + t * g x) • weakGradient σ.sqrt σ.sqrt_mem x) -
      (Real.sqrt (1 + t * g x) * σ.sqrt x) •
        ((2 * (σ.sqrt x)⁻¹) • weakGradient σ.sqrt σ.sqrt_mem x) = _
    by_cases hu : σ.sqrt x = 0
    · simp [hu, hz hu]
    · ext j
      simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      field_simp [hu, (Real.sqrt_pos.2 (hp x)).ne']
      <;> ring
  rw [hdiff]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs, sq_abs, div_pow, mul_pow]
  rw [Real.sq_sqrt (hp x).le]
  unfold AbsoluteDensity.density
  ring

private theorem scalarGap_of_split_law (A : InteractionData 1) {ρ σ : AbsoluteDensity 1}
    (he : densityMeasure ρ = densityMeasure σ) : scalarGap A ρ = scalarGap A σ := by
  apply NNReal.eq
  rw [coe_scalarGap, coe_scalarGap]
  congr 1
  apply EReal.coe_injective
  rw [coe_densityFreeEnergy, coe_densityFreeEnergy, he]

private theorem scalarDissipation_of_split_density (A : InteractionData 1) (b : AbsoluteDrift A)
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
  have hgrad := ((isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hr
    (EventuallyEq.refl _ _)).ae_eq (isWeakGradient_weakGradient σ.sqrt_mem)
  unfold scalarDissipation scalarScore
  apply lintegral_congr_ae
  filter_upwards [hr, hf, hgrad] with x hx hf hg
  rw [hx, hf, hg]

section Finite
variable (σ : AbsoluteDensity 1) (q : ℕ+) (θ : Fin q → ℝ)
  (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1)
  (g : Fin q → Torus 1 → ℝ) (G : Fin q → Torus 1 → Tangent 1)
  (hg : ∀ s, IsWeakGradient (g s) (G s)) (hgc : ∀ s, Continuous (g s))
  (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
  (hcancel : ∀ x, ∑ s, θ s * g s x = 0)
  (t : ℝ) (hp : ∀ s x, 0 < 1 + t * g s x)

include hcancel

/-- Actual finite entropy increase, with no smoothness assumption on tangents. -/
theorem finiteH1Split_gap (A : InteractionData 1) :
    (speciesGap A (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp) : ℝ) =
      (scalarGap A σ : ℝ) + ∑ s, θ s *
        ∫ x, InformationTheory.klFun (1 + t * g s x) ∂(densityMeasure σ : Measure (Torus 1)) := by
  rw [SpeciesFamily.speciesGap_decomposition,
    scalarGap_of_split_law A (finiteH1Split_barycenter σ q θ hθ hθsum g G hg hgc hm hcancel t hp),
    finiteH1Split_barycenter σ q θ hθ hθsum g G hg hgc hm hcancel t hp]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change θ s * (relativeEntropy (densityMeasure
    (relativeH1SplitDensity σ (g s) (G s) (hg s) (hgc s) (hm s) t (hp s)) : Measure (Torus 1))
    (densityMeasure σ : Measure (Torus 1))).toReal = _
  rw [relativeH1SplitDensity_entropy, ENNReal.toReal_ofReal
    (integral_nonneg fun x => InformationTheory.klFun_nonneg (hp s x).le)]

/-- Exact extended dissipation identity on the actual finite split, including
an infinite base dissipation. The barycenter force is identified only a.e. -/
theorem finiteH1Split_dissipation (A : InteractionData 1) (b : AbsoluteDrift A) :
    speciesDissipation A b (finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp) =
      scalarDissipation A b σ + ∑ s, ENNReal.ofReal (θ s) *
        ∫⁻ x, ENNReal.ofReal
          (t ^ 2 * σ.density x * ‖G s x‖ ^ 2 / (1 + t * g s x)) ∂haar 1 := by
  let F := finiteH1Split σ q θ hθ hθsum g G hg hgc hm t hp
  have hb : ∀ x, (barycenter F).density x = σ.density x :=
    finiteH1Split_barycenter_density σ q θ hθ hθsum g G hg hgc hm hcancel t hp
  rw [SpeciesFamily.speciesDissipation_decomposition,
    scalarDissipation_of_split_density A b hb]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  change ENNReal.ofReal (θ s) * F.scoreInformation s = _
  rw [relativeH1SplitDensity_scoreInformation σ (g s) (G s) (hg s) (hgc s) (hm s)
    t (hp s) F s hb (by rfl)]

end Finite
end DGPS.Examples.ThreeSpeciesCircle
