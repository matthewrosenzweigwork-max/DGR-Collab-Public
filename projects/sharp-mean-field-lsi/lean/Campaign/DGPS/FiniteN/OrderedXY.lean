import DGPS.FiniteN.CriticalXYRows
import DGPS.FiniteN.RotationalTools
import DGPS.FiniteN.OrderedRadialLift
import DGPS.FiniteN.OrderedRadialNormalization

open MeasureTheory
open scoped ENNReal ContDiff Matrix

namespace DGPS.FiniteN

open DGPS DGPS.Circle.AngularNormalization DGPS.FiniteN.Tools
  DGPS.FiniteN.Tools.UniformVonMises DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.UnitTorusNormalization DGPS.FiniteN.Tools.ConditionalEntropyPinsker
  DGPS.FiniteN.Tools.AngularAssembly DGPS.Circle.BesselMoments

/-- `D = κ I` -/
noncomputable def orderedD_FIN046 (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun _ => κ

theorem orderedD_posDef_FIN046 {κ : ℝ} (hκ : 0 < κ) : (orderedD_FIN046 κ).PosDef := by
  unfold orderedD_FIN046
  simp [Matrix.posDef_diagonal_iff, hκ]

theorem orderedD_inv_FIN046 {κ : ℝ} (hκ : κ ≠ 0) :
    (orderedD_FIN046 κ)⁻¹ = Matrix.diagonal fun _ => κ⁻¹ := by
  unfold orderedD_FIN046
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; field_simp

theorem quadForm_orderedD_inv_FIN046 {κ : ℝ} (hκ : κ ≠ 0) (v : Fin 2 → ℝ) :
    Hubbard.quadForm (orderedD_FIN046 κ)⁻¹ v = (v 0 ^ 2 + v 1 ^ 2) / κ := by
  rw [orderedD_inv_FIN046 hκ]
  simp [Hubbard.quadForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  field_simp

/-- The ordered XY interaction data: `V = 0`, `W(x,y) = κ(1 - cos 2π(x-y))`. -/
def IsOrderedXY_FIN046 (κ : ℝ) (A : InteractionData 1) : Prop :=
  (∀ x, A.V x = 0) ∧
    ∀ s t : ℝ, A.W (torusLift fun _ => s) (torusLift fun _ => t) =
      κ * (1 - Real.cos (2 * Real.pi * (s - t)))

theorem angV_ordered_FIN046 {κ : ℝ} {A : InteractionData 1} (hA : IsOrderedXY_FIN046 κ A) :
    angV A = fun _ => (0 : ℝ) := by
  funext θ; exact hA.1 _

theorem angW_ordered_FIN046 {κ : ℝ} {A : InteractionData 1} (hA : IsOrderedXY_FIN046 κ A)
    (a b : AngCircle) :
    angW A a b = κ - κ * (phi a ⬝ᵥ phi b) := by
  induction a using QuotientAddGroup.induction_on with
  | H s =>
  induction b using QuotientAddGroup.induction_on with
  | H t =>
  unfold angW
  rw [angEquiv_symm_coe, angEquiv_symm_coe, hA.2]
  have e : 2 * Real.pi * (s / (2 * Real.pi) - t / (2 * Real.pi)) = s - t := by
    field_simp
  rw [e, Real.cos_sub]
  have hs := phi_coe s
  have ht := phi_coe t
  rw [hs, ht]
  simp [dotProduct, Fin.sum_univ_two]
  ring

theorem dot_orderedD_FIN046 (κ : ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ orderedD_FIN046 κ *ᵥ v = κ * (v ⬝ᵥ v) := by
  simp [orderedD_FIN046, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

theorem angHamiltonian_ordered_FIN046 {κ : ℝ} {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) (N : ℕ+) (θ : AngParticleSpace N) :
    angHamiltonian (angV A) (angW A) N θ =
      κ * (N : ℝ) / 2 -
        κ * (Hubbard.fieldSum phi θ ⬝ᵥ Hubbard.fieldSum phi θ) / (2 * N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold angHamiltonian
  simp_rw [angV_ordered_FIN046 hA, angW_ordered_FIN046 hA]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_phi_dot]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem particleWeight_ordered_FIN046 (κ : ℝ) (N : ℕ+) (θ : AngParticleSpace N) :
    Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi (orderedD_FIN046 κ)
        (fun _ : Fin 2 => (0 : ℝ)) N θ =
      Real.exp (κ * (Hubbard.fieldSum phi θ ⬝ᵥ Hubbard.fieldSum phi θ) / (2 * N)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold Hubbard.particleWeight
  rw [dot_orderedD_FIN046]
  congr 1
  simp

theorem angDensity_ordered_FIN046 {κ : ℝ} {A : InteractionData 1} (hA : IsOrderedXY_FIN046 κ A)
    (N : ℕ+) (θ : AngParticleSpace N) :
    ENNReal.ofReal (angDensity (angV A) (angW A) N θ) =
      ENNReal.ofReal ((angPartition (angV A) (angW A) N)⁻¹ * Real.exp (-(κ * (N : ℝ) / 2))) *
        ENNReal.ofReal (Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi
          (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ)) N θ) := by
  have hZ : 0 ≤ angPartition (angV A) (angW A) N := integral_nonneg fun _ => (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul (by positivity), particleWeight_ordered_FIN046]
  congr 1
  unfold angDensity
  rw [angHamiltonian_ordered_FIN046 hA, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem particleLaw_ordered_FIN046 {κ : ℝ} (hκ : 0 < κ) {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) (N : ℕ+) :
    angParticleLaw (angV A) (angW A) N =
      Hubbard.hubbardParticleLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
        (fun _ : AngCircle => (0 : ℝ)) phi angHaar N := by
  have hP : IsProbabilityMeasure (angParticleLaw (angV A) (angW A) N) := by
    rw [← map_particleLaw A N]
    exact (Measure.isProbabilityMeasure_map_iff (angEquivN N).measurable.aemeasurable).2
      inferInstance
  have hH := AuxiliaryTransfer.isProbabilityMeasure_particleLaw hubbardHyp_angular
    (orderedD_posDef_FIN046 hκ) (fun _ : Fin 2 => (0 : ℝ)) N
  set ν : Measure (AngParticleSpace N) := (angParticleHaar N).withDensity fun θ =>
    ENNReal.ofReal (Hubbard.particleWeight (fun _ : AngCircle => (0 : ℝ)) phi (orderedD_FIN046 κ)
          (fun _ : Fin 2 => (0 : ℝ)) N θ) with hν
  have e1 : angParticleLaw (angV A) (angW A) N =
      ENNReal.ofReal ((angPartition (angV A) (angW A) N)⁻¹ * Real.exp (-(κ * (N : ℝ) / 2))) • ν := by
    unfold angParticleLaw
    simp_rw [angDensity_ordered_FIN046 hA N]
    rw [hν]
    exact withDensity_smul' _ _ ENNReal.ofReal_ne_top
  have e2 : Hubbard.hubbardParticleLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N =
      (Hubbard.particleMass (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
        (fun _ : AngCircle => (0 : ℝ)) phi angHaar N)⁻¹ • ν := rfl
  rw [e1, e2]
  rw [e1] at hP
  rw [e2] at hH
  exact eq_of_prob_smul hP hH

theorem auxPotential_ordered_FIN046 {κ : ℝ} (hκ : κ ≠ 0) (w : Fin 2 → ℝ) :
    Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi (orderedD_FIN046 κ)
        (fun _ : Fin 2 => (0 : ℝ)) angHaar w =
      radialPsi_orad κ ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖ := by
  have hZ : Hubbard.auxPartition (fun _ : AngCircle => (0 : ℝ)) phi angHaar w =
      besselI 0 ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖ := by
    rw [← vmNorm_eq_bessel]
    unfold Hubbard.auxPartition Hubbard.expTerm vmNorm
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [sub_zero]
    rw [show w ⬝ᵥ phi θ = vmPhase (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) θ from dot_phi _ θ]
  unfold Hubbard.auxPotential radialPsi_orad
  have hw : w - (fun _ : Fin 2 => (0 : ℝ)) = w := by funext i; simp
  rw [hZ, hw, quadForm_orderedD_inv_FIN046 hκ, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have : 0 ≤ ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by positivity
  rw [Real.sq_sqrt this]
  simp only [Real.norm_eq_abs, sq_abs]
  field_simp


theorem continuous_radialPsi_orad_FIN046 (κ : ℝ) : Continuous (radialPsi_orad κ) :=
  continuous_iff_continuousAt.2 fun r => (psi_hasDerivAt_orad r).continuousAt

/-- the auxiliary law `η_N ∝ exp(-N ψ(‖z‖))` on `ℝ²` -/
noncomputable def orderedAuxiliaryLaw_FIN046 (κ N : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  StrongConvexityLSI.gibbs (fun z : EuclideanSpace ℝ (Fin 2) => N * radialPsi_orad κ ‖z‖)

theorem auxLaw_map_ordered_FIN046 {κ : ℝ} (hκ : 0 < κ) (N : ℕ+) :
    (Hubbard.auxLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ))
        phi angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) =
      orderedAuxiliaryLaw_FIN046 κ (N : ℝ) := by
  set G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-(N : ℝ) * radialPsi_orad κ ‖z‖)) with hG
  set ν : Measure (EuclideanSpace ℝ (Fin 2)) := volume.withDensity G with hν
  have hF : (fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi (orderedD_FIN046 κ)
        (fun _ : Fin 2 => (0 : ℝ)) angHaar w))) = fun w => G (WithLp.toLp 2 w) := by
    funext w
    simp only [hG, auxPotential_ordered_FIN046 hκ.ne']
  have hmap : ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w : Fin 2 → ℝ =>
      ENNReal.ofReal (Real.exp (-(N : ℝ) *
      Hubbard.auxPotential (fun _ : AngCircle => (0 : ℝ)) phi (orderedD_FIN046 κ)
        (fun _ : Fin 2 => (0 : ℝ)) angHaar w)))).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = ν := by
    refine Measure.ext fun s hs => ?_
    rw [hF]
    exact map_withDensity_toLp G s hs
  have e1 : (Hubbard.auxLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
        (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) =
      (Hubbard.auxMass (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
        (fun _ : AngCircle => (0 : ℝ)) phi angHaar N)⁻¹ • ν := by
    unfold Hubbard.auxLaw
    rw [Measure.map_smul, hmap]
    exact (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable
  have hmass : ν Set.univ = Hubbard.auxMass (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N := by
    rw [← hmap, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 2) => radialPsi_orad κ ‖z‖) :=
    (continuous_radialPsi_orad_FIN046 κ).comp continuous_norm
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-((N : ℝ) * radialPsi_orad κ ‖z‖))) := by
    have hm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-((N : ℝ) * radialPsi_orad κ ‖z‖))) volume :=
      (Real.continuous_exp.comp (continuous_const.mul hcont).neg).aestronglyMeasurable
    rw [← lintegral_ofReal_ne_top_iff_integrable hm (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    have : ∫⁻ z : EuclideanSpace ℝ (Fin 2),
        ENNReal.ofReal (Real.exp (-((N : ℝ) * radialPsi_orad κ ‖z‖))) = ν Set.univ := by
      rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      simp only [hG, neg_mul]
    rw [this, hmass]
    exact Hubbard.auxMass_ne_top hubbardHyp_angular (orderedD_posDef_FIN046 hκ) _ N
  have hgib : IsProbabilityMeasure (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) :=
    StrongConvexityLSI.gibbs_isProbabilityMeasure hint
  have e2 : orderedAuxiliaryLaw_FIN046 κ (N : ℝ) = ENNReal.ofReal
      ((∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-((N : ℝ) * radialPsi_orad κ ‖y‖)))⁻¹) • ν := by
    unfold orderedAuxiliaryLaw_FIN046 StrongConvexityLSI.gibbs
    rw [hν, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    have hZ : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-((N : ℝ) * radialPsi_orad κ ‖y‖)) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    simp only [hG, neg_mul, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  have hP1 : IsProbabilityMeasure ((Hubbard.auxLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ))
      (fun _ : AngCircle => (0 : ℝ)) phi angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) := by
    have := AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_angular
      (orderedD_posDef_FIN046 hκ) (fun _ : Fin 2 => (0 : ℝ)) N
    exact (Measure.isProbabilityMeasure_map_iff
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable).2 this
  rw [e1, e2]
  rw [e1] at hP1
  rw [e2] at hgib
  exact eq_of_prob_smul hP1 hgib

section PolarC_FIN046
open Set Real
open DGPS.FiniteN.Tools.PlanarPoincare

theorem lintegral_Ioc_shift_FIN046 {Φ : ℝ → ℝ≥0∞} (hΦ : Function.Periodic Φ (2 * π)) :
    ∫⁻ θ in Ioc 0 (2 * π), Φ θ = ∫⁻ θ in Ioc (-π) π, Φ θ := by
  have : Fact (0 < 2 * π) := ⟨by positivity⟩
  have h1 := AddCircle.lintegral_preimage (2 * π) 0 (hΦ.lift)
  have h2 := AddCircle.lintegral_preimage (2 * π) (-π) (hΦ.lift)
  simp only [Function.Periodic.lift_coe, zero_add] at h1 h2
  rw [h1]
  have : -π + 2 * π = π := by ring
  rw [this] at h2
  rw [h2]

theorem lintegral_radial_polar_FIN046 (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    ∫⁻ p, g p * k (√(p.1 ^ 2 + p.2 ^ 2)) =
      ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ r in Ioi 0, ENNReal.ofReal r * k r * g (polar (θ, r)) := by
  rw [← lintegral_comp_polarCoord_symm]
  simp only [smul_eq_mul]
  have hT : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hfun : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 * (g (polarCoord.symm p) * k (√((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2))) =
        ENNReal.ofReal p.1 * k p.1 * g (polar (p.2, p.1)) := by
    intro p hp
    have hr : 0 < p.1 := hp.1
    have : √((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) = p.1 := by
      simp only [polarCoord_symm_apply]
      rw [show (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 by
        nlinarith [Real.sin_sq_add_cos_sq p.2]]
      exact Real.sqrt_sq hr.le
    rw [this]
    simp only [polarCoord_symm_apply, polar]
    ring
  rw [setLIntegral_congr_fun (polarCoord.open_target.measurableSet) hfun]
  rw [hT, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 * k p.1 * g (polar (p.2, p.1)) := by
    have : Measurable fun p : ℝ × ℝ => polar (p.2, p.1) :=
      continuous_polar.measurable.comp (measurable_snd.prodMk measurable_fst)
    exact ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hk.comp measurable_fst)).mul
      (hg.comp this)
  rw [lintegral_prod _ hmeas.aemeasurable]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  set Φ : ℝ → ℝ≥0∞ := fun θ => ∫⁻ r in Ioi 0, ENNReal.ofReal r * k r * g (polar (θ, r)) with hΦ
  have hper : Function.Periodic Φ (2 * π) := by
    intro θ
    simp only [hΦ, polar, Real.cos_add_two_pi, Real.sin_add_two_pi]
  calc ∫⁻ y in Ioo (-π) π, Φ y = ∫⁻ y in Ioc (-π) π, Φ y := setLIntegral_congr Ioo_ae_eq_Ioc
    _ = ∫⁻ y in Ioc 0 (2 * π), Φ y := (lintegral_Ioc_shift_FIN046 hper).symm


/-- unnormalised planar Gibbs measure `exp(-N ψ(|p|)) dp` -/
noncomputable def orderedPlanarMeasure_FIN046 (κ N : ℝ) : Measure (ℝ × ℝ) :=
  volume.withDensity fun p => ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ (√(p.1 ^ 2 + p.2 ^ 2)))))

theorem rotational_eq_smul_FIN046 {κ r0 N : ℝ}
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N) :
    rotationalMeasure (orderedRadialLaw_FIN035 κ r0 N) =
      (ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal (Real.exp (N * radialPsi_orad κ r0) /
        orderedRadialZ_FIN035 κ r0 N)) • orderedPlanarMeasure_FIN046 κ N := by
  set Z := orderedRadialZ_FIN035 κ r0 N with hZdef
  set C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (N * radialPsi_orad κ r0) / Z) with hC
  set k : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ r))) with hk
  have hkm : Measurable k :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((continuous_const.mul (continuous_radialPsi_orad_FIN046 κ)).neg).measurable))
  have hρ : Measurable fun r => ENNReal.ofReal
      (orderedRadialWeight_FIN035 κ r0 N r / Z) :=
    ((orderedRadialWeight_measurable_FIN035 κ r0 N).div_const _).ennreal_ofReal
  have key : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ p, g p ∂(rotationalMeasure (orderedRadialLaw_FIN035 κ r0 N)) =
        (ENNReal.ofReal (2 * π)⁻¹ * C) * ∫⁻ p, g p * k (√(p.1 ^ 2 + p.2 ^ 2)) := by
    intro g hg
    rw [lintegral_radial_polar_FIN046 g hg k hkm]
    unfold rotationalMeasure
    rw [lintegral_map hg continuous_polar.measurable]
    have hgp : Measurable fun q : ℝ × ℝ => g (polar q) := hg.comp continuous_polar.measurable
    have hσ : orderedRadialLaw_FIN035 κ r0 N = volume.withDensity
        (fun r => ENNReal.ofReal (orderedRadialWeight_FIN035 κ r0 N r / Z)) := rfl
    have : SFinite (orderedRadialLaw_FIN035 κ r0 N) := by rw [hσ]; infer_instance
    rw [lintegral_prod _ hgp.aemeasurable]
    unfold angleLaw
    rw [lintegral_smul_measure, smul_eq_mul, mul_assoc,
      ← lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    congr 1
    refine lintegral_congr fun θ => ?_
    have hm : Measurable fun r : ℝ => g (polar (θ, r)) := hgp.comp measurable_prodMk_left
    rw [hσ, lintegral_withDensity_eq_lintegral_mul _ hρ hm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun r => ?_
    by_cases hr : 0 < r
    · simp only [Set.indicator, Set.mem_Ioi, hr, ite_true, Pi.mul_apply, orderedRadialWeight_FIN035,
        radialU_orad, hk]
      have hB : 0 ≤ Real.exp (N * radialPsi_orad κ r0) / Z := by positivity
      rw [← ENNReal.ofReal_mul hr.le, ← mul_assoc, ← ENNReal.ofReal_mul hB]
      congr 2
      rw [show -N * (radialPsi_orad κ r - radialPsi_orad κ r0) =
        N * radialPsi_orad κ r0 + -(N * radialPsi_orad κ r) by ring, Real.exp_add]
      ring
    · simp [Set.indicator, hr, orderedRadialWeight_FIN035]
  refine Measure.ext fun s hs => ?_
  have h1 := key (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h1
  rw [h1, Measure.smul_apply, smul_eq_mul, orderedPlanarMeasure_FIN046, withDensity_apply _ hs,
    ← lintegral_indicator hs]
  congr 1
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ s <;> simp [Set.indicator, hp, hk]


/-- `ℓ` on the Euclidean plane: `‖ℓ‖² = ℓ(e₀)² + ℓ(e₁)²`. -/
theorem norm_sq_clm_FIN046 (ℓ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :
    ‖ℓ‖ ^ 2 = ℓ (EuclideanSpace.single 0 1) ^ 2 + ℓ (EuclideanSpace.single 1 1) ^ 2 := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm ℓ with hv
  have h1 : ‖v‖ = ‖ℓ‖ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.norm_map ℓ
  have h2 : ∀ x, inner ℝ v x = ℓ x := fun x =>
    InnerProductSpace.toDual_symm_apply
  rw [← h1, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two,
    ← h2, ← h2]
  simp [EuclideanSpace.inner_single_right]

/-- the measurable identification `ℝ² ≃ ℝ × ℝ` -/
noncomputable def eEq_FIN046 : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem eEq_apply_FIN046 (z : EuclideanSpace ℝ (Fin 2)) : eEq_FIN046 z = (z 0, z 1) := rfl

theorem eEq_volume_FIN046 : MeasurePreserving eEq_FIN046 :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_toLp (Fin 2)).symm


/-- the inverse of `eEq_FIN046` as a continuous linear map -/
noncomputable def invL_FIN046 : ℝ × ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

theorem invL_apply_FIN046 (p : ℝ × ℝ) :
    invL_FIN046 p = eEq_FIN046.symm p := by
  ext i
  fin_cases i <;> simp [invL_FIN046, eEq_FIN046, MeasurableEquiv.finTwoArrow]

theorem invL_eEq_FIN046 (z : EuclideanSpace ℝ (Fin 2)) : invL_FIN046 (eEq_FIN046 z) = z := by
  rw [invL_apply_FIN046]; exact eEq_FIN046.symm_apply_apply z

theorem eEq_invL_FIN046 (p : ℝ × ℝ) : eEq_FIN046 (invL_FIN046 p) = p := by
  rw [invL_apply_FIN046]; exact eEq_FIN046.apply_symm_apply p

theorem gradSq_comp_FIN046 {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (z : EuclideanSpace ℝ (Fin 2)) :
    PlanarPoincare.gradSq (fun p => f (invL_FIN046 p)) (eEq_FIN046 z) = ‖fderiv ℝ f z‖ ^ 2 := by
  have hd : HasFDerivAt (fun p => f (invL_FIN046 p)) ((fderiv ℝ f z).comp invL_FIN046)
      (eEq_FIN046 z) := by
    have h1 : HasFDerivAt f (fderiv ℝ f (invL_FIN046 (eEq_FIN046 z))) (invL_FIN046 (eEq_FIN046 z)) :=
      ((hf.differentiable (by simp)) _).hasFDerivAt
    have := h1.comp (eEq_FIN046 z) (invL_FIN046.hasFDerivAt (x := eEq_FIN046 z))
    rw [invL_eEq_FIN046] at this
    exact this
  unfold PlanarPoincare.gradSq
  rw [hd.fderiv, norm_sq_clm_FIN046]
  have e0 : invL_FIN046 ((1 : ℝ), (0 : ℝ)) = EuclideanSpace.single 0 1 := by
    simp [invL_FIN046]
  have e1 : invL_FIN046 ((0 : ℝ), (1 : ℝ)) = EuclideanSpace.single 1 1 := by
    simp [invL_FIN046]
  simp only [ContinuousLinearMap.comp_apply, e0, e1]

theorem planar_map_eEq_FIN046 (κ N : ℝ) :
    (volume.withDensity (fun z : EuclideanSpace ℝ (Fin 2) =>
      ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ ‖z‖))))).map eEq_FIN046 =
      orderedPlanarMeasure_FIN046 κ N := by
  set H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ (√(p.1 ^ 2 + p.2 ^ 2))))) with hH
  have hG : ∀ z : EuclideanSpace ℝ (Fin 2),
      ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ ‖z‖))) = H (eEq_FIN046 z) := by
    intro z
    simp only [hH, eEq_apply_FIN046, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
      sq_abs]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply eEq_FIN046.measurable hs,
    withDensity_apply _ (eEq_FIN046.measurable hs), orderedPlanarMeasure_FIN046,
    withDensity_apply _ hs]
  simp_rw [hG]
  exact (eEq_volume_FIN046.setLIntegral_comp_preimage_emb eEq_FIN046.measurableEmbedding H s)

theorem isProbabilityMeasure_rotational_FIN046 {σ : Measure ℝ} (hσ : IsProbabilityMeasure σ) :
    IsProbabilityMeasure (rotationalMeasure σ) := by
  unfold rotationalMeasure
  have := hσ
  exact (Measure.isProbabilityMeasure_map_iff PlanarPoincare.continuous_polar.aemeasurable).2
    inferInstance

theorem orderedAux_map_eEq_FIN046 {κ r0 N : ℝ}
    (hZ : 0 < orderedRadialZ_FIN035 κ r0 N)
    (hi : Integrable (orderedRadialWeight_FIN035 κ r0 N)) :
    (orderedAuxiliaryLaw_FIN046 κ N).map eEq_FIN046 =
      rotationalMeasure (orderedRadialLaw_FIN035 κ r0 N) := by
  have hσ := orderedRadialLaw_probability_FIN035 hi hZ
  have hrot := isProbabilityMeasure_rotational_FIN046 hσ
  have hrs := rotational_eq_smul_FIN046 hZ
  set C : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ * ENNReal.ofReal (Real.exp (N * radialPsi_orad κ r0) /
        orderedRadialZ_FIN035 κ r0 N) with hC
  set P := orderedPlanarMeasure_FIN046 κ N with hP
  set G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ ‖z‖))) with hG
  have hPm : (volume.withDensity G).map eEq_FIN046 = P := planar_map_eEq_FIN046 κ N
  have hPuniv : P Set.univ ≠ ⊤ := by
    intro htop
    have h1 := hrot.measure_univ
    rw [hrs, Measure.smul_apply, htop, smul_eq_mul] at h1
    by_cases hC0 : C = 0
    · rw [hC0] at h1; simp at h1
    · rw [ENNReal.mul_top hC0] at h1; exact ENNReal.top_ne_one h1
  have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 2) => radialPsi_orad κ ‖z‖) :=
    (continuous_radialPsi_orad_FIN046 κ).comp continuous_norm
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin 2) =>
      Real.exp (-(N * radialPsi_orad κ ‖z‖))) := by
    have hm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 2) =>
        Real.exp (-(N * radialPsi_orad κ ‖z‖))) volume :=
      (Real.continuous_exp.comp (continuous_const.mul hcont).neg).aestronglyMeasurable
    rw [← lintegral_ofReal_ne_top_iff_integrable hm (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    have : ∫⁻ z : EuclideanSpace ℝ (Fin 2),
        ENNReal.ofReal (Real.exp (-(N * radialPsi_orad κ ‖z‖))) =
        (volume.withDensity G) Set.univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [this]
    have h2 := congrArg (fun m => m Set.univ) hPm
    simp only [Measure.map_apply eEq_FIN046.measurable MeasurableSet.univ, Set.preimage_univ]
      at h2
    rw [h2]; exact hPuniv
  have hgib : IsProbabilityMeasure (orderedAuxiliaryLaw_FIN046 κ N) :=
    StrongConvexityLSI.gibbs_isProbabilityMeasure (V := fun z => N * radialPsi_orad κ ‖z‖) hint
  have e2 : orderedAuxiliaryLaw_FIN046 κ N = ENNReal.ofReal
      ((∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-(N * radialPsi_orad κ ‖y‖)))⁻¹) •
        volume.withDensity G := by
    unfold orderedAuxiliaryLaw_FIN046 StrongConvexityLSI.gibbs
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext x
    have hZ' : 0 ≤ ∫ y : EuclideanSpace ℝ (Fin 2), Real.exp (-(N * radialPsi_orad κ ‖y‖)) :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    simp only [hG, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul]
  have hmap : (orderedAuxiliaryLaw_FIN046 κ N).map eEq_FIN046 =
      ENNReal.ofReal ((∫ y : EuclideanSpace ℝ (Fin 2),
        Real.exp (-(N * radialPsi_orad κ ‖y‖)))⁻¹) • P := by
    rw [e2, Measure.map_smul, hPm]
    exact eEq_FIN046.measurable.aemeasurable
  have hmapP : IsProbabilityMeasure ((orderedAuxiliaryLaw_FIN046 κ N).map eEq_FIN046) :=
    (Measure.isProbabilityMeasure_map_iff eEq_FIN046.measurable.aemeasurable).2 hgib
  rw [hmap] at hmapP ⊢
  rw [hrs] at hrot ⊢
  exact eq_of_prob_smul hmapP hrot

theorem hasLSIRate_of_planar_FIN046 {η : Measure (EuclideanSpace ℝ (Fin 2))}
    (hη : IsProbabilityMeasure η) {ρ : Measure (ℝ × ℝ)} (hρ : η.map eEq_FIN046 = ρ)
    {A : ℝ} (hA : 0 < A)
    (h : ∀ F : ℝ × ℝ → ℝ, ContDiff ℝ ∞ F → ∀ B D : ℝ, (∀ x, |F x| ≤ B) →
      (∀ x, PlanarPoincare.gradSq F x ≤ D) →
      homogeneousEntropy ρ (fun x => F x ^ 2) ≤
        ENNReal.ofReal (A * ∫ x, PlanarPoincare.gradSq F x ∂ρ)) :
    StrongConvexityLSI.HasLSIRate η (2 / A) := by
  intro f hf
  obtain ⟨hfs, hfc⟩ := hf
  set F : ℝ × ℝ → ℝ := fun p => f (invL_FIN046 p) with hF
  have hFs : ContDiff ℝ ∞ F := hfs.comp invL_FIN046.contDiff
  obtain ⟨B, hB⟩ := hfs.continuous.bounded_above_of_compact_support hfc
  have hdc : Continuous (fun z => fderiv ℝ f z) := hfs.continuous_fderiv (by simp)
  obtain ⟨D0, hD0⟩ := hdc.bounded_above_of_compact_support (hfc.fderiv (𝕜 := ℝ))
  have hFB : ∀ p, |F p| ≤ B := fun p => by
    have := hB (invL_FIN046 p); simpa using this
  have hgs : ∀ p, PlanarPoincare.gradSq F p = ‖fderiv ℝ f (invL_FIN046 p)‖ ^ 2 := fun p => by
    have := gradSq_comp_FIN046 hfs (invL_FIN046 p)
    rw [eEq_invL_FIN046] at this
    exact this
  have hgD : ∀ p, PlanarPoincare.gradSq F p ≤ D0 ^ 2 := fun p => by
    rw [hgs]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD0 _) 2
  have key := h F hFs B (D0 ^ 2) hFB hgD
  have hent : homogeneousEntropy ρ (fun x => F x ^ 2) =
      homogeneousEntropy η (fun z => f z ^ 2) := by
    rw [← hρ, homogeneousEntropy_map_measurableEquiv]
    simp only [hF, invL_eEq_FIN046]
  have hint : ∫ x, PlanarPoincare.gradSq F x ∂ρ = ∫ z, ‖fderiv ℝ f z‖ ^ 2 ∂η := by
    rw [← hρ, eEq_FIN046.measurableEmbedding.integral_map]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact gradSq_comp_FIN046 hfs z
  have hI : Integrable (fun z => ‖fderiv ℝ f z‖ ^ 2) η := by
    refine Integrable.of_bound (C := D0 ^ 2) ?_ ?_
    · exact (hdc.norm.pow 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hD0 _) 2
  rw [hent, hint] at key
  refine key.trans ?_
  have h2A : 2 / (2 / A) = A := by field_simp
  rw [h2A, ENNReal.ofReal_mul hA.le,
    ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall fun z => by positivity)]
  refine le_of_eq ?_
  congr 1
  refine lintegral_congr fun z => ?_
  simp only [StrongConvexityLSI.gradSq]
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end PolarC_FIN046

section Final_FIN046
open Set Real
open DGPS.FiniteN.Tools.PlanarPoincare (rotationalMeasure angleLaw polar continuous_polar)
open DGPS.FiniteN.RotationalTools

theorem ordered_radial_data_FIN046 {κ : ℝ} (hκ : 2 < κ) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 = κ * besselRatio r0 ∧ ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ N : ℕ+, IsProbabilityMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        Integrable (fun r => (r - r0) ^ 2) (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        ∫ r, (r - r0) ^ 2 ∂(orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ≤ K / (N : ℝ) ∧
        (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)).map eEq_FIN046 =
          rotationalMeasure (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) ∧
        StrongConvexityLSI.HasLSIRate (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) (2 / A) := by
  obtain ⟨r0, hr0, hroot, huniq, c, C, hc, hcC, -, -, hUU⟩ := ordered_radial_well_geometry hκ
  obtain ⟨r1, hr1, hroot1, A, hA, hF⟩ := ordered_planar_lsi_FIN040 hκ
  have e : r1 = r0 := huniq r1 hr1 hroot1
  rw [e] at hF
  set E := ∫ u, orderedEnvelope_FIN035 r0 c u with hE
  have hE0 : 0 ≤ E := integral_nonneg fun u => by unfold orderedEnvelope_FIN035; positivity
  have hC0 : 0 ≤ C := hc.le.trans hcC
  have hKpos : 0 < E * Real.exp C / r0 + 1 := by positivity
  refine ⟨r0, hr0, hroot, A, E * Real.exp C / r0 + 1, hA, hKpos, fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN0 : (0 : ℝ) < N := by linarith
  set s := Real.sqrt (N : ℝ) with hs
  have hs1 : 1 ≤ s := by rw [hs, Real.one_le_sqrt]; exact hN1
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = (N : ℝ) := Real.sq_sqrt hN0.le
  have hU1 : ∀ r, 0 ≤ r → c * (r - r0) ^ 2 ≤ radialU_orad κ r0 r := fun r hr => (hUU r hr).1
  have hU2 : ∀ r, 0 ≤ r → radialU_orad κ r0 r ≤ C * (r - r0) ^ 2 := fun r hr => (hUU r hr).2
  have hi := orderedRadialWeight_integrable_FIN035 hr0 hc hs1 hU1
  have hZl := orderedRadialZ_lower_FIN035 hr0 hc hC0 hs1 hU1 hU2
  have hcm := orderedCentralMoment_upper_FIN035 hr0 hc hs1 hU1
  have hint := orderedCentralMoment_integrable_FIN035 hr0 hc hs1 hU1
  rw [hs2] at hi hZl hcm hint
  have hZ : 0 < orderedRadialZ_FIN035 κ r0 (N : ℝ) := lt_of_lt_of_le (by positivity) hZl
  have hprob := orderedRadialLaw_probability_FIN035 hi hZ
  have hI2 : Integrable (fun r => (r - r0) ^ 2) (orderedRadialLaw_FIN035 κ r0 (N : ℝ)) :=
    orderedRadialLaw_integrable_FIN035 hZ _ hint
  have hmap := orderedAux_map_eEq_FIN046 hZ hi
  refine ⟨hprob, hI2, ?_, hmap, ?_⟩
  · rw [orderedRadialLaw_integral_FIN035 hZ, div_le_div_iff₀ hZ hN0]
    set J := ∫ r, (r - r0) ^ 2 * orderedRadialWeight_FIN035 κ r0 (N : ℝ) r with hJ
    have h1 : J ≤ E / s ^ 3 := (le_div_iff₀ (by positivity)).2 (by linarith [hcm])
    have h2 : J * N ≤ E / s := by
      calc J * N = J * s ^ 2 := by rw [hs2]
        _ ≤ E / s ^ 3 * s ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = E / s := by field_simp
    have h3 : (E * Real.exp C / r0 + 1) * (r0 * Real.exp (-C) / s) = (E + r0 * Real.exp (-C)) / s := by
      rw [Real.exp_neg]; field_simp
    have h4 : E / s ≤ (E * Real.exp C / r0 + 1) * (r0 * Real.exp (-C) / s) := by
      rw [h3]; exact div_le_div_of_nonneg_right (by have := Real.exp_pos (-C); nlinarith [mul_pos hr0 this]) hs0.le
    calc J * N ≤ _ := h2
      _ ≤ _ := h4
      _ ≤ _ := mul_le_mul_of_nonneg_left hZl hKpos.le
  · have hrot := isProbabilityMeasure_rotational_FIN046 hprob
    have hη : IsProbabilityMeasure (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
      refine (Measure.isProbabilityMeasure_map_iff eEq_FIN046.measurable.aemeasurable).1 ?_
      rw [hmap]; exact hrot
    exact hasLSIRate_of_planar_FIN046 hη hmap hA (hF N)

theorem ordered_lower_FIN046 {κ : ℝ} (hκ : 2 < κ) {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+, ENNReal.ofReal (c * DGPS.Circle.AngularNormalization.a0 / (N : ℝ)) ≤ particleRateAll A N := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨r0, hr0, hroot, A', K, hA', hK, hdata⟩ := ordered_radial_data_FIN046 hκ
  obtain ⟨γ, hγ, h1, -⟩ := uniform_one_site_von_mises_lsi
  set lam : ℝ := 2 / A' with hlam
  have hlam0 : 0 < lam := by positivity
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  refine ⟨γ / (1 + 1 / lam), by positivity, fun N => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN0 : (0 : ℝ) < N := by linarith
  have haux : StrongConvexityLSI.HasLSIRate
      ((Hubbard.auxLaw (orderedD_FIN046 κ) (fun _ : Fin 2 => (0 : ℝ)) (fun _ : AngCircle => (0 : ℝ))
        phi angHaar N).map (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))) lam := by
    rw [auxLaw_map_ordered_FIN046 hκ0 N]
    exact (hdata N).2.2.2.2
  have hmain := criticalRate_of_classical A N (orderedD_posDef_FIN046 hκ0)
    (fun _ : Fin 2 => (0 : ℝ)) (particleLaw_ordered_FIN046 hκ0 hA N) hγ hlam0
    (criticalClassicalProductLSI hγ h1 N) haux
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have hd : 1 + (N : ℝ) / lam ≤ (1 + 1 / lam) * N := by
    have : 1 / lam * 1 ≤ 1 / lam * N := mul_le_mul_of_nonneg_left hN1 (by positivity)
    have h2 : (N : ℝ) / lam = 1 / lam * N := by ring
    nlinarith
  calc γ / (1 + 1 / lam) * DGPS.Circle.AngularNormalization.a0 / (N : ℝ) = DGPS.Circle.AngularNormalization.a0 * γ / ((1 + 1 / lam) * N) := by
        field_simp
    _ ≤ DGPS.Circle.AngularNormalization.a0 * γ / (1 + (N : ℝ) / lam) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hd

theorem orderedAuxiliaryLaw_map_qturnL_FIN046 (κ M : ℝ) :
    (orderedAuxiliaryLaw_FIN046 κ M).map qturnL = orderedAuxiliaryLaw_FIN046 κ M := by
  unfold orderedAuxiliaryLaw_FIN046 DGPS.FiniteN.Tools.StrongConvexityLSI.gibbs
  refine map_qturnL_withDensity _ fun x => ?_
  simp only [norm_qturnL]

theorem isProbabilityMeasure_orderedAuxiliaryLaw_FIN046 {κ : ℝ} (hκ : 0 < κ) (N : ℕ+) :
    IsProbabilityMeasure (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
  rw [← auxLaw_map_ordered_FIN046 hκ N]
  exact (Measure.isProbabilityMeasure_map_iff
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable).2
    (DGPS.FiniteN.Tools.AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_angular
      (orderedD_posDef_FIN046 hκ) (fun _ : Fin 2 => (0 : ℝ)) N)

theorem isAngularMixture_ordered_FIN046 {κ : ℝ} (hκ : 0 < κ) {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) (N : ℕ+) :
    IsAngularMixture A N (orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
  intro G hG
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hG.continuousOn
  rw [particleLaw_ordered_FIN046 hκ hA N]
  have key := DGPS.FiniteN.Tools.AuxiliaryTransfer.integral_particle_eq hubbardHyp_angular
    (orderedD_posDef_FIN046 hκ)
    (fun _ : Fin 2 => (0 : ℝ)) N hG.measurable (B := C) (fun x => by simpa using hC x (Set.mem_univ x))
  rw [key, ← auxLaw_map_ordered_FIN046 hκ N]
  rw [(MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [MeasurableEquiv.toLp_apply]
  rw [pi_vmLaw_eq_condLaw]


theorem integral_besselRatio_sq_FIN046 {σ : Measure ℝ} [IsProbabilityMeasure σ]
    {η : Measure (EuclideanSpace ℝ (Fin 2))} (hmap : η.map eEq_FIN046 = rotationalMeasure σ) :
    ∫ z, besselRatio ‖z‖ ^ 2 ∂η = ∫ r, besselRatio |r| ^ 2 ∂σ := by
  set F : ℝ × ℝ → ℝ := fun p => besselRatio (Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ^ 2 with hF
  have hFc : Continuous F := by
    have := DGPS.Circle.BesselConcavity.continuous_besselRatio
    simp only [hF]; fun_prop
  have h1 : ∀ z : EuclideanSpace ℝ (Fin 2), besselRatio ‖z‖ ^ 2 = F (eEq_FIN046 z) := by
    intro z
    simp only [hF, eEq_apply_FIN046, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  calc ∫ z, besselRatio ‖z‖ ^ 2 ∂η = ∫ z, F (eEq_FIN046 z) ∂η := integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ p, F p ∂(η.map eEq_FIN046) := (eEq_FIN046.measurableEmbedding.integral_map F).symm
    _ = ∫ p, F p ∂(rotationalMeasure σ) := by rw [hmap]
    _ = ∫ q, F (polar q) ∂(angleLaw.prod σ) := by
        unfold rotationalMeasure
        exact integral_map continuous_polar.aemeasurable hFc.aestronglyMeasurable
    _ = ∫ q, besselRatio |q.2| ^ 2 ∂(angleLaw.prod σ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        simp only [hF, polar]
        congr 3
        rw [show (q.2 * Real.cos q.1) ^ 2 + (q.2 * Real.sin q.1) ^ 2 = q.2 ^ 2 by
          nlinarith [Real.sin_sq_add_cos_sq q.1]]
        exact Real.sqrt_sq_eq_abs _
    _ = ∫ r, besselRatio |r| ^ 2 ∂σ := by
        rw [integral_fun_snd (μ := angleLaw) (ν := σ) (fun r => besselRatio |r| ^ 2)]
        simp


theorem besselRatio_sq_lower_FIN046 {r0 : ℝ} (hr0 : 0 < r0) (r : ℝ) :
    besselRatio r0 ^ 2 - |r - r0| ≤ besselRatio |r| ^ 2 := by
  set s := |r| with hs
  have hs0 : 0 ≤ s := abs_nonneg r
  have hg0 : 0 ≤ besselRatio s := by
    rcases hs0.eq_or_lt with h | h
    · rw [← h, besselRatio_zero_orad]
    · exact (DGPS.Circle.BesselMonotonicity.besselRatio_pos s h).le
  have hg1 : besselRatio s < 1 := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one s
  have hr0p := DGPS.Circle.BesselMonotonicity.besselRatio_pos r0 hr0
  have hr01 := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one r0
  have hlip : |besselRatio s - besselRatio r0| ≤ 1 / 2 * |s - r0| := by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := besselRatio) (s := Ici 0)
      (C := 1 / 2) (fun z _ => (besselRatio_hasDerivAt_orad z).differentiableAt) ?_
      (convex_Ici 0) (mem_Ici.mpr hr0.le) (mem_Ici.mpr hs0)
    · simpa [Real.norm_eq_abs] using this
    · intro z hz
      have := besselRatio_deriv_mem_orad (mem_Ici.mp hz)
      rw [Real.norm_eq_abs, abs_of_pos this.1]
      exact this.2
  have hsr : |s - r0| ≤ |r - r0| := by
    have := abs_abs_sub_abs_le_abs_sub r r0
    rwa [abs_of_pos hr0] at this
  have hd := abs_le.1 hlip
  have : -|r - r0| ≤ besselRatio s ^ 2 - besselRatio r0 ^ 2 := by
    have h2 : besselRatio s ^ 2 - besselRatio r0 ^ 2 =
        (besselRatio s - besselRatio r0) * (besselRatio s + besselRatio r0) := by ring
    rw [h2]
    have hsum0 : 0 ≤ besselRatio s + besselRatio r0 := by linarith
    have hsum2 : besselRatio s + besselRatio r0 ≤ 2 := by linarith
    have habs := abs_nonneg (s - r0)
    rcases le_or_gt 0 (besselRatio s - besselRatio r0) with h | h
    · nlinarith [abs_nonneg (r - r0)]
    · have h3 : besselRatio s - besselRatio r0 ≥ -(1 / 2 * |s - r0|) := by linarith [hd.1]
      nlinarith [abs_nonneg (r - r0)]
  linarith


theorem ordered_concentration_FIN046 {κ : ℝ} (hκ : 2 < κ) :
    ∃ m : ℝ, 0 < m ∧ ∃ N0 : ℝ, ∀ N : ℕ+, N0 ≤ (N : ℝ) →
      m ≤ ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
  obtain ⟨r0, hr0, hroot, A, K, hA, hK, hdata⟩ := ordered_radial_data_FIN046 hκ
  have hg0 := DGPS.Circle.BesselMonotonicity.besselRatio_pos r0 hr0
  set m0 : ℝ := besselRatio r0 ^ 2 with hm0
  have hm0p : 0 < m0 := by positivity
  refine ⟨m0 / 2, by positivity, 4 * K / m0 ^ 2, fun N hN => ?_⟩
  obtain ⟨hprob, hI2, hmom, hmap, -⟩ := hdata N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [integral_besselRatio_sq_FIN046 hmap]
  set σ := orderedRadialLaw_FIN035 κ r0 (N : ℝ) with hσ
  set a : ℝ := m0 / 2 with ha
  have hap : 0 < a := by positivity
  have hgc : Continuous fun r : ℝ => besselRatio |r| ^ 2 :=
    (DGPS.Circle.BesselConcavity.continuous_besselRatio.comp continuous_abs).pow 2
  have hgi : Integrable (fun r : ℝ => besselRatio |r| ^ 2) σ := by
    refine Integrable.of_bound hgc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun r => ?_)
    have h0 : 0 ≤ besselRatio |r| := by
      rcases (abs_nonneg r).eq_or_lt with h | h
      · rw [← h, besselRatio_zero_orad]
      · exact (DGPS.Circle.BesselMonotonicity.besselRatio_pos _ h).le
    have h1 := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one |r|
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hlow : Integrable (fun r : ℝ => m0 - a / 2 - (1 / (2 * a)) * (r - r0) ^ 2) σ :=
    (integrable_const _).sub (hI2.const_mul _)
  have hmono : ∫ r, (m0 - a / 2 - (1 / (2 * a)) * (r - r0) ^ 2) ∂σ ≤ ∫ r, besselRatio |r| ^ 2 ∂σ := by
    refine integral_mono hlow hgi fun r => ?_
    have h1 := besselRatio_sq_lower_FIN046 hr0 r
    have h2 : |r - r0| ≤ a / 2 + (1 / (2 * a)) * (r - r0) ^ 2 := by
      have : 0 ≤ (|r - r0| - a) ^ 2 := sq_nonneg _
      have h3 : (r - r0) ^ 2 = |r - r0| ^ 2 := (sq_abs _).symm
      rw [h3]
      rw [show a / 2 + 1 / (2 * a) * |r - r0| ^ 2 = (a ^ 2 + |r - r0| ^ 2) / (2 * a) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hint : ∫ r, (m0 - a / 2 - (1 / (2 * a)) * (r - r0) ^ 2) ∂σ =
      m0 - a / 2 - (1 / (2 * a)) * ∫ r, (r - r0) ^ 2 ∂σ := by
    rw [integral_sub (integrable_const _) (hI2.const_mul _), integral_const_mul]
    simp
  have hbound : (1 / (2 * a)) * ∫ r, (r - r0) ^ 2 ∂σ ≤ m0 / 4 := by
    have hKN : K / (N : ℝ) ≤ m0 ^ 2 / 4 := by
      rw [div_le_iff₀ hN0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < m0 ^ 2)).1 (show 4 * K / m0 ^ 2 ≤ N from hN)
      nlinarith
    calc (1 / (2 * a)) * ∫ r, (r - r0) ^ 2 ∂σ ≤ (1 / (2 * a)) * (K / N) :=
          mul_le_mul_of_nonneg_left hmom (by positivity)
      _ ≤ (1 / (2 * a)) * (m0 ^ 2 / 4) := mul_le_mul_of_nonneg_left hKN (by positivity)
      _ = m0 / 4 := by rw [ha]; field_simp
  rw [hint] at hmono
  rw [ha] at hmono hbound ⊢
  linarith


/-- The symmetric magnetization Poincare quotient at the ordered XY model. -/
noncomputable def orderedMagnetizationQuotient_FIN046 (κ : ℝ) (N : ℕ+) : ℝ :=
  DGPS.Circle.AngularNormalization.a0 / (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)))

theorem ordered_aux_sum_pos_FIN046 (κ : ℝ) (N : ℕ+) :
    0 < 1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hI : 0 ≤ ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) :=
    integral_nonneg fun _ => sq_nonneg _
  have : 0 ≤ ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) :=
    mul_nonneg (by linarith) hI
  linarith

theorem ordered_rates_le_magnetization_quotient_FIN046 {κ : ℝ} (hκ : 0 < κ) {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) (N : ℕ+) :
    particleRateAll A N ≤ ENNReal.ofReal (orderedMagnetizationQuotient_FIN046 κ N) ∧
    particleRateSym A N ≤ ENNReal.ofReal (orderedMagnetizationQuotient_FIN046 κ N) ∧
    particlePoincareRate A N ≤ ENNReal.ofReal (orderedMagnetizationQuotient_FIN046 κ N) := by
  have := isProbabilityMeasure_orderedAuxiliaryLaw_FIN046 hκ N
  obtain ⟨f, hfeq, _, _, hsym, hmean, hvar, hE, hq⟩ :=
    rotational_symmetric_magnetization_variance A N (orderedAuxiliaryLaw_FIN046 κ (N : ℝ))
      (orderedAuxiliaryLaw_map_qturnL_FIN046 κ _) (isAngularMixture_ordered_FIN046 hκ hA N)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hS := ordered_aux_sum_pos_FIN046 κ N
  have hvpos : 0 < ProbabilityTheory.variance f.1 (particleLaw A N) := by
    rw [hvar]; positivity
  have hb : ∀ x, |f x| ≤ (N : ℝ) := by
    intro x
    have h1 : f x = ∑ i, (mode 1 (x i)).re := by
      have := congrFun hfeq x
      simpa using this
    rw [h1]
    calc |∑ i, (mode 1 (x i)).re| ≤ ∑ i, |(mode 1 (x i)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
          rw [mode_apply]; simp [fourier_apply]
      _ = N := by simp
  have hquot : particleEnergy A N f / ProbabilityTheory.variance f.1 (particleLaw A N) =
      orderedMagnetizationQuotient_FIN046 κ N := by
    rw [hE, hvar]
    unfold orderedMagnetizationQuotient_FIN046
    field_simp
  have hlin := bounded_test_lsi_linearization A N f (N : ℝ) hb hmean hvpos
  rw [hquot] at hlin
  refine ⟨hlin.2.2.1, hlin.2.2.2 hsym, ?_⟩
  refine (particlePoincareRate_le_quotient A N f hvpos).trans (le_of_eq ?_)
  rw [hq]; rfl


theorem ordered_quotient_upper_FIN046 {κ : ℝ} (hκ : 2 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
      orderedMagnetizationQuotient_FIN046 κ N ≤
        C * DGPS.Circle.AngularNormalization.a0 * (N : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨m, hm, Nr, hNr⟩ := ordered_concentration_FIN046 hκ
  refine ⟨2 / m, by positivity, max 2 ⌈Nr⌉₊, le_trans (by norm_num) (le_max_left _ _), fun N hN => ?_⟩
  have h2 : 2 ≤ (N : ℕ) := le_trans (le_max_left _ _) hN
  have hc : Nr ≤ (N : ℝ) :=
    (Nat.le_ceil Nr).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hI := hNr N hc
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast h2
  have hN0 : (0 : ℝ) < N := by linarith
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  unfold orderedMagnetizationQuotient_FIN046
  rw [Real.rpow_neg_one]
  have hden : (N : ℝ) * m / 2 ≤
      1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) := by
    have : ((N : ℝ) - 1) * m ≤ ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hI (by linarith)
    nlinarith
  calc DGPS.Circle.AngularNormalization.a0 / (1 + ((N : ℝ) - 1) * ∫ z, besselRatio ‖z‖ ^ 2 ∂(orderedAuxiliaryLaw_FIN046 κ (N : ℝ)))
      ≤ DGPS.Circle.AngularNormalization.a0 / ((N : ℝ) * m / 2) :=
        div_le_div_of_nonneg_left ha.le (by positivity) hden
    _ = 2 / m * DGPS.Circle.AngularNormalization.a0 * (N : ℝ)⁻¹ := by field_simp

/-- **FIN046.** For every fixed `κ > 2`, in the ordered XY model (`V = 0`,
`W = κ (1 - cos 2π (x - y))`) the unrestricted Poincare rate `λ_N` and both log-Sobolev rates
`r_N^all`, `r_N^sym` are `Θ_1`, i.e. `≍ N⁻¹`. -/
theorem ordered_particle_lower_and_upper_scales {κ : ℝ} (hκ : 2 < κ) {A : InteractionData 1}
    (hA : IsOrderedXY_FIN046 κ A) :
    ThetaScale 1 (fun n : ℕ => if h : 0 < n then (particlePoincareRate A ⟨n, h⟩).toReal
      else 0) ∧
    ThetaScale 1 (fun n : ℕ => if h : 0 < n then (particleRateAll A ⟨n, h⟩).toReal
      else 0) ∧
    ThetaScale 1 (fun n : ℕ => if h : 0 < n then (particleRateSym A ⟨n, h⟩).toReal
      else 0) := by
  have hκ0 : 0 < κ := by linarith
  obtain ⟨c, hc, hlow⟩ := ordered_lower_FIN046 hκ hA
  obtain ⟨C, hC, N₀, hN₀, hup⟩ := ordered_quotient_upper_FIN046 hκ
  have ha0 := DGPS.Circle.AngularNormalization.a0_pos
  set a0 := DGPS.Circle.AngularNormalization.a0 with ha0def
  have key : ∀ N : ℕ+, N₀ ≤ (N : ℕ) →
      (c * a0 * (N : ℝ) ^ (-(1 : ℝ)) ≤ (particleRateAll A N).toReal ∧
        (particleRateAll A N).toReal ≤ (particleRateSym A N).toReal ∧
        (particleRateAll A N).toReal ≤ (particlePoincareRate A N).toReal ∧
        (particlePoincareRate A N).toReal ≤ C * a0 * (N : ℝ) ^ (-(1 : ℝ)) ∧
        (particleRateAll A N).toReal ≤ C * a0 * (N : ℝ) ^ (-(1 : ℝ)) ∧
        (particleRateSym A N).toReal ≤ C * a0 * (N : ℝ) ^ (-(1 : ℝ))) := by
    intro N hN
    obtain ⟨-, -, ⟨-, hAt⟩, ⟨-, hSt⟩, ⟨-, hPt⟩, -, -, -, -, hAS, hAiff, -, -⟩ :=
      finite_positive_particle_rate_and_real_bridge A (by norm_num : 0 < 1) N
    obtain ⟨hAQ, hSQ, hPQ⟩ := ordered_rates_le_magnetization_quotient_FIN046 hκ0 hA N
    have hQ : 0 ≤ orderedMagnetizationQuotient_FIN046 κ N :=
      (div_pos ha0 (ordered_aux_sum_pos_FIN046 κ N)).le
    have hQN := hup N hN
    have hl : c * a0 * (N : ℝ) ^ (-(1 : ℝ)) ≤ (particleRateAll A N).toReal := by
      have := (hAiff _).1 (hlow N)
      rwa [Real.rpow_neg_one, ← div_eq_mul_inv]
    have hPge : (particleRateAll A N).toReal ≤ (particlePoincareRate A N).toReal := by
      have h1 : ENNReal.ofReal (particleRateAll A N).toReal ≤ particleRateAll A N := by
        rw [ENNReal.ofReal_toReal hAt.ne]
      have h2 := ofReal_le_particlePoincareRate_of_rateAll A N _ h1
      exact (ENNReal.ofReal_le_iff_le_toReal hPt.ne).1 h2
    exact ⟨hl, hAS, hPge, (ENNReal.toReal_le_of_le_ofReal hQ hPQ).trans hQN,
      (ENNReal.toReal_le_of_le_ofReal hQ hAQ).trans hQN,
      (ENNReal.toReal_le_of_le_ofReal hQ hSQ).trans hQN⟩
  refine ⟨⟨c * a0, C * a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩,
    ⟨c * a0, C * a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩,
    ⟨c * a0, C * a0, by positivity, by positivity, N₀, hN₀, fun n hn => ?_⟩⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨hl, -, hAP, hu, -, -⟩ := key ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hl hAP hu
    simp only [hn0, ↓reduceDIte]
    exact ⟨hl.trans hAP, hu⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨hl, -, -, -, hu, -⟩ := key ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hl hu
    simp only [hn0, ↓reduceDIte]
    exact ⟨hl, hu⟩
  · have hn0 : 0 < n := lt_of_lt_of_le hN₀ hn
    obtain ⟨hl, hAS, -, -, -, hu⟩ := key ⟨n, hn0⟩ hn
    simp only [PNat.mk_coe] at hl hAS hu
    simp only [hn0, ↓reduceDIte]
    exact ⟨hl.trans hAS, hu⟩

end Final_FIN046

end DGPS.FiniteN
