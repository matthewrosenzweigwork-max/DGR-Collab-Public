import DGPS.FiniteN.TiltedXYRateFIN049
import DGPS.FiniteN.CriticalXYLower
import DGPS.FiniteN.TiltedXY
import DGPS.FiniteN.Tools.AuxiliaryTransferTorus
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.FiniteN.Tools.BoundedComparison
import DGPS.FiniteN.Tools.AuxiliaryTransfer
import DGPS.FiniteN.Tools.LSIExtension
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff Matrix

namespace DGPS.FiniteN.TiltedXY.Fin050

open DGPS DGPS.FiniteN DGPS.FiniteN.Tools DGPS.Circle.AngularNormalization
  DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.ConditionalEntropyPinsker
  DGPS.FiniteN.Tools.UniformVonMises DGPS.Circle.BesselMoments
  DGPS.FiniteN.TiltedXY.Fin051

/-- The feature map `x ↦ (cos 2πx, sin 2πx)` on `𝕋^1`. -/
noncomputable def phiT (x : Torus 1) : Fin 2 → ℝ := phi (angEquiv x)

theorem phase_eq_toCircle_FIN050 (x : Torus 1) :
    phase x = ((AddCircle.toCircle (angEquiv x) : Circle) : ℂ) := by
  rw [angEquiv_apply, phase]
  induction (x 0) using QuotientAddGroup.induction_on with
  | H s =>
    rw [fourier_coe_apply, angRescale_mk, AddCircle.toCircle_apply_mk, Circle.coe_exp]
    congr 1
    push_cast; field_simp

theorem phiT_zero_FIN050 (x : Torus 1) : phiT x 0 = (phase x).re := by
  rw [phase_eq_toCircle_FIN050]; rfl

theorem phiT_one_FIN050 (x : Torus 1) : phiT x 1 = (phase x).im := by
  rw [phase_eq_toCircle_FIN050]; rfl


theorem phiT_eq_FIN050 (x : Torus 1) : phiT x = ![(phase x).re, (phase x).im] := by
  funext i; fin_cases i
  · exact phiT_zero_FIN050 x
  · exact phiT_one_FIN050 x

theorem measurable_phiT_FIN050 : Measurable phiT :=
  measurable_phi.comp angEquiv.measurable

theorem hubbardHyp_FIN050 : HubbardHyp (haar 1) (fun _ : Torus 1 => (0 : ℝ)) phiT where
  m_ne_zero := (IsProbabilityMeasure.ne_zero (haar 1))
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := measurable_phiT_FIN050
  φ_bound := ⟨1, fun _ => norm_phi_le _⟩

/-- The coupling matrix `D = 4 I`. -/
noncomputable def tiltD : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal fun _ => (4 : ℝ)

/-- The field `h = (1/2, 0)`. -/
noncomputable def tiltH : Fin 2 → ℝ := ![1 / 2, 0]

theorem tiltD_posDef : tiltD.PosDef := by
  unfold tiltD
  simp [Matrix.posDef_diagonal_iff]

theorem tiltD_inv : tiltD⁻¹ = Matrix.diagonal fun _ => (1 / 4 : ℝ) := by
  unfold tiltD
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext i; norm_num

theorem quadForm_tiltD_inv (v : Fin 2 → ℝ) :
    quadForm tiltD⁻¹ v = (v 0 ^ 2 + v 1 ^ 2) / 4 := by
  rw [tiltD_inv]
  simp [quadForm, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

theorem dot_tiltD (v : Fin 2 → ℝ) : v ⬝ᵥ tiltD *ᵥ v = 4 * (v 0 ^ 2 + v 1 ^ 2) := by
  simp [tiltD, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two]
  ring

theorem auxPartition_FIN050 (w : Fin 2 → ℝ) :
    auxPartition (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w =
      besselI 0 ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖ := by
  rw [← vmNorm_eq_bessel]
  unfold auxPartition expTerm vmNorm
  have : ∀ x : Torus 1, Real.exp (w ⬝ᵥ phiT x - 0) =
      (fun θ => Real.exp (vmPhase (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) θ)) (angEquiv x) := by
    intro x
    simp only [sub_zero]
    rw [show w ⬝ᵥ phiT x = vmPhase (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) (angEquiv x) from
      dot_phi (WithLp.toLp 2 w) (angEquiv x)]
  simp_rw [this]
  exact integral_comp_angEquiv (fun θ => Real.exp (vmPhase (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) θ))


open DGPS.FiniteN.TiltedXY.Fin048 in
theorem auxPotential_FIN050 (w : Fin 2 → ℝ) :
    auxPotential (fun _ : Torus 1 => (0 : ℝ)) phiT tiltD tiltH (haar 1) w =
      tiltPsi 4 (1 / 2) (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) := by
  unfold auxPotential tiltPsi
  rw [auxPartition_FIN050, quadForm_tiltD_inv, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have : ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) - (1 / 2 : ℝ) • e1‖ ^ 2 =
      (w 0 - 1 / 2) ^ 2 + (w 1) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two,
      Real.sq_sqrt (by positivity)]
    simp [e1_apply_zero, e1_apply_one, sq_abs]
  rw [this]
  simp only [Pi.sub_apply, tiltH]
  simp
  ring


open DGPS.FiniteN.TiltedXY.Fin048 in
theorem auxLaw_map_FIN050 (N : ℕ+) :
    (auxLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = imsEta (N : ℝ) (tiltPsi 4 (1 / 2)) := by
  set G : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (Real.exp (-((N : ℝ) * tiltPsi 4 (1 / 2) z))) with hG
  set ν : Measure (EuclideanSpace ℝ (Fin 2)) := volume.withDensity G with hν
  have hF : (fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential (fun _ : Torus 1 => (0 : ℝ)) phiT tiltD tiltH (haar 1) w))) =
        fun w => G (WithLp.toLp 2 w) := by
    funext w
    simp only [hG, auxPotential_FIN050, neg_mul]
  have hmap : ((volume : Measure (Fin 2 → ℝ)).withDensity (fun w : Fin 2 → ℝ =>
      ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential (fun _ : Torus 1 => (0 : ℝ)) phiT tiltD tiltH (haar 1) w)))).map
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) = ν := by
    refine Measure.ext fun s hs => ?_
    rw [hF]
    exact map_withDensity_toLp G s hs
  have hmass : ν Set.univ = auxMass tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N := by
    rw [← hmap, Measure.map_apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable MeasurableSet.univ,
      Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  unfold auxLaw
  rw [Measure.map_smul, hmap]
  unfold imsEta
  rw [← hmass, hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable


theorem fieldSum_FIN050 (N : ℕ+) (x : ParticleSpace 1 N) :
    fieldSum phiT x = ![(∑ i, phase (x i)).re, (∑ i, phase (x i)).im] := by
  funext j
  fin_cases j
  · simp [fieldSum, phiT_zero_FIN050, Complex.re_sum]
  · simp [fieldSum, phiT_one_FIN050, Complex.im_sum]

theorem particleWeight_FIN050 (N : ℕ+) (x : ParticleSpace 1 N) :
    particleWeight (fun _ : Torus 1 => (0 : ℝ)) phiT tiltD tiltH N x =
      Real.exp (2 * (N : ℝ)) * Real.exp (-particleHamiltonian (tiltedXYData (1 / 2) 4) N x) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  rw [← Real.exp_add]
  unfold particleWeight
  congr 1
  rw [DGPS.FiniteN.TiltedXY.Fin051.hamiltonian_eq, fieldSum_FIN050, dot_tiltD, Complex.normSq_apply]
  simp only [tiltH, dotProduct, Fin.sum_univ_two]
  simp
  field_simp
  ring

theorem hubbardParticleLaw_FIN050 (N : ℕ+) :
    hubbardParticleLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N =
      DGPS.particleLaw (tiltedXYData (1 / 2) 4) N := by
  have hP := DGPS.Particle.particleLaw_isProbabilityMeasure' (tiltedXYData (1 / 2) 4) N
  have hH := AuxiliaryTransfer.isProbabilityMeasure_particleLaw hubbardHyp_FIN050
    tiltD_posDef tiltH N
  set ν : Measure (ParticleSpace 1 N) := (particleHaar 1 N).withDensity fun x =>
    ENNReal.ofReal (Real.exp (-particleHamiltonian (tiltedXYData (1 / 2) 4) N x)) with hν
  have e1 : DGPS.particleLaw (tiltedXYData (1 / 2) 4) N =
      ENNReal.ofReal (particlePartition (tiltedXYData (1 / 2) 4) N)⁻¹ • ν :=
    DGPS.Particle.particleLaw_eq_smul (tiltedXYData (1 / 2) 4) N
  have e2 : hubbardParticleLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N =
      ((particleMass tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N)⁻¹ *
        ENNReal.ofReal (Real.exp (2 * (N : ℝ)))) • ν := by
    unfold hubbardParticleLaw
    simp_rw [particleWeight_FIN050, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [hν, mul_smul]
    congr 1
    exact withDensity_smul' (ENNReal.ofReal (Real.exp (2 * (N : ℝ)))) _ ENNReal.ofReal_ne_top
  rw [e1] at hP ⊢
  rw [e2] at hH ⊢
  exact eq_of_prob_smul hH hP

open DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.AuxiliaryTransferTorus
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.AuxiliaryTransfer

/-- one-site carre du champ on `𝕋^1`. -/
noncomputable def gam1_FIN050 (f : Torus 1 → ℝ) (x : Torus 1) : ℝ≥0∞ :=
  ENNReal.ofReal (coordPartial 0 f x ^ 2)

theorem base_poincare_FIN050 :
    PoincareAt (haar 1) IsSmoothPeriodic gam1_FIN050 (1 / (4 * Real.pi ^ 2)) := by
  intro f hf
  have hw := hf.isWeakGradient
  have h1 := DGPS.FiniteN.PositiveRate.torus_poincare hw
  have hm : MemLp f 2 (haar 1) := hw.memLp
  rw [← hm.ofReal_variance_eq]
  have hint : ∫ y, ‖smoothGrad f y‖ ^ 2 ∂haar 1 = ∫ y, coordPartial 0 f y ^ 2 ∂haar 1 := by
    congr 1; funext y
    rw [EuclideanSpace.norm_sq_eq]; simp [smoothGrad]
  rw [hint] at h1
  have hint2 : Integrable (fun y => coordPartial 0 f y ^ 2) (haar 1) :=
    ((hf.continuous_coordPartial 0).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold gam1_FIN050
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpi := Real.pi_pos
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  linarith

theorem abs_dot_phiT_le_FIN050 (w : Fin 2 → ℝ) (x : Torus 1) :
    |w ⬝ᵥ phiT x| ≤ |w 0| + |w 1| := by
  have hb : ∀ i, |phiT x i| ≤ 1 := fun i => by
    have h := norm_le_pi_norm (phi (angEquiv x)) i
    rw [Real.norm_eq_abs] at h
    exact le_trans h (norm_phi_le _)
  rw [dotProduct, Fin.sum_univ_two]
  calc |w 0 * phiT x 0 + w 1 * phiT x 1| ≤ |w 0 * phiT x 0| + |w 1 * phiT x 1| := abs_add_le _ _
    _ ≤ |w 0| + |w 1| := by
      rw [abs_mul, abs_mul]
      have := hb 0; have := hb 1
      nlinarith [abs_nonneg (w 0), abs_nonneg (w 1), abs_nonneg (phiT x 0), abs_nonneg (phiT x 1)]

/-- one-site Poincare inequality for the site law, with constant `C(w) = e^{2(|w₀|+|w₁|)}/(4π²)`. -/
theorem site_poincare_FIN050 (w : Fin 2 → ℝ) :
    PoincareAt (siteLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w) IsSmoothPeriodic gam1_FIN050
      (Real.exp (2 * (|w 0| + |w 1|)) * (1 / (4 * Real.pi ^ 2))) := by
  have := isProbabilityMeasure_siteLaw hubbardHyp_FIN050 (m := haar 1) w
  have hz := auxPartition_pos hubbardHyp_FIN050 (m := haar 1) (U := fun _ : Torus 1 => (0 : ℝ))
    (φ := phiT) w
  refine poincare_comparison (Q := haar 1) (P := siteLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w)
    (ρ := siteDensity (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w) rfl
    (fun x => div_nonneg (expTerm_pos w x).le hz.le) (fun x y => ?_)
    (fun f hf => hf.isWeakGradient.memLp) base_poincare_FIN050
  unfold siteDensity expTerm
  rw [div_le_iff₀ hz, mul_div_assoc', div_mul_cancel₀ _ hz.ne', ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_dot_phiT_le_FIN050 w x
  have h2 := abs_dot_phiT_le_FIN050 w y
  have := (abs_le.1 h1).2
  have := (abs_le.1 h2).1
  linarith


/-! ### Slices of smooth periodic particle functions -/

theorem particleLift_sec_FIN050 {N : ℕ+} (x : ParticleSpace 1 N) :
    particleLift (fun k => SharpLSI.secT (x k)) = x := by
  funext k; simp [particleLift, torusLift, SharpLSI.liftT_secT]

theorem particleLift_update_FIN050 {N : ℕ+} (x : ParticleSpace 1 N) (i : Fin N) (t : Fin 1 → ℝ) :
    particleLift (Function.update (fun k => SharpLSI.secT (x k)) i t) =
      Function.update x i (torusLift t) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [particleLift]
  · simp [particleLift, Function.update_of_ne hk, torusLift, SharpLSI.liftT_secT]

theorem slice_comp_lift_FIN050 {N : ℕ+} (f : ParticleSpace 1 N → ℝ) (x : ParticleSpace 1 N)
    (i : Fin N) :
    (slice i f x) ∘ torusLift =
      (f ∘ particleLift) ∘ Function.update (fun k => SharpLSI.secT (x k)) i := by
  funext t
  simp [slice, Function.comp, particleLift_update_FIN050]

theorem isSmoothPeriodic_slice_FIN050 {N : ℕ+} {f : ParticleSpace 1 N → ℝ}
    (hf : IsSmoothPeriodicParticle f) (x : ParticleSpace 1 N) (i : Fin N) :
    IsSmoothPeriodic (slice i f x) := by
  unfold IsSmoothPeriodic
  rw [slice_comp_lift_FIN050]
  exact hf.comp (contDiff_update _ _ _)

theorem coordPartial_slice_FIN050 {N : ℕ+} {f : ParticleSpace 1 N → ℝ}
    (hf : IsSmoothPeriodicParticle f) (x : ParticleSpace 1 N) (i : Fin N) :
    coordPartial 0 (slice i f x) (x i) = particlePartial i 0 f x := by
  unfold coordPartial particlePartial
  rw [slice_comp_lift_FIN050]
  have hu := hasFDerivAt_update (𝕜 := ℝ) (fun k => SharpLSI.secT (x k)) (i := i) (SharpLSI.secT (x i))
  have hd : DifferentiableAt ℝ (f ∘ particleLift)
      (Function.update (fun k => SharpLSI.secT (x k)) i (SharpLSI.secT (x i))) :=
    (hf.differentiable (by simp)) _
  have := hd.hasFDerivAt.comp (SharpLSI.secT (x i)) hu
  rw [this.fderiv, Function.update_eq_self]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  congr 1
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [hk]


/-- conditional Poincare inverse constant. -/
noncomputable def Cc_FIN050 (w : Fin 2 → ℝ) : ℝ :=
  Real.exp (2 * (|w 0| + |w 1|)) * (1 / (4 * Real.pi ^ 2))

theorem measurable_Cc_FIN050 : Measurable Cc_FIN050 := by
  unfold Cc_FIN050
  have h0 : Measurable fun w : Fin 2 → ℝ => w 0 := measurable_pi_apply 0
  have h1 : Measurable fun w : Fin 2 → ℝ => w 1 := measurable_pi_apply 1
  exact (Real.measurable_exp.comp (measurable_const.mul (h0.abs.add h1.abs))).mul measurable_const

theorem cond_poincare_FIN050 (N : ℕ+) (w : Fin 2 → ℝ) :
    PoincareAt (condLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N w)
      IsSmoothPeriodicParticle smoothGamma (Cc_FIN050 w) := by
  have hp := isProbabilityMeasure_siteLaw hubbardHyp_FIN050 (m := haar 1) w
  intro f hf
  have hb := measurable_bounded_of_smooth hf
  unfold condLaw
  have hT : TP IsSmoothPeriodic gam1_FIN050
      (fun _ : Fin N => siteLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w) f :=
    { meas := hb.1
      memLp := by
        obtain ⟨B, hB⟩ := hb.2
        exact memLp_of_bounded (a := -B) (b := B) (ae_of_all _ fun x => abs_le.1 (hB x))
          hb.1.aestronglyMeasurable 2
      sm := fun x i => isSmoothPeriodic_slice_FIN050 hf x i
      aem := fun i => by
        have : dens gam1_FIN050 f i = fun x => ENNReal.ofReal (particlePartial i 0 f x ^ 2) := by
          funext x
          unfold dens gam1_FIN050
          rw [coordPartial_slice_FIN050 hf x i]
        rw [this]
        exact ((measurable_bounded_partial_of_smooth hf i 0).1.pow_const 2).ennreal_ofReal.aemeasurable }
  have := poincare_tensorization (fun _ : Fin N => siteLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) w)
    (fun _ => site_poincare_FIN050 w) f hT
  refine this.trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  unfold smoothGamma
  have e : ∀ i, gam1_FIN050 (slice i f x) (x i) = ENNReal.ofReal (particlePartial i 0 f x ^ 2) := by
    intro i
    unfold gam1_FIN050
    rw [coordPartial_slice_FIN050 hf x i]
  simp_rw [e]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp


/-! ### Gaussian exponential moment -/

open DGPS.FiniteN.Tools.GaussianCoupling

theorem lintegral_gauss_exp_FIN050 (N : ℕ+) (c s : Fin 2 → ℝ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) ∂gaussLaw tiltD N c =
      ENNReal.ofReal (Real.exp (c ⬝ᵥ s + (s ⬝ᵥ tiltD *ᵥ s) / (2 * (N : ℝ)))) := by
  have hD := tiltD_posDef
  unfold gaussLaw
  have hm1 : Measurable fun w : Fin 2 → ℝ => ENNReal.ofReal (gaussNorm tiltD N * gaussWeight tiltD c N w) :=
    ((continuous_gaussWeight tiltD c N).measurable.const_mul _).ennreal_ofReal
  have hm2 : Measurable fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) := by
    refine Real.measurable_exp.ennreal_ofReal.comp ?_
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _
  rw [lintegral_withDensity_eq_lintegral_mul _ hm1 hm2, ← integral_gaussWeight_mul_exp hD N c s,
    ofReal_integral_eq_lintegral_ofReal ((integrable_gaussWeight_mul_exp hD N c s).const_mul _)
      (Filter.Eventually.of_forall fun w =>
        mul_nonneg (gaussNorm_pos hD N).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
  refine lintegral_congr fun w => ?_
  simp only [Pi.mul_apply]
  have hg : 0 ≤ gaussNorm tiltD N * gaussWeight tiltD c N w :=
    mul_nonneg (gaussNorm_pos hD N).le (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hg, mul_assoc]

theorem exp_le_four_FIN050 (w : Fin 2 → ℝ) :
    Real.exp (2 * (|w 0| + |w 1|)) ≤
      Real.exp (w ⬝ᵥ ![2, 2]) + Real.exp (w ⬝ᵥ ![2, -2]) +
        Real.exp (w ⬝ᵥ ![-2, 2]) + Real.exp (w ⬝ᵥ ![-2, -2]) := by
  have key : ∀ t : ℝ, Real.exp (2 * |t|) ≤ Real.exp (2 * t) + Real.exp (-(2 * t)) := by
    intro t
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith [Real.exp_pos (-(2 * t))]
    · rw [h]; have : 2 * -t = -(2 * t) := by ring
      rw [this]; linarith [Real.exp_pos (2 * t)]
  have e : Real.exp (2 * (|w 0| + |w 1|)) = Real.exp (2 * |w 0|) * Real.exp (2 * |w 1|) := by
    rw [← Real.exp_add]; congr 1; ring
  have h0 := key (w 0)
  have h1 := key (w 1)
  have p0 := Real.exp_pos (2 * w 0)
  have p1 := Real.exp_pos (2 * w 1)
  have q0 := Real.exp_pos (-(2 * w 0))
  have q1 := Real.exp_pos (-(2 * w 1))
  have d : ∀ a b : ℝ, w ⬝ᵥ ![a, b] = a * w 0 + b * w 1 := by
    intro a b; simp [dotProduct, Fin.sum_univ_two]; ring
  rw [e]
  simp only [d]
  have f1 : Real.exp (2 * w 0 + 2 * w 1) = Real.exp (2 * w 0) * Real.exp (2 * w 1) :=
    Real.exp_add _ _
  have f2 : Real.exp (2 * w 0 + -2 * w 1) = Real.exp (2 * w 0) * Real.exp (-(2 * w 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  have f3 : Real.exp (-2 * w 0 + 2 * w 1) = Real.exp (-(2 * w 0)) * Real.exp (2 * w 1) := by
    rw [← Real.exp_add]; congr 1; ring
  have f4 : Real.exp (-2 * w 0 + -2 * w 1) = Real.exp (-(2 * w 0)) * Real.exp (-(2 * w 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [f1, f2, f3, f4]
  have := mul_le_mul h0 h1 (Real.exp_pos _).le (add_pos p0 q0).le
  linarith


theorem measurable_expdot_FIN050 (s : Fin 2 → ℝ) :
    Measurable fun w : Fin 2 → ℝ => ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) := by
  refine Real.measurable_exp.ennreal_ofReal.comp ?_
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

theorem exp_bound_FIN050 (N : ℕ+) (c : Fin 2 → ℝ) (hc : |c 0| + |c 1| ≤ 9) (a b : ℝ)
    (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    ENNReal.ofReal (Real.exp (c ⬝ᵥ ![a, b] + (![a, b] ⬝ᵥ tiltD *ᵥ ![a, b]) / (2 * (N : ℝ)))) ≤
      ENNReal.ofReal (Real.exp 34) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  rw [dot_tiltD]
  simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : c 0 * a ≤ |c 0| * 2 := by
    calc c 0 * a ≤ |c 0 * a| := le_abs_self _
      _ = |c 0| * |a| := abs_mul _ _
      _ ≤ |c 0| * 2 := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
  have h2 : c 1 * b ≤ |c 1| * 2 := by
    calc c 1 * b ≤ |c 1 * b| := le_abs_self _
      _ = |c 1| * |b| := abs_mul _ _
      _ ≤ |c 1| * 2 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have ha2 : a ^ 2 ≤ 4 := by nlinarith [abs_nonneg a, sq_abs a]
  have hb2 : b ^ 2 ≤ 4 := by nlinarith [abs_nonneg b, sq_abs b]
  have h3 : 4 * (a ^ 2 + b ^ 2) / (2 * (N : ℝ)) ≤ 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem moment_FIN050 (N : ℕ+) (c : Fin 2 → ℝ) (hc : |c 0| + |c 1| ≤ 9) :
    ∫⁻ w, ENNReal.ofReal (Cc_FIN050 w) ∂gaussLaw tiltD N c ≤
      ENNReal.ofReal (Real.exp 34 / Real.pi ^ 2) := by
  have hpi := Real.pi_pos
  have hpt : ∀ w : Fin 2 → ℝ, ENNReal.ofReal (Cc_FIN050 w) ≤
      ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) *
        (ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, 2])) + ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, -2])) +
          ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, 2])) + ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, -2]))) := by
    intro w
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold Cc_FIN050
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (exp_le_four_FIN050 w) (by positivity)
  refine (lintegral_mono hpt).trans ?_
  have m1 := measurable_expdot_FIN050 ![2, 2]
  have m2 := measurable_expdot_FIN050 ![2, -2]
  have m3 := measurable_expdot_FIN050 ![-2, 2]
  have hsplit : ∫⁻ w, (ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, 2])) +
        ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, -2])) +
          ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, 2])) + ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, -2])))
        ∂gaussLaw tiltD N c =
      ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, 2])) ∂gaussLaw tiltD N c +
      ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, -2])) ∂gaussLaw tiltD N c +
      ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, 2])) ∂gaussLaw tiltD N c +
      ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, -2])) ∂gaussLaw tiltD N c := by
    rw [lintegral_add_left (f := fun w => ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, 2])) +
        ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, -2])) +
          ENNReal.ofReal (Real.exp (w ⬝ᵥ ![-2, 2]))) ((m1.add m2).add m3),
      lintegral_add_left (f := fun w => ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, 2])) +
        ENNReal.ofReal (Real.exp (w ⬝ᵥ ![2, -2]))) (m1.add m2),
      lintegral_add_left m1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsplit,
    lintegral_gauss_exp_FIN050, lintegral_gauss_exp_FIN050, lintegral_gauss_exp_FIN050,
    lintegral_gauss_exp_FIN050]
  have e1 := exp_bound_FIN050 N c hc 2 2 (by norm_num) (by norm_num)
  have e2 := exp_bound_FIN050 N c hc 2 (-2) (by norm_num) (by norm_num)
  have e3 := exp_bound_FIN050 N c hc (-2) 2 (by norm_num) (by norm_num)
  have e4 := exp_bound_FIN050 N c hc (-2) (-2) (by norm_num) (by norm_num)
  calc ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) * _
      ≤ ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) *
        (ENNReal.ofReal (Real.exp 34) + ENNReal.ofReal (Real.exp 34) +
          ENNReal.ofReal (Real.exp 34) + ENNReal.ofReal (Real.exp 34)) := by gcongr
    _ = ENNReal.ofReal (Real.exp 34 / Real.pi ^ 2) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
        ← ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

theorem sq_phiT_FIN050 (x : Torus 1) : ∑ j, phiT x j ^ 2 = 1 := by
  rw [Fin.sum_univ_two, phiT_zero_FIN050, phiT_one_FIN050]
  have h := norm_phase x
  rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply] at h
  nlinarith

theorem hL_FIN050 (x : Torus 1) : Real.sqrt (∑ j, phiT x j ^ 2) ≤ 1 := by
  rw [sq_phiT_FIN050]; simp

theorem center_bound_FIN050 (N : ℕ+) (x : ParticleSpace 1 N) :
    |posteriorCenter tiltD tiltH phiT N x 0| + |posteriorCenter tiltD tiltH phiT N x 1| ≤ 9 := by
  have hb : ∀ i j, |phiT (x i) j| ≤ 1 := fun i j => by
    have h := norm_le_pi_norm (phi (angEquiv (x i))) j
    rw [Real.norm_eq_abs] at h
    exact le_trans h (norm_phi_le _)
  have hS : ∀ j, |fieldSum phiT x j| ≤ N := fun j => by
    unfold fieldSum
    rw [Finset.sum_apply]
    calc |∑ i, phiT (x i) j| ≤ ∑ i, |phiT (x i) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => hb i j
      _ = N := by simp
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  have hD : ∀ j, (tiltD *ᵥ fieldSum phiT x) j = 4 * fieldSum phiT x j := fun j => by
    rw [tiltD, Matrix.mulVec_diagonal]
  have key : ∀ j, |(N : ℝ)⁻¹ * (4 * fieldSum phiT x j)| ≤ 4 := fun j => by
    rw [abs_mul, abs_mul, abs_inv, abs_of_pos hN]
    have := hS j
    have h2 : (N : ℝ)⁻¹ * |fieldSum phiT x j| ≤ 1 := by
      rw [inv_mul_le_iff₀ hN]; linarith
    norm_num
    nlinarith [abs_nonneg (fieldSum phiT x j), inv_pos.2 hN]
  have c0 : posteriorCenter tiltD tiltH phiT N x 0 = 1 / 2 + (N : ℝ)⁻¹ * (4 * fieldSum phiT x 0) := by
    rw [posteriorCenter, Pi.add_apply, Pi.smul_apply, hD]
    simp [tiltH]
  have c1 : posteriorCenter tiltD tiltH phiT N x 1 = (N : ℝ)⁻¹ * (4 * fieldSum phiT x 1) := by
    rw [posteriorCenter, Pi.add_apply, Pi.smul_apply, hD]
    simp [tiltH]
  rw [c0, c1]
  have k0 := key 0
  have k1 := key 1
  have : |1 / 2 + (N : ℝ)⁻¹ * (4 * fieldSum phiT x 0)| ≤ 1 / 2 + 4 :=
    (abs_add_le _ _).trans (by
      have : |(1 : ℝ) / 2| = 1 / 2 := by norm_num
      linarith)
  linarith

theorem hK_FIN050 (N : ℕ+) (x : ParticleSpace 1 N) :
    ∫⁻ w, ENNReal.ofReal (Cc_FIN050 w) ∂gaussLaw tiltD N (posteriorCenter tiltD tiltH phiT N x) ≤
      ENNReal.ofReal (Real.exp 34 / Real.pi ^ 2) :=
  moment_FIN050 N _ (center_bound_FIN050 N x)


section CondMeanSmooth

variable {k : ℕ}

theorem contDiff_lin_FIN050 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {a : E → Fin k → ℝ} (ha : ∀ j, ContDiff ℝ n fun w => a w j) :
    ContDiff ℝ n fun w => lin (a w) := by
  have : (fun w => lin (a w)) = fun w => ∑ j, a w j • ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin k => ℝ) j := by
    funext w; simp [lin]
  rw [this]
  exact ContDiff.sum fun j _ => (ha j).smul contDiff_const

theorem contDiff_tilt_nat_FIN050 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {V : Y → ℝ} {S : Y → Fin k → ℝ} (hV : Measurable V) (hS : Measurable S) {c u : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ y j, |S y j| ≤ c) (hu : ∀ y, -u ≤ V y) (n : ℕ) :
    ∀ {g : Y → ℝ}, Measurable g → ∀ {B : ℝ}, 0 ≤ B → (∀ y, |g y| ≤ B) →
      ContDiff ℝ n (tilt (ν := ν) g V S) := by
  induction n with
  | zero =>
    intro g hg B hB0 hB
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun w =>
      (hasFDerivAt_tilt hg hV hS hB0 hc0 hB hc hu w).continuousAt)
  | succ n ih =>
    intro g hg B hB0 hB
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 := by
      push_cast; rfl
    rw [hcast, contDiff_succ_iff_hasFDerivAt]
    have hSj : ∀ j, Measurable fun y => S y j := fun j => (measurable_pi_apply j).comp hS
    refine ⟨fun w => lin fun j => tilt (ν := ν) (fun y => g y * S y j) V S w, ?_, fun w =>
      hasFDerivAt_tilt hg hV hS hB0 hc0 hB hc hu w⟩
    refine contDiff_lin_FIN050 (E := Fin k → ℝ)
      (a := fun w j => tilt (ν := ν) (fun y => g y * S y j) V S w) fun j => ?_
    exact ih (hg.mul (hSj j)) (mul_nonneg hB0 hc0) fun y => by
      rw [abs_mul]; exact mul_le_mul (hB y) (hc y j) (abs_nonneg _) hB0


theorem contDiff_tilt_FIN050 {Y : Type*} [MeasurableSpace Y] {ν : Measure Y} [IsFiniteMeasure ν]
    {V : Y → ℝ} {S : Y → Fin k → ℝ} (hV : Measurable V) (hS : Measurable S) {c u : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ y j, |S y j| ≤ c) (hu : ∀ y, -u ≤ V y) {g : Y → ℝ} (hg : Measurable g)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, |g y| ≤ B) : ContDiff ℝ ∞ (tilt (ν := ν) g V S) :=
  contDiff_infty.2 fun n => contDiff_tilt_nat_FIN050 hV hS hc0 hc hu n hg hB0 hB

theorem contDiff_condMean_FIN050 {M : Type*} [MeasurableSpace M] {m : Measure M}
    [IsFiniteMeasure m] {U : M → ℝ} {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ) {N : ℕ+}
    {f : (Fin N → M) → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    ContDiff ℝ ∞ (condMean U φ m N f) := by
  obtain ⟨c, hc0, hc⟩ := abs_fieldSum_le hyp (N := N)
  obtain ⟨c0, hc0'⟩ := hyp.U_lower
  have hVm : Measurable (potSum U : (Fin N → M) → ℝ) :=
    Finset.measurable_sum _ fun i _ => hyp.U_meas.comp (measurable_pi_apply i)
  have hu : ∀ x : Fin N → M, -(N * |c0|) ≤ potSum U x := by
    intro x
    unfold potSum
    have : ∀ i : Fin N, -|c0| ≤ U (x i) := fun i => by
      linarith [hc0' (x i), neg_abs_le c0]
    calc -(N * |c0|) = ∑ _i : Fin N, -|c0| := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have h1 := contDiff_tilt_FIN050 (ν := Measure.pi fun _ : Fin N => m) hVm
    (measurable_fieldSum hyp) hc0 hc hu hf hB0 (fun y => (hB y).trans (le_max_left _ _))
  have h2 := contDiff_tilt_FIN050 (ν := Measure.pi fun _ : Fin N => m) hVm
    (measurable_fieldSum hyp) hc0 hc hu (g := fun _ => (1 : ℝ)) measurable_const zero_le_one
    (fun y => by simp)
  have hfun : condMean U φ m N f = fun w =>
      tilt (ν := Measure.pi fun _ : Fin N => m) f (potSum U) (fieldSum φ) w /
        tilt (ν := Measure.pi fun _ : Fin N => m) (fun _ => (1 : ℝ)) (potSum U) (fieldSum φ) w := by
    funext w
    simp only [condMean, integral_condLaw hyp N w, tilt_one hyp]
  rw [hfun]
  exact h1.div h2 fun w => by
    rw [tilt_one hyp]; exact (pow_pos (auxPartition_pos hyp w) _).ne'


end CondMeanSmooth

section GenTransfer

variable {k : ℕ}

section Transfer

variable {M : Type*} [MeasurableSpace M] {m : Measure M} [IsFiniteMeasure m] {U : M → ℝ}
  {φ : M → Fin k → ℝ} (hyp : HubbardHyp m U φ) {D : Matrix (Fin k) (Fin k) ℝ}
include hyp

/-- **Abstract auxiliary-to-particle Poincare transfer.** -/
theorem poincare_transfer_gen_FIN050 (hD : D.PosDef) (h : Fin k → ℝ) (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    {Sa : ((Fin k → ℝ) → ℝ) → Prop}
    (haux : PoincareAt (auxLaw D h U φ m N) Sa auxGradSq lam⁻¹)
    {Sm : ((Fin N → M) → ℝ) → Prop} {Γ : ((Fin N → M) → ℝ) → (Fin N → M) → ℝ≥0∞}
    (hSm : ∀ f, Sm f → Measurable f ∧ ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (hΓ : ∀ f, Sm f → Measurable (Γ f))
    (hSa : ∀ f, Sm f → Sa (condMean U φ m N f))
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ m N w) Sm Γ (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x)) ≤
      ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    PoincareAt (hubbardParticleLaw D h U φ m N) Sm Γ (K * (1 + N * L ^ 2 / lam)) := by
  intro f hfS
  obtain ⟨hf, B, hB⟩ := hSm f hfS
  have hΓf := hΓ f hfS
  have := DGPS.FiniteN.Tools.AuxiliaryTransfer.isProbabilityMeasure_auxLaw hyp hD h N
  have := isProbabilityMeasure_particleLaw hyp hD h N
  set P := hubbardParticleLaw D h U φ m N with hP
  set η := auxLaw D h U φ m N with hη
  set a := condMean U φ m N f with ha
  have hder : ∀ w, HasFDerivAt a (lin (condGrad U φ m N f w)) w :=
    fun w => hasFDerivAt_condMean hyp hf hB w
  set T : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (C w) * ∫⁻ x, Γ f x ∂(condLaw U φ m N w) ∂η with hT
  have hV : ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η ≤ T :=
    lintegral_mono fun w => by
      have := isProbabilityMeasure_condLaw hyp N w
      have hmem : MemLp f 2 (condLaw U φ m N w) :=
        MemLp.of_bound hf.aestronglyMeasurable B
          (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
      rw [hmem.ofReal_variance_eq]
      exact hcond w f hfS
  have hgrad : ∫⁻ w, auxGradSq a w ∂η ≤ ENNReal.ofReal (N * L ^ 2) * T := by
    calc ∫⁻ w, auxGradSq a w ∂η
        ≤ ∫⁻ w, ENNReal.ofReal (N * L ^ 2) *
            ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η := by
          refine lintegral_mono fun w => ?_
          unfold auxGradSq
          have hfd : fderiv ℝ a w = lin (condGrad U φ m N f w) := (hder w).fderiv
          have hs : ∑ j, (fderiv ℝ a w (Pi.single j 1)) ^ 2 =
              ∑ j, condGrad U φ m N f w j ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hfd, lin_apply]
            simp [Pi.single_apply]
          rw [hs, ← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal
            (condGrad_sq_le hyp hf hB w hL)
      _ = ENNReal.ofReal (N * L ^ 2) *
            ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (N * L ^ 2) * T := by gcongr
  have haux' := haux a (hSa f hfS)
  have hsplit := ofReal_variance_split hyp hD h N hf hB
  have hfP : MemLp f 2 P :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hx : 0 ≤ (N : ℝ) * L ^ 2 / lam := by positivity
  have hstep : evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
    calc evariance f P
        = ∫⁻ w, ENNReal.ofReal (variance f (condLaw U φ m N w)) ∂η + evariance a η := by
          rw [← hfP.ofReal_variance_eq]; exact hsplit
      _ ≤ T + ENNReal.ofReal lam⁻¹ * (ENNReal.ofReal (N * L ^ 2) * T) :=
          add_le_add hV (haux'.trans (by gcongr))
      _ = ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := by
          have e : lam⁻¹ * ((N : ℝ) * L ^ 2) = N * L ^ 2 / lam := by
            rw [div_eq_inv_mul]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le), e,
            ENNReal.ofReal_add zero_le_one hx, ENNReal.ofReal_one, add_mul, one_mul]
  have hCm : Measurable fun w => ENNReal.ofReal (C w) := ENNReal.measurable_ofReal.comp hC
  have hTle : T ≤ ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := by
    have hG : Measurable fun z : (Fin k → ℝ) × (Fin N → M) => ENNReal.ofReal (C z.1) * Γ f z.2 :=
      (hCm.comp measurable_fst).mul (hΓf.comp measurable_snd)
    have e1 : T = ∫⁻ z, ENNReal.ofReal (C z.1) * Γ f z.2 ∂(hubbardJoint D h U φ m N) := by
      rw [lintegral_joint_eq hyp hD h N hG]
      refine lintegral_congr fun w => ?_
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    rw [e1, lintegral_joint_eq_gauss hyp hD h N hG]
    calc ∫⁻ x, ∫⁻ w, ENNReal.ofReal (C w) * Γ f x
          ∂(gaussLaw D N (posteriorCenter D h φ N x)) ∂P
        = ∫⁻ x, (∫⁻ w, ENNReal.ofReal (C w)
          ∂(gaussLaw D N (posteriorCenter D h φ N x))) * Γ f x ∂P :=
          lintegral_congr fun x => lintegral_mul_const _ hCm
      _ ≤ ∫⁻ x, ENNReal.ofReal K * Γ f x ∂P :=
          lintegral_mono fun x => by gcongr; exact hK x
      _ = ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P := lintegral_const_mul _ hΓf
  calc evariance f P ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * T := hstep
    _ ≤ ENNReal.ofReal (1 + N * L ^ 2 / lam) * (ENNReal.ofReal K * ∫⁻ x, Γ f x ∂P) :=
        by gcongr
    _ = ENNReal.ofReal (K * (1 + N * L ^ 2 / lam)) * ∫⁻ x, Γ f x ∂P := by
        rw [ENNReal.ofReal_mul hK0]; ring

end Transfer


end GenTransfer

section Extension

open Filter Topology DGPS.FiniteN.Tools.LSIExtension



theorem cut_tendsto_FIN050 (x : (EuclideanSpace ℝ (Fin 2))) : Tendsto (fun n : ℕ => cut n x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
  symm
  have h1 := Nat.le_ceil ‖x‖
  have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  exact cut_eq_one (by linarith)

theorem poincare_ext_FIN050 {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ] {r : ℝ}
    (hμ : ∀ F : (EuclideanSpace ℝ (Fin 2)) → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F → ∫ x, F x ∂μ = 0 →
      r * ∫ x, F x ^ 2 ∂μ ≤ ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂μ)
    {G : (EuclideanSpace ℝ (Fin 2)) → ℝ} (hG : ContDiff ℝ ∞ G) {M : ℝ} (hM : ∀ x, |G x| ≤ M) {Γ : ℝ}
    (hΓ : ∀ x, ‖fderiv ℝ G x‖ ≤ Γ) :
    r * ∫ x, (G x - ∫ y, G y ∂μ) ^ 2 ∂μ ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂μ := by
  obtain ⟨C, hC0, hC⟩ := exists_cut_fderiv_bound (k := 2)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ 0)
  set m : ℝ := ∫ y, G y ∂μ with hm
  have hGc : Continuous G := hG.continuous
  have hcutc : ∀ n : ℕ, Continuous (cut (k := 2) n) := fun n => (cut_contDiff n).continuous
  have hGint : Integrable G μ := Integrable.of_bound hGc.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  -- integrals of cut and cut * G
  set I : ℕ → ℝ := fun n => ∫ x, cut n x ∂μ with hI
  set J : ℕ → ℝ := fun n => ∫ x, cut n x * G x ∂μ with hJ
  have hIt : Tendsto I atTop (𝓝 1) := by
    have := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n x => cut (k := 2) n x)
      (f := fun _ => (1 : ℝ)) (fun _ => 1)
      (fun n => (hcutc n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cut_nonneg n x)]; exact cut_le_one n x)
      (Eventually.of_forall cut_tendsto_FIN050)
    simpa using this
  have hJt : Tendsto J atTop (𝓝 m) := by
    refine tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n x => cut (k := 2) n x * G x)
      (f := G) (fun _ => M)
      (fun n => ((hcutc n).mul hGc).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n x)]
      calc cut n x * |G x| ≤ 1 * M :=
            mul_le_mul (cut_le_one n x) (hM x) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · simpa using (cut_tendsto_FIN050 x).mul_const (G x)
  set b : ℕ → ℝ := fun n => J n / I n with hb
  have hbt : Tendsto b atTop (𝓝 m) := by
    have := hJt.div hIt one_ne_zero
    rw [div_one] at this
    exact this
  have hIpos : ∀ᶠ n in atTop, I n ≠ 0 := by
    filter_upwards [hIt.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    exact hn.ne'
  have hbb : ∀ᶠ n in atTop, |b n| ≤ |m| + 1 := by
    have := (hbt.sub_const m).abs
    simp only [sub_self, abs_zero] at this
    filter_upwards [this.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    calc |b n| = |(b n - m) + m| := by ring_nf
      _ ≤ |b n - m| + |m| := abs_add_le _ _
      _ ≤ |m| + 1 := by linarith
  -- test functions
  set F : ℕ → (EuclideanSpace ℝ (Fin 2)) → ℝ := fun n x => cut n x * (G x - b n) with hF
  have hFd : ∀ n, ContDiff ℝ ∞ (F n) := fun n =>
    (cut_contDiff n).mul (hG.sub contDiff_const)
  have hFs : ∀ n, HasCompactSupport (F n) := fun n =>
    (cut_compactSupport n).mul_right
  have hFmean : ∀ᶠ n in atTop, ∫ x, F n x ∂μ = 0 := by
    filter_upwards [hIpos] with n hn
    have h1 : Integrable (fun x => cut (k := 2) n x * G x) μ :=
      Integrable.of_bound ((hcutc n).mul hGc).aestronglyMeasurable M
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg n x)]
          calc cut n x * |G x| ≤ 1 * M :=
                mul_le_mul (cut_le_one n x) (hM x) (abs_nonneg _) zero_le_one
            _ = M := one_mul M)
    have h2 : Integrable (fun x => cut (k := 2) n x) μ :=
      Integrable.of_bound (hcutc n).aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (cut_nonneg n x)]; exact cut_le_one n x)
    have : (fun x => F n x) = fun x => cut n x * G x - b n * cut n x := by
      funext x; simp only [hF]; ring
    rw [this, integral_sub h1 (h2.const_mul _), integral_const_mul]
    change J n - b n * I n = 0
    simp only [hb]
    field_simp
    ring
  -- limit of F n x
  have hFev : ∀ x : (EuclideanSpace ℝ (Fin 2)), ∀ᶠ n : ℕ in atTop, F n =ᶠ[𝓝 x] fun y => G y - b n := by
    intro x
    filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by
      have : ‖x‖ ≤ (⌈‖x‖⌉₊ : ℝ) := Nat.le_ceil _
      have : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
      linarith
    have : ∀ᶠ y in 𝓝 x, ‖y‖ < (n : ℝ) + 1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds hx)
    filter_upwards [this] with y hy
    simp [hF, cut_eq_one hy.le]
  have hFlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x - m)) := by
    intro x
    refine ((tendsto_const_nhds.sub hbt)).congr' ?_
    filter_upwards [hFev x] with n hn
    exact (hn.eq_of_nhds).symm
  have hdlim : ∀ x, ∀ᶠ n : ℕ in atTop, fderiv ℝ (F n) x = fderiv ℝ G x := by
    intro x
    filter_upwards [hFev x] with n hn
    rw [hn.fderiv_eq, fderiv_sub_const]
  -- bounds
  have hFb : ∀ᶠ n in atTop, ∀ x, |F n x| ≤ M + (|m| + 1) := by
    filter_upwards [hbb] with n hn x
    simp only [hF]
    rw [abs_mul, abs_of_nonneg (cut_nonneg n x)]
    calc cut n x * |G x - b n| ≤ 1 * (M + (|m| + 1)) := by
          refine mul_le_mul (cut_le_one n x) ?_ (abs_nonneg _) zero_le_one
          calc |G x - b n| ≤ |G x| + |b n| := abs_sub _ _
            _ ≤ _ := add_le_add (hM x) hn
      _ = _ := one_mul _
  have hFdb : ∀ᶠ n in atTop, ∀ x, ‖fderiv ℝ (F n) x‖ ≤ Γ + (M + (|m| + 1)) * C := by
    filter_upwards [hbb] with n hn x
    have h1 : DifferentiableAt ℝ (cut (k := 2) n) x :=
      ((cut_contDiff n).differentiable (by simp)) x
    have h2 : DifferentiableAt ℝ (fun y => G y - b n) x :=
      (hG.differentiable (by simp) x).sub_const _
    have : fderiv ℝ (F n) x = cut n x • fderiv ℝ (fun y => G y - b n) x +
        (G x - b n) • fderiv ℝ (cut n) x := fderiv_mul h1 h2
    rw [this, fderiv_sub_const]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg n x)]
      calc cut n x * ‖fderiv ℝ G x‖ ≤ 1 * Γ :=
            mul_le_mul (cut_le_one n x) (hΓ x) (norm_nonneg _) zero_le_one
        _ = Γ := one_mul Γ
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul ?_ (hC n x) (norm_nonneg _) (by positivity)
      calc |G x - b n| ≤ |G x| + |b n| := abs_sub _ _
        _ ≤ _ := add_le_add (hM x) hn
  -- convergence of the two integrals
  have hL1 : Tendsto (fun n => ∫ x, F n x ^ 2 ∂μ) atTop (𝓝 (∫ x, (G x - m) ^ 2 ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (M + (|m| + 1)) ^ 2)
      (Eventually.of_forall fun n => ((hFd n).continuous.pow 2).aestronglyMeasurable) ?_
      (integrable_const _) (Eventually.of_forall fun x => (hFlim x).pow 2)
    filter_upwards [hFb] with n hn
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hn x) 2
  have hL2 : Tendsto (fun n => ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 ∂μ) atTop
      (𝓝 (∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun _ => (Γ + (M + (|m| + 1)) * C) ^ 2)
      (Eventually.of_forall fun n => (((hFd n).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable)
      ?_ (integrable_const _) (Eventually.of_forall fun x => ?_)
    · filter_upwards [hFdb] with n hn
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn x) 2
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hdlim x] with n hn
      rw [hn]
  refine le_of_tendsto_of_tendsto (hL1.const_mul r) hL2 ?_
  filter_upwards [hFmean] with n hn
  exact hμ (F n) (hFd n) (hFs n) hn


theorem norm_dual_sq_FIN050 (ℓ : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ) :
    ‖ℓ‖ ^ 2 = ∑ j : Fin 2, (ℓ (EuclideanSpace.single j 1)) ^ 2 := by
  set v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm ℓ with hv
  have h1 : ‖ℓ‖ = ‖v‖ := ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2))).symm.norm_map ℓ).symm
  have h2 : ∀ x, ℓ x = inner ℝ v x := fun x => by
    have := InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (x := v) (y := x)
    rw [hv, LinearIsometryEquiv.apply_symm_apply] at this
    exact this
  rw [h1]
  have := (EuclideanSpace.basisFun (Fin 2) ℝ).sum_sq_norm_inner_right v
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h2, EuclideanSpace.basisFun_apply, real_inner_comm, Real.norm_eq_abs, sq_abs]

theorem fderiv_comp_ofLp_FIN050 {g : (Fin 2 → ℝ) → ℝ} (hg : Differentiable ℝ g) (x : (EuclideanSpace ℝ (Fin 2))) :
    ‖fderiv ℝ (fun y : (EuclideanSpace ℝ (Fin 2)) => g (WithLp.ofLp y)) x‖ ^ 2 =
      ∑ j : Fin 2, (fderiv ℝ g (WithLp.ofLp x) (Pi.single j 1)) ^ 2 := by
  have he : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 2)) => WithLp.ofLp y) (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap x :=
    (EuclideanSpace.equiv (Fin 2) ℝ).hasFDerivAt
  have hcomp := (hg (WithLp.ofLp x)).hasFDerivAt.comp x he
  have hf : fderiv ℝ (fun y : (EuclideanSpace ℝ (Fin 2)) => g (WithLp.ofLp y)) x = _ := hcomp.fderiv
  rw [hf, norm_dual_sq_FIN050]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : (EuclideanSpace.equiv (Fin 2) ℝ) (EuclideanSpace.single j (1 : ℝ)) = Pi.single j 1 := by
    ext i
    simp [EuclideanSpace.equiv, Pi.single_apply]
  rw [ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, e1]


end Extension

section AuxPoincare

open DGPS.FiniteN.TiltedXY.Fin048

/-- Test class on the auxiliary plane: bounded smooth functions with bounded gradient. -/
def SaT_FIN050 (g : (Fin 2 → ℝ) → ℝ) : Prop :=
  (∃ B : ℝ, ∀ w, |g w| ≤ B) ∧ ContDiff ℝ ∞ g ∧
    ∃ Γ : ℝ, ∀ w, ∑ j : Fin 2, (fderiv ℝ g w (Pi.single j 1)) ^ 2 ≤ Γ

theorem aux_poincare_FIN050 :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ+, N₀ ≤ (N : ℝ) →
      PoincareAt (auxLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N)
        SaT_FIN050 auxGradSq (c * N)⁻¹ := by
  obtain ⟨c, hc, N₀, h⟩ := DGPS.FiniteN.tilted_auxiliary_rate_at_least_n
  refine ⟨c, hc, N₀, fun N hN g hg => ?_⟩
  obtain ⟨⟨B, hB⟩, hgd, Γ, hΓ⟩ := hg
  have hη : IsProbabilityMeasure (auxLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N) :=
    AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_FIN050 tiltD_posDef tiltH N
  set η := auxLaw tiltD tiltH (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N with hηdef
  have hmap := auxLaw_map_FIN050 N
  rw [← hηdef] at hmap
  have hμ : IsProbabilityMeasure (imsEta (N : ℝ) (tiltPsi 4 (1 / 2))) := by
    rw [← hmap]
    exact (Measure.isProbabilityMeasure_map_iff (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.aemeasurable).2 hη
  have hNpos : (0 : ℝ) < c * N := mul_pos hc (by exact_mod_cast N.pos)
  set G : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => g (WithLp.ofLp x) with hG
  have hGd : ContDiff ℝ ∞ G := hgd.comp PiLp.contDiff_ofLp
  have hGM : ∀ x, |G x| ≤ B := fun x => hB _
  have hgdiff : Differentiable ℝ g := hgd.differentiable (by simp)
  have hnorm : ∀ x, ‖fderiv ℝ G x‖ ^ 2 = ∑ j : Fin 2, (fderiv ℝ g (WithLp.ofLp x) (Pi.single j 1)) ^ 2 :=
    fun x => fderiv_comp_ofLp_FIN050 hgdiff x
  have hGΓ : ∀ x, ‖fderiv ℝ G x‖ ≤ √Γ := fun x => by
    rw [← Real.sqrt_sq (norm_nonneg (fderiv ℝ G x)), hnorm x]
    exact Real.sqrt_le_sqrt (hΓ _)
  have key := poincare_ext_FIN050 (μ := imsEta (N : ℝ) (tiltPsi 4 (1 / 2))) (r := c * N)
    (h N hN) hGd hGM hGΓ
  rw [← hmap] at key
  simp only [integral_map_equiv] at key
  have hGe : ∀ w : Fin 2 → ℝ, G ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) w) = g w := fun w => rfl
  have hne : ∀ w : Fin 2 → ℝ, ‖fderiv ℝ G ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) w)‖ ^ 2 =
      ∑ j : Fin 2, (fderiv ℝ g w (Pi.single j 1)) ^ 2 := fun w => hnorm _
  simp only [hGe, hne] at key
  set S : (Fin 2 → ℝ) → ℝ := fun w => ∑ j : Fin 2, (fderiv ℝ g w (Pi.single j 1)) ^ 2 with hS
  have hSc : Continuous S := by
    have hf : Continuous (fderiv ℝ g) := hgd.continuous_fderiv (by simp)
    exact continuous_finsetSum _ fun j _ => ((hf.clm_apply continuous_const).pow 2)
  have hSint : Integrable S η :=
    Integrable.of_bound hSc.aestronglyMeasurable Γ (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
      exact hΓ w)
  have hgm : Measurable g := hgd.continuous.measurable
  have hgmem : MemLp g 2 η := MemLp.of_bound hgm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB w)
  have hgrad : ∫⁻ w, auxGradSq g w ∂η = ENNReal.ofReal (∫ w, S w ∂η) := by
    rw [ofReal_integral_eq_lintegral_ofReal hSint
      (Filter.Eventually.of_forall fun w => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    rfl
  rw [← hgmem.ofReal_variance_eq, hgrad, ← ENNReal.ofReal_mul (inv_nonneg.2 hNpos.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [variance_eq_integral hgm.aemeasurable, inv_mul_eq_div, le_div_iff₀ hNpos]
  linarith

open DGPS.FiniteN.Tools.ConditionalMeanDerivative in
theorem condMean_SaT_FIN050 (N : ℕ+) {f : ParticleSpace 1 N → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    SaT_FIN050 (condMean (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N f) := by
  have hyp := hubbardHyp_FIN050
  have hP := isProbabilityMeasure_condLaw hyp N
  have hvar : ∀ w, Var[f; condLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N w] ≤ B ^ 2 := by
    intro w
    have := hP w
    refine (variance_le_expectation_sq hf.aestronglyMeasurable).trans ?_
    have h2 := norm_integral_le_of_norm_le_const (μ := condLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N w)
      (f := (f ^ 2 : ParticleSpace 1 N → ℝ)) (C := B ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Pi.pow_apply, abs_of_nonneg (sq_nonneg _)]
        calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
    simp only [probReal_univ, mul_one] at h2
    exact (le_abs_self _).trans h2
  refine ⟨⟨B, fun w => ?_⟩, contDiff_condMean_FIN050 hyp hf hB, ?_⟩
  · have := hP w
    have h3 := norm_integral_le_of_norm_le_const (μ := condLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N w)
      (f := f) (C := B) (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
    simpa [condMean, probReal_univ, Real.norm_eq_abs] using h3
  · refine ⟨N * B ^ 2, fun w => ?_⟩
    have hd := hasFDerivAt_condMean hyp hf hB w
    have e : ∀ j : Fin 2, fderiv ℝ (condMean (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N f) w
        (Pi.single j 1) = condGrad (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N f w j := by
      intro j
      rw [hd.fderiv, lin_apply]
      simp [Pi.single_apply]
    simp only [e]
    have h4 := condGrad_sq_le hyp hf hB w hL_FIN050
    calc _ ≤ _ := h4
      _ ≤ (N : ℝ) * 1 ^ 2 * B ^ 2 := by
        gcongr
        exact hvar w
      _ = _ := by ring

end AuxPoincare

section Assembly

/-- Eventual (large `N`) lower bound for the unrestricted particle Poincare rate. -/
theorem eventual_rate_FIN050 :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℝ, ∀ N : ℕ+, N₀ ≤ (N : ℝ) →
      ENNReal.ofReal r ≤ DGPS.particlePoincareRate (tiltedXYData (1 / 2) 4) N := by
  obtain ⟨c, hc, N₀, haux⟩ := aux_poincare_FIN050
  set K : ℝ := Real.exp 34 / Real.pi ^ 2 with hKdef
  have hKp : 0 < K := by positivity
  have hC0 : 0 < K * (1 + 1 / c) := by positivity
  refine ⟨(K * (1 + 1 / c))⁻¹, by positivity, N₀, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlam : 0 < c * (N : ℝ) := mul_pos hc hNpos
  have hmain := poincare_transfer_gen_FIN050 hubbardHyp_FIN050 tiltD_posDef tiltH N hlam
    (haux N hN) (Sm := IsSmoothPeriodicParticle) (Γ := smoothGamma)
    (fun f hf => measurable_bounded_of_smooth hf)
    (fun f hf => measurable_smoothGamma_of_smooth hf)
    (fun f hf => by
      obtain ⟨hm, B, hB⟩ := measurable_bounded_of_smooth hf
      exact condMean_SaT_FIN050 N hm hB)
    measurable_Cc_FIN050 (cond_poincare_FIN050 N) hKp.le (hK_FIN050 N) (fun x => hL_FIN050 x)
  rw [hubbardParticleLaw_FIN050 N] at hmain
  have hconst : K * (1 + (N : ℝ) * 1 ^ 2 / (c * N)) = K * (1 + 1 / c) := by
    field_simp
  rw [hconst] at hmain
  have hvar := (fixed_n_weighted_sobolev_extension (tiltedXYData (1 / 2) 4) N).2.2.1 _
    fun f hf => variance_le_of_poincareAt (tiltedXYData (1 / 2) 4) hC0.le hmain hf
  rw [DGPS.le_particlePoincareRate_iff_forall]
  intro f _
  rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hC0]
  have := hvar f
  linarith

/-- Uniform-in-`N` lower bound for the unrestricted particle Poincare rate. -/
theorem uniform_rate_FIN050 :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ N : ℕ+,
      ENNReal.ofReal lam0 ≤ DGPS.particlePoincareRate (tiltedXYData (1 / 2) 4) N := by
  obtain ⟨r, hr, N₀, hev⟩ := eventual_rate_FIN050
  set q : ℕ → ℝ := fun n => if h : 0 < n then
    (DGPS.particlePoincareRate (tiltedXYData (1 / 2) 4) ⟨n, h⟩).toReal else 1 with hq
  have hqpos : ∀ n, 0 < q n := by
    intro n
    by_cases h : 0 < n
    · simp only [hq, h, ↓reduceDIte]
      obtain ⟨_, _, p0, pT⟩ := rates_pos_lt_top (tiltedXYData (1 / 2) 4) ⟨n, h⟩ Nat.one_pos
      exact (toReal_bridge p0 pT).1
    · simp [hq, h]
  set M : ℕ := ⌈N₀⌉₊ with hM
  obtain ⟨n0, -, hmin⟩ := Finset.exists_min_image (Finset.range (M + 1)) q ⟨0, by simp⟩
  refine ⟨min r (q n0), lt_min hr (hqpos n0), fun N => ?_⟩
  by_cases hN : N₀ ≤ (N : ℝ)
  · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (hev N hN)
  · have hNM : (N : ℕ) ≤ M := by
      have h1 : (N : ℝ) < N₀ := not_le.1 hN
      have h2 : N₀ ≤ (M : ℝ) := Nat.le_ceil N₀
      exact_mod_cast (h1.trans_le h2).le
    have h3 : q n0 ≤ q N := hmin N (Finset.mem_range.2 (Nat.lt_succ_of_le hNM))
    have hqN : q N = (DGPS.particlePoincareRate (tiltedXYData (1 / 2) 4) N).toReal := by
      simp only [hq, N.pos, ↓reduceDIte]
      rfl
    obtain ⟨_, _, p0, pT⟩ := rates_pos_lt_top (tiltedXYData (1 / 2) 4) N Nat.one_pos
    exact ((toReal_bridge p0 pT).2.2 _).2 ((min_le_right _ _).trans (hqN ▸ h3))

end Assembly

end DGPS.FiniteN.TiltedXY.Fin050

namespace DGPS.FiniteN

open DGPS DGPS.FiniteN.TiltedXY.Fin050 DGPS.FiniteN.Tools.Hubbard
  DGPS.FiniteN.Tools.GaussianCoupling DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.AuxiliaryTransferTorus DGPS.FiniteN.Tools.ConditionalMeanDerivative
  DGPS.FiniteN.TiltedXY.Fin051

/-- **FIN050.** For the attractive finite-rank tilted XY model
(`tiltedXYData (1/2) 4`, Hubbard-Stratonovich rank two with `D = 4 I`, `h = (1/2, 0)`):

* there are conditional inverse Poincare constants `C(w)` of the one-site-product laws
  `q_w^{⊗N}` (smooth test class), of exponential growth `C(w) ≤ C₀ exp(C₀ |w|₁)`, and, since the
  posterior centers satisfy `|m_N|₁ ≤ 9`, their Gaussian posterior averages
  `E[C(m_N + N^{-1/2} ξ)]` are bounded by a single constant `K`, uniformly in `N ≥ 1` and in the
  particle configuration;
* the unrestricted particle Poincare rate is bounded below by a single `λ₀ > 0` for all `N ≥ 1`. -/
theorem posterior_averaged_conditional_constants_and_uniform_pi :
    (∃ (C : (Fin 2 → ℝ) → ℝ) (K C₀ : ℝ), 0 < C₀ ∧ 0 ≤ K ∧ Measurable C ∧
      (∀ w, C w ≤ C₀ * Real.exp (C₀ * (|w 0| + |w 1|))) ∧
      (∀ (N : ℕ+) (w : Fin 2 → ℝ),
        PoincareAt (condLaw (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) N w)
          IsSmoothPeriodicParticle smoothGamma (C w)) ∧
      (∀ (N : ℕ+) (x : ParticleSpace 1 N),
        |posteriorCenter tiltD tiltH phiT N x 0| + |posteriorCenter tiltD tiltH phiT N x 1| ≤ 9 ∧
        ∫⁻ w, ENNReal.ofReal (C w) ∂gaussLaw tiltD N (posteriorCenter tiltD tiltH phiT N x) ≤
          ENNReal.ofReal K)) ∧
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ N : ℕ+,
      ENNReal.ofReal lam0 ≤ particlePoincareRate (tiltedXYData (1 / 2) 4) N := by
  refine ⟨⟨Cc_FIN050, Real.exp 34 / Real.pi ^ 2, 2, by norm_num, by positivity,
    measurable_Cc_FIN050, fun w => ?_, cond_poincare_FIN050, fun N x =>
      ⟨center_bound_FIN050 N x, hK_FIN050 N x⟩⟩, uniform_rate_FIN050⟩
  unfold Cc_FIN050
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h1 : 1 / (4 * Real.pi ^ 2) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc Real.exp (2 * (|w 0| + |w 1|)) * (1 / (4 * Real.pi ^ 2))
      ≤ Real.exp (2 * (|w 0| + |w 1|)) * 2 :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = 2 * Real.exp (2 * (|w 0| + |w 1|)) := mul_comm _ _

end DGPS.FiniteN
