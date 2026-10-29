import DGPS.FiniteN.TiltedXYPosteriorFIN050
import DGPS.FiniteN.FalseMinimumFIN078
import DGPS.FiniteN.ScalarCosine
import DGPS.FiniteN.Tools.EntropyDefects
import DGPS.FiniteN.Tools.Rothaus

/-!
# FIN079: all-test-particle lower exponents at the false minimum

For the scalar cosine model with `κ > 2` and `0 < h < h_c(κ)`, the Poincare rate `λ_N` and the
all-test rate `r_N^all` (arbitrary, non-symmetric particle tests) satisfy
`λ_N ≥ c N⁻¹ e^{-NB}` and `r_N^all ≥ c' N⁻² e^{-NB}` for all `N ≥ 1`, with `B = ψ(-s₁) - ψ(-s₂) > 0`
the FIN076/FIN078 barrier.  Consequently `liminf N⁻¹ log λ_N ≥ -B` and
`liminf N⁻¹ log r_N^all ≥ -B`.

Route: the Hubbard-Stratonovich transfer (`poincare_transfer_gen_FIN050`, instantiated at rank
one for `scalarCosine`) turns the FIN078 auxiliary Poincare bound into a particle Poincare bound with
constant `K (1 + N/λ_aux)`; the exact angular entropy defect (FIN017) combined with Rothaus
centering gives `r_N^all` from `λ_N`; logarithms are taken after the positive finite bridge
(FIN001), and `log N / N → 0` removes the polynomial factors.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff Matrix

namespace DGPS.FiniteN.FalseMinimumFIN079

open DGPS DGPS.FiniteN DGPS.FiniteN.Tools DGPS.Circle.AngularNormalization
  DGPS.FiniteN.Tools.Hubbard DGPS.Circle.BesselMoments DGPS.Models
  DGPS.FiniteN.TiltedXY.Fin050 DGPS.FiniteN.TiltedXY.Fin051

/-- The cosine feature map `x ↦ (cos 2πx)` on `𝕋^1`, valued in `ℝ^1`. -/
noncomputable def cosF_FIN079 (x : Torus 1) : Fin 1 → ℝ := fun _ => scalarCos x

theorem cosF_apply_FIN079 (x : Torus 1) (j : Fin 1) : cosF_FIN079 x j = scalarCos x := rfl

theorem measurable_cosF_FIN079 : Measurable cosF_FIN079 :=
  Measurable.of_eval fun _ => continuous_scalarCos.measurable

theorem hubbardHyp_FIN079 :
    HubbardHyp (haar 1) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 where
  m_ne_zero := (IsProbabilityMeasure.ne_zero (haar 1))
  U_meas := measurable_const
  U_lower := ⟨0, fun _ => le_rfl⟩
  φ_meas := measurable_cosF_FIN079
  φ_bound := ⟨1, fun x => by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    simpa [cosF_apply_FIN079, Real.norm_eq_abs] using scalarCos_bound x⟩

noncomputable def cosD_FIN079 (κ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal fun _ => κ

noncomputable def cosH_FIN079 (h : ℝ) : Fin 1 → ℝ := fun _ => h

theorem cosD_posDef_FIN079 {κ : ℝ} (hκ : 0 < κ) : (cosD_FIN079 κ).PosDef := by
  unfold cosD_FIN079
  simp [Matrix.posDef_diagonal_iff, hκ]

theorem quadForm_cosD_inv_FIN079 {κ : ℝ} (hκ : 0 < κ) (v : Fin 1 → ℝ) :
    quadForm (cosD_FIN079 κ)⁻¹ v = v 0 ^ 2 / κ := by
  have : (cosD_FIN079 κ)⁻¹ = Matrix.diagonal fun _ => κ⁻¹ := by
    unfold cosD_FIN079
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; field_simp
  rw [this]
  simp [quadForm, Matrix.mulVec_diagonal, dotProduct]
  ring

theorem dot_cosD_FIN079 (κ : ℝ) (v : Fin 1 → ℝ) : v ⬝ᵥ cosD_FIN079 κ *ᵥ v = κ * v 0 ^ 2 := by
  simp [cosD_FIN079, Matrix.mulVec_diagonal, dotProduct]
  ring

theorem auxPartition_FIN079 (w : Fin 1 → ℝ) :
    auxPartition (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w = besselI 0 (w 0) := by
  have h1 := auxPartition_FIN050 ![w 0, 0]
  have h2 : auxPartition (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w =
      auxPartition (fun _ : Torus 1 => (0 : ℝ)) phiT (haar 1) ![w 0, 0] := by
    unfold auxPartition expTerm
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hs : scalarCos x = (phase x).re := rfl
    simp only [dotProduct, Fin.sum_univ_two, Fin.sum_univ_one, cosF_apply_FIN079, phiT_zero_FIN050,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero, hs]
  rw [h2, h1, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Real.norm_eq_abs, sq_abs,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs]
  rcases abs_cases (w 0) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, besselI_neg]; simp

theorem auxPotential_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (w : Fin 1 → ℝ) :
    auxPotential (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (cosD_FIN079 κ) (cosH_FIN079 h) (haar 1) w =
      scalarPsi κ h (w 0) := by
  unfold auxPotential scalarPsi
  rw [auxPartition_FIN079, quadForm_cosD_inv_FIN079 hκ]
  simp only [Pi.sub_apply, cosH_FIN079]
  field_simp

theorem fieldSum_FIN079 (N : ℕ+) (x : ParticleSpace 1 N) :
    fieldSum cosF_FIN079 x = fun _ => ∑ i, scalarCos (x i) := by
  funext j
  simp [fieldSum, cosF_apply_FIN079, Finset.sum_apply]

theorem particleWeight_FIN079 (κ h : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    particleWeight (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (cosD_FIN079 κ) (cosH_FIN079 h) N x =
      Real.exp (-particleHamiltonian (scalarCosine κ h) N x) := by
  unfold particleWeight
  congr 1
  rw [scalarCosine_hamiltonian, fieldSum_FIN079, dot_cosD_FIN079]
  simp only [cosH_FIN079, dotProduct, Finset.univ_unique, Finset.sum_singleton]
  simp
  ring

theorem hubbardParticleLaw_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    hubbardParticleLaw (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079
      (haar 1) N = DGPS.particleLaw (scalarCosine κ h) N := by
  have hP := DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
  have hH := AuxiliaryTransfer.isProbabilityMeasure_particleLaw hubbardHyp_FIN079
    (cosD_posDef_FIN079 hκ) (cosH_FIN079 h) N
  set ν : Measure (ParticleSpace 1 N) := (particleHaar 1 N).withDensity fun x =>
    ENNReal.ofReal (Real.exp (-particleHamiltonian (scalarCosine κ h) N x)) with hν
  have e1 : DGPS.particleLaw (scalarCosine κ h) N =
      ENNReal.ofReal (particlePartition (scalarCosine κ h) N)⁻¹ • ν :=
    DGPS.Particle.particleLaw_eq_smul (scalarCosine κ h) N
  have e2 : hubbardParticleLaw (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ))
      cosF_FIN079 (haar 1) N =
      (particleMass (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079
        (haar 1) N)⁻¹ • ν := by
    unfold hubbardParticleLaw
    simp_rw [particleWeight_FIN079]
    rfl
  rw [e1] at hP ⊢
  rw [e2] at hH ⊢
  exact eq_of_prob_smul hH hP

open DGPS.FiniteN.Tools.BoundedComparison DGPS.FiniteN.Tools.AuxiliaryTransferTorus
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.AuxiliaryTransfer

theorem abs_dot_cosF_le_FIN079 (w : Fin 1 → ℝ) (x : Torus 1) : |w ⬝ᵥ cosF_FIN079 x| ≤ |w 0| := by
  simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, cosF_apply_FIN079]
  rw [abs_mul]
  calc |w default| * |scalarCos x| ≤ |w default| * 1 :=
        mul_le_mul_of_nonneg_left (scalarCos_bound x) (abs_nonneg _)
    _ = |w 0| := by simp [Fin.default_eq_zero]

/-- one-site Poincare inequality for the site law, with constant `C(w) = e^{2|w₀|}/(4π²)`. -/
theorem site_poincare_FIN079 (w : Fin 1 → ℝ) :
    PoincareAt (siteLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w) IsSmoothPeriodic
      gam1_FIN050 (Real.exp (2 * |w 0|) * (1 / (4 * Real.pi ^ 2))) := by
  have := isProbabilityMeasure_siteLaw hubbardHyp_FIN079 (m := haar 1) w
  have hz := auxPartition_pos hubbardHyp_FIN079 (m := haar 1) (U := fun _ : Torus 1 => (0 : ℝ))
    (φ := cosF_FIN079) w
  refine poincare_comparison (Q := haar 1)
    (P := siteLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w)
    (ρ := siteDensity (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w) rfl
    (fun x => div_nonneg (expTerm_pos w x).le hz.le) (fun x y => ?_)
    (fun f hf => hf.isWeakGradient.memLp) base_poincare_FIN050
  unfold siteDensity expTerm
  rw [div_le_iff₀ hz, mul_div_assoc', div_mul_cancel₀ _ hz.ne', ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_dot_cosF_le_FIN079 w x
  have h2 := abs_dot_cosF_le_FIN079 w y
  have := (abs_le.1 h1).2
  have := (abs_le.1 h2).1
  linarith

/-- conditional Poincare inverse constant. -/
noncomputable def Cc_FIN079 (w : Fin 1 → ℝ) : ℝ :=
  Real.exp (2 * |w 0|) * (1 / (4 * Real.pi ^ 2))

theorem measurable_Cc_FIN079 : Measurable Cc_FIN079 := by
  unfold Cc_FIN079
  have h0 : Measurable fun w : Fin 1 → ℝ => w 0 := measurable_pi_apply 0
  exact (Real.measurable_exp.comp (measurable_const.mul h0.abs)).mul measurable_const

theorem cond_poincare_FIN079 (N : ℕ+) (w : Fin 1 → ℝ) :
    PoincareAt (condLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N w)
      IsSmoothPeriodicParticle smoothGamma (Cc_FIN079 w) := by
  have hp := isProbabilityMeasure_siteLaw hubbardHyp_FIN079 (m := haar 1) w
  intro f hf
  have hb := measurable_bounded_of_smooth hf
  unfold condLaw
  have hT : TP IsSmoothPeriodic gam1_FIN050
      (fun _ : Fin N => siteLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w) f :=
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
  have := poincare_tensorization
    (fun _ : Fin N => siteLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) w)
    (fun _ => site_poincare_FIN079 w) f hT
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

theorem lintegral_gauss_exp_FIN079 {κ : ℝ} (hκ : 0 < κ) (N : ℕ+) (c s : Fin 1 → ℝ) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) ∂gaussLaw (cosD_FIN079 κ) N c =
      ENNReal.ofReal (Real.exp (c ⬝ᵥ s + (s ⬝ᵥ cosD_FIN079 κ *ᵥ s) / (2 * (N : ℝ)))) := by
  have hD := cosD_posDef_FIN079 hκ
  unfold gaussLaw
  have hm1 : Measurable fun w : Fin 1 → ℝ =>
      ENNReal.ofReal (gaussNorm (cosD_FIN079 κ) N * gaussWeight (cosD_FIN079 κ) c N w) :=
    ((continuous_gaussWeight (cosD_FIN079 κ) c N).measurable.const_mul _).ennreal_ofReal
  have hm2 : Measurable fun w : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) := by
    refine Real.measurable_exp.ennreal_ofReal.comp ?_
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _
  rw [lintegral_withDensity_eq_lintegral_mul _ hm1 hm2, ← integral_gaussWeight_mul_exp hD N c s,
    ofReal_integral_eq_lintegral_ofReal ((integrable_gaussWeight_mul_exp hD N c s).const_mul _)
      (Filter.Eventually.of_forall fun w =>
        mul_nonneg (gaussNorm_pos hD N).le (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
  refine lintegral_congr fun w => ?_
  simp only [Pi.mul_apply]
  have hg : 0 ≤ gaussNorm (cosD_FIN079 κ) N * gaussWeight (cosD_FIN079 κ) c N w :=
    mul_nonneg (gaussNorm_pos hD N).le (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hg, mul_assoc]

theorem measurable_expdot_FIN079 (s : Fin 1 → ℝ) :
    Measurable fun w : Fin 1 → ℝ => ENNReal.ofReal (Real.exp (w ⬝ᵥ s)) := by
  refine Real.measurable_exp.ennreal_ofReal.comp ?_
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul_const _

theorem exp_le_two_FIN079 (w : Fin 1 → ℝ) :
    Real.exp (2 * |w 0|) ≤
      Real.exp (w ⬝ᵥ (fun _ => 2)) + Real.exp (w ⬝ᵥ (fun _ => -2)) := by
  have d : ∀ a : ℝ, w ⬝ᵥ (fun _ : Fin 1 => a) = a * w 0 := by
    intro a; simp [dotProduct, Fin.default_eq_zero]; ring
  rw [d, d]
  rcases abs_cases (w 0) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-2 * w 0)]
  · rw [h]
    have : 2 * -w 0 = -2 * w 0 := by ring
    rw [this]; linarith [Real.exp_pos (2 * w 0)]

theorem exp_bound_FIN079 {κ : ℝ} (hκ : 0 < κ) (N : ℕ+) (c : Fin 1 → ℝ) {a : ℝ} (hc : |c 0| ≤ a)
    (s : ℝ) (hs : |s| = 2) :
    ENNReal.ofReal (Real.exp (c ⬝ᵥ (fun _ => s) + ((fun _ : Fin 1 => s) ⬝ᵥ cosD_FIN079 κ *ᵥ
      (fun _ : Fin 1 => s)) / (2 * (N : ℝ)))) ≤ ENNReal.ofReal (Real.exp (2 * a + 2 * κ)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  rw [dot_cosD_FIN079]
  simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
  have h1 : c default * s ≤ a * 2 := by
    calc c default * s ≤ |c default * s| := le_abs_self _
      _ = |c 0| * |s| := by rw [abs_mul]; simp [Fin.default_eq_zero]
      _ ≤ a * 2 := by rw [hs]; exact mul_le_mul_of_nonneg_right hc (by norm_num)
  have hs2 : s ^ 2 = 4 := by rw [← sq_abs, hs]; norm_num
  have h3 : κ * s ^ 2 / (2 * (N : ℝ)) ≤ 2 * κ := by
    rw [hs2, div_le_iff₀ (by positivity)]
    nlinarith
  simp only [Fin.default_eq_zero] at h1 ⊢
  linarith

theorem moment_FIN079 {κ : ℝ} (hκ : 0 < κ) (N : ℕ+) (c : Fin 1 → ℝ) {a : ℝ} (hc : |c 0| ≤ a) :
    ∫⁻ w, ENNReal.ofReal (Cc_FIN079 w) ∂gaussLaw (cosD_FIN079 κ) N c ≤
      ENNReal.ofReal (Real.exp (2 * a + 2 * κ) / (2 * Real.pi ^ 2)) := by
  have hpi := Real.pi_pos
  have hpt : ∀ w : Fin 1 → ℝ, ENNReal.ofReal (Cc_FIN079 w) ≤
      ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) *
        (ENNReal.ofReal (Real.exp (w ⬝ᵥ (fun _ => 2))) +
          ENNReal.ofReal (Real.exp (w ⬝ᵥ (fun _ => -2)))) := by
    intro w
    rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold Cc_FIN079
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (exp_le_two_FIN079 w) (by positivity)
  refine (lintegral_mono hpt).trans ?_
  have m1 := measurable_expdot_FIN079 (fun _ => 2)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left m1,
    lintegral_gauss_exp_FIN079 hκ, lintegral_gauss_exp_FIN079 hκ]
  have e1 := exp_bound_FIN079 hκ N c hc 2 (by norm_num)
  have e2 := exp_bound_FIN079 hκ N c hc (-2) (by norm_num)
  calc ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) * _
      ≤ ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) *
        (ENNReal.ofReal (Real.exp (2 * a + 2 * κ)) + ENNReal.ofReal (Real.exp (2 * a + 2 * κ))) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (2 * a + 2 * κ) / (2 * Real.pi ^ 2)) := by
      rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring

theorem hL_FIN079 (x : Torus 1) : Real.sqrt (∑ j, cosF_FIN079 x j ^ 2) ≤ 1 := by
  simp only [Finset.univ_unique, Finset.sum_singleton, cosF_apply_FIN079]
  rw [Real.sqrt_sq_eq_abs]
  exact scalarCos_bound x

theorem center_bound_FIN079 (κ h : ℝ) (hκ : 0 < κ) (N : ℕ+) (x : ParticleSpace 1 N) :
    |posteriorCenter (cosD_FIN079 κ) (cosH_FIN079 h) cosF_FIN079 N x 0| ≤ |h| + κ := by
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  have hS : |fieldSum cosF_FIN079 x 0| ≤ N := by
    rw [fieldSum_FIN079]
    calc |∑ i, scalarCos (x i)| ≤ ∑ i, |scalarCos (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => scalarCos_bound (x i)
      _ = N := by simp
  have hD : (cosD_FIN079 κ *ᵥ fieldSum cosF_FIN079 x) 0 = κ * fieldSum cosF_FIN079 x 0 := by
    rw [cosD_FIN079, Matrix.mulVec_diagonal]
  have c0 : posteriorCenter (cosD_FIN079 κ) (cosH_FIN079 h) cosF_FIN079 N x 0 =
      h + (N : ℝ)⁻¹ * (κ * fieldSum cosF_FIN079 x 0) := by
    rw [posteriorCenter, Pi.add_apply, Pi.smul_apply, hD]
    simp [cosH_FIN079]
  rw [c0]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_mul, abs_inv, abs_of_pos hN, abs_of_pos hκ]
  have h2 : (N : ℝ)⁻¹ * |fieldSum cosF_FIN079 x 0| ≤ 1 := by
    rw [inv_mul_le_iff₀ hN]; linarith
  nlinarith [abs_nonneg (fieldSum cosF_FIN079 x 0), inv_pos.2 hN]

/-- The unnormalized auxiliary density on the line. -/
noncomputable def Fd_FIN079 (κ h : ℝ) (N : ℕ+) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((N : ℝ) * scalarPsi κ h t)))

theorem auxMass_eq_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    auxMass (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N =
      ∫⁻ t, Fd_FIN079 κ h N t := by
  unfold auxMass
  have e : ∀ w : Fin 1 → ℝ, ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (cosD_FIN079 κ) (cosH_FIN079 h)
        (haar 1) w)) = Fd_FIN079 κ h N (MeasurableEquiv.funUnique (Fin 1) ℝ w) := by
    intro w
    rw [auxPotential_FIN079 hκ h w, neg_mul]
    rfl
  simp_rw [e]
  exact (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding _

theorem measurable_Fd_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    Measurable (Fd_FIN079 κ h N) := by
  have := DGPS.FiniteN.FalseMinimumFIN078.scalarPsi_continuous_FIN078 (h := h) hκ
  unfold Fd_FIN079
  fun_prop

theorem integrable_exp_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    Integrable fun t => Real.exp (-((N : ℝ) * scalarPsi κ h t)) := by
  have hne := auxMass_ne_top hubbardHyp_FIN079 (cosD_posDef_FIN079 hκ) (cosH_FIN079 h) N
  rw [auxMass_eq_FIN079 hκ h N] at hne
  have hc := DGPS.FiniteN.FalseMinimumFIN078.scalarPsi_continuous_FIN078 (h := h) hκ
  refine ⟨(by fun_prop : Continuous fun t => Real.exp (-((N : ℝ) * scalarPsi κ h t))).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ t, ‖Real.exp (-((N : ℝ) * scalarPsi κ h t))‖ₑ = Fd_FIN079 κ h N t := fun t => by
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]; rfl
  simp_rw [this]
  exact lt_top_iff_ne_top.2 hne

theorem auxLaw_map_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) :
    (auxLaw (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N).map
        (MeasurableEquiv.funUnique (Fin 1) ℝ) =
      DGPS.FiniteN.densityMeasure Set.univ
        (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N) := by
  have hint := integrable_exp_FIN079 hκ h N
  have hZ : 0 < ∫ y, Real.exp (-((N : ℝ) * scalarPsi κ h y)) :=
    integral_exp_pos (f := fun y => -((N : ℝ) * scalarPsi κ h y)) hint
  have hmass : ∫⁻ t, Fd_FIN079 κ h N t =
      ENNReal.ofReal (∫ y, Real.exp (-((N : ℝ) * scalarPsi κ h y))) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    rfl
  ext s hs
  have hm := (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
  have hF := measurable_Fd_FIN079 hκ h N
  rw [Measure.map_apply hm hs]
  unfold auxLaw
  rw [Measure.smul_apply, auxMass_eq_FIN079 hκ h N, hmass, smul_eq_mul]
  unfold DGPS.FiniteN.densityMeasure
  rw [withDensity_apply _ hs, Measure.restrict_univ]
  have e : ∀ w : Fin 1 → ℝ, ENNReal.ofReal (Real.exp (-(N : ℝ) *
      auxPotential (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (cosD_FIN079 κ) (cosH_FIN079 h)
        (haar 1) w)) = Fd_FIN079 κ h N (MeasurableEquiv.funUnique (Fin 1) ℝ w) := by
    intro w
    rw [auxPotential_FIN079 hκ h w, neg_mul]
    rfl
  simp_rw [e]
  rw [withDensity_apply _ (hm hs)]
  have hpre := (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding (Fd_FIN079 κ h N) s
  refine (congrArg (fun z => (ENNReal.ofReal (∫ y, Real.exp (-((N : ℝ) * scalarPsi κ h y))))⁻¹ * z)
    hpre).trans ?_
  rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
  refine setLIntegral_congr_fun hs (fun t _ => ?_)
  unfold DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 Fd_FIN079
  rw [ENNReal.ofReal_div_of_pos hZ, ENNReal.div_eq_inv_mul]

/-- Test class on the auxiliary line: bounded smooth functions with bounded gradient. -/
def SaT_FIN079 (g : (Fin 1 → ℝ) → ℝ) : Prop :=
  (∃ B : ℝ, ∀ w, |g w| ≤ B) ∧ ContDiff ℝ ∞ g ∧
    ∃ Γ : ℝ, ∀ w, ∑ j : Fin 1, (fderiv ℝ g w (Pi.single j 1)) ^ 2 ≤ Γ

theorem aux_poincare_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    (hrate : ENNReal.ofReal lam ≤ DGPS.FiniteN.FalseMinimumFIN078.poincareRateFIN078 Set.univ
      (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N)) :
    PoincareAt (auxLaw (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079
      (haar 1) N) SaT_FIN079 auxGradSq lam⁻¹ := by
  intro g hg
  obtain ⟨⟨B, hB⟩, hgd, Γ, hΓ⟩ := hg
  set η := auxLaw (cosD_FIN079 κ) (cosH_FIN079 h) (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079
    (haar 1) N with hηdef
  have hη : IsProbabilityMeasure η :=
    AuxiliaryTransfer.isProbabilityMeasure_auxLaw hubbardHyp_FIN079 (cosD_posDef_FIN079 hκ)
      (cosH_FIN079 h) N
  set e := MeasurableEquiv.funUnique (Fin 1) ℝ with hedef
  have hmap : η.map e = DGPS.FiniteN.densityMeasure Set.univ
      (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N) :=
    auxLaw_map_FIN079 hκ h N
  set μ := DGPS.FiniteN.densityMeasure Set.univ
      (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N) with hμdef
  have hμ : IsProbabilityMeasure μ := by
    rw [← hmap]
    exact (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 hη
  set S : (Fin 1 → ℝ) → ℝ := fun w => ∑ j : Fin 1, (fderiv ℝ g w (Pi.single j 1)) ^ 2 with hS
  have hgdiff : Differentiable ℝ g := hgd.differentiable (by simp)
  have hfc : Continuous (fderiv ℝ g) := hgd.continuous_fderiv (by simp)
  have hSc : Continuous S :=
    continuous_finsetSum _ fun j _ => ((hfc.clm_apply continuous_const).pow 2)
  have hS0 : ∀ w, 0 ≤ S w := fun w => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hSint : Integrable S η :=
    Integrable.of_bound hSc.aestronglyMeasurable Γ (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hS0 w)]
      exact hΓ w)
  have hgm : Measurable g := hgd.continuous.measurable
  have hgmem : MemLp g 2 η := MemLp.of_bound hgm.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hB w)
  have hgrad : ∫⁻ w, auxGradSq g w ∂η = ENNReal.ofReal (∫ w, S w ∂η) := by
    rw [ofReal_integral_eq_lintegral_ofReal hSint (Filter.Eventually.of_forall hS0)]
    rfl
  have hlin : lam * Var[g; η] ≤ ∫ w, S w ∂η := by
    have hV0 : 0 ≤ Var[g; η] := variance_nonneg _ _
    have hE0 : 0 ≤ ∫ w, S w ∂η := integral_nonneg hS0
    rcases hV0.eq_or_lt with hV | hV
    · rw [← hV]; simpa using hE0
    -- the test pair on the line
    set G : ℝ → ℝ := fun t => g (fun _ => t) with hG
    set G' : ℝ → ℝ := fun t => fderiv ℝ g (fun _ => t) (Pi.single 0 1) with hG'
    have hsec : Continuous fun t : ℝ => (fun _ : Fin 1 => t) := continuous_pi fun _ => continuous_id
    have hderiv : ∀ t, HasDerivAt G (G' t) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (fun _ : Fin 1 => t)) (fun _ : Fin 1 => (1 : ℝ)) t :=
        hasDerivAt_pi.2 fun _ => hasDerivAt_id t
      have h2 := (hgdiff (fun _ => t)).hasFDerivAt.comp_hasDerivAt t h1
      have e1 : (fun _ : Fin 1 => (1 : ℝ)) = Pi.single 0 1 := by
        funext i; rw [Subsingleton.elim i 0]; simp
      rw [e1] at h2
      exact h2
    have hG'c : Continuous G' :=
      ((hfc.comp hsec).clm_apply continuous_const)
    have hG'sq : ∀ t, G' t ^ 2 = S (fun _ => t) := by
      intro t
      simp [hS, hG']
    have hvarEq : Var[G; μ] = Var[g; η] := by
      rw [← hmap, variance_map_equiv]
      congr 1
      funext w
      simp only [Function.comp_apply, hG, hedef]
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      rfl
    have hEeq : ∫ t, G' t ^ 2 ∂μ = ∫ w, S w ∂η := by
      rw [← hmap, integral_map_equiv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      have e2 : (fun _ : Fin 1 => e w) = w := by
        funext i; rw [Subsingleton.elim i 0]; rfl
      simp only
      rw [hG'sq, e2]
    have hpair : DGPS.FiniteN.FalseMinimumFIN078.PoincareTestFIN078 Set.univ
        (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N) G G' := by
      refine ⟨fun x _ y _ => ?_, hG'c.locallyIntegrable.locallyIntegrableOn _, ?_, ?_⟩
      · exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
          (hG'c.intervalIntegrable x y)).symm
      · refine Integrable.of_bound (hG'c.pow 2).aestronglyMeasurable Γ
          (Filter.Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hG'sq]
        exact hΓ _
      · rw [hvarEq]; exact hV
    have hkey := hrate.trans (iInf_le_of_le G (iInf_le_of_le G' (iInf_le _ hpair)))
    rw [hvarEq, hEeq] at hkey
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hV).ne')
      (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hlam.le] at hkey
    exact (ENNReal.ofReal_le_ofReal_iff hE0).1 hkey
  rw [← hgmem.ofReal_variance_eq, hgrad, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ hlam]
  linarith

open DGPS.FiniteN.Tools.ConditionalMeanDerivative in
theorem condMean_SaT_FIN079 (N : ℕ+) {f : ParticleSpace 1 N → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    SaT_FIN079 (condMean (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N f) := by
  have hyp := hubbardHyp_FIN079
  have hP := isProbabilityMeasure_condLaw hyp N
  have hvar : ∀ w, Var[f; condLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N w] ≤ B ^ 2 := by
    intro w
    have := hP w
    refine (variance_le_expectation_sq hf.aestronglyMeasurable).trans ?_
    have h2 := norm_integral_le_of_norm_le_const
      (μ := condLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N w)
      (f := (f ^ 2 : ParticleSpace 1 N → ℝ)) (C := B ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Pi.pow_apply, abs_of_nonneg (sq_nonneg _)]
        calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
    simp only [probReal_univ, mul_one] at h2
    exact (le_abs_self _).trans h2
  refine ⟨⟨B, fun w => ?_⟩, contDiff_condMean_FIN050 hyp hf hB, ?_⟩
  · have := hP w
    have h3 := norm_integral_le_of_norm_le_const
      (μ := condLaw (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N w)
      (f := f) (C := B) (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
    simpa [condMean, probReal_univ, Real.norm_eq_abs] using h3
  · refine ⟨N * B ^ 2, fun w => ?_⟩
    have hd := hasFDerivAt_condMean hyp hf hB w
    have e : ∀ j : Fin 1, fderiv ℝ (condMean (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N f) w
        (Pi.single j 1) = condGrad (fun _ : Torus 1 => (0 : ℝ)) cosF_FIN079 (haar 1) N f w j := by
      intro j
      obtain rfl : j = 0 := Subsingleton.elim j 0
      rw [hd.fderiv, lin_apply]
      simp [Pi.single_apply]
    simp only [e]
    have h4 := condGrad_sq_le hyp hf hB w hL_FIN079
    calc _ ≤ _ := h4
      _ ≤ (N : ℝ) * 1 ^ 2 * B ^ 2 := by
        gcongr
        exact hvar w
      _ = _ := by ring

/-- The constant bounding the posterior-averaged conditional Poincare constants. -/
noncomputable def Kc_FIN079 (κ h : ℝ) : ℝ :=
  Real.exp (2 * (|h| + κ) + 2 * κ) / (2 * Real.pi ^ 2)

theorem Kc_pos_FIN079 (κ h : ℝ) : 0 < Kc_FIN079 κ h := by
  unfold Kc_FIN079; positivity

theorem poincare_N_FIN079 {κ : ℝ} (hκ : 0 < κ) (h : ℝ) (N : ℕ+) {lam : ℝ} (hlam : 0 < lam)
    (hrate : ENNReal.ofReal lam ≤ DGPS.FiniteN.FalseMinimumFIN078.poincareRateFIN078 Set.univ
      (DGPS.FiniteN.FalseMinimumFIN077.auxDensityFIN077 (scalarPsi κ h) N)) :
    ENNReal.ofReal ((Kc_FIN079 κ h * (1 + (N : ℝ) / lam))⁻¹) ≤
      DGPS.particlePoincareRate (scalarCosine κ h) N := by
  have hKp := Kc_pos_FIN079 κ h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hC0 : 0 < Kc_FIN079 κ h * (1 + (N : ℝ) / lam) := by positivity
  have hmain := poincare_transfer_gen_FIN050 hubbardHyp_FIN079 (cosD_posDef_FIN079 hκ)
    (cosH_FIN079 h) N hlam (aux_poincare_FIN079 hκ h N hlam hrate)
    (Sm := IsSmoothPeriodicParticle) (Γ := smoothGamma)
    (fun f hf => measurable_bounded_of_smooth hf)
    (fun f hf => measurable_smoothGamma_of_smooth hf)
    (fun f hf => by
      obtain ⟨hm, B, hB⟩ := measurable_bounded_of_smooth hf
      exact condMean_SaT_FIN079 N hm hB)
    measurable_Cc_FIN079 (cond_poincare_FIN079 N) hKp.le
    (fun x => moment_FIN079 hκ N _ (center_bound_FIN079 κ h hκ N x))
    (fun x => hL_FIN079 x)
  rw [hubbardParticleLaw_FIN079 hκ h N] at hmain
  have hmain' : PoincareAt (particleLaw (scalarCosine κ h) N) IsSmoothPeriodicParticle smoothGamma
      (Kc_FIN079 κ h * (1 + (N : ℝ) / lam)) := by
    have e : Kc_FIN079 κ h * (1 + (N : ℝ) * 1 ^ 2 / lam) = Kc_FIN079 κ h * (1 + (N : ℝ) / lam) := by
      rw [one_pow, mul_one]
    rw [← e]; exact hmain
  have hvar := (fixed_n_weighted_sobolev_extension (scalarCosine κ h) N).2.2.1 _
    fun f hf => variance_le_of_poincareAt (scalarCosine κ h) hC0.le hmain' hf
  rw [DGPS.le_particlePoincareRate_iff_forall]
  intro f _
  rw [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hC0]
  have := hvar f
  linarith

theorem rall_lower_FIN079 {d : ℕ} (A : InteractionData d) (N : ℕ+) {a b r : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hr : 0 < r)
    (hdef : ∀ f : ParticleH1 A N, homogeneousEntropy (particleLaw A N) (fun y => f.1 y ^ 2) ≤
      ENNReal.ofReal (a * particleEnergy A N f + b * ∫ y, f.1 y ^ 2 ∂particleLaw A N))
    (hP : ENNReal.ofReal r ≤ particlePoincareRate A N) :
    ENNReal.ofReal (2 / (a + (b + 2) / r)) ≤ particleRateAll A N := by
  have := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hPf := (le_particlePoincareRate_iff_forall A N r).1 hP
  set q : ℝ := a + (b + 2) / r with hq
  have hqpos : 0 < q := by positivity
  refine le_iInf fun ⟨f, hf⟩ => ?_
  show _ ≤ particleQuotient A N f
  have hfm : MemLp f.1 2 (particleLaw A N) := (isParticleWeakGradient_particleWeakGradient f).memLp
  set m : ℝ := ∫ y, f.1 y ∂particleLaw A N with hm
  let g : ParticleH1 A N := ⟨fun x => 1 * f.1 x + (-m), f.2.elim fun _ hg => ⟨_, hg.affine 1 (-m)⟩⟩
  have hgE : particleEnergy A N g = particleEnergy A N f := by
    have := particleEnergy_affine (N := N) f g 1 (-m) rfl
    simpa using this
  have hgv : ∫ y, g.1 y ^ 2 ∂particleLaw A N = variance f.1 (particleLaw A N) := by
    rw [variance_eq_integral hfm.aemeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [g, hm]
    ring
  have hvar : variance f.1 (particleLaw A N) * r ≤ particleEnergy A N f := by
    rcases (variance_nonneg f.1 (particleLaw A N)).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul]; exact particleEnergy_nonneg f
    · rw [mul_comm]; exact hPf f h0
  have hg2 : MemLp g.1 2 (particleLaw A N) := (isParticleWeakGradient_particleWeakGradient g).memLp
  have hcent := Rothaus.rothaus_centering_variance (P := particleLaw A N) hfm
  have hgeq : (fun x => (f.1 x - m) ^ 2) = fun y => g.1 y ^ 2 := by
    funext x; simp [g]; ring
  rw [hgeq] at hcent
  have hE0 := particleEnergy_nonneg f
  have hdg := hdef g
  rw [hgE, hgv] at hdg
  have hV0 := variance_nonneg f.1 (particleLaw A N)
  have hEnt : particleEntropy A N f ≤ ENNReal.ofReal (q * particleEnergy A N f) := by
    calc particleEntropy A N f ≤ _ := hcent
      _ ≤ ENNReal.ofReal (a * particleEnergy A N f + b * variance f.1 (particleLaw A N)) +
          ENNReal.ofReal (2 * variance f.1 (particleLaw A N)) := by gcongr
      _ = ENNReal.ofReal (a * particleEnergy A N f + b * variance f.1 (particleLaw A N) +
          2 * variance f.1 (particleLaw A N)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ ENNReal.ofReal (q * particleEnergy A N f) := by
        apply ENNReal.ofReal_le_ofReal
        have : variance f.1 (particleLaw A N) ≤ particleEnergy A N f / r := by
          rw [le_div_iff₀ hr]; exact hvar
        have h2 : (b + 2) * variance f.1 (particleLaw A N) ≤ (b + 2) * (particleEnergy A N f / r) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        rw [hq]
        have : (a + (b + 2) / r) * particleEnergy A N f = a * particleEnergy A N f +
            (b + 2) * (particleEnergy A N f / r) := by ring
        rw [this]
        linarith
  have hEne : particleEntropy A N f ≠ 0 := hf.ne'
  have hEnt' : particleEntropy A N f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEnt
  unfold particleQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl hEne) (Or.inl hEnt')]
  calc ENNReal.ofReal (2 / q) * particleEntropy A N f
      ≤ ENNReal.ofReal (2 / q) * ENNReal.ofReal (q * particleEnergy A N f) := by gcongr
    _ = ENNReal.ofReal (2 * particleEnergy A N f) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp


theorem lambda_lower_FIN079 (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ B : ℝ, 0 < B ∧ ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
        DGPS.particlePoincareRate (scalarCosine κ h) N := by
  obtain ⟨s1, s2, tp, -, -, -, -, hgeom, c0, hc0, hr⟩ :=
    DGPS.FiniteN.FalseMinimumFIN078.false_minimum_auxiliary_exponential_lower κ h hκ hh0 hhc
  have hB : 0 < scalarPsi κ h (-s1) - scalarPsi κ h (-s2) := hgeom.2.2.2.2.2.2.2.1.1
  set B : ℝ := scalarPsi κ h (-s1) - scalarPsi κ h (-s2) with hBdef
  have hKp := Kc_pos_FIN079 κ h
  have hc : 0 < (Kc_FIN079 κ h * (1 + 1 / c0))⁻¹ := by positivity
  refine ⟨B, hB, _, hc, fun N => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hlam : 0 < c0 * Real.exp (-((N : ℝ) * B)) := by positivity
  have hmain := poincare_N_FIN079 (by linarith) h N hlam (hr N hN1)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have hE : 1 ≤ (N : ℝ) * Real.exp ((N : ℝ) * B) := by
    have : 1 ≤ Real.exp ((N : ℝ) * B) := Real.one_le_exp (by positivity)
    nlinarith
  have hEp : 0 < Real.exp ((N : ℝ) * B) := Real.exp_pos _
  have e1 : (Kc_FIN079 κ h * (1 + 1 / c0))⁻¹ * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B)) =
      (Kc_FIN079 κ h * (1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B)))⁻¹ := by
    rw [Real.exp_neg]
    field_simp
  rw [e1]
  apply inv_anti₀ (by positivity)
  have e2 : (N : ℝ) / (c0 * Real.exp (-((N : ℝ) * B))) =
      (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  have : 1 + (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 ≤
      (1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B)) := by
    have h3 : 0 < 1 / c0 := by positivity
    have h4 : (N : ℝ) * Real.exp ((N : ℝ) * B) / c0 =
        1 / c0 * ((N : ℝ) * Real.exp ((N : ℝ) * B)) := by ring
    rw [h4]
    nlinarith
  calc Kc_FIN079 κ h * (1 + (N : ℝ) * Real.exp ((N : ℝ) * B) / c0)
      ≤ Kc_FIN079 κ h * ((1 + 1 / c0) * ((N : ℝ) * Real.exp ((N : ℝ) * B))) :=
        mul_le_mul_of_nonneg_left this hKp.le
    _ = _ := by ring

theorem rall_lower_N_FIN079 (κ h : ℝ) (hκ : 2 < κ) (hh0 : 0 < h)
    (hhc : h < scalarFoldField κ) :
    ∃ B : ℝ, 0 < B ∧ (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
        DGPS.particlePoincareRate (scalarCosine κ h) N) ∧
      ∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c' * ((N : ℝ) ^ 2)⁻¹ * Real.exp (-((N : ℝ) * B))) ≤
        DGPS.particleRateAll (scalarCosine κ h) N := by
  obtain ⟨B, hB, c, hc, hlam⟩ := lambda_lower_FIN079 κ h hκ hh0 hhc
  refine ⟨B, hB, ⟨c, hc, hlam⟩, ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  set a : ℝ := 2 / (4 * Real.pi ^ 2) with ha
  have ha0 : 0 < a := by positivity
  set s : ℝ := |h| + κ with hs
  have hs0 : 0 ≤ s := by positivity
  set Q : ℝ := a + (s + 2) / c with hQ
  have hQ0 : 0 < Q := by positivity
  refine ⟨2 / Q, by positivity, fun N => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hEp : 0 < Real.exp ((N : ℝ) * B) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp ((N : ℝ) * B) := Real.one_le_exp (by positivity)
  have hr : 0 < c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B)) := by positivity
  have hdef := DGPS.FiniteN.EntropyDefects.cos_entropy_defect N h (κ := κ) (by linarith)
  have hmain := rall_lower_FIN079 (scalarCosine κ h) N (a := a) (b := s * N) ha0.le
    (by positivity) hr hdef (hlam N)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hmain
  have e1 : (s * N + 2) / (c * (N : ℝ)⁻¹ * Real.exp (-((N : ℝ) * B))) =
      (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c := by
    rw [Real.exp_neg]
    field_simp
  rw [e1]
  have hle : a + (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c ≤
      (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) * Q := by
    have h1 : (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c ≤
        (s + 2) * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) / c := by
      apply div_le_div_of_nonneg_right _ hc.le
      have : (s * N + 2) * N ≤ (s + 2) * (N : ℝ) ^ 2 := by nlinarith
      calc (s * N + 2) * N * Real.exp ((N : ℝ) * B)
          ≤ (s + 2) * (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) := by gcongr
        _ = _ := by ring
    have h2 : a ≤ a * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := by
      have : 1 ≤ (N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) := by nlinarith
      nlinarith
    have h3 : (s + 2) * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) / c =
        (s + 2) / c * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := by ring
    rw [h3] at h1
    calc _ ≤ a * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) +
          (s + 2) / c * ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B)) := add_le_add h2 h1
      _ = _ := by rw [hQ]; ring
  have hpos : 0 < a + (s * N + 2) * N * Real.exp ((N : ℝ) * B) / c := by positivity
  have e2 : 2 / Q * ((N : ℝ) ^ 2)⁻¹ * Real.exp (-((N : ℝ) * B)) =
      2 / ((N : ℝ) ^ 2 * Real.exp ((N : ℝ) * B) * Q) := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  exact div_le_div_of_nonneg_left (by norm_num) hpos hle

theorem tendsto_log_div_FIN079 :
    Filter.Tendsto (fun N : ℕ+ => Real.log ((N : ℕ) : ℝ) / ((N : ℕ) : ℝ)) Filter.atTop
      (nhds 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 := h.comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)
  refine h2.congr fun N => ?_
  simp

theorem tendsto_inv_FIN079 :
    Filter.Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹) Filter.atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop)

theorem liminf_lower_FIN079 {B c : ℝ} (hc : 0 < c) (p : ℕ) (r : ℕ+ → ℝ)
    (hr : ∀ N : ℕ+, c * (((N : ℕ) : ℝ) ^ p)⁻¹ * Real.exp (-(((N : ℕ) : ℝ) * B)) ≤ r N) :
    (((-B : ℝ)) : EReal) ≤
      Filter.liminf (fun N : ℕ+ => ((((N : ℕ) : ℝ)⁻¹ * Real.log (r N) : ℝ) : EReal))
        Filter.atTop := by
  set v : ℕ+ → ℝ := fun N =>
    -B + (Real.log c * ((N : ℕ) : ℝ)⁻¹ - (p : ℝ) * (Real.log ((N : ℕ) : ℝ) / ((N : ℕ) : ℝ))) with hv
  have hlim : Filter.Tendsto v Filter.atTop (nhds (-B)) := by
    have h1 := ((tendsto_inv_FIN079.const_mul (Real.log c)).sub
      (tendsto_log_div_FIN079.const_mul (p : ℝ))).const_add (-B)
    simpa using h1
  have hle : ∀ N : ℕ+, v N ≤ ((N : ℕ) : ℝ)⁻¹ * Real.log (r N) := by
    intro N
    have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    have hpos : 0 < c * (((N : ℕ) : ℝ) ^ p)⁻¹ * Real.exp (-(((N : ℕ) : ℝ) * B)) := by positivity
    have hlog := Real.log_le_log hpos (hr N)
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hc.ne' (by positivity),
      Real.log_inv, Real.log_pow, Real.log_exp] at hlog
    have : v N = ((N : ℕ) : ℝ)⁻¹ * (Real.log c - (p : ℝ) * Real.log ((N : ℕ) : ℝ) -
        ((N : ℕ) : ℝ) * B) := by
      simp only [hv]
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc (((-B : ℝ)) : EReal)
      = Filter.liminf (fun N : ℕ+ => ((v N : ℝ) : EReal)) Filter.atTop :=
        ((continuous_coe_real_ereal.tendsto _).comp hlim).liminf_eq.symm
    _ ≤ _ := Filter.liminf_le_liminf (Filter.Eventually.of_forall fun N => by
        exact_mod_cast hle N)

end DGPS.FiniteN.FalseMinimumFIN079

namespace DGPS.FiniteN

open DGPS DGPS.Models

/-- **False minimum: all-test-particle lower exponents.**  For the scalar cosine model with
`κ > 2` and `0 < h < h_c(κ)`, there is `B > 0` (the false-minimum barrier
`ψ(-s₁) - ψ(-s₂)`) and constants `c, c' > 0` with
`λ_N ≥ c N⁻¹ e^{-N B}` and `r_N^all ≥ c' N⁻² e^{-N B}` for every `N ≥ 1`
(arbitrary, non-symmetric particle tests), and consequently
`liminf N⁻¹ log λ_N ≥ -B` and `liminf N⁻¹ log r_N^all ≥ -B` (in `EReal`, along `ℕ+`). -/
theorem false_minimum_all_test_particle_lower_exponents (κ h : ℝ) (hκ : 2 < κ)
    (hh0 : 0 < h) (hhc : h < scalarFoldField κ) :
    ∃ B : ℝ, 0 < B ∧
      (∃ c : ℝ, 0 < c ∧ ∀ N : ℕ+,
        ENNReal.ofReal (c * ((N : ℕ) : ℝ)⁻¹ * Real.exp (-(((N : ℕ) : ℝ) * B))) ≤
          particlePoincareRate (scalarCosine κ h) N) ∧
      (∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
        ENNReal.ofReal (c' * (((N : ℕ) : ℝ) ^ 2)⁻¹ * Real.exp (-(((N : ℕ) : ℝ) * B))) ≤
          particleRateAll (scalarCosine κ h) N) ∧
      (((-B : ℝ)) : EReal) ≤ Filter.liminf (fun N : ℕ+ =>
        ((((N : ℕ) : ℝ)⁻¹ * Real.log (particlePoincareRate (scalarCosine κ h) N).toReal : ℝ) :
          EReal)) Filter.atTop ∧
      (((-B : ℝ)) : EReal) ≤ Filter.liminf (fun N : ℕ+ =>
        ((((N : ℕ) : ℝ)⁻¹ * Real.log (particleRateAll (scalarCosine κ h) N).toReal : ℝ) :
          EReal)) Filter.atTop := by
  obtain ⟨B, hB, ⟨c, hc, hlam⟩, c', hc', hall⟩ :=
    FalseMinimumFIN079.rall_lower_N_FIN079 κ h hκ hh0 hhc
  refine ⟨B, hB, ⟨c, hc, hlam⟩, ⟨c', hc', hall⟩, ?_, ?_⟩
  · have := FalseMinimumFIN079.liminf_lower_FIN079 (B := B) hc 1
      (fun N => (particlePoincareRate (scalarCosine κ h) N).toReal) (fun N => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hP⟩ :=
          finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
        have := (hP _).1 (hlam N)
        simpa using this)
    exact this
  · have := FalseMinimumFIN079.liminf_lower_FIN079 (B := B) hc' 2
      (fun N => (particleRateAll (scalarCosine κ h) N).toReal) (fun N => by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hA, -, -⟩ :=
          finite_positive_particle_rate_and_real_bridge (scalarCosine κ h) Nat.one_pos N
        exact (hA _).1 (hall N))
    exact this

end DGPS.FiniteN
