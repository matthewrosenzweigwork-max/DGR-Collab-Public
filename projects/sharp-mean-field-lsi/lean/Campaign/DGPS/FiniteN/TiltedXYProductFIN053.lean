import DGPS.FiniteN.TiltedXY
import DGPS.Examples.AttractiveXYTiltRemoteEX025
import DGPS.Particle.ProductRecoveryLimits
import DGPS.Particle.DiagonalForce
import DGPS.Particle.ProductForceFisher

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN.TiltedXYProductFIN053

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
  DGPS.Examples.AttractiveXYTiltEX024 DGPS.Examples.AttractiveXYTiltRemoteEX025
  DGPS.Examples.CriticalRecoveryBridgesEX021 DGPS.Circle.BesselMoments
  DGPS.Particle.ProductRecovery DGPS.Particle.ProductForceVariance DGPS.Particle.ProductForceFisher
  DGPS.Lipschitz

theorem tiltedXYData_eq_attractiveXY_FIN053 (h κ : ℝ) :
    DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData h κ = attractiveXY κ h := by
  apply InteractionData.ext
  · funext x
    show -h * (DGPS.FiniteN.TiltedXY.Fin051.phase x).re = -h * (xyMode x).re
    rw [xyMode_apply]; rfl
  · funext x y
    show κ * (1 - (DGPS.FiniteN.TiltedXY.Fin051.phase x *
      (starRingEnd ℂ) (DGPS.FiniteN.TiltedXY.Fin051.phase y)).re) = κ * (1 - (xyMode (x - y)).re)
    rw [xyMode_sub, xyMode_apply, xyMode_apply]; rfl

/-- One-species family of the von Mises law at tilt `t`. -/
noncomputable def famFIN053 (t : ℝ) : SpeciesFamily 1 :=
  SpeciesFamily.single (vonMisesAbsoluteDensityEX021 t)

noncomputable def labFIN053 (t : ℝ) (N : ℕ+) : Fin N → Fin (famFIN053 t).count :=
  fun _ => firstSpecies (famFIN053 t)

theorem speciesLaw_famFIN053 (t : ℝ) (s : Fin (famFIN053 t).count) :
    speciesLaw (famFIN053 t) s = (xyLaw_EX023 t : Measure (Torus 1)) :=
  density_identity_EX025 t

theorem sum_offdiag_FIN053 (N : ℕ+) (c : ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else c) = N * (N - 1) * c := by
  have h1 : ∀ i : Fin N, ∑ j : Fin N, (if i = j then (0 : ℝ) else c) = ((N : ℝ) - 1) * c := by
    intro i
    rw [← Finset.sum_erase Finset.univ (f := fun j => if i = j then (0 : ℝ) else c) (a := i)
      (by simp)]
    rw [Finset.sum_congr rfl (g := fun _ => c) (fun j hj => by
      simp [(Finset.ne_of_mem_erase hj).symm])]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [Nat.cast_sub N.pos]
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp
  ring

theorem entropy_formula_FIN053 (κ h : ℝ) (N : ℕ+) (t : ℝ) :
    (relativeEntropy (productLaw (famFIN053 t) (labFIN053 t N))
        (particleLaw (attractiveXY κ h) N)).toReal =
      N * (t * besselRatio t - Real.log (besselI 0 t)) + N * (-h * besselRatio t) +
        (1 / (2 * (N : ℝ))) * (N * (N - 1) * (κ * (1 - besselRatio t ^ 2))) +
        Real.log (particlePartition (attractiveXY κ h) N) := by
  rw [relativeEntropy_productLaw_toReal]
  have hs : ∀ i, speciesEntropy (famFIN053 t) (labFIN053 t N i) =
      t * besselRatio t - Real.log (besselI 0 t) := fun i => by
    unfold speciesEntropy
    rw [speciesLaw_famFIN053]
    exact (law_entropy_EX023 t).2
  have hp : ∀ i, potentialEnergy (attractiveXY κ h) (speciesLaw (famFIN053 t) (labFIN053 t N i))
      = -h * besselRatio t := fun i => by
    rw [speciesLaw_famFIN053, potentialEnergy_attractiveXY]
    have := law_cos_EX023 t
    unfold xyZ1 at this
    rw [xyZ1, this]
  have hc : ∀ i j, crossEnergy (attractiveXY κ h) (speciesLaw (famFIN053 t) (labFIN053 t N i))
      (speciesLaw (famFIN053 t) (labFIN053 t N j)) = κ * (1 - besselRatio t ^ 2) := fun i j => by
    rw [speciesLaw_famFIN053, speciesLaw_famFIN053]
    have h1 := law_cos_EX023 t
    have h2 := law_sin_EX023 t
    show interactionEnergy (attractiveXY κ h) (xyLaw_EX023 t : Measure (Torus 1)) = _
    rw [interactionEnergy_attractiveXY, xyZ1, xyZ2]
    rw [xyZ1] at h1; rw [xyZ2] at h2
    rw [h1, h2]; ring
  simp only [hs, hp, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [sum_offdiag_FIN053]

/-! ### Scalar vectors in `Tangent 1` -/

/-- The constant vector `(c)` of the one-dimensional tangent space. -/
noncomputable def vec1FIN053 (c : ℝ) : Tangent 1 := WithLp.toLp 2 (fun _ => c)

theorem vec1_eq_FIN053 (c : ℝ) : vec1FIN053 c = c • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
  ext j; fin_cases j; simp [vec1FIN053]

theorem continuous_vec1_FIN053 : Continuous vec1FIN053 := by
  have : vec1FIN053 = fun c : ℝ => c • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :=
    funext vec1_eq_FIN053
  rw [this]; fun_prop

theorem norm_sq_vec1_FIN053 (c : ℝ) : ‖vec1FIN053 c‖ ^ 2 = c ^ 2 := by
  rw [vec1_eq_FIN053, norm_smul]; simp

theorem norm_vec1_FIN053 (c : ℝ) : ‖vec1FIN053 c‖ = |c| := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _), sq_abs]; exact norm_sq_vec1_FIN053 c

theorem smoothGrad_eq_vec1_FIN053 (φ : Torus 1 → ℝ) (x : Torus 1) :
    smoothGrad φ x = vec1FIN053 (coordPartial 0 φ x) := by
  ext j; fin_cases j; simp [vec1FIN053]

/-- The kernel `B(x,y) = ∇_x W(x,y)` of the XY model, as a scalar. -/
noncomputable def BFIN053 (κ : ℝ) (x y : Torus 1) : Tangent 1 :=
  vec1FIN053 (2 * Real.pi * κ * ((xyMode x).im * (xyMode y).re - (xyMode x).re * (xyMode y).im))

/-- The gradient of the field potential `V = -h cos`. -/
noncomputable def gVFIN053 (h : ℝ) (x : Torus 1) : Tangent 1 :=
  vec1FIN053 (2 * Real.pi * h * (xyMode x).im)

/-- The explicit self-score `2π c sin(2π x)`. -/
noncomputable def aFIN053 (c : ℝ) (x : Torus 1) : Tangent 1 :=
  vec1FIN053 (2 * Real.pi * c * (xyMode x).im)

theorem continuous_xyRe_FIN053 : Continuous fun x : Torus 1 => (xyMode x).re :=
  Complex.continuous_re.comp continuous_xyMode

theorem continuous_xyIm_FIN053 : Continuous fun x : Torus 1 => (xyMode x).im :=
  Complex.continuous_im.comp continuous_xyMode

theorem measurable_B_FIN053 (κ : ℝ) : Measurable (Function.uncurry (BFIN053 κ)) := by
  have hc : Continuous (Function.uncurry (BFIN053 κ)) := by
    unfold BFIN053 Function.uncurry
    refine continuous_vec1_FIN053.comp ?_
    have h1 : Continuous fun p : Torus 1 × Torus 1 => (xyMode p.1).re :=
      continuous_xyRe_FIN053.comp continuous_fst
    have h2 : Continuous fun p : Torus 1 × Torus 1 => (xyMode p.1).im :=
      continuous_xyIm_FIN053.comp continuous_fst
    have h3 : Continuous fun p : Torus 1 × Torus 1 => (xyMode p.2).re :=
      continuous_xyRe_FIN053.comp continuous_snd
    have h4 : Continuous fun p : Torus 1 × Torus 1 => (xyMode p.2).im :=
      continuous_xyIm_FIN053.comp continuous_snd
    exact continuous_const.mul ((h2.mul h3).sub (h1.mul h4))
  exact hc.measurable

theorem norm_B_le_FIN053 (κ : ℝ) (x y : Torus 1) : ‖BFIN053 κ x y‖ ≤ 4 * Real.pi * |κ| := by
  unfold BFIN053
  rw [norm_vec1_FIN053, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2),
    abs_of_pos Real.pi_pos]
  have hx1 := abs_xyMode_re_le x
  have hx2 := abs_xyMode_im_le x
  have hy1 := abs_xyMode_re_le y
  have hy2 := abs_xyMode_im_le y
  have : |(xyMode x).im * (xyMode y).re - (xyMode x).re * (xyMode y).im| ≤ 2 := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg (xyMode x).im, abs_nonneg (xyMode y).re, abs_nonneg (xyMode x).re,
      abs_nonneg (xyMode y).im]
  have hκ : 0 ≤ 2 * Real.pi * |κ| := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hκ]

theorem isWeakGradient_V_FIN053 (κ h : ℝ) :
    IsWeakGradient (attractiveXY κ h).V (gVFIN053 h) := by
  have e : (attractiveXY κ h).V = xyTrig (-h) 0 0 := by
    funext x; simp [attractiveXY_V, xyTrig]
  have e2 : gVFIN053 h = smoothGrad (xyTrig (-h) 0 0) := by
    funext x
    rw [smoothGrad_eq_vec1_FIN053, coordPartial_xyTrig]
    simp only [gVFIN053, xyTrig]
    congr 1; ring
  rw [e, e2]
  exact (isSmoothPeriodic_xyTrig _ _ _).isWeakGradient

theorem isWeakGradient_W_FIN053 (κ h : ℝ) (y : Torus 1) :
    IsWeakGradient (fun x => (attractiveXY κ h).W x y) (fun x => BFIN053 κ x y) := by
  have e : (fun x => (attractiveXY κ h).W x y) =
      xyTrig (-κ * (xyMode y).re) (-κ * (xyMode y).im) κ := by
    funext x
    simp only [attractiveXY_W, xyMode_re_sub, xyTrig]; ring
  have e2 : (fun x => BFIN053 κ x y) =
      smoothGrad (xyTrig (-κ * (xyMode y).re) (-κ * (xyMode y).im) κ) := by
    funext x
    rw [smoothGrad_eq_vec1_FIN053, coordPartial_xyTrig]
    simp only [BFIN053, xyTrig]
    congr 1; ring
  rw [e, e2]
  exact (isSmoothPeriodic_xyTrig _ _ _).isWeakGradient

theorem isParticleWeakGradient_FIN053 (κ h : ℝ) (N : ℕ+) :
    IsParticleWeakGradient (attractiveXY κ h) N (particleHamiltonian (attractiveXY κ h) N)
      (fun x i => gVFIN053 h (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
        BFIN053 κ (x i) (x j)) := by
  have hδ : IsWeakGradient (fun x => (attractiveXY κ h).W x x) (fun _ => (0 : Tangent 1)) := by
    have : (fun x => (attractiveXY κ h).W x x) = fun _ => (0 : ℝ) :=
      funext (attractiveXY κ h).W_diag
    rw [this]
    exact isWeakGradient_zero
  have hFc : Continuous (Function.uncurry (attractiveXY κ h).W) :=
    (attractiveXY κ h).W_continuous
  have := DGPS.Lipschitz.df_core (V := (attractiveXY κ h).V) (gV := gVFIN053 h)
    (gδ := fun _ => 0) (F := (attractiveXY κ h).W) (B := BFIN053 κ)
    (attractiveXY κ h).W_symm hFc (measurable_B_FIN053 κ) (norm_B_le_FIN053 κ)
    (isWeakGradient_W_FIN053 κ h) (isWeakGradient_V_FIN053 κ h) hδ N
  simp only [smul_zero, add_zero] at this
  exact (isParticleWeakGradient_iff (attractiveXY κ h) N _ _).2 this

theorem smul_vec1_FIN053 (c d : ℝ) : c • vec1FIN053 d = vec1FIN053 (c * d) := by
  ext j; simp [vec1FIN053]

theorem vec1_add_FIN053 (c d : ℝ) : vec1FIN053 c + vec1FIN053 d = vec1FIN053 (c + d) := by
  ext j; simp [vec1FIN053]

theorem vec1_sub_FIN053 (c d : ℝ) : vec1FIN053 c - vec1FIN053 d = vec1FIN053 (c - d) := by
  ext j; simp [vec1FIN053]

theorem vec1_sum_FIN053 {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∑ i ∈ s, vec1FIN053 (f i) = vec1FIN053 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext j; simp [vec1FIN053]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, vec1_add_FIN053]

theorem root_pos_FIN053 (t : ℝ) (x : Torus 1) : 0 < vonMisesRootEX021 t x := by
  unfold vonMisesRootEX021
  exact mul_pos (inv_pos.2 (Real.sqrt_pos.2 (besselI_zero_pos t))) (Real.exp_pos _)

theorem driftA_ae_FIN053 (t h : ℝ) (s : Fin (famFIN053 t).count) :
    ∀ᵐ x ∂speciesLaw (famFIN053 t) s,
      driftA (famFIN053 t) (gVFIN053 h) s x =
        aFIN053 (h - t) x := by
  have h1 : (famFIN053 t).sqrtGradient s =ᵐ[haar 1] smoothGrad (vonMisesRootEX021 t) :=
    IsWeakGradient.ae_eq ((famFIN053 t).isWeakGradient_sqrtGradient s)
      (vonMisesRoot_smoothEX021 t).isWeakGradient
  filter_upwards [(speciesLaw_ac (famFIN053 t) s).ae_le h1] with x hx
  unfold driftA
  rw [hx, smoothGrad_eq_vec1_FIN053, vonMisesRoot_coordPartialEX021, coordPartial_re_xyMode,
    smul_vec1_FIN053]
  unfold gVFIN053 aFIN053
  rw [vec1_add_FIN053]
  have hr : (vonMisesRootEX021 t x) ≠ 0 := (root_pos_FIN053 t x).ne'
  congr 1
  show 2 * (vonMisesRootEX021 t x)⁻¹ * (t / 2 * vonMisesRootEX021 t x * (-(2 * Real.pi) * (xyMode x).im))
    + 2 * Real.pi * h * (xyMode x).im = _
  field_simp
  ring

theorem integral_vec1_FIN053 {μ : Measure (Torus 1)} (f : Torus 1 → ℝ) :
    ∫ y, vec1FIN053 (f y) ∂μ = vec1FIN053 (∫ y, f y ∂μ) := by
  simp_rw [vec1_eq_FIN053]
  exact integral_smul_const _ _

theorem integrable_cont_law_FIN053 (t : ℝ) {φ : Torus 1 → ℝ} (hφ : Continuous φ) :
    Integrable φ (xyLaw_EX023 t : Measure (Torus 1)) :=
  integrable_cont_EX024 _ hφ

theorem poly_integral_FIN053 {t : ℝ} (ht : t ≠ 0) (P Q R S T U : ℝ) :
    ∫ y, (P * (xyMode y).re ^ 2 + Q * ((xyMode y).re * (xyMode y).im) + R * (xyMode y).im ^ 2
        + S * (xyMode y).re + T * (xyMode y).im + U) ∂(xyLaw_EX023 t : Measure (Torus 1)) =
      P * (1 - besselRatio t / t) + R * (besselRatio t / t) + S * besselRatio t + U := by
  have hxy : Continuous xyMode := continuous_xyMode
  have hre : Continuous fun y : Torus 1 => (xyMode y).re := continuous_xyRe_FIN053
  have him : Continuous fun y : Torus 1 => (xyMode y).im := continuous_xyIm_FIN053
  have i1 := integrable_cont_law_FIN053 t (φ := fun y : Torus 1 => (xyMode y).re ^ 2) (hre.pow 2)
  have i2 := integrable_cont_law_FIN053 t (φ := fun y : Torus 1 => (xyMode y).re * (xyMode y).im)
    (hre.mul him)
  have i3 := integrable_cont_law_FIN053 t (φ := fun y : Torus 1 => (xyMode y).im ^ 2) (him.pow 2)
  have i4 := integrable_cont_law_FIN053 t hre
  have i5 := integrable_cont_law_FIN053 t him
  have j1 : Integrable (fun y : Torus 1 => P * (xyMode y).re ^ 2 +
      Q * ((xyMode y).re * (xyMode y).im)) (xyLaw_EX023 t : Measure (Torus 1)) :=
    (i1.const_mul P).add (i2.const_mul Q)
  have j2 : Integrable (fun y : Torus 1 => P * (xyMode y).re ^ 2 +
      Q * ((xyMode y).re * (xyMode y).im) + R * (xyMode y).im ^ 2)
      (xyLaw_EX023 t : Measure (Torus 1)) := j1.add (i3.const_mul R)
  have j3 : Integrable (fun y : Torus 1 => P * (xyMode y).re ^ 2 +
      Q * ((xyMode y).re * (xyMode y).im) + R * (xyMode y).im ^ 2 + S * (xyMode y).re)
      (xyLaw_EX023 t : Measure (Torus 1)) := j2.add (i4.const_mul S)
  have j4 : Integrable (fun y : Torus 1 => P * (xyMode y).re ^ 2 +
      Q * ((xyMode y).re * (xyMode y).im) + R * (xyMode y).im ^ 2 + S * (xyMode y).re +
      T * (xyMode y).im) (xyLaw_EX023 t : Measure (Torus 1)) := j3.add (i5.const_mul T)
  rw [integral_add j4 (integrable_const U), integral_add j3 (i5.const_mul T),
    integral_add j2 (i4.const_mul S), integral_add j1 (i3.const_mul R),
    integral_add (i1.const_mul P) (i2.const_mul Q)]
  rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, law_cos_sq_EX024 ht, m_cs_EX024, m_ss_EX024 t ht, m_c_EX024, m_s_EX024]
  simp

theorem kernelMean_FIN053 (κ t : ℝ) (s : Fin (famFIN053 t).count) (x : Torus 1) :
    kernelMean (speciesLaw (famFIN053 t) s) (BFIN053 κ) x =
      vec1FIN053 (2 * Real.pi * κ * besselRatio t * (xyMode x).im) := by
  unfold kernelMean BFIN053
  rw [speciesLaw_famFIN053, integral_vec1_FIN053]
  congr 1
  have hre : Continuous fun y : Torus 1 => (xyMode y).re := continuous_xyRe_FIN053
  have him : Continuous fun y : Torus 1 => (xyMode y).im := continuous_xyIm_FIN053
  have h1 := integrable_cont_law_FIN053 t hre
  have h2 := integrable_cont_law_FIN053 t him
  rw [integral_const_mul, integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul,
    integral_const_mul, m_c_EX024, m_s_EX024]
  ring

theorem meanForce_FIN053 (κ h t : ℝ) (N : ℕ+) (i : Fin N) (x : Torus 1) :
    meanForce (speciesLaw (famFIN053 t)) (fun _ => aFIN053 (h - t)) (BFIN053 κ) (labFIN053 t N)
        (labFIN053 t N i) x =
      vec1FIN053 (2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t) *
        (xyMode x).im) := by
  rw [meanForce_eq]
  simp only [kernelMean_FIN053]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_vec1_FIN053, smul_vec1_FIN053]
  unfold aFIN053
  rw [vec1_add_FIN053]
  congr 1
  have hN : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 N.pos).ne'
  rw [Nat.cast_sub N.pos, Nat.cast_one]
  field_simp

theorem fluct_sq_FIN053 (κ t : ℝ) (N : ℕ+) (x : Torus 1) (j : Fin N) (y : Torus 1) :
    ‖fluct (speciesLaw (famFIN053 t)) (BFIN053 κ) (labFIN053 t N) x j y‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2 *
        ((xyMode x).im * ((xyMode y).re - besselRatio t) - (xyMode x).re * (xyMode y).im) ^ 2 := by
  unfold fluct
  rw [kernelMean_FIN053]
  unfold BFIN053
  rw [vec1_sub_FIN053, smul_vec1_FIN053, norm_sq_vec1_FIN053]
  ring

theorem condVar_FIN053 (κ h t : ℝ) (ht : t ≠ 0) (N : ℕ+) (i : Fin N) (x : Torus 1) :
    condVar (speciesLaw (famFIN053 t)) (fun _ => aFIN053 (h - t)) (BFIN053 κ) (labFIN053 t N) i x =
      ((N : ℝ) - 1) * ((((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
        ((xyMode x).im ^ 2 * (1 - besselRatio t / t - besselRatio t ^ 2) +
          (xyMode x).re ^ 2 * (besselRatio t / t))) := by
  have hM : (0 : ℝ) ≤ 4 * Real.pi * |κ| := by positivity
  rw [condVar_eq (speciesLaw (famFIN053 t)) (fun _ => aFIN053 (h - t)) (measurable_B_FIN053 κ)
    hM (norm_B_le_FIN053 κ) (labFIN053 t N) i x]
  simp only [fluct_sq_FIN053, speciesLaw_famFIN053]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub N.pos, Nat.cast_one]
  congr 1
  rw [integral_const_mul]
  congr 1
  have e : ∀ y : Torus 1, ((xyMode x).im * ((xyMode y).re - besselRatio t) -
      (xyMode x).re * (xyMode y).im) ^ 2 =
      (xyMode x).im ^ 2 * (xyMode y).re ^ 2 +
      (-2 * (xyMode x).im * (xyMode x).re) * ((xyMode y).re * (xyMode y).im) +
      (xyMode x).re ^ 2 * (xyMode y).im ^ 2 +
      (-2 * (xyMode x).im ^ 2 * besselRatio t) * (xyMode y).re +
      (2 * (xyMode x).im * (xyMode x).re * besselRatio t) * (xyMode y).im +
      (xyMode x).im ^ 2 * besselRatio t ^ 2 := fun y => by ring
  simp_rw [e]
  rw [poly_integral_FIN053 ht]
  ring

theorem continuous_aFIN_FIN053 (c : ℝ) : Continuous (aFIN053 c) :=
  continuous_vec1_FIN053.comp (continuous_const.mul continuous_xyIm_FIN053)

theorem norm_sq_aFIN_FIN053 (c : ℝ) (x : Torus 1) :
    ‖aFIN053 c x‖ ^ 2 = (2 * Real.pi * c * (xyMode x).im) ^ 2 := norm_sq_vec1_FIN053 _

theorem score_int_FIN053 (κ h t : ℝ) (ht : t ≠ 0) (N : ℕ+) (i : Fin N) :
    ∫ z, ‖score (fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) (BFIN053 κ)
        (labFIN053 t N) i z‖ ^ 2 ∂productLaw (famFIN053 t) (labFIN053 t N) =
      (2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t)) ^ 2 *
          (besselRatio t / t) +
        ((N : ℝ) - 1) * ((((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
          ((1 - besselRatio t / t - besselRatio t ^ 2) * (besselRatio t / t) +
            (1 - besselRatio t / t) * (besselRatio t / t))) := by
  have hM : (0 : ℝ) ≤ 4 * Real.pi * |κ| := by positivity
  have hasm : ∀ s : Fin (famFIN053 t).count, AEStronglyMeasurable
      ((fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) s) (speciesLaw (famFIN053 t) s) :=
    fun s => (continuous_aFIN_FIN053 _).aestronglyMeasurable
  have hai : ∀ s : Fin (famFIN053 t).count, Integrable
      (fun x => ‖(fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) s x‖ ^ 2)
      (speciesLaw (famFIN053 t) s) := fun s => by
    simp only [norm_sq_aFIN_FIN053]
    rw [speciesLaw_famFIN053]
    have hxy : Continuous xyMode := continuous_xyMode
    exact integrable_cont_law_FIN053 t (by fun_prop)
  have hh := integrable_score_sq (speciesLaw (famFIN053 t)) hasm hai (measurable_B_FIN053 κ) hM
    (norm_B_le_FIN053 κ) (labFIN053 t N) i
  unfold productLaw
  rw [integral_pi_update_split _ i hh]
  have hφeq : (fun x => ∫ z, ‖score (fun _ : Fin (famFIN053 t).count => aFIN053 (h - t))
      (BFIN053 κ) (labFIN053 t N) i (Function.update z i x)‖ ^ 2
        ∂(Measure.pi fun j => speciesLaw (famFIN053 t) (labFIN053 t N j))) =
      fun x => (2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t) *
          (xyMode x).im) ^ 2 +
        ((N : ℝ) - 1) * ((((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
          ((xyMode x).im ^ 2 * (1 - besselRatio t / t - besselRatio t ^ 2) +
            (xyMode x).re ^ 2 * (besselRatio t / t))) := by
    funext x
    rw [condSq_eq (speciesLaw (famFIN053 t)) (fun _ => aFIN053 (h - t)) (measurable_B_FIN053 κ)
      hM (norm_B_le_FIN053 κ) (labFIN053 t N) i x, meanForce_FIN053, norm_sq_vec1_FIN053,
      condVar_FIN053 κ h t ht]
  rw [hφeq]
  simp only [labFIN053, speciesLaw_famFIN053]
  have e : ∀ x : Torus 1, (2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t) *
          (xyMode x).im) ^ 2 +
        ((N : ℝ) - 1) * ((((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
          ((xyMode x).im ^ 2 * (1 - besselRatio t / t - besselRatio t ^ 2) +
            (xyMode x).re ^ 2 * (besselRatio t / t))) =
      (((N : ℝ) - 1) * (((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) * (besselRatio t / t)) *
        (xyMode x).re ^ 2 + 0 * ((xyMode x).re * (xyMode x).im) +
      ((2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t)) ^ 2 +
        ((N : ℝ) - 1) * (((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
          (1 - besselRatio t / t - besselRatio t ^ 2)) * (xyMode x).im ^ 2 +
      0 * (xyMode x).re + 0 * (xyMode x).im + 0 := fun x => by ring
  simp_rw [e]
  rw [poly_integral_FIN053 ht]
  ring

theorem fisher_score_FIN053 (κ h t : ℝ) (ht : t ≠ 0) (N : ℕ+) :
    particleRelativeFisher (attractiveXY κ h) N (productLaw (famFIN053 t) (labFIN053 t N)) =
      ENNReal.ofReal ((N : ℝ) *
        ((2 * Real.pi * ((h - t) + ((N : ℝ) - 1) / N * κ * besselRatio t)) ^ 2 *
            (besselRatio t / t) +
          ((N : ℝ) - 1) * ((((N : ℝ)⁻¹) ^ 2 * (2 * Real.pi * κ) ^ 2) *
            ((1 - besselRatio t / t - besselRatio t ^ 2) * (besselRatio t / t) +
              (1 - besselRatio t / t) * (besselRatio t / t))))) := by
  have hM : (0 : ℝ) ≤ 4 * Real.pi * |κ| := by positivity
  have hasm' : ∀ s : Fin (famFIN053 t).count, AEStronglyMeasurable
      ((fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) s) (speciesLaw (famFIN053 t) s) :=
    fun s => (continuous_aFIN_FIN053 _).aestronglyMeasurable
  have hai' : ∀ s : Fin (famFIN053 t).count, Integrable
      (fun x => ‖(fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) s x‖ ^ 2)
      (speciesLaw (famFIN053 t) s) := fun s => by
    simp only [norm_sq_aFIN_FIN053]
    rw [speciesLaw_famFIN053]
    have hxy : Continuous xyMode := continuous_xyMode
    exact integrable_cont_law_FIN053 t (by fun_prop)
  have hasm : ∀ s : Fin (famFIN053 t).count, AEStronglyMeasurable
      (driftA (famFIN053 t) (gVFIN053 h) s) (speciesLaw (famFIN053 t) s) := fun s =>
    (hasm' s).congr ((driftA_ae_FIN053 t h s).mono fun x hx => hx.symm)
  have hai : ∀ s : Fin (famFIN053 t).count, Integrable
      (fun x => ‖driftA (famFIN053 t) (gVFIN053 h) s x‖ ^ 2) (speciesLaw (famFIN053 t) s) :=
    fun s => (hai' s).congr (by
      filter_upwards [driftA_ae_FIN053 t h s] with x hx
      rw [hx])
  rw [relativeFisher_eq_score (attractiveXY κ h) (lipschitzData_attractiveXY κ h) (famFIN053 t)
    (measurable_B_FIN053 κ) hM (norm_B_le_FIN053 κ) (isWeakGradient_V_FIN053 κ h) hasm hai
    (labFIN053 t N) (isParticleWeakGradient_FIN053 κ h N)]
  congr 1
  have hae : ∀ᵐ z ∂productLaw (famFIN053 t) (labFIN053 t N),
      ∀ i, driftA (famFIN053 t) (gVFIN053 h) (labFIN053 t N i) (z i) = aFIN053 (h - t) (z i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun j => speciesLaw (famFIN053 t) (labFIN053 t N j))
      i).quasiMeasurePreserving.ae (driftA_ae_FIN053 t h (labFIN053 t N i))
  have h1 : ∫ z, ∑ i, ‖score (driftA (famFIN053 t) (gVFIN053 h)) (BFIN053 κ) (labFIN053 t N) i z‖ ^ 2
      ∂productLaw (famFIN053 t) (labFIN053 t N) =
      ∫ z, ∑ i, ‖score (fun _ : Fin (famFIN053 t).count => aFIN053 (h - t)) (BFIN053 κ)
        (labFIN053 t N) i z‖ ^ 2 ∂productLaw (famFIN053 t) (labFIN053 t N) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold score
    rw [hz i]
  rw [h1]
  unfold productLaw
  rw [integral_finsetSum _ fun i _ => integrable_score_sq (speciesLaw (famFIN053 t)) hasm' hai'
    (measurable_B_FIN053 κ) hM (norm_B_le_FIN053 κ) (labFIN053 t N) i]
  have h2 := score_int_FIN053 κ h t ht N
  unfold productLaw at h2
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem alg_FIN053 (N g d s : ℝ) (hN : 0 < N) (h4 : 4 * g = s + 1 / 2) :
    N * ((2 * Real.pi * ((1 / 2 - -s) + (N - 1) / N * 4 * -g)) ^ 2 * d +
      (N - 1) * (((N⁻¹) ^ 2 * (2 * Real.pi * 4) ^ 2) *
        ((1 - d - (-g) ^ 2) * d + (1 - d) * d))) =
      4 * Real.pi ^ 2 * 4 ^ 2 * d * ((-g) ^ 2 / N + (N - 1) * ((1 - d - g ^ 2) + 1 - d) / N) := by
  have hs : s = 4 * g - 1 / 2 := by linarith
  subst hs
  field_simp
  ring

theorem fisher_neg_FIN053 (N : ℕ+) {s : ℝ} (hs0 : 0 < s) (hroot : 4 * besselRatio s - s = 1 / 2) :
    particleRelativeFisher (attractiveXY 4 (1 / 2)) N
        (productLaw (famFIN053 (-s)) (labFIN053 (-s) N)) =
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) *
        ((-besselRatio s) ^ 2 / N +
          ((N : ℝ) - 1) * (deriv besselRatio s + 1 - besselRatio s / s) / N)) := by
  rw [fisher_score_FIN053 4 (1 / 2) (-s) (neg_ne_zero.2 hs0.ne') N, besselRatio_neg,
    neg_div_neg_eq]
  congr 1
  have hv : deriv besselRatio s = 1 - besselRatio s / s - besselRatio s ^ 2 := by
    rw [DGPS.Circle.BesselConcavity.deriv_ratio]; exact ratioDeriv_eq_EX024 hs0.ne'
  rw [hv]
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have := alg_FIN053 (N : ℝ) (besselRatio s) (besselRatio s / s) s hN (by linarith)
  rw [← this]

theorem fisher_bound_FIN053 (N : ℕ+) {s : ℝ} (hs0 : 0 < s) (hroot : 4 * besselRatio s - s = 1 / 2) :
    4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) *
        ((-besselRatio s) ^ 2 / N +
          ((N : ℝ) - 1) * (deriv besselRatio s + 1 - besselRatio s / s) / N) ≤
      4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) := by
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
  have hg0 := DGPS.Circle.BesselMonotonicity.besselRatio_pos s hs0
  have hg1 := DGPS.Circle.BesselMonotonicity.besselRatio_lt_one s
  have hv := DGPS.Circle.BesselConcavity.ratioDeriv_lt_div s hs0
  rw [DGPS.Circle.BesselConcavity.deriv_ratio]
  have hd : 0 < besselRatio s / s := div_pos hg0 hs0
  have hpos : 0 < 4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) := by positivity
  have hkey : (-besselRatio s) ^ 2 / N +
      ((N : ℝ) - 1) * (DGPS.Circle.BesselConcavity.ratioDeriv s + 1 - besselRatio s / s) / N ≤ 1 := by
    rw [← add_div, div_le_one (by linarith)]
    have h1 : (-besselRatio s) ^ 2 < 1 := by nlinarith
    have h2 : ((N : ℝ) - 1) * (DGPS.Circle.BesselConcavity.ratioDeriv s + 1 - besselRatio s / s) ≤ ((N : ℝ) - 1) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  nlinarith

theorem entropy_lower_FIN053 (N : ℕ+) {s : ℝ} :
    ENNReal.ofReal (2 * (1 / 2) * N * besselRatio s) ≤
      relativeEntropy (productLaw (famFIN053 (-s)) (labFIN053 (-s) N))
        (particleLaw (attractiveXY 4 (1 / 2)) N) := by
  apply ENNReal.ofReal_le_of_le_toReal
  have h1 := entropy_formula_FIN053 4 (1 / 2) N (-s)
  have h2 := entropy_formula_FIN053 4 (1 / 2) N s
  have h3 : 0 ≤ (relativeEntropy (productLaw (famFIN053 s) (labFIN053 s N))
      (particleLaw (attractiveXY 4 (1 / 2)) N)).toReal := ENNReal.toReal_nonneg
  rw [h2] at h3
  rw [h1, besselRatio_neg]
  have h0 : besselI 0 (-s) = besselI 0 s := by rw [besselI_neg]; simp
  rw [h0]
  nlinarith

theorem productLaw_eq_pi_FIN053 (t : ℝ) (N : ℕ+) :
    productLaw (famFIN053 t) (labFIN053 t N) =
      Measure.pi fun _ : Fin N => (xyLaw_EX023 t : Measure (Torus 1)) := by
  unfold productLaw
  simp only [speciesLaw_famFIN053]

theorem likelihood_root_FIN053 (κ h t : ℝ) (N : ℕ+) :
    ∃ f : ParticleH1 (attractiveXY κ h) N,
      IsLikelihoodRoot (attractiveXY κ h) N (productLaw (famFIN053 t) (labFIN053 t N)) f ∧
        IsSymmetricParticleTest f := by
  have hLip := lipschitzData_attractiveXY κ h
  have hgV := isWeakGradient_V_FIN053 κ h
  have hM : (0 : ℝ) ≤ 4 * Real.pi * |κ| := by positivity
  have hU := (isParticleWeakGradient_iff (attractiveXY κ h) N _ _).1
    (isParticleWeakGradient_FIN053 κ h N)
  obtain ⟨C, hC⟩ := ae_bound_gV hLip hgV
  have hall : ∀ᵐ x ∂particleHaar 1 N, ∀ i, ‖gVFIN053 h (x i)‖ ≤ C := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => haar 1) i).quasiMeasurePreserving.ae hC
  have hb : ∃ C' : ℝ, ∀ᵐ x : ParticleSpace 1 N ∂particleHaar 1 N, particleTangentNormSq
      ((fun x i => gVFIN053 h (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
        BFIN053 κ (x i) (x j)) x) ≤ C' := by
    refine ⟨N * (C + 4 * Real.pi * |κ|) ^ 2, ?_⟩
    filter_upwards [hall] with x hx
    unfold particleTangentNormSq
    calc ∑ i, ‖gVFIN053 h (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, BFIN053 κ (x i) (x j)‖ ^ 2
        ≤ ∑ _i : Fin N, (C + 4 * Real.pi * |κ|) ^ 2 := Finset.sum_le_sum fun i _ => by
          have h' := norm_score_le (a := fun _ : Fin 1 => gVFIN053 h) hM
            (norm_B_le_FIN053 κ) (fun _ => (0 : Fin 1)) i x
          exact pow_le_pow_left₀ (norm_nonneg _) (h'.trans (add_le_add_left (hx i) _)) 2
      _ = N * (C + 4 * Real.pi * |κ|) ^ 2 := by simp
  obtain ⟨f, hfroot, hfL⟩ := exists_likelihoodRoot (attractiveXY κ h) (famFIN053 t)
    (labFIN053 t N) hU hb
  exact ⟨f, hfL, isSymmetric_root _ _ rfl _ f hfroot⟩

end DGPS.FiniteN.TiltedXYProductFIN053

namespace DGPS.FiniteN

open MeasureTheory
open scoped ENNReal
open DGPS DGPS.Models DGPS.Examples.AttractiveXYTilt DGPS.Circle.BesselMoments
  DGPS.FiniteN.TiltedXYProductFIN053 DGPS.Particle.ProductForceFisher DGPS.Lipschitz
  DGPS.Particle.ProductRecovery

/-- **FIN053.**  At `κ = 4`, `h = 1/2`, let `s ∈ (1,4)` be a root of `4 g(s) - s = 1/2`
(`g = besselRatio`) and `Q = (q_{-s})^{⊗N}` the product of the negative tilted laws.  Then
`I(Q|P_N) = a₀ κ² d [b²/N + (N-1)(v+1-d)/N] ≤ a₀ κ² d` with `a₀ = 4π²`, `b = -g(s)`, `d = g(s)/s`,
`v = g'(s)`; `H(Q|P_N) ≥ 2 h N g(s)`; and the smooth symmetric likelihood root `√(dQ/dP_N)`
gives `r_N^sym ≤ a₀ κ² / (4 h s N) ≤ 8 a₀ / N`. -/
theorem tilted_exact_stationary_product_upper_test (N : ℕ+) {s : ℝ} (hs1 : 1 < s) (_hs4 : s < 4)
    (hroot : 4 * besselRatio s - s = 1 / 2) :
    particleRelativeFisher (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N
        (Measure.pi fun _ : Fin N => (xyLaw_EX023 (-s) : Measure (Torus 1))) =
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) *
        ((-besselRatio s) ^ 2 / N +
          ((N : ℝ) - 1) * (deriv besselRatio s + 1 - besselRatio s / s) / N)) ∧
    particleRelativeFisher (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N
        (Measure.pi fun _ : Fin N => (xyLaw_EX023 (-s) : Measure (Torus 1))) ≤
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s)) ∧
    ENNReal.ofReal (2 * (1 / 2) * N * besselRatio s) ≤
      relativeEntropy (Measure.pi fun _ : Fin N => (xyLaw_EX023 (-s) : Measure (Torus 1)))
        (particleLaw (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N) ∧
    ∃ f : ParticleH1 (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N,
      IsLikelihoodRoot (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N
        (Measure.pi fun _ : Fin N => (xyLaw_EX023 (-s) : Measure (Torus 1))) f ∧
      IsSymmetricParticleTest f ∧
      particleQuotient (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N f ≤
        ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N)) ∧
      particleRateSym (TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≤
        ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N)) ∧
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N)) ≤
        ENNReal.ofReal (8 * (4 * Real.pi ^ 2) / N) := by
  rw [tiltedXYData_eq_attractiveXY_FIN053 (1 / 2) 4, ← productLaw_eq_pi_FIN053 (-s) N]
  have hs0 : 0 < s := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hg0 := DGPS.Circle.BesselMonotonicity.besselRatio_pos s hs0
  have hF := fisher_neg_FIN053 N hs0 hroot
  have hB := fisher_bound_FIN053 N hs0 hroot
  have hH := entropy_lower_FIN053 N (s := s)
  have hFle : particleRelativeFisher (attractiveXY 4 (1 / 2)) N
      (productLaw (famFIN053 (-s)) (labFIN053 (-s) N)) ≤
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s)) := by
    rw [hF]; exact ENNReal.ofReal_le_ofReal hB
  refine ⟨hF, hFle, hH, ?_⟩
  obtain ⟨f, hL, hsym⟩ := likelihood_root_FIN053 4 (1 / 2) (-s) N
  have hE := hL.2.2.2.1
  have hEnt := hL.2.2.2.2
  refine ⟨f, hL, hsym, ?_⟩
  have hX : (particleRelativeFisher (attractiveXY 4 (1 / 2)) N
      (productLaw (famFIN053 (-s)) (labFIN053 (-s) N))).toReal ≤
      4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFle
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hX0 := ENNReal.toReal_nonneg (a := particleRelativeFisher (attractiveXY 4 (1 / 2)) N
      (productLaw (famFIN053 (-s)) (labFIN053 (-s) N)))
  have h2E : 2 * particleEnergy (attractiveXY 4 (1 / 2)) N f ≤
      4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) / 2 := by linarith
  have hpos : (0 : ℝ) < 2 * (1 / 2) * N * besselRatio s := by positivity
  have hQ : particleQuotient (attractiveXY 4 (1 / 2)) N f ≤
      ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N)) := by
    unfold particleQuotient
    rw [hEnt]
    calc ENNReal.ofReal (2 * particleEnergy (attractiveXY 4 (1 / 2)) N f) /
          relativeEntropy (productLaw (famFIN053 (-s)) (labFIN053 (-s) N))
            (particleLaw (attractiveXY 4 (1 / 2)) N)
        ≤ ENNReal.ofReal (2 * particleEnergy (attractiveXY 4 (1 / 2)) N f) /
          ENNReal.ofReal (2 * (1 / 2) * N * besselRatio s) :=
          ENNReal.div_le_div_left hH _
      _ = ENNReal.ofReal (2 * particleEnergy (attractiveXY 4 (1 / 2)) N f /
          (2 * (1 / 2) * N * besselRatio s)) := (ENNReal.ofReal_div_of_pos hpos).symm
      _ ≤ ENNReal.ofReal (4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hpos]
          have e : 4 * Real.pi ^ 2 * 4 ^ 2 / (4 * (1 / 2) * s * N) *
              (2 * (1 / 2) * N * besselRatio s) =
              4 * Real.pi ^ 2 * 4 ^ 2 * (besselRatio s / s) / 2 := by
            field_simp
            norm_num
          rw [e]; exact h2E
  refine ⟨hQ, ?_, ?_⟩
  · have hnn : 0 < relativeEntropy (productLaw (famFIN053 (-s)) (labFIN053 (-s) N))
        (particleLaw (attractiveXY 4 (1 / 2)) N) :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos) hH
    exact (particleRateSym_le_quotient _ N f hsym (by rw [hEnt]; exact hnn)).trans hQ
  · apply ENNReal.ofReal_le_ofReal
    have hpi : 0 < Real.pi ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hN]
    nlinarith [mul_pos hpi hN, mul_pos (mul_pos hpi hN) (sub_pos.2 hs1)]

end DGPS.FiniteN
