import DGPS.FiniteN.SecondHarmonicRates
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.FiniteN.Tools.UnitTorusNormalization

/-!
# Exact symmetric harmonic covariance trial (FIN090)

For `F_N(x) = ∑ᵢ cos 2π xᵢ` on the unit-period `N`-particle torus and the second-harmonic Gibbs
law `P_N`: `F_N` is smooth, permutation symmetric and centered, `Var_{P_N}(F_N) = N/2`
and `E_N(F_N) = a₀ N / 2` (Dirichlet energy without a factor `1/N`, `a₀ = 4π²`), so the exact
Poincare quotient of `F_N` is `a₀`, for every `N ≥ 1`.  Inputs: FIN089 (tagged Haar marginals and
vanishing cross moments) and FIN002 (`a₀ = 4π²`).
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal ContDiff

namespace DGPS.FiniteN

/-- The trial function `F_N(x) = ∑ᵢ cos 2π xᵢ`. -/
noncomputable def harmonicTrial (N : ℕ+) : DGPS.ParticleSpace 1 N → ℝ :=
  fun x => ∑ i, (mode 1 (x i)).re

theorem harmonicTrial_lift (N : ℕ+) (y : Fin N → Fin 1 → ℝ) :
    harmonicTrial N (DGPS.particleLift y) = ∑ k, Real.cos (2 * Real.pi * y k 0) := by
  unfold harmonicTrial
  refine Finset.sum_congr rfl fun k _ => ?_
  have : DGPS.particleLift y k = DGPS.torusLift (y k) := rfl
  rw [this, mode_lift]
  have h : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (y k 0 : ℂ)) = ((2 * Real.pi * y k 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

theorem harmonicTrial_eq_witness (N : ℕ+) :
    harmonicTrial N = DGPS.FiniteN.PositiveRate.witnessSum N Nat.one_pos := by
  funext x
  unfold harmonicTrial DGPS.FiniteN.PositiveRate.witnessSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mode_apply]; rfl

theorem isSmooth_harmonicTrial (N : ℕ+) : DGPS.IsSmoothPeriodicParticle (harmonicTrial N) := by
  rw [harmonicTrial_eq_witness]; exact DGPS.FiniteN.PositiveRate.isSmooth_witnessSum _

theorem particlePartial_harmonicTrial (N : ℕ+) (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (harmonicTrial N) x = -(2 * Real.pi) * (mode 1 (x i)).im := by
  have hs := isSmooth_harmonicTrial N
  set y0 : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k) with hy0
  set v : Fin N → Fin 1 → ℝ := Pi.single i (Pi.single 0 (1 : ℝ)) with hv
  have hD : DifferentiableAt ℝ (harmonicTrial N ∘ DGPS.particleLift) y0 :=
    (hs.differentiable (by simp)) _
  have hline : HasDerivAt (fun t : ℝ => y0 + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y0
  have hD' : HasFDerivAt (harmonicTrial N ∘ DGPS.particleLift)
      (fderiv ℝ (harmonicTrial N ∘ DGPS.particleLift) y0) (y0 + (0:ℝ) • v) := by
    simpa using hD.hasFDerivAt
  have h1 := hD'.comp_hasDerivAt (0:ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => (harmonicTrial N ∘ DGPS.particleLift) (y0 + t • v))
      (-(2 * Real.pi) * Real.sin (2 * Real.pi * y0 i 0)) 0 := by
    have : (fun t : ℝ => (harmonicTrial N ∘ DGPS.particleLift) (y0 + t • v)) =
        fun t => ∑ k, Real.cos (2 * Real.pi * (y0 + t • v) k 0) := by
      funext t; simp only [Function.comp_apply]; exact harmonicTrial_lift N _
    rw [this]
    have hk : ∀ k ∈ (Finset.univ : Finset (Fin N)), HasDerivAt
        (fun t : ℝ => Real.cos (2 * Real.pi * (y0 + t • v) k 0))
        (if k = i then -(2 * Real.pi) * Real.sin (2 * Real.pi * y0 i 0) else 0) 0 := by
      intro k _
      by_cases hk : k = i
      · subst hk
        have hin : HasDerivAt (fun t : ℝ => 2 * Real.pi * (y0 + t • v) k 0) (2 * Real.pi) 0 := by
          have : (fun t : ℝ => 2 * Real.pi * (y0 + t • v) k 0) = fun t => 2 * Real.pi * (y0 k 0 + t) := by
            funext t; simp [hv]
          rw [this]
          simpa using ((hasDerivAt_id (0:ℝ)).const_add (y0 k 0)).const_mul (2 * Real.pi)
        have := (Real.hasDerivAt_cos _).comp (0:ℝ) hin
        simp only [ite_true]
        convert this using 1
        · funext t; simp
        · simp [hv]; ring
      · have : (fun t : ℝ => Real.cos (2 * Real.pi * (y0 + t • v) k 0)) = fun _ => Real.cos (2 * Real.pi * y0 k 0) := by
          funext t; simp [hv, hk]
        rw [this]; simpa only [hk, ↓reduceIte] using hasDerivAt_const _ _
    have := HasDerivAt.fun_sum hk
    simpa using this
  have h3 := h1.unique h2
  have him : (mode 1 (x i)).im = Real.sin (2 * Real.pi * y0 i 0) := by
    have hx : x i = DGPS.torusLift (y0 i) := by
      simp [hy0, DGPS.torusLift, SharpLSI.liftT_secT]
    rw [hx, mode_lift]
    have h : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (y0 i 0 : ℂ)) = ((2 * Real.pi * y0 i 0 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h, Complex.exp_ofReal_mul_I_im]
  rw [him]
  unfold DGPS.particlePartial
  exact h3

theorem continuous_harmonicTrial (N : ℕ+) : Continuous (harmonicTrial N) := by
  rw [harmonicTrial_eq_witness]; exact DGPS.FiniteN.PositiveRate.continuous_witnessSum _

theorem re_mode_one_sq (x : DGPS.Torus 1) :
    (mode 1 x).re ^ 2 = (1 + (mode 2 x).re) / 2 := by
  have h1 := normSq_mode 1 x
  have h2 : mode 2 x = mode 1 x * mode 1 x := by rw [mode_mul]; norm_num
  rw [h2, Complex.mul_re]
  rw [Complex.normSq_apply] at h1
  nlinarith

theorem im_mode_one_sq (x : DGPS.Torus 1) :
    (mode 1 x).im ^ 2 = (1 - (mode 2 x).re) / 2 := by
  have h1 := normSq_mode 1 x
  have h2 : mode 2 x = mode 1 x * mode 1 x := by rw [mode_mul]; norm_num
  rw [h2, Complex.mul_re]
  rw [Complex.normSq_apply] at h1
  nlinarith

theorem integral_re_mode_haar {k : ℤ} (hk : k ≠ 0) : ∫ x, (mode k x).re ∂DGPS.haar 1 = 0 := by
  have := integral_re (integrable_mode k) (𝕜 := ℂ)
  simp only [RCLike.re_to_complex] at this
  rw [this, integral_mode_haar hk]; simp

theorem integral_re_mode_one_sq : ∫ x, (mode 1 x).re ^ 2 ∂DGPS.haar 1 = 1 / 2 := by
  simp_rw [re_mode_one_sq]
  have hi : Integrable (fun x => (mode 2 x).re) (DGPS.haar 1) :=
    (integrable_mode 2).re
  rw [integral_div, integral_add (integrable_const _) hi, integral_re_mode_haar (by norm_num)]
  simp

theorem integral_im_mode_one_sq : ∫ x, (mode 1 x).im ^ 2 ∂DGPS.haar 1 = 1 / 2 := by
  simp_rw [im_mode_one_sq]
  have hi : Integrable (fun x => (mode 2 x).re) (DGPS.haar 1) :=
    (integrable_mode 2).re
  rw [integral_div, integral_sub (integrable_const _) hi, integral_re_mode_haar (by norm_num)]
  simp

/-- **FIN090.** For every `N ≥ 1` the trial `F_N = ∑ᵢ cos 2π xᵢ` is an `H¹(P_N)` test, smooth,
permutation symmetric (pointwise and in the `IsSymmetricParticleTest` sense), centered, with
`Var_{P_N}(F_N) = N/2 > 0`, `E_N(F_N) = a₀ N/2` and Poincare quotient exactly `a₀`. -/
theorem exact_symmetric_harmonic_covariance_trial (κ : ℝ) (N : ℕ+) :
    ∃ f : DGPS.ParticleH1 (secondHarmonicData κ) N,
      f.1 = (fun x : DGPS.ParticleSpace 1 N => ∑ i, (mode 1 (x i)).re) ∧
      DGPS.IsSmoothPeriodicParticle f.1 ∧
      (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
        f.1 (DGPS.permuteParticles σ x) = f.1 x) ∧
      DGPS.IsSymmetricParticleTest f ∧
      ∫ x, f.1 x ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
      ProbabilityTheory.variance f.1 (DGPS.particleLaw (secondHarmonicData κ) N) = (N : ℝ) / 2 ∧
      0 < ProbabilityTheory.variance f.1 (DGPS.particleLaw (secondHarmonicData κ) N) ∧
      DGPS.particleEnergy (secondHarmonicData κ) N f =
        DGPS.Circle.AngularNormalization.a0 * (N : ℝ) / 2 ∧
      DGPS.particlePoincareQuotient (secondHarmonicData κ) N f =
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 := by
  set A := secondHarmonicData κ with hA
  set P := DGPS.particleLaw A N with hP
  have hPprob : IsProbabilityMeasure P := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  obtain ⟨-, -, -, -, -, -, -, hmarg, hcross⟩ := second_harmonic_particle_symmetries κ N
  have ha0 : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 :=
    (angular_to_unit_torus_normalization).1
  -- marginal integrals
  have hI : ∀ (i : Fin N) (g : DGPS.Torus 1 → ℝ), Continuous g →
      ∫ x, g (x i) ∂P = ∫ y, g y ∂DGPS.haar 1 := by
    intro i g hg
    rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]
  have hint : ∀ {h : DGPS.ParticleSpace 1 N → ℝ}, Continuous h → Integrable h P := fun hc =>
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcont : ∀ i : Fin N, Continuous (fun x : DGPS.ParticleSpace 1 N => (mode 1 (x i)).re) :=
    fun i => Complex.continuous_re.comp ((continuous_mode 1).comp (continuous_apply i))
  have hcontim : ∀ i : Fin N, Continuous (fun x : DGPS.ParticleSpace 1 N => (mode 1 (x i)).im) :=
    fun i => Complex.continuous_im.comp ((continuous_mode 1).comp (continuous_apply i))
  -- membership in H¹
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth (isSmooth_harmonicTrial N)
  have hGP : DGPS.IsParticleWeakGradient A N (harmonicTrial N)
      (fun x i => WithLp.toLp 2 fun j => DGPS.particlePartial i j (harmonicTrial N) x) :=
    (DGPS.isParticleWeakGradient_iff A N _ _).2 hG
  have hmem : DGPS.MemParticleH1 A N (harmonicTrial N) := ⟨_, hGP⟩
  set f : DGPS.ParticleH1 A N := ⟨harmonicTrial N, hmem⟩ with hf
  have hfv : f.1 = harmonicTrial N := rfl
  -- mean
  have hmean : ∫ x, harmonicTrial N x ∂P = 0 := by
    unfold harmonicTrial
    rw [integral_finsetSum _ (fun i _ => hint (hcont i))]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hI i (fun y => (mode 1 y).re) (Complex.continuous_re.comp (continuous_mode 1))]
    exact integral_re_mode_haar (by norm_num)
  -- second moment
  have hsq : ∫ x, (harmonicTrial N x) ^ 2 ∂P = (N : ℝ) / 2 := by
    have e : ∀ x, (harmonicTrial N x) ^ 2 = ∑ i, ∑ j, (mode 1 (x i)).re * (mode 1 (x j)).re := by
      intro x; unfold harmonicTrial; rw [sq, Finset.sum_mul_sum]
    have hij : ∀ i j : Fin N, Integrable (fun x : DGPS.ParticleSpace 1 N =>
        (mode 1 (x i)).re * (mode 1 (x j)).re) P := fun i j => hint ((hcont i).mul (hcont j))
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hij i j)]
    have hrow : ∀ i : Fin N, ∫ x, ∑ j, (mode 1 (x i)).re * (mode 1 (x j)).re ∂P = 1 / 2 := by
      intro i
      rw [integral_finsetSum _ (fun j _ => hij i j)]
      rw [Finset.sum_eq_single i]
      · have := hI i (fun y => (mode 1 y).re ^ 2)
          ((Complex.continuous_re.comp (continuous_mode 1)).pow 2)
        simp only [← sq] at this ⊢
        rw [this, integral_re_mode_one_sq]
      · intro j _ hj
        exact (hcross i j (Ne.symm hj)).1
      · simp
    simp_rw [hrow]
    simp [div_eq_mul_inv, mul_comm]
  have hvar : ProbabilityTheory.variance (harmonicTrial N) P = (N : ℝ) / 2 := by
    rw [ProbabilityTheory.variance_eq_integral (continuous_harmonicTrial N).aemeasurable]
    simp only [hmean, sub_zero]
    exact hsq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  -- energy
  have hen : DGPS.particleEnergy A N f = DGPS.Circle.AngularNormalization.a0 * (N : ℝ) / 2 := by
    rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient f hGP, ha0]
    simp only [DGPS.particleTangentNormSq_eq]
    have e : ∀ x : DGPS.ParticleSpace 1 N,
        ∑ i, ∑ j : Fin 1, (WithLp.toLp 2 (fun j => DGPS.particlePartial i j (harmonicTrial N) x) :
          DGPS.Tangent 1) j ^ 2 = ∑ i, (4 * Real.pi ^ 2) * (mode 1 (x i)).im ^ 2 := by
      intro x
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.sum_univ_one]
      rw [particlePartial_harmonicTrial]; ring
    simp_rw [e]
    have hij2 : ∀ i : Fin N, Integrable (fun x : DGPS.ParticleSpace 1 N =>
        (4 * Real.pi ^ 2) * (mode 1 (x i)).im ^ 2) P := fun i =>
      hint (continuous_const.mul ((hcontim i).pow 2))
    rw [← hP, integral_finsetSum _ (fun i _ => hij2 i)]
    have hrow : ∀ i : Fin N, ∫ x, (4 * Real.pi ^ 2) * (mode 1 (x i)).im ^ 2 ∂P =
        (4 * Real.pi ^ 2) * (1 / 2) := by
      intro i
      rw [integral_const_mul]
      have := hI i (fun y => (mode 1 y).im ^ 2)
        ((Complex.continuous_im.comp (continuous_mode 1)).pow 2)
      rw [this, integral_im_mode_one_sq]
    simp_rw [hrow]
    simp; ring
  refine ⟨f, rfl, isSmooth_harmonicTrial N, ?_, ?_, hmean, hvar, by rw [hvar]; positivity, hen, ?_⟩
  · intro σ x
    show harmonicTrial N _ = harmonicTrial N x
    rw [harmonicTrial_eq_witness, DGPS.FiniteN.PositiveRate.witnessSum_permute]
  · rw [DGPS.isSymmetricParticleTest_iff f]
    intro σ
    refine Filter.Eventually.of_forall fun x => ?_
    show harmonicTrial N _ = harmonicTrial N x
    rw [harmonicTrial_eq_witness, DGPS.FiniteN.PositiveRate.witnessSum_permute]
  · unfold DGPS.particlePoincareQuotient
    rw [hen, hfv, hvar, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp

end DGPS.FiniteN
