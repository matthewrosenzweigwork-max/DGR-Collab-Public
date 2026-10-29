import DGPS.FiniteN.Tools.PositiveRate
import DGPS.FiniteN.Tools.BoundedComparison
import DGPS.Circle.AngularNormalization
import DGPS.Analysis.CircleMoments

/-!
# Tilted tagged upper Poincare bound (FIN051)

On `𝕋^1 = Torus 1` consider the tilted attractive cosine model
`V_h(x) = -h cos(2π x)`, `W_κ(x,y) = κ (1 - cos(2π (x - y)))` (`tiltedXYData h κ`).
For the finite-`N` Gibbs law, moving a single (tagged) coordinate changes the Hamiltonian by at
most `2(h+κ)` (the closed form `H = -h Re S + κ/(2N) (N² - |S|²)`, `S = ∑ e^{2πi x_j}`), so the
Gibbs density satisfies `ρ(t, a) ≥ e^{-2(h+κ)} ρ(s, a)`.  Testing the Poincare quotient on the
tagged function `x ↦ cos(2π x_0)` (energy `≤ a0 = 4π²`, variance `≥ e^{-2(h+κ)}/2`) gives
`λ_N ≤ 2 a0 e^{2(h+κ)}` for every `N ≥ 1`; `tilted_tagged_upper_poincare_bound` is the case
`h = 1/2`, `κ = 4`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN.TiltedXY.Fin051

/-- The unit phase `e^{2πi x}` of a point of the circle `𝕋^1`. -/
noncomputable def phase (x : DGPS.Torus 1) : ℂ := fourier 1 (x 0)

theorem norm_phase (x : DGPS.Torus 1) : ‖phase x‖ = 1 := by
  simp [phase]

theorem continuous_phase : Continuous phase :=
  (map_continuous (fourier (T := 1) 1)).comp (continuous_apply 0)

theorem phase_lift (a : Fin 1 → ℝ) :
    phase (DGPS.torusLift a) = Complex.exp (2 * Real.pi * Complex.I * a 0) := by
  have h : (DGPS.torusLift a) 0 = ((a 0 : ℝ) : UnitAddCircle) := rfl
  rw [phase, h, fourier_coe_apply]
  congr 1
  push_cast; ring

theorem phase_re_lift (a : Fin 1 → ℝ) :
    (phase (DGPS.torusLift a)).re = Real.cos (2 * Real.pi * a 0) := by
  rw [phase_lift]
  have : (2 * Real.pi * Complex.I * a 0 : ℂ) = ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem phase_mul_conj_re_lift (a b : Fin 1 → ℝ) :
    (phase (DGPS.torusLift a) * (starRingEnd ℂ) (phase (DGPS.torusLift b))).re =
      Real.cos (2 * Real.pi * (a 0 - b 0)) := by
  rw [phase_lift, phase_lift, ← Complex.exp_conj, ← Complex.exp_add]
  have : (2 * Real.pi * Complex.I * a 0 + (starRingEnd ℂ) (2 * Real.pi * Complex.I * b 0) : ℂ) =
      ((2 * Real.pi * (a 0 - b 0) : ℝ) : ℂ) * Complex.I := by
    simp [map_mul, map_ofNat]; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

/-- The tilted attractive cosine model on `𝕋^1`: `V_h(x) = -h cos(2π x)` and
`W_κ(x,y) = κ (1 - cos(2π (x - y)))`. -/
noncomputable def tiltedXYData (h κ : ℝ) : DGPS.InteractionData 1 where
  V := fun x => -h * (phase x).re
  W := fun x y => κ * (1 - (phase x * (starRingEnd ℂ) (phase y)).re)
  V_continuous := continuous_const.mul (Complex.continuous_re.comp continuous_phase)
  W_continuous := continuous_const.mul (continuous_const.sub (Complex.continuous_re.comp
    ((continuous_phase.comp continuous_fst).mul
      (Complex.continuous_conj.comp (continuous_phase.comp continuous_snd)))))
  W_symm := fun x y => by simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  W_diag := fun x => by
    have h1 := norm_phase x
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, h1]
    simp

theorem tiltedXYData_V_lift (h κ : ℝ) (a : Fin 1 → ℝ) :
    (tiltedXYData h κ).V (DGPS.torusLift a) = -h * Real.cos (2 * Real.pi * a 0) := by
  show -h * (phase _).re = _
  rw [phase_re_lift]

theorem tiltedXYData_W_lift (h κ : ℝ) (a b : Fin 1 → ℝ) :
    (tiltedXYData h κ).W (DGPS.torusLift a) (DGPS.torusLift b) =
      κ * (1 - Real.cos (2 * Real.pi * (a 0 - b 0))) := by
  show κ * (1 - _) = _
  rw [phase_mul_conj_re_lift]

theorem hamiltonian_eq (h κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleHamiltonian (tiltedXYData h κ) N x =
      -h * (∑ i, phase (x i)).re +
        κ / (2 * (N : ℝ)) * ((N : ℝ) ^ 2 - Complex.normSq (∑ i, phase (x i))) := by
  have hS : ∑ i, ∑ j, (phase (x i) * (starRingEnd ℂ) (phase (x j))).re =
      Complex.normSq (∑ i, phase (x i)) := by
    have h1 : (∑ i, phase (x i)) * (starRingEnd ℂ) (∑ j, phase (x j)) =
        ∑ i, ∑ j, phase (x i) * (starRingEnd ℂ) (phase (x j)) := by
      rw [map_sum, Finset.sum_mul_sum]
    have h2 := congrArg Complex.re h1
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.re_sum] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ => (Complex.re_sum _ _).symm
  unfold DGPS.particleHamiltonian
  show ∑ i, (-h * (phase (x i)).re) + _ * ∑ i, ∑ j, κ * (1 - (phase (x i) * (starRingEnd ℂ) (phase (x j))).re) = _
  rw [← Finset.mul_sum, Complex.re_sum]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hS]
  ring

/-- The configuration of `n+1` particles with tagged particle `t` and the others `a`. -/
abbrev consP (n : ℕ) (t : DGPS.Torus 1) (a : Fin n → DGPS.Torus 1) :
    DGPS.ParticleSpace 1 n.succPNat :=
  (Fin.cons t a : Fin (n + 1) → DGPS.Torus 1)

theorem sum_phase_cons (n : ℕ) (t : DGPS.Torus 1) (a : Fin n → DGPS.Torus 1) :
    ∑ i : Fin (n.succPNat : ℕ), phase (consP n t a i) =
      phase t + ∑ j, phase (a j) := by
  show ∑ i : Fin (n + 1), phase ((Fin.cons t a : Fin (n + 1) → DGPS.Torus 1) i) = _
  rw [Fin.sum_univ_succ]
  simp

theorem hamiltonian_cons_le {h κ : ℝ} (hh : 0 ≤ h) (hκ : 0 ≤ κ) (n : ℕ)
    (s t : DGPS.Torus 1) (a : Fin n → DGPS.Torus 1) :
    DGPS.particleHamiltonian (tiltedXYData h κ) n.succPNat
        (consP n t a) ≤
      DGPS.particleHamiltonian (tiltedXYData h κ) n.succPNat
        (consP n s a) + 2 * (h + κ) := by
  rw [hamiltonian_eq, hamiltonian_eq, sum_phase_cons, sum_phase_cons]
  set T : ℂ := ∑ j, phase (a j) with hT
  have hTn : ‖T‖ ≤ n := by
    calc ‖T‖ ≤ ∑ j, ‖phase (a j)‖ := norm_sum_le _ _
      _ = n := by simp [norm_phase]
  have hp : |(phase t).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (norm_phase t).le
  have hq : |(phase s).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (norm_phase s).le
  have hpT : |((phase t) * (starRingEnd ℂ) T).re| ≤ n := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, norm_phase, one_mul]; exact hTn
  have hqT : |((phase s) * (starRingEnd ℂ) T).re| ≤ n := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, norm_phase, one_mul]; exact hTn
  have e1 : Complex.normSq (phase t) = 1 := by rw [Complex.normSq_eq_norm_sq, norm_phase]; simp
  have e2 : Complex.normSq (phase s) = 1 := by rw [Complex.normSq_eq_norm_sq, norm_phase]; simp
  rw [Complex.normSq_add, Complex.normSq_add, e1, e2, Complex.add_re, Complex.add_re]
  have hN : ((n.succPNat : ℕ+) : ℝ) = (n : ℝ) + 1 := by simp
  rw [hN]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE : κ / (2 * ((n : ℝ) + 1)) * (4 * n) ≤ 2 * κ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hE0 : 0 ≤ κ / (2 * ((n : ℝ) + 1)) := by positivity
  have habs := abs_le.mp hp
  have habs2 := abs_le.mp hq
  have h1 := abs_le.mp hpT
  have h2 := abs_le.mp hqT
  have key : κ / (2 * ((n : ℝ) + 1)) *
      (((n : ℝ) + 1) ^ 2 - (1 + Complex.normSq T + 2 * ((phase t) * (starRingEnd ℂ) T).re)) ≤
      κ / (2 * ((n : ℝ) + 1)) *
      (((n : ℝ) + 1) ^ 2 - (1 + Complex.normSq T + 2 * ((phase s) * (starRingEnd ℂ) T).re)) +
        κ / (2 * ((n : ℝ) + 1)) * (4 * n) := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hE0
    nlinarith
  nlinarith [mul_nonneg hh hh]

theorem density_cons_ge {h κ : ℝ} (hh : 0 ≤ h) (hκ : 0 ≤ κ) (n : ℕ)
    (s t : DGPS.Torus 1) (a : Fin n → DGPS.Torus 1) :
    Real.exp (-(2 * (h + κ))) *
        DGPS.particleDensity (tiltedXYData h κ) n.succPNat
          (consP n s a) ≤
      DGPS.particleDensity (tiltedXYData h κ) n.succPNat
        (consP n t a) := by
  unfold DGPS.particleDensity
  have hZ : 0 < (DGPS.particlePartition (tiltedXYData h κ) n.succPNat)⁻¹ :=
    inv_pos.mpr (DGPS.Particle.particlePartition_pos _ _)
  have := hamiltonian_cons_le hh hκ n s t a
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ hZ.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith


/-- The configuration of `n+1` particles as a function on `Fin (n+1)`. -/
abbrev consF (n : ℕ) (t : DGPS.Torus 1) (a : Fin n → DGPS.Torus 1) :
    Fin (n + 1) → DGPS.Torus 1 := Fin.cons t a

theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem continuous_consF (n : ℕ) :
    Continuous (fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) => consF n p.1 p.2) :=
  Continuous.finCons (n := n) (A := fun _ => DGPS.Torus 1)
    (f := fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) => p.1)
    (g := fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) => p.2) continuous_fst continuous_snd

theorem fubini_lower (n : ℕ) (ρ : (Fin (n + 1) → DGPS.Torus 1) → ℝ) (hρc : Continuous ρ)
    (K : ℝ) (hmono : ∀ s t a, K * ρ (consF n s a) ≤ ρ (consF n t a))
    (hρ1 : ∫ x, ρ x ∂(Measure.pi fun _ : Fin (n + 1) => DGPS.haar 1) = 1)
    (G : DGPS.Torus 1 → ℝ) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t) :
    K * ∫ t, G t ∂DGPS.haar 1 ≤
      ∫ x, ρ x * G (x 0) ∂(Measure.pi fun _ : Fin (n + 1) => DGPS.haar 1) := by
  have hmp := DGPS.FiniteN.Tools.BoundedComparison.measurePreserving_consEquiv (n := n)
    (fun _ : Fin (n + 1) => DGPS.haar 1)
  set ν : Measure (Fin n → DGPS.Torus 1) := Measure.pi fun _ : Fin n => DGPS.haar 1 with hν
  have hc : ∀ p, DGPS.FiniteN.Tools.BoundedComparison.consEquiv n p = consF n p.1 p.2 :=
    fun p => DGPS.FiniteN.Tools.BoundedComparison.consEquiv_apply p
  have hfc : Continuous (fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) =>
      ρ (consF n p.1 p.2) * G p.1) :=
    (hρc.comp (continuous_consF n)).mul (hG.comp continuous_fst)
  have hρcc : Continuous (fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) =>
      ρ (consF n p.1 p.2)) := hρc.comp (continuous_consF n)
  have hL : ∫ x, ρ x * G (x 0) ∂(Measure.pi fun _ : Fin (n + 1) => DGPS.haar 1) =
      ∫ p, ρ (consF n p.1 p.2) * G p.1 ∂(DGPS.haar 1).prod ν := by
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [hc, consF]
  have hI : ∫ x, ρ x ∂(Measure.pi fun _ : Fin (n + 1) => DGPS.haar 1) =
      ∫ p, ρ (consF n p.1 p.2) ∂(DGPS.haar 1).prod ν := by
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [hc]
  have i1 : Integrable (fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) =>
      ρ (consF n p.1 p.2) * G p.1) ((DGPS.haar 1).prod ν) := integrable_of_cont hfc
  have i2 : Integrable (fun p : DGPS.Torus 1 × (Fin n → DGPS.Torus 1) =>
      ρ (consF n p.1 p.2)) ((DGPS.haar 1).prod ν) := integrable_of_cont hρcc
  rw [hL, integral_prod_symm _ i1]
  set Φ : (Fin n → DGPS.Torus 1) → ℝ := fun a => ∫ s, ρ (consF n s a) ∂DGPS.haar 1 with hΦ
  have hΦint : ∫ a, Φ a ∂ν = 1 := by
    have h3 : ∫ p, ρ (consF n p.1 p.2) ∂(DGPS.haar 1).prod ν = ∫ a, Φ a ∂ν :=
      integral_prod_symm _ i2
    rw [← h3, ← hI]
    exact hρ1
  have hΦi : Integrable Φ ν := i2.integral_prod_right
  have hcont_a : ∀ a, Continuous (fun t => ρ (consF n t a)) := fun a =>
    hρc.comp ((continuous_consF n).comp (continuous_id.prodMk continuous_const))
  have hpt : ∀ a t, K * Φ a ≤ ρ (consF n t a) := by
    intro a t
    have : K * Φ a = ∫ s, K * ρ (consF n s a) ∂DGPS.haar 1 := by
      rw [integral_const_mul]
    rw [this]
    calc ∫ s, K * ρ (consF n s a) ∂DGPS.haar 1 ≤ ∫ s, ρ (consF n t a) ∂DGPS.haar 1 :=
          integral_mono (integrable_of_cont (continuous_const.mul (hcont_a a)))
            (integrable_const _) (fun s => hmono s t a)
      _ = ρ (consF n t a) := by simp
  have hin : ∀ a, K * Φ a * ∫ t, G t ∂DGPS.haar 1 ≤
      ∫ t, ρ (consF n t a) * G t ∂DGPS.haar 1 := by
    intro a
    rw [← integral_const_mul]
    exact integral_mono (integrable_of_cont (continuous_const.mul hG))
      (integrable_of_cont ((hcont_a a).mul hG)) (fun t => mul_le_mul_of_nonneg_right (hpt a t) (hG0 t))
  calc K * ∫ t, G t ∂DGPS.haar 1 = ∫ a, K * Φ a * ∫ t, G t ∂DGPS.haar 1 ∂ν := by
        rw [integral_mul_const, integral_const_mul, hΦint]; ring
    _ ≤ _ := by
        refine integral_mono ((hΦi.const_mul K).mul_const _) ?_ hin
        exact i1.integral_prod_right


/-- The tagged test function `x ↦ cos(2π x_{0})`. -/
noncomputable def testG (N : ℕ+) (x : DGPS.ParticleSpace 1 N) : ℝ :=
  (phase (x ⟨0, N.pos⟩)).re

theorem testG_eq_mFourier (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    testG N x = (UnitAddTorus.mFourier
      (Pi.single ((⟨0, N.pos⟩ : Fin N), (0 : Fin 1)) (1 : ℤ) : Fin N × Fin 1 → ℤ)
      (DGPS.particleUncurry 1 N x)).re := by
  unfold testG
  congr 1
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single ((⟨0, N.pos⟩ : Fin N), (0 : Fin 1))]
  · simp [DGPS.particleUncurry_apply, phase]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · simp

theorem isSmooth_testG (N : ℕ+) : DGPS.IsSmoothPeriodicParticle (testG N) := by
  have : testG N = fun x => (UnitAddTorus.mFourier
      (Pi.single ((⟨0, N.pos⟩ : Fin N), (0 : Fin 1)) (1 : ℤ) : Fin N × Fin 1 → ℤ)
      (DGPS.particleUncurry 1 N x)).re := funext (testG_eq_mFourier N)
  rw [this]
  exact DGPS.isSmoothPeriodicParticle_re_mFourier _

theorem continuous_testG (N : ℕ+) : Continuous (testG N) :=
  Complex.continuous_re.comp (continuous_phase.comp (continuous_apply _))

theorem fderiv_testG (N : ℕ+) (y : Fin N → Fin 1 → ℝ) (i : Fin N) (j : Fin 1) :
    fderiv ℝ (testG N ∘ DGPS.particleLift) y (Pi.single i (Pi.single j (1 : ℝ))) =
      -(Real.sin (2 * Real.pi * y ⟨0, N.pos⟩ 0)) * (2 * Real.pi) *
        (if i = ⟨0, N.pos⟩ then 1 else 0) := by
  have hfun : (testG N ∘ DGPS.particleLift) =
      fun y : Fin N → Fin 1 → ℝ => Real.cos (2 * Real.pi * y ⟨0, N.pos⟩ 0) := by
    funext y
    simp only [Function.comp, testG, DGPS.particleLift]
    exact phase_re_lift _
  rw [hfun]
  let L : (Fin N → Fin 1 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 1 → ℝ) (⟨0, N.pos⟩ : Fin N))
  have hd : HasFDerivAt (fun y : Fin N → Fin 1 → ℝ => Real.cos (2 * Real.pi * y ⟨0, N.pos⟩ 0))
      (-Real.sin (2 * Real.pi * L y) • (2 * Real.pi) • L) y :=
    ((L.hasFDerivAt (x := y)).const_mul (2 * Real.pi)).cos
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [hd.fderiv]
  simp only [smul_apply, smul_eq_mul]
  have hL : L (Pi.single i (Pi.single 0 (1 : ℝ))) = if i = ⟨0, N.pos⟩ then 1 else 0 := by
    by_cases hi : i = ⟨0, N.pos⟩
    · subst hi
      simp only [↓reduceIte]
      show (Pi.single (⟨0, N.pos⟩ : Fin N) (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ) ⟨0, N.pos⟩ 0 = 1
      simp
    · simp only [hi, ↓reduceIte]
      show (Pi.single i (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ) ⟨0, N.pos⟩ 0 = 0
      rw [Pi.single_eq_of_ne (Ne.symm hi)]
      rfl
  have hLy : L y = y ⟨0, N.pos⟩ 0 := rfl
  rw [hL, hLy]
  ring


theorem continuous_re_phase : Continuous fun t : DGPS.Torus 1 => (phase t).re :=
  Complex.continuous_re.comp continuous_phase

theorem integral_haar_re_phase : ∫ t, (phase t).re ∂DGPS.haar 1 = 0 := by
  have hc : Continuous ((fun t : DGPS.Torus 1 => (phase t).re) ∘ DGPS.torusLift) := by
    have : ((fun t : DGPS.Torus 1 => (phase t).re) ∘ DGPS.torusLift) =
        fun a : Fin 1 → ℝ => Real.cos (2 * Real.pi * a 0) := funext phase_re_lift
    rw [this]; fun_prop
  rw [DGPS.Analysis.CircleMoments.integral_haar_eq hc]
  simp only [phase_re_lift]
  exact DGPS.Analysis.CircleMoments.integral_cos_two_pi

theorem integral_haar_re_phase_sq : ∫ t, (phase t).re ^ 2 ∂DGPS.haar 1 = 1 / 2 := by
  have hc : Continuous ((fun t : DGPS.Torus 1 => (phase t).re ^ 2) ∘ DGPS.torusLift) := by
    have : ((fun t : DGPS.Torus 1 => (phase t).re ^ 2) ∘ DGPS.torusLift) =
        fun a : Fin 1 → ℝ => Real.cos (2 * Real.pi * a 0) ^ 2 := by
      funext a; simp [phase_re_lift]
    rw [this]; fun_prop
  rw [DGPS.Analysis.CircleMoments.integral_haar_eq hc]
  simp only [phase_re_lift]
  exact DGPS.Analysis.CircleMoments.integral_cos_sq_two_pi

theorem half_le_integral_haar_sq (m : ℝ) :
    1 / 2 ≤ ∫ t, ((phase t).re - m) ^ 2 ∂DGPS.haar 1 := by
  have h1 : Integrable (fun t : DGPS.Torus 1 => (phase t).re) (DGPS.haar 1) :=
    integrable_of_cont continuous_re_phase
  have h2 : Integrable (fun t : DGPS.Torus 1 => (phase t).re ^ 2) (DGPS.haar 1) :=
    integrable_of_cont (continuous_re_phase.pow 2)
  have : ∀ t : DGPS.Torus 1, ((phase t).re - m) ^ 2 =
      (phase t).re ^ 2 - 2 * m * (phase t).re + m ^ 2 := fun t => by ring
  simp_rw [this]
  have h3 : Integrable (fun t : DGPS.Torus 1 => 2 * m * (phase t).re) (DGPS.haar 1) :=
    h1.const_mul _
  have hi : Integrable (fun t : DGPS.Torus 1 => (phase t).re ^ 2 - 2 * m * (phase t).re)
      (DGPS.haar 1) := h2.sub h3
  rw [integral_add hi (integrable_const (m ^ 2)), integral_sub h2 h3, integral_const_mul,
    integral_haar_re_phase, integral_haar_re_phase_sq]
  simp
  nlinarith [sq_nonneg m]

theorem tangentNormSq_testG (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particleTangentNormSq
      ((fun x i => (WithLp.toLp 2 fun j => DGPS.particlePartial i j (testG N) x :
        DGPS.Tangent 1)) x : Fin N → DGPS.Tangent 1) ≤ DGPS.Circle.AngularNormalization.a0 := by
  rw [DGPS.particleTangentNormSq_eq]
  have : ∀ (i : Fin N) (j : Fin 1), DGPS.particlePartial i j (testG N) x =
      -(Real.sin (2 * Real.pi * SharpLSI.secT (x ⟨0, N.pos⟩) 0)) * (2 * Real.pi) *
        (if i = ⟨0, N.pos⟩ then 1 else 0) := fun i j => fderiv_testG N _ i j
  simp only [this]
  simp only [Fin.sum_univ_one, mul_pow, ite_pow, one_pow, zero_pow two_ne_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold DGPS.Circle.AngularNormalization.a0
  nlinarith [Real.sin_sq_le_one (2 * Real.pi * SharpLSI.secT (x ⟨0, N.pos⟩) 0), sq_nonneg Real.pi]


theorem poincareRate_le_general {h κ : ℝ} (hh : 0 ≤ h) (hκ : 0 ≤ κ) (n : ℕ) :
    DGPS.particlePoincareRate (tiltedXYData h κ) n.succPNat ≤
      ENNReal.ofReal (2 * DGPS.Circle.AngularNormalization.a0 * Real.exp (2 * (h + κ))) := by
  set A := tiltedXYData h κ with hA
  set N : ℕ+ := n.succPNat with hN
  set K : ℝ := Real.exp (-(2 * (h + κ))) with hK
  have hK0 : 0 < K := Real.exp_pos _
  have hP := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth (isSmooth_testG N)
  have hmem : DGPS.MemParticleH1 A N (testG N) := (DGPS.memParticleH1_iff A N _).2 ⟨_, hG⟩
  let F : DGPS.ParticleH1 A N := ⟨testG N, hmem⟩
  have hgrad := (DGPS.isParticleWeakGradient_iff A N _ _).2 hG
  have hE : DGPS.particleEnergy A N F ≤ DGPS.Circle.AngularNormalization.a0 := by
    rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient F hgrad]
    calc _ ≤ ∫ _x, DGPS.Circle.AngularNormalization.a0 ∂DGPS.particleLaw A N :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall fun x => tangentNormSq_testG N x)
      _ = _ := by simp
  have hmeas : AEMeasurable (testG N) (DGPS.particleLaw A N) :=
    (continuous_testG N).measurable.aemeasurable
  set m : ℝ := ∫ x, testG N x ∂DGPS.particleLaw A N with hm
  have hV : K / 2 ≤ ProbabilityTheory.variance (testG N) (DGPS.particleLaw A N) := by
    rw [ProbabilityTheory.variance_eq_integral hmeas, DGPS.Particle.integral_particleLaw A N]
    have hfub := fubini_lower n (fun x : Fin (n + 1) → DGPS.Torus 1 => DGPS.particleDensity A N x)
      (DGPS.Particle.particleDensity_continuous A N) K
      (fun s t a => density_cons_ge hh hκ n s t a) (DGPS.Particle.integral_particleDensity A N)
      (fun t => ((phase t).re - m) ^ 2) ((continuous_re_phase.sub continuous_const).pow 2)
      (fun t => sq_nonneg _)
    have h2 := half_le_integral_haar_sq m
    calc K / 2 = K * (1 / 2) := by ring
      _ ≤ K * ∫ t, ((phase t).re - m) ^ 2 ∂DGPS.haar 1 := by gcongr
      _ ≤ _ := hfub
  have hVpos : 0 < ProbabilityTheory.variance F.1 (DGPS.particleLaw A N) :=
    lt_of_lt_of_le (by positivity) hV
  refine (DGPS.particlePoincareRate_le_quotient A N F hVpos).trans ?_
  unfold DGPS.particlePoincareQuotient
  rw [← ENNReal.ofReal_div_of_pos hVpos]
  apply ENNReal.ofReal_le_ofReal
  have h3 : DGPS.particleEnergy A N F / ProbabilityTheory.variance F.1 (DGPS.particleLaw A N) ≤
      DGPS.Circle.AngularNormalization.a0 / (K / 2) :=
    div_le_div₀ DGPS.Circle.AngularNormalization.a0_pos.le hE (by positivity) hV
  refine h3.trans (le_of_eq ?_)
  rw [hK, Real.exp_neg]
  field_simp

end DGPS.FiniteN.TiltedXY.Fin051

namespace DGPS.FiniteN

/-- FIN051: for the tilted XY model with `κ = 4`, `h = 1/2` and every `N ≥ 1`, the finite-`N`
Poincare rate satisfies `λ_N ≤ 2 a0 exp(2(h+κ))`, `a0 = 4π²`. -/
theorem tilted_tagged_upper_poincare_bound (N : ℕ+) :
    DGPS.particlePoincareRate (DGPS.FiniteN.TiltedXY.Fin051.tiltedXYData (1 / 2) 4) N ≤
      ENNReal.ofReal (2 * DGPS.Circle.AngularNormalization.a0 *
        Real.exp (2 * ((1 / 2 : ℝ) + 4))) := by
  have h := DGPS.FiniteN.TiltedXY.Fin051.poincareRate_le_general (h := 1 / 2) (κ := 4)
    (by norm_num) (by norm_num) N.natPred
  rwa [PNat.succPNat_natPred] at h

end DGPS.FiniteN
