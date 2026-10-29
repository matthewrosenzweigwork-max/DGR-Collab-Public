import DGPS.FiniteN.SymmetricHarmonicTrial

/-!
# Second harmonic residual: explicit formula and strict sign (FIN091)

For the second-harmonic model `V = 0`, `W = κ[cos 4π(x−y) − 1]` on the unit-period circle and the
symmetric trial `F_N = ∑ᵢ cos 2π xᵢ` (FIN090), the residual of the generator
`L_N = Δ − ∇H_N·∇` (unscaled coordinates, `H_N` the particle Hamiltonian) is
`R_N = −L_N F_N − a₀ F_N = (8π²κ/N) ∑_{i<j} sin 4π(xᵢ−xⱼ)[sin 2πxᵢ − sin 2πxⱼ]`.
For every `N ≥ 2` and `κ > 0` it is smooth, permutation symmetric, takes the value
`(8π²κ/N)(N−1)√2/2 > 0` at the configuration `x₁ = 1/8`, `xⱼ = 0 (j > 1)`, and hence
`‖R_N‖²_{L²(P_N)} > 0`.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal ContDiff

namespace DGPS.FiniteN

/-- The generator `L_N f = ∑ᵢ ∂ᵢ² f − ∑ᵢ ∂ᵢH_N ∂ᵢ f` of the (unscaled) `N`-particle Gibbs
diffusion on the circle, acting on smooth periodic functions via the representative partial
derivatives `particlePartial`. -/
noncomputable def particleGenerator (A : DGPS.InteractionData 1) (N : ℕ+)
    (f : DGPS.ParticleSpace 1 N → ℝ) (x : DGPS.ParticleSpace 1 N) : ℝ :=
  ∑ i, DGPS.particlePartial i 0 (DGPS.particlePartial i 0 f) x -
    ∑ i, DGPS.particlePartial i 0 (DGPS.particleHamiltonian A N) x *
      DGPS.particlePartial i 0 f x

/-- The residual `R_N = −L_N F_N − a₀ F_N` of the symmetric harmonic trial. -/
noncomputable def secondHarmonicResidual (κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) : ℝ :=
  -particleGenerator (secondHarmonicData κ) N (harmonicTrial N) x -
    DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x

/-- The displayed closed form of the residual. -/
noncomputable def explicitResidual (κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) : ℝ :=
  (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
    (mode 2 (x i - x j)).im * ((mode 1 (x i)).im - (mode 1 (x j)).im)

/-! ### Line derivatives -/

theorem shift_apply {N : ℕ+} (y0 : Fin N → Fin 1 → ℝ) (i k : Fin N) (t : ℝ) :
    (y0 + t • (Pi.single i (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ)) k 0 =
      y0 k 0 + if k = i then t else 0 := by
  by_cases h : k = i
  · subst h; simp
  · simp [h]

theorem particlePartial_eq_of_hasDerivAt {N : ℕ+} {φ : DGPS.ParticleSpace 1 N → ℝ}
    (hs : DGPS.IsSmoothPeriodicParticle φ) (i : Fin N) (x : DGPS.ParticleSpace 1 N) (c : ℝ)
    (h : HasDerivAt (fun t : ℝ => (φ ∘ DGPS.particleLift)
      ((fun k => SharpLSI.secT (x k)) +
        t • (Pi.single i (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ))) c 0) :
    DGPS.particlePartial i 0 φ x = c := by
  set y0 : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k) with hy0
  set v : Fin N → Fin 1 → ℝ := Pi.single i (Pi.single 0 (1 : ℝ)) with hv
  have hD : DifferentiableAt ℝ (φ ∘ DGPS.particleLift) y0 :=
    (hs.differentiable (by simp)) _
  have hline : HasDerivAt (fun t : ℝ => y0 + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y0
  have hD' : HasFDerivAt (φ ∘ DGPS.particleLift)
      (fderiv ℝ (φ ∘ DGPS.particleLift) y0) (y0 + (0:ℝ) • v) := by
    simpa using hD.hasFDerivAt
  have h1 := hD'.comp_hasDerivAt (0:ℝ) hline
  have h3 := h1.unique h
  unfold DGPS.particlePartial
  exact h3

theorem hasDerivAt_sum_shift {N : ℕ+} (g g' : ℝ → ℝ) (hg : ∀ a, HasDerivAt g (g' a) a)
    (u : Fin N → ℝ) (i : Fin N) :
    HasDerivAt (fun t : ℝ => ∑ k, g (u k + if k = i then t else 0)) (g' (u i)) 0 := by
  have hk : ∀ k ∈ (Finset.univ : Finset (Fin N)), HasDerivAt
      (fun t : ℝ => g (u k + if k = i then t else 0)) (if k = i then g' (u i) else 0) 0 := by
    intro k _
    by_cases h : k = i
    · subst h
      simp only [ite_true]
      have := (hg (u k + 0)).comp_const_add (u k) 0
      simpa using this
    · simp only [h, ite_false, add_zero]
      exact hasDerivAt_const _ _
  have := HasDerivAt.fun_sum hk
  simpa using this

/-! ### Trigonometric forms of the lifts -/

theorem im_mode_one_lift (a : Fin 1 → ℝ) :
    (mode 1 (DGPS.torusLift a)).im = Real.sin (2 * Real.pi * a 0) := by
  rw [mode_lift]
  have h : (2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (a 0 : ℂ)) =
      ((2 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

theorem re_mode_two_lift (a : Fin 1 → ℝ) :
    (mode 2 (DGPS.torusLift a)).re = Real.cos (4 * Real.pi * a 0) := by
  rw [mode_lift]
  have h : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * (a 0 : ℂ)) =
      ((4 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

theorem im_mode_two_lift (a : Fin 1 → ℝ) :
    (mode 2 (DGPS.torusLift a)).im = Real.sin (4 * Real.pi * a 0) := by
  rw [mode_lift]
  have h : (2 * Real.pi * Complex.I * ((2 : ℤ) : ℂ) * (a 0 : ℂ)) =
      ((4 * Real.pi * a 0 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

theorem im_mode_two_sub_lift (a b : Fin 1 → ℝ) :
    (mode 2 (DGPS.torusLift a - DGPS.torusLift b)).im = Real.sin (4 * Real.pi * (a 0 - b 0)) := by
  have h : DGPS.torusLift a - DGPS.torusLift b = DGPS.torusLift (a - b) := by
    ext i; simp [DGPS.torusLift, SharpLSI.liftT]
  rw [h, im_mode_two_lift]; simp

theorem hamiltonian_lift (κ : ℝ) (N : ℕ+) (y : Fin N → Fin 1 → ℝ) :
    DGPS.particleHamiltonian (secondHarmonicData κ) N (DGPS.particleLift y) =
      κ * ((∑ k, Real.cos (4 * Real.pi * y k 0)) ^ 2 + (∑ k, Real.sin (4 * Real.pi * y k 0)) ^ 2)
        / (2 * (N : ℝ)) - κ * (N : ℝ) / 2 := by
  rw [hamiltonian_eq, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  have e : ∀ k, DGPS.particleLift y k = DGPS.torusLift (y k) := fun k => rfl
  simp_rw [e, re_mode_two_lift, im_mode_two_lift]
  ring

theorem isSmooth_hamiltonian (κ : ℝ) (N : ℕ+) :
    DGPS.IsSmoothPeriodicParticle (DGPS.particleHamiltonian (secondHarmonicData κ) N) := by
  unfold DGPS.IsSmoothPeriodicParticle
  have : DGPS.particleHamiltonian (secondHarmonicData κ) N ∘ DGPS.particleLift =
      fun y : Fin N → Fin 1 → ℝ => κ * ((∑ k, Real.cos (4 * Real.pi * y k 0)) ^ 2 +
        (∑ k, Real.sin (4 * Real.pi * y k 0)) ^ 2) / (2 * (N : ℝ)) - κ * (N : ℝ) / 2 :=
    funext fun y => hamiltonian_lift κ N y
  rw [this]
  have hc : ∀ k : Fin N, ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => y k 0) := fun k =>
    (contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_apply ℝ (Fin 1 → ℝ) k)
  have hC : ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => ∑ k, Real.cos (4 * Real.pi * y k 0)) :=
    ContDiff.sum fun k _ => Real.contDiff_cos.comp (contDiff_const.mul (hc k))
  have hS : ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => ∑ k, Real.sin (4 * Real.pi * y k 0)) :=
    ContDiff.sum fun k _ => Real.contDiff_sin.comp (contDiff_const.mul (hc k))
  exact (((contDiff_const.mul ((hC.pow 2).add (hS.pow 2))).div_const _).sub contDiff_const)

/-! ### Partial derivatives of `F_N` and `H_N` -/

theorem particlePartial_harmonicTrial_real (N : ℕ+) (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (harmonicTrial N) x =
      -(2 * Real.pi) * Real.sin (2 * Real.pi * SharpLSI.secT (x i) 0) := by
  rw [particlePartial_harmonicTrial]
  have hx : x i = DGPS.torusLift (SharpLSI.secT (x i)) := by
    simp [DGPS.torusLift, SharpLSI.liftT_secT]
  rw [hx, im_mode_one_lift]
  simp [DGPS.torusLift, SharpLSI.liftT_secT]

theorem particlePartial_particlePartial_harmonicTrial (N : ℕ+) (i : Fin N)
    (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (DGPS.particlePartial i 0 (harmonicTrial N)) x =
      -(4 * Real.pi ^ 2) * Real.cos (2 * Real.pi * SharpLSI.secT (x i) 0) := by
  have hψ : DGPS.particlePartial i 0 (harmonicTrial N) =
      fun x : DGPS.ParticleSpace 1 N => -(2 * Real.pi) * (mode 1 (x i)).im :=
    funext fun x => particlePartial_harmonicTrial N i x
  rw [hψ]
  have hlift : ((fun x : DGPS.ParticleSpace 1 N => -(2 * Real.pi) * (mode 1 (x i)).im) ∘
      DGPS.particleLift) = fun y : Fin N → Fin 1 → ℝ => -(2 * Real.pi) * Real.sin (2 * Real.pi * y i 0) := by
    funext y
    simp only [Function.comp_apply]
    have : DGPS.particleLift y i = DGPS.torusLift (y i) := rfl
    rw [this, im_mode_one_lift]
  have hs : DGPS.IsSmoothPeriodicParticle
      (fun x : DGPS.ParticleSpace 1 N => -(2 * Real.pi) * (mode 1 (x i)).im) := by
    unfold DGPS.IsSmoothPeriodicParticle
    rw [hlift]
    have hc : ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => y i 0) :=
      (contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_apply ℝ (Fin 1 → ℝ) i)
    exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hc))
  refine particlePartial_eq_of_hasDerivAt hs i x _ ?_
  set y0 : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k) with hy0
  have hf : (fun t : ℝ => ((fun x : DGPS.ParticleSpace 1 N => -(2 * Real.pi) * (mode 1 (x i)).im) ∘
      DGPS.particleLift) (y0 + t • (Pi.single i (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ))) =
      fun t : ℝ => -(2 * Real.pi) * Real.sin (2 * Real.pi * (y0 i 0 + t)) := by
    funext t
    rw [hlift]
    simp only [shift_apply, ite_true]
  rw [hf]
  have := (((((hasDerivAt_id' (0:ℝ)).const_add (y0 i 0)).const_mul (2 * Real.pi)).sin).const_mul
    (-(2 * Real.pi)))
  convert this using 1
  simp only [hy0]
  ring_nf

theorem particlePartial_hamiltonian (κ : ℝ) (N : ℕ+) (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (DGPS.particleHamiltonian (secondHarmonicData κ) N) x =
      (4 * Real.pi * κ / (N : ℝ)) *
        ((∑ k, Real.sin (4 * Real.pi * SharpLSI.secT (x k) 0)) *
            Real.cos (4 * Real.pi * SharpLSI.secT (x i) 0) -
          (∑ k, Real.cos (4 * Real.pi * SharpLSI.secT (x k) 0)) *
            Real.sin (4 * Real.pi * SharpLSI.secT (x i) 0)) := by
  refine particlePartial_eq_of_hasDerivAt (isSmooth_hamiltonian κ N) i x _ ?_
  set u : Fin N → ℝ := fun k => SharpLSI.secT (x k) 0 with hu
  have hf : (fun t : ℝ => (DGPS.particleHamiltonian (secondHarmonicData κ) N ∘ DGPS.particleLift)
      ((fun k => SharpLSI.secT (x k)) +
        t • (Pi.single i (Pi.single 0 (1 : ℝ)) : Fin N → Fin 1 → ℝ))) =
      fun t : ℝ => κ * ((∑ k, Real.cos (4 * Real.pi * (u k + if k = i then t else 0))) ^ 2 +
        (∑ k, Real.sin (4 * Real.pi * (u k + if k = i then t else 0))) ^ 2) / (2 * (N : ℝ)) -
          κ * (N : ℝ) / 2 := by
    funext t
    simp only [Function.comp_apply]
    rw [hamiltonian_lift]
    simp only [shift_apply, hu]
  rw [hf]
  have hC := hasDerivAt_sum_shift (N := N) (fun a => Real.cos (4 * Real.pi * a))
    (fun a => -(4 * Real.pi) * Real.sin (4 * Real.pi * a))
    (fun a => by
      have := ((hasDerivAt_id' a).const_mul (4 * Real.pi)).cos
      convert this using 1; ring) u i
  have hS := hasDerivAt_sum_shift (N := N) (fun a => Real.sin (4 * Real.pi * a))
    (fun a => (4 * Real.pi) * Real.cos (4 * Real.pi * a))
    (fun a => by
      have := ((hasDerivAt_id' a).const_mul (4 * Real.pi)).sin
      convert this using 1; ring) u i
  have := (((hC.pow 2).add (hS.pow 2)).const_mul κ |>.div_const (2 * (N : ℝ))).sub_const
    (κ * (N : ℝ) / 2)
  convert this using 1
  have hN : (N : ℝ) ≠ 0 := by positivity
  simp only [hu]
  field_simp
  simp
  ring_nf

/-! ### Pairing lemmas -/

theorem sum_sum_Ioi_two {N : ℕ+} (T : Fin N → Fin N → ℝ) (hsymm : ∀ i j, T j i = T i j)
    (hdiag : ∀ i, T i i = 0) :
    ∑ i, ∑ j, T i j = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, T i j := by
  have h1 : ∀ i, ∑ j, T i j =
      ∑ j, ((if i < j then T i j else 0) + (if j < i then T i j else 0)) := by
    intro i
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.not_gt]
    · subst h; simp [hdiag]
    · simp [h, h.not_gt]
  simp_rw [h1, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, (if j < i then T i j else 0) = ∑ i, ∑ j, (if i < j then T i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsymm]
  have h3 : ∀ i, ∑ j, (if i < j then T i j else 0) = ∑ j ∈ Finset.Ioi i, T i j := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  simp_rw [h3] at h2 ⊢
  rw [h2]; ring

theorem sum_antisymm_pair {N : ℕ+} (s : Fin N → ℝ) (g : Fin N → Fin N → ℝ)
    (hg : ∀ i j, g j i = -g i j) :
    ∑ i, ∑ j, g i j * s i = ∑ i, ∑ j ∈ Finset.Ioi i, g i j * (s i - s j) := by
  have hT := sum_sum_Ioi_two (fun i j => g i j * (s i - s j))
    (fun i j => by simp only [hg i j]; ring) (fun i => by simp)
  have hcomm : ∑ i, ∑ j, g i j * s j = -∑ i, ∑ j, g i j * s i := by
    calc ∑ i, ∑ j, g i j * s j = ∑ j, ∑ i, g i j * s j := Finset.sum_comm
      _ = ∑ i, ∑ j, -(g i j * s i) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hg i j]; ring
      _ = _ := by simp [Finset.sum_neg_distrib]
  have hsub : ∑ i, ∑ j, g i j * (s i - s j) =
      ∑ i, ∑ j, g i j * s i - ∑ i, ∑ j, g i j * s j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  linarith

theorem real_form {N : ℕ+} (κ : ℝ) (u : Fin N → ℝ) :
    ∑ i, (4 * Real.pi * κ / (N : ℝ)) *
        ((∑ k, Real.sin (4 * Real.pi * u k)) * Real.cos (4 * Real.pi * u i) -
          (∑ k, Real.cos (4 * Real.pi * u k)) * Real.sin (4 * Real.pi * u i)) *
        (-(2 * Real.pi) * Real.sin (2 * Real.pi * u i)) =
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
        Real.sin (4 * Real.pi * (u i - u j)) *
          (Real.sin (2 * Real.pi * u i) - Real.sin (2 * Real.pi * u j)) := by
  have e : ∀ i, (∑ k, Real.sin (4 * Real.pi * u k)) * Real.cos (4 * Real.pi * u i) -
      (∑ k, Real.cos (4 * Real.pi * u k)) * Real.sin (4 * Real.pi * u i) =
      -∑ k, Real.sin (4 * Real.pi * (u i - u k)) := by
    intro i
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_sub, Real.sin_sub]; ring
  have e2 : ∀ i, (4 * Real.pi * κ / (N : ℝ)) *
        ((∑ k, Real.sin (4 * Real.pi * u k)) * Real.cos (4 * Real.pi * u i) -
          (∑ k, Real.cos (4 * Real.pi * u k)) * Real.sin (4 * Real.pi * u i)) *
        (-(2 * Real.pi) * Real.sin (2 * Real.pi * u i)) =
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) *
        ∑ k, Real.sin (4 * Real.pi * (u i - u k)) * Real.sin (2 * Real.pi * u i) := by
    intro i
    rw [e i, ← Finset.sum_mul]; ring
  simp_rw [e2]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_antisymm_pair (fun i => Real.sin (2 * Real.pi * u i))
    (fun i j => Real.sin (4 * Real.pi * (u i - u j)))
    (fun i j => by
      rw [show 4 * Real.pi * (u j - u i) = -(4 * Real.pi * (u i - u j)) by ring, Real.sin_neg])

/-! ### The explicit formula -/

theorem explicitResidual_lift (κ : ℝ) (N : ℕ+) (y : Fin N → Fin 1 → ℝ) :
    explicitResidual κ N (DGPS.particleLift y) =
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
        Real.sin (4 * Real.pi * (y i 0 - y j 0)) *
          (Real.sin (2 * Real.pi * y i 0) - Real.sin (2 * Real.pi * y j 0)) := by
  unfold explicitResidual
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi : DGPS.particleLift y i = DGPS.torusLift (y i) := rfl
  have hj : DGPS.particleLift y j = DGPS.torusLift (y j) := rfl
  rw [hi, hj, im_mode_two_sub_lift, im_mode_one_lift, im_mode_one_lift]

theorem explicitResidual_eq_secT (κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    explicitResidual κ N x =
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
        Real.sin (4 * Real.pi * (SharpLSI.secT (x i) 0 - SharpLSI.secT (x j) 0)) *
          (Real.sin (2 * Real.pi * SharpLSI.secT (x i) 0) -
            Real.sin (2 * Real.pi * SharpLSI.secT (x j) 0)) := by
  have := explicitResidual_lift κ N (fun i => SharpLSI.secT (x i))
  rwa [DGPS.FiniteN.PositiveRate.particleLift_secT] at this

theorem secondHarmonicResidual_eq (κ : ℝ) (N : ℕ+) (x : DGPS.ParticleSpace 1 N) :
    secondHarmonicResidual κ N x = explicitResidual κ N x := by
  rw [explicitResidual_eq_secT, ← real_form κ (fun k => SharpLSI.secT (x k) 0)]
  have hF : harmonicTrial N x = ∑ i, Real.cos (2 * Real.pi * SharpLSI.secT (x i) 0) := by
    have := harmonicTrial_lift N (fun i => SharpLSI.secT (x i))
    rwa [DGPS.FiniteN.PositiveRate.particleLift_secT] at this
  unfold secondHarmonicResidual particleGenerator
  simp only [particlePartial_particlePartial_harmonicTrial, particlePartial_hamiltonian,
    particlePartial_harmonicTrial_real, hF]
  have ha : DGPS.Circle.AngularNormalization.a0 = 4 * Real.pi ^ 2 := rfl
  rw [ha, ← Finset.mul_sum]
  ring

/-! ### Regularity and symmetry -/

theorem continuous_explicitResidual (κ : ℝ) (N : ℕ+) : Continuous (explicitResidual κ N) := by
  unfold explicitResidual
  refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)
  have h2 : Continuous fun x : DGPS.ParticleSpace 1 N => (mode 2 (x i - x j)).im :=
    Complex.continuous_im.comp ((continuous_mode 2).comp
      ((continuous_apply i).sub (continuous_apply j)))
  have h1 : ∀ k : Fin N, Continuous fun x : DGPS.ParticleSpace 1 N => (mode 1 (x k)).im :=
    fun k => Complex.continuous_im.comp ((continuous_mode 1).comp (continuous_apply k))
  exact h2.mul ((h1 i).sub (h1 j))

theorem isSmooth_explicitResidual (κ : ℝ) (N : ℕ+) :
    DGPS.IsSmoothPeriodicParticle (explicitResidual κ N) := by
  unfold DGPS.IsSmoothPeriodicParticle
  have : explicitResidual κ N ∘ DGPS.particleLift = fun y : Fin N → Fin 1 → ℝ =>
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
        Real.sin (4 * Real.pi * (y i 0 - y j 0)) *
          (Real.sin (2 * Real.pi * y i 0) - Real.sin (2 * Real.pi * y j 0)) :=
    funext fun y => explicitResidual_lift κ N y
  rw [this]
  have hc : ∀ k : Fin N, ContDiff ℝ ∞ (fun y : Fin N → Fin 1 → ℝ => y k 0) := fun k =>
    (contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_apply ℝ (Fin 1 → ℝ) k)
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)
  exact (Real.contDiff_sin.comp (contDiff_const.mul ((hc i).sub (hc j)))).mul
    ((Real.contDiff_sin.comp (contDiff_const.mul (hc i))).sub
      (Real.contDiff_sin.comp (contDiff_const.mul (hc j))))

theorem explicitResidual_permute (κ : ℝ) (N : ℕ+) (σ : Equiv.Perm (Fin N))
    (x : DGPS.ParticleSpace 1 N) :
    explicitResidual κ N (DGPS.permuteParticles σ x) = explicitResidual κ N x := by
  rw [explicitResidual_eq_secT, explicitResidual_eq_secT]
  congr 1
  set u : Fin N → ℝ := fun k => SharpLSI.secT (x k) 0 with hu
  set T : Fin N → Fin N → ℝ := fun i j => Real.sin (4 * Real.pi * (u i - u j)) *
    (Real.sin (2 * Real.pi * u i) - Real.sin (2 * Real.pi * u j)) with hT
  have hsymm : ∀ i j, T j i = T i j := by
    intro i j
    simp only [hT]
    rw [show 4 * Real.pi * (u j - u i) = -(4 * Real.pi * (u i - u j)) by ring, Real.sin_neg]
    ring
  have hdiag : ∀ i, T i i = 0 := fun i => by simp [hT]
  have hT2 := sum_sum_Ioi_two T hsymm hdiag
  have hT3 := sum_sum_Ioi_two (fun i j => T (σ i) (σ j)) (fun i j => hsymm _ _) (fun i => hdiag _)
  have hperm : ∑ i, ∑ j, T (σ i) (σ j) = ∑ i, ∑ j, T i j := by
    rw [← Equiv.sum_comp σ (fun i => ∑ j, T i j)]
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => T (σ i) j)
  show ∑ i, ∑ j ∈ Finset.Ioi i, T (σ i) (σ j) = ∑ i, ∑ j ∈ Finset.Ioi i, T i j
  linarith

/-! ### Evaluation at the displayed configuration -/

/-- The first label. -/
def firstLabel (N : ℕ+) : Fin N := ⟨0, N.pos⟩

theorem torusLift_zero : DGPS.torusLift (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  ext i; simp [DGPS.torusLift, SharpLSI.liftT]

/-- The configuration `x₁ = 1/8`, `xⱼ = 0` for `j > 1`. -/
noncomputable def residualConfig (N : ℕ+) : DGPS.ParticleSpace 1 N :=
  fun k => if k = firstLabel N then DGPS.torusLift (fun _ => (1 / 8 : ℝ)) else 0

theorem residualConfig_eq_lift (N : ℕ+) :
    residualConfig N = DGPS.particleLift (fun k _ => if k = firstLabel N then (1 / 8 : ℝ) else 0) := by
  funext k
  by_cases h : k = firstLabel N
  · simp [residualConfig, DGPS.particleLift, h]
  · simp [residualConfig, DGPS.particleLift, h, torusLift_zero]

theorem explicitResidual_config (κ : ℝ) (N : ℕ+) :
    explicitResidual κ N (residualConfig N) =
      8 * Real.pi ^ 2 * κ / (N : ℝ) * (((N : ℕ) : ℝ) - 1) * (Real.sqrt 2 / 2) := by
  rw [residualConfig_eq_lift, explicitResidual_lift]
  have hmin : ∀ i : Fin N, firstLabel N ≤ i := fun i => Nat.zero_le _
  have hs1 : Real.sin (4 * Real.pi * (1 / 8 : ℝ)) = 1 := by
    rw [show 4 * Real.pi * (1 / 8 : ℝ) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  have hs2 : Real.sin (2 * Real.pi * (1 / 8 : ℝ)) = Real.sqrt 2 / 2 := by
    rw [show 2 * Real.pi * (1 / 8 : ℝ) = Real.pi / 4 by ring, Real.sin_pi_div_four]
  rw [mul_assoc (8 * Real.pi ^ 2 * κ / (N : ℝ))]
  congr 1
  rw [Finset.sum_eq_single (firstLabel N)]
  · have : ∀ j ∈ Finset.Ioi (firstLabel N),
        Real.sin (4 * Real.pi * ((if firstLabel N = firstLabel N then (1 / 8 : ℝ) else 0) -
            (if j = firstLabel N then (1 / 8 : ℝ) else 0))) *
          (Real.sin (2 * Real.pi * (if firstLabel N = firstLabel N then (1 / 8 : ℝ) else 0)) -
            Real.sin (2 * Real.pi * (if j = firstLabel N then (1 / 8 : ℝ) else 0))) =
          Real.sqrt 2 / 2 := by
      intro j hj
      have hne : j ≠ firstLabel N := ne_of_gt (Finset.mem_Ioi.1 hj)
      simp only [ite_true, hne, ite_false, mul_zero, Real.sin_zero, sub_zero, hs1, hs2, one_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul]
    have h1 : 1 ≤ (N : ℕ) := N.pos
    have : ((N : ℕ) - 1 - (firstLabel N : ℕ) : ℕ) = (N : ℕ) - 1 := by simp [firstLabel]
    rw [this, Nat.cast_sub h1]
    simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : i < j := Finset.mem_Ioi.1 hj
    have hjn : j ≠ firstLabel N := ne_of_gt (lt_of_le_of_lt (hmin i) hj')
    simp [hi, hjn]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The main statement -/

/-- **FIN091.** For `κ > 0` and `N ≥ 2`, the residual `R_N = −L_N F_N − a₀ F_N` of the symmetric
harmonic trial `F_N = ∑ᵢ cos 2π xᵢ` with respect to the generator `L_N = Δ − ∇H_N·∇` equals
`(8π²κ/N) ∑_{i<j} sin 4π(xᵢ−xⱼ)[sin 2πxᵢ − sin 2πxⱼ]`; it is smooth and permutation symmetric;
it equals `(8π²κ/N)(N−1)√2/2 > 0` at `x₁ = 1/8`, `xⱼ = 0` (`j > 1`); consequently
`‖R_N‖²_{L²(P_N)} > 0`. -/
theorem second_harmonic_residual_explicit_strict_sign (κ : ℝ) (hκ : 0 < κ) (N : ℕ+)
    (hN : 2 ≤ N) :
    (∀ x : DGPS.ParticleSpace 1 N, secondHarmonicResidual κ N x =
      (8 * Real.pi ^ 2 * κ / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.Ioi i,
        (mode 2 (x i - x j)).im * ((mode 1 (x i)).im - (mode 1 (x j)).im)) ∧
    DGPS.IsSmoothPeriodicParticle (secondHarmonicResidual κ N) ∧
    (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
      secondHarmonicResidual κ N (DGPS.permuteParticles σ x) = secondHarmonicResidual κ N x) ∧
    (∃ x₀ : DGPS.ParticleSpace 1 N,
      x₀ (firstLabel N) = DGPS.torusLift (fun _ => (1 / 8 : ℝ)) ∧
      (∀ j, j ≠ firstLabel N → x₀ j = 0) ∧
      secondHarmonicResidual κ N x₀ =
        8 * Real.pi ^ 2 * κ / (N : ℝ) * ((((N : ℕ) : ℝ) - 1) * (Real.sqrt 2 / 2)) ∧
      0 < secondHarmonicResidual κ N x₀) ∧
    0 < ∫ x, (secondHarmonicResidual κ N x) ^ 2 ∂DGPS.particleLaw (secondHarmonicData κ) N := by
  have hres : secondHarmonicResidual κ N = explicitResidual κ N :=
    funext (secondHarmonicResidual_eq κ N)
  have hvalue : secondHarmonicResidual κ N (residualConfig N) =
      8 * Real.pi ^ 2 * κ / (N : ℝ) * ((((N : ℕ) : ℝ) - 1) * (Real.sqrt 2 / 2)) := by
    rw [hres, explicitResidual_config, mul_assoc]
  have hN' : (2 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have hpos : 0 < secondHarmonicResidual κ N (residualConfig N) := by
    rw [hvalue]
    have : (0 : ℝ) < (N : ℝ) := by positivity
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have h3 : (0 : ℝ) < ((N : ℕ) : ℝ) - 1 := by linarith
    positivity
  refine ⟨fun x => ?_, ?_, ?_, ⟨residualConfig N, ?_, ?_, hvalue, hpos⟩, ?_⟩
  · rw [secondHarmonicResidual_eq]; rfl
  · rw [hres]; exact isSmooth_explicitResidual κ N
  · intro σ x
    rw [hres]; exact explicitResidual_permute κ N σ x
  · simp [residualConfig]
  · intro j hj; simp [residualConfig, hj]
  · have hcont : Continuous (secondHarmonicResidual κ N) := by
      rw [hres]; exact continuous_explicitResidual κ N
    have : (DGPS.particleHaar 1 N).IsOpenPosMeasure := by
      unfold DGPS.particleHaar; infer_instance
    rw [DGPS.Particle.integral_particleLaw]
    have hd : Continuous (DGPS.particleDensity (secondHarmonicData κ) N) :=
      continuous_const.mul (Real.continuous_exp.comp
        (DGPS.Particle.particleHamiltonian_continuous (secondHarmonicData κ) N).neg)
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := residualConfig N) (hd.mul (hcont.pow 2)) (HasCompactSupport.of_compactSpace _)
      (fun x => mul_nonneg (DGPS.Particle.particleDensity_pos _ N x).le (sq_nonneg _)) ?_
    exact mul_ne_zero (DGPS.Particle.particleDensity_pos _ N _).ne' (pow_ne_zero 2 hpos.ne')

end DGPS.FiniteN
