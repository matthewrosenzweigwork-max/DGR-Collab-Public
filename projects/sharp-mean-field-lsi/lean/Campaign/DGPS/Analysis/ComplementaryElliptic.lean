import DGPS.Analysis.PeriodicHolder

/-!
# Complementary circle elliptic inverse (FOU018)

Circle `ℝ/ℤ` with angular coordinate `θ = 2π x`, so that `∂θ² = (2π)⁻² ∂x²`.  The operator
`∂θ² + 1` acts as `u ↦ (2π)⁻² u'' + u` and has multiplier `1 - n²` on the mode `n`.
`Q = {1, cos θ, sin θ}` and `PH.orthSub α k` is the closed subspace of `PH α k` orthogonal to `Q`.
-/

open Function Filter Topology

namespace DGPS.Analysis.ComplementaryElliptic

open DGPS.Analysis.PeriodicHolder

/-- The square `(2π)²` of the angular frequency. -/
noncomputable def kappa : ℝ := (2 * Real.pi) ^ 2

theorem kappa_pos : 0 < kappa := by unfold kappa; positivity

/-- The operator `∂θ² + 1` on functions of `x`, where `θ = 2π x`: `u ↦ κ⁻¹ u'' + u`. -/
noncomputable def ellFun (u : ℝ → ℝ) : ℝ → ℝ := kappa⁻¹ • deriv (deriv u) + u

section Operator

variable {α : ℝ} [HolderExponent α]

omit [HolderExponent α] in
theorem isPH_deriv_deriv {u : ℝ → ℝ} (h : IsPH α 2 u) : IsPH α 0 (deriv (deriv u)) := h.2.2.2.2

theorem isPH_of_two {u : ℝ → ℝ} (h : IsPH α 2 u) : IsPH α 0 u :=
  IsPH.of_succ (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le
    (IsPH.of_succ (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le h)

theorem isPH_ellFun {u : ℝ → ℝ} (h : IsPH α 2 u) : IsPH α 0 (ellFun u) :=
  (IsPH.smul _ (isPH_deriv_deriv h)).add (isPH_of_two h)

theorem phNorm_ellFun_le {u : ℝ → ℝ} (h : IsPH α 2 u) :
    phNorm α 0 (ellFun u) ≤ (kappa⁻¹ + 9) * phNorm α 2 u := by
  have hα0 := (HolderExponent.pos (α := α)).le
  have hα1 := (HolderExponent.lt_one (α := α)).le
  have h1 : IsPH α 1 u := IsPH.of_succ hα0 hα1 h
  have e1 : phNorm α 1 u ≤ 3 * phNorm α 2 u := phNorm_le_succ hα0 hα1 h
  have e2 : phNorm α 0 u ≤ 3 * phNorm α 1 u := phNorm_le_succ hα0 hα1 h1
  have e3 := phNorm_add_le (IsPH.smul kappa⁻¹ (isPH_deriv_deriv h)) (isPH_of_two h)
  have e4 := phNorm_smul_le kappa⁻¹ (isPH_deriv_deriv h)
  have hk : |kappa⁻¹| = kappa⁻¹ := abs_of_pos (inv_pos.mpr kappa_pos)
  have e5 : phNorm α 0 (deriv (deriv u)) ≤ phNorm α 2 u := by
    have := supNorm_nonneg u
    have := supNorm_nonneg (deriv u)
    simp only [phNorm]; linarith
  have e6 := phNorm_nonneg (α := α) 0 (deriv (deriv u))
  have e7 : 0 ≤ kappa⁻¹ := (inv_pos.mpr kappa_pos).le
  unfold ellFun
  rw [hk] at e4
  nlinarith

theorem deriv_add_fun {u v : ℝ → ℝ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) :
    deriv (u + v) = deriv u + deriv v := by
  ext x; exact deriv_add (hu x) (hv x)

theorem deriv_smul_fun {u : ℝ → ℝ} (c : ℝ) (hu : Differentiable ℝ u) :
    deriv (c • u) = c • deriv u := by
  ext x; exact deriv_const_smul c (hu x)

omit [HolderExponent α] in
theorem ellFun_add {u v : ℝ → ℝ} (hu : IsPH α 2 u) (hv : IsPH α 2 v) :
    ellFun (u + v) = ellFun u + ellFun v := by
  have h1 : deriv (u + v) = deriv u + deriv v := deriv_add_fun hu.2.1 hv.2.1
  have h2 : deriv (deriv u + deriv v) = deriv (deriv u) + deriv (deriv v) :=
    deriv_add_fun hu.2.2.2.1 hv.2.2.2.1
  unfold ellFun
  rw [h1, h2]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [HolderExponent α] in
theorem ellFun_smul {u : ℝ → ℝ} (c : ℝ) (hu : IsPH α 2 u) :
    ellFun (c • u) = c • ellFun u := by
  have h1 : deriv (c • u) = c • deriv u := deriv_smul_fun c hu.2.1
  have h2 : deriv (c • deriv u) = c • deriv (deriv u) := deriv_smul_fun c hu.2.2.2.1
  unfold ellFun
  rw [h1, h2]
  ext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The operator `∂θ² + 1 : C^{2,α} → C^{0,α}` as a bounded linear map. -/
noncomputable def ell : PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun u => PH.mk (ellFun u.val) (isPH_ellFun u.isPH)
      map_add' := fun u v => PH.ext (ellFun_add u.isPH v.isPH)
      map_smul' := fun c u => PH.ext (ellFun_smul c u.isPH) }
    (kappa⁻¹ + 9) (fun u => by
      show phNorm α 0 (ellFun u.val) ≤ (kappa⁻¹ + 9) * phNorm α 2 u.val
      exact phNorm_ellFun_le u.isPH)

theorem ell_val (u : PH α 2) : (ell u).val = ellFun u.val := rfl

end Operator

/-! ### Integration by parts and the Fourier multiplier of `∂θ² + 1` -/

section Fourier

variable {α : ℝ} [HolderExponent α]

/-- Integration by parts over one period for periodic `C¹` functions. -/
theorem ibp_periodic {f f1 g g1 : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f1 x) x)
    (hg : ∀ x, HasDerivAt g (g1 x) x) (hfp : Periodic f 1) (hgp : Periodic g 1)
    (hf1 : Continuous f1) (hg1 : Continuous g1) :
    ∫ x in (0 : ℝ)..1, f1 x * g x = -∫ x in (0 : ℝ)..1, f x * g1 x := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := f) (u' := f1)
    (v := g) (v' := g1) (fun x _ => hf x) (fun x _ => hg x)
    (hf1.intervalIntegrable _ _) (hg1.intervalIntegrable _ _)
  have e1 : f 1 = f 0 := by simpa using hfp 0
  have e2 : g 1 = g 0 := by simpa using hgp 0
  rw [e1, e2] at h
  have h' : ∫ x in (0 : ℝ)..1, f x * g1 x = -∫ x in (0 : ℝ)..1, f1 x * g x := by
    rw [h]; ring
  linarith

omit [HolderExponent α] in
theorem hasDerivAt_deriv_of_isPH {u : ℝ → ℝ} (h : IsPH α 2 u) (x : ℝ) :
    HasDerivAt u (deriv u x) x := (h.2.1 x).hasDerivAt

omit [HolderExponent α] in
theorem hasDerivAt_deriv_deriv_of_isPH {u : ℝ → ℝ} (h : IsPH α 2 u) (x : ℝ) :
    HasDerivAt (deriv u) (deriv (deriv u) x) x := (h.2.2.2.1 x).hasDerivAt

omit [HolderExponent α] in
/-- Multiplier identity: if `g'' = -μ g` with `g` periodic, then
`∫ (∂θ² + 1) u · g = (1 - μ/κ) ∫ u g`. -/
theorem integral_ellFun_mul {u g g1 : ℝ → ℝ} (hu : IsPH α 2 u) {μ : ℝ}
    (hg : ∀ x, HasDerivAt g (g1 x) x) (hg1 : ∀ x, HasDerivAt g1 (-μ * g x) x)
    (hgp : Periodic g 1) (hg1p : Periodic g1 1) (hgc : Continuous g) (hg1c : Continuous g1) :
    ∫ x in (0 : ℝ)..1, ellFun u x * g x = (1 - μ / kappa) * ∫ x in (0 : ℝ)..1, u x * g x := by
  have hu1c : Continuous (deriv u) := hu.2.2.2.1.continuous
  have hu2c : Continuous (deriv (deriv u)) := (isPH_deriv_deriv hu).continuous
  have hup : Periodic u 1 := hu.1
  have hu1p : Periodic (deriv u) 1 := hu.2.2.1
  have i1 := ibp_periodic (hasDerivAt_deriv_deriv_of_isPH hu) hg hu1p hgp hu2c hg1c
  have i2 := ibp_periodic (hasDerivAt_deriv_of_isPH hu) hg1 hup hg1p hu1c
    (by fun_prop : Continuous fun x => -μ * g x)
  have i3 : ∫ x in (0 : ℝ)..1, u x * (-μ * g x) = -μ * ∫ x in (0 : ℝ)..1, u x * g x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  have hI2 : ∫ x in (0 : ℝ)..1, deriv (deriv u) x * g x =
      -μ * ∫ x in (0 : ℝ)..1, u x * g x := by
    rw [i1, i2, i3]; ring
  have a1 : IntervalIntegrable (fun x => kappa⁻¹ * (deriv (deriv u) x * g x))
      MeasureTheory.volume 0 1 := ((hu2c.mul hgc).const_mul _).intervalIntegrable _ _
  have a2 : IntervalIntegrable (fun x => u x * g x) MeasureTheory.volume 0 1 :=
    (hu.continuous.mul hgc).intervalIntegrable _ _
  have hint : ∫ x in (0 : ℝ)..1, ellFun u x * g x =
      ∫ x in (0 : ℝ)..1, (kappa⁻¹ * (deriv (deriv u) x * g x) + u x * g x) :=
    intervalIntegral.integral_congr fun x _ => by
      simp only [ellFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  rw [hint, intervalIntegral.integral_add a1 a2, intervalIntegral.integral_const_mul, hI2]
  have hk : kappa ≠ 0 := kappa_pos.ne'
  field_simp
  ring

omit [HolderExponent α] in
theorem integral_ellFun_trig {u : ℝ → ℝ} (hu : IsPH α 2 u) (n : ℕ) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, ellFun u x * trigFun n a b x =
      (1 - (n : ℝ) ^ 2) * ∫ x in (0 : ℝ)..1, u x * trigFun n a b x := by
  have hμ : (1 : ℝ) - (2 * Real.pi * n) ^ 2 / kappa = 1 - (n : ℝ) ^ 2 := by
    unfold kappa
    have : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [← hμ]
  refine integral_ellFun_mul hu (μ := (2 * Real.pi * n) ^ 2) (g := trigFun n a b)
    (g1 := trigFun n (b * (2 * Real.pi * n)) (-(a * (2 * Real.pi * n)))) (fun x => ?_)
    (fun x => ?_) (trigFun_periodic n a b) (trigFun_periodic _ _ _) (trigFun_continuous n a b)
    (trigFun_continuous _ _ _)
  · exact trigFun_hasDerivAt n a b x
  · refine (trigFun_hasDerivAt n _ _ x).congr_deriv ?_
    simp only [trigFun]; ring

theorem cosCoeff_ell (n : ℕ) (u : PH α 2) :
    PH.cosCoeff 0 n (ell u) = (1 - (n : ℝ) ^ 2) * PH.cosCoeff 2 n u := by
  rw [PH.cosCoeff_apply, PH.cosCoeff_apply, ell_val]
  have h := integral_ellFun_trig u.isPH n 1 0
  have e : trigFun n 1 0 = fun x => Real.cos (2 * Real.pi * n * x) := by
    funext x; simp [trigFun]
  rw [e] at h
  exact h

theorem sinCoeff_ell (n : ℕ) (u : PH α 2) :
    PH.sinCoeff 0 n (ell u) = (1 - (n : ℝ) ^ 2) * PH.sinCoeff 2 n u := by
  rw [PH.sinCoeff_apply, PH.sinCoeff_apply, ell_val]
  have h := integral_ellFun_trig u.isPH n 0 1
  have e : trigFun n 0 1 = fun x => Real.sin (2 * Real.pi * n * x) := by
    funext x; simp [trigFun]
  rw [e] at h
  exact h

theorem integral_ell (u : PH α 2) : PH.integral 0 (ell u) = PH.integral 2 u := by
  have h0 : ∀ (k : ℕ) (f : PH α k), PH.cosCoeff k 0 f = PH.integral k f := fun k f => by
    simp [PH.cosCoeff_apply, PH.integral_apply]
  rw [← h0, ← h0, cosCoeff_ell]
  simp

theorem cosCoeff_one_ell (u : PH α 2) : PH.cosCoeff 0 1 (ell u) = 0 := by
  rw [cosCoeff_ell]; simp

theorem sinCoeff_one_ell (u : PH α 2) : PH.sinCoeff 0 1 (ell u) = 0 := by
  rw [sinCoeff_ell]; simp

theorem ell_mem_orthSub {u : PH α 2} (hu : u ∈ PH.orthSub α 2) : ell u ∈ PH.orthSub α 0 :=
  ⟨by rw [integral_ell]; exact hu.1, cosCoeff_one_ell u, sinCoeff_one_ell u⟩

/-- `∂θ² + 1` restricted to `Q`-orthogonal functions, `C^{2,α}_Q → C^{0,α}_Q`. -/
noncomputable def ellOrth : PH.orthSub α 2 →L[ℝ] PH.orthSub α 0 :=
  (ell.comp (PH.orthSub α 2).subtypeL).codRestrict (PH.orthSub α 0) fun u => ell_mem_orthSub u.2

end Fourier

/-! ### Injectivity: the kernel of `∂θ² + 1` is spanned by `cos`, `sin` -/

section Kernel

variable {α : ℝ} [HolderExponent α]

/-- Uniqueness for `u'' = -κ u` via the conserved energy. -/
theorem ode_unique {u u1 T T1 : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u1 x) x)
    (hu1 : ∀ x, HasDerivAt u1 (-kappa * u x) x) (hT : ∀ x, HasDerivAt T (T1 x) x)
    (hT1 : ∀ x, HasDerivAt T1 (-kappa * T x) x) (h0 : u 0 = T 0) (h1 : u1 0 = T1 0) :
    u = T := by
  have hE : ∀ x, HasDerivAt (fun x => (u1 x - T1 x) ^ 2 + kappa * (u x - T x) ^ 2) 0 x := by
    intro x
    have a := (((hu1 x).sub (hT1 x)).pow 2).add ((((hu x).sub (hT x)).pow 2).const_mul kappa)
    refine a.congr_deriv ?_
    simp only [Nat.cast_ofNat, Pi.sub_apply]
    ring
  have hconst : ∀ x, (u1 x - T1 x) ^ 2 + kappa * (u x - T x) ^ 2 =
      (u1 0 - T1 0) ^ 2 + kappa * (u 0 - T 0) ^ 2 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hE y).differentiableAt) (fun y => (hE y).deriv) x 0
  funext x
  have h := hconst x
  rw [h0, h1] at h
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero] at h
  have hk := kappa_pos
  have : kappa * (u x - T x) ^ 2 = 0 := by nlinarith [sq_nonneg (u1 x - T1 x), sq_nonneg (u x - T x)]
  have h2 : (u x - T x) ^ 2 = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk.ne'
    · exact h
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
  linarith

theorem integral_cos_sq_mul_comb (A B : ℝ) :
    ∫ x in (0 : ℝ)..1, (A * Real.cos (2 * Real.pi * x) ^ 2 +
      B * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x))) = A / 2 := by
  have hc : Continuous fun x : ℝ => Real.cos (2 * Real.pi * x) := by fun_prop
  have hs : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) := by fun_prop
  have := int_comb3 (p := fun x => Real.cos (2 * Real.pi * x) ^ 2)
    (q := fun x => Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x))
    (r := fun _ => (0 : ℝ)) (hc.pow 2) (hs.mul hc) continuous_const A B 0
  simp only [zero_mul, add_zero, mul_zero] at this
  rw [this, int_cos_sq, int_sin_mul_cos]
  ring

theorem integral_sin_sq_mul_comb (A B : ℝ) :
    ∫ x in (0 : ℝ)..1, (A * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) +
      B * Real.sin (2 * Real.pi * x) ^ 2) = B / 2 := by
  have hc : Continuous fun x : ℝ => Real.cos (2 * Real.pi * x) := by fun_prop
  have hs : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) := by fun_prop
  have := int_comb3 (p := fun x => Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x))
    (q := fun x => Real.sin (2 * Real.pi * x) ^ 2)
    (r := fun _ => (0 : ℝ)) (hs.mul hc) (hs.pow 2) continuous_const A B 0
  simp only [zero_mul, add_zero, mul_zero] at this
  rw [this, int_sin_mul_cos, int_sin_sq]
  ring

theorem eq_zero_of_ell_eq_zero {u : PH α 2} (h : ell u = 0) (hu : u ∈ PH.orthSub α 2) :
    u = 0 := by
  have hz : ∀ x, deriv (deriv u.val) x = -kappa * u.val x := by
    intro x
    have h1 := congrFun (congrArg PH.val h) x
    simp only [ell_val, ellFun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, PH.val_zero,
      Pi.zero_apply] at h1
    have hk : kappa ≠ 0 := kappa_pos.ne'
    field_simp at h1
    linarith
  set A := u.val 0 with hA
  set B := deriv u.val 0 / (2 * Real.pi) with hB
  have hT : ∀ x, HasDerivAt (trigFun 1 A B) (trigFun 1 (B * (2 * Real.pi * (1 : ℕ)))
      (-(A * (2 * Real.pi * (1 : ℕ)))) x) x := fun x => trigFun_hasDerivAt 1 A B x
  have hT1 : ∀ x, HasDerivAt (trigFun 1 (B * (2 * Real.pi * (1 : ℕ)))
      (-(A * (2 * Real.pi * (1 : ℕ))))) (-kappa * trigFun 1 A B x) x := by
    intro x
    refine (trigFun_hasDerivAt 1 _ _ x).congr_deriv ?_
    simp only [trigFun, kappa, Nat.cast_one]
    ring
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq : u.val = trigFun 1 A B := by
    refine ode_unique (u := u.val) (u1 := deriv u.val) (hasDerivAt_deriv_of_isPH u.isPH)
      (fun x => by simpa [hz x] using hasDerivAt_deriv_deriv_of_isPH u.isPH x) hT hT1 ?_ ?_
    · simp [trigFun, hA]
    · simp only [trigFun, hB, Nat.cast_one, mul_one, Real.cos_zero, Real.sin_zero, mul_zero,
        add_zero]
      field_simp
  have hc := hu.2.1
  have hs := hu.2.2
  rw [PH.cosCoeff_apply] at hc
  rw [PH.sinCoeff_apply] at hs
  have eA : A / 2 = 0 := by
    have hi : ∫ x in (0 : ℝ)..1, (A * Real.cos (2 * Real.pi * x) ^ 2 +
        B * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x))) =
        ∫ x in (0 : ℝ)..1, u.val x * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [heq, trigFun, Nat.cast_one, mul_one]
      ring
    rw [integral_cos_sq_mul_comb, hc] at hi
    exact hi
  have eB : B / 2 = 0 := by
    have hi : ∫ x in (0 : ℝ)..1, (A * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) +
        B * Real.sin (2 * Real.pi * x) ^ 2) =
        ∫ x in (0 : ℝ)..1, u.val x * Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [heq, trigFun, Nat.cast_one, mul_one]
      ring
    rw [integral_sin_sq_mul_comb, hs] at hi
    exact hi
  have hA0 : A = 0 := by linarith
  have hB0 : B = 0 := by linarith
  refine PH.ext ?_
  rw [heq, hA0, hB0]
  funext x
  simp [trigFun]

end Kernel

/-! ### Surjectivity: variation of constants -/

section Surj

variable {α : ℝ} [HolderExponent α]

/-- Cumulative cosine integral `∫₀ˣ f(t) cos(2π t) dt`. -/
noncomputable def cumC (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t * Real.cos (2 * Real.pi * t)

/-- Cumulative sine integral `∫₀ˣ f(t) sin(2π t) dt`. -/
noncomputable def cumS (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, f t * Real.sin (2 * Real.pi * t)

/-- Particular solution `2π ∫₀ˣ sin(2π(x-t)) f(t) dt` of `u'' + κ u = κ f`. -/
noncomputable def upFun (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * Real.pi * (Real.sin (2 * Real.pi * x) * cumC f x - Real.cos (2 * Real.pi * x) * cumS f x)

/-- The derivative of `upFun f`. -/
noncomputable def up1Fun (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  kappa * (Real.cos (2 * Real.pi * x) * cumC f x + Real.sin (2 * Real.pi * x) * cumS f x)

theorem hasDerivAt_cumC {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (cumC f) (f x * Real.cos (2 * Real.pi * x)) x :=
  (Continuous.integral_hasStrictDerivAt (hf.mul (by fun_prop)) 0 x).hasDerivAt

theorem hasDerivAt_cumS {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (cumS f) (f x * Real.sin (2 * Real.pi * x)) x :=
  (Continuous.integral_hasStrictDerivAt (hf.mul (by fun_prop)) 0 x).hasDerivAt

theorem hasDerivAt_sin_two_pi (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (2 * Real.pi * x)) (2 * Real.pi * Real.cos (2 * Real.pi * x)) x := by
  have h : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  exact h.sin.congr_deriv (by ring)

theorem hasDerivAt_cos_two_pi (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x)) (-(2 * Real.pi * Real.sin (2 * Real.pi * x))) x := by
  have h : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi)
  exact h.cos.congr_deriv (by ring)

theorem hasDerivAt_upFun {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (upFun f) (up1Fun f x) x := by
  have h := (((hasDerivAt_sin_two_pi x).mul (hasDerivAt_cumC hf x)).sub
    ((hasDerivAt_cos_two_pi x).mul (hasDerivAt_cumS hf x))).const_mul (2 * Real.pi)
  refine h.congr_deriv ?_
  simp only [up1Fun, kappa]
  ring

theorem hasDerivAt_up1Fun {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (up1Fun f) (-kappa * upFun f x + kappa * f x) x := by
  have h := (((hasDerivAt_cos_two_pi x).mul (hasDerivAt_cumC hf x)).add
    ((hasDerivAt_sin_two_pi x).mul (hasDerivAt_cumS hf x))).const_mul kappa
  refine h.congr_deriv ?_
  have := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  simp only [upFun]
  linear_combination (kappa * f x) * this

theorem periodic_cum {g : ℝ → ℝ} (hg : Continuous g) (hp : Periodic g 1)
    (h1 : ∫ t in (0 : ℝ)..1, g t = 0) : Periodic (fun x => ∫ t in (0 : ℝ)..x, g t) 1 := by
  intro x
  have h := hp.intervalIntegral_add_eq x 0
  have h2 := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume) (a := 0) (b := x) (c := x + 1)
    (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  simp only [zero_add] at h
  show ∫ t in (0 : ℝ)..(x + 1), g t = ∫ t in (0 : ℝ)..x, g t
  rw [← h2, h, h1, add_zero]

theorem periodic_mul_cos {f : ℝ → ℝ} (hp : Periodic f 1) :
    Periodic (fun t => f t * Real.cos (2 * Real.pi * t)) 1 := by
  intro x
  have h : Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x) := by
    rw [mul_add, mul_one, Real.cos_add_two_pi]
  simp only [hp x, h]

theorem periodic_mul_sin {f : ℝ → ℝ} (hp : Periodic f 1) :
    Periodic (fun t => f t * Real.sin (2 * Real.pi * t)) 1 := by
  intro x
  have h : Real.sin (2 * Real.pi * (x + 1)) = Real.sin (2 * Real.pi * x) := by
    rw [mul_add, mul_one, Real.sin_add_two_pi]
  simp only [hp x, h]

theorem periodic_sin_two_pi : Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  show Real.sin (2 * Real.pi * (x + 1)) = Real.sin (2 * Real.pi * x)
  rw [mul_add, mul_one, Real.sin_add_two_pi]

theorem periodic_cos_two_pi : Periodic (fun x : ℝ => Real.cos (2 * Real.pi * x)) 1 := by
  intro x
  show Real.cos (2 * Real.pi * (x + 1)) = Real.cos (2 * Real.pi * x)
  rw [mul_add, mul_one, Real.cos_add_two_pi]

theorem isPH_upFun {f : ℝ → ℝ} (hf : IsPH α 0 f) (hc : ∫ t in (0 : ℝ)..1, f t * Real.cos (2 * Real.pi * t) = 0)
    (hs : ∫ t in (0 : ℝ)..1, f t * Real.sin (2 * Real.pi * t) = 0) : IsPH α 2 (upFun f) := by
  have hfc : Continuous f := hf.2.1
  have hC : Periodic (cumC f) 1 :=
    periodic_cum (hfc.mul (by fun_prop)) (periodic_mul_cos hf.1) hc
  have hS : Periodic (cumS f) 1 :=
    periodic_cum (hfc.mul (by fun_prop)) (periodic_mul_sin hf.1) hs
  have hup : Periodic (upFun f) 1 := by
    intro x
    simp only [upFun, hC x, hS x, periodic_sin_two_pi x, periodic_cos_two_pi x]
  have hup1 : Periodic (up1Fun f) 1 := by
    intro x
    simp only [up1Fun, hC x, hS x, periodic_sin_two_pi x, periodic_cos_two_pi x]
  have hd : deriv (upFun f) = up1Fun f := funext fun x => (hasDerivAt_upFun hfc x).deriv
  have hd1 : deriv (up1Fun f) = (-kappa) • upFun f + kappa • f := funext fun x => by
    simpa using (hasDerivAt_up1Fun hfc x).deriv
  have hdiff : Differentiable ℝ (upFun f) := fun x => (hasDerivAt_upFun hfc x).differentiableAt
  have hdiff1 : Differentiable ℝ (up1Fun f) := fun x => (hasDerivAt_up1Fun hfc x).differentiableAt
  have hcont1 : Continuous (up1Fun f) := hdiff1.continuous
  have h0 : IsPH α 0 (upFun f) :=
    isPH_zero_of_lip (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le hup hdiff
      (by rw [hd]; exact periodic_bdd hup1 hcont1)
  refine ⟨hup, hdiff, ?_⟩
  rw [hd]
  refine ⟨hup1, hdiff1, ?_⟩
  rw [hd1]
  exact (IsPH.smul _ h0).add (IsPH.smul _ hf)

omit [HolderExponent α] in
theorem ellFun_upFun {f : ℝ → ℝ} (hfc : Continuous f) : ellFun (upFun f) = f := by
  funext x
  have hd : deriv (upFun f) = up1Fun f := funext fun x => (hasDerivAt_upFun hfc x).deriv
  have hd1 := (hasDerivAt_up1Fun hfc x).deriv
  have hk : kappa ≠ 0 := kappa_pos.ne'
  simp only [ellFun, hd, hd1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

end Surj

/-! ### The isomorphism `∂θ² + 1 : C^{2,α}_Q → C^{0,α}_Q` -/

section Equiv

variable {α : ℝ} [HolderExponent α]

omit [HolderExponent α] in
theorem ellFun_const_add_trig (I a b : ℝ) :
    ellFun (fun x => I + trigFun 1 a b x) = fun _ => I := by
  have h1 : deriv (fun x => I + trigFun 1 a b x) =
      trigFun 1 (b * (2 * Real.pi * ((1 : ℕ) : ℝ))) (-(a * (2 * Real.pi * ((1 : ℕ) : ℝ)))) :=
    funext fun x => ((trigFun_hasDerivAt 1 a b x).const_add I).deriv
  have h2 := trigFun_deriv 1 (b * (2 * Real.pi * ((1 : ℕ) : ℝ))) (-(a * (2 * Real.pi * ((1 : ℕ) : ℝ))))
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  funext x
  simp only [ellFun, h1, h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [trigFun, kappa, Nat.cast_one]
  field_simp
  ring

theorem ell_modeProj01 (w : PH α 2) :
    (ell (PH.modeProj 2 {0, 1} w)).val = fun _ => PH.integral 2 w := by
  have h : (PH.modeProj 2 {0, 1} w).val = fun x => PH.integral 2 w +
      trigFun 1 (2 * PH.cosCoeff 2 1 w) (2 * PH.sinCoeff 2 1 w) x := by
    funext x
    rw [PH.modeProj01_val]
    simp only [trigFun, Nat.cast_one, mul_one]
    ring
  rw [ell_val, h]
  exact ellFun_const_add_trig _ _ _

theorem exists_preimage {f : PH α 0} (hf : f ∈ PH.orthSub α 0) :
    ∃ v ∈ PH.orthSub α 2, ell v = f := by
  have hc : ∫ t in (0 : ℝ)..1, f.val t * Real.cos (2 * Real.pi * t) = 0 := by
    have := hf.2.1
    rw [PH.cosCoeff_apply] at this
    simpa using this
  have hs : ∫ t in (0 : ℝ)..1, f.val t * Real.sin (2 * Real.pi * t) = 0 := by
    have := hf.2.2
    rw [PH.sinCoeff_apply] at this
    simpa using this
  let w : PH α 2 := PH.mk (upFun f.val) (isPH_upFun f.isPH hc hs)
  have hw : ell w = f := PH.ext (ellFun_upFun f.isPH.continuous)
  have hI : PH.integral 2 w = 0 := by
    rw [← integral_ell, hw]; exact hf.1
  refine ⟨w - PH.modeProj 2 {0, 1} w, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := PH.modeProj01_orth w
    refine ⟨?_, ?_, ?_⟩
    · rw [map_sub, a, sub_self]
    · rw [map_sub, b, sub_self]
    · rw [map_sub, c, sub_self]
  · have h0 : ell (PH.modeProj 2 {0, 1} w) = 0 := PH.ext (by rw [ell_modeProj01, hI]; rfl)
    rw [map_sub, h0, hw, sub_zero]

theorem ellOrth_apply (u : PH.orthSub α 2) : ((ellOrth u : PH.orthSub α 0) : PH α 0) = ell u.1 := rfl

theorem ellOrth_injective : Function.Injective (ellOrth (α := α)) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h : ell u.1 = 0 := by
    rw [← ellOrth_apply, hu]; rfl
  exact Subtype.ext (eq_zero_of_ell_eq_zero h u.2)

theorem ellOrth_surjective : Function.Surjective (ellOrth (α := α)) := fun f => by
  obtain ⟨v, hv, h⟩ := exists_preimage f.2
  exact ⟨⟨v, hv⟩, Subtype.ext h⟩

instance completeSpace_orthSub (k : ℕ) : CompleteSpace (PH.orthSub α k) :=
  (PH.isClosed_orthSub (α := α) k).completeSpace_coe

/-- `∂θ² + 1 : C^{2,α}_Q → C^{0,α}_Q` as a continuous linear equivalence. -/
noncomputable def ellEquiv : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0 :=
  ContinuousLinearEquiv.ofBijective ellOrth
    (LinearMap.ker_eq_bot.2 ellOrth_injective)
    (LinearMap.range_eq_top.2 ellOrth_surjective)

theorem ellEquiv_apply (u : PH.orthSub α 2) : (ellEquiv u : PH α 0) = ell u.1 := rfl

/-- The inverse `C^{0,α}_Q → C^{2,α}_Q` of `∂θ² + 1`. -/
noncomputable def ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2 :=
  (ellEquiv (α := α)).symm.toContinuousLinearMap

theorem ellInv_apply (f : PH.orthSub α 0) : ellInv f = (ellEquiv (α := α)).symm f := rfl

theorem ell_ellInv (f : PH.orthSub α 0) : ell (ellInv f).1 = f.1 := by
  have := congrArg Subtype.val ((ellEquiv (α := α)).apply_symm_apply f)
  rw [ellEquiv_apply] at this
  rw [ellInv_apply]
  exact this

theorem ellInv_ell (u : PH.orthSub α 2) : ellInv (ellOrth u) = u :=
  (ellEquiv (α := α)).symm_apply_apply u

/-- The Fourier coefficients of the inverse: `û(n) = f̂(n) / (1 - n²)` for `n ≥ 2`. -/
theorem ellInv_coeff (f : PH.orthSub α 0) {n : ℕ} (hn : 2 ≤ n) :
    PH.cosCoeff 2 n (ellInv f).1 = PH.cosCoeff 0 n f.1 / (1 - (n : ℝ) ^ 2) ∧
    PH.sinCoeff 2 n (ellInv f).1 = PH.sinCoeff 0 n f.1 / (1 - (n : ℝ) ^ 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (1 : ℝ) - (n : ℝ) ^ 2 ≠ 0 := by nlinarith
  have h := ell_ellInv f
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hne, ← h, cosCoeff_ell]; ring
  · rw [eq_div_iff hne, ← h, sinCoeff_ell]; ring

end Equiv

/-! ### Fourier modes: eigenfunctions and orthogonality -/

section Modes

variable {α : ℝ} [HolderExponent α]

theorem ellFun_trigFun (n : ℕ) (a b : ℝ) :
    ellFun (trigFun n a b) = (1 - (n : ℝ) ^ 2) • trigFun n a b := by
  have h1 := trigFun_deriv n a b
  have h2 := trigFun_deriv n (b * (2 * Real.pi * n)) (-(a * (2 * Real.pi * n)))
  have hpi := Real.pi_ne_zero
  funext x
  simp only [ellFun, h1, h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [trigFun, kappa]
  field_simp
  ring

omit [HolderExponent α] in
/-- Distinct Fourier modes are orthogonal. -/
theorem integral_trig_trig {n n' : ℕ} (h : n ≠ n') (a b c d : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x * trigFun n' c d x = 0 := by
  have : HolderExponent (1 / 2 : ℝ) := ⟨by norm_num, by norm_num⟩
  have hu : IsPH (1 / 2 : ℝ) 2 (trigFun n a b) := isPH_trigFun n 2 a b
  have key := integral_ellFun_trig hu n' c d
  rw [ellFun_trigFun] at key
  simp only [Pi.smul_apply, smul_eq_mul] at key
  have e : ∫ x in (0 : ℝ)..1, (1 - (n : ℝ) ^ 2) * trigFun n a b x * trigFun n' c d x =
      (1 - (n : ℝ) ^ 2) * ∫ x in (0 : ℝ)..1, trigFun n a b x * trigFun n' c d x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by ring
  rw [e] at key
  have hne : (n : ℝ) ^ 2 ≠ (n' : ℝ) ^ 2 := by
    intro h'
    exact h (by exact_mod_cast (sq_eq_sq₀ (Nat.cast_nonneg n) (Nat.cast_nonneg n')).1 h')
  have : ((n' : ℝ) ^ 2 - (n : ℝ) ^ 2) * ∫ x in (0 : ℝ)..1, trigFun n a b x * trigFun n' c d x = 0 := by
    linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd (by linarith) hne
  · exact h0

theorem integral_trig_const {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x = 0 := by
  have h := integral_trig_trig hn a b 1 0
  have e : trigFun 0 1 0 = fun _ => (1 : ℝ) := by funext x; simp [trigFun]
  rw [e] at h
  simpa using h

theorem integral_trig_cos_one {n : ℕ} (hn : n ≠ 1) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) = 0 := by
  have h := integral_trig_trig hn a b 1 0
  have e : trigFun 1 1 0 = fun x => Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x) := by
    funext x; simp [trigFun]
  rw [e] at h
  exact h

theorem integral_trig_sin_one {n : ℕ} (hn : n ≠ 1) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x * Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x) = 0 := by
  have h := integral_trig_trig hn a b 0 1
  have e : trigFun 1 0 1 = fun x => Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x) := by
    funext x; simp [trigFun]
  rw [e] at h
  exact h

theorem int_cos_nat {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * m * x) = 0 := by
  have hc : (2 * Real.pi * m) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.cos u) hc
  rw [this]
  have hs : Real.sin (2 * Real.pi * m) = 0 := by
    have := Real.sin_nat_mul_pi (2 * m)
    rw [show ((2 * m : ℕ) : ℝ) * Real.pi = 2 * Real.pi * m by push_cast; ring] at this
    exact this
  simp [integral_cos, hs]

theorem int_sin_nat {m : ℕ} (hm : m ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * m * x) = 0 := by
  have hc : (2 * Real.pi * m) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sin u) hc
  rw [this]
  have hs : Real.cos (2 * Real.pi * m) = 1 := by
    have := Real.cos_nat_mul_two_pi m
    rw [show (m : ℝ) * (2 * Real.pi) = 2 * Real.pi * m by ring] at this
    exact this
  simp [integral_sin, hs]

theorem int_cos_sq_nat {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * n * x) ^ 2 = 1 / 2 := by
  have hm : 2 * n ≠ 0 := by omega
  have e : ∀ x : ℝ, Real.cos (2 * Real.pi * n * x) ^ 2 =
      1 / 2 + (1 / 2) * Real.cos (2 * Real.pi * ((2 * n : ℕ) : ℝ) * x) := fun x => by
    rw [Real.cos_sq]
    push_cast
    ring_nf
  have hcont : Continuous fun x : ℝ => Real.cos (2 * Real.pi * ((2 * n : ℕ) : ℝ) * x) := by
    fun_prop
  rw [intervalIntegral.integral_congr (fun x _ => e x),
    intervalIntegral.integral_add (by simp) ((hcont.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, int_cos_nat hm]
  simp

theorem int_sin_sq_nat {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * n * x) ^ 2 = 1 / 2 := by
  have hm : 2 * n ≠ 0 := by omega
  have e : ∀ x : ℝ, Real.sin (2 * Real.pi * n * x) ^ 2 =
      1 / 2 - (1 / 2) * Real.cos (2 * Real.pi * ((2 * n : ℕ) : ℝ) * x) := fun x => by
    rw [Real.sin_sq_eq_half_sub]
    push_cast
    ring_nf
  have hcont : Continuous fun x : ℝ => Real.cos (2 * Real.pi * ((2 * n : ℕ) : ℝ) * x) := by
    fun_prop
  rw [intervalIntegral.integral_congr (fun x _ => e x),
    intervalIntegral.integral_sub (by simp) ((hcont.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, int_cos_nat hm]
  simp

theorem int_sin_mul_cos_nat {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x) = 0 := by
  have hm : 2 * n ≠ 0 := by omega
  have e : ∀ x : ℝ, Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x) =
      (1 / 2) * Real.sin (2 * Real.pi * ((2 * n : ℕ) : ℝ) * x) := fun x => by
    have := Real.sin_two_mul (2 * Real.pi * n * x)
    push_cast
    rw [show 2 * Real.pi * (2 * (n : ℝ)) * x = 2 * (2 * Real.pi * n * x) by ring, this]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => e x), intervalIntegral.integral_const_mul,
    int_sin_nat hm]
  simp

theorem integral_trig_cos_self {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x * Real.cos (2 * Real.pi * n * x) = a / 2 := by
  have hc : Continuous fun x : ℝ => Real.cos (2 * Real.pi * n * x) := by fun_prop
  have hs : Continuous fun x : ℝ => Real.sin (2 * Real.pi * n * x) := by fun_prop
  have h := int_comb3 (p := fun x => Real.cos (2 * Real.pi * n * x) ^ 2)
    (q := fun x => Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x))
    (r := fun _ => (0 : ℝ)) (hc.pow 2) (hs.mul hc) continuous_const a b 0
  simp only [zero_mul, add_zero, mul_zero] at h
  rw [int_cos_sq_nat hn, int_sin_mul_cos_nat hn] at h
  have e : ∀ x : ℝ, trigFun n a b x * Real.cos (2 * Real.pi * n * x) =
      a * Real.cos (2 * Real.pi * n * x) ^ 2 +
        b * (Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x)) := fun x => by
    simp only [trigFun]; ring
  rw [intervalIntegral.integral_congr (fun x _ => e x), h]
  ring

theorem integral_trig_sin_self {n : ℕ} (hn : n ≠ 0) (a b : ℝ) :
    ∫ x in (0 : ℝ)..1, trigFun n a b x * Real.sin (2 * Real.pi * n * x) = b / 2 := by
  have hc : Continuous fun x : ℝ => Real.cos (2 * Real.pi * n * x) := by fun_prop
  have hs : Continuous fun x : ℝ => Real.sin (2 * Real.pi * n * x) := by fun_prop
  have h := int_comb3 (p := fun x => Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x))
    (q := fun x => Real.sin (2 * Real.pi * n * x) ^ 2)
    (r := fun _ => (0 : ℝ)) (hs.mul hc) (hs.pow 2) continuous_const a b 0
  simp only [zero_mul, add_zero, mul_zero] at h
  rw [int_sin_sq_nat hn, int_sin_mul_cos_nat hn] at h
  have e : ∀ x : ℝ, trigFun n a b x * Real.sin (2 * Real.pi * n * x) =
      a * (Real.sin (2 * Real.pi * n * x) * Real.cos (2 * Real.pi * n * x)) +
        b * Real.sin (2 * Real.pi * n * x) ^ 2 := fun x => by
    simp only [trigFun]; ring
  rw [intervalIntegral.integral_congr (fun x _ => e x), h]
  ring

end Modes

/-! ### Mode maps and the perturbed operator -/

section Perturb

variable {α : ℝ} [HolderExponent α]

/-- The `n`-th Fourier mode of a `C^{k,α}` function, viewed in `C^{k',α}`. -/
noncomputable def modeMap (k k' n : ℕ) : PH α k →L[ℝ] PH α k' :=
  (modeWeight n • PH.cosCoeff k n).smulRight (PH.trig k' n 1 0) +
    (modeWeight n • PH.sinCoeff k n).smulRight (PH.trig k' n 0 1)

theorem modeMap_val {k k' : ℕ} (n : ℕ) (f : PH α k) (x : ℝ) :
    (modeMap k k' n f).val x =
      trigFun n (modeWeight n * PH.cosCoeff k n f) (modeWeight n * PH.sinCoeff k n f) x := by
  simp [modeMap, trigFun]

theorem cosCoeff_eq_trig {k : ℕ} (m : ℕ) (f : PH α k) :
    PH.cosCoeff k m f = ∫ x in (0 : ℝ)..1, f.val x * trigFun m 1 0 x := by
  rw [PH.cosCoeff_apply]
  exact intervalIntegral.integral_congr fun x _ => by simp [trigFun]

theorem sinCoeff_eq_trig {k : ℕ} (m : ℕ) (f : PH α k) :
    PH.sinCoeff k m f = ∫ x in (0 : ℝ)..1, f.val x * trigFun m 0 1 x := by
  rw [PH.sinCoeff_apply]
  exact intervalIntegral.integral_congr fun x _ => by simp [trigFun]

theorem integral_eq_cosCoeff_zero {k : ℕ} (f : PH α k) : PH.integral k f = PH.cosCoeff k 0 f := by
  simp [PH.cosCoeff_apply, PH.integral_apply]

theorem modeWeight_ne_zero {n : ℕ} (hn : n ≠ 0) : modeWeight n = 2 := by
  simp [modeWeight, hn]

theorem cosCoeff_modeMap {k k' : ℕ} {n : ℕ} (hn : n ≠ 0) (m : ℕ) (f : PH α k) :
    PH.cosCoeff k' m (modeMap k k' n f) = if m = n then PH.cosCoeff k n f else 0 := by
  by_cases h : m = n
  · subst h
    rw [PH.cosCoeff_apply]; simp only [↓reduceIte]
    simp only [modeMap_val]
    rw [integral_trig_cos_self hn, modeWeight_ne_zero hn]
    ring
  · simp only [h, ↓reduceIte]; rw [cosCoeff_eq_trig]
    simp only [modeMap_val]
    exact integral_trig_trig (Ne.symm h) _ _ 1 0

theorem sinCoeff_modeMap {k k' : ℕ} {n : ℕ} (hn : n ≠ 0) (m : ℕ) (f : PH α k) :
    PH.sinCoeff k' m (modeMap k k' n f) = if m = n then PH.sinCoeff k n f else 0 := by
  by_cases h : m = n
  · subst h
    rw [PH.sinCoeff_apply]; simp only [↓reduceIte]
    simp only [modeMap_val]
    rw [integral_trig_sin_self hn, modeWeight_ne_zero hn]
    ring
  · simp only [h, ↓reduceIte]; rw [sinCoeff_eq_trig]
    simp only [modeMap_val]
    exact integral_trig_trig (Ne.symm h) _ _ 0 1

theorem modeMap_comp {k k' k'' : ℕ} {n : ℕ} (hn : n ≠ 0) (n' : ℕ) (f : PH α k) :
    modeMap k' k'' n' (modeMap k k' n f) = if n' = n then modeMap k k'' n f else 0 := by
  by_cases h : n' = n
  · subst h
    refine PH.ext (funext fun x => ?_)
    simp only [↓reduceIte, modeMap_val, cosCoeff_modeMap hn, sinCoeff_modeMap hn]
  · refine PH.ext (funext fun x => ?_)
    rw [modeMap_val, cosCoeff_modeMap hn, sinCoeff_modeMap hn]
    simp [trigFun, h]

theorem modeMap_mem {k k' : ℕ} {n : ℕ} (hn : 2 ≤ n) (f : PH α k) :
    modeMap k k' n f ∈ PH.orthSub α k' := by
  have h0 : n ≠ 0 := by omega
  rw [PH.mem_orthSub, integral_eq_cosCoeff_zero, cosCoeff_modeMap h0, sinCoeff_modeMap h0,
    cosCoeff_modeMap h0]
  have h1 : (1 : ℕ) ≠ n := by omega
  have h2 : (0 : ℕ) ≠ n := by omega
  simp [h1, h2]

/-- The `n`-th mode as a map between the orthogonal subspaces (zero for `n < 2`). -/
noncomputable def modeOrth (k k' n : ℕ) : PH.orthSub α k →L[ℝ] PH.orthSub α k' :=
  if h : 2 ≤ n then
    ((modeMap k k' n).comp (PH.orthSub α k).subtypeL).codRestrict (PH.orthSub α k')
      (fun u => modeMap_mem h u.1)
  else 0

theorem modeOrth_val {k k' n : ℕ} (hn : 2 ≤ n) (u : PH.orthSub α k) :
    ((modeOrth k k' n u : PH.orthSub α k') : PH α k') = modeMap k k' n u.1 := by
  simp [modeOrth, hn]
  rfl

theorem modeOrth_of_lt {k k' n : ℕ} (hn : ¬ 2 ≤ n) : modeOrth (α := α) k k' n = 0 := by
  simp [modeOrth, hn]

theorem modeOrth_comp {k k' k'' : ℕ} {n : ℕ} (hn : 2 ≤ n) (n' : ℕ) (u : PH.orthSub α k) :
    modeOrth k' k'' n' (modeOrth k k' n u) = if n' = n then modeOrth k k'' n u else 0 := by
  by_cases h : n' = n
  · subst h
    refine Subtype.ext ?_
    simp only [↓reduceIte, modeOrth_val hn, modeMap_comp (by omega : n' ≠ 0)]
  · simp only [h, ↓reduceIte]
    by_cases h' : 2 ≤ n'
    · refine Subtype.ext ?_
      rw [modeOrth_val h', modeOrth_val hn, modeMap_comp (by omega)]
      simp [h]
    · rw [modeOrth_of_lt h']; rfl

theorem ellOrth_modeOrth (n : ℕ) (u : PH.orthSub α 2) :
    ellOrth (modeOrth 2 2 n u) = (1 - (n : ℝ) ^ 2) • modeOrth 2 0 n u := by
  by_cases hn : 2 ≤ n
  · refine Subtype.ext (PH.ext ?_)
    rw [ellOrth_apply, ell_val]
    have : (modeOrth 2 2 n u).1.val = trigFun n (modeWeight n * PH.cosCoeff 2 n u.1)
        (modeWeight n * PH.sinCoeff 2 n u.1) := by
      rw [modeOrth_val hn]; exact funext (modeMap_val n u.1)
    have h2 : (modeOrth 2 0 n u).1.val = trigFun n (modeWeight n * PH.cosCoeff 2 n u.1)
        (modeWeight n * PH.sinCoeff 2 n u.1) := by
      rw [modeOrth_val hn]; exact funext (modeMap_val n u.1)
    rw [this, ellFun_trigFun]
    funext x
    simp [h2]
  · rw [modeOrth_of_lt hn, modeOrth_of_lt hn]; simp

theorem norm_modeOrth_le (k k' n : ℕ) : ‖modeOrth (α := α) k k' n‖ ≤ ‖modeMap (α := α) k k' n‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  by_cases hn : 2 ≤ n
  · have : ‖modeOrth k k' n u‖ = ‖modeMap k k' n u.1‖ := by
      show ‖((modeOrth k k' n u : PH.orthSub α k') : PH α k')‖ = _
      rw [modeOrth_val hn]
    rw [this]
    exact (modeMap k k' n).le_opNorm u.1
  · rw [modeOrth_of_lt hn]
    simpa using mul_nonneg (norm_nonneg (modeMap (α := α) k k' n)) (norm_nonneg u)

end Perturb

section InvAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inv_aux (P : ℕ → E →L[ℝ] E) (S : Finset ℕ)
    (hP : ∀ n ∈ S, ∀ k, ∀ u, P k (P n u) = if k = n then P n u else 0)
    (a b : ℕ → ℝ) (hab : ∀ n ∈ S, b n + a n + a n * b n = 0) (u : E) :
    (u + ∑ n ∈ S, b n • P n u) + ∑ k ∈ S, a k • P k (u + ∑ n ∈ S, b n • P n u) = u := by
  have h1 : ∀ k ∈ S, P k (u + ∑ n ∈ S, b n • P n u) = (1 + b k) • P k u := by
    intro k hk
    rw [map_add, map_sum]
    have : ∀ n ∈ S, P k (b n • P n u) = if k = n then b n • P n u else 0 := by
      intro n hn
      rw [map_smul, hP n hn k u]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp only [hk, ↓reduceIte]
    module
  have h2 : ∑ k ∈ S, a k • P k (u + ∑ n ∈ S, b n • P n u) =
      ∑ k ∈ S, (a k * (1 + b k)) • P k u :=
    Finset.sum_congr rfl fun k hk => by rw [h1 k hk, smul_smul]
  rw [h2, add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
  intro k hk
  have := hab k hk
  rw [← add_smul]
  have e : b k + a k * (1 + b k) = 0 := by linarith
  rw [e, zero_smul]

end InvAux

section Pert

variable {α : ℝ} [HolderExponent α]

/-- The explicit perturbed operator on `C^{2,α}_Q`: `∂θ² + 1` with the multiplier on the modes
`n ∈ S` changed from `1 - n²` to `m n`. -/
noncomputable def perturbed (S : Finset ℕ) (m : ℕ → ℝ) :
    PH.orthSub α 2 →L[ℝ] PH.orthSub α 0 :=
  ellOrth + ∑ n ∈ S, (m n - (1 - (n : ℝ) ^ 2)) • modeOrth 2 0 n

theorem perturbed_apply (S : Finset ℕ) (m : ℕ → ℝ) (u : PH.orthSub α 2) :
    perturbed S m u = ellOrth u + ∑ n ∈ S, (m n - (1 - (n : ℝ) ^ 2)) • modeOrth 2 0 n u := by
  simp [perturbed]

theorem perturbed_coeff {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n) (m : ℕ → ℝ) {n : ℕ}
    (u : PH.orthSub α 2) :
    PH.cosCoeff 0 n (perturbed S m u).1 =
        (if n ∈ S then m n else 1 - (n : ℝ) ^ 2) * PH.cosCoeff 2 n u.1 ∧
      PH.sinCoeff 0 n (perturbed S m u).1 =
        (if n ∈ S then m n else 1 - (n : ℝ) ^ 2) * PH.sinCoeff 2 n u.1 := by
  have key : ∀ k ∈ S, ∀ (c : ℝ), (PH.cosCoeff 0 n (modeOrth 2 0 k u).1 = if n = k then PH.cosCoeff 2 k u.1 else 0) ∧
      (PH.sinCoeff 0 n (modeOrth 2 0 k u).1 = if n = k then PH.sinCoeff 2 k u.1 else 0) := by
    intro k hk _
    have hk0 : k ≠ 0 := by have := hS k hk; omega
    rw [modeOrth_val (hS k hk)]
    exact ⟨cosCoeff_modeMap hk0 n u.1, sinCoeff_modeMap hk0 n u.1⟩
  have hv : (perturbed S m u).1 = ell u.1 +
      ∑ k ∈ S, (m k - (1 - (k : ℝ) ^ 2)) • (modeOrth 2 0 k u).1 := by
    rw [perturbed_apply]; simp [ellOrth_apply]
  rw [hv]
  constructor
  · rw [map_add, map_sum, cosCoeff_ell]
    have : ∀ k ∈ S, PH.cosCoeff 0 n ((m k - (1 - (k : ℝ) ^ 2)) • (modeOrth 2 0 k u).1) =
        if n = k then (m n - (1 - (n : ℝ) ^ 2)) * PH.cosCoeff 2 n u.1 else 0 := by
      intro k hk
      rw [map_smul, (key k hk 0).1]
      split_ifs with h
      · subst h; simp
      · simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs <;> ring
  · rw [map_add, map_sum, sinCoeff_ell]
    have : ∀ k ∈ S, PH.sinCoeff 0 n ((m k - (1 - (k : ℝ) ^ 2)) • (modeOrth 2 0 k u).1) =
        if n = k then (m n - (1 - (n : ℝ) ^ 2)) * PH.sinCoeff 2 n u.1 else 0 := by
      intro k hk
      rw [map_smul, (key k hk 0).2]
      split_ifs with h
      · subst h; simp
      · simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    split_ifs <;> ring

theorem ellOrth_ellInv (f : PH.orthSub α 0) : ellOrth (ellInv f) = f :=
  Subtype.ext (by rw [ellOrth_apply]; exact ell_ellInv f)

theorem perturbed_inverse {S : Finset ℕ} (hS : ∀ n ∈ S, 2 ≤ n) {δ : ℝ} (hδ : 0 < δ) (m : ℕ → ℝ)
    (hm : ∀ n ∈ S, δ ≤ |m n|) :
    ∃ g : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2,
      g.comp (perturbed S m) = 1 ∧ (perturbed S m).comp g = 1 ∧
        ‖g‖ ≤ ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
          (1 + ∑ n ∈ S, (|1 - (n : ℝ) ^ 2| / δ + 1) * ‖modeMap (α := α) 2 2 n‖) := by
  set P : ℕ → PH.orthSub α 2 →L[ℝ] PH.orthSub α 2 := fun n => modeOrth 2 2 n with hPdef
  set a : ℕ → ℝ := fun n => (m n - (1 - (n : ℝ) ^ 2)) / (1 - (n : ℝ) ^ 2) with ha
  set b : ℕ → ℝ := fun n => (1 - (n : ℝ) ^ 2) / m n - 1 with hb
  have hlam : ∀ n ∈ S, (1 - (n : ℝ) ^ 2) ≠ 0 := by
    intro n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hS n hn
    nlinarith
  have hm0 : ∀ n ∈ S, m n ≠ 0 := by
    intro n hn h0
    have := hm n hn
    rw [h0, abs_zero] at this
    linarith
  have hP : ∀ n ∈ S, ∀ k, ∀ u, P k (P n u) = if k = n then P n u else 0 :=
    fun n hn k u => modeOrth_comp (hS n hn) k u
  have hab : ∀ n ∈ S, b n + a n + a n * b n = 0 := by
    intro n hn
    have h1 := hlam n hn
    have h2 := hm0 n hn
    simp only [ha, hb]
    field_simp
    ring
  have hab' : ∀ n ∈ S, a n + b n + b n * a n = 0 := fun n hn => by
    have := hab n hn; linarith
  let D : PH.orthSub α 2 →L[ℝ] PH.orthSub α 2 := 1 + ∑ n ∈ S, a n • P n
  let Dinv : PH.orthSub α 2 →L[ℝ] PH.orthSub α 2 := 1 + ∑ n ∈ S, b n • P n
  have hDu : ∀ u, D u = u + ∑ n ∈ S, a n • P n u := fun u => by simp [D]
  have hDiu : ∀ u, Dinv u = u + ∑ n ∈ S, b n • P n u := fun u => by simp [Dinv]
  have hDDi : ∀ u, D (Dinv u) = u := fun u => by
    rw [hDu, hDiu]; exact inv_aux P S hP a b hab u
  have hDiD : ∀ u, Dinv (D u) = u := fun u => by
    rw [hDu, hDiu]; exact inv_aux P S hP b a hab' u
  have hpert : ∀ u, perturbed S m u = ellOrth (D u) := by
    intro u
    rw [perturbed_apply, hDu, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [map_smul, ellOrth_modeOrth, smul_smul]
    congr 1
    simp only [ha]
    rw [div_mul_cancel₀ _ (hlam n hn)]
  refine ⟨Dinv.comp ellInv, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun u => ?_
    simp only [ContinuousLinearMap.comp_apply, hpert, ellInv_ell, hDiD, one_apply_eq_self]
  · refine ContinuousLinearMap.ext fun f => ?_
    simp only [ContinuousLinearMap.comp_apply, hpert, hDDi, ellOrth_ellInv,
      one_apply_eq_self]
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ContinuousLinearMap.norm_id_le ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    refine (ContinuousLinearMap.opNorm_smul_le (b n) (P n)).trans ?_
    have hbn : ‖b n‖ ≤ |1 - (n : ℝ) ^ 2| / δ + 1 := by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_one]
      have : |1 - (n : ℝ) ^ 2| / |m n| ≤ |1 - (n : ℝ) ^ 2| / δ :=
        div_le_div_of_nonneg_left (abs_nonneg _) hδ (hm n hn)
      linarith
    exact mul_le_mul hbn (norm_modeOrth_le 2 2 n) (norm_nonneg _) (by positivity)

end Pert

end DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Analysis

open DGPS.Analysis.PeriodicHolder

/-- **Complementary circle elliptic inverse (FOU018).**  On the period-1 circle `ℝ/ℤ`
(`θ = 2πx`) the operator `∂θ² + 1` (realised as `(2π)⁻² u'' + u`) is a continuous linear
equivalence `C^{2,α}_Q → C^{0,α}_Q`, where `Q` is the closed subspace orthogonal to `1`,
`cos θ`, `sin θ`; its inverse acts diagonally on the cos/sin Fourier coefficients of order
`n ≥ 2` by `1/(1 - n²)`; and changing the multiplier on a finite set `S` of modes (`n ≥ 2`) by
values `m n` with `|m n| ≥ δ` leaves it invertible, with an inverse bound depending only on
`(S, δ, α)`. -/
theorem complementary_circle_elliptic_inverse (α : ℝ) [HolderExponent α] :
    (∃ e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      (∀ u : PH.orthSub α 2, (e u : PH α 0) = ComplementaryElliptic.ell (u : PH α 2)) ∧
      ∀ (f : PH.orthSub α 0) (n : ℕ), 2 ≤ n →
        PH.cosCoeff 2 n (e.symm f : PH α 2) =
            PH.cosCoeff 0 n (f : PH α 0) / (1 - (n : ℝ) ^ 2) ∧
        PH.sinCoeff 2 n (e.symm f : PH α 2) =
            PH.sinCoeff 0 n (f : PH α 0) / (1 - (n : ℝ) ^ 2)) ∧
    (∀ (S : Finset ℕ), (∀ n ∈ S, 2 ≤ n) → ∀ (m : ℕ → ℝ) (n : ℕ) (u : PH.orthSub α 2),
      PH.cosCoeff 0 n (ComplementaryElliptic.perturbed S m u : PH α 0) =
          (if n ∈ S then m n else 1 - (n : ℝ) ^ 2) * PH.cosCoeff 2 n (u : PH α 2) ∧
      PH.sinCoeff 0 n (ComplementaryElliptic.perturbed S m u : PH α 0) =
          (if n ∈ S then m n else 1 - (n : ℝ) ^ 2) * PH.sinCoeff 2 n (u : PH α 2)) ∧
    (∀ (S : Finset ℕ), (∀ n ∈ S, 2 ≤ n) → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ m : ℕ → ℝ,
      (∀ n ∈ S, δ ≤ |m n|) →
        ∃ g : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2,
          g.comp (ComplementaryElliptic.perturbed S m) = 1 ∧
          (ComplementaryElliptic.perturbed S m).comp g = 1 ∧ ‖g‖ ≤ C) := by
  refine ⟨⟨ComplementaryElliptic.ellEquiv, fun u => rfl, fun f n hn => ?_⟩, ?_, ?_⟩
  · exact ComplementaryElliptic.ellInv_coeff f hn
  · intro S hS m n u
    exact ComplementaryElliptic.perturbed_coeff hS m u
  · intro S hS δ hδ
    refine ⟨‖(ComplementaryElliptic.ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
      (1 + ∑ n ∈ S, (|1 - (n : ℝ) ^ 2| / δ + 1) *
        ‖ComplementaryElliptic.modeMap (α := α) 2 2 n‖), fun m hm => ?_⟩
    exact ComplementaryElliptic.perturbed_inverse hS hδ m hm

end DGPS.Analysis
