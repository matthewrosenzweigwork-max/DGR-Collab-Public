import FullLabeledLSI.Examples.Paper.Sec9Regularity
import FullLabeledLSI.Examples.Paper.Sec9SmallRateC

/-!
# Lemma 9.5, calculus of the cosine kernel (steps L0/L1 of `PLAN_C.md` section 3)

Lane C of the Section 9 formalization.  For `C = harmKernel k a = 2a cos(2πkx)` everything is expressed through
the functions `Reg.cosK j`, `sinK j` of module `Sec9RegularityA` (`cos(2πj·secT x 0)`) and the four moments
`c₁ = ∫ Reg.cosK k ρ`, `s₁ = ∫ sinK k ρ`, `c₂ = ∫ Reg.cosK (2k) ρ`, `s₂ = ∫ sinK (2k) ρ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Def

open SharpLSI
open FL.Ex.Reg FL.Ex FL.Ex.SR

/-! ### Bridge between `fourier` and `Reg.cosK`, `sinK` -/

theorem fourier_eq_cosK_sinK (k : ℤ) (x : Torus 1) :
    fourier k (x 0) = ((Reg.cosK k x : ℝ) : ℂ) + ((sinK k x : ℝ) : ℂ) * Complex.I := by
  have hx : x 0 = ((secT x 0 : ℝ) : UnitAddCircle) := (congrFun (liftT_secT x) 0).symm
  rw [hx, fourier_coe_apply]
  have : (2 * (π : ℂ) * Complex.I * (k : ℂ) * ((secT x 0 : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * π * k * secT x 0 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rfl

theorem cosK_eq_re (k : ℤ) (x : Torus 1) : Reg.cosK k x = (fourier k (x 0)).re := by
  rw [fourier_eq_cosK_sinK]; simp

theorem sinK_eq_im (k : ℤ) (x : Torus 1) : sinK k x = (fourier k (x 0)).im := by
  rw [fourier_eq_cosK_sinK]; simp

theorem continuous_cosK (k : ℤ) : Continuous (Reg.cosK k) := by
  have : Reg.cosK k = fun x : Torus 1 => (fourier k (x 0)).re := funext (cosK_eq_re k)
  rw [this]
  exact Complex.continuous_re.comp ((fourier k).continuous.comp (continuous_apply 0))

theorem continuous_sinK (k : ℤ) : Continuous (sinK k) := by
  have : sinK k = fun x : Torus 1 => (fourier k (x 0)).im := funext (sinK_eq_im k)
  rw [this]
  exact Complex.continuous_im.comp ((fourier k).continuous.comp (continuous_apply 0))

theorem cosMode_eq (k : ℕ) (x : Torus 1) : cosMode k x = Reg.cosK k x := by
  rw [cosK_eq_re]; rfl

theorem harmKernel_eq (k : ℕ) (a : ℝ) (x : Torus 1) : harmKernel k a x = 2 * a * Reg.cosK k x := by
  unfold harmKernel; rw [cosMode_eq]

/-! ### Torus arithmetic -/

theorem liftT_const_sub (a b : ℝ) (x y : Torus 1) (hx : secT x 0 = a) (hy : secT y 0 = b) :
    liftT (fun _ : Fin 1 => a - b) = x - y := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have h1 : (a : UnitAddCircle) = x 0 := by rw [← hx]; exact congrFun (liftT_secT x) 0
  have h2 : (b : UnitAddCircle) = y 0 := by rw [← hy]; exact congrFun (liftT_secT y) 0
  show ((a - b : ℝ) : UnitAddCircle) = x 0 - y 0
  rw [AddCircle.coe_sub, h1, h2]

theorem secT_sub_int (x y : Torus 1) : ∃ n : ℤ, secT (x - y) 0 = secT x 0 - secT y 0 + n := by
  have h := liftT_const_sub _ _ x y rfl rfl
  obtain ⟨m, hm⟩ := secT_liftT_eq (fun _ : Fin 1 => secT x 0 - secT y 0)
  refine ⟨m 0, ?_⟩
  rw [h] at hm
  have := congrFun hm 0
  simpa [intVec] using this

theorem periodic_secT_sub {G : ℝ → ℝ} (hp : Function.Periodic G 1) (x y : Torus 1) :
    G (secT (x - y) 0) = G (secT x 0 - secT y 0) := by
  obtain ⟨n, hn⟩ := secT_sub_int x y
  rw [hn]
  have := (hp.int_mul n) (secT x 0 - secT y 0)
  simpa using this

theorem secT_neg_int (x : Torus 1) : ∃ n : ℤ, secT (-x) 0 = -secT x 0 + n := by
  have h : liftT (fun _ : Fin 1 => -secT x 0) = -x := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h1 : ((secT x 0 : ℝ) : UnitAddCircle) = x 0 := congrFun (liftT_secT x) 0
    show ((-secT x 0 : ℝ) : UnitAddCircle) = -x 0
    rw [AddCircle.coe_neg, h1]
  obtain ⟨m, hm⟩ := secT_liftT_eq (fun _ : Fin 1 => -secT x 0)
  refine ⟨m 0, ?_⟩
  rw [h] at hm
  have := congrFun hm 0
  simpa [intVec] using this

theorem cosK_neg (k : ℤ) (x : Torus 1) : Reg.cosK k (-x) = Reg.cosK k x := by
  obtain ⟨n, hn⟩ := secT_neg_int x
  unfold Reg.cosK
  rw [hn]
  rw [show 2 * π * k * (-secT x 0 + n) = -(2 * π * k * secT x 0) + ((k * n : ℤ) : ℝ) * (2 * π) by
    push_cast; ring]
  rw [Real.cos_add_int_mul_two_pi, Real.cos_neg]

theorem integral_cosK (k : ℤ) (hk : k ≠ 0) : ∫ x, Reg.cosK k x ∂haar 1 = 0 := by
  have hp : Function.Periodic (fun t : ℝ => Real.cos (2 * π * k * t)) 1 := by
    intro t
    have : 2 * π * k * (t + 1) = 2 * π * k * t + ((k : ℤ) : ℝ) * (2 * π) := by ring
    simp only [this, Real.cos_add_int_mul_two_pi]
  have h := integral_torus_eq (G := fun t => Real.cos (2 * π * k * t))
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)) hp
  have e : ∫ x, Reg.cosK k x ∂haar 1 = ∫ x : Torus 1, Real.cos (2 * π * k * secT x 0) ∂haar 1 := rfl
  rw [e, h]
  have hk' : (2 * π * k : ℝ) ≠ 0 := by
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.cos t) hk']
  have hs : Real.sin (2 * π * k) = 0 := by
    have := Real.sin_int_mul_pi (2 * k)
    push_cast at this
    rw [← this]; congr 1; ring
  simp [integral_cos, hs]

theorem goodKernel_harmKernel {k : ℕ} (hk : 1 ≤ k) (a : ℝ) : GoodKernel (harmKernel k a) := by
  have hk0 : ((k : ℤ)) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · have : harmKernel k a = fun x => 2 * a * Reg.cosK k x := funext (harmKernel_eq k a)
    rw [this]
    unfold IsSmoothT
    exact (contDiff_const.mul (isSmoothT_cosK k))
  · intro x
    rw [harmKernel_eq, harmKernel_eq, cosK_neg]
  · have : (fun x => harmKernel k a x) = fun x => 2 * a * Reg.cosK k x := funext (harmKernel_eq k a)
    rw [this, integral_const_mul, integral_cosK k hk0, mul_zero]

/-! ### Derivatives of the kernel -/

/-- `ω = 2πk`. -/
noncomputable def omg (k : ℕ) : ℝ := 2 * π * k

theorem periodic_cos_mul (k : ℤ) (c0 : ℝ) :
    Function.Periodic (fun t : ℝ => c0 * Real.cos (2 * π * k * t)) 1 := by
  intro t
  have : 2 * π * k * (t + 1) = 2 * π * k * t + ((k : ℤ) : ℝ) * (2 * π) := by ring
  simp only [this, Real.cos_add_int_mul_two_pi]

theorem periodic_sin_mul (k : ℤ) (c0 : ℝ) :
    Function.Periodic (fun t : ℝ => c0 * Real.sin (2 * π * k * t)) 1 := by
  intro t
  have : 2 * π * k * (t + 1) = 2 * π * k * t + ((k : ℤ) : ℝ) * (2 * π) := by ring
  simp only [this, Real.sin_add_int_mul_two_pi]

theorem harmKernel_fun (k : ℕ) (a : ℝ) :
    harmKernel k a = fun y : Torus 1 => (fun t : ℝ => 2 * a * Real.cos (2 * π * (k : ℤ) * t)) (secT y 0) := by
  funext y; rw [harmKernel_eq]; rfl

theorem dT_harmKernel (k : ℕ) (a : ℝ) :
    dT (harmKernel k a) = fun y => -(2 * a * omg k) * sinK k y := by
  rw [harmKernel_fun]
  funext y
  rw [dT_comp_secT (periodic_cos_mul k (2 * a))]
  have h : HasDerivAt (fun t : ℝ => 2 * a * Real.cos (2 * π * (k : ℤ) * t))
      (2 * a * (-Real.sin (2 * π * (k : ℤ) * secT y 0) * (2 * π * (k : ℤ) * 1))) (secT y 0) :=
    (((hasDerivAt_id' (secT y 0)).const_mul (2 * π * (k : ℤ))).cos).const_mul (2 * a)
  rw [h.deriv]
  unfold omg sinK
  push_cast
  ring

theorem dT_dT_harmKernel (k : ℕ) (a : ℝ) :
    dT (dT (harmKernel k a)) = fun y => -(2 * a * omg k ^ 2) * Reg.cosK k y := by
  rw [dT_harmKernel]
  have hf : (fun y : Torus 1 => -(2 * a * omg k) * sinK k y) =
      fun y : Torus 1 => (fun t : ℝ => -(2 * a * omg k) * Real.sin (2 * π * (k : ℤ) * t)) (secT y 0) :=
    rfl
  rw [hf]
  funext y
  rw [dT_comp_secT (periodic_sin_mul k (-(2 * a * omg k)))]
  have h : HasDerivAt (fun t : ℝ => -(2 * a * omg k) * Real.sin (2 * π * (k : ℤ) * t))
      (-(2 * a * omg k) * (Real.cos (2 * π * (k : ℤ) * secT y 0) * (2 * π * (k : ℤ) * 1)))
      (secT y 0) :=
    (((hasDerivAt_id' (secT y 0)).const_mul (2 * π * (k : ℤ))).sin).const_mul _
  rw [h.deriv]
  unfold omg Reg.cosK
  push_cast
  ring

/-! ### Moments and convolutions -/

/-- `∫ cos(2πj x) ρ`. -/
noncomputable def mcos (j : ℤ) (ρ : Torus 1 → ℝ) : ℝ := ∫ y, Reg.cosK j y * ρ y ∂haar 1

/-- `∫ sin(2πj x) ρ`. -/
noncomputable def msin (j : ℤ) (ρ : Torus 1 → ℝ) : ℝ := ∫ y, sinK j y * ρ y ∂haar 1

theorem integrable_cosK_mul {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (j : ℤ) :
    Integrable (fun y => Reg.cosK j y * ρ y) (haar 1) := by
  have := hρ.mul_bdd (measurable_cosK j).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_cosK_le j y)
  simpa [mul_comm] using this

theorem integrable_sinK_mul {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (j : ℤ) :
    Integrable (fun y => sinK j y * ρ y) (haar 1) := by
  have := hρ.mul_bdd (measurable_sinK j).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_sinK_le j y)
  simpa [mul_comm] using this

theorem cosK_sub (k : ℤ) (x y : Torus 1) :
    Reg.cosK k (x - y) = Reg.cosK k x * Reg.cosK k y + sinK k x * sinK k y := by
  have h := periodic_secT_sub (periodic_cos_mul k 1) x y
  simp only [one_mul] at h
  unfold Reg.cosK sinK
  rw [h, show 2 * π * k * (secT x 0 - secT y 0) = 2 * π * k * secT x 0 - 2 * π * k * secT y 0 by ring,
    Real.cos_sub]

theorem sinK_sub (k : ℤ) (x y : Torus 1) :
    sinK k (x - y) = sinK k x * Reg.cosK k y - Reg.cosK k x * sinK k y := by
  have h := periodic_secT_sub (periodic_sin_mul k 1) x y
  simp only [one_mul] at h
  unfold Reg.cosK sinK
  rw [h, show 2 * π * k * (secT x 0 - secT y 0) = 2 * π * k * secT x 0 - 2 * π * k * secT y 0 by ring,
    Real.sin_sub]

theorem convT_cos {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℤ) (c0 : ℝ) (x : Torus 1) :
    convT (fun y => c0 * Reg.cosK k y) ρ x =
      c0 * (Reg.cosK k x * mcos k ρ + sinK k x * msin k ρ) := by
  unfold convT mcos msin
  have e : ∀ y, c0 * Reg.cosK k (x - y) * ρ y =
      c0 * (Reg.cosK k x * (Reg.cosK k y * ρ y) + sinK k x * (sinK k y * ρ y)) := fun y => by
    rw [cosK_sub]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_add ((integrable_cosK_mul hρ k).const_mul _)
    ((integrable_sinK_mul hρ k).const_mul _), integral_const_mul, integral_const_mul]

theorem convT_sin {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℤ) (c0 : ℝ) (x : Torus 1) :
    convT (fun y => c0 * sinK k y) ρ x =
      c0 * (sinK k x * mcos k ρ - Reg.cosK k x * msin k ρ) := by
  unfold convT mcos msin
  have e : ∀ y, c0 * sinK k (x - y) * ρ y =
      c0 * (sinK k x * (Reg.cosK k y * ρ y) - Reg.cosK k x * (sinK k y * ρ y)) := fun y => by
    rw [sinK_sub]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_sub ((integrable_cosK_mul hρ k).const_mul _)
    ((integrable_sinK_mul hρ k).const_mul _), integral_const_mul, integral_const_mul]

theorem convT_C {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℕ) (a : ℝ) (x : Torus 1) :
    convT (harmKernel k a) ρ x =
      2 * a * (Reg.cosK k x * mcos k ρ + sinK k x * msin k ρ) := by
  have : harmKernel k a = fun y => 2 * a * Reg.cosK k y := funext (harmKernel_eq k a)
  rw [this]; exact convT_cos hρ k (2 * a) x

theorem convT_dC {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℕ) (a : ℝ) (x : Torus 1) :
    convT (dT (harmKernel k a)) ρ x =
      -(2 * a * omg k) * (sinK k x * mcos k ρ - Reg.cosK k x * msin k ρ) := by
  rw [dT_harmKernel]; exact convT_sin hρ k _ x

theorem convT_ddC {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℕ) (a : ℝ) (x : Torus 1) :
    convT (dT (dT (harmKernel k a))) ρ x =
      -(2 * a * omg k ^ 2) * (Reg.cosK k x * mcos k ρ + sinK k x * msin k ρ) := by
  rw [dT_dT_harmKernel]; exact convT_cos hρ k _ x

/-! ### Double angles and the basis integral -/

theorem cosK_two (k : ℤ) (y : Torus 1) : Reg.cosK (2 * k) y = 2 * Reg.cosK k y ^ 2 - 1 := by
  unfold Reg.cosK
  rw [show 2 * π * ((2 * k : ℤ) : ℝ) * secT y 0 = 2 * (2 * π * k * secT y 0) by push_cast; ring,
    Real.cos_two_mul]

theorem sinK_two (k : ℤ) (y : Torus 1) : sinK (2 * k) y = 2 * sinK k y * Reg.cosK k y := by
  unfold Reg.cosK sinK
  rw [show 2 * π * ((2 * k : ℤ) : ℝ) * secT y 0 = 2 * (2 * π * k * secT y 0) by push_cast; ring,
    Real.sin_two_mul]

theorem sinK_sq_add_cosK_sq (k : ℤ) (y : Torus 1) : sinK k y ^ 2 + Reg.cosK k y ^ 2 = 1 := by
  unfold Reg.cosK sinK; exact Real.sin_sq_add_cos_sq _

theorem integrable_cosK (j : ℤ) : Integrable (Reg.cosK j) (haar 1) :=
  (BM.of_continuous (continuous_cosK j)).integrable

/-- Integral of a density against a trigonometric polynomial of degree two. -/
theorem int_basis {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (k : ℤ) (p0 p1 p2 p3 p4 : ℝ) :
    ∫ x, ρ x * (p0 + p1 * Reg.cosK k x + p2 * sinK k x + p3 * Reg.cosK (2 * k) x +
        p4 * sinK (2 * k) x) ∂haar 1 =
      p0 * ∫ x, ρ x ∂haar 1 + p1 * mcos k ρ + p2 * msin k ρ + p3 * mcos (2 * k) ρ +
        p4 * msin (2 * k) ρ := by
  unfold mcos msin
  have i1 := (integrable_cosK_mul hρ k).const_mul p1
  have i2 := (integrable_sinK_mul hρ k).const_mul p2
  have i3 := (integrable_cosK_mul hρ (2 * k)).const_mul p3
  have i4 := (integrable_sinK_mul hρ (2 * k)).const_mul p4
  have i0 := hρ.const_mul p0
  have e : ∀ x, ρ x * (p0 + p1 * Reg.cosK k x + p2 * sinK k x + p3 * Reg.cosK (2 * k) x +
        p4 * sinK (2 * k) x) =
      p0 * ρ x + p1 * (Reg.cosK k x * ρ x) + p2 * (sinK k x * ρ x) +
        p3 * (Reg.cosK (2 * k) x * ρ x) + p4 * (sinK (2 * k) x * ρ x) := fun x => by ring
  simp_rw [e]
  have j1 : Integrable (fun x => p0 * ρ x + p1 * (Reg.cosK k x * ρ x)) (haar 1) := i0.add i1
  have j2 : Integrable (fun x => p0 * ρ x + p1 * (Reg.cosK k x * ρ x) + p2 * (sinK k x * ρ x))
      (haar 1) := j1.add i2
  have j3 : Integrable (fun x => p0 * ρ x + p1 * (Reg.cosK k x * ρ x) + p2 * (sinK k x * ρ x) +
      p3 * (Reg.cosK (2 * k) x * ρ x)) (haar 1) := j2.add i3
  rw [integral_add j3 i4, integral_add j2 i3, integral_add j1 i2, integral_add i0 i1,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ### The polynomial `Ψ` and the common potential -/

/-- `Ψ(c₁,s₁,c₂,s₂)`, the interaction part of the deficit. -/
noncomputable def Psi (k : ℕ) (a r c1 s1 c2 s2 : ℝ) : ℝ :=
  2 * a * (r - 2 * omg k ^ 2) * (c1 ^ 2 + s1 ^ 2) +
    2 * a ^ 2 * omg k ^ 2 * (c1 ^ 2 * (1 - c2) - 2 * c1 * s1 * s2 + s1 ^ 2 * (1 + c2))

/-- The common potential as a trigonometric polynomial in the moments. -/
noncomputable def Abasis (k : ℕ) (a r c1 s1 c2 s2 : ℝ) (x : Torus 1) : ℝ :=
  2 * a ^ 2 * omg k ^ 2 * (c1 ^ 2 + s1 ^ 2) +
    (4 * a * (r - 2 * omg k ^ 2) * c1 + 2 * a ^ 2 * omg k ^ 2 * (2 * c1 * (1 - c2) - 2 * s1 * s2))
      * Reg.cosK k x +
    (4 * a * (r - 2 * omg k ^ 2) * s1 + 2 * a ^ 2 * omg k ^ 2 * (-2 * c1 * s2 + 2 * s1 * (1 + c2)))
      * sinK k x +
    (2 * a ^ 2 * omg k ^ 2 * (-c1 ^ 2 + s1 ^ 2)) * Reg.cosK (2 * (k : ℤ)) x +
    (2 * a ^ 2 * omg k ^ 2 * (-2 * c1 * s1)) * sinK (2 * (k : ℤ)) x

theorem Phi_eq {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1)) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (k : ℕ) (a r : ℝ) :
    2 * (∫ x, ρ x * convT (dT (dT (harmKernel k a))) ρ x ∂haar 1) +
        (∫ x, ρ x * (convT (dT (harmKernel k a)) ρ x) ^ 2 ∂haar 1) +
        r * (∫ x, ρ x * convT (harmKernel k a) ρ x ∂haar 1) =
      Psi k a r (mcos k ρ) (msin k ρ) (mcos (2 * (k : ℤ)) ρ) (msin (2 * (k : ℤ)) ρ) := by
  set c1 := mcos k ρ with hc1
  set s1 := msin k ρ with hs1
  set c2 := mcos (2 * (k : ℤ)) ρ with hc2
  set s2 := msin (2 * (k : ℤ)) ρ with hs2
  have k0 : ((k : ℕ) : ℤ) = (k : ℤ) := rfl
  -- first and third terms
  have T1 : ∫ x, ρ x * convT (harmKernel k a) ρ x ∂haar 1 = 2 * a * (c1 ^ 2 + s1 ^ 2) := by
    have e : ∀ x, ρ x * convT (harmKernel k a) ρ x =
        ρ x * (0 + (2 * a * c1) * Reg.cosK k x + (2 * a * s1) * sinK k x +
          0 * Reg.cosK (2 * (k : ℤ)) x + 0 * sinK (2 * (k : ℤ)) x) := fun x => by
      rw [convT_C hρ k a x]; ring
    simp_rw [e]
    rw [int_basis hρ k, h1]; ring
  have T2 : ∫ x, ρ x * convT (dT (dT (harmKernel k a))) ρ x ∂haar 1 =
      -(2 * a * omg k ^ 2) * (c1 ^ 2 + s1 ^ 2) := by
    have e : ∀ x, ρ x * convT (dT (dT (harmKernel k a))) ρ x =
        ρ x * (0 + (-(2 * a * omg k ^ 2) * c1) * Reg.cosK k x +
          (-(2 * a * omg k ^ 2) * s1) * sinK k x +
          0 * Reg.cosK (2 * (k : ℤ)) x + 0 * sinK (2 * (k : ℤ)) x) := fun x => by
      rw [convT_ddC hρ k a x]; ring
    simp_rw [e]
    rw [int_basis hρ k, h1]; ring
  have T3 : ∫ x, ρ x * (convT (dT (harmKernel k a)) ρ x) ^ 2 ∂haar 1 =
      2 * a ^ 2 * omg k ^ 2 * (c1 ^ 2 * (1 - c2) - 2 * c1 * s1 * s2 + s1 ^ 2 * (1 + c2)) := by
    have e : ∀ x, ρ x * (convT (dT (harmKernel k a)) ρ x) ^ 2 =
        ρ x * ((2 * a ^ 2 * omg k ^ 2 * (c1 ^ 2 + s1 ^ 2)) + 0 * Reg.cosK k x + 0 * sinK k x +
          (2 * a ^ 2 * omg k ^ 2 * (s1 ^ 2 - c1 ^ 2)) * Reg.cosK (2 * (k : ℤ)) x +
          (2 * a ^ 2 * omg k ^ 2 * (-2 * c1 * s1)) * sinK (2 * (k : ℤ)) x) := fun x => by
      rw [convT_dC hρ k a x, cosK_two, sinK_two]
      have hp := sinK_sq_add_cosK_sq (k : ℤ) x
      linear_combination (ρ x * (4 * a ^ 2 * omg k ^ 2 * c1 ^ 2)) * hp
    simp_rw [e]
    rw [int_basis hρ k, h1]; ring
  rw [T1, T2, T3]
  unfold Psi; ring

theorem commonPotential_eq {ρ : Torus 1 → ℝ} (hρ : Integrable ρ (haar 1))
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (k : ℕ) (a r : ℝ) (x : Torus 1) :
    commonPotential (harmKernel k a) r ρ x =
      Abasis k a r (mcos k ρ) (msin k ρ) (mcos (2 * (k : ℤ)) ρ) (msin (2 * (k : ℤ)) ρ) x := by
  set c1 := mcos k ρ with hc1
  set s1 := msin k ρ with hs1
  set c2 := mcos (2 * (k : ℤ)) ρ with hc2
  set s2 := msin (2 * (k : ℤ)) ρ with hs2
  set ω := omg k with hω
  -- the auxiliary density `ρ u`
  set ρ' : Torus 1 → ℝ := fun y => ρ y * convT (dT (harmKernel k a)) ρ y with hρ'
  have hρ'e : ∀ y, ρ' y = (-(2 * a * ω) * c1) * (sinK k y * ρ y) + (2 * a * ω * s1) * (Reg.cosK k y * ρ y) := by
    intro y
    simp only [hρ']
    rw [convT_dC hρ k a y]; ring
  have hρ'i : Integrable ρ' (haar 1) := by
    have : ρ' = fun y => (-(2 * a * ω) * c1) * (sinK k y * ρ y) + (2 * a * ω * s1) * (Reg.cosK k y * ρ y) :=
      funext hρ'e
    rw [this]
    exact ((integrable_sinK_mul hρ k).const_mul _).add ((integrable_cosK_mul hρ k).const_mul _)
  have M1 : mcos k ρ' = a * ω * s1 + a * ω * s1 * c2 - a * ω * c1 * s2 := by
    unfold mcos
    have e : ∀ y, Reg.cosK k y * ρ' y =
        ρ y * ((a * ω * s1) + 0 * Reg.cosK k y + 0 * sinK k y + (a * ω * s1) * Reg.cosK (2 * (k : ℤ)) y +
          (-(a * ω * c1)) * sinK (2 * (k : ℤ)) y) := fun y => by
      rw [hρ'e y, cosK_two, sinK_two]
      ring
    simp_rw [e]
    rw [int_basis hρ k, h1]; ring
  have M2 : msin k ρ' = -(a * ω * c1) + a * ω * c1 * c2 + a * ω * s1 * s2 := by
    unfold msin
    have e : ∀ y, sinK k y * ρ' y =
        ρ y * ((-(a * ω * c1)) + 0 * Reg.cosK k y + 0 * sinK k y + (a * ω * c1) * Reg.cosK (2 * (k : ℤ)) y +
          (a * ω * s1) * sinK (2 * (k : ℤ)) y) := fun y => by
      rw [hρ'e y, cosK_two, sinK_two]
      have hp := sinK_sq_add_cosK_sq (k : ℤ) y
      linear_combination (ρ y * (-(2 * a * ω * c1))) * hp
    simp_rw [e]
    rw [int_basis hρ k, h1]; ring
  unfold commonPotential
  rw [convT_ddC hρ k a x, convT_dC hρ k a x, convT_C hρ k a x]
  have : convT (dT (harmKernel k a)) (fun y => ρ y * convT (dT (harmKernel k a)) ρ y) x =
      -(2 * a * ω) * (sinK k x * mcos k ρ' - Reg.cosK k x * msin k ρ') := convT_dC hρ'i k a x
  rw [this, M1, M2]
  unfold Abasis
  rw [cosK_two, sinK_two]
  have hp := sinK_sq_add_cosK_sq (k : ℤ) x
  linear_combination (4 * a ^ 2 * ω ^ 2 * c1 ^ 2) * hp

end SharpLSI.FL.Ex.Def
