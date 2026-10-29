import DGPS.Examples.RoughBoundary.Feature

/-!
# Exact shift symmetries and feature moments (RUF006)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.5.  For the phase
`θ(x) = A_L(2x) - 1/6 + ε φ(6x)` with `φ` any `1`-periodic measurable function (the rough
counterexample is `φ = g`, the periodic primitive `gLine`), the feature
`U = (cos 2πθ, sin 2πθ)` satisfies `U(x + 1/6) = R_{2π/3} U(x)`, `U(x + 1/2) = U(x)`,
`∫ U dm = 0` and `∫ U Uᵀ dm = I₂ / 2`.
-/

open MeasureTheory Set
open scoped Real

namespace DGPS.Examples.RoughBoundary.Feature

open DGPS.Examples.RoughBoundary.Spikes (gLine pt)

/-- The phase with a general periodic perturbation `φ`. -/
noncomputable def thetaGen (φ : ℝ → ℝ) (L ε x : ℝ) : ℝ := Aprim L (2 * x) - 1 / 6 + ε * φ (6 * x)

/-- The feature with a general periodic perturbation `φ` in the phase. -/
noncomputable def UrealGen (φ : ℝ → ℝ) (L ε x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * thetaGen φ L ε x), Real.sin (2 * π * thetaGen φ L ε x)]

/-- The general feature as a function on the torus `Torus 1`. -/
noncomputable def UtorGen (φ : ℝ → ℝ) (L ε : ℝ) (y : Torus 1) : EuclideanSpace ℝ (Fin 2) :=
  UrealGen φ L ε (SharpLSI.secT y 0)

/-- Rotation `R_{2π/3}` of `ℝ²`. -/
noncomputable def rot120 (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π / 3) * v 0 - Real.sin (2 * π / 3) * v 1,
    Real.sin (2 * π / 3) * v 0 + Real.cos (2 * π / 3) * v 1]

lemma theta_eq_gen (L ε x : ℝ) : theta L ε x = thetaGen gLine L ε x := theta_pt_eq L ε x

lemma Ureal_eq_gen (L ε x : ℝ) : Ureal L ε x = UrealGen gLine L ε x := by
  unfold Ureal UrealGen; rw [theta_eq_gen]

lemma Ufeat_eq_gen (L ε : ℝ) (y : Torus 1) : Ufeat L ε y = UtorGen gLine L ε y := by
  unfold Ufeat UtorGen; rw [Ureal_eq_gen]

section Gen

variable {φ : ℝ → ℝ} {L : ℝ}

lemma thetaGen_add_sixth (hL : 0 < L) (hφ : Function.Periodic φ 1) (ε x : ℝ) :
    thetaGen φ L ε (x + 1 / 6) = thetaGen φ L ε x + 1 / 3 := by
  unfold thetaGen
  have e : 2 * (x + 1 / 6) = 2 * x + 1 / 3 := by ring
  have e2 : φ (6 * (x + 1 / 6)) = φ (6 * x) := by
    have : 6 * (x + 1 / 6) = 6 * x + 1 := by ring
    rw [this]; exact hφ _
  rw [e, aprim_add_third hL, e2]; ring

lemma thetaGen_add_half (hL : 0 < L) (hφ : Function.Periodic φ 1) (ε x : ℝ) :
    thetaGen φ L ε (x + 1 / 2) = thetaGen φ L ε x + 1 := by
  unfold thetaGen
  have e : 2 * (x + 1 / 2) = 2 * x + ((3 : ℕ) : ℝ) * (1 / 3) := by push_cast; ring
  have e2 : φ (6 * (x + 1 / 2)) = φ (6 * x) := by
    have : 6 * (x + 1 / 2) = 6 * x + ((3 : ℕ) : ℝ) := by push_cast; ring
    rw [this]; simpa using (hφ.nat_mul 3) (6 * x)
  rw [e, aprim_add_nat_third hL, e2]; push_cast; ring

lemma thetaGen_add_one (hL : 0 < L) (hφ : Function.Periodic φ 1) (ε x : ℝ) :
    thetaGen φ L ε (x + 1) = thetaGen φ L ε x + 2 := by
  have h := thetaGen_add_half hL hφ ε (x + 1 / 2)
  have e : x + 1 / 2 + 1 / 2 = x + 1 := by ring
  rw [e, thetaGen_add_half hL hφ] at h
  linarith

lemma UrealGen_add_sixth (hL : 0 < L) (hφ : Function.Periodic φ 1) (ε x : ℝ) :
    UrealGen φ L ε (x + 1 / 6) = rot120 (UrealGen φ L ε x) := by
  have h : 2 * π * thetaGen φ L ε (x + 1 / 6) = 2 * π * thetaGen φ L ε x + 2 * π / 3 := by
    rw [thetaGen_add_sixth hL hφ]; ring
  have hc : Real.cos (2 * π * thetaGen φ L ε (x + 1 / 6)) =
      Real.cos (2 * π / 3) * Real.cos (2 * π * thetaGen φ L ε x) -
        Real.sin (2 * π / 3) * Real.sin (2 * π * thetaGen φ L ε x) := by
    rw [h, Real.cos_add]; ring
  have hs : Real.sin (2 * π * thetaGen φ L ε (x + 1 / 6)) =
      Real.sin (2 * π / 3) * Real.cos (2 * π * thetaGen φ L ε x) +
        Real.cos (2 * π / 3) * Real.sin (2 * π * thetaGen φ L ε x) := by
    rw [h, Real.sin_add]; ring
  ext i
  fin_cases i
  · simpa [UrealGen, rot120] using hc
  · simpa [UrealGen, rot120] using hs

lemma UrealGen_add_half (hL : 0 < L) (hφ : Function.Periodic φ 1) (ε x : ℝ) :
    UrealGen φ L ε (x + 1 / 2) = UrealGen φ L ε x := by
  have h : 2 * π * thetaGen φ L ε (x + 1 / 2) = 2 * π * thetaGen φ L ε x + (1 : ℕ) * (2 * π) := by
    rw [thetaGen_add_half hL hφ]; push_cast; ring
  unfold UrealGen
  rw [h, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

end Gen


/-! ### Moments of a phase with the shift symmetry -/

section Harm

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa using hC x

lemma shift_integral {f : ℝ → ℝ} (hf : Function.Periodic f 1) :
    ∫ x in (0 : ℝ)..1, f (x + 1 / 6) = ∫ x in (0 : ℝ)..1, f x := by
  rw [intervalIntegral.integral_comp_add_right f (1 / 6)]
  have := hf.intervalIntegral_add_eq (1 / 6) 0
  simpa [add_comm] using this

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -1 / 2 := by
  have : 2 * π / 3 = π - π / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

lemma cos_four_pi_div_three : Real.cos (2 * π * 2 / 3) = -1 / 2 := by
  have : 2 * π * 2 / 3 = π / 3 + π := by ring
  rw [this, Real.cos_add_pi, Real.cos_pi_div_three]; ring

variable {T : ℝ → ℝ}

/-- If the phase `T` satisfies `T(x+1) = T(x) + 2` and `T(x+1/6) = T(x) + 1/3`, then the first
and second harmonics of `exp(2πi T)` have zero mean. -/
lemma harm_zero (hm : Measurable T) (hT1 : ∀ x, T (x + 1) = T x + 2)
    (hT6 : ∀ x, T (x + 1 / 6) = T x + 1 / 3) (k : ℕ)
    (hk : Real.cos (2 * π * k / 3) = -1 / 2) :
    (∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * T x)) = 0 ∧
      (∫ x in (0 : ℝ)..1, Real.sin (2 * π * k * T x)) = 0 := by
  set c := Real.cos (2 * π * k / 3) with hc
  set s := Real.sin (2 * π * k / 3) with hs
  have hs2 : s ^ 2 = 3 / 4 := by
    have := Real.sin_sq_add_cos_sq (2 * π * k / 3)
    rw [← hs, ← hc, hk] at this; linarith
  have hper : ∀ F : ℝ → ℝ, (F = Real.cos ∨ F = Real.sin) →
      Function.Periodic (fun x => F (2 * π * k * T x)) 1 := by
    intro F hF x
    have : 2 * π * k * T (x + 1) = 2 * π * k * T x + ((2 * k : ℕ) : ℝ) * (2 * π) := by
      rw [hT1]; push_cast; ring
    rcases hF with rfl | rfl
    · simp only [this, Real.cos_add_nat_mul_two_pi]
    · simp only [this, Real.sin_add_nat_mul_two_pi]
  have hcm : Measurable fun x => Real.cos (2 * π * k * T x) := by fun_prop
  have hsm : Measurable fun x => Real.sin (2 * π * k * T x) := by fun_prop
  have hci := intervalIntegrable_of_bdd hcm (C := 1) fun x => Real.abs_cos_le_one _
  have hsi := intervalIntegrable_of_bdd hsm (C := 1) fun x => Real.abs_sin_le_one _
  have e1 := shift_integral (hper Real.cos (Or.inl rfl))
  have e2 := shift_integral (hper Real.sin (Or.inr rfl))
  have a1 : ∀ x, Real.cos (2 * π * k * T (x + 1 / 6)) =
      c * Real.cos (2 * π * k * T x) - s * Real.sin (2 * π * k * T x) := by
    intro x
    have : 2 * π * k * T (x + 1 / 6) = 2 * π * k * T x + 2 * π * k / 3 := by rw [hT6]; ring
    rw [this, Real.cos_add]; ring
  have a2 : ∀ x, Real.sin (2 * π * k * T (x + 1 / 6)) =
      s * Real.cos (2 * π * k * T x) + c * Real.sin (2 * π * k * T x) := by
    intro x
    have : 2 * π * k * T (x + 1 / 6) = 2 * π * k * T x + 2 * π * k / 3 := by rw [hT6]; ring
    rw [this, Real.sin_add]; ring
  simp only [a1, a2] at e1 e2
  rw [intervalIntegral.integral_sub (hci.const_mul c) (hsi.const_mul s),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at e1
  rw [intervalIntegral.integral_add (hci.const_mul s) (hsi.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at e2
  set p := ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * T x)
  set q := ∫ x in (0 : ℝ)..1, Real.sin (2 * π * k * T x)
  rw [hk] at e1 e2
  have hp : p * 3 = 0 := by linear_combination (-3 / 2) * e1 + s * e2 - p * hs2
  have hq : q * 3 = 0 := by linear_combination (-s) * e1 - (3 / 2) * e2 - q * hs2
  exact ⟨by linarith, by linarith⟩


/-- The first and second moments of `(cos 2πT, sin 2πT)` over one period. -/
lemma line_moments (hm : Measurable T) (hT1 : ∀ x, T (x + 1) = T x + 2)
    (hT6 : ∀ x, T (x + 1 / 6) = T x + 1 / 3) :
    (∫ x in (0 : ℝ)..1, Real.cos (2 * π * T x)) = 0 ∧
    (∫ x in (0 : ℝ)..1, Real.sin (2 * π * T x)) = 0 ∧
    (∫ x in (0 : ℝ)..1, Real.cos (2 * π * T x) * Real.cos (2 * π * T x)) = 1 / 2 ∧
    (∫ x in (0 : ℝ)..1, Real.sin (2 * π * T x) * Real.sin (2 * π * T x)) = 1 / 2 ∧
    (∫ x in (0 : ℝ)..1, Real.cos (2 * π * T x) * Real.sin (2 * π * T x)) = 0 ∧
    (∫ x in (0 : ℝ)..1, Real.sin (2 * π * T x) * Real.cos (2 * π * T x)) = 0 := by
  have h1 := harm_zero hm hT1 hT6 1 (by simpa using cos_two_pi_div_three)
  have h2 := harm_zero hm hT1 hT6 2 (by simpa using cos_four_pi_div_three)
  simp only [Nat.cast_one, mul_one] at h1
  simp only [Nat.cast_ofNat] at h2
  obtain ⟨h1c, h1s⟩ := h1
  obtain ⟨h2c, h2s⟩ := h2
  have hcm : Measurable fun x => Real.cos (2 * π * 2 * T x) := by fun_prop
  have hsm : Measurable fun x => Real.sin (2 * π * 2 * T x) := by fun_prop
  have hci := intervalIntegrable_of_bdd hcm (C := 1) fun x => Real.abs_cos_le_one _
  have hc1 : (fun x => Real.cos (2 * π * T x) * Real.cos (2 * π * T x)) =
      fun x => 1 / 2 + (1 / 2) * Real.cos (2 * π * 2 * T x) := by
    funext x
    have := Real.cos_sq (2 * π * T x)
    rw [← sq, this]; ring_nf
  have hs1 : (fun x => Real.sin (2 * π * T x) * Real.sin (2 * π * T x)) =
      fun x => 1 / 2 - (1 / 2) * Real.cos (2 * π * 2 * T x) := by
    funext x
    have := Real.cos_sq (2 * π * T x)
    have h2 := Real.sin_sq_add_cos_sq (2 * π * T x)
    have e : 2 * π * 2 * T x = 2 * (2 * π * T x) := by ring
    rw [e, ← sq]
    nlinarith
  have hcs : (fun x => Real.cos (2 * π * T x) * Real.sin (2 * π * T x)) =
      fun x => (1 / 2) * Real.sin (2 * π * 2 * T x) := by
    funext x
    have := Real.sin_two_mul (2 * π * T x)
    have e : 2 * π * 2 * T x = 2 * (2 * π * T x) := by ring
    rw [e, this]; ring
  have hsc : (fun x => Real.sin (2 * π * T x) * Real.cos (2 * π * T x)) =
      fun x => (1 / 2) * Real.sin (2 * π * 2 * T x) := by
    rw [← hcs]; funext x; ring
  refine ⟨h1c, h1s, ?_, ?_, ?_, ?_⟩
  · rw [hc1, intervalIntegral.integral_add intervalIntegrable_const (hci.const_mul _),
      intervalIntegral.integral_const_mul, h2c]; simp
  · rw [hs1, intervalIntegral.integral_sub intervalIntegrable_const (hci.const_mul _),
      intervalIntegral.integral_const_mul, h2c]; simp
  · rw [hcs, intervalIntegral.integral_const_mul, h2s]; simp
  · rw [hsc, intervalIntegral.integral_const_mul, h2s]; simp

end Harm


/-! ### Transfer to the torus and the final statement -/

lemma continuous_aprim (L : ℝ) : Continuous (Aprim L) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_aprim L s).continuousAt

lemma measurable_thetaGen {φ : ℝ → ℝ} (hφ : Measurable φ) (L ε : ℝ) :
    Measurable (thetaGen φ L ε) := by
  unfold thetaGen
  have := (continuous_aprim L).measurable
  fun_prop

lemma integral_haar_secT {G : ℝ → ℝ} (hm : Measurable G) (hG : Function.Periodic G 1) :
    ∫ y, G (SharpLSI.secT y 0) ∂haar 1 = ∫ t in (0 : ℝ)..1, G t := by
  have hmeas : Measurable fun y : Torus 1 => G (SharpLSI.secT y 0) :=
    hm.comp ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)
  rw [Spikes.integral_haar_eq hmeas.aestronglyMeasurable,
    intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ => Spikes.periodic_secT hG t

lemma measurable_UrealGen {φ : ℝ → ℝ} (hφ : Measurable φ) (L ε : ℝ) :
    Measurable (UrealGen φ L ε) := by
  have hT := measurable_thetaGen hφ L ε
  have h2 : Measurable fun x : ℝ => (fun i : Fin 2 => if i = 0 then Real.cos (2 * π * thetaGen φ L ε x)
      else Real.sin (2 * π * thetaGen φ L ε x)) := by
    refine Measurable.of_eval fun i => ?_
    by_cases hi : i = 0 <;> simp only [hi, ite_true, ite_false] <;> fun_prop
  have h3 := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp h2
  convert h3 using 1
  funext x
  ext i
  fin_cases i <;> simp [UrealGen]

lemma measurable_UtorGen {φ : ℝ → ℝ} (hφ : Measurable φ) (L ε : ℝ) :
    Measurable (UtorGen φ L ε) :=
  (measurable_UrealGen hφ L ε).comp ((measurable_pi_apply 0).comp SharpLSI.measurable_secT)

lemma norm_UrealGen (φ : ℝ → ℝ) (L ε x : ℝ) : ‖UrealGen φ L ε x‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [UrealGen, Fin.sum_univ_two]

/-- Exact shift symmetries and the first two moments of the unit feature on the torus, for a
general periodic measurable phase perturbation `φ`. -/
lemma moments_gen {L : ℝ} (hL : 0 < L) {φ : ℝ → ℝ} (hφ : Function.Periodic φ 1)
    (hφm : Measurable φ) (ε : ℝ) :
    ∫ y, UtorGen φ L ε y ∂haar 1 = 0 ∧
      ∀ i j : Fin 2, ∫ y, UtorGen φ L ε y i * UtorGen φ L ε y j ∂haar 1 =
        if i = j then 1 / 2 else 0 := by
  have hm := measurable_thetaGen hφm L ε
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := line_moments hm (thetaGen_add_one hL hφ ε)
    (thetaGen_add_sixth hL hφ ε)
  have hp : ∀ F : ℝ → ℝ, (F = Real.cos ∨ F = Real.sin) →
      Function.Periodic (fun x => F (2 * π * thetaGen φ L ε x)) 1 := by
    intro F hF x
    have : 2 * π * thetaGen φ L ε (x + 1) = 2 * π * thetaGen φ L ε x + ((2 : ℕ) : ℝ) * (2 * π) := by
      rw [thetaGen_add_one hL hφ]; push_cast; ring
    rcases hF with rfl | rfl
    · simp only [this, Real.cos_add_nat_mul_two_pi]
    · simp only [this, Real.sin_add_nat_mul_two_pi]
  have hpc := hp Real.cos (Or.inl rfl)
  have hps := hp Real.sin (Or.inr rfl)
  have hcm : Measurable fun x => Real.cos (2 * π * thetaGen φ L ε x) := by fun_prop
  have hsm : Measurable fun x => Real.sin (2 * π * thetaGen φ L ε x) := by fun_prop
  have tc := integral_haar_secT hcm hpc
  have ts := integral_haar_secT hsm hps
  have tcc := integral_haar_secT (hcm.mul hcm) (hpc.mul hpc)
  have tss := integral_haar_secT (hsm.mul hsm) (hps.mul hps)
  have tcs := integral_haar_secT (hcm.mul hsm) (hpc.mul hps)
  have tsc := integral_haar_secT (hsm.mul hcm) (hps.mul hpc)
  have hint : Integrable (UtorGen φ L ε) (haar 1) := by
    refine Integrable.of_bound (measurable_UtorGen hφm L ε).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y => (norm_UrealGen φ L ε _).le
  constructor
  · ext j
    have := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hint
    simp at this
    rw [← this]
    fin_cases j
    · simpa [UtorGen, UrealGen] using tc.trans m1
    · simpa [UtorGen, UrealGen] using ts.trans m2
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa [UtorGen, UrealGen] using tcc.trans m3
    · simpa [UtorGen, UrealGen] using tcs.trans m5
    · simpa [UtorGen, UrealGen] using tsc.trans m6
    · simpa [UtorGen, UrealGen] using tss.trans m4

/-- **RUF006.**  For every `L > 0` and `ε ∈ ℝ`: `U(x + 1/6) = R_{2π/3} U(x)`, `U(x + 1/2) = U(x)`,
`∫ U dm = 0` and `∫ U Uᵀ dm = I₂ / 2` (entrywise: `∫ U_i U_j dm = ½ δ_{ij}`), where `m = haar 1`
and the integrals are taken for the torus feature `Ufeat`.  The same assertions hold after
replacing the periodic perturbation `g` in the phase by any `1`-periodic measurable function `φ`
(with `UrealGen`, `UtorGen`). -/
theorem exact_shift_symmetries_and_feature_moments {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    ((∀ x, Ureal L ε (x + 1 / 6) = rot120 (Ureal L ε x)) ∧
      (∀ x, Ureal L ε (x + 1 / 2) = Ureal L ε x) ∧
      ∫ y, Ufeat L ε y ∂haar 1 = 0 ∧
      ∀ i j : Fin 2, ∫ y, Ufeat L ε y i * Ufeat L ε y j ∂haar 1 = if i = j then 1 / 2 else 0) ∧
    ∀ φ : ℝ → ℝ, Function.Periodic φ 1 → Measurable φ →
      ((∀ x, UrealGen φ L ε (x + 1 / 6) = rot120 (UrealGen φ L ε x)) ∧
        (∀ x, UrealGen φ L ε (x + 1 / 2) = UrealGen φ L ε x) ∧
        ∫ y, UtorGen φ L ε y ∂haar 1 = 0 ∧
        ∀ i j : Fin 2, ∫ y, UtorGen φ L ε y i * UtorGen φ L ε y j ∂haar 1 =
          if i = j then 1 / 2 else 0) := by
  have gen : ∀ φ : ℝ → ℝ, Function.Periodic φ 1 → Measurable φ →
      ((∀ x, UrealGen φ L ε (x + 1 / 6) = rot120 (UrealGen φ L ε x)) ∧
        (∀ x, UrealGen φ L ε (x + 1 / 2) = UrealGen φ L ε x) ∧
        ∫ y, UtorGen φ L ε y ∂haar 1 = 0 ∧
        ∀ i j : Fin 2, ∫ y, UtorGen φ L ε y i * UtorGen φ L ε y j ∂haar 1 =
          if i = j then 1 / 2 else 0) := fun φ hφ hφm =>
    ⟨UrealGen_add_sixth hL hφ ε, UrealGen_add_half hL hφ ε, (moments_gen hL hφ hφm ε).1,
      (moments_gen hL hφ hφm ε).2⟩
  refine ⟨?_, gen⟩
  have h := gen gLine Spikes.gLine_periodic Spikes.continuous_gLine.measurable
  simp only [Ufeat_eq_gen, Ureal_eq_gen]
  exact h

end DGPS.Examples.RoughBoundary.Feature
