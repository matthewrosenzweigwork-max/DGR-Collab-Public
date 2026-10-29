import DGPS.Frontier.STR029.T02

/-!
# STR029.03: Exact stable dual norm

Task id: STR029.03. Title: Exact stable dual norm (node STR029, size M).

Provides:
* `DGPS.Frontier.STR029.f_STR02903`: the source `f(t) = 3 sin(3t) p'(t)` for `p(s) = A cos s + B sin s`.
* `DGPS.Frontier.STR029.invLHarm_STR02903`: the inverse of `L = -∂² - 1` on the second and fourth harmonics of a
  function, obtained by dividing its normalized Fourier coefficients at frequencies `2` and `4` by `3` and `15`.
* `DGPS.Frontier.STR029.str029_03_exact_stable_dual_norm`: for `v = L⁻¹ f`, `∫ f v dm = (9/10) ‖p‖₂²`; and for every
  `w` of STR029.02, `|∫ f w dm| ≤ √(9/10) ‖p‖₂ √(B0(w))`.
* Helper declarations, all suffixed `_STR02903`: the coefficient sequences `fA`, `fB`, `vA`, `vB`; the trigonometric
  expansions of `f` and `v`; the pairing identity `∫ f w dm = B0(w, v)`; the value `B0(v) = (9/10) ‖p‖₂²`; and the
  orthogonality of `v` to `cos t` and `sin t`.

R5 notes:
* Carriers: `w` and its weak derivative `g` are concrete `2π`-periodic functions `ℝ → ℝ` in the sense of
  `IsPeriodicWeakDerivative_STR02933` (STR029.33). `B0(w) = ∫ (g² - w²) dm` and `B0(w, v) = ∫ (g v' - w v) dm` use
  the given `g`. No existence or uniqueness of the weak derivative is used.
* Measure: `∫ · dm` is `normInt_STR02933`, the normalized integral over `(0, 2π]` as in STR029.33.
* `‖p‖₂²` is `∫ p² dm`, and `‖p‖₂` is its square root. Both are written out in the statement as
  `Real.sqrt (normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2))`.
* `f` uses the classical derivative `deriv` of the explicit function `s ↦ A cos s + B sin s`. The specified `p'` is read
  literally, and `f` is defined pointwise.
* `L⁻¹` is defined only on the second and fourth harmonics, as the specification says. `invLHarm_STR02903 F` divides
  `cosCoeff_STR02933 F 2` and `sinCoeff_STR02933 F 2` by `3 = 2² - 1`, and `cosCoeff_STR02933 F 4` and
  `sinCoeff_STR02933 F 4` by `15 = 4² - 1`. All other harmonics are dropped. Frequency one is not in the domain of this
  map, and it is not needed because `f` has no such harmonic.
* The orthogonality of `w` to `1, cos t, sin t` is the class of STR029.02. The hypotheses `h0`, `hc`, `hs` are kept in
  the second conjunct, because the specification says "for every `w` in STR029.02". No other hypothesis is added.
* The complementary inequality of STR029.02 is applied to `v = L⁻¹ f`. Its hypotheses (trigonometric polynomial form,
  mean zero, orthogonality to `cos t` and `sin t`) are proved here, not assumed.
* The identity `∫ f w dm = B0(w, v)` is obtained from the bilinear Parseval identities of STR029.34 applied to the
  coefficients of `f` and of `v`. Both sides reduce to the same finite sum over frequencies `2` and `4`, so no separate
  integration by parts is formalized.
* The constant `9/10` in the first conjunct is computed from coefficients: `∫ f v dm = (9/20)(A² + B²)` and
  `‖p‖₂² = (A² + B²)/2`.
* Integrability of the integrands is discharged through continuity of trigonometric polynomials and, for `w` and `g`,
  through the `MemLp` hypotheses via STR029.34. The Bochner convention is not relied on.
-/

open MeasureTheory Set Real

namespace DGPS.Frontier.STR029

/-- Coefficients of the cosine part of `f`: index `1` is frequency `2` and index `3` is frequency `4`. -/
noncomputable def fA_STR02903 (A : ℝ) : ℕ → ℝ :=
  fun k => if k = 1 then -(3 * A / 2) else if k = 3 then 3 * A / 2 else 0

/-- Coefficients of the sine part of `f`. -/
noncomputable def fB_STR02903 (B : ℝ) : ℕ → ℝ :=
  fun k => if k = 1 then 3 * B / 2 else if k = 3 then 3 * B / 2 else 0

/-- Coefficients of the cosine part of `v = L⁻¹ f`: `-(A/2)` at frequency `2` and `A/10` at frequency `4`. -/
noncomputable def vA_STR02903 (A : ℝ) : ℕ → ℝ :=
  fun k => if k = 1 then -(A / 2) else if k = 3 then A / 10 else 0

/-- Coefficients of the sine part of `v = L⁻¹ f`: `B/2` at frequency `2` and `B/10` at frequency `4`. -/
noncomputable def vB_STR02903 (B : ℝ) : ℕ → ℝ :=
  fun k => if k = 1 then B / 2 else if k = 3 then B / 10 else 0

/-- The source `f(t) = 3 sin(3t) p'(t)` for `p(s) = A cos s + B sin s`. -/
noncomputable def f_STR02903 (A B t : ℝ) : ℝ :=
  3 * Real.sin (3 * t) * deriv (fun s : ℝ => A * Real.cos s + B * Real.sin s) t

/-- The inverse of `L = -∂² - 1` on the second and fourth harmonics of `F`. The normalized Fourier coefficient at
frequency `n` is divided by `n² - 1`, which is `3` for `n = 2` and `15` for `n = 4`. -/
noncomputable def invLHarm_STR02903 (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  cosCoeff_STR02933 F 2 / 3 * Real.cos (2 * t) + sinCoeff_STR02933 F 2 / 3 * Real.sin (2 * t)
    + cosCoeff_STR02933 F 4 / 15 * Real.cos (4 * t) + sinCoeff_STR02933 F 4 / 15 * Real.sin (4 * t)

theorem deriv_p_STR02903 (A B t : ℝ) :
    deriv (fun s : ℝ => A * Real.cos s + B * Real.sin s) t = -A * Real.sin t + B * Real.cos t := by
  have h : HasDerivAt (fun s : ℝ => A * Real.cos s + B * Real.sin s)
      (A * -Real.sin t + B * Real.cos t) t :=
    ((Real.hasDerivAt_cos t).const_mul A).add ((Real.hasDerivAt_sin t).const_mul B)
  rw [h.deriv]
  ring

theorem cos_two_STR02903 (t : ℝ) :
    Real.cos (2 * t) = Real.cos (3 * t) * Real.cos t + Real.sin (3 * t) * Real.sin t := by
  rw [show (2 : ℝ) * t = 3 * t - t by ring, Real.cos_sub]

theorem cos_four_STR02903 (t : ℝ) :
    Real.cos (4 * t) = Real.cos (3 * t) * Real.cos t - Real.sin (3 * t) * Real.sin t := by
  rw [show (4 : ℝ) * t = 3 * t + t by ring, Real.cos_add]

theorem sin_two_STR02903 (t : ℝ) :
    Real.sin (2 * t) = Real.sin (3 * t) * Real.cos t - Real.cos (3 * t) * Real.sin t := by
  rw [show (2 : ℝ) * t = 3 * t - t by ring, Real.sin_sub]

theorem sin_four_STR02903 (t : ℝ) :
    Real.sin (4 * t) = Real.sin (3 * t) * Real.cos t + Real.cos (3 * t) * Real.sin t := by
  rw [show (4 : ℝ) * t = 3 * t + t by ring, Real.sin_add]

theorem trigPoly_fcoef_STR02903 (A B t : ℝ) :
    trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 t
      = -(3 * A / 2) * Real.cos (2 * t) + 3 * A / 2 * Real.cos (4 * t)
        + 3 * B / 2 * Real.sin (2 * t) + 3 * B / 2 * Real.sin (4 * t) := by
  norm_num [trigPoly_STR02934, Finset.sum_range_succ, fA_STR02903, fB_STR02903]
  ring

theorem trigPoly_vcoef_STR02903 (A B t : ℝ) :
    trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t
      = -(A / 2) * Real.cos (2 * t) + A / 10 * Real.cos (4 * t)
        + B / 2 * Real.sin (2 * t) + B / 10 * Real.sin (4 * t) := by
  norm_num [trigPoly_STR02934, Finset.sum_range_succ, vA_STR02903, vB_STR02903]
  ring

/-- The source `f` is the trigonometric polynomial with coefficient sequences `fA`, `fB` over frequencies `2, 4`. -/
theorem f_eq_trigPoly_STR02903 (A B t : ℝ) :
    f_STR02903 A B t = trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 t := by
  rw [trigPoly_fcoef_STR02903, cos_two_STR02903, cos_four_STR02903, sin_two_STR02903, sin_four_STR02903]
  unfold f_STR02903
  rw [deriv_p_STR02903]
  ring

theorem coeff_f_STR02903 (A B : ℝ) :
    cosCoeff_STR02933 (f_STR02903 A B) 2 = -(3 * A / 2) ∧
      sinCoeff_STR02933 (f_STR02903 A B) 2 = 3 * B / 2 ∧
      cosCoeff_STR02933 (f_STR02903 A B) 4 = 3 * A / 2 ∧
      sinCoeff_STR02933 (f_STR02903 A B) 4 = 3 * B / 2 := by
  have hfe : f_STR02903 A B = trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 :=
    funext (f_eq_trigPoly_STR02903 A B)
  have h1 := cosCoeff_trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 1
  have h2 := sinCoeff_trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 1
  have h3 := cosCoeff_trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 3
  have h4 := sinCoeff_trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 3
  rw [hfe]
  exact ⟨by simpa [fA_STR02903] using h1, by simpa [fB_STR02903] using h2,
    by simpa [fA_STR02903] using h3, by simpa [fB_STR02903] using h4⟩

theorem invLHarm_f_STR02903 (A B : ℝ) :
    invLHarm_STR02903 (f_STR02903 A B) = trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 := by
  obtain ⟨hc2, hs2, hc4, hs4⟩ := coeff_f_STR02903 A B
  funext t
  unfold invLHarm_STR02903
  rw [hc2, hs2, hc4, hs4, trigPoly_vcoef_STR02903]
  ring

theorem normInt_invLHarm_zero_STR02903 (A B : ℝ) :
    normInt_STR02933 (invLHarm_STR02903 (f_STR02903 A B)) = 0 := by
  rw [invLHarm_f_STR02903, normInt_trigPoly_STR02934]

theorem trigPoly_cos_STR02903 (t : ℝ) :
    trigPoly_STR02934 0 (fun _ => 1) (fun _ => 0) 1 t = Real.cos t := by
  simp [trigPoly_STR02934]

theorem trigPoly_sin_STR02903 (t : ℝ) :
    trigPoly_STR02934 0 (fun _ => 0) (fun _ => 1) 1 t = Real.sin t := by
  simp [trigPoly_STR02934]

/-- `v = L⁻¹ f` is orthogonal to `cos t` in the normalized inner product. -/
theorem normInt_invLHarm_cos_STR02903 (A B : ℝ) :
    normInt_STR02933 (fun t => invLHarm_STR02903 (f_STR02903 A B) t * Real.cos t) = 0 := by
  have e : (fun t : ℝ => invLHarm_STR02903 (f_STR02903 A B) t * Real.cos t)
      = fun t => trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t
          * trigPoly_STR02934 0 (fun _ => 1) (fun _ => 0) 1 t := by
    funext t
    rw [invLHarm_f_STR02903, trigPoly_cos_STR02903]
  rw [e, normInt_mul_trigPoly_STR02934 (integrable_continuous_STR02934
      (continuous_trigPoly_STR02902 0 (vA_STR02903 A) (vB_STR02903 B) 4)),
    Finset.sum_range_one, cosCoeff_trigPoly_STR02934, sinCoeff_trigPoly_STR02934]
  simp [vA_STR02903, vB_STR02903]

/-- `v = L⁻¹ f` is orthogonal to `sin t` in the normalized inner product. -/
theorem normInt_invLHarm_sin_STR02903 (A B : ℝ) :
    normInt_STR02933 (fun t => invLHarm_STR02903 (f_STR02903 A B) t * Real.sin t) = 0 := by
  have e : (fun t : ℝ => invLHarm_STR02903 (f_STR02903 A B) t * Real.sin t)
      = fun t => trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t
          * trigPoly_STR02934 0 (fun _ => 0) (fun _ => 1) 1 t := by
    funext t
    rw [invLHarm_f_STR02903, trigPoly_sin_STR02903]
  rw [e, normInt_mul_trigPoly_STR02934 (integrable_continuous_STR02934
      (continuous_trigPoly_STR02902 0 (vA_STR02903 A) (vB_STR02903 B) 4)),
    Finset.sum_range_one, cosCoeff_trigPoly_STR02934, sinCoeff_trigPoly_STR02934]
  simp [vA_STR02903, vB_STR02903]

/-- Parseval identity for `p = A cos t + B sin t`: `∫ p² dm = (A² + B²)/2`. -/
theorem normInt_sq_p_STR02903 (A B : ℝ) :
    normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2) = 1 / 2 * (A ^ 2 + B ^ 2) := by
  have e : (fun t : ℝ => (A * Real.cos t + B * Real.sin t) ^ 2)
      = fun t => trigPoly_STR02934 0 (fun _ => A) (fun _ => B) 1 t ^ 2 := by
    funext t
    simp [trigPoly_STR02934]
  rw [e, normInt_sq_trigPoly_STR02902]
  simp

/-- The pairing identity `∫ f v dm = (9/10) ‖p‖₂²` for `v = L⁻¹ f`. -/
theorem pairing_STR02903 (A B : ℝ) :
    normInt_STR02933 (fun t => f_STR02903 A B t * invLHarm_STR02903 (f_STR02903 A B) t)
      = 9 / 10 * normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2) := by
  have hfI : Integrable (trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4)
      (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 (continuous_trigPoly_STR02902 0 (fA_STR02903 A) (fB_STR02903 B) 4)
  have hfe : f_STR02903 A B = trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 :=
    funext (f_eq_trigPoly_STR02903 A B)
  rw [invLHarm_f_STR02903, hfe, normInt_mul_trigPoly_STR02934 hfI, normInt_sq_p_STR02903]
  simp only [cosCoeff_trigPoly_STR02934, sinCoeff_trigPoly_STR02934]
  norm_num [Finset.sum_range_succ, fA_STR02903, fB_STR02903, vA_STR02903, vB_STR02903]
  ring

/-- The pairing `∫ f w dm` equals the bilinear form `B0(w, v) = ∫ (g v' - w v) dm` for `v = L⁻¹ f`. -/
theorem fw_eq_B0_STR02903 (A B : ℝ) (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0) :
    normInt_STR02933 (fun t => f_STR02903 A B t * w t)
      = normInt_STR02933 (fun t => g t * deriv (trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4) t
          - w t * trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t) := by
  have hwi : Integrable w (volume.restrict (Ioc 0 (2 * π))) := integrable_of_memLp_STR02934 hwg.1.2
  have hgi : Integrable g (volume.restrict (Ioc 0 (2 * π))) := integrable_of_memLp_STR02934 hwg.2.1.2
  have hgv : Integrable (fun t => g t * deriv (trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4) t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simp only [deriv_trigPoly_STR02934]
    exact integrable_mul_trigPoly_STR02902 hgi _ _ _ _
  have hwv : Integrable (fun t => w t * trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t)
      (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_mul_trigPoly_STR02902 hwi _ _ _ _
  have hfw : normInt_STR02933 (fun t => f_STR02903 A B t * w t)
      = normInt_STR02933 (fun t => w t * trigPoly_STR02934 0 (fA_STR02903 A) (fB_STR02903 B) 4 t) := by
    congr 1
    funext t
    rw [f_eq_trigPoly_STR02903]
    ring
  obtain ⟨hF1, -, -⟩ :=
    str029_34_parseval_adapter_periodic_weak_domain_bilinear w g hwg h0 0 (fA_STR02903 A) (fB_STR02903 B) 4
  obtain ⟨hV1, hV2, -⟩ :=
    str029_34_parseval_adapter_periodic_weak_domain_bilinear w g hwg h0 0 (vA_STR02903 A) (vB_STR02903 B) 4
  rw [hfw, hF1, normInt_sub_STR02902 hgv hwv, hV1, hV2]
  norm_num [Finset.sum_range_succ, fA_STR02903, fB_STR02903, vA_STR02903, vB_STR02903]
  ring

/-- The value `B0(v) = ∫ (v'² - v²) dm = (9/10) ‖p‖₂²` for `v = L⁻¹ f`. -/
theorem normInt_B0_v_STR02903 (A B : ℝ) :
    normInt_STR02933 (fun t => deriv (trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4) t ^ 2
        - trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t ^ 2)
      = 9 / 10 * normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2) := by
  have hdv2 : Integrable (fun t => deriv (trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4) t ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simp only [deriv_trigPoly_STR02934]
    exact integrable_continuous_STR02934 ((continuous_trigPoly_STR02902 _ _ _ _).pow 2)
  have hv2 : Integrable (fun t => trigPoly_STR02934 0 (vA_STR02903 A) (vB_STR02903 B) 4 t ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) :=
    integrable_continuous_STR02934 ((continuous_trigPoly_STR02902 _ _ _ _).pow 2)
  rw [normInt_sub_STR02902 hdv2 hv2, normInt_sq_deriv_trigPoly_STR02902, normInt_sq_trigPoly_STR02902,
    normInt_sq_p_STR02903]
  norm_num [Finset.sum_range_succ, vA_STR02903, vB_STR02903]
  ring

/-- Second conjunct of the main statement: the complementary bound for `w` in the class of STR029.02. -/
theorem dual_bound_STR02903 (A B : ℝ) (w g : ℝ → ℝ) (hwg : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0) (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    |normInt_STR02933 (fun t => f_STR02903 A B t * w t)|
      ≤ Real.sqrt (9 / 10) * Real.sqrt (normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2))
        * Real.sqrt (normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)) := by
  have hB := (str029_02_complementary_fourier_quadratic_inequalities w g hwg h0 hc hs).2.2
    (invLHarm_STR02903 (f_STR02903 A B)) ⟨0, vA_STR02903 A, vB_STR02903 B, 4, invLHarm_f_STR02903 A B⟩
    (normInt_invLHarm_zero_STR02903 A B) (normInt_invLHarm_cos_STR02903 A B)
    (normInt_invLHarm_sin_STR02903 A B)
  rw [invLHarm_f_STR02903, ← fw_eq_B0_STR02903 A B w g hwg h0, normInt_B0_v_STR02903] at hB
  have hNp : 0 ≤ normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2) := by
    rw [normInt_sq_p_STR02903]
    positivity
  calc |normInt_STR02933 (fun t => f_STR02903 A B t * w t)|
      ≤ Real.sqrt (normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)
          * (9 / 10 * normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2))) :=
        Real.abs_le_sqrt hB
    _ = Real.sqrt (normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2))
          * Real.sqrt (9 / 10 * normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2)) :=
        Real.sqrt_mul' _ (mul_nonneg (by norm_num) hNp)
    _ = Real.sqrt (9 / 10) * Real.sqrt (normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2))
          * Real.sqrt (normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9 / 10)]
        ring

/-- STR029.03, exact stable dual norm. For `p = A cos t + B sin t`, `f = 3 sin(3t) p'` and `v = L⁻¹ f` (division by `3`
and `15` on the second and fourth harmonics), `∫ f v dm = (9/10) ‖p‖₂²`. For every periodic `H¹` function `w` with weak
derivative `g`, orthogonal to `1, cos t, sin t`, `|∫ f w dm| ≤ √(9/10) ‖p‖₂ √(B0(w))` with `B0(w) = ∫ (g² - w²) dm`. -/
theorem str029_03_exact_stable_dual_norm (A B : ℝ) :
    normInt_STR02933 (fun t => f_STR02903 A B t * invLHarm_STR02903 (f_STR02903 A B) t)
        = 9 / 10 * normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2) ∧
      ∀ w g : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 w g → normInt_STR02933 w = 0 →
        normInt_STR02933 (fun t => w t * Real.cos t) = 0 →
        normInt_STR02933 (fun t => w t * Real.sin t) = 0 →
        |normInt_STR02933 (fun t => f_STR02903 A B t * w t)|
          ≤ Real.sqrt (9 / 10) * Real.sqrt (normInt_STR02933 (fun t => (A * Real.cos t + B * Real.sin t) ^ 2))
            * Real.sqrt (normInt_STR02933 (fun t => g t ^ 2 - w t ^ 2)) :=
  ⟨pairing_STR02903 A B, fun w g hwg h0 hc hs => dual_bound_STR02903 A B w g hwg h0 hc hs⟩

end DGPS.Frontier.STR029
