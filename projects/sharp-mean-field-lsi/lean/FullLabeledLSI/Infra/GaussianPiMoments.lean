import Mathlib

/-!
# Moments of the product standard Gaussian on `ℝ^J` (Lindeberg step, Lemma 7.1)
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI.FL

/-- The product standard Gaussian on `Fin J → ℝ`. -/
noncomputable abbrev gaussPi (J : ℕ) : Measure (Fin J → ℝ) :=
  Measure.pi fun _ : Fin J => gaussianReal 0 1

private theorem gaussPi_map_eval (J : ℕ) (m : Fin J) :
    (gaussPi J).map (fun y => y m) = gaussianReal 0 1 :=
  (measurePreserving_eval (fun _ : Fin J => gaussianReal 0 1) m).map_eq

private theorem gaussian_integral_sq : ∫ x : ℝ, x * x ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simp only [integral_id_gaussianReal, sub_zero] at h
  simpa [sq] using h

theorem gaussPi_integral_coord (J : ℕ) (m : Fin J) : ∫ y, y m ∂gaussPi J = 0 := by
  have h := integral_map (μ := gaussPi J) (φ := fun y : Fin J → ℝ => y m)
    (f := fun x : ℝ => x) (measurable_pi_apply m).aemeasurable (by fun_prop)
  rw [gaussPi_map_eval, integral_id_gaussianReal] at h
  exact h.symm

theorem gaussPi_integral_mul (J : ℕ) (m m' : Fin J) :
    ∫ y, y m * y m' ∂gaussPi J = if m = m' then 1 else 0 := by
  split_ifs with hmm
  · subst hmm
    have h := integral_map (μ := gaussPi J) (φ := fun y : Fin J → ℝ => y m)
      (f := fun x : ℝ => x * x) (measurable_pi_apply m).aemeasurable (by fun_prop)
    rw [gaussPi_map_eval, gaussian_integral_sq] at h
    exact h.symm
  · have hind : iIndepFun (fun (i : Fin J) (y : Fin J → ℝ) => (id : ℝ → ℝ) (y i))
        (gaussPi J) :=
      iIndepFun_pi (μ := fun _ : Fin J => gaussianReal 0 1) (X := fun _ => (id : ℝ → ℝ))
        (fun _ => measurable_id.aemeasurable)
    have h2 := (hind.indepFun hmm).integral_mul_eq_mul_integral
      ((measurable_pi_apply m).aestronglyMeasurable) ((measurable_pi_apply m').aestronglyMeasurable)
    simp only [id] at h2
    have h3 : ∫ y : Fin J → ℝ, y m * y m' ∂gaussPi J
        = (∫ y : Fin J → ℝ, y m ∂gaussPi J) * ∫ y : Fin J → ℝ, y m' ∂gaussPi J := h2
    rw [h3, gaussPi_integral_coord, zero_mul]

private theorem gaussPi_integrable_abs_cube (J : ℕ) (m : Fin J) :
    Integrable (fun y : Fin J → ℝ => |y m| ^ 3) (gaussPi J) := by
  have h1 : Integrable (fun x : ℝ => |x| ^ 3) (gaussianReal 0 1) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 3).integrable_norm_pow
      (by norm_num)
    simpa using this
  exact (measurePreserving_eval (fun _ : Fin J => gaussianReal 0 1) m).integrable_comp_of_integrable
    h1

theorem gaussPi_integrable_norm_cube (J : ℕ) :
    Integrable (fun y : Fin J → ℝ => ‖y‖ ^ 3) (gaussPi J) := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ
    (fun m _ => gaussPi_integrable_abs_cube J m)) (by fun_prop) (Filter.Eventually.of_forall ?_)
  intro y
  rw [norm_pow, norm_norm]
  rcases isEmpty_or_nonempty (Fin J) with hJ | hJ
  · have : y = 0 := Subsingleton.elim _ _
    simp [this]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      (fun b => ‖y b‖₊)
    have hn : ‖y‖ = |y i| := by
      rw [← Real.norm_eq_abs, ← coe_nnnorm, Pi.nnnorm_def, hi]
      simp
    rw [hn]
    exact Finset.single_le_sum (f := fun m => |y m| ^ 3) (fun m _ => by positivity)
      (Finset.mem_univ i)

end SharpLSI.FL
