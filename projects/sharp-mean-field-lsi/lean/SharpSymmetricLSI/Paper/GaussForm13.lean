import SharpSymmetricLSI.Paper.GaussForm12

/-!
# R32 (D2): sums of cylinders in a common dimension

For cylinders `u, v` and `N = J_u + J_v`, `G_± = u(z_{<J_u}) ± v(z_{<J_v})` is a smooth function of
`z_{<N}` with bounded derivatives, and
`formG(G_+) + formG(G_-) = 2ℰ(u) + 2ℰ(v)` for `λ ≥ 0` (`formG_parallelogram`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)}

/-- `u` as a function of `z_{<N}`. -/
noncomputable def Cyl.lift (u : Cyl) {N : ℕ} (h : u.J ≤ N) (x : Fin N → ℝ) : ℝ :=
  u.φ (projCLM h x)

theorem Cyl.contDiff_lift (u : Cyl) {N : ℕ} (h : u.J ≤ N) : ContDiff ℝ ∞ (u.lift h) :=
  u.smooth.comp (projCLM h).contDiff

theorem Cyl.lift_zBlock (u : Cyl) {N : ℕ} (h : u.J ≤ N) (z : ℕ → ℝ) :
    u.lift h (zBlock N z) = u.eval z := rfl

theorem Cyl.pd_lift (u : Cyl) {N : ℕ} (h : u.J ≤ N) (i : Fin N) (z : ℕ → ℝ) :
    pd (u.lift h) i (zBlock N z) = u.dd i z := by
  obtain ⟨B, -, -, -, -, hder⟩ := exists_bounds_comp u.smooth u.compact (projCLM h)
  unfold pd
  rw [show u.lift h = fun y => u.φ (projCLM h y) from rfl, hder, ContinuousLinearMap.comp_apply,
    projCLM_single]
  unfold Cyl.dd
  split_ifs with h1
  · rfl
  · simp

theorem Cyl.exists_lift_bounds (u : Cyl) {N : ℕ} (h : u.J ≤ N) :
    ∃ B, (∀ x, |u.lift h x| ≤ B) ∧ ∀ x, ‖fderiv ℝ (u.lift h) x‖ ≤ B := by
  obtain ⟨B, h1, h2, -, -, -⟩ := exists_bounds_comp u.smooth u.compact (projCLM h)
  exact ⟨B, h1, h2⟩

/-- `∑_{i<N} λ_i (∂_i u)² = ∑_{i<J_u} λ_i (∂_i u)²` for `N ≥ J_u`. -/
theorem Cyl.sum_fin_dd_sq (lam' : ℕ → ℝ) (u : Cyl) {N : ℕ} (h : u.J ≤ N) (z : ℕ → ℝ) :
    ∑ i : Fin N, lam' i * u.dd i z ^ 2 = ∑ i : Fin u.J, lam' i * u.dd i z ^ 2 := by
  rw [u.sum_fin_eq_range, u.sum_fin_eq_range]
  obtain ⟨k, rfl⟩ : ∃ k, N = u.J + k := ⟨N - u.J, by omega⟩
  rw [Finset.sum_range_add]
  have : ∀ x, lam' (u.J + x) * u.dd (u.J + x) z ^ 2 = 0 := fun x => by simp [Cyl.dd]
  simp [this]

theorem Cyl.form_eq_lintegral_dd (lam' : ℕ → ℝ) (u : Cyl) :
    u.form lam' γ = ∫⁻ z, ENNReal.ofReal (∑ i : Fin u.J, lam' i * u.dd i z ^ 2) ∂γ := by
  unfold Cyl.form
  refine lintegral_congr fun z => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [u.dd_of_lt i.isLt]; rfl

/-- `G_s = u + s v` as a function of `z_{<J_u + J_v}`. -/
noncomputable def Cyl.pm (u v : Cyl) (s : ℝ) (x : Fin (u.J + v.J) → ℝ) : ℝ :=
  u.lift (Nat.le_add_right u.J v.J) x + s * v.lift (Nat.le_add_left v.J u.J) x

theorem Cyl.contDiff_pm (u v : Cyl) (s : ℝ) : ContDiff ℝ ∞ (u.pm v s) :=
  (u.contDiff_lift _).add (contDiff_const.mul (v.contDiff_lift _))

theorem Cyl.pm_zBlock (u v : Cyl) (s : ℝ) (z : ℕ → ℝ) :
    u.pm v s (zBlock (u.J + v.J) z) = u.eval z + s * v.eval z := rfl

theorem Cyl.pd_pm (u v : Cyl) (s : ℝ) (i : Fin (u.J + v.J)) (z : ℕ → ℝ) :
    pd (u.pm v s) i (zBlock (u.J + v.J) z) = u.dd i z + s * v.dd i z := by
  have h1 := (u.contDiff_lift (Nat.le_add_right u.J v.J)).differentiable (by simp)
    (zBlock (u.J + v.J) z)
  have h2 := (v.contDiff_lift (Nat.le_add_left v.J u.J)).differentiable (by simp)
    (zBlock (u.J + v.J) z)
  unfold pd Cyl.pm
  rw [fderiv_fun_add h1 (h2.const_mul s), fderiv_const_mul h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have e1 := u.pd_lift (Nat.le_add_right u.J v.J) i z
  have e2 := v.pd_lift (Nat.le_add_left v.J u.J) i z
  unfold pd at e1 e2
  rw [e1, e2]

theorem Cyl.exists_pm_bounds (u v : Cyl) (s : ℝ) :
    ∃ B, (∀ x, |u.pm v s x| ≤ B) ∧ ∀ x, ‖fderiv ℝ (u.pm v s) x‖ ≤ B := by
  obtain ⟨Bu, hu1, hu2⟩ := u.exists_lift_bounds (Nat.le_add_right u.J v.J)
  obtain ⟨Bv, hv1, hv2⟩ := v.exists_lift_bounds (Nat.le_add_left v.J u.J)
  refine ⟨Bu + |s| * Bv, fun x => ?_, fun x => ?_⟩
  · unfold Cyl.pm
    refine (abs_add_le _ _).trans (add_le_add (hu1 x) ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hv1 x) (abs_nonneg _)
  · have h1 := (u.contDiff_lift (Nat.le_add_right u.J v.J)).differentiable (by simp) x
    have h2 := (v.contDiff_lift (Nat.le_add_left v.J u.J)).differentiable (by simp) x
    unfold Cyl.pm
    rw [fderiv_fun_add h1 (h2.const_mul s), fderiv_const_mul h2]
    refine (norm_add_le _ _).trans (add_le_add (hu2 x) ?_)
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hv2 x) (abs_nonneg _)

/-- **Parallelogram identity for the lifted sums.** -/
theorem formG_parallelogram {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (u v : Cyl) :
    formG lam' γ (u.J + v.J) (u.pm v 1) + formG lam' γ (u.J + v.J) (u.pm v (-1)) =
      2 * u.form lam' γ + 2 * v.form lam' γ := by
  set N := u.J + v.J
  have hpm : ∀ s : ℝ, formG lam' γ N (u.pm v s) =
      ∫⁻ z, ENNReal.ofReal (∑ i : Fin N, lam' i * (u.dd i z + s * v.dd i z) ^ 2) ∂γ := fun s =>
    lintegral_congr fun z => by
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [show fderiv ℝ (u.pm v s) (zBlock N z)
        (Pi.single i 1) = pd (u.pm v s) i (zBlock N z) from rfl, Cyl.pd_pm]
  have hmeas : ∀ s : ℝ, Measurable fun z =>
      ENNReal.ofReal (∑ i : Fin N, lam' i * (u.dd i z + s * v.dd i z) ^ 2) := fun s =>
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul (((u.measurable_dd i).add (measurable_const.mul (v.measurable_dd i))).pow_const 2))
  have hmu : Measurable fun z => ENNReal.ofReal (∑ i : Fin u.J, lam' i * u.dd i z ^ 2) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((u.measurable_dd i).pow_const 2))
  have hmv : Measurable fun z => ENNReal.ofReal (∑ i : Fin v.J, lam' i * v.dd i z ^ 2) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((v.measurable_dd i).pow_const 2))
  rw [hpm, hpm, u.form_eq_lintegral_dd, v.form_eq_lintegral_dd, ← lintegral_const_mul _ hmu,
    ← lintegral_const_mul _ hmv, ← lintegral_add_left (hmeas 1), ← lintegral_add_left (hmu.const_mul _)]
  refine lintegral_congr fun z => ?_
  have hn : ∀ s : ℝ, 0 ≤ ∑ i : Fin N, lam' i * (u.dd i z + s * v.dd i z) ^ 2 := fun s =>
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
  have hu0 : 0 ≤ ∑ i : Fin u.J, lam' i * u.dd i z ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
  have hv0 : 0 ≤ ∑ i : Fin v.J, lam' i * v.dd i z ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)
  rw [← ENNReal.ofReal_add (hn 1) (hn (-1)), ← u.sum_fin_dd_sq lam' (Nat.le_add_right u.J v.J),
    ← v.sum_fin_dd_sq lam' (Nat.le_add_left v.J u.J)]
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by rw [u.sum_fin_dd_sq lam' (Nat.le_add_right u.J v.J)]; positivity)
      (by rw [v.sum_fin_dd_sq lam' (Nat.le_add_left v.J u.J)]; positivity)]
  congr 1
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end SharpLSI
