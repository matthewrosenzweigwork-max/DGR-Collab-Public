import SharpSymmetricLSI.Paper.FormDuality4
import SharpSymmetricLSI.Paper.Occ10

/-!
# R32 (8.8), part 5: tools for Hermite functions of `ξ`

* one-dimensional cutoffs `ρ_R(s) = ρ(s/R)` with derivatives bounded uniformly in `R ≥ 1`;
* partial derivatives of products `∏_k f_k(y_k)` and of finite sums;
* the Hermite equation `q_n'' - x q_n' = -n q_n` for the normalized Hermite polynomials;
* dominated convergence in `L²(γ_ref)` for products of one-dimensional functions.
-/

open MeasureTheory ProbabilityTheory Filter Topology Polynomial
open scoped ENNReal ContDiff

namespace SharpLSI

/-! ### One-dimensional cutoffs -/

/-- The bump `ρ` on `ℝ`: `1` on `[-1,1]`, `0` outside `(-2,2)`. -/
noncomputable def bumpRho : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `ρ_R(s) = ρ(s/R)`. -/
noncomputable def rho1 (R : ℝ) (s : ℝ) : ℝ := bumpRho (R⁻¹ * s)

theorem contDiff_rho1 (R : ℝ) : ContDiff ℝ ∞ (rho1 R) :=
  bumpRho.contDiff.comp (contDiff_const.mul contDiff_id)

theorem rho1_nonneg (R s : ℝ) : 0 ≤ rho1 R s := bumpRho.nonneg

theorem rho1_le_one (R s : ℝ) : rho1 R s ≤ 1 := bumpRho.le_one

theorem rho1_eq_one {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ R) : rho1 R s = 1 := by
  refine bumpRho.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hR]
  exact (inv_mul_le_iff₀ hR).2 (by simpa [bumpRho] using hs)

theorem rho1_eq_zero {R s : ℝ} (hR : 0 < R) (hs : 2 * R ≤ |s|) : rho1 R s = 0 := by
  refine bumpRho.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero, abs_mul, abs_inv, abs_of_pos hR]
  exact (le_inv_mul_iff₀ hR).2 (by simpa [bumpRho, mul_comm] using hs)

theorem rho1_eventuallyEq_one {R s : ℝ} (hR : 0 < R) (hs : |s| < R) :
    rho1 R =ᶠ[𝓝 s] fun _ => 1 := by
  have h := abs_lt.1 hs
  filter_upwards [Ioo_mem_nhds h.1 h.2] with u hu
  exact rho1_eq_one hR (abs_le.2 ⟨hu.1.le, hu.2.le⟩)

theorem deriv_rho1 (R : ℝ) : deriv (rho1 R) = fun s => R⁻¹ * deriv bumpRho (R⁻¹ * s) := by
  funext s
  unfold rho1
  rw [deriv_comp_mul_left, smul_eq_mul]

theorem deriv_deriv_rho1 (R : ℝ) :
    deriv (deriv (rho1 R)) = fun s => R⁻¹ * (R⁻¹ * deriv (deriv bumpRho) (R⁻¹ * s)) := by
  rw [deriv_rho1, deriv_const_mul_field']
  funext s
  rw [deriv_comp_mul_left, smul_eq_mul]

theorem exists_rho1_deriv_bound : ∃ M, 0 ≤ M ∧ ∀ R, 1 ≤ R → ∀ s,
    |deriv (rho1 R) s| ≤ M ∧ |deriv (deriv (rho1 R)) s| ≤ M := by
  have hb : ContDiff ℝ ∞ (bumpRho : ℝ → ℝ) := bumpRho.contDiff
  have h1 : ContDiff ℝ ∞ (deriv bumpRho) := (contDiff_infty_iff_deriv.mp hb).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv bumpRho)) := (contDiff_infty_iff_deriv.mp h1).2
  obtain ⟨M1, hM1⟩ := bumpRho.hasCompactSupport.deriv.exists_bound_of_continuous h1.continuous
  obtain ⟨M2, hM2⟩ := bumpRho.hasCompactSupport.deriv.deriv.exists_bound_of_continuous h2.continuous
  refine ⟨max (max M1 M2) 0, le_max_right _ _, fun R hR s => ?_⟩
  have hR0 : 0 < R := by linarith
  have hRi : 0 ≤ R⁻¹ := inv_nonneg.2 hR0.le
  have hRi1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  constructor
  · rw [deriv_rho1, abs_mul, abs_of_nonneg hRi]
    have := hM1 (R⁻¹ * s); rw [Real.norm_eq_abs] at this
    calc R⁻¹ * |deriv bumpRho (R⁻¹ * s)| ≤ 1 * M1 :=
          mul_le_mul hRi1 this (abs_nonneg _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact (le_max_left _ _).trans (le_max_left _ _)
  · rw [deriv_deriv_rho1, abs_mul, abs_mul, abs_of_nonneg hRi]
    have := hM2 (R⁻¹ * s); rw [Real.norm_eq_abs] at this
    calc R⁻¹ * (R⁻¹ * |deriv (deriv bumpRho) (R⁻¹ * s)|) ≤ 1 * (1 * M2) :=
          mul_le_mul hRi1 (mul_le_mul hRi1 this (abs_nonneg _) zero_le_one)
            (mul_nonneg hRi (abs_nonneg _)) zero_le_one
      _ ≤ _ := by rw [one_mul, one_mul]; exact (le_max_right _ _).trans (le_max_left _ _)

/-! ### The cut polynomial `ρ_R q` -/

/-- `ρ_R(s) q(s)`. -/
noncomputable def cutPoly (q : ℝ[X]) (R : ℝ) (s : ℝ) : ℝ := rho1 R s * q.eval s

theorem contDiff_polyEval (q : ℝ[X]) : ContDiff ℝ ∞ (fun s : ℝ => q.eval s) := by
  have := q.contDiff_aeval (𝕜 := ℝ) ∞
  simpa using this

theorem contDiff_cutPoly (q : ℝ[X]) (R : ℝ) : ContDiff ℝ ∞ (cutPoly q R) :=
  (contDiff_rho1 R).mul (contDiff_polyEval q)

theorem deriv_cutPoly (q : ℝ[X]) (R : ℝ) : deriv (cutPoly q R) =
    fun s => deriv (rho1 R) s * q.eval s + rho1 R s * (derivative q).eval s := by
  funext s
  unfold cutPoly
  rw [deriv_fun_mul ((contDiff_rho1 R).differentiable (by simp) s) q.differentiableAt,
    Polynomial.deriv]

theorem deriv_deriv_cutPoly (q : ℝ[X]) (R : ℝ) : deriv (deriv (cutPoly q R)) =
    fun s => deriv (deriv (rho1 R)) s * q.eval s + 2 * (deriv (rho1 R) s * (derivative q).eval s) +
      rho1 R s * (derivative (derivative q)).eval s := by
  have hd1 : Differentiable ℝ (deriv (rho1 R)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_rho1 R)).2).differentiable (by simp)
  have hd0 : Differentiable ℝ (rho1 R) := (contDiff_rho1 R).differentiable (by simp)
  rw [deriv_cutPoly]
  funext s
  rw [deriv_fun_add (f := fun s => deriv (rho1 R) s * q.eval s)
    (g := fun s => rho1 R s * (derivative q).eval s)
    ((hd1 s).mul q.differentiableAt) ((hd0 s).mul (derivative q).differentiableAt),
    deriv_fun_mul (hd1 s) q.differentiableAt, deriv_fun_mul (hd0 s) (derivative q).differentiableAt,
    Polynomial.deriv, Polynomial.deriv]
  ring

theorem cutPoly_eventuallyEq {q : ℝ[X]} {R s : ℝ} (hR : 0 < R) (hs : |s| < R) :
    cutPoly q R =ᶠ[𝓝 s] fun s => q.eval s := by
  filter_upwards [rho1_eventuallyEq_one (s := s) hR hs] with u hu
  simp [cutPoly, hu]

/-- For fixed `s`, eventually (in `n`, `R = n + 1`) the cut polynomial and its first two
derivatives agree with those of `q` at `s`. -/
theorem eventually_cutPoly_eq (q : ℝ[X]) (s : ℝ) : ∀ᶠ n : ℕ in atTop,
    cutPoly q (n + 1) s = q.eval s ∧ deriv (cutPoly q (n + 1)) s = (derivative q).eval s ∧
      deriv (deriv (cutPoly q (n + 1))) s = (derivative (derivative q)).eval s := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt |s|
  filter_upwards [eventually_ge_atTop n₀] with n hn
  have hR : (0 : ℝ) < n + 1 := by positivity
  have hs : |s| < (n : ℝ) + 1 := by
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := cutPoly_eventuallyEq (q := q) hR hs
  refine ⟨h.eq_of_nhds, ?_, ?_⟩
  · rw [h.deriv_eq, Polynomial.deriv]
  · have h2 : deriv (cutPoly q (n + 1)) =ᶠ[𝓝 s] fun s => (derivative q).eval s := by
      filter_upwards [h.deriv] with u hu
      rw [hu, Polynomial.deriv]
    rw [h2.deriv_eq, Polynomial.deriv]

/-- The dominating function for cut polynomials and their generator terms. -/
noncomputable def domPoly (M : ℝ) (q : ℝ[X]) (s : ℝ) : ℝ :=
  (1 + 2 * M) * (|q.eval s| + |(derivative q).eval s| + |(derivative (derivative q)).eval s| +
    |s * q.eval s| + |s * (derivative q).eval s|)

theorem continuous_domPoly (M : ℝ) (q : ℝ[X]) : Continuous (domPoly M q) := by
  unfold domPoly
  have h := q.continuous; have h1 := (derivative q).continuous
  have h2 := (derivative (derivative q)).continuous
  fun_prop

theorem memLp_poly_gaussian (p : ℝ[X]) : MemLp (fun s => p.eval s) 2 (gaussianReal 0 1) := by
  refine (memLp_two_iff_integrable_sq p.continuous.aestronglyMeasurable).mpr ?_
  have e : (fun s => p.eval s ^ 2) = fun s => (p ^ 2).eval s := by funext s; simp [eval_pow]
  rw [e]; exact integrable_poly_gaussian _

theorem memLp_domPoly (M : ℝ) (q : ℝ[X]) : MemLp (domPoly M q) 2 (gaussianReal 0 1) := by
  unfold domPoly
  have habs : ∀ p : ℝ[X], MemLp (fun s => |p.eval s|) 2 (gaussianReal 0 1) := fun p => by
    simpa only [Real.norm_eq_abs] using (memLp_poly_gaussian p).norm
  have e1 : (fun s : ℝ => |s * q.eval s|) = fun s => |(X * q).eval s| := by funext s; simp
  have e2 : (fun s : ℝ => |s * (derivative q).eval s|) = fun s => |(X * derivative q).eval s| := by
    funext s; simp
  have h1 := habs q
  have h2 := habs (derivative q)
  have h3 := habs (derivative (derivative q))
  have h4 : MemLp (fun s : ℝ => |s * q.eval s|) 2 (gaussianReal 0 1) := by
    rw [e1]; exact habs _
  have h5 : MemLp (fun s : ℝ => |s * (derivative q).eval s|) 2 (gaussianReal 0 1) := by
    rw [e2]; exact habs _
  exact ((((h1.add h2).add h3).add h4).add h5).const_mul _

section bounds
variable {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ R, 1 ≤ R → ∀ s,
    |deriv (rho1 R) s| ≤ M ∧ |deriv (deriv (rho1 R)) s| ≤ M)
include hM0

omit hM0 in
theorem abs_le_domPoly_aux {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hM0 : 0 ≤ M) {x : ℝ} (hx : x ≤ M * a + 2 * M * b + c + M * d + e) :
    x ≤ (1 + 2 * M) * (a + b + c + d + e) := by
  nlinarith

theorem abs_le_domPoly (q : ℝ[X]) (s : ℝ) : |q.eval s| ≤ domPoly M q s := by
  unfold domPoly
  have := abs_nonneg ((derivative q).eval s); have := abs_nonneg ((derivative (derivative q)).eval s)
  have := abs_nonneg (s * q.eval s); have := abs_nonneg (s * (derivative q).eval s)
  nlinarith [abs_nonneg (q.eval s)]

theorem abs_gen_le_domPoly (q : ℝ[X]) (s : ℝ) :
    |(derivative (derivative q)).eval s - s * (derivative q).eval s| ≤ domPoly M q s := by
  unfold domPoly
  have := abs_nonneg (q.eval s); have := abs_nonneg ((derivative q).eval s)
  have := abs_nonneg (s * q.eval s)
  have h1 := abs_sub ((derivative (derivative q)).eval s) (s * (derivative q).eval s)
  nlinarith [abs_nonneg ((derivative (derivative q)).eval s), abs_nonneg (s * (derivative q).eval s)]

include hM in
theorem abs_cutPoly_le (q : ℝ[X]) {R : ℝ} (hR : 1 ≤ R) (s : ℝ) :
    |cutPoly q R s| ≤ domPoly M q s := by
  refine le_trans ?_ (abs_le_domPoly hM0 q s)
  unfold cutPoly
  rw [abs_mul, abs_of_nonneg (rho1_nonneg R s)]
  exact mul_le_of_le_one_left (abs_nonneg _) (rho1_le_one R s)

include hM in
theorem abs_gen_cutPoly_le (q : ℝ[X]) {R : ℝ} (hR : 1 ≤ R) (s : ℝ) :
    |deriv (deriv (cutPoly q R)) s - s * deriv (cutPoly q R) s| ≤ domPoly M q s := by
  rw [deriv_deriv_cutPoly, deriv_cutPoly]
  obtain ⟨h1, h2⟩ := hM R hR s
  have h0 := rho1_nonneg R s
  have h01 := rho1_le_one R s
  set a := |q.eval s|; set b := |(derivative q).eval s|
  set c := |(derivative (derivative q)).eval s|
  set d := |s * q.eval s|; set e := |s * (derivative q).eval s|
  unfold domPoly
  refine abs_le_domPoly_aux (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
    (abs_nonneg _) hM0 ?_
  have e1 : deriv (deriv (rho1 R)) s * q.eval s + 2 * (deriv (rho1 R) s * (derivative q).eval s) +
      rho1 R s * (derivative (derivative q)).eval s -
      s * (deriv (rho1 R) s * q.eval s + rho1 R s * (derivative q).eval s) =
      deriv (deriv (rho1 R)) s * q.eval s + 2 * (deriv (rho1 R) s * (derivative q).eval s) +
      rho1 R s * (derivative (derivative q)).eval s -
      deriv (rho1 R) s * (s * q.eval s) - rho1 R s * (s * (derivative q).eval s) := by ring
  rw [e1]
  have t1 : |deriv (deriv (rho1 R)) s * q.eval s| ≤ M * a := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have t2 : |2 * (deriv (rho1 R) s * (derivative q).eval s)| ≤ 2 * M * b := by
    rw [abs_mul, abs_mul, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) (by norm_num)
  have t3 : |rho1 R s * (derivative (derivative q)).eval s| ≤ c := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h01
  have t4 : |deriv (rho1 R) s * (s * q.eval s)| ≤ M * d := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have t5 : |rho1 R s * (s * (derivative q).eval s)| ≤ e := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h01
  calc _ ≤ |deriv (deriv (rho1 R)) s * q.eval s + 2 * (deriv (rho1 R) s * (derivative q).eval s) +
        rho1 R s * (derivative (derivative q)).eval s - deriv (rho1 R) s * (s * q.eval s)| +
        |rho1 R s * (s * (derivative q).eval s)| := abs_sub _ _
    _ ≤ (|deriv (deriv (rho1 R)) s * q.eval s + 2 * (deriv (rho1 R) s * (derivative q).eval s) +
        rho1 R s * (derivative (derivative q)).eval s| + |deriv (rho1 R) s * (s * q.eval s)|) +
        |rho1 R s * (s * (derivative q).eval s)| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|deriv (deriv (rho1 R)) s * q.eval s| + |2 * (deriv (rho1 R) s * (derivative q).eval s)|
        + |rho1 R s * (derivative (derivative q)).eval s|) + |deriv (rho1 R) s * (s * q.eval s)|) +
        |rho1 R s * (s * (derivative q).eval s)| := by
          gcongr; exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M * a + 2 * M * b + c + M * d + e := by linarith

end bounds

/-! ### The Hermite equation -/

theorem hermite_ode (n : ℕ) :
    derivative (derivative (hermite n)) - X * derivative (hermite n) = -((n : ℤ) • hermite n) := by
  cases n with
  | zero => simp [hermite_zero]
  | succ k =>
    rw [derivative_hermite_succ, derivative_smul]
    have h' : derivative (hermite k) = X * hermite k - hermite (k + 1) := by
      rw [hermite_succ k]; ring
    rw [h']
    simp only [zsmul_eq_mul]
    push_cast
    ring

theorem hermiteQ_ode (n : ℕ) (s : ℝ) :
    (derivative (derivative (hermiteQ n))).eval s - s * (derivative (hermiteQ n)).eval s =
      -((n : ℝ) * (hermiteQ n).eval s) := by
  have h := congrArg (fun P : ℤ[X] => (P.map (Int.castRingHom ℝ)).eval s) (hermite_ode n)
  simp only [zsmul_eq_mul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_neg,
    Polynomial.map_X, Polynomial.map_intCast, eval_sub, eval_mul, eval_X, eval_neg,
    eval_intCast] at h
  unfold hermiteQ hermiteR
  simp only [derivative_C_mul, derivative_map, eval_mul, eval_C]
  push_cast at h
  linear_combination ((Real.sqrt (n.factorial : ℝ))⁻¹) * h

/-! ### Partial derivatives of products and sums -/

theorem pd_eq_deriv_update {m : ℕ} {F : (Fin m → ℝ) → ℝ} {y : Fin m → ℝ}
    (hF : DifferentiableAt ℝ F y) (j : Fin m) :
    pd F j y = deriv (fun t => F (Function.update y j t)) (y j) := by
  have h := hF.hasFDerivAt.comp_hasDerivAt_of_eq (y j) (hasDerivAt_update y j (y j))
    (Function.update_eq_self j y).symm
  rw [Function.comp_def] at h
  rw [h.deriv]; rfl

theorem prod_update_eq {m : ℕ} (f : Fin m → ℝ → ℝ) (j : Fin m) (a : ℝ → ℝ) (y : Fin m → ℝ) :
    ∏ k, Function.update f j a k (y k) = a (y j) * ∏ k ∈ Finset.univ.erase j, f k (y k) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

theorem contDiff_prod_coord {m : ℕ} {f : Fin m → ℝ → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k)) :
    ContDiff ℝ ∞ (fun y : Fin m → ℝ => ∏ k, f k (y k)) :=
  contDiff_prod fun k _ => (hf k).comp (contDiff_apply ℝ ℝ k)

theorem pd_prod_coord {m : ℕ} {f : Fin m → ℝ → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k)) (j : Fin m) :
    pd (fun y : Fin m → ℝ => ∏ k, f k (y k)) j =
      fun y => ∏ k, Function.update f j (deriv (f j)) k (y k) := by
  funext y
  rw [pd_eq_deriv_update ((contDiff_prod_coord hf).differentiable (by simp) y),
    prod_update_eq]
  have e : (fun t => ∏ k, f k (Function.update y j t k)) =
      fun t => f j t * ∏ k ∈ Finset.univ.erase j, f k (y k) := by
    funext t
    have := prod_update_eq f j (f j) (Function.update y j t)
    rw [Function.update_eq_self, Function.update_self] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e, deriv_mul_const (((hf j).differentiable (by simp)) (y j))]

theorem contDiff_update_deriv {m : ℕ} {f : Fin m → ℝ → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (j : Fin m) : ∀ k, ContDiff ℝ ∞ (Function.update f j (deriv (f j)) k) := fun k => by
  by_cases h : k = j
  · subst h; rw [Function.update_self]; exact (contDiff_infty_iff_deriv.mp (hf k)).2
  · rw [Function.update_of_ne h]; exact hf k

theorem pd_pd_prod_coord {m : ℕ} {f : Fin m → ℝ → ℝ} (hf : ∀ k, ContDiff ℝ ∞ (f k)) (j : Fin m) :
    pd (pd (fun y : Fin m → ℝ => ∏ k, f k (y k)) j) j =
      fun y => ∏ k, Function.update f j (deriv (deriv (f j))) k (y k) := by
  rw [pd_prod_coord hf, pd_prod_coord (contDiff_update_deriv hf j), Function.update_self,
    Function.update_idem]

theorem pd_finset_sum_mul {ι : Type*} {m : ℕ} (s : Finset ι) {g : ι → (Fin m → ℝ) → ℝ}
    (hg : ∀ a, Differentiable ℝ (g a)) (c : ι → ℝ) (k : Fin m) (y : Fin m → ℝ) :
    pd (fun y => ∑ a ∈ s, c a * g a y) k y = ∑ a ∈ s, c a * pd (g a) k y := by
  unfold pd
  rw [fderiv_fun_sum fun a _ => ((hg a y).const_mul (c a)), ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [fderiv_const_mul (hg a y), ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### Dominated convergence for products under `γ_ref` -/

theorem tendsto_prod_gammaRef (S : Finset ℕ) {a : ℕ → ℕ → ℝ → ℝ} {a₀ D : ℕ → ℝ → ℝ}
    (ha : ∀ n k, Continuous (a n k)) (ha₀ : ∀ k, Continuous (a₀ k)) (hD : ∀ k, Continuous (D k))
    (hD2 : ∀ k, MemLp (D k) 2 (gaussianReal 0 1))
    (hdom : ∀ n k s, |a n k s| ≤ D k s) (hdom₀ : ∀ k s, |a₀ k s| ≤ D k s)
    (hev : ∀ k s, ∀ᶠ n in atTop, a n k s = a₀ k s) :
    Tendsto (fun n => eLpNorm (fun y : ℕ → ℝ => ∏ k ∈ S, a n k (y k) - ∏ k ∈ S, a₀ k (y k)) 2
      gammaRef) atTop (𝓝 0) := by
  have hDc : Continuous fun y : ℕ → ℝ => ∏ k ∈ S, D k (y k) :=
    continuous_finsetProd _ fun k _ => (hD k).comp (continuous_apply k)
  have hgL : MemLp (fun y : ℕ → ℝ => 2 * ∏ k ∈ S, D k (y k)) 2 gammaRef := by
    refine MemLp.const_mul ?_ 2
    refine (memLp_two_iff_integrable_sq hDc.aestronglyMeasurable).mpr ?_
    have e : (fun y : ℕ → ℝ => (∏ k ∈ S, D k (y k)) ^ 2) = fun y => ∏ k ∈ S, D k (y k) ^ 2 := by
      funext y; rw [Finset.prod_pow]
    rw [e]
    exact integrable_gammaRef_prod S (fun k s => D k s ^ 2) (fun k => (hD k).pow 2)
      fun k => (memLp_two_iff_integrable_sq (hD k).aestronglyMeasurable).mp (hD2 k)
  refine tendsto_eLpNorm_two_of_dom (fun n => ?_) hgL (fun n y => ?_) fun y => ?_
  · exact ((continuous_finsetProd _ fun k _ => (ha n k).comp (continuous_apply k)).sub
      (continuous_finsetProd _ fun k _ => (ha₀ k).comp (continuous_apply k))).aestronglyMeasurable
  · have hD0 : ∀ k s, 0 ≤ D k s := fun k s => (abs_nonneg _).trans (hdom₀ k s)
    have h1 : |∏ k ∈ S, a n k (y k)| ≤ ∏ k ∈ S, D k (y k) := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => hdom n k (y k)
    have h2 : |∏ k ∈ S, a₀ k (y k)| ≤ ∏ k ∈ S, D k (y k) := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => hdom₀ k (y k)
    refine (abs_sub _ _).trans ?_
    linarith
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finset S).2 fun k _ => hev k (y k)] with n hn
    rw [Finset.prod_congr rfl hn, sub_self]

/-- Transfer of `L²` norms along `ξ` with `γ.map ξ = γ_ref`. -/
theorem eLpNorm_comp_xi {γ : Measure (ℕ → ℝ)} {ξ : ℕ → (ℕ → ℝ) → ℝ}
    (hΞ : AEMeasurable (fun z j => ξ j z) γ) (hmap : γ.map (fun z j => ξ j z) = gammaRef)
    {h : (ℕ → ℝ) → ℝ} (hh : AEStronglyMeasurable h gammaRef) :
    eLpNorm (fun z => h (fun j => ξ j z)) 2 γ = eLpNorm h 2 gammaRef := by
  rw [← hmap] at hh ⊢
  rw [eLpNorm_map_measure hh hΞ]; rfl

end SharpLSI
