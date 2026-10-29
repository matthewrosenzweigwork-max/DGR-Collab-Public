import SharpSymmetricLSI.Vendor.SLT.GaussianLSI.OneDimGLSICompSmo
import SharpSymmetricLSI.Infra.EntropyTensor

/-!
# Gross' inequality in one dimension, shifted by a constant (R32, milestone E)

* `gross_1d`: the vendored inequality `Ent_γ(f²) ≤ 2 ∫ f'² dγ` (`f ∈ C²_c`, `γ = N(0,1)`) in the
  `entR` form of `Infra/EntropyTensor`.
* `gross_1d_shift`: `Ent_γ((a + ψ)²) ≤ 2 ∫ ψ'² dγ` for `ψ ∈ C^∞_c` and a constant `a`, by
  applying `gross_1d` to `ψ + a χ(·/(n+1))` (`χ` a bump equal to `1` on `[-1,1]`) and letting
  `n → ∞` by dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace SharpLSI

/-- The vendored one-dimensional Gross inequality. -/
theorem gross_1d {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    entR (gaussianReal 0 1) (fun x => f x ^ 2) ≤ 2 * ∫ x, deriv f x ^ 2 ∂gaussianReal 0 1 :=
  GaussianLSI.gaussian_logSobolev_CompSmo ⟨hf, hc⟩

section conv
variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]

/-- Bounded pointwise convergence passes through continuous functions under the integral. -/
theorem tendsto_integral_comp_of_bdd {u : ℕ → α → ℝ} {v : α → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (u n) P) {B : ℝ} (hB : ∀ n x, |u n x| ≤ B)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) {G : ℝ → ℝ} (hG : Continuous G) :
    Tendsto (fun n => ∫ x, G (u n x) ∂P) atTop (𝓝 (∫ x, G (v x) ∂P)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn
    hG.continuousOn
  refine tendsto_integral_of_dominated_convergence (fun _ => M)
    (fun n => hG.comp_aestronglyMeasurable (hm n)) (integrable_const M)
    (fun n => Eventually.of_forall fun x => hM _ ?_)
    (Eventually.of_forall fun x => (hG.tendsto _).comp (hlim x))
  exact abs_le.1 (hB n x)

/-- Bounded pointwise convergence gives convergence of `entR`. -/
theorem tendsto_entR_of_bdd {u : ℕ → α → ℝ} {v : α → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (u n) P) {B : ℝ} (hB : ∀ n x, |u n x| ≤ B)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto (fun n => entR P (u n)) atTop (𝓝 (entR P v)) := by
  have h1 := tendsto_integral_comp_of_bdd hm hB hlim Real.continuous_mul_log
  have h2 := tendsto_integral_comp_of_bdd hm hB hlim continuous_id
  have h3 := (Real.continuous_mul_log.tendsto _).comp h2
  exact h1.sub h3

end conv

/-- The fixed bump `χ`, equal to `1` on `[-1,1]` and `0` outside `(-2,2)`. -/
noncomputable def bump1 : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_n(t) = χ(t/(n+1))`. -/
noncomputable def chiN (n : ℕ) (t : ℝ) : ℝ := bump1 (t / (n + 1))

theorem contDiff_chiN (n : ℕ) : ContDiff ℝ ∞ (chiN n) :=
  bump1.contDiff.comp (contDiff_id.div_const _)

theorem hasCompactSupport_chiN (n : ℕ) : HasCompactSupport (chiN n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * (n + 1))) fun t ht => ?_
  have hn : (0 : ℝ) < n + 1 := by positivity
  refine bump1.zero_of_le_dist ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at ht
  rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hn, le_div_iff₀ hn]
  rw [Real.norm_eq_abs] at ht
  show 2 * (↑n + 1) ≤ |t|
  linarith

theorem hasDerivAt_chiN (n : ℕ) (t : ℝ) :
    HasDerivAt (chiN n) (deriv bump1 (t / (n + 1)) / (n + 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / (n + 1)) (1 / (n + 1)) t :=
    (hasDerivAt_id t).div_const _
  have h2 : HasDerivAt bump1 (deriv bump1 (t / (n + 1))) (t / (n + 1)) :=
    ((bump1.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have := h2.comp t h1
  rw [mul_one_div] at this
  exact this

theorem chiN_eventually_one (t : ℝ) : ∀ᶠ n : ℕ in atTop, chiN n t = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (0 : ℝ) < n + 1 := by positivity
  refine bump1.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hn',
    div_le_iff₀ hn']
  show |t| ≤ 1 * (↑n + 1)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem exists_bound_deriv_bump1 : ∃ M, ∀ x, |deriv bump1 x| ≤ M := by
  obtain ⟨M, hM⟩ := (bump1.hasCompactSupport.deriv).exists_bound_of_continuous
    ((bump1.contDiff (n := 1)).continuous_deriv le_rfl)
  exact ⟨M, fun x => by rw [← Real.norm_eq_abs]; exact hM x⟩

/-- **Gross' inequality for `a + ψ`**, `ψ ∈ C^∞_c`. -/
theorem gross_1d_shift {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (a : ℝ) :
    entR (gaussianReal 0 1) (fun t => (a + ψ t) ^ 2) ≤
      2 * ∫ t, deriv ψ t ^ 2 ∂gaussianReal 0 1 := by
  set w : ℕ → ℝ → ℝ := fun n t => ψ t + a * chiN n t with hw
  have hwd : ∀ n t, deriv (w n) t = deriv ψ t + a * (deriv bump1 (t / (n + 1)) / (n + 1)) :=
    fun n t => (((hψ.differentiable (by simp)) t).hasDerivAt.add
      ((hasDerivAt_chiN n t).const_mul a)).deriv
  have hineq : ∀ n, entR (gaussianReal 0 1) (fun t => w n t ^ 2) ≤
      2 * ∫ t, deriv (w n) t ^ 2 ∂gaussianReal 0 1 := fun n =>
    gross_1d ((hψ.add (contDiff_const.mul (contDiff_chiN n))).of_le (by simp))
      (hc.add ((hasCompactSupport_chiN n).mul_left))
  obtain ⟨Bψ, hBψ⟩ := hc.exists_bound_of_continuous hψ.continuous
  obtain ⟨Bd, hBd⟩ := (hc.deriv).exists_bound_of_continuous (hψ.continuous_deriv (by simp))
  obtain ⟨M, hM⟩ := exists_bound_deriv_bump1
  have hchi : ∀ n t, |chiN n t| ≤ 1 := fun n t => by
    unfold chiN; rw [abs_of_nonneg bump1.nonneg]; exact bump1.le_one
  -- left-hand side
  have hwB : ∀ n t, |w n t| ≤ Bψ + |a| := fun n t => by
    calc |w n t| ≤ |ψ t| + |a * chiN n t| := abs_add_le _ _
      _ ≤ Bψ + |a| * 1 := by
        rw [abs_mul]
        exact add_le_add (by rw [← Real.norm_eq_abs]; exact hBψ t)
          (mul_le_mul_of_nonneg_left (hchi n t) (abs_nonneg _))
      _ = _ := by ring
  have hL : Tendsto (fun n => entR (gaussianReal 0 1) (fun t => w n t ^ 2)) atTop
      (𝓝 (entR (gaussianReal 0 1) (fun t => (a + ψ t) ^ 2))) := by
    refine tendsto_entR_of_bdd (B := (Bψ + |a|) ^ 2)
      (fun n => ((hψ.continuous.add (continuous_const.mul (contDiff_chiN n).continuous)).pow
        2).aestronglyMeasurable) (fun n t => ?_) (fun t => ?_)
    · rw [abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ (abs_nonneg _) (hwB n t) 2
      rwa [sq_abs] at this
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [chiN_eventually_one t] with n hn
      simp only [hw, hn]; ring
  -- right-hand side
  have hR : Tendsto (fun n => ∫ t, deriv (w n) t ^ 2 ∂gaussianReal 0 1) atTop
      (𝓝 (∫ t, deriv ψ t ^ 2 ∂gaussianReal 0 1)) := by
    simp_rw [hwd]
    refine tendsto_integral_comp_of_bdd (B := Bd + |a| * M) (fun n => ?_) (fun n t => ?_)
      (fun t => ?_) (continuous_pow 2)
    · have hdb : Continuous (deriv bump1) := (bump1.contDiff (n := 1)).continuous_deriv le_rfl
      have hdψ : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
      exact (by fun_prop : Continuous fun t : ℝ =>
        deriv ψ t + a * (deriv bump1 (t / (n + 1)) / (n + 1))).aestronglyMeasurable
    · have hn : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h1 : |deriv bump1 (t / (n + 1)) / (n + 1)| ≤ M := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n + 1), div_le_iff₀ (by linarith)]
        nlinarith [hM (t / (n + 1)), abs_nonneg (deriv bump1 (t / (n + 1)))]
      calc _ ≤ |deriv ψ t| + |a * (deriv bump1 (t / (n + 1)) / (n + 1))| := abs_add_le _ _
        _ ≤ Bd + |a| * M := by
          rw [abs_mul]
          exact add_le_add (by rw [← Real.norm_eq_abs]; exact hBd t)
            (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    · have hz : Tendsto (fun n : ℕ => deriv bump1 (t / (n + 1)) / (n + 1)) atTop (𝓝 0) := by
        have hinv : Tendsto (fun n : ℕ => M * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul M
        refine squeeze_zero_norm (fun n => ?_) hinv
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < n + 1),
          mul_one_div]
        exact div_le_div_of_nonneg_right (hM _) (by positivity)
      simpa using (hz.const_mul a).const_add (deriv ψ t)
  exact le_of_tendsto_of_tendsto' hL (hR.const_mul 2) hineq

end SharpLSI
