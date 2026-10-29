import SharpSymmetricLSI.Paper.GaussForm9

/-!
# R32 (B4): the cutoff lemma (version 1: bounded `G` with bounded derivatives)

For `G ∈ C^∞(ℝ^N)` bounded with bounded first derivatives, the cylinders `c_n = χ_n G`,
`χ_n(x) = χ(x/(n+1))` (`χ` a smooth bump, `= 1` on the unit ball), satisfy
`c_n → G(z_{<N})` in `L²(γ)` (`tendsto_cutCyl_L2`) and `ℰ(c_n) → ∫ ∑ λ_i (∂_iG)² dγ`
(`tendsto_cutCyl_form`), for any probability measure `γ` on `ℝ^ℕ`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

/-- A fixed smooth bump on `ℝ^N`: `1` on the unit ball, supported in the ball of radius `2`. -/
noncomputable def bumpN (N : ℕ) : ContDiffBump (0 : Fin N → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ_R(x) = χ(x/R)`. -/
noncomputable def chiR (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : ℝ := bumpN N (R⁻¹ • x)

theorem contDiff_chiR (N : ℕ) (R : ℝ) : ContDiff ℝ ∞ (chiR N R) :=
  (bumpN N).contDiff.comp (contDiff_const_smul _)

theorem chiR_nonneg (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : 0 ≤ chiR N R x := (bumpN N).nonneg

theorem chiR_le_one (N : ℕ) (R : ℝ) (x : Fin N → ℝ) : chiR N R x ≤ 1 := (bumpN N).le_one

theorem chiR_eq_one {N : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin N → ℝ} (hx : ‖x‖ ≤ R) :
    chiR N R x = 1 := by
  refine (bumpN N).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hR)]
  calc R⁻¹ * ‖x‖ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hR.le)
    _ = 1 := inv_mul_cancel₀ hR.ne'
    _ = (bumpN N).rIn := rfl

theorem hasCompactSupport_chiR {N : ℕ} {R : ℝ} (hR : 0 < R) : HasCompactSupport (chiR N R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin N → ℝ) (2 * R)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  unfold chiR
  rw [← Function.notMem_support, (bumpN N).support_eq, Metric.mem_ball, dist_zero_right, not_lt,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  show (2 : ℝ) ≤ R⁻¹ * ‖x‖
  rw [le_inv_mul_iff₀ hR]; linarith

/-- `‖Dχ_R‖ ≤ M/R`. -/
theorem exists_fderiv_chiR_bound (N : ℕ) : ∃ M, 0 ≤ M ∧ ∀ R, 0 < R → ∀ x,
    ‖fderiv ℝ (chiR N R) x‖ ≤ M * R⁻¹ := by
  have hd : Continuous fun x => fderiv ℝ (bumpN N) x :=
    ((bumpN N).contDiff (n := 1)).continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := ((bumpN N).hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun R hR x => ?_⟩
  set P : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ _
  have hP : ∀ y, P y = R⁻¹ • y := fun y => rfl
  have hder : fderiv ℝ (chiR N R) x = (fderiv ℝ (bumpN N) (P x)).comp P := by
    have h := (((bumpN N).contDiff (n := 1)).differentiable (by norm_num) (P x)).hasFDerivAt.comp x
      P.hasFDerivAt
    exact h.fderiv
  rw [hder]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hM _) ?_ (norm_nonneg _) hM0)
  show ‖R⁻¹ • ContinuousLinearMap.id ℝ (Fin N → ℝ)‖ ≤ R⁻¹
  refine (norm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ (Fin N → ℝ))).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  calc R⁻¹ * ‖ContinuousLinearMap.id ℝ (Fin N → ℝ)‖ ≤ R⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (inv_nonneg.2 hR.le)
    _ = R⁻¹ := mul_one _

/-- `χ_R = 1` near `x` when `‖x‖ < R`, so `Dχ_R(x) = 0`. -/
theorem fderiv_chiR_eq_zero {N : ℕ} {R : ℝ} (hR : 0 < R) {x : Fin N → ℝ} (hx : ‖x‖ < R) :
    fderiv ℝ (chiR N R) x = 0 := by
  have h : chiR N R =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds x (sub_pos.2 hx)] with y hy
    refine chiR_eq_one hR ?_
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have := norm_le_insert' y x
    linarith [norm_sub_norm_le y x]
  rw [h.fderiv_eq]; simp

/-- **Dominated convergence in `L²`** for uniformly bounded measurable functions. -/
theorem tendsto_eLpNorm_two_of_bdd {γ : Measure (ℕ → ℝ)} [IsFiniteMeasure γ]
    {F : ℕ → (ℕ → ℝ) → ℝ} (hm : ∀ n, Measurable (F n)) {B : ℝ} (hB : ∀ n z, |F n z| ≤ B)
    (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 γ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (F n) 2 γ = (∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hm n).aestronglyMeasurable
  simp_rw [e]
  have hint : Tendsto (fun n => ∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := γ)
      (F := fun n z => ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal) (f := fun _ => 0)
      (fun _ => ENNReal.ofReal B ^ (2 : ℝ≥0∞).toReal)
      (fun n => ((hm n).enorm).pow_const _)
      (fun n => Eventually.of_forall fun z => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hB n z))
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
      (Eventually.of_forall fun z => by
        have h1 : Tendsto (fun n => ‖F n z‖ₑ) atTop (𝓝 0) := by
          have := (continuous_enorm.tendsto (0 : ℝ)).comp (hlim z)
          simpa [Function.comp_def] using this
        have := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp h1
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this)
    simpa using this
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hint
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this

/-- The cutoff cylinder `χ_{n+1} G`. -/
noncomputable def cutCyl (N : ℕ) {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (n : ℕ) : Cyl where
  J := N
  φ := fun x => chiR N ((n : ℝ) + 1) x * G x
  smooth := (contDiff_chiR N _).mul hG
  compact := (hasCompactSupport_chiR (by positivity)).mul_right

/-- **(i)** `χ_n G → G` in `L²(γ)`. -/
theorem tendsto_cutCyl_L2 {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {N : ℕ}
    {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {B : ℝ} (hGB : ∀ x, |G x| ≤ B) :
    Tendsto (fun n => eLpNorm (fun z => (cutCyl N hG n).eval z - G (zBlock N z)) 2 γ) atTop
      (𝓝 0) := by
  refine tendsto_eLpNorm_two_of_bdd (B := 2 * B) (fun n => ?_) (fun n z => ?_) fun z => ?_
  · exact (cutCyl N hG n).measurable_eval.sub (measurable_comp_block hG.continuous)
  · show |chiR N ((n : ℝ) + 1) (zBlock N z) * G (zBlock N z) - G (zBlock N z)| ≤ 2 * B
    have h0 := chiR_nonneg N ((n : ℝ) + 1) (zBlock N z)
    have h1 := chiR_le_one N ((n : ℝ) + 1) (zBlock N z)
    rw [← sub_one_mul, abs_mul]
    have : |chiR N ((n : ℝ) + 1) (zBlock N z) - 1| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [hGB (zBlock N z), abs_nonneg (G (zBlock N z))]
  · refine tendsto_const_nhds.congr' ?_
    obtain ⟨m, hm⟩ := exists_nat_ge ‖zBlock N z‖
    filter_upwards [eventually_ge_atTop m] with n hn
    show 0 = chiR N ((n : ℝ) + 1) (zBlock N z) * G (zBlock N z) - G (zBlock N z)
    rw [chiR_eq_one (by positivity) (by
      have : (m : ℝ) ≤ n := by exact_mod_cast hn
      linarith), one_mul, sub_self]

/-- The form of a smooth function of the first `N` coordinates. -/
noncomputable def formG (lam' : ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (N : ℕ) (G : (Fin N → ℝ) → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (∑ i : Fin N, lam' i * (fderiv ℝ G (zBlock N z) (Pi.single i 1)) ^ 2) ∂γ

theorem Cyl.form_eq_formG (lam' : ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (c : Cyl) :
    c.form lam' γ = formG lam' γ c.J c.φ := rfl

theorem fderiv_chiR_mul {N : ℕ} {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) (R : ℝ)
    (x v : Fin N → ℝ) :
    fderiv ℝ (fun y => chiR N R y * G y) x v =
      chiR N R x * fderiv ℝ G x v + G x * fderiv ℝ (chiR N R) x v := by
  rw [fderiv_fun_mul ((contDiff_chiR N R).differentiable (by simp) x) (hG.differentiable (by simp) x)]
  simp [smul_eq_mul]

/-- **(ii)** `ℰ(χ_n G) → ℰ(G)`. -/
theorem tendsto_cutCyl_form {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {N : ℕ}
    {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {B : ℝ} (hGB : ∀ x, |G x| ≤ B)
    (hdB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) (lam' : ℕ → ℝ) :
    Tendsto (fun n => (cutCyl N hG n).form lam' γ) atTop (𝓝 (formG lam' γ N G)) := by
  obtain ⟨M, hM0, hM⟩ := exists_fderiv_chiR_bound N
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hGB 0)
  set D := B + B * M
  have hpd : ∀ (n : ℕ) (x : Fin N → ℝ) (i : Fin N),
      |fderiv ℝ (fun y => chiR N ((n : ℝ) + 1) y * G y) x (Pi.single i 1)| ≤ D := fun n x i => by
    rw [fderiv_chiR_mul hG]
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hRi : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
    have h1 : |fderiv ℝ G x (Pi.single i 1)| ≤ B := abs_pd_le hdB i x
    have h2 : |fderiv ℝ (chiR N ((n : ℝ) + 1)) x (Pi.single i 1)| ≤ M := by
      have := abs_pd_le (fun y => hM _ hR y) i x
      exact this.trans (by nlinarith)
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h3 := chiR_nonneg N ((n : ℝ) + 1) x
    have h4 := chiR_le_one N ((n : ℝ) + 1) x
    rw [abs_of_nonneg h3]
    calc chiR N ((n : ℝ) + 1) x * |fderiv ℝ G x (Pi.single i 1)| +
          |G x| * |fderiv ℝ (chiR N ((n : ℝ) + 1)) x (Pi.single i 1)|
        ≤ 1 * B + B * M := add_le_add (mul_le_mul h4 h1 (abs_nonneg _) zero_le_one)
          (mul_le_mul (hGB x) h2 (abs_nonneg _) hB0)
      _ = D := by simp [D]
  unfold Cyl.form
  refine tendsto_lintegral_of_dominated_convergence
    (fun _ => ENNReal.ofReal (∑ i : Fin N, |lam' i| * D ^ 2)) (fun n => ?_) (fun n => ?_) ?_ ?_
  · refine ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => ?_)
    refine measurable_const.mul (Measurable.pow_const ?_ 2)
    exact measurable_comp_block ((((cutCyl N hG n).smooth.continuous_fderiv (by simp))).clm_apply
      continuous_const)
  · refine Eventually.of_forall fun z => ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun i _ => ?_)
    have h := hpd n (fun j => z j) i
    have : (fderiv ℝ (cutCyl N hG n).φ (fun j => z j) (Pi.single i 1)) ^ 2 ≤ D ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    calc lam' i * (fderiv ℝ (cutCyl N hG n).φ (fun j => z j) (Pi.single i 1)) ^ 2
        ≤ |lam' i| * (fderiv ℝ (cutCyl N hG n).φ (fun j => z j) (Pi.single i 1)) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ |lam' i| * D ^ 2 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
  · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · refine Eventually.of_forall fun z => tendsto_const_nhds.congr' ?_
    obtain ⟨m, hm⟩ := exists_nat_gt ‖(fun j : Fin N => z j)‖
    filter_upwards [eventually_ge_atTop m] with n hn
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hx : ‖(fun j : Fin N => z j)‖ < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = lam' i * (fderiv ℝ (fun y => chiR N ((n : ℝ) + 1) y * G y) (fun j => z j) (Pi.single i 1)) ^ 2
    rw [fderiv_chiR_mul hG, fderiv_chiR_eq_zero hR hx, chiR_eq_one hR hx.le]
    simp only [one_mul, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
    rfl

end SharpLSI
