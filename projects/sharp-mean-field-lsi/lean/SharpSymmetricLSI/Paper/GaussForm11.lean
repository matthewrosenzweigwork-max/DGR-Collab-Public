import SharpSymmetricLSI.Paper.GaussForm10

/-!
# R32 (B5): the cutoff lemma (version 1), part (iii): the generator

For `G ∈ C^∞(ℝ^N)` with `‖D^k G‖ ≤ B` (`k ≤ 2`) and `Y_i ∈ L²(γ)`:
`L(χ_n G) → L G` in `L²(γ)` (`tendsto_cutCyl_gen`), where
`L G = ∑_i λ_i [∂_{ii}G - (z_i + Y_i) ∂_iG]` (`genG`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

/-- `∂_{ii} f`. -/
noncomputable def d2 {N : ℕ} (f : (Fin N → ℝ) → ℝ) (i : Fin N) (x : Fin N → ℝ) : ℝ :=
  fderiv ℝ (pd f i) x (Pi.single i 1)

theorem d2_eq_iteratedFDeriv {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin N)
    (x : Fin N → ℝ) :
    d2 f i x = iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single i 1] := by
  rw [iteratedFDeriv_two_apply]
  unfold d2 pd
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ f y) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp

theorem abs_d2_le {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin N) (x : Fin N → ℝ) :
    |d2 f i x| ≤ ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [d2_eq_iteratedFDeriv hf, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  have : ‖(Pi.single i 1 : Fin N → ℝ)‖ = 1 := by simp [Pi.norm_single]
  simp [Fin.prod_univ_two, this]

theorem abs_pd_le_iter {N : ℕ} {f : (Fin N → ℝ) → ℝ} (i : Fin N) (x : Fin N → ℝ) :
    |pd f i x| ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  rw [norm_iteratedFDeriv_one, pd, ← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans (le_of_eq ?_)
  have : ‖(Pi.single i 1 : Fin N → ℝ)‖ = 1 := by simp [Pi.norm_single]
  rw [this, mul_one]

/-- Uniform bounds on `D^k χ_R`, `k ≤ 2`, `R ≥ 1`. -/
theorem exists_iteratedFDeriv_chiR_bound (N : ℕ) : ∃ M, 0 ≤ M ∧ ∀ R, 1 ≤ R → ∀ k ≤ 2, ∀ x,
    ‖iteratedFDeriv ℝ k (chiR N R) x‖ ≤ M := by
  have hb : ∀ k : ℕ, ∃ M, ∀ y, ‖iteratedFDeriv ℝ k (bumpN N) y‖ ≤ M := fun k =>
    ((bumpN N).hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) k).exists_bound_of_continuous
      (((bumpN N).contDiff (n := (k : ℕ∞))).continuous_iteratedFDeriv le_rfl)
  choose Mb hMb using hb
  refine ⟨max (max (Mb 0) (Mb 1)) (Mb 2), (norm_nonneg _).trans ((hMb 0 0).trans
    ((le_max_left _ _).trans (le_max_left _ _))), fun R hR k hk x => ?_⟩
  set g : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := R⁻¹ • ContinuousLinearMap.id ℝ _
  have hg : ‖g‖ ≤ 1 := by
    refine (norm_smul_le (R⁻¹) (ContinuousLinearMap.id ℝ (Fin N → ℝ))).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (by linarith))]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ (Fin N → ℝ)‖ ≤ 1 * 1 :=
          mul_le_mul (inv_le_one_of_one_le₀ hR) ContinuousLinearMap.norm_id_le (norm_nonneg _)
            zero_le_one
      _ = 1 := one_mul 1
  have e : chiR N R = (bumpN N) ∘ g := rfl
  rw [e, g.iteratedFDeriv_comp_right ((bumpN N).contDiff (n := (k : ℕ∞))) x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin k, ‖g‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hg
  calc ‖iteratedFDeriv ℝ k (bumpN N) (g x)‖ * ∏ _i : Fin k, ‖g‖
      ≤ Mb k * 1 := mul_le_mul (hMb k _) hp (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          ((norm_nonneg _).trans (hMb k 0))
    _ ≤ _ := by
        rw [mul_one]
        interval_cases k
        · exact (le_max_left _ _).trans (le_max_left _ _)
        · exact (le_max_right _ _).trans (le_max_left _ _)
        · exact le_max_right _ _

/-- **Leibniz bound** for `χ_R G`. -/
theorem norm_iteratedFDeriv_chiR_mul_le {N : ℕ} {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G)
    {B : ℝ} (hGB : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k G x‖ ≤ B) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ R, 1 ≤ R → ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (chiR N R) x‖ ≤ M) {R : ℝ} (hR : 1 ≤ R)
    {k : ℕ} (hk : k ≤ 2) (x : Fin N → ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => chiR N R y * G y) x‖ ≤ 4 * (M * B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hGB 0 (by norm_num) 0)
  refine (norm_iteratedFDeriv_mul_le (contDiff_chiR N R) hG x (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chiR N R) x‖ *
        ‖iteratedFDeriv ℝ (k - i) G x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (M * B) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hM R hR i (by omega) x)
          (hGB (k - i) (by omega) x) (norm_nonneg _) hM0) (Nat.cast_nonneg _)
    _ = 2 ^ k * (M * B) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k
    _ ≤ 4 * (M * B) := by
        have : (2 : ℝ) ^ k ≤ 4 := by
          calc (2 : ℝ) ^ k ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hk
            _ = 4 := by norm_num
        exact mul_le_mul_of_nonneg_right this (mul_nonneg hM0 hB0)

/-- **Dominated convergence in `L²`** with an `L²` dominating function. -/
theorem tendsto_eLpNorm_two_of_dom {γ : Measure (ℕ → ℝ)} {F : ℕ → (ℕ → ℝ) → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (F n) γ) {g : (ℕ → ℝ) → ℝ} (hg : MemLp g 2 γ)
    (hB : ∀ n z, |F n z| ≤ g z) (hlim : ∀ z, Tendsto (fun n => F n z) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 γ) atTop (𝓝 0) := by
  have e : ∀ n, eLpNorm (F n) 2 γ = (∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    fun n => eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hm n)
  simp_rw [e]
  have hfin : ∫⁻ z, ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hg.eLpNorm_lt_top).ne
  have hint : Tendsto (fun n => ∫⁻ z, ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal ∂γ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := γ)
      (F := fun n z => ‖F n z‖ₑ ^ (2 : ℝ≥0∞).toReal) (f := fun _ => 0)
      (fun z => ‖g z‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (fun n => ((hm n).enorm).pow_const _)
      (fun n => Eventually.of_forall fun z => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by
          rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact (hB n z).trans (le_abs_self _)))
      hfin
      (Eventually.of_forall fun z => by
        have h1 : Tendsto (fun n => ‖F n z‖ₑ) atTop (𝓝 0) := by
          have := (continuous_enorm.tendsto (0 : ℝ)).comp (hlim z)
          simpa [Function.comp_def] using this
        have := (ENNReal.continuous_rpow_const (y := (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp h1
        simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this)
    simpa using this
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ≥0∞).toReal)).tendsto 0 |>.comp hint
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this

/-- `χ_R G = G` near `x` when `‖x‖ + 1 < R`: the partial derivatives agree near `x`. -/
theorem pd_chiR_mul_eventuallyEq {N : ℕ} {G : (Fin N → ℝ) → ℝ} {R : ℝ} (hR : 0 < R)
    {x : Fin N → ℝ} (hx : ‖x‖ + 1 < R) (i : Fin N) :
    pd (fun y => chiR N R y * G y) i =ᶠ[𝓝 x] pd G i := by
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have hloc : (fun w => chiR N R w * G w) =ᶠ[𝓝 y] G := by
    have hy' : ‖y‖ < R := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith [norm_le_insert' y x]
    filter_upwards [Metric.ball_mem_nhds y (sub_pos.2 hy')] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    rw [chiR_eq_one hR (by linarith [norm_le_insert' w y]), one_mul]
  unfold pd
  rw [hloc.fderiv_eq]

/-- The generator on a smooth function of the first `N` coordinates. -/
noncomputable def genG (lam' : ℕ → ℝ) (Y : ℕ → (ℕ → ℝ) → ℝ) (N : ℕ) (G : (Fin N → ℝ) → ℝ)
    (z : ℕ → ℝ) : ℝ :=
  ∑ i : Fin N, lam' i * (d2 G i (zBlock N z) - (z i + Y i z) * pd G i (zBlock N z))

theorem Cyl.gen_eq_genG (lam' : ℕ → ℝ) (Y : ℕ → (ℕ → ℝ) → ℝ) (c : Cyl) :
    c.gen lam' Y = genG lam' Y c.J c.φ := rfl

theorem continuous_pd {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin N) :
    Continuous (pd f i) := (contDiff_pd hf i).continuous

theorem continuous_d2 {N : ℕ} {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin N) :
    Continuous (d2 f i) :=
  ((contDiff_pd hf i).continuous_fderiv (by simp)).clm_apply continuous_const

/-- **(iii)** `L(χ_n G) → L G` in `L²(γ)`. -/
theorem tendsto_cutCyl_gen {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {N : ℕ} {G : (Fin N → ℝ) → ℝ}
    (hG : ContDiff ℝ ∞ G) {B : ℝ} (hGB : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k G x‖ ≤ B)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ)
    (hY : ∀ i, MemLp (Y i) 2 γ) (lam' : ℕ → ℝ) :
    Tendsto (fun n => eLpNorm (fun z => (cutCyl N hG n).gen lam' Y z - genG lam' Y N G z) 2 γ)
      atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_iteratedFDeriv_chiR_bound N
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hGB 0 (by norm_num) 0)
  set K := 4 * (M * B) + B
  have hK0 : 0 ≤ K := by positivity
  set χG : ℕ → (Fin N → ℝ) → ℝ := fun n y => chiR N ((n : ℝ) + 1) y * G y
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hχ : ∀ n, ContDiff ℝ ∞ (χG n) := fun n => (contDiff_chiR N _).mul hG
  have hb1 : ∀ n i x, |pd (χG n) i x| ≤ K := fun n i x =>
    (abs_pd_le_iter i x).trans ((norm_iteratedFDeriv_chiR_mul_le hG hGB hM0 hM (hR1 n)
      (by norm_num) x).trans (by simp [K]; linarith))
  have hb2 : ∀ n i x, |d2 (χG n) i x| ≤ K := fun n i x =>
    (abs_d2_le (hχ n) i x).trans ((norm_iteratedFDeriv_chiR_mul_le hG hGB hM0 hM (hR1 n)
      (le_refl 2) x).trans (by simp [K]; linarith))
  have hg1 : ∀ i x, |pd G i x| ≤ K := fun i x =>
    (abs_pd_le_iter i x).trans ((hGB 1 (by norm_num) x).trans (by simp [K]; positivity))
  have hg2 : ∀ i x, |d2 G i x| ≤ K := fun i x =>
    (abs_d2_le hG i x).trans ((hGB 2 le_rfl x).trans (by simp [K]; positivity))
  set g : (ℕ → ℝ) → ℝ := fun z => ∑ i : Fin N, |lam' i| * (2 * K + 2 * K * |z i + Y i z|)
  have hgL : MemLp g 2 γ := by
    refine memLp_finsetSum (ε' := ℝ) _ fun i _ => ?_
    have h1 : MemLp (fun z : ℕ → ℝ => z i + Y i z) 2 γ := (hz i).add (hY i)
    have h2 : MemLp (fun z : ℕ → ℝ => |z i + Y i z|) 2 γ := h1.abs
    have h3 : MemLp (fun z : ℕ → ℝ => 2 * K + 2 * K * |z i + Y i z|) 2 γ :=
      (memLp_const (2 * K)).add (h2.const_mul (2 * K))
    exact h3.const_mul |lam' i|
  refine tendsto_eLpNorm_two_of_dom (g := g) (fun n => ?_) hgL (fun n z => ?_) fun z => ?_
  · -- measurability
    rw [Cyl.gen_eq_genG]
    refine (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_).sub
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_)
    · exact aestronglyMeasurable_const.mul (((continuous_d2 (hχ n) i).measurable.comp
        (measurable_zBlock N)).aestronglyMeasurable.sub ((((hz i).add (hY i)).aestronglyMeasurable).mul
        ((continuous_pd (hχ n) i).measurable.comp (measurable_zBlock N)).aestronglyMeasurable))
    · exact aestronglyMeasurable_const.mul (((continuous_d2 hG i).measurable.comp
        (measurable_zBlock N)).aestronglyMeasurable.sub ((((hz i).add (hY i)).aestronglyMeasurable).mul
        ((continuous_pd hG i).measurable.comp (measurable_zBlock N)).aestronglyMeasurable))
  · -- domination
    show |genG lam' Y N (χG n) z - genG lam' Y N G z| ≤ g z
    unfold genG
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have e : d2 (χG n) i (zBlock N z) - (z i + Y i z) * pd (χG n) i (zBlock N z) -
        (d2 G i (zBlock N z) - (z i + Y i z) * pd G i (zBlock N z)) =
        (d2 (χG n) i (zBlock N z) - d2 G i (zBlock N z)) -
          (z i + Y i z) * (pd (χG n) i (zBlock N z) - pd G i (zBlock N z)) := by ring
    rw [e]
    have hb2' := hb2 n i (zBlock N z)
    have hg2' := hg2 i (zBlock N z)
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (by linarith)) ?_)
    rw [abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ((abs_sub _ _).trans ?_) (abs_nonneg _)
    linarith [hb1 n i (zBlock N z), hg1 i (zBlock N z)]
  · -- eventually zero
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨m, hm⟩ := exists_nat_gt (‖zBlock N z‖ + 1)
    filter_upwards [eventually_ge_atTop m] with n hn
    have hx : ‖zBlock N z‖ + 1 < (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    show 0 = genG lam' Y N (χG n) z - genG lam' Y N G z
    unfold genG
    rw [← Finset.sum_sub_distrib]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    have h1 := pd_chiR_mul_eventuallyEq (G := G) hR hx i
    have hpd : pd (χG n) i (zBlock N z) = pd G i (zBlock N z) := h1.eq_of_nhds
    have hd2 : d2 (χG n) i (zBlock N z) = d2 G i (zBlock N z) := by
      unfold d2; rw [h1.fderiv_eq]
    rw [hpd, hd2]; ring

end SharpLSI
