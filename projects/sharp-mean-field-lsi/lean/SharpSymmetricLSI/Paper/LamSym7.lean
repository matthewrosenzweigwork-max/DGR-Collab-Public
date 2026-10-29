import SharpSymmetricLSI.Paper.LamSym6
import SharpSymmetricLSI.Paper.TestEnergy7

/-!
# (2.8) (lane s42): variance and energy limits of the linear test statistics

`linStat e N n v = ∑_{i<n} v_i Z_{N,i}` (manuscript Section 8.5).
* `tendsto_var_linStat`: `Var_{P_N}(linStat) → ⟨v, C v⟩`, from the convergence in law of the
  fluctuations (R27) and `∫ exp(a linStat²) dP_N ≤ B` (hypothesis; the linear-test drafts
  derive it from `lintegral_exp_sq_sum_le`).
* `tendsto_energy_of_mob`: if `|∇ f_N|² = ∑_{i,j<n} v_i v_j A_{N,ij}` a.e. (the mobility identity,
  hypothesis) with `A_{N,ij}` bounded and `E_{P_N}|A_{N,ij} - D_{ij}| → 0`, then
  `ℰ_N(f_N) → ∑ v_i v_j D_{ij}`; with `tendsto_gibbs_abs_mob` and `sum_diag_mob`,
  `ℰ_N(f_N) → ∑ λ'_i v_i²` (`tendsto_energy_linStat`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Finset
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The linear test statistic `∑_{i<n} v_i Z_{N,i}`. -/
noncomputable def linStat (e : ℕ → Torus d → ℝ) (N n : ℕ) (v : ℕ → ℝ) (X : Config N d) : ℝ :=
  ∑ i ∈ range n, v i * fluct e N i X

theorem fourth_le_exp {a : ℝ} (ha : 0 < a) (t : ℝ) :
    t ^ 4 ≤ 2 / a ^ 2 * Real.exp (a * t ^ 2) := by
  have h : (a * t ^ 2) ^ 2 / 2 ≤ Real.exp (a * t ^ 2) := by
    simpa [Nat.factorial] using Real.pow_div_factorial_le_exp (a * t ^ 2) (by positivity) 2
  have h2 : a ^ 2 * t ^ 4 ≤ 2 * Real.exp (a * t ^ 2) := by nlinarith [h]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- A uniform `exp(a Y²)` bound gives a uniform fourth moment bound. -/
theorem fourth_moment_of_exp {α : Type*} [MeasurableSpace α] {m : Measure α} {Y : α → ℝ}
    (hY : AEStronglyMeasurable Y m) {a : ℝ} (ha : 0 < a) {B : ℝ≥0∞} (hBt : B ≠ ⊤)
    (hB : ∫⁻ x, ENNReal.ofReal (Real.exp (a * Y x ^ 2)) ∂m ≤ B) :
    Integrable (fun x => Y x ^ 4) m ∧ ∫ x, Y x ^ 4 ∂m ≤ 2 / a ^ 2 * B.toReal := by
  have hexm : AEStronglyMeasurable (fun x => Real.exp (a * Y x ^ 2)) m :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).comp_aestronglyMeasurable hY
  have hexp : Integrable (fun x => Real.exp (a * Y x ^ 2)) m := by
    refine ⟨hexm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact lt_of_le_of_lt hB (lt_top_iff_ne_top.mpr hBt)
  have h4 : Integrable (fun x => Y x ^ 4) m :=
    Integrable.mono' (hexp.const_mul (2 / a ^ 2)) (hY.pow 4)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact fourth_le_exp ha (Y x))
  refine ⟨h4, ?_⟩
  calc ∫ x, Y x ^ 4 ∂m ≤ ∫ x, 2 / a ^ 2 * Real.exp (a * Y x ^ 2) ∂m :=
        integral_mono h4 (hexp.const_mul _) fun x => fourth_le_exp ha (Y x)
    _ = 2 / a ^ 2 * ∫ x, Real.exp (a * Y x ^ 2) ∂m := integral_const_mul _ _
    _ ≤ 2 / a ^ 2 * B.toReal := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (Real.exp_pos _).le)
          hexm]
        exact ENNReal.toReal_mono hBt hB

/-- **The variance of the linear statistic converges to `⟨v, Cv⟩`.** -/
theorem tendsto_var_linStat (hyp : Hyp V W KV KW) {e : ℕ → Torus d → ℝ}
    {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C)
    (hlaw : ∀ (J : ℕ) (g : (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (fun i => fluct e N i X) ∂gibbs V W N) atTop
        (𝓝 (∫ z, g (fun i => z i) ∂γ)))
    (n : ℕ) (v : ℕ → ℝ) (hQ : 0 ≤ ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j)
    (hL2 : ∀ᶠ N in atTop, MemLp (linStat e N n v) 2 (gibbs V W N))
    (hmom : ∃ a : ℝ, 0 < a ∧ ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ᶠ N in atTop,
      ∫⁻ X, ENNReal.ofReal (Real.exp (a * linStat e N n v X ^ 2)) ∂gibbs V W N ≤ B) :
    Tendsto (fun N => var (gibbs V W N) (linStat e N n v)) atTop
      (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j))) := by
  haveI := hγ.1
  haveI : ∀ N, IsProbabilityMeasure (gibbs V W N) := fun N => gibbs_isProbabilityMeasure hyp N
  obtain ⟨a, ha, B, hBt, hB⟩ := hmom
  set ℓ : (ℕ → ℝ) → ℝ := fun z => ∑ i ∈ range n, v i * z i
  have hℓm : Measurable ℓ := measurable_linSum _ v
  set ν := γ.map ℓ
  haveI : IsProbabilityMeasure ν := inferInstance
  -- convergence in law of the linear statistic
  set L : C(Fin n → ℝ, ℝ) := ⟨fun z => ∑ i : Fin n, v i * z i,
    continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_apply i)⟩
  have hlaw' : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ X, g (linStat e N n v X) ∂gibbs V W N) atTop
      (𝓝 (∫ x, g x ∂ν)) := fun g => by
    have h := hlaw n (g.compContinuous L)
    simp only [BoundedContinuousFunction.compContinuous_apply] at h
    have e1 : ∀ N (X : Config N d), L (fun i => fluct e N i X) = linStat e N n v X := fun N X => by
      simp only [L, ContinuousMap.coe_mk, linStat]
      exact (Finset.sum_range fun i => v i * fluct e N i X).symm
    have e2 : ∀ z : ℕ → ℝ, L (fun i => z i) = ℓ z := fun z => by
      simp only [L, ContinuousMap.coe_mk, ℓ]
      exact (Finset.sum_range fun i => v i * z i).symm
    simp_rw [e1, e2] at h
    rw [integral_map hℓm.aemeasurable g.continuous.aestronglyMeasurable]
    exact h
  have hB4 : ∀ᶠ N in atTop, Integrable (fun X => linStat e N n v X ^ 4) (gibbs V W N) ∧
      ∫ X, linStat e N n v X ^ 4 ∂gibbs V W N ≤ 2 / a ^ 2 * B.toReal := by
    filter_upwards [hL2, hB] with N hN hBN
    exact fourth_moment_of_exp hN.aestronglyMeasurable ha hBt hBN
  -- every `Y_N` is a.e.-strongly measurable from some point on; replace by `0` before
  obtain ⟨N0, hN0⟩ := hL2.exists_forall_of_atTop
  set Y : (N : ℕ) → Config N d → ℝ := fun N => if N0 ≤ N then linStat e N n v else fun _ => 0
  have hYeq : ∀ᶠ N in atTop, Y N = linStat e N n v := by
    filter_upwards [eventually_ge_atTop N0] with N hN; simp [Y, hN]
  have hYm : ∀ N, AEStronglyMeasurable (Y N) (gibbs V W N) := fun N => by
    by_cases h : N0 ≤ N
    · simp only [Y, if_pos h]; exact (hN0 N h).aestronglyMeasurable
    · simp only [Y, if_neg h]; exact aestronglyMeasurable_const
  have hlawY : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ X, g (Y N X) ∂gibbs V W N) atTop
      (𝓝 (∫ x, g x ∂ν)) := fun g =>
    (hlaw' g).congr' (by filter_upwards [hYeq] with N hN; rw [hN])
  have hBY : ∀ᶠ N in atTop, Integrable (fun X => Y N X ^ 4) (gibbs V W N) ∧
      ∫ X, Y N X ^ 4 ∂gibbs V W N ≤ 2 / a ^ 2 * B.toReal := by
    filter_upwards [hB4, hYeq] with N hN hNe; rw [hNe]; exact hN
  obtain ⟨-, h1⟩ := tendsto_integral_pow_of_law hYm hlawY hBY (k := 1) (by norm_num)
  obtain ⟨-, h2⟩ := tendsto_integral_pow_of_law hYm hlawY hBY (k := 2) (by norm_num)
  have hm1 : ∫ x : ℝ, x ^ 1 ∂ν = 0 := by
    rw [integral_map hℓm.aemeasurable (continuous_pow 1).aestronglyMeasurable]
    simp only [pow_one]; exact integral_linSum_gamma hγ _ v
  have hm2 : ∫ x : ℝ, x ^ 2 ∂ν = ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j := by
    rw [integral_map hℓm.aemeasurable (continuous_pow 2).aestronglyMeasurable]
    exact integral_linSum_sq_gamma hγ _ v hQ
  rw [hm1] at h1
  rw [hm2] at h2
  have hvar : Tendsto (fun N => ENNReal.ofReal (∫ X, Y N X ^ 2 ∂gibbs V W N -
      (∫ X, Y N X ^ 1 ∂gibbs V W N) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j - 0 ^ 2))) :=
    ENNReal.tendsto_ofReal (h2.sub (h1.pow 2))
  rw [show ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j - (0 : ℝ) ^ 2 =
    ∑ i ∈ range n, ∑ j ∈ range n, v i * C i j * v j by ring] at hvar
  refine hvar.congr' ?_
  filter_upwards [hYeq, hL2] with N hN hNL
  rw [hN]
  show _ = evariance _ _
  rw [← hNL.ofReal_variance_eq, variance_eq_sub hNL]
  simp only [pow_one, Pi.pow_apply]

/-- **The energy converges**, given the mobility identity. -/
theorem tendsto_energy_of_mob (hyp : Hyp V W KV KW) {f : (N : ℕ) → Config N d → ℝ}
    {A : (N : ℕ) → Config N d → ℕ → ℕ → ℝ} (n : ℕ) (v : ℕ → ℝ) {D : ℕ → ℕ → ℝ} {M : ℝ}
    (hAm : ∀ N i j, Measurable fun X => A N X i j) (hAb : ∀ N X i j, |A N X i j| ≤ M)
    (hA : ∀ i j, Tendsto (fun N => ∫ X, |A N X i j - D i j| ∂gibbs V W N) atTop (𝓝 0))
    (hmob : ∀ᶠ N in atTop, (fun X => gradSqC (f N) X) =ᵐ[gibbs V W N]
      fun X => ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A N X i j) :
    Tendsto (fun N => energy V W N (f N)) atTop
      (𝓝 (ENNReal.ofReal (∑ i ∈ range n, ∑ j ∈ range n, v i * v j * D i j))) := by
  haveI : ∀ N, IsProbabilityMeasure (gibbs V W N) := fun N => gibbs_isProbabilityMeasure hyp N
  have hAi : ∀ N i j, Integrable (fun X => A N X i j) (gibbs V W N) := fun N i j =>
    Integrable.of_bound (hAm N i j).aestronglyMeasurable M
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hAb N X i j)
  have hSi : ∀ N, Integrable (fun X => ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A N X i j)
      (gibbs V W N) := fun N =>
    integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hAi N i j).const_mul _
  have hint : ∀ N, ∫ X, ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A N X i j ∂gibbs V W N =
      ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * ∫ X, A N X i j ∂gibbs V W N := fun N => by
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (hAi N i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun j _ => (hAi N i j).const_mul _]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hlimA : ∀ i j, Tendsto (fun N => ∫ X, A N X i j ∂gibbs V W N) atTop (𝓝 (D i j)) :=
    fun i j => by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) (hA i j)
      rw [Real.norm_eq_abs]
      have : ∫ X, A N X i j ∂gibbs V W N - D i j = ∫ X, (A N X i j - D i j) ∂gibbs V W N := by
        rw [integral_sub (hAi N i j) (integrable_const _)]; simp
      rw [this]
      exact abs_integral_le_integral_abs
  have hlimS : Tendsto (fun N => ∫ X, ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A N X i j
      ∂gibbs V W N) atTop (𝓝 (∑ i ∈ range n, ∑ j ∈ range n, v i * v j * D i j)) := by
    simp_rw [hint]
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      (hlimA i j).const_mul _
  refine (ENNReal.tendsto_ofReal hlimS).congr' ?_
  filter_upwards [hmob] with N hN
  have hnn : 0 ≤ᵐ[gibbs V W N] fun X => ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * A N X i j := by
    filter_upwards [hN] with X hX
    rw [← hX]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  unfold energy
  rw [ofReal_integral_eq_lintegral_ofReal (hSi N) hnn]
  refine lintegral_congr_ae ?_
  filter_upwards [hN] with X hX
  rw [hX]

/-- **The energy of the linear statistic converges to `∑ λ'_i v_i²`**, given the mobility
identity, from `tendsto_gibbs_abs_mob`. -/
theorem tendsto_energy_linStat (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e eC : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j)
    (hpart : ∃ Bp p : ℝ, 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    {f : (N : ℕ) → Config N d → ℝ} (n : ℕ) (v : ℕ → ℝ)
    (hmob : ∀ᶠ N in atTop, (fun X => gradSqC (f N) X) =ᵐ[gibbs V W N]
      fun X => ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * mobA eC N X i j) :
    Tendsto (fun N => energy V W N (f N)) atTop
      (𝓝 (ENNReal.ofReal (∑ i ∈ range n, lamShift lam i * v i ^ 2))) := by
  -- a uniform bound for the mobility entries
  have hbd : ∀ i j, ∃ K, ∀ N X, |mobA eC N X i j| ≤ K := fun i j => by
    obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i + 1))
    obtain ⟨Cj, hCj⟩ := exists_bound_cgrad (hφ (j + 1))
    refine ⟨d * (|Ci| * |Cj|), fun N X => abs_mobA_le (fun x => ?_) N X⟩
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |cgrad (eC (i + 1)) x k * cgrad (eC (j + 1)) x k| ≤ ∑ _k : Fin d, |Ci| * |Cj| :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul]
            exact mul_le_mul ((hCi x k).trans (le_abs_self _)) ((hCj x k).trans (le_abs_self _))
              (abs_nonneg _) (abs_nonneg _)
      _ = d * (|Ci| * |Cj|) := by simp
  choose K hK using hbd
  set M := ∑ i ∈ range n, ∑ j ∈ range n, |K i j|
  have hM : ∀ N X i j, i ∈ range n → j ∈ range n → |mobA eC N X i j| ≤ M := by
    intro N X i j hi hj
    refine (hK i j N X).trans ((le_abs_self _).trans ?_)
    exact (Finset.single_le_sum (f := fun j => |K i j|) (fun _ _ => abs_nonneg _) hj).trans
      (Finset.single_le_sum (f := fun i => ∑ j ∈ range n, |K i j|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) hi)
  -- truncate the indices to `range n`
  set A : (N : ℕ) → Config N d → ℕ → ℕ → ℝ := fun N X i j =>
    if i ∈ range n ∧ j ∈ range n then mobA eC N X i j else 0
  set D : ℕ → ℕ → ℝ := fun i j =>
    if i ∈ range n ∧ j ∈ range n then (if i = j then lamShift lam i else 0) else 0
  have h := tendsto_energy_of_mob hyp (f := f) (A := A) (D := D) (M := M) n v
    (fun N i j => by
      simp only [A]; split_ifs
      · exact measurable_mobA hφ N i j
      · exact measurable_const)
    (fun N X i j => by
      simp only [A]; split_ifs with h
      · exact hM N X i j h.1 h.2
      · simp only [abs_zero]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          abs_nonneg _)
    (fun i j => by
      by_cases h : i ∈ range n ∧ j ∈ range n
      · simp only [A, D, if_pos h]
        exact tendsto_gibbs_abs_mob hyp hμ he hφ heC hpart i j
      · simp only [A, D, if_neg h, sub_zero, abs_zero, integral_zero]
        exact tendsto_const_nhds)
    (by
      filter_upwards [hmob] with N hN
      filter_upwards [hN] with X hX
      rw [hX]
      refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
      simp only [A, if_pos (And.intro hi hj)])
  have e : ∑ i ∈ range n, ∑ j ∈ range n, v i * v j * D i j =
      ∑ i ∈ range n, lamShift lam i * v i ^ 2 := by
    rw [← sum_diag_mob]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [D, if_pos (And.intro hi hj)]
  rw [e] at h
  exact h

end SharpLSI
