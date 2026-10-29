import SharpSymmetricLSI.Paper.FormLiminfS2

/-!
# (8.20), Gaussian side (lane s42): the `R`-limit of the row terms

`tendsto_gauss_row_term`: for the finite-rank kernels `K_R = ∑_{i,j∈s_R} a^R_{ij} e_{i+1} ⊗ e_{j+1}`
((6.4)), `∫ F ∑_i ψ_i ∑_{p,q∈s_R} a^R_{pq} z_q [p = i] dγ → ∫ F ∑_i ψ_i Y_i dγ`. The inner sum is
the finite row `∑_{q<n} kerMat(K_R)_{iq} z_q` for `n` large (`kerMat_eq_zero_of_not_mem`); by
`rowVar_approx` it converges to `Y_i` in `L²(γ)`, and `|∫ F ψ_i (S - Y_i)| ≤ ‖Fψ_i‖₂ ‖S - Y_i‖₂`.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The `R`-limit of the Gaussian row terms.** -/
theorem tendsto_gauss_row_term {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {KR : ℕ → Torus d → Torus d → ℝ} (hKR : IsKernelApprox W μ e KR)
    {s : ℕ → Finset ℕ} {a : ℕ → ℕ → ℕ → ℝ}
    (hK : ∀ R x y, KR R x y = ∑ i ∈ s R, ∑ j ∈ s R, a R i j * e (i + 1) x * e (j + 1) y)
    (h21 : Prop21Conclusion V W μ) {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C) {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i)) {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    {J : ℕ} (ψ : Fin J → (ℕ → ℝ) → ℝ) (hψm : ∀ i, Measurable (ψ i)) {K : ℝ}
    (hψ : ∀ i z, |ψ i z| ≤ K) :
    Tendsto (fun R => ∫ z, F z * ∑ i : Fin J, ψ i z * ∑ p ∈ s R, ∑ q ∈ s R,
        a R p q * z q * (if p = (i : ℕ) then 1 else 0) ∂γ) atTop
      (𝓝 (∫ z, F z * ∑ i : Fin J, ψ i z * Y i z ∂γ)) := by
  haveI := hγ.1
  -- the finite rows
  set N : ℕ → ℕ := fun R => (s R).sup id + 1
  have hsN : ∀ R, s R ⊆ Finset.range (N R) := fun R q hq => by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)
  set S : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun R i z =>
    ∑ q ∈ Finset.range (N R), kerMat (KR R) μ e i q * z q
  have hkm : ∀ R p q, kerMat (KR R) μ e p q = if p ∈ s R ∧ q ∈ s R then a R p q else 0 :=
    fun R p q => kerMat_eq_zero_of_not_mem he (hK R) p q
  -- the inner sum is the finite row, for every `n ≥ N R`
  have hrow : ∀ R (i : ℕ) n, N R ≤ n → ∀ z : ℕ → ℝ, ∑ q ∈ Finset.range n, kerMat (KR R) μ e i q * z q =
      ∑ p ∈ s R, ∑ q ∈ s R, a R p q * z q * (if p = i then 1 else 0) := fun R i n hn z => by
    have hsub : s R ⊆ Finset.range n := (hsN R).trans (Finset.range_subset_range.2 hn)
    rw [← Finset.sum_subset hsub (fun q _ hq => by rw [hkm, if_neg (fun h => hq h.2), zero_mul])]
    by_cases hi : i ∈ s R
    · rw [Finset.sum_eq_single i (fun p _ hp => Finset.sum_eq_zero fun q _ => by
        rw [if_neg hp, mul_zero]) (fun h => absurd hi h)]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [hkm, if_pos ⟨hi, hq⟩, if_pos rfl, mul_one]
    · rw [Finset.sum_eq_zero fun q hq => by rw [hkm, if_neg (fun h => hi h.1), zero_mul]]
      exact (Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q _ => by
        rw [if_neg (fun (h : p = i) => hi (h ▸ hp)), mul_zero]).symm
  -- `L²` convergence of the rows
  have hconv : ∀ i : ℕ, Tendsto (fun R => ∫ z, (S R i z - Y i z) ^ 2 ∂γ) atTop (𝓝 0) := fun i => by
    have h := rowVar_approx hyp hμ he hKR h21 hC hγ hY i
    refine h.congr fun R => ?_
    have hev : (fun n => ∫ z, (∑ q ∈ Finset.range n, kerMat (KR R) μ e i q * z q - Y i z) ^ 2 ∂γ)
        =ᶠ[atTop] fun _ => ∫ z, (S R i z - Y i z) ^ 2 ∂γ := by
      filter_upwards [eventually_ge_atTop (N R)] with n hn
      congr 1; funext z
      simp only [S]
      rw [hrow R i n hn z, hrow R i (N R) le_rfl z]
    rw [limsup_congr hev, limsup_const]
  -- the bound for each `i`
  have hFψ : ∀ i : Fin J, MemLp (fun z => F z * ψ i z) 2 γ := fun i => by
    refine (hF.norm.const_mul K).of_le (hF.aestronglyMeasurable.mul (hψm i).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hψ i z)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      K * ‖F z‖), Real.norm_eq_abs, mul_comm K]
    exact mul_le_mul_of_nonneg_left (hψ i z) (abs_nonneg _)
  have hSm : ∀ R i, MemLp (S R i) 2 γ := fun R i => memLp_linSum_gamma hγ _ _
  have hDm : ∀ R (i : ℕ), MemLp (fun z => S R i z - Y i z) 2 γ := fun R i =>
    (hSm R i).sub (hY i).1
  have hint : ∀ (G : ℕ → (ℕ → ℝ) → ℝ), (∀ i, MemLp (G i) 2 γ) →
      ∫ z, F z * ∑ i : Fin J, ψ i z * G i z ∂γ = ∑ i : Fin J, ∫ z, (F z * ψ i z) * G i z ∂γ :=
    fun G hG => by
      rw [← integral_finsetSum (f := fun (i : Fin J) z => (F z * ψ i z) * G i z) _ fun i _ =>
        (hFψ i).integrable_mul (hG i)]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  -- rewrite the sequence
  have hseq : ∀ R, ∫ z, F z * ∑ i : Fin J, ψ i z * ∑ p ∈ s R, ∑ q ∈ s R,
      a R p q * z q * (if p = (i : ℕ) then 1 else 0) ∂γ =
        ∑ i : Fin J, ∫ z, (F z * ψ i z) * S R i z ∂γ := fun R => by
    rw [← hint (fun i => S R i) (hSm R)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [S]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrow R i (N R) le_rfl z]
  simp only [hseq]
  rw [hint Y fun i => (hY i).1]
  refine tendsto_finsetSum _ fun i _ => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbd : ∀ R, ‖∫ z, (F z * ψ i z) * S R i z ∂γ - ∫ z, (F z * ψ i z) * Y i z ∂γ‖ ≤
      (eLpNorm (fun z => F z * ψ i z) 2 γ).toReal * √(∫ z, (S R i z - Y i z) ^ 2 ∂γ) := fun R => by
    rw [← integral_sub (f := fun z => (F z * ψ i z) * S R i z) (g := fun z => (F z * ψ i z) * Y i z)
      ((hFψ i).integrable_mul (hSm R i)) ((hFψ i).integrable_mul (hY i).1), Real.norm_eq_abs]
    have e1 : (fun z => F z * ψ i z * S R i z - F z * ψ i z * Y i z) =
        fun z => (F z * ψ i z) * (S R i z - Y i z) := by funext z; ring
    rw [e1]
    refine (abs_integral_mul_le_L2 (hFψ i) (hDm R i)).trans (le_of_eq ?_)
    rw [eLpNorm_two_eq_sqrt_gamma (hDm R i), ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  refine squeeze_zero (fun _ => norm_nonneg _) hbd ?_
  have := ((hconv i).sqrt).const_mul (eLpNorm (fun z => F z * ψ i z) 2 γ).toReal
  simpa using this

end SharpLSI
