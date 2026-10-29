import SharpSymmetricLSI.Paper.Occ11

/-!
# Deterministic inputs for the joint law of the occupation basis (Phase 3, lane D; R28(d))
-/

noncomputable section
open MvPolynomial Finset.HasAntidiagonal Filter Topology

namespace SharpLSI

variable {K N : ℕ}

theorem coeff_linForm_pow (b : Fin K → ℝ) (m : ℕ) (γ : Fin K →₀ ℕ) :
    (linForm b ^ m).coeff γ = ∑ p : Fin m → Fin K,
      if ∑ t, Finsupp.single (p t) 1 = γ then ∏ t, b (p t) else 0 := by
  classical
  unfold linForm
  rw [Fintype.sum_pow, coeff_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp_rw [C_mul_X_eq_monomial]
  rw [← monomial_sum_prod, coeff_monomial]

theorem continuous_coeff_linForm_pow (m : ℕ) (γ : Fin K →₀ ℕ) :
    Continuous fun b : Fin K → ℝ => (linForm b ^ m).coeff γ := by
  simp_rw [coeff_linForm_pow]
  refine continuous_finsetSum _ fun p _ => ?_
  split_ifs
  · exact continuous_finsetProd _ fun t _ => continuous_apply _
  · exact continuous_const

theorem continuous_newtonCoeff (j : Fin K) (γ : Fin K →₀ ℕ) :
    Continuous fun a : Fin N → Fin K → ℝ => newtonCoeff a j γ := by
  unfold newtonCoeff
  refine continuous_const.mul (continuous_finsetSum _ fun i _ => Continuous.mul ?_ ?_)
  · show Continuous fun a : Fin N → Fin K → ℝ => a i j
    fun_prop
  · exact (continuous_coeff_linForm_pow _ _).comp (continuous_apply i)

theorem newtonRec_congr {q q' : Fin K → (Fin K →₀ ℕ) → ℝ} :
    ∀ n α, (∀ j γ, γ.degree < α.degree → q j γ = q' j γ) → newtonRec q n α = newtonRec q' n α := by
  intro n
  induction n with
  | zero => intro α _; rfl
  | succ n ih =>
    intro α hq
    by_cases h : α = 0
    · simp [newtonRec, h]
    simp only [newtonRec, dite_eq_right h]
    set j := α.support.min' (Finsupp.support_nonempty_iff.mpr h)
    have hj : α j ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    have hle : Finsupp.single j 1 ≤ α := by rw [Finsupp.single_le_iff]; omega
    have hdeg : (α - Finsupp.single j 1).degree + 1 = α.degree := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle]
      rw [map_add, Finsupp.degree_single]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have h1 := degree_le_of_mem_antidiagonal hx
    rw [ih x.1 fun j' γ hγ => hq j' γ (by omega), hq j x.2 (by omega)]

theorem newtonRec_scaled (s : ℝ) (a : Fin N → Fin K → ℝ) :
    ∀ n α, α.degree ≤ n → newtonRec (fun j γ => s ^ (γ.degree + 1) * newtonCoeff a j γ) n α =
      s ^ α.degree * (genPoly a).coeff α := by
  refine newtonRec_eq (by simp [genPoly_coeff_zero]) fun α j => ?_
  rw [map_add, Finsupp.degree_single, pow_succ]
  calc ((α j : ℝ) + 1) * (s ^ α.degree * s * (genPoly a).coeff (α + Finsupp.single j 1))
      = s ^ α.degree * s * (((α j : ℝ) + 1) * (genPoly a).coeff (α + Finsupp.single j 1)) := by
        ring
    _ = _ := by
      rw [newton_genPoly, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)
      have : α.degree = x.1.degree + x.2.degree := by rw [← hx', map_add]
      rw [this, pow_add]
      ring

theorem degree_finK (α : ℕ →₀ ℕ) (hK : ∀ n, K ≤ n → α n = 0) :
    (finK K α).degree = occSize α := by
  rw [Finsupp.degree_eq_sum]
  simp only [finK_apply]
  rw [Fin.sum_univ_eq_sum_range (fun n => α n)]
  unfold occSize Finsupp.sum
  refine (Finset.sum_subset (fun n hn => Finset.mem_range.mpr ?_) fun n _ hn => ?_).symm
  · by_contra h; exact Finsupp.mem_support_iff.mp hn (hK n (by omega))
  · simpa using hn

theorem sqrt_prod' {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb,
      Real.sqrt_mul (hf b (Finset.mem_insert_self _ _)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem hermiteBasis_eq_hermLim (α : ℕ →₀ ℕ) (hK : ∀ n, K ≤ n → α n = 0) (z : ℕ → ℝ) :
    hermiteBasis α z = Real.sqrt (occFactorial α) * hermLim (fun k : Fin K => z k) (finK K α) := by
  have h1 : hermLim (fun k : Fin K => z k) (finK K α) = ∏ n ∈ α.support, hermNorm (z n) (α n) := by
    unfold hermLim
    simp only [finK_apply]
    rw [Fin.prod_univ_eq_prod_range (fun n => hermNorm (z n) (α n))]
    refine (Finset.prod_subset (fun n hn => Finset.mem_range.mpr ?_) fun n _ hn => ?_).symm
    · by_contra h; exact Finsupp.mem_support_iff.mp hn (hK n (by omega))
    · have : α n = 0 := by simpa using hn
      rw [this, hermNorm_zero]
  have h2 : (occFactorial α : ℝ) = ∏ n ∈ α.support, ((α n).factorial : ℝ) := by
    unfold occFactorial Finsupp.prod; push_cast; rfl
  rw [h1, h2, sqrt_prod' _ _ fun n _ => by positivity, ← Finset.prod_mul_distrib]
  unfold hermiteBasis
  refine Finset.prod_congr rfl fun n _ => ?_
  unfold hermNorm
  have hpos : (0 : ℝ) < Real.sqrt ((α n).factorial : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt ((α n).factorial : ℝ) ^ 2 = ((α n).factorial : ℝ) :=
    Real.sq_sqrt (by positivity)
  field_simp
  rw [hsq]

/-! ### Deterministic limits -/

theorem tendsto_descFactorial_div_pow (k : ℕ) :
    Tendsto (fun N : ℕ => (N.descFactorial k : ℝ) / (N : ℝ) ^ k) atTop (𝓝 1) := by
  have hlim : Tendsto (fun N : ℕ => ∏ i ∈ Finset.range k, (1 - (i : ℝ) / N)) atTop
      (𝓝 (∏ i ∈ Finset.range k, (1 - 0 : ℝ))) :=
    tendsto_finsetProd _ fun i _ => tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  simp only [sub_zero, Finset.prod_const_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop 1] with N hk h1
  have hN : (N : ℝ) ≠ 0 := by positivity
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, ← Finset.card_range k, ← Finset.prod_const,
    Finset.card_range, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Nat.cast_sub (by omega)]
  field_simp

theorem sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : Real.sqrt x ^ k = Real.sqrt (x ^ k) := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg x) k), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hx]

/-- The normalization `N^{k/2} / √((N)_k) → 1`. -/
theorem tendsto_kappa (k : ℕ) :
    Tendsto (fun N : ℕ => Real.sqrt N ^ k / Real.sqrt (N.descFactorial k)) atTop (𝓝 1) := by
  have h := ((Real.continuous_sqrt.tendsto 1).comp (tendsto_descFactorial_div_pow k)).inv₀
    (by simp)
  simp only [Real.sqrt_one, inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N h1
  have hN : (0 : ℝ) < N := by exact_mod_cast h1
  simp only [Function.comp]
  rw [Real.sqrt_div (Nat.cast_nonneg _), sqrt_pow_eq _ hN.le, inv_div]

/-- If the empirical second moments converge, the normalized `p`-th power sums (`p ≥ 3`)
tend to `0`. -/
theorem tendsto_sum_pow_of_mean_sq {v : ℕ → ℝ} (hv : ∀ i, 0 ≤ v i) {c : ℝ}
    (hc : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, v i ^ 2) / N) atTop (𝓝 c)) {p : ℕ}
    (hp : 3 ≤ p) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, ((Real.sqrt N)⁻¹ * v i) ^ p) atTop (𝓝 0) := by
  set S : ℕ → ℝ := fun N => ∑ i ∈ Finset.range N, v i ^ 2
  -- step A: `v_N² / (N+1) → 0`
  have hA : Tendsto (fun N : ℕ => v N ^ 2 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => S (N + 1) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 c) :=
      hc.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 1) :=
      tendsto_natCast_div_add_atTop 1
    have h3 := h1.sub (hc.mul h2)
    rw [mul_one, sub_self] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    simp only [S, Finset.sum_range_succ]
    push_cast
    field_simp
    ring
  -- step B: uniform smallness of the summands
  have hB : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ i < N, v i ^ 2 ≤ ε * N := by
    intro ε hε
    obtain ⟨i₀, hi₀⟩ := (Metric.tendsto_atTop.mp hA) (ε / 2) (by positivity)
    set C := ∑ i ∈ Finset.range i₀, v i ^ 2
    filter_upwards [eventually_ge_atTop i₀, eventually_ge_atTop ⌈C / ε⌉₊] with N hN1 hN2 i hi
    by_cases hii : i₀ ≤ i
    · have := hi₀ i hii
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ (by positivity)] at this
      have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
      nlinarith
    · have h1 : v i ^ 2 ≤ C :=
        Finset.single_le_sum (f := fun i => v i ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_range.mpr (by omega))
      have h2 : C / ε ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN2)
      rw [div_le_iff₀ hε] at h2
      linarith
  -- step C and D
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set M := |c| + 1
  have hM : 0 < M := by positivity
  set ε := min 1 ((δ / (2 * M)) ^ 2)
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hsε : Real.sqrt ε ≤ δ / (2 * M) := by
    rw [Real.sqrt_le_left (by positivity)]; exact min_le_right _ _
  have hcM : ∀ᶠ N : ℕ in atTop, S N / N ≤ M := by
    filter_upwards [(Metric.tendsto_atTop.mp hc) 1 one_pos |> fun ⟨N0, h⟩ =>
      eventually_atTop.mpr ⟨N0, h⟩] with N hN
    rw [Real.dist_eq] at hN
    have := le_abs_self c
    linarith [abs_lt.mp hN]
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp ((hB ε hε).and (hcM.and (eventually_ge_atTop 1)))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hsmall, hSM, hN1⟩ := hN0 N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set s := (Real.sqrt N)⁻¹
  have hs : 0 ≤ s := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs2 : s ^ 2 = (N : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt hNpos.le]
  have hterm : ∀ i ∈ Finset.range N, (s * v i) ^ p ≤ Real.sqrt ε * (s * v i) ^ 2 := by
    intro i hi
    have hsv : 0 ≤ s * v i := mul_nonneg hs (hv i)
    have hsq : (s * v i) ^ 2 ≤ ε := by
      rw [mul_pow, hs2, inv_mul_le_iff₀ hNpos, mul_comm]
      exact hsmall i (Finset.mem_range.mp hi)
    have hle : s * v i ≤ Real.sqrt ε := Real.le_sqrt_of_sq_le hsq
    have hle1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
    have h1 : (s * v i) ^ q ≤ 1 := pow_le_one₀ hsv (hle.trans hle1)
    calc (s * v i) ^ (q + 3) = (s * v i) ^ q * (s * v i) * (s * v i) ^ 2 := by ring
      _ ≤ 1 * Real.sqrt ε * (s * v i) ^ 2 := by gcongr
      _ = Real.sqrt ε * (s * v i) ^ 2 := by ring
  have hsum2 : ∑ i ∈ Finset.range N, (s * v i) ^ 2 = S N / N := by
    simp only [mul_pow, hs2, S, ← Finset.mul_sum]
    rw [inv_mul_eq_div]
  have hnn : 0 ≤ ∑ i ∈ Finset.range N, (s * v i) ^ p :=
    Finset.sum_nonneg fun i _ => pow_nonneg (mul_nonneg hs (hv i)) _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  calc ∑ i ∈ Finset.range N, (s * v i) ^ p ≤ ∑ i ∈ Finset.range N, Real.sqrt ε * (s * v i) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = Real.sqrt ε * (S N / N) := by rw [← Finset.mul_sum, hsum2]
    _ ≤ δ / (2 * M) * M := by
        gcongr
    _ < δ := by field_simp; linarith

end SharpLSI
