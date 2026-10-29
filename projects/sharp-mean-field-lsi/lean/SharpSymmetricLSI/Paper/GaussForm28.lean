import SharpSymmetricLSI.Paper.GaussForm27

/-!
# R32 (G3): the coordinates are `L²(γ)` limits of the `ξ_j`

With `c_{ij} = (C v_j)_i`: `E[ξ_iξ_j] = δ_{ij}`, `E[z_i z_q] = C_{iq}`, `E[z_i ξ_j] = c_{ij}`, and
`E[(z_i - ∑_{j<N} c_{ij}ξ_j)²] = C_{ii} - ∑_{j<N} c_{ij}² → 0` (`tendsto_coord_approx`), using the
expansion `C_{ii} = ∑_j c_{ij}²` of `exists_genEigen_matrix`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped InnerProductSpace ENNReal NNReal

namespace SharpLSI

/-- The second moment of a centered Gaussian variable. -/
theorem integral_sq_of_map_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : AEMeasurable Y P) {v : ℝ≥0} (h : P.map Y = gaussianReal 0 v) :
    ∫ ω, Y ω ^ 2 ∂P = v := by
  rw [show (∫ ω, Y ω ^ 2 ∂P) = ∫ ω, (fun x : ℝ => x ^ 2) (Y ω) ∂P from rfl,
    ← integral_map hY (continuous_pow 2).aestronglyMeasurable, h]
  have h2 := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero measurable_id.aemeasurable
    (by simp [integral_id_gaussianReal])] at h2
  simpa using h2

section moments
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)
  {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
include hT hS hσ0 hσ hC hCs hγ

/-- `E[z_i z_q] = C_{iq}`. -/
theorem integral_coord_mul (i q : ℕ) : ∫ z, z i * z q ∂γ = C i q := by
  have hnn := quadC_nonneg hT hS hσ0 hσ hC
  by_cases hiq : i = q
  · subst hiq
    have h := integral_linSum_sq_gamma hγ {i} (fun _ => 1) (hnn _ _)
    simp only [Finset.sum_singleton, one_mul, mul_one] at h
    rw [← h]; exact integral_congr_ae (Eventually.of_forall fun z => by simp [sq])
  · have hp := integral_linSum_sq_gamma hγ {i, q} (Pi.single i 1 + Pi.single q 1) (hnn _ _)
    have hm := integral_linSum_sq_gamma hγ {i, q} (Pi.single i 1 - Pi.single q 1) (hnn _ _)
    have hq : q ≠ i := Ne.symm hiq
    simp only [Finset.sum_pair hiq, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hiq, Pi.single_eq_of_ne hq] at hp hm
    have hi2 := (memLp_coord_gamma hγ i)
    have hq2 := (memLp_coord_gamma hγ q)
    have hint : ∀ a b : ℝ, Integrable (fun z : ℕ → ℝ => (a * z i + b * z q) ^ 2) γ :=
      fun a b => ((hi2.const_mul a).add (hq2.const_mul b)).integrable_sq
    have e : ∀ z : ℕ → ℝ, z i * z q =
        ((1 * z i + 1 * z q) ^ 2 - ((1 - 0) * z i + (0 - 1) * z q) ^ 2) / 4 := fun z => by ring
    simp only [add_zero, zero_add, sub_zero, zero_sub] at hp hm
    rw [integral_congr_ae (Eventually.of_forall e), integral_div,
      integral_sub (by simpa using hint 1 1) (by simpa using hint 1 (-1))]
    have e1 : ∫ z, (1 * z i + 1 * z q) ^ 2 ∂γ = C i i + C i q + (C q i + C q q) := by
      simpa using hp
    have e2 : ∫ z, ((1 - 0) * z i + (0 - 1) * z q) ^ 2 ∂γ = C i i + -C i q + (-C q i + C q q) := by
      have : ∀ z : ℕ → ℝ, ((1 - 0) * z i + (0 - 1) * z q) ^ 2 = (1 * z i + -1 * z q) ^ 2 :=
        fun z => by ring
      simp_rw [this]
      simpa [neg_mul, sub_eq_add_neg] using hm
    rw [e1, e2, hCs q i]; ring

variable {v : ℕ → ℕ → ℝ} (hv2 : ∀ j, Summable fun i => v j i ^ 2)
  (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
  {ξ : ℕ → (ℕ → ℝ) → ℝ} (hξ : ∀ j, IsRowVariable v γ j (ξ j))
include hv2 hvC hξ

theorem integral_comb_xi_sq {J : ℕ} (t : Fin J → ℝ) :
    ∫ z, (∑ k : Fin J, t k * ξ k z) ^ 2 ∂γ = ∑ k : Fin J, t k ^ 2 := by
  have hY : AEMeasurable (fun z => ∑ k : Fin J, t k * ξ k z) γ :=
    Finset.aemeasurable_fun_sum _ fun k _ =>
      ((hξ k).1.aestronglyMeasurable.aemeasurable).const_mul _
  rw [integral_sq_of_map_gaussianReal hY (map_lin_xi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ t),
    Real.coe_toNNReal _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- `E[ξ_i ξ_j] = δ_{ij}`. -/
theorem integral_xi_mul (i j : ℕ) : ∫ z, ξ i z * ξ j z ∂γ = if i = j then 1 else 0 := by
  set J := max i j + 1
  have hi : i < J := by omega
  have hj : j < J := by omega
  set i' : Fin J := ⟨i, hi⟩
  set j' : Fin J := ⟨j, hj⟩
  have hsum : ∀ (a b : ℝ) (z : ℕ → ℝ), i ≠ j →
      ∑ k : Fin J, (Pi.single i' a + Pi.single j' b : Fin J → ℝ) k * ξ k z =
        a * ξ i z + b * ξ j z := fun a b z hij => by
    have hne : i' ≠ j' := fun h => hij (congrArg Fin.val h)
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, Pi.single_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  by_cases hij : i = j
  · subst hij
    have h := integral_comb_xi_sq hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ (Pi.single i' (1 : ℝ))
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ite_pow, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at h
    rw [if_pos rfl, ← h]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp [sq, i'])
  · rw [if_neg hij]
    have hp := integral_comb_xi_sq hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ
      (Pi.single i' (1 : ℝ) + Pi.single j' 1)
    have hm := integral_comb_xi_sq hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ
      (Pi.single i' (1 : ℝ) + Pi.single j' (-1))
    simp_rw [hsum _ _ _ hij] at hp hm
    have hne : i' ≠ j' := fun h => hij (congrArg Fin.val h)
    have hs2 : ∀ b : ℝ, ∑ k : Fin J, (Pi.single i' (1 : ℝ) + Pi.single j' b : Fin J → ℝ) k ^ 2 =
        1 + b ^ 2 := fun b => by
      have hk : ∀ k : Fin J, (Pi.single i' (1 : ℝ) + Pi.single j' b : Fin J → ℝ) k ^ 2 =
          (Pi.single i' (1 : ℝ) : Fin J → ℝ) k ^ 2 + (Pi.single j' b : Fin J → ℝ) k ^ 2 := by
        intro k
        by_cases h1 : k = i'
        · subst h1; simp [Pi.single_apply, hne]
        · simp [Pi.single_apply, h1]
      simp_rw [hk, Finset.sum_add_distrib]
      simp [Pi.single_apply, ite_pow]
    rw [hs2] at hp hm
    have h1 := (hξ i).1
    have h2 := (hξ j).1
    have e : ∀ z, ξ i z * ξ j z =
        ((1 * ξ i z + 1 * ξ j z) ^ 2 - (1 * ξ i z + -1 * ξ j z) ^ 2) / 4 := fun z => by ring
    rw [integral_congr_ae (Eventually.of_forall e), integral_div, integral_sub, hp, hm]
    · norm_num
    · simpa using (h1.add h2).integrable_sq
    · simpa [neg_mul, ← sub_eq_add_neg] using (h1.sub h2).integrable_sq

/-- `E[z_i ξ_j] = (C v_j)_i`. -/
theorem integral_coord_mul_xi (i j : ℕ) :
    ∫ z, z i * ξ j z ∂γ = ∑' b, C i b * v j b := by
  have := hγ.1
  set S : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ q ∈ Finset.range n, v j q * z q
  have hzi := memLp_coord_gamma hγ i
  have hS2 : ∀ n, MemLp (S n) 2 γ := fun n => memLp_linSum_gamma hγ _ _
  have hint : ∀ n, ∫ z, z i * S n z ∂γ = ∑ q ∈ Finset.range n, C i q * v j q := fun n => by
    simp only [S, Finset.mul_sum]
    rw [integral_finset_sum _ fun q _ => by
      simpa [mul_left_comm] using (hzi.integrable_mul (memLp_coord_gamma hγ q)).const_mul (v j q)]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show (fun z : ℕ → ℝ => z i * (v j q * z q)) = fun z => v j q * (z i * z q) by
      funext z; ring, integral_const_mul, integral_coord_mul hT hS hσ0 hσ hC hCs hγ]
    ring
  have hcol : Summable fun b => C i b ^ 2 := by
    simpa [hCs i] using (hC i).1
  have hsumm := (tsum_mul_sq_le hcol (hv2 j)).1
  have h1 : Tendsto (fun n => ∫ z, z i * S n z ∂γ) atTop (𝓝 (∑' b, C i b * v j b)) := by
    simp_rw [hint]; exact hsumm.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun n => ∫ z, z i * S n z ∂γ) atTop (𝓝 (∫ z, z i * ξ j z ∂γ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hle : ∀ n, ‖∫ z, z i * S n z ∂γ - ∫ z, z i * ξ j z ∂γ‖ ≤
        (eLpNorm (fun z => z i) 2 γ).toReal *
          (eLpNorm (fun z => S n z - ξ j z) 2 γ).toReal := fun n => by
      rw [← integral_sub (f := fun z => z i * S n z) (g := fun z => z i * ξ j z)
        (by exact hzi.integrable_mul (hS2 n)) (by exact hzi.integrable_mul (hξ j).1),
        Real.norm_eq_abs]
      have := abs_integral_mul_le_L2 hzi ((hS2 n).sub (hξ j).1)
      have e : ∫ z, z i * S n z - z i * ξ j z ∂γ = ∫ z, z i * (S n - ξ j) z ∂γ :=
        integral_congr_ae (Eventually.of_forall fun z => by simp [mul_sub])
      rw [e]; exact this
    have h0 : Tendsto (fun n => (eLpNorm (fun z => z i) 2 γ).toReal *
        (eLpNorm (fun z => S n z - ξ j z) 2 γ).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hξ j).2).const_mul
        (eLpNorm (fun z => z i) 2 γ).toReal
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) hle h0
  exact tendsto_nhds_unique h2 h1

/-- `E[(∑_{j<N} c_{ij}ξ_j - z_i)²] = C_{ii} - ∑_{j<N} c_{ij}²`. -/
theorem integral_coord_approx_sq (i N : ℕ) :
    ∫ z, (∑ j ∈ Finset.range N, (∑' b, C i b * v j b) * ξ j z - z i) ^ 2 ∂γ =
      C i i - ∑ j ∈ Finset.range N, (∑' b, C i b * v j b) ^ 2 := by
  set c : ℕ → ℝ := fun j => ∑' b, C i b * v j b with hc
  have hzi := memLp_coord_gamma hγ i
  have hpt : ∀ z : ℕ → ℝ, (∑ j ∈ Finset.range N, c j * ξ j z - z i) ^ 2 =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, (c j * c k) * (ξ j z * ξ k z) -
        ∑ j ∈ Finset.range N, (2 * c j) * (z i * ξ j z) + z i * z i := fun z => by
    rw [sub_sq, sq, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul, sq]
    congr 1
    congr 1
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have iξξ : ∀ j k, Integrable (fun z => ξ j z * ξ k z) γ := fun j k =>
    (hξ j).1.integrable_mul (hξ k).1
  have izξ : ∀ j, Integrable (fun z => z i * ξ j z) γ := fun j => hzi.integrable_mul (hξ j).1
  have h1 : Integrable (fun z => ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      (c j * c k) * (ξ j z * ξ k z)) γ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (iξξ j k).const_mul _
  have h2 : Integrable (fun z => ∑ j ∈ Finset.range N, (2 * c j) * (z i * ξ j z)) γ :=
    integrable_finsetSum _ fun j _ => (izξ j).const_mul _
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_add (f := fun z => ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      (c j * c k) * (ξ j z * ξ k z) - ∑ j ∈ Finset.range N, (2 * c j) * (z i * ξ j z))
      (g := fun z => z i * z i) (by exact h1.sub h2) (by exact hzi.integrable_mul hzi),
    integral_sub (f := fun z => ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      (c j * c k) * (ξ j z * ξ k z))
      (g := fun z => ∑ j ∈ Finset.range N, (2 * c j) * (z i * ξ j z)) h1 h2,
    integral_finset_sum _ fun j _ => integrable_finsetSum _ fun k _ => (iξξ j k).const_mul _,
    integral_finset_sum _ fun j _ => (izξ j).const_mul _,
    integral_coord_mul hT hS hσ0 hσ hC hCs hγ]
  simp_rw [integral_finset_sum _ fun k _ => (iξξ _ k).const_mul _, integral_const_mul,
    integral_xi_mul hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ,
    integral_coord_mul_xi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  rw [Finset.sum_congr rfl fun j hj => if_pos (Finset.mem_range.1 hj)]
  simp only [hc, ← Finset.sum_mul, sq]
  rw [Finset.sum_congr rfl fun j _ => (show (2 * c j) * c j = 2 * (c j * c j) by ring),
    ← Finset.mul_sum]
  ring

variable (hP : ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i))
include hP

/-- **`z_i = ∑_j (C v_j)_i ξ_j` in `L²(γ)`.** -/
theorem tendsto_coord_approx (i : ℕ) :
    Tendsto (fun N => eLpNorm (fun z => ∑ j ∈ Finset.range N,
      (∑' b, C i b * v j b) * ξ j z - z i) 2 γ) atTop (𝓝 0) := by
  have hm : ∀ N, MemLp (fun z => ∑ j ∈ Finset.range N,
      (∑' b, C i b * v j b) * ξ j z - z i) 2 γ := fun N =>
    (memLp_finsetSum (ε' := ℝ) _ fun j _ => (hξ j).1.const_mul _).sub (memLp_coord_gamma hγ i)
  simp_rw [fun N => eLpNorm_two_eq_sqrt_gamma (hm N),
    integral_coord_approx_sq hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ]
  have h := (hP i).tendsto_sum_nat
  have h2 : Tendsto (fun N => C i i - ∑ j ∈ Finset.range N, (∑' b, C i b * v j b) ^ 2) atTop
      (𝓝 0) := by simpa using (tendsto_const_nhds (x := C i i)).sub h
  have h3 := (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp h2)
  have h4 : ENNReal.ofReal √0 = 0 := by simp
  rw [h4] at h3
  exact h3

end moments

end SharpLSI
