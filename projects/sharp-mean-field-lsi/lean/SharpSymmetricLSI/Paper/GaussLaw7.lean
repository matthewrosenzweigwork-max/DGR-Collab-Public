import SharpSymmetricLSI.Paper.GaussLaw6

/-!
# R27: the exponential moments of `γ_∞` (Lemma 6.1, infinite-dimensional step)

Under `I + T_n ≥ σ` for every finite section: with `q = 1 + σ/2`, `1 + q t_k ≥ σ(1+σ)/2`, so the
truncated densities `exp(t⟨v,z⟩ - Q_n/2)` are bounded in `L^q(γ)` uniformly in `n`; with
`Q_n → Q` in `L²(γ)` (hence a.e. along subsequences) Vitali gives
`∫ exp(t⟨v,z⟩ - Q/2) dγ = lim_n gaussProd_n(1, t u_n) = (∫ e^{-Q/2} dγ) exp(t²⟨v,Cv⟩/2)`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace

namespace SharpLSI

theorem sum_fin_sq_le_tsum {T : ℕ → ℕ → ℝ} (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2)
    (n : ℕ) : ∑ i : Fin n, ∑ j : Fin n, T i j ^ 2 ≤ ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2 := by
  have h : ∑ i : Fin n, ∑ j : Fin n, T i j ^ 2 =
      ∑ p ∈ Finset.range n ×ˢ Finset.range n, T p.1 p.2 ^ 2 := by
    rw [Finset.sum_product, ← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, T i j ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun j => T i j ^ 2) n
  rw [h]
  exact hS.sum_le_tsum _ fun _ _ => sq_nonneg _

section lim
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos T Q)

include hQ in
theorem tendstoInMeasure_quadTrunc :
    TendstoInMeasure gammaRef (fun n => quadTrunc T n) atTop Q :=
  tendstoInMeasure_of_tendsto_eLpNorm (p := 2) two_ne_zero hQ.2

include hσ0 hσ in
theorem secEig_ge_delta (n : ℕ) (k : Fin n) :
    σ * (1 + σ) / 2 ≤ 1 + (1 + σ / 2) * secEig hT n k := by
  have h := secEig_ge hT (hσ n) k
  have : (1 + σ / 2) * (σ - 1) ≤ (1 + σ / 2) * secEig hT n k :=
    mul_le_mul_of_nonneg_left h (by positivity)
  nlinarith

include hT hS hσ0 hσ hQ in
/-- **Vitali for the truncated Gaussian densities.** -/
theorem gauss_limit (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) :
    Integrable (fun z => rexp (t * ∑ i ∈ s, v i * z i - Q z / 2)) gammaRef ∧
    Tendsto (fun n => ∫ z, rexp (t * ∑ i ∈ s, v i * z i - quadTrunc T n z / 2) ∂gammaRef)
      atTop (𝓝 (∫ z, rexp (t * ∑ i ∈ s, v i * z i - Q z / 2) ∂gammaRef)) := by
  set N0 := s.sup id + 1
  have hs : ∀ n, ∀ i ∈ s, i < n + N0 := fun n i hi => by
    have := Finset.le_sup (f := id) hi; simp only [id] at this; omega
  set q := 1 + σ / 2
  set δ := σ * (1 + σ) / 2
  have hq : 1 < q := by simp only [q]; linarith
  have hδ : 0 < δ := by positivity
  set S := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2
  set V := ∑ i ∈ s, v i ^ 2
  set L : (ℕ → ℝ) → ℝ := fun z => ∑ i ∈ s, v i * z i
  set F : ℕ → (ℕ → ℝ) → ℝ := fun n z => rexp (t * L z - quadTrunc T (n + N0) z / 2)
  set G : (ℕ → ℝ) → ℝ := fun z => rexp (t * L z - Q z / 2)
  have hpos1 : ∀ n k, 0 < 1 + 1 * secEig hT n k := fun n k => by
    rw [one_mul]; exact secEig_pos hT hσ0 hσ n k
  have hposq : ∀ n k, 0 < 1 + q * secEig hT n k := fun n k =>
    hδ.trans_le (secEig_ge_delta hT hσ0 hσ n k)
  have hFi : ∀ n, Integrable (F n) gammaRef := fun n => by
    have := integrable_gammaRef_exp_quad hT s (hs n) v t 1 (hpos1 _)
    simpa only [one_mul] using this
  have hFq : ∀ n, (fun z => F n z ^ q) =
      fun z => rexp ((q * t) * L z - q * quadTrunc T (n + N0) z / 2) := fun n => by
    funext z; simp only [F, ← Real.exp_mul]; congr 1; ring
  have hFqi : ∀ n, Integrable (fun z => F n z ^ q) gammaRef := fun n => by
    rw [hFq]; exact integrable_gammaRef_exp_quad hT s (hs n) v (q * t) q (hposq _)
  set B := rexp ((q ^ 2 * S + (q * t) ^ 2 * V) / (2 * δ))
  have hFB : ∀ n, ∫ z, F n z ^ q ∂gammaRef ≤ B := fun n => by
    rw [hFq, integral_gammaRef_exp_quad hT s (hs n) v (q * t) q (hposq _)]
    refine (gaussProd_le hT hδ _ (fun k => secEig_ge_delta hT hσ0 hσ _ k)).trans ?_
    refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_finVec_sq s (hs n)]
    have h2 := mul_le_mul_of_nonneg_left (sum_fin_sq_le_tsum hS (n + N0)) (sq_nonneg q)
    have h3 : (1 + σ / 2) ^ 2 = q ^ 2 := rfl
    rw [h3]
    linarith
  have hm := tendstoInMeasure_quadTrunc hQ
  have key : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      Integrable G gammaRef ∧
      Tendsto (fun k => ∫ z, F (ns (ms k)) z ∂gammaRef) atTop (𝓝 (∫ z, G z ∂gammaRef)) := by
    intro ns hns
    have hm' := hm.comp ((tendsto_add_atTop_nat N0).comp hns)
    obtain ⟨ms, -, hms⟩ := hm'.exists_seq_tendsto_ae
    refine ⟨ms, tendsto_integral_of_ae_of_rpow_le (f := fun k => F (ns (ms k)))
      (fun _ _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) (fun k => hFi _) hq
      (fun k => hFqi _) (fun k => hFB _) ?_⟩
    filter_upwards [hms] with z hz
    exact (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds.sub (hz.div_const 2)))
  obtain ⟨_, hGi, -⟩ := key id tendsto_id
  refine ⟨hGi, ?_⟩
  refine (tendsto_add_atTop_iff_nat N0).1 (tendsto_of_subseq_tendsto fun ns hns => ?_)
  obtain ⟨ms, -, h⟩ := key ns hns
  exact ⟨ms, h⟩

variable {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C)

include hT hS hσ0 hσ hQ in
theorem one_le_integral_exp_Q : 1 ≤ ∫ z, rexp (-(Q z / 2)) ∂gammaRef := by
  have h := (gauss_limit hT hS hσ0 hσ hQ ∅ (fun _ => 0) 0).2
  simp only [Finset.sum_empty, mul_zero, zero_sub] at h
  refine ge_of_tendsto h (Eventually.of_forall fun n => ?_)
  have h1 := integral_gammaRef_exp_quad hT (∅ : Finset ℕ) (by simp) (fun _ => 0) 0 1
    (fun k => by rw [one_mul]; exact secEig_pos hT hσ0 hσ n k)
  simp only [Finset.sum_empty, mul_zero, zero_sub, one_mul, zero_smul] at h1
  rw [h1]
  exact one_le_gaussProd_zero hT (secEig_pos hT hσ0 hσ n)

include hT hS hσ0 hσ hQ hC in
/-- **The exponential moments of the tilted Gaussian.** -/
theorem integral_exp_lin_sub_Q (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) :
    ∫ z, rexp (t * ∑ i ∈ s, v i * z i - Q z / 2) ∂gammaRef =
      (∫ z, rexp (-(Q z / 2)) ∂gammaRef) *
        rexp (t ^ 2 * (∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j) / 2) := by
  have ht := (gauss_limit hT hS hσ0 hσ hQ s v t).2
  have h0 := (gauss_limit hT hS hσ0 hσ hQ s v 0).2
  simp only [zero_mul, zero_sub] at h0
  have hr := tendsto_inner_secRes hT hS hσ0 hσ hC s v
  have hlim := h0.mul ((Real.continuous_exp.tendsto _).comp ((hr.const_mul (t ^ 2)).div_const 2))
  refine tendsto_nhds_unique ht (hlim.congr' ?_)
  filter_upwards [eventually_lt_of_finset s] with n hn
  have hpos : ∀ k, 0 < 1 + 1 * secEig hT n k := fun k => by
    rw [one_mul]; exact secEig_pos hT hσ0 hσ n k
  have e1 := integral_gammaRef_exp_quad hT s hn v t 1 hpos
  have e0 := integral_gammaRef_exp_quad hT s hn v 0 1 hpos
  simp only [one_mul, zero_mul, zero_sub, zero_smul] at e1 e0
  have hsum : (∑ k, (1 + secEig hT n k)⁻¹ * ⟪secVec hT n k, t • finVec s v n⟫_ℝ ^ 2 / 2) =
      t ^ 2 * (∑ k, (1 + secEig hT n k)⁻¹ * ⟪secVec hT n k, finVec s v n⟫_ℝ ^ 2) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_smul_right]; ring
  simp only [Function.comp]
  rw [e1, e0, gaussProd_one hT (t • finVec s v n) (secEig_pos hT hσ0 hσ n), inner_secRes, hsum]

end lim

end SharpLSI
