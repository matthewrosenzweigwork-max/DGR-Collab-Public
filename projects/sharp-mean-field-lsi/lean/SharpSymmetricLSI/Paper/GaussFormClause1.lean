import SharpSymmetricLSI.Paper.GaussForm28
import SharpSymmetricLSI.Paper.GaussForm30

/-!
# R32 form clause (lane s42), step 1: the generator relation `L ξ_j = -ν_j ξ_j`

For the diagonalizing vectors `v_j` (`⟨v_i, C v_j⟩ = δ_{ij}`, `⟨v_i, Λ v_j⟩ = ν_i δ_{ij}`,
Parseval `∑_j (C v_j)_i² = C_{ii}`), the row variables `ξ_j = ⟨v_j, z⟩` and `Y_i = (Tz)_i`:
`∑_{i<N} λ'_i v_{ji} (z_i + Y_i) → ν_j ξ_j` in `L²(γ)` (`tendsto_gen_xi`; i.e.
`⟨(I+T)Λ v_j, z⟩ = ν_j ξ_j`).

Proof in `L²(γ)`: the partial sums `S_N` are Cauchy (`‖∑_{i∈s} a_i(z_i+Y_i)‖ ≤ K |a_s|`, from
`⟨w,Cw⟩ ≤ |w|²/σ`), with limit `X`. `D = X - ν_j ξ_j` is orthogonal to every `ξ_k`
(`⟨z_i + Y_i, ξ_k⟩ = ((I+T)C v_k)_i = v_{ki}` and `hvΛ`), hence to every `z_i`
(`z_i = ∑_k (Cv_k)_i ξ_k`, GaussForm28 `tendsto_coord_approx`, which uses Parseval), hence to
every `Y_i` and every `S_N`; so `‖D‖² = ⟨D, X - ν_j ξ_j⟩ = 0`.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped InnerProductSpace ENNReal

namespace SharpLSI

theorem coeFn_sum_ae {α : Type*} [MeasurableSpace α] {P : Measure α} {ι : Type*}
    (s : Finset ι) (f : ι → Lp ℝ 2 P) :
    (⇑(∑ i ∈ s, f i) : α → ℝ) =ᵐ[P] fun x => ∑ i ∈ s, (f i : α → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero _ _ _
  | insert b t hb ih =>
    simp only [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (f b) (∑ i ∈ t, f i), ih] with z h1 h2
    rw [h1, Pi.add_apply, h2]

/-- `toLp (∑ wᵢ fᵢ) = ∑ wᵢ • toLp fᵢ`. -/
theorem toLp_linComb {α : Type*} [MeasurableSpace α] {P : Measure α} {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) {f : ι → α → ℝ} (hf : ∀ i, MemLp (f i) 2 P)
    (h : MemLp (fun x => ∑ i ∈ s, w i * f i x) 2 P) :
    h.toLp _ = ∑ i ∈ s, w i • (hf i).toLp (f i) := by
  refine Lp.ext ?_
  have h1 : ∀ i, ∀ᵐ x ∂P, ((w i • (hf i).toLp (f i) : Lp ℝ 2 P) : α → ℝ) x = w i * f i x :=
    fun i => by
      filter_upwards [Lp.coeFn_smul (w i) ((hf i).toLp (f i)), (hf i).coeFn_toLp] with x h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have hall : ∀ᵐ x ∂P, ∀ i ∈ s, ((w i • (hf i).toLp (f i) : Lp ℝ 2 P) : α → ℝ) x = w i * f i x :=
    (Filter.eventually_all_finset s).2 fun i _ => h1 i
  filter_upwards [h.coeFn_toLp, coeFn_sum_ae s (fun i => w i • (hf i).toLp (f i)), hall]
    with x h1 h2 h3
  rw [h1, h2]
  exact (Finset.sum_congr rfl fun i hi => h3 i hi).symm

theorem inner_toLp_two {α : Type*} [MeasurableSpace α] {P : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) : ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂P := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp only [RCLike.inner_apply, conj_trivial, h1, h2]
  ring

/-- Row variables as `L²(γ)` limits of finite combinations of the coordinates. -/
theorem tendsto_toLp_rowVar {γ : Measure (ℕ → ℝ)} (hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ)
    {u : ℕ → ℕ → ℝ} {i : ℕ} {U : (ℕ → ℝ) → ℝ} (hU : IsRowVariable u γ i U) :
    Tendsto (fun m => ∑ q ∈ Finset.range m, u i q • (hz q).toLp (fun z : ℕ → ℝ => z q)) atTop
      (𝓝 (hU.1.toLp U)) := by
  have hlin : ∀ m, MemLp (fun z : ℕ → ℝ => ∑ q ∈ Finset.range m, u i q * z q) 2 γ := fun m =>
    memLp_finsetSum (ε' := ℝ) _ fun q _ => (hz q).const_mul (u i q)
  have h2 : Tendsto (fun m => eLpNorm ((fun z : ℕ → ℝ => ∑ q ∈ Finset.range m, u i q * z q) - U)
      2 γ) atTop (𝓝 0) := by
    refine hU.2.congr fun m => ?_
    congr 1
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := γ) (p := 2) (E := ℝ) (ι := ℕ) (fi := atTop)
    (fun m (z : ℕ → ℝ) => ∑ q ∈ Finset.range m, u i q * z q)
    hlin U hU.1).2 h2
  exact h.congr fun m => toLp_linComb (f := fun q (z : ℕ → ℝ) => z q) (Finset.range m) (u i) hz
    (hlin m)

section gen
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)
  {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
  {v : ℕ → ℕ → ℝ} (hv2 : ∀ j, Summable fun i => v j i ^ 2)
  (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
  {ξ : ℕ → (ℕ → ℝ) → ℝ} (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hP : ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i))
  {lam' : ℕ → ℝ} {ν : ℕ → ℝ} (hvl : ∀ j, Summable fun i => (lam' i * v j i) ^ 2)
  (hvΛ : ∀ i j, ∑' a, lam' a * v i a * v j a = if i = j then ν i else 0)
  {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
include hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ hP hvl hvΛ hY

/-- **The generator relation** `∑_{i<N} λ'_i v_{ji}(z_i + Y_i) → ν_j ξ_j` in `L²(γ)`. -/
theorem tendsto_gen_xi (j : ℕ) :
    Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N, lam' i * v j i * (z i + Y i z) -
      ν j * ξ j z) 2 γ) atTop (𝓝 0) := by
  haveI := hγ.1
  -- the basic `L²` elements
  have hz : ∀ i, MemLp (fun z : ℕ → ℝ => z i) 2 γ := fun i => memLp_coord_gamma hγ i
  have hYm : ∀ i, MemLp (Y i) 2 γ := fun i => (hY i).1
  have hξm : ∀ k, MemLp (ξ k) 2 γ := fun k => (hξ k).1
  set Z : ℕ → Lp ℝ 2 γ := fun i => (hz i).toLp _ with hZ
  set YL : ℕ → Lp ℝ 2 γ := fun i => (hYm i).toLp _ with hYL
  set Ξ : ℕ → Lp ℝ 2 γ := fun k => (hξm k).toLp _ with hΞ
  set c : ℕ → ℕ → ℝ := fun i k => ∑' b, C i b * v k b with hc
  have iZZ : ∀ i q, ⟪Z i, Z q⟫_ℝ = C i q := fun i q => by
    rw [inner_toLp_two]; exact integral_coord_mul hT hS hσ0 hσ hC hCs hγ i q
  have iZΞ : ∀ i k, ⟪Z i, Ξ k⟫_ℝ = c i k := fun i k => by
    rw [inner_toLp_two]; exact integral_coord_mul_xi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ i k
  have iΞΞ : ∀ i k, ⟪Ξ i, Ξ k⟫_ℝ = if i = k then 1 else 0 := fun i k => by
    rw [inner_toLp_two]; exact integral_xi_mul hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ i k
  -- finite combinations of coordinates
  have hlin : ∀ (s : Finset ℕ) (w : ℕ → ℝ), MemLp (fun z : ℕ → ℝ => ∑ q ∈ s, w q * z q) 2 γ :=
    fun s w => memLp_linSum_gamma hγ s w
  have hnormZ : ∀ (s : Finset ℕ) (w : ℕ → ℝ),
      ‖∑ q ∈ s, w q • Z q‖ ^ 2 ≤ (∑ q ∈ s, w q ^ 2) / σ := fun s w => by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    have e : ∑ a ∈ s, ⟪w a • Z a, ∑ q ∈ s, w q • Z q⟫_ℝ =
        ∑ a ∈ s, ∑ b ∈ s, w a * C a b * w b := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right, iZZ]; ring
    rw [e]
    exact quadC_le hT hS hσ0 hσ hC s w
  -- limits of row variables
  have hYlim : ∀ i, Tendsto (fun m => ∑ q ∈ Finset.range m, T i q • Z q) atTop (𝓝 (YL i)) :=
    fun i => tendsto_toLp_rowVar hz (hY i)
  have hξc : ∀ (s : Finset ℕ) (w : ℕ → ℝ), MemLp (fun z => ∑ k ∈ s, w k * ξ k z) 2 γ :=
    fun s w => memLp_finsetSum (ε' := ℝ) _ fun k _ => (hξm k).const_mul (w k)
  have hZlim : ∀ i, Tendsto (fun N => ∑ k ∈ Finset.range N, c i k • Ξ k) atTop (𝓝 (Z i)) :=
    fun i => by
      have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := γ) (p := 2) (E := ℝ) (ι := ℕ)
        (fi := atTop) (fun N (z : ℕ → ℝ) => ∑ k ∈ Finset.range N, c i k * ξ k z)
        (fun N => hξc _ _) (fun z => z i) (hz i)).2
        (tendsto_coord_approx hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ hP i)
      exact h.congr fun N => toLp_linComb (f := ξ) (Finset.range N) (c i) hξm (hξc _ _)
  -- `c + T c = v`
  have hcT : ∀ i k, Summable (fun q => T i q * c q k) ∧ c i k + ∑' q, T i q * c q k = v k i :=
    fun i k => by
      set vk := mkL2N (v k) (hv2 k)
      set ck := (ipT hS hσ0 hσ).symm vk
      have hcc : ∀ q, c q k = ck q := fun q => by
        have := tsum_C_mul hT hS hσ0 hσ hC hCs vk q
        simp only [vk, mkL2N_apply] at this
        exact this
      have h1 : ipT hS hσ0 hσ ck = vk := (ipT hS hσ0 hσ).apply_symm_apply vk
      rw [ipT_apply (hT := hT)] at h1
      have h2 := congrArg (fun x : L2N => x i) h1
      simp only [lp.coeFn_add, Pi.add_apply, hsOp_apply, vk, mkL2N_apply] at h2
      simp only [hcc]
      exact ⟨summable_row_mul hS ck i, h2⟩
  have iYΞ : ∀ i k, ⟪YL i, Ξ k⟫_ℝ = ∑' q, T i q * c q k := fun i k => by
    have h1 : Tendsto (fun m => ⟪∑ q ∈ Finset.range m, T i q • Z q, Ξ k⟫_ℝ) atTop
        (𝓝 ⟪YL i, Ξ k⟫_ℝ) := (hYlim i).inner tendsto_const_nhds
    have h2 : (fun m => ⟪∑ q ∈ Finset.range m, T i q • Z q, Ξ k⟫_ℝ) =
        fun m => ∑ q ∈ Finset.range m, T i q * c q k := by
      funext m; rw [sum_inner]
      exact Finset.sum_congr rfl fun q _ => by rw [real_inner_smul_left, iZΞ]
    rw [h2] at h1
    exact tendsto_nhds_unique h1 (hcT i k).1.hasSum.tendsto_sum_nat
  -- the partial sums
  set a : ℕ → ℝ := fun i => lam' i * v j i with ha
  set S : ℕ → Lp ℝ 2 γ := fun N => ∑ i ∈ Finset.range N, a i • (Z i + YL i) with hSdef
  have iSΞ : ∀ N k, ⟪S N, Ξ k⟫_ℝ = ∑ i ∈ Finset.range N, a i * v k i := fun N k => by
    simp only [hSdef, sum_inner, real_inner_smul_left, inner_add_left, iZΞ, iYΞ]
    exact Finset.sum_congr rfl fun i _ => by rw [(hcT i k).2]
  -- the norm bound for combinations of the `Y_i`
  set HS := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2
  have hHS0 : 0 ≤ HS := tsum_nonneg fun _ => sq_nonneg _
  have hnormY : ∀ (s : Finset ℕ) (w : ℕ → ℝ),
      ‖∑ i ∈ s, w i • YL i‖ ≤ √(∑ i ∈ s, w i ^ 2) * √(HS / σ) := fun s w => by
    have hlim : Tendsto (fun m => ∑ q ∈ Finset.range m, (∑ i ∈ s, w i * T i q) • Z q) atTop
        (𝓝 (∑ i ∈ s, w i • YL i)) := by
      have h := tendsto_finsetSum s fun i _ => (hYlim i).const_smul (w i)
      refine h.congr fun m => ?_
      simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    refine le_of_tendsto hlim.norm (Eventually.of_forall fun m => ?_)
    have hb : ∑ q ∈ Finset.range m, (∑ i ∈ s, w i * T i q) ^ 2 ≤ (∑ i ∈ s, w i ^ 2) * HS := by
      calc ∑ q ∈ Finset.range m, (∑ i ∈ s, w i * T i q) ^ 2
          ≤ ∑ q ∈ Finset.range m, (∑ i ∈ s, w i ^ 2) * ∑ i ∈ s, T i q ^ 2 :=
            Finset.sum_le_sum fun q _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = (∑ i ∈ s, w i ^ 2) * ∑ p ∈ s ×ˢ Finset.range m, T p.1 p.2 ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_product, Finset.sum_comm]
        _ ≤ (∑ i ∈ s, w i ^ 2) * HS :=
            mul_le_mul_of_nonneg_left (hS.sum_le_tsum _ fun _ _ => sq_nonneg _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h1 := hnormZ (Finset.range m) (fun q => ∑ i ∈ s, w i * T i q)
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← mul_div_assoc]
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (h1.trans (div_le_div_of_nonneg_right hb hσ0.le))
  have hnormZ' : ∀ (s : Finset ℕ) (w : ℕ → ℝ), ‖∑ i ∈ s, w i • Z i‖ ≤ √(∑ i ∈ s, w i ^ 2) * √(1 / σ) :=
    fun s w => by
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_one_div,
        ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt (hnormZ s w)
  set K := √(1 / σ) + √(HS / σ)
  have hdist : ∀ M N, M ≤ N → ‖S N - S M‖ ≤ K * √(∑ i ∈ Finset.Ico M N, a i ^ 2) := fun M N hMN => by
    have e : S N - S M = ∑ i ∈ Finset.Ico M N, a i • Z i + ∑ i ∈ Finset.Ico M N, a i • YL i := by
      simp only [hSdef]
      rw [← Finset.sum_Ico_eq_sub _ hMN, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => smul_add _ _ _
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := hnormZ' (Finset.Ico M N) a
    have := hnormY (Finset.Ico M N) a
    nlinarith [Real.sqrt_nonneg (∑ i ∈ Finset.Ico M N, a i ^ 2)]
  -- Cauchy
  have ha2 : Summable fun i => a i ^ 2 := hvl j
  set A := ∑' i, a i ^ 2
  have hAt : Tendsto (fun M => K * √(A - ∑ i ∈ Finset.range M, a i ^ 2)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := A)).sub ha2.hasSum.tendsto_sum_nat).sqrt.const_mul K
    rwa [sub_self, Real.sqrt_zero, mul_zero] at h
  have hcauchy : CauchySeq S := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N0, hN0⟩ := (hAt.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
    refine ⟨N0, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (hdist N0 n hn) (lt_of_le_of_lt ?_ (hN0 N0 le_rfl))
    have hK : 0 ≤ K := by positivity
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hK
    rw [Finset.sum_Ico_eq_sub _ hn]
    linarith [ha2.sum_le_tsum (Finset.range n) fun _ _ => sq_nonneg _]
  obtain ⟨X, hX⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- `D = X - ν_j ξ_j` vanishes
  have hav : ∀ k, Summable fun i => a i * v k i := fun k => by
    refine Summable.of_norm_bounded ((ha2.add (hv2 k)).div_const 2) fun i => ?_
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|a i| - |v k i|), sq_abs (a i), sq_abs (v k i)]
  set D := X - ν j • Ξ j
  have iDΞ : ∀ k, ⟪D, Ξ k⟫_ℝ = 0 := fun k => by
    have h1 : Tendsto (fun N => ⟪S N, Ξ k⟫_ℝ) atTop (𝓝 ⟪X, Ξ k⟫_ℝ) := hX.inner tendsto_const_nhds
    simp only [iSΞ] at h1
    have h2 := tendsto_nhds_unique h1 (hav k).hasSum.tendsto_sum_nat
    have h3 : ∑' i, a i * v k i = if j = k then ν j else 0 := by
      rw [← hvΛ j k]
    simp only [D, inner_sub_left, real_inner_smul_left, iΞΞ, h2, h3]
    split_ifs <;> simp
  have hzero : ∀ (F : ℕ → Lp ℝ 2 γ) (G : Lp ℝ 2 γ), Tendsto F atTop (𝓝 G) →
      (∀ N, ⟪D, F N⟫_ℝ = 0) → ⟪D, G⟫_ℝ = 0 := fun F G hF h0 =>
    tendsto_nhds_unique (tendsto_const_nhds.inner hF) (by simp only [h0]; exact tendsto_const_nhds)
  have iDZ : ∀ i, ⟪D, Z i⟫_ℝ = 0 := fun i => hzero _ _ (hZlim i) fun N => by
    simp only [inner_sum, real_inner_smul_right, iDΞ, mul_zero, Finset.sum_const_zero]
  have iDY : ∀ i, ⟪D, YL i⟫_ℝ = 0 := fun i => hzero _ _ (hYlim i) fun N => by
    simp only [inner_sum, real_inner_smul_right, iDZ, mul_zero, Finset.sum_const_zero]
  have iDX : ⟪D, X⟫_ℝ = 0 := hzero _ _ hX fun N => by
    simp only [hSdef, inner_sum, real_inner_smul_right, inner_add_right, iDZ, iDY, add_zero,
      mul_zero, Finset.sum_const_zero]
  have hD0 : D = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℝ)]
    calc ⟪D, D⟫_ℝ = ⟪D, X⟫_ℝ - ν j * ⟪D, Ξ j⟫_ℝ := by
          simp only [D, inner_sub_right, real_inner_smul_right]
      _ = 0 := by rw [iDX, iDΞ, mul_zero, sub_zero]
  have hXe : X = ν j • Ξ j := sub_eq_zero.mp hD0
  -- back to functions
  have hf : ∀ i, MemLp (fun z : ℕ → ℝ => z i + Y i z) 2 γ := fun i => (hz i).add (hYm i)
  have hfun : ∀ N, MemLp (fun z => ∑ i ∈ Finset.range N, a i * (z i + Y i z)) 2 γ := fun N =>
    memLp_finsetSum (ε' := ℝ) _ fun i _ => (hf i).const_mul (a i)
  have hSe : ∀ N, (hfun N).toLp _ = S N := fun N => by
    rw [toLp_linComb (f := fun i (z : ℕ → ℝ) => z i + Y i z) (Finset.range N) a hf (hfun N)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
  have hlimF : MemLp (fun z => ν j * ξ j z) 2 γ := (hξm j).const_mul (ν j)
  have hlimE : hlimF.toLp _ = ν j • Ξ j := MemLp.toLp_const_smul (ν j) (hξm j)
  have hfin := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := γ) (p := 2) (E := ℝ) (ι := ℕ)
    (fi := atTop) (fun N (z : ℕ → ℝ) => ∑ i ∈ Finset.range N,
    a i * (z i + Y i z)) hfun (fun z => ν j * ξ j z) hlimF).1 (by
      rw [hlimE, ← hXe]; exact hX.congr fun N => (hSe N).symm)
  refine hfin.congr fun N => ?_
  congr 1

end gen

section prop21
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **`L ξ_j = -ν_j ξ_j`** for the paper's data, conditional on Proposition 2.1:
`∑_{i<N} λ'_i v_{ji} (z_i + Y_i) → ν_j ξ_j` in `L²(γ)`. -/
theorem gen_xi_of_prop21 (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) (h21 : Prop21Conclusion V W μ)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {v : ℕ → ℕ → ℝ} {ν : ℕ → ℝ} {ξ : ℕ → (ℕ → ℝ) → ℝ}
    (hv : ∀ j, Summable (fun i => v j i ^ 2) ∧ Summable (fun i => (lamShift lam i * v j i) ^ 2))
    (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
    (hvΛ : ∀ i j, ∑' a, lamShift lam a * v i a * v j a = if i = j then ν i else 0)
    (hξ : ∀ j, IsRowVariable v γ j (ξ j))
    (hCv : ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i))
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i)) (j : ℕ) :
    Tendsto (fun N => eLpNorm (fun z => ∑ i ∈ Finset.range N,
      lamShift lam i * v j i * (z i + Y i z) - ν j * ξ j z) 2 γ) atTop (𝓝 0) := by
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have hCs : ∀ a b, C a b = C b a := fun a b => C_symm_of_secOp hT hS hσ0 hσ hC a b
  exact tendsto_gen_xi hT hS hσ0 hσ hC hCs hγ (fun j => (hv j).1) hvC hξ hCv
    (fun j => (hv j).2) hvΛ hY j

end prop21

end SharpLSI
