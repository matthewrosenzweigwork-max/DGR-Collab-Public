import SharpSymmetricLSI.Paper.GaussFormClause3

/-!
# R32 form clause (lane s42), step 4: the upper bound `ℰ_∞(F(ξ)) ≤ ∫ ∑ ν_j (∂_jF(ξ))² dγ`

`F(ξ^{(n)}) → F(ξ)` in `L²(γ)` (`F` Lipschitz, `ξ^{(n)}_j → ξ_j`), a subsequence converges a.e.,
`ℰ_∞(G_n(z_{<n})) ≤ formG(G_n)` by the cutoff lemma (GaussForm10), `formG(G_n) → target`
(Paper/GaussFormClause3) and `ℰ_∞` is lower semicontinuous (Paper/GaussFormClause2).
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal ContDiff

namespace SharpLSI

theorem eLpNorm_finsetSum_le {α : Type*} [MeasurableSpace α] {P : Measure α} {ι : Type*}
    (s : Finset ι) (f : ι → α → ℝ) :
    eLpNorm (fun x => ∑ i ∈ s, f i x) 2 P ≤ ∑ i ∈ s, eLpNorm (f i) 2 P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    simp only [Finset.sum_insert hb]
    exact (eLpNorm_add_le (f := f b) (g := fun x => ∑ i ∈ t, f i x) one_le_two).trans
      (add_le_add le_rfl ih)

/-- `ℰ_∞(G(z_{<N})) ≤ formG(G)` for `G` smooth, bounded with bounded derivative. -/
theorem gaussForm_le_formG {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] (lam' : ℕ → ℝ) {N : ℕ}
    {G : (Fin N → ℝ) → ℝ} (hG : ContDiff ℝ ∞ G) {B : ℝ} (hGB : ∀ x, |G x| ≤ B)
    (hdB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) :
    gaussForm lam' γ (fun z => G (zBlock N z)) ≤ formG lam' γ N G :=
  (gaussForm_le_liminf _ (tendsto_cutCyl_L2 hG hGB)).trans_eq
    (tendsto_cutCyl_form hG hGB hdB lam').liminf_eq

variable {J : ℕ} {F : (Fin J → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
  {v : ℕ → ℕ → ℝ} {lam' : ℕ → ℝ} {ν : ℕ → ℝ}
  (hv2 : ∀ j, Summable fun i => v j i ^ 2) (hvl : ∀ j, Summable fun i => (lam' i * v j i) ^ 2)
  (hvΛ : ∀ i j, ∑' a, lam' a * v i a * v j a = if i = j then ν i else 0)
  {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ] {ξ : ℕ → (ℕ → ℝ) → ℝ}
  (hξ : ∀ j, IsRowVariable v γ j (ξ j))
include hF hFc

/-- `F(ξ^{(n)}) → F(ξ)` in `L²(γ)`, and a subsequence of `ξ^{(n)}` converges a.e. -/
theorem trunc_xi_conv (hξ : ∀ j, IsRowVariable v γ j (ξ j)) :
    Tendsto (fun n => eLpNorm (fun z => F (linA v J n (zBlock n z)) - F (fun j => ξ j z)) 2 γ)
      atTop (𝓝 0) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ z ∂γ, ∀ j : Fin J,
      Tendsto (fun k => ∑ i ∈ Finset.range (φ k), v j i * z i) atTop (𝓝 (ξ j z)) := by
  obtain ⟨B, -, hB2, -, hd⟩ := exists_bounds_of_cc hF hFc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB2 0)
  have hξm : ∀ j, AEStronglyMeasurable (ξ j) γ := fun j => (hξ j).1.aestronglyMeasurable
  have hdiff : ∀ (n : ℕ) (j : ℕ), AEStronglyMeasurable
      (fun z => ∑ i ∈ Finset.range n, v j i * z i - ξ j z) γ := fun n j =>
    (measurable_linSum (Finset.range n) (v j)).aestronglyMeasurable.sub (hξm j)
  have hξv : AEStronglyMeasurable (fun z => fun j : Fin J => ξ j z) γ :=
    (AEMeasurable.of_eval (f := fun z (j : Fin J) => ξ j z) fun j =>
      (hξm j).aemeasurable).aestronglyMeasurable
  set e : ℕ → (ℕ → ℝ) → ℝ := fun n z => ∑ j : Fin J, |∑ i ∈ Finset.range n, v j i * z i - ξ j z|
  have he : Tendsto (fun n => eLpNorm (e n) 2 γ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑ j : Fin J,
        eLpNorm (fun z => ∑ i ∈ Finset.range n, v j i * z i - ξ j z) 2 γ) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Finset.univ : Finset (Fin J)) fun j _ => (hξ j).2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le)
      fun n => (eLpNorm_finsetSum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine le_of_eq ?_
    rw [← eLpNorm_norm _ (hdiff n j)]
    congr 1
  have hlip : ∀ a b : Fin J → ℝ, |F a - F b| ≤ B * ∑ j, |a j - b j| := fun a b => by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (fun x _ => (hd x)) (fun x _ => hB2 x) convex_univ (Set.mem_univ b) (Set.mem_univ a)
    rw [Real.norm_eq_abs] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun j => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |a j - b j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  refine ⟨?_, ?_⟩
  · have hb : ∀ n, eLpNorm (fun z => F (linA v J n (zBlock n z)) - F (fun j => ξ j z)) 2 γ ≤
        ‖B‖ₑ * eLpNorm (e n) 2 γ := fun n => by
      rw [← eLpNorm_const_smul]
      have hm : AEStronglyMeasurable (fun z => F (linA v J n (zBlock n z)) - F (fun j => ξ j z)) γ :=
        ((hF.continuous.comp ((linA v J n).continuous.comp
          (continuous_pi fun i => continuous_apply _))).aestronglyMeasurable).sub
          (hF.continuous.comp_aestronglyMeasurable hξv)
      refine eLpNorm_mono hm fun z => ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul,
        abs_of_nonneg (mul_nonneg hB0 (Finset.sum_nonneg fun _ _ => abs_nonneg _))]
      refine (hlip _ _).trans (le_of_eq ?_)
      simp only [e, linA_zBlock]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => bot_le) hb
    simpa using ENNReal.Tendsto.const_mul he (Or.inr enorm_ne_top)
  · obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (f := e) (g := fun _ => 0)
      (p := 2) (by norm_num) (he.congr fun n => by congr 1; funext z; simp)).exists_seq_tendsto_ae
    refine ⟨φ, hφ, ?_⟩
    filter_upwards [hae] with z hz j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hz
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j : Fin J =>
      |∑ i ∈ Finset.range (φ k), v j i * z i - ξ j z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

include hv2 hvl hvΛ hξ in
/-- **The upper bound** `ℰ_∞(F(ξ)) ≤ ∫ ∑_j ν_j (∂_jF(ξ))² dγ`. -/
theorem gaussForm_xi_le :
    gaussForm lam' γ (fun z => F (fun j => ξ j z)) ≤
      ∫⁻ z, ENNReal.ofReal (∑ j : Fin J, ν j * (fderiv ℝ F (fun i => ξ i z) (Pi.single j 1)) ^ 2)
        ∂γ := by
  obtain ⟨hL2, φ, hφ, hae⟩ := trunc_xi_conv hF hFc hξ
  have hsub : Tendsto (fun k => eLpNorm (fun z => F (linA v J (φ k) (zBlock (φ k) z)) -
      F (fun j => ξ j z)) 2 γ) atTop (𝓝 0) := hL2.comp hφ.tendsto_atTop
  refine (gaussForm_le_liminf_of_L2 (lam' := lam')
    (f := fun k z => F (linA v J (φ k) (zBlock (φ k) z))) hsub).trans ?_
  have hform := tendsto_formG_trunc (F := F) (v := v) (lam' := lam') (ν := ν) (γ := γ) (ξ := ξ)
    hF hFc hv2 hvl hvΛ hφ hae
  rw [← hform.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun k => ?_)
  obtain ⟨B, hB1, hB2⟩ := trunc_bounds hF v hFc (φ k)
  exact gaussForm_le_formG (γ := γ) (N := φ k) (G := fun x => F (linA v J (φ k) x)) lam'
    (contDiff_trunc hF v (φ k)) hB1 hB2

end SharpLSI
