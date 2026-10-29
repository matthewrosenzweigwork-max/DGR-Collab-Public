import SharpSymmetricLSI.Paper.LipChain1

/-!
# Lipschitz chain rule, part 2: `∇(χ ∘ u) = G` with `|G| ≤ L |∇u|`

`exists_isWeakGrad_comp_lipschitz`: if `IsWeakGrad u g` on `𝕋^ι`, `u` is integrable, every `g_k` is
in `L²`, and `χ` is `L`-Lipschitz, then `χ ∘ u` has a weak gradient `G` with
`|G|² ≤ L² |g|²` a.e. The gradients `χ_j'(u) g` of the smooth approximations are bounded in
`L²(𝕋^ι; ℝ^ι)`; convex combinations of their tails converge strongly
(`exists_tendsto_convexHull`), the matching combinations of `χ_j ∘ u` converge uniformly to `χ ∘ u`,
and `isWeakGrad_of_tendsto` passes to the limit. Each combination is `c · g` with `|c| ≤ L`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped Convolution NNReal ENNReal

namespace SharpLSI
/-! ### The chain rule for Lipschitz functions -/

section chain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector `g y` as an element of `EuclideanSpace ℝ ι`. -/
noncomputable def eVec (g : UnitAddTorus ι → ι → ℝ) (y : UnitAddTorus ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (g y)

theorem norm_eVec_sq (g : UnitAddTorus ι → ι → ℝ) (y : UnitAddTorus ι) :
    ‖eVec g y‖ ^ 2 = sqNorm (g y) := by
  rw [EuclideanSpace.real_norm_sq_eq]; rfl

theorem memLp_eVec {g : UnitAddTorus ι → ι → ℝ} (hg2 : ∀ k, MemLp (fun y => g y k) 2 volume) :
    MemLp (eVec g) 2 volume := by
  have hm : AEStronglyMeasurable (eVec g) volume :=
    (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable
      (AEMeasurable.of_eval fun k => (hg2 k).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  refine (memLp_finsetSum Finset.univ fun k _ => (hg2 k).norm).of_le hm
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
  have h1 : ‖eVec g y‖ ^ 2 ≤ (∑ k, ‖g y k‖) ^ 2 := by
    rw [norm_eVec_sq]
    unfold sqNorm
    calc ∑ k, g y k ^ 2 = ∑ k, ‖g y k‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
      _ ≤ (∑ k, ‖g y k‖) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => norm_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Finset.sum_nonneg fun k _ => norm_nonneg _)
    two_ne_zero).mp h1

theorem integrable_comp_lipschitzWith {χ : ℝ → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ)
    {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume) : Integrable (fun y => χ (u y)) volume := by
  refine Integrable.mono' ((integrable_const |χ 0|).add (hu.norm.const_mul L))
    (hχ.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  have h := hχ.dist_le_mul (u y) 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have := abs_sub_abs_le_abs_sub (χ (u y)) (χ 0)
  linarith

/-- **Chain rule for Lipschitz functions.** If `∇u = g` weakly with `g ∈ L²` and `χ` is
`L`-Lipschitz, then `χ ∘ u` has a weak gradient `G` with `|G| ≤ L |g|` a.e. -/
theorem exists_isWeakGrad_comp_lipschitz {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (hu : Integrable u volume) (hg2 : ∀ k, MemLp (fun y => g y k) 2 volume)
    {χ : ℝ → ℝ} {L : ℝ≥0} (hχ : LipschitzWith L χ) :
    ∃ G : UnitAddTorus ι → ι → ℝ, IsWeakGrad (χ ∘ u) G ∧
      ∀ᵐ y ∂volume, sqNorm (G y) ≤ (L : ℝ) ^ 2 * sqNorm (g y) := by
  obtain ⟨χs, hcd, hder, hunif⟩ := exists_smooth_lipschitz_approx hχ
  have hgi : ∀ k, Integrable (fun y => g y k) volume := fun k => (hg2 k).integrable one_le_two
  have hum := hu.aestronglyMeasurable
  have hvm := memLp_eVec hg2
  set E := Lp (EuclideanSpace ℝ ι) 2 (volume : Measure (UnitAddTorus ι))
  -- the gradients of `χ_j ∘ u`
  have hcj : ∀ j, AEStronglyMeasurable (fun y => deriv (χs j) (u y)) volume := fun j =>
    ((hcd j).continuous_deriv le_rfl).comp_aestronglyMeasurable hum
  have hvj : ∀ j, MemLp (fun y => deriv (χs j) (u y) • eVec g y) 2 volume := fun j =>
    (hvm.const_smul (L : ℝ)).of_le ((hcj j).smul hvm.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, NNReal.abs_eq]
        exact mul_le_mul_of_nonneg_right (hder j _) (norm_nonneg _))
  set x : ℕ → E := fun j => (hvj j).toLp _
  have hxb : ∀ j, ‖x j‖ ≤ L * ‖hvm.toLp (eVec g)‖ := fun j => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(hvj j).coeFn_toLp, hvm.coeFn_toLp] with y h1 h2
    rw [h1, h2, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hder j _) (norm_nonneg _)
  obtain ⟨v, w, hwK, hwv⟩ := exists_tendsto_convexHull x hxb
  -- the convex sets of admissible pairs
  set S : ℕ → Set E := fun n => {z | ∃ (F : UnitAddTorus ι → ℝ) (c : UnitAddTorus ι → ℝ),
    IsWeakGrad F (fun y k => c y * g y k) ∧ Integrable F volume ∧ AEStronglyMeasurable c volume ∧
    (∀ y, |c y| ≤ L) ∧ (∀ y, |F y - χ (u y)| ≤ L / ((n : ℝ) + 1)) ∧
    (⇑z =ᵐ[volume] fun y => c y • eVec g y)} with hS
  have hSconv : ∀ n, Convex ℝ (S n) := by
    intro n z₁ hz₁ z₂ hz₂ a b ha hb hab
    obtain ⟨F₁, c₁, hw₁, hF₁, hc₁, hcb₁, hFb₁, he₁⟩ := hz₁
    obtain ⟨F₂, c₂, hw₂, hF₂, hc₂, hcb₂, hFb₂, he₂⟩ := hz₂
    refine ⟨fun y => a * F₁ y + b * F₂ y, fun y => a * c₁ y + b * c₂ y, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · convert (hw₁.cmul a).add (hw₂.cmul b) using 1
      funext y k; ring
    · exact (hF₁.const_mul a).add (hF₂.const_mul b)
    · exact (hc₁.const_mul a).add (hc₂.const_mul b)
    · intro y
      calc |a * c₁ y + b * c₂ y| ≤ a * |c₁ y| + b * |c₂ y| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * L + b * L := by gcongr <;> [exact hcb₁ y; exact hcb₂ y]
        _ = L := by rw [← add_mul, hab, one_mul]
    · intro y
      have e : a * F₁ y + b * F₂ y - χ (u y) = a * (F₁ y - χ (u y)) + b * (F₂ y - χ (u y)) := by
        linear_combination (χ (u y)) * hab
      rw [e]
      calc |a * (F₁ y - χ (u y)) + b * (F₂ y - χ (u y))|
          ≤ a * |F₁ y - χ (u y)| + b * |F₂ y - χ (u y)| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
        _ ≤ a * (L / ((n : ℝ) + 1)) + b * (L / ((n : ℝ) + 1)) := by
            gcongr <;> [exact hFb₁ y; exact hFb₂ y]
        _ = L / ((n : ℝ) + 1) := by rw [← add_mul, hab, one_mul]
    · filter_upwards [Lp.coeFn_add (a • z₁) (b • z₂), Lp.coeFn_smul a z₁, Lp.coeFn_smul b z₂, he₁, he₂]
        with y h1 h2 h3 h4 h5
      rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, add_smul, smul_smul,
        smul_smul]
  have hxS : ∀ n j, n ≤ j → x j ∈ S n := fun n j hnj => by
    refine ⟨fun y => χs j (u y), fun y => deriv (χs j) (u y),
      isWeakGrad_comp h hu hgi (hcd j) (hder j), integrable_comp_of_lipschitz (hcd j) (hder j) hu,
      hcj j, fun y => hder j _, fun y => (hunif j (u y)).trans ?_, (hvj j).coeFn_toLp⟩
    have h1 : ((n : ℝ) + 1) ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnj
    exact div_le_div_of_nonneg_left L.2 (by positivity) h1
  have hwS : ∀ n, w n ∈ S n := fun n =>
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; exact hxS n j hj) (hSconv n) (hwK n)
  choose F c hFw hFi hcm hcb hFb hwe using hwS
  -- the limit
  have hvL : MemLp (⇑v) 2 volume := Lp.memLp v
  have hGi : ∀ k, Integrable (fun y => (v y) k) volume := fun k =>
    ((hvL.of_le ((PiLp.continuous_apply 2 _ k).comp_aestronglyMeasurable hvL.aestronglyMeasurable)
      (Eventually.of_forall fun y => PiLp.norm_apply_le (v y) k)).integrable one_le_two)
  have hdiff : Tendsto (fun n => eLpNorm (⇑(w n) - ⇑v) 2 volume) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' w v).mp hwv
  refine ⟨fun y k => (v y) k, ?_, ?_⟩
  · refine isWeakGrad_of_tendsto (F := F) (G := fun n y k => c n y * g y k) hFw hFi
      (fun n k => (hgi k).bdd_mul (hcm n) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hcb n y))
      (integrable_comp_lipschitzWith hχ hu) hGi ?_ ?_
    · have hb : ∀ n, ∫⁻ y, ‖F n y - (χ ∘ u) y‖ₑ ≤ ENNReal.ofReal (L / ((n : ℝ) + 1)) := fun n => by
        calc ∫⁻ y, ‖F n y - (χ ∘ u) y‖ₑ ≤ ∫⁻ _, ENNReal.ofReal (L / ((n : ℝ) + 1)) :=
              lintegral_mono fun y => by
                rw [← ofReal_norm, Real.norm_eq_abs]
                exact ENNReal.ofReal_le_ofReal (hFb n y)
          _ = _ := by simp
      have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (L / ((n : ℝ) + 1))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine ENNReal.tendsto_ofReal ?_
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (L : ℝ)
        simpa [div_eq_mul_inv] using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun n => zero_le) hb
    · intro k
      have hb : ∀ n, ∫⁻ y, ‖c n y * g y k - (v y) k‖ₑ ≤ eLpNorm (⇑(w n) - ⇑v) 2 volume := fun n => by
        calc ∫⁻ y, ‖c n y * g y k - (v y) k‖ₑ = ∫⁻ y, ‖(⇑(w n) - ⇑v) y k‖ₑ := by
              refine lintegral_congr_ae ?_
              filter_upwards [hwe n] with y hy
              rw [Pi.sub_apply, hy]
              rfl
          _ ≤ ∫⁻ y, ‖(⇑(w n) - ⇑v) y‖ₑ := lintegral_mono fun y => by
              simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
              exact PiLp.nnnorm_apply_le _ k
          _ = eLpNorm (⇑(w n) - ⇑v) 1 volume := (eLpNorm_one_eq_lintegral_enorm
                ((Lp.memLp (w n)).aestronglyMeasurable.sub hvL.aestronglyMeasurable)).symm
          _ ≤ eLpNorm (⇑(w n) - ⇑v) 2 volume := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff (fun n => zero_le) hb
  · have hmeas : TendstoInMeasure volume (fun n => ⇑(w n)) atTop ⇑v :=
      tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hdiff
    obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hns, ae_all_iff.mpr hwe] with y hy hye
    have hbd : ∀ i, ‖(w (ns i)) y‖ ^ 2 ≤ (L : ℝ) ^ 2 * sqNorm (g y) := fun i => by
      rw [hye (ns i), norm_smul, mul_pow, norm_eVec_sq, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hcb _ y) 2)
        (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have hlim : Tendsto (fun i => ‖(w (ns i)) y‖ ^ 2) atTop (𝓝 (‖v y‖ ^ 2)) :=
      (continuous_norm.tendsto _ |>.comp hy).pow 2
    have := le_of_tendsto' hlim hbd
    have e1 : sqNorm (fun k => (v y) k) = ‖v y‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; rfl
    rw [e1]; exact this

end chain

end SharpLSI
