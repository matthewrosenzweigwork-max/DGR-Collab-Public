import SharpSymmetricLSI.Paper.AppAConv2

/-!
# Convergence toolkit (3): the rate at level `(ε, δ)` converges as `ε → 0`

For bounded `f ∈ H¹` and bounded `F`, `R_{ε,δ}(f, F) → R_δ(f, F)` (`tendsto_epsRate`), where
`R_δ(f, F) = ∑ⱼ ∫ (G_δ''(f) ∂ⱼf + ∂ⱼV + ∂ⱼ(W*f)) (∂ⱼf + Fⱼ)`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem abs_entGpp_sub_le {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    |entGpp δ a - entGpp δ b| ≤ |a - b| / δ ^ 2 := by
  unfold entGpp
  set A := Real.sqrt (a ^ 2 + δ ^ 2)
  set B := Real.sqrt (b ^ 2 + δ ^ 2)
  have hA : δ ≤ A := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg a])
  have hB : δ ≤ B := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg b])
  have hA0 : 0 < A := hδ.trans_le hA
  have hB0 : 0 < B := hδ.trans_le hB
  have haA : |a| ≤ A := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hbB : |b| ≤ B := by rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hA2 : A ^ 2 = a ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : B ^ 2 = b ^ 2 + δ ^ 2 := Real.sq_sqrt (by positivity)
  -- `|B - A| ≤ |a - b|`
  have hBA : |B - A| ≤ |a - b| := by
    have e : (B - A) * (B + A) = (b - a) * (b + a) := by nlinarith
    have hpos : 0 < B + A := by linarith
    have h1 : |B - A| * (B + A) = |b - a| * |b + a| := by
      rw [← abs_of_pos hpos, ← abs_mul, e, abs_mul]
    have h2 : |b + a| ≤ B + A := (abs_add_le _ _).trans (by linarith)
    rw [abs_sub_comm a b]
    by_contra hc
    push Not at hc
    have : |b - a| * |b + a| < |B - A| * (B + A) := by
      calc |b - a| * |b + a| ≤ |b - a| * (B + A) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ < |B - A| * (B + A) := mul_lt_mul_of_pos_right hc hpos
    linarith
  rw [inv_sub_inv hA0.ne' hB0.ne', abs_div, abs_of_pos (mul_pos hA0 hB0)]
  rw [div_le_div_iff₀ (mul_pos hA0 hB0) (by positivity)]
  calc |B - A| * δ ^ 2 ≤ |a - b| * δ ^ 2 := mul_le_mul_of_nonneg_right hBA (by positivity)
    _ ≤ |a - b| * (A * B) := mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)

theorem sq_integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : MemLp g 2 μ) : (∫ x, |g x| ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have hgi : Integrable g μ := hg.integrable one_le_two
  set m := ∫ x, |g x| ∂μ
  have h2 := hg.integrable_sq
  have hvar : 0 ≤ ∫ x, (|g x| - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (|g x| - m) ^ 2 ∂μ = (∫ x, g x ^ 2 ∂μ) - m ^ 2 := by
    have e1 : (fun x => (|g x| - m) ^ 2) = fun x => (g x ^ 2 + (-(2 * m)) * |g x|) + m ^ 2 := by
      funext x; nlinarith [sq_abs (g x)]
    rw [e1, integral_add (f := fun x => g x ^ 2 + -(2 * m) * |g x|) (g := fun _ => m ^ 2)
      (h2.add (hgi.abs.const_mul _)) (integrable_const _),
      integral_add (f := fun x => g x ^ 2) (g := fun x => -(2 * m) * |g x|) h2
        (hgi.abs.const_mul _), integral_const_mul, integral_const, probReal_univ, one_smul]
    ring
  linarith

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The limit rate `R_δ(f, F)`. -/
noncomputable def limRate (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (δ : ℝ)
    (f : Torus d → ℝ) (F : Torus d → Fin d → ℝ) : ℝ :=
  ∑ j, ∫ x, (entGpp δ (f x) * weakGrad f x j + lipGrad V x j + bForceL W f x j) *
    (weakGrad f x j + F x j)

/-- **The rate converges as `ε → 0`.** -/
theorem tendsto_epsRate (hyp : Hyp V W KV KW) {δ : ℝ} (hδ : 0 < δ) {f : Torus d → ℝ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) {F : Torus d → Fin d → ℝ}
    (hF : ∀ k, Measurable fun z => F z k) {AK : ℝ} (hFb : ∀ z k, |F z k| ≤ AK)
    {g : Torus d → Fin d → ℝ} (hg : IsWeakGrad f g) (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) :
    Tendsto (fun ε => epsRate V W δ ε f F) (𝓝[>] 0) (𝓝 (limRate V W δ f F)) := by
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  set w := weakGrad f with hwdef
  have hw : IsWeakGrad f w := appA_isWeakGrad_weakGrad ⟨g, hg⟩
  have hwg : w =ᵐ[volume] g := appA_weakGrad_ae_eq hg
  have hw2 : ∀ j, MemLp (fun y => w y j) 2 volume := fun j =>
    (hg2 j).ae_eq (hwg.mono fun x hx => (congrFun hx j).symm)
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hVg := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hφL2 := tendsto_heatT_L2 hf hK
  have hφi : ∀ ε, 0 < ε → Integrable (heatT ε f) (haar d) := fun ε hε =>
    (memLp_of_continuous (continuous_heatT hε hfi) 2).integrable one_le_two
  have hφ2 : ∀ ε, 0 < ε → MemLp (fun x => heatT ε f x - f x) 2 (haar d) := fun ε hε =>
    (memLp_of_continuous (continuous_heatT hε hfi) 2).sub (memLp_of_abs_le hf hK 2)
  have hδ1 : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  have hGabs : ∀ r, |entGpp δ r| ≤ δ⁻¹ := fun r => by
    rw [abs_of_pos (entGpp_pos hδ r)]; exact entGpp_le hδ r
  unfold epsRate limRate
  refine tendsto_finsetSum _ fun j _ => ?_
  -- the `L²` facts
  have hBc2 : MemLp (fun x => lipGrad V x j) 2 (haar d) :=
    MemLp.of_bound (appA_aestronglyMeasurable_grad hVg j) LV
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hLV x j)
  have hCf2 : ∀ {h : Torus d → ℝ}, Integrable h (haar d) →
      MemLp (fun x => bForceL W h x j) 2 (haar d) := fun {h} hh =>
    MemLp.of_bound (appA_aestronglyMeasurable_grad (isWeakGrad_convDens' hyp hh) j)
      (Cb * ∫ y, |h y| ∂haar d) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact appA_abs_bForceL_le hCb hh x j)
  have hA02 : MemLp (fun x => entGpp δ (f x) * w x j) 2 (haar d) :=
    ((hw2 j).const_mul δ⁻¹).of_le
      (((continuous_entGpp hδ).measurable.comp hf).aestronglyMeasurable.mul (hw2 j).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hδ1]
        exact mul_le_mul_of_nonneg_right (hGabs _) (abs_nonneg _))
  have hX : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (fun x => entGpp δ (heatT ε f x) * dpart_appA (heatT ε f) j x +
      lipGrad V x j + bForceL W (heatT ε f) x j) 2 (haar d) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact ((memLp_of_continuous (((continuous_entGpp hδ).comp (continuous_heatT hε hfi)).mul
      (continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j))) 2).add hBc2).add
      (hCf2 (hφi ε hε))
  have hY : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (fun x => dpart_appA (heatT ε f) j x +
      heatT ε (fun z => F z j) x) 2 (haar d) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact memLp_of_continuous ((continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)).add
      (continuous_heatT hε (appA_integrable_of_abs_le' (hF j) fun z => hFb z j))) 2
  have hX0 : MemLp (fun x => entGpp δ (f x) * w x j + lipGrad V x j + bForceL W f x j) 2 (haar d) :=
    (hA02.add hBc2).add (hCf2 hfi)
  have hY0 : MemLp (fun x => w x j + F x j) 2 (haar d) :=
    (hw2 j).add (memLp_of_abs_le (hF j) (fun z => hFb z j) 2)
  -- (i) `G_δ''(φ_ε) ∂ⱼφ_ε → G_δ''(f) wⱼ`
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x => entGpp δ (heatT ε f x)) (haar d) ∧
      ∀ x, |entGpp δ (heatT ε f x)| ≤ δ⁻¹ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact ⟨((continuous_entGpp hδ).comp (continuous_heatT hε hfi)).aestronglyMeasurable,
      fun x => hGabs _⟩
  have hm2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun x => (entGpp δ (heatT ε f x) - entGpp δ (f x)) ^ 2) (haar d) ∧
      ∀ x, |(entGpp δ (heatT ε f x) - entGpp δ (f x)) ^ 2| ≤ (2 * δ⁻¹) ^ 2 := by
    filter_upwards [hm] with ε ⟨h1, h2⟩
    refine ⟨(h1.sub ((continuous_entGpp hδ).measurable.comp hf).aestronglyMeasurable).pow 2,
      fun x => ?_⟩
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) 2
    linarith [h2 x, hGabs (f x)]
  have hm2c : Tendsto (fun ε => ∫ x, |(entGpp δ (heatT ε f x) - entGpp δ (f x)) ^ 2| ∂haar d)
      (𝓝[>] 0) (𝓝 0) := by
    have hup := hφL2.const_mul ((δ ^ 2)⁻¹ ^ 2)
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun ε => integral_nonneg fun x => abs_nonneg _) ?_
    filter_upwards [hm2, self_mem_nhdsWithin] with ε h12 (hε : 0 < ε)
    obtain ⟨h1, h2⟩ := h12
    rw [← integral_const_mul]
    refine integral_mono (integrable_of_abs_le_finite (continuous_abs.comp_aestronglyMeasurable h1) (B := (2 * δ⁻¹) ^ 2) fun x => by
        rw [abs_abs]; exact h2 x)
      ((hφ2 ε hε).integrable_sq.const_mul _) fun x => ?_
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    have := abs_entGpp_sub_le hδ (heatT ε f x) (f x)
    rw [← sq_abs, show (δ ^ 2)⁻¹ ^ 2 * (heatT ε f x - f x) ^ 2 = (|heatT ε f x - f x| / δ ^ 2) ^ 2 by
      rw [div_pow, sq_abs]; field_simp]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hmc : Tendsto (fun ε => ∫ x, (entGpp δ (heatT ε f x) - entGpp δ (f x)) ^ 2 * w x j ^ 2 ∂haar d)
      (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_abs_mul_of_L1 (by positivity) hm2 hm2c (hw2 j).integrable_sq
    refine this.congr' (Eventually.of_forall fun ε => integral_congr_ae
      (Eventually.of_forall fun x => ?_))
    simp only
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
  have hAc := tendsto_L2_mul_bdd (μ := haar d) hm
    ((continuous_entGpp hδ).measurable.comp hf).aestronglyMeasurable (fun x => hGabs (f x))
    (X := fun ε x => dpart_appA (heatT ε f) j x) (X0 := fun x => w x j)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact memLp_of_continuous (continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)) 2)
    (hw2 j) (tendsto_dpart_heatT_L2 hf hK hw hw2 j) hmc
  -- (ii) the potential term is fixed
  have hBc : Tendsto (fun _ : ℝ => ∫ x, (lipGrad V x j - lipGrad V x j) ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
    simp
  -- (iii) `bForceL W φ_ε → bForceL W f` uniformly
  have hCc : Tendsto (fun ε => ∫ x, (bForceL W (heatT ε f) x j - bForceL W f x j) ^ 2 ∂haar d)
      (𝓝[>] 0) (𝓝 0) := by
    have hup := hφL2.const_mul (Cb ^ 2)
    rw [mul_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun ε => integral_nonneg fun x => sq_nonneg _) ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hpt : ∀ x, (bForceL W (heatT ε f) x j - bForceL W f x j) ^ 2 ≤
        Cb ^ 2 * ∫ y, (heatT ε f y - f y) ^ 2 ∂haar d := fun x => by
      rw [bForceL_sub hCb hyp (hφi ε hε) hfi x j]
      have h1 := appA_abs_bForceL_le hCb ((hφi ε hε).sub hfi) x j
      have h2 := sq_integral_abs_le (μ := haar d) (hφ2 ε hε)
      have h3 : (bForceL W (fun y => heatT ε f y - f y) x j) ^ 2 ≤
          (Cb * ∫ y, |heatT ε f y - f y| ∂haar d) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [mul_pow] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    calc ∫ x, (bForceL W (heatT ε f) x j - bForceL W f x j) ^ 2 ∂haar d
        ≤ ∫ _x, Cb ^ 2 * ∫ y, (heatT ε f y - f y) ^ 2 ∂haar d ∂haar d :=
          integral_mono (((hCf2 (hφi ε hε)).sub (hCf2 hfi)).integrable_sq) (integrable_const _) hpt
      _ = Cb ^ 2 * ∫ y, (heatT ε f y - f y) ^ 2 ∂haar d := by simp
  have hXA : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (fun x => entGpp δ (heatT ε f x) * dpart_appA (heatT ε f) j x)
      2 (haar d) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact memLp_of_continuous (((continuous_entGpp hδ).comp (continuous_heatT hε hfi)).mul
      (continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j))) 2
  have hAB := tendsto_L2_add hXA (Eventually.of_forall fun _ => hBc2) hA02 hBc2 hAc hBc
  have hXC : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (fun x => bForceL W (heatT ε f) x j) 2 (haar d) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hCf2 (hφi ε hε)
  have hXAB : ∀ᶠ ε in 𝓝[>] (0 : ℝ), MemLp (fun x => entGpp δ (heatT ε f x) * dpart_appA (heatT ε f) j x +
      lipGrad V x j) 2 (haar d) := by
    filter_upwards [hXA] with ε h
    exact h.add hBc2
  have hXc := tendsto_L2_add hXAB hXC (hA02.add hBc2) (hCf2 hfi) hAB hCc
  -- `Y`
  have hYc := tendsto_L2_add (Y := fun ε x => heatT ε (fun z => F z j) x) (Y0 := fun x => F x j)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact memLp_of_continuous (continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)) 2)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact memLp_of_continuous (continuous_heatT hε
        (appA_integrable_of_abs_le' (hF j) fun z => hFb z j)) 2)
    (hw2 j) (memLp_of_abs_le (hF j) (fun z => hFb z j) 2)
    (tendsto_dpart_heatT_L2 hf hK hw hw2 j) (tendsto_heatT_L2 (hF j) (fun z => hFb z j))
  exact tendsto_integral_mul_of_L2_appA hX hY hX0 hY0 hXc hYc

end SharpLSI
