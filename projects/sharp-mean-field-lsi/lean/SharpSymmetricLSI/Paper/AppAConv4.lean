import SharpSymmetricLSI.Paper.AppAConv3

/-!
# Convergence toolkit (4): the free-energy identity at level `δ`

`E_{ε,δ}(f) → E_δ(f)` for bounded `f` (`tendsto_epsE`), and the identity
`E_δ(ρ_t) = E_δ(ρ₀) - ∫_{(0,t]} R_δ(ρ_u, N_u) du` (`LinMild.delta_identity`), by dominated
convergence in time with the bound `|R_{ε,δ}(u)| ≤ C₁ ∑ⱼ ∫ |∇ρ_u|² + C₂`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem exists_lipschitz_entG {δ : ℝ} (hδ : 0 < δ) (K : ℝ) :
    ∃ L, 0 ≤ L ∧ ∀ a b, |a| ≤ K → |b| ≤ K → |entG δ a - entG δ b| ≤ L * |a - b| := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_on_Icc (continuous_entGp δ) K
  refine ⟨L, hL0, fun a b ha hb => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := entG δ) (f' := entGp δ)
    (s := Icc (-K) K) (C := L) (fun x _ => (hasDerivAt_entG hδ x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hL x (abs_le.2 hx)) (convex_Icc _ _)
    (abs_le.1 hb) (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using this

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The regularized free energy at level `δ`. -/
noncomputable def limE (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (δ : ℝ)
    (f : Torus d → ℝ) : ℝ :=
  (∫ x, (entG δ (f x) + V x * f x)) + (∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)) / 2

theorem tendsto_integral_abs_heatT_sub_eps {f : Torus d → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun ε => ∫ x, |heatT ε f x - f x| ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  have hup := (Real.continuous_sqrt.tendsto 0).comp (tendsto_heatT_L2 hf hK)
  rw [Real.sqrt_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun ε => integral_nonneg fun x => abs_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact Real.le_sqrt_of_sq_le (sq_integral_abs_le
    ((memLp_of_continuous (continuous_heatT hε hfi) 2).sub (memLp_of_abs_le hf hK 2)))

/-- **`E_{ε,δ}(f) → E_δ(f)`.** -/
theorem tendsto_epsE (hyp : Hyp V W KV KW) {δ : ℝ} (hδ : 0 < δ) {f : Torus d → ℝ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun ε => epsE V W δ ε f) (𝓝[>] 0) (𝓝 (limE V W δ f)) := by
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_entG hδ K
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  have hMV0 : 0 ≤ MV := (abs_nonneg _).trans (hVb 0)
  obtain ⟨MW, hMW⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_W.continuousOn
  have hWb : ∀ x y, |W x y| ≤ MW := fun x y => by
    simpa [Real.norm_eq_abs] using hMW (x, y) (mem_univ _)
  have hMW0 : 0 ≤ MW := (abs_nonneg _).trans (hWb 0 0)
  have hWm : Measurable fun p : Torus d × Torus d => W p.1 p.2 := hyp.continuous_W.measurable
  have hL1 := tendsto_integral_abs_heatT_sub_eps hf hK
  have hbd : ∀ ε, 0 < ε → ∀ x, |heatT ε f x| ≤ K := fun ε hε x =>
    abs_heatT_le hε hf.aestronglyMeasurable (Eventually.of_forall hK) x
  -- the bound `|E_{ε,δ}(f) - E_δ(f)| ≤ (L + MV + MW K) ∫ |φ_ε - f|`
  set C := L + MV + MW * K
  have hup := hL1.const_mul C
  rw [mul_zero] at hup
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun ε => norm_nonneg _) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hφc := continuous_heatT hε hfi
  have hφm := hφc.measurable
  have hEm : ∀ {g : Torus d → ℝ}, Measurable g → (∀ x, |g x| ≤ K) →
      Integrable (fun x => entG δ (g x) + V x * g x) (haar d) := fun {g} hg hgK => by
    obtain ⟨M, -, hM⟩ := exists_bound_on_Icc (continuous_entG hδ) K
    exact integrable_of_abs_le_finite (((continuous_entG hδ).measurable.comp hg).add
      (hyp.continuous_V.measurable.mul hg)).aestronglyMeasurable (B := M + MV * K) fun x => by
      refine (abs_add_le _ _).trans (add_le_add (hM _ (hgK x)) ?_)
      rw [abs_mul]; exact mul_le_mul (hVb x) (hgK x) (abs_nonneg _) hMV0
  have hWi : ∀ {g : Torus d → ℝ}, Measurable g → (∀ x, |g x| ≤ K) →
      Integrable (fun p : Torus d × Torus d => W p.1 p.2 * (g p.1 * g p.2)) (volume.prod volume) :=
    fun {g} hg hgK => integrable_of_abs_le_finite (hWm.mul ((hg.comp measurable_fst).mul
      (hg.comp measurable_snd))).aestronglyMeasurable (B := MW * (K * K)) fun p => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hWb _ _) (mul_le_mul (hgK _) (hgK _) (abs_nonneg _) hK0) (by positivity) hMW0
  have hD : Integrable (fun x => |heatT ε f x - f x|) (haar d) :=
    ((memLp_of_continuous hφc 2).integrable one_le_two |>.sub hfi).abs
  unfold epsE limE
  rw [Real.norm_eq_abs]
  have e1 : |(∫ x, (entG δ (heatT ε f x) + V x * heatT ε f x)) - ∫ x, (entG δ (f x) + V x * f x)| ≤
      (L + MV) * ∫ x, |heatT ε f x - f x| ∂haar d := by
    rw [← integral_sub (hEm hφm (hbd ε hε)) (hEm hf hK), ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono
      ((hEm hφm (hbd ε hε)).sub (hEm hf hK)).abs (hD.const_mul _) fun x => ?_)
    simp only
    have h1 := hL _ _ (hbd ε hε x) (hK x)
    calc |entG δ (heatT ε f x) + V x * heatT ε f x - (entG δ (f x) + V x * f x)|
        = |(entG δ (heatT ε f x) - entG δ (f x)) + V x * (heatT ε f x - f x)| := by ring_nf
      _ ≤ L * |heatT ε f x - f x| + MV * |heatT ε f x - f x| := by
          refine (abs_add_le _ _).trans (add_le_add h1 ?_)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hVb x) (abs_nonneg _)
      _ = (L + MV) * |heatT ε f x - f x| := by ring
  have e2 : |(∫ p, W p.1 p.2 * (heatT ε f p.1 * heatT ε f p.2) ∂(volume.prod volume)) -
      ∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)| ≤
      2 * (MW * K) * ∫ x, |heatT ε f x - f x| ∂haar d := by
    rw [← integral_sub (hWi hφm (hbd ε hε)) (hWi hf hK)]
    have hD1 : Integrable (fun p : Torus d × Torus d => |heatT ε f p.1 - f p.1|) (volume.prod volume) :=
      hD.comp_fst (ν := volume)
    have hD2 : Integrable (fun p : Torus d × Torus d => |heatT ε f p.2 - f p.2|) (volume.prod volume) :=
      hD.comp_snd (μ := volume)
    have i1 : ∫ p : Torus d × Torus d, |heatT ε f p.1 - f p.1| ∂(volume.prod volume) =
        ∫ x, |heatT ε f x - f x| ∂haar d := by
      rw [integral_fun_fst (fun x => |heatT ε f x - f x|)]; simp
    have i2 : ∫ p : Torus d × Torus d, |heatT ε f p.2 - f p.2| ∂(volume.prod volume) =
        ∫ x, |heatT ε f x - f x| ∂haar d := by
      rw [integral_fun_snd (fun x => |heatT ε f x - f x|)]; simp
    refine (abs_integral_le_integral_abs).trans ((integral_mono
      ((hWi hφm (hbd ε hε)).sub (hWi hf hK)).abs ((hD1.add hD2).const_mul (MW * K)) fun p => ?_).trans
      (le_of_eq ?_))
    · show |W p.1 p.2 * (heatT ε f p.1 * heatT ε f p.2) - W p.1 p.2 * (f p.1 * f p.2)| ≤
        MW * K * (|heatT ε f p.1 - f p.1| + |heatT ε f p.2 - f p.2|)
      rw [← mul_sub, abs_mul]
      have : |heatT ε f p.1 * heatT ε f p.2 - f p.1 * f p.2| ≤
          K * |heatT ε f p.1 - f p.1| + K * |heatT ε f p.2 - f p.2| := by
        have e : heatT ε f p.1 * heatT ε f p.2 - f p.1 * f p.2 =
            heatT ε f p.2 * (heatT ε f p.1 - f p.1) + f p.1 * (heatT ε f p.2 - f p.2) := by ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
        · exact mul_le_mul_of_nonneg_right (hbd ε hε _) (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_right (hK _) (abs_nonneg _)
      calc |W p.1 p.2| * |heatT ε f p.1 * heatT ε f p.2 - f p.1 * f p.2|
          ≤ MW * (K * |heatT ε f p.1 - f p.1| + K * |heatT ε f p.2 - f p.2|) :=
            mul_le_mul (hWb _ _) this (abs_nonneg _) hMW0
        _ = MW * K * (|heatT ε f p.1 - f p.1| + |heatT ε f p.2 - f p.2|) := by ring
    · rw [integral_const_mul]
      have i3 : ∫ p : Torus d × Torus d, (|heatT ε f p.1 - f p.1| + |heatT ε f p.2 - f p.2|)
          ∂(volume.prod volume) = 2 * ∫ x, |heatT ε f x - f x| ∂haar d := by
        rw [integral_add hD1 hD2, i1, i2]; ring
      simp only [Pi.add_apply]
      rw [i3]
      ring
  calc |(∫ x, (entG δ (heatT ε f x) + V x * heatT ε f x)) +
        (∫ p, W p.1 p.2 * (heatT ε f p.1 * heatT ε f p.2) ∂(volume.prod volume)) / 2 -
      ((∫ x, (entG δ (f x) + V x * f x)) +
        (∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)) / 2)|
      ≤ |(∫ x, (entG δ (heatT ε f x) + V x * heatT ε f x)) - ∫ x, (entG δ (f x) + V x * f x)| +
        |(∫ p, W p.1 p.2 * (heatT ε f p.1 * heatT ε f p.2) ∂(volume.prod volume)) -
          ∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)| / 2 := by
        rw [← abs_two, ← abs_div]
        refine (le_of_eq (by ring_nf)).trans (abs_add_le _ _)
    _ ≤ (L + MV) * ∫ x, |heatT ε f x - f x| ∂haar d +
        2 * (MW * K) * (∫ x, |heatT ε f x - f x| ∂haar d) / 2 := by
        gcongr
    _ = C * ∫ x, |heatT ε f x - f x| ∂haar d := by simp only [C]; ring

/-- **The uniform bound** `|R_{ε,δ}(f, F)| ≤ C₁ ∑ⱼ ∫ gⱼ² + C₂`. -/
theorem exists_epsRate_bound (hyp : Hyp V W KV KW) {δ : ℝ} (hδ : 0 < δ) (K AK : ℝ) :
    ∃ C₁ C₂ : ℝ, ∀ ε, 0 < ε → ∀ f : Torus d → ℝ, Measurable f → (∀ x, |f x| ≤ K) →
      ∀ F : Torus d → Fin d → ℝ, (∀ k, Measurable fun z => F z k) → (∀ z k, |F z k| ≤ AK) →
      ∀ g : Torus d → Fin d → ℝ, IsWeakGrad f g → (∀ j, MemLp (fun y => g y j) 2 volume) →
      |epsRate V W δ ε f F| ≤ C₁ * (∑ j, ∫ x, g x j ^ 2) + C₂ := by
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  set K' := max K 0
  set e := max AK 0
  set c := LV + Cb * K'
  have hc0 : 0 ≤ c := by positivity
  set C₁ := δ⁻¹ + δ⁻¹ * e + c
  set C₂ := δ⁻¹ * e + c + c * e
  have hδ1 : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  refine ⟨C₁, Fintype.card (Fin d) * C₂, fun ε hε f hf hK F hF hFb g hg hg2 => ?_⟩
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  have hφc := continuous_heatT hε hfi
  have hφi : Integrable (heatT ε f) (haar d) := (memLp_of_continuous hφc 2).integrable one_le_two
  have hφK : ∀ x, |heatT ε f x| ≤ K' := fun x =>
    (abs_heatT_le hε hf.aestronglyMeasurable (Eventually.of_forall hK) x).trans (le_max_left _ _)
  have hφ1 : ∫ y, |heatT ε f y| ∂haar d ≤ K' := by
    have := abs_integral_le_of_abs_le (μ := haar d) (f := fun y => |heatT ε f y|)
      (M := K') fun y => by rw [abs_abs]; exact hφK y
    rwa [abs_of_nonneg (integral_nonneg fun y => abs_nonneg _)] at this
  unfold epsRate
  have eS : C₁ * (∑ j, ∫ x, g x j ^ 2) + (Fintype.card (Fin d) : ℝ) * C₂ =
      ∑ j : Fin d, (C₁ * (∫ x, g x j ^ 2) + C₂) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [eS]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  set a := dpart_appA (heatT ε f) j
  have hac : Continuous a := continuous_of_isSmoothT (isSmoothT_dpart (isSmoothT_heatT hε hfi) j)
  have hpt : ∀ x, |(entGpp δ (heatT ε f x) * a x + lipGrad V x j + bForceL W (heatT ε f) x j) *
      (a x + heatT ε (fun z => F z j) x)| ≤ C₁ * a x ^ 2 + C₂ := fun x => by
    have hX : |entGpp δ (heatT ε f x) * a x + lipGrad V x j + bForceL W (heatT ε f) x j| ≤
        δ⁻¹ * |a x| + c := by
      have h1 : |entGpp δ (heatT ε f x) * a x| ≤ δ⁻¹ * |a x| := by
        rw [abs_mul, abs_of_pos (entGpp_pos hδ _)]
        exact mul_le_mul_of_nonneg_right (entGpp_le hδ _) (abs_nonneg _)
      have h2 := appA_abs_bForceL_le hCb hφi x j
      have h3 : Cb * ∫ y, |heatT ε f y| ∂haar d ≤ Cb * K' := mul_le_mul_of_nonneg_left hφ1 hCb0
      calc _ ≤ |entGpp δ (heatT ε f x) * a x| + |lipGrad V x j| + |bForceL W (heatT ε f) x j| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ δ⁻¹ * |a x| + LV + Cb * K' := by linarith [hLV x j]
        _ = δ⁻¹ * |a x| + c := by ring
    have hAKe : AK ≤ e := le_max_left _ _
    have hψ : |heatT ε (fun z => F z j) x| ≤ e := (abs_heatT_le hε (hF j).aestronglyMeasurable
      (Eventually.of_forall fun z => hFb z j) x).trans hAKe
    have hY : |a x + heatT ε (fun z => F z j) x| ≤ |a x| + e :=
      (abs_add_le _ _).trans (add_le_add le_rfl hψ)
    have he0 : 0 ≤ e := le_max_right _ _
    have ha1 : |a x| ≤ 1 + a x ^ 2 := by nlinarith [sq_abs (a x), abs_nonneg (a x)]
    rw [abs_mul]
    calc _ ≤ (δ⁻¹ * |a x| + c) * (|a x| + e) :=
          mul_le_mul hX hY (abs_nonneg _) (by positivity)
      _ = δ⁻¹ * a x ^ 2 + (δ⁻¹ * e + c) * |a x| + c * e := by rw [← sq_abs (a x)]; ring
      _ ≤ δ⁻¹ * a x ^ 2 + (δ⁻¹ * e + c) * (1 + a x ^ 2) + c * e := by gcongr
      _ = C₁ * a x ^ 2 + C₂ := by simp only [C₁, C₂]; ring
  have ha2 : Integrable (fun x => a x ^ 2) (haar d) := (memLp_of_continuous hac 2).integrable_sq
  calc |∫ x, (entGpp δ (heatT ε f x) * a x + lipGrad V x j + bForceL W (heatT ε f) x j) *
        (a x + heatT ε (fun z => F z j) x) ∂haar d|
      ≤ ∫ x, (C₁ * a x ^ 2 + C₂) ∂haar d :=
        (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun x => abs_nonneg _) ((ha2.const_mul C₁).add (integrable_const C₂))
          (Eventually.of_forall hpt))
    _ = C₁ * (∫ x, a x ^ 2 ∂haar d) + C₂ := by
        rw [integral_add (ha2.const_mul C₁) (integrable_const C₂), integral_const_mul]; simp
    _ ≤ C₁ * (∫ x, g x j ^ 2) + C₂ := by
        have : 0 ≤ C₁ := by positivity
        have := mul_le_mul_of_nonneg_left (integral_dpart_heatT_sq_le hε hf hK hg hg2 j) this
        linarith

namespace LinMild

variable {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {N : ℝ → Torus d → Fin d → ℝ} {A : ℝ}

theorem exists_measurable_epsRate (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ}
    (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) {T K : ℝ} (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) :
    ∃ Φ : ℝ → ℝ, Measurable Φ ∧ ∀ u ∈ Icc 0 T, epsRate V W δ ε (ρ u) (N u) = Φ u := by
  set Fo := forcing (ρ := ρ) (N := N) ε with hFo
  have hFm : Measurable (Function.uncurry Fo) := h.measurable_forcing hε
  have hWm : Measurable (Function.uncurry W) := hyp.continuous_W.measurable
  set Af : ℝ → ℝ := fun u => ∫ x, (entGp δ (heatT ε (ρ u) x) + V x) * Fo u x with hAf
  set Bf : ℝ → ℝ := fun u =>
    ∫ p, W p.1 p.2 * (Fo u p.1 * heatT ε (ρ u) p.2) ∂(volume.prod volume) with hBf
  have hAm : Measurable Af := by
    have hm : Measurable fun p : ℝ × Torus d =>
        (entGp δ (heatT ε (ρ p.1) p.2) + V p.2) * Fo p.1 p.2 :=
      (((continuous_entGp δ).measurable.comp (measurable_heatT_family h.meas)).add
        (hyp.continuous_V.measurable.comp measurable_snd)).mul hFm
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable Bf := by
    have hm : Measurable fun q : ℝ × (Torus d × Torus d) =>
        W q.2.1 q.2.2 * (Fo q.1 q.2.1 * heatT ε (ρ q.1) q.2.2) :=
      (hWm.comp measurable_snd).mul ((hFm.comp (measurable_fst.prodMk
        (measurable_fst.comp measurable_snd))).mul ((measurable_heatT_family h.meas).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  refine ⟨fun u => -(Af u + Bf u), (hAm.add hBm).neg, fun u hu => ?_⟩
  have := h.rate_eq hyp hδ hε hK hu
  simp only [hAf, hBf]; linarith

/-- **The free-energy identity at level `δ`.** -/
theorem delta_identity (hyp : Hyp V W KV KW) (h : LinMild ρ₀ ρ N A) {δ : ℝ} (hδ : 0 < δ)
    {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {t : ℝ} (ht : t ∈ Icc 0 T) :
    limE V W δ (ρ t) = limE V W δ ρ₀ - ∫ u in Ioc 0 t, limRate V W δ (ρ u) (N u) := by
  have hT0 : 0 ≤ T := ht.1.trans ht.2
  have hρ₀b : ∀ x, |ρ₀ x| ≤ K := fun x => by rw [← h.init]; exact hK 0 ⟨le_rfl, hT0⟩ x
  obtain ⟨C₁, C₂, hC⟩ := exists_epsRate_bound hyp hδ (W := W) (V := V) K (A * K)
  -- the good times
  have hgood := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2)
    (h.ae_isWeakGrad hK0 hK hT0)
  set bnd : ℝ → ℝ := fun u => C₁ * (dirE ρ u).toReal + C₂
  have hbnd : IntegrableOn bnd (Ioc 0 t) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have hfin : ∫⁻ u in Ioc 0 t, dirE ρ u ≠ ⊤ :=
      (lt_of_le_of_lt (lintegral_mono_set (Ioc_subset_Ioc le_rfl ht.2))
        (h.lintegral_dirE_lt_top hK0 hK hT0)).ne
    exact ((integrable_toReal_of_lintegral_ne_top h.measurable_dirE.aemeasurable hfin).const_mul
      C₁).add (integrable_const C₂)
  have hlimR : Tendsto (fun ε => ∫ u in Ioc 0 t, epsRate V W δ ε (ρ u) (N u)) (𝓝[>] 0)
      (𝓝 (∫ u in Ioc 0 t, limRate V W δ (ρ u) (N u))) := by
    refine tendsto_integral_filter_of_dominated_convergence bnd ?_ ?_ hbnd ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      obtain ⟨Φ, hΦm, hΦ⟩ := h.exists_measurable_epsRate hyp hδ hε hK
      refine hΦm.aestronglyMeasurable.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact (hΦ u ⟨hu.1.le, hu.2.trans ht.2⟩).symm
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with u hgu hu
      obtain ⟨g, hg, hg2, -, hgE⟩ := hgu
      have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
      have hE : ∑ j, ∫ x, g x j ^ 2 = (dirE ρ u).toReal := by
        rw [← hgE, ENNReal.toReal_ofReal (Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _)]
      rw [Real.norm_eq_abs]
      have := hC ε hε (ρ u) (h.measurable_section u) (hK u hu') (N u) (fun k => h.measurable_sectionN u k)
        (fun z k => h.abs_N_le hK hu' z k) g hg hg2
      rwa [hE] at this
    · filter_upwards [hgood, ae_restrict_mem measurableSet_Ioc] with u hgu hu
      obtain ⟨g, hg, hg2, -, -⟩ := hgu
      have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
      exact tendsto_epsRate hyp hδ (h.measurable_section u) (hK u hu')
        (fun k => h.measurable_sectionN u k) (fun z k => h.abs_N_le hK hu' z k) hg hg2
  have hL := tendsto_epsE hyp hδ (h.measurable_section t) (hK t ht)
  have hR := (tendsto_epsE hyp hδ h.meas0 hρ₀b).sub hlimR
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (h.eps_identity hyp hδ hε hK0 hK ht).symm

end LinMild

end SharpLSI
