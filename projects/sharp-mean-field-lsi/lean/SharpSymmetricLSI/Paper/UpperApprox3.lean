import SharpSymmetricLSI.Paper.UpperApprox2

/-!
# Smooth approximation of admissible densities, part 3: assembly (Phase 3, lane D; R6)
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem continuous_moll' {ι : Type*} [Fintype ι] (n : ℕ) {f : UnitAddTorus ι → ℝ}
    (hf : Integrable f volume) : Continuous (moll n f) :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp
    (moll_comp_liftT_contDiff n hf).continuous

theorem abs_bForceL_sub_le (hyp : Hyp V W KV KW) {ρ ρ' : Torus d → ℝ} (hρ : Integrable ρ (haar d))
    (hρ' : Integrable ρ' (haar d)) {Cb : ℝ} (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb) (x : Torus d)
    (k : Fin d) :
    |bForceL W ρ x k - bForceL W ρ' x k| ≤ Cb * (∫⁻ y, ‖ρ y - ρ' y‖ₑ ∂haar d).toReal := by
  have hBm : Measurable fun y => bGrad W x y k :=
    (measurable_bGrad hyp (W := W) k).of_uncurry_left
  have hi : ∀ {r : Torus d → ℝ}, Integrable r (haar d) →
      Integrable (fun y => bGrad W x y k * r y) (haar d) := fun {r} hr =>
    (hr.norm.const_mul Cb).mono' (hBm.aestronglyMeasurable.mul hr.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_mul, Real.norm_eq_abs (bGrad W x y k)]
        exact mul_le_mul_of_nonneg_right (hCb x y k) (norm_nonneg _))
  unfold bForceL
  rw [← integral_sub (hi hρ) (hi hρ')]
  refine (abs_integral_le_integral_abs).trans ?_
  have e : ∀ y, |bGrad W x y k * ρ y - bGrad W x y k * ρ' y| ≤ Cb * |ρ y - ρ' y| := fun y => by
    rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _)
  calc ∫ y, |bGrad W x y k * ρ y - bGrad W x y k * ρ' y| ∂haar d ≤ ∫ y, Cb * |ρ y - ρ' y| ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hρ.sub hρ').abs.const_mul Cb) (Eventually.of_forall e)
    _ = Cb * (∫⁻ y, ‖ρ y - ρ' y‖ₑ ∂haar d).toReal := by
        rw [integral_const_mul]
        congr 1
        have := integral_norm_eq_lintegral_enorm (μ := haar d) (hρ.sub hρ').aestronglyMeasurable
        simpa [Real.norm_eq_abs] using this

/-- The mollification norms converge: `∫ |vⱼ|² → ∫ u²` along an a.e.-convergent subsequence. -/
theorem tendsto_moll_sq_norm {ι : Type*} [Fintype ι] [DecidableEq ι] {u : UnitAddTorus ι → ℝ}
    (hu : Integrable u volume) (hu2 : ∫⁻ y, ‖u y‖ₑ ^ 2 ≠ ⊤) {ns : ℕ → ℕ}
    (hae : ∀ᵐ y ∂(volume : Measure (UnitAddTorus ι)),
      Tendsto (fun j => moll (ns j) u y) atTop (𝓝 (u y))) :
    Tendsto (fun j => ∫⁻ y, ‖moll (ns j) u y‖ₑ ^ 2) atTop (𝓝 (∫⁻ y, ‖u y‖ₑ ^ 2)) := by
  have hL2 := L2Tendsto_moll hu hu2 hae
  refine tendsto_of_le_liminf_of_limsup_le ?_ (hL2.limsup_le hu.aemeasurable hu2)
  have hF := lintegral_liminf_le' (μ := volume) (u := atTop)
    (fun j => ((measurable_moll (ns j) hu).enorm.pow_const 2).aemeasurable)
  refine le_trans (le_of_eq ?_) hF
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with y hy
  have h1 := ((ENNReal.continuous_pow 2).tendsto _).comp ((continuous_enorm.tendsto _).comp hy)
  exact h1.liminf_eq.symm

theorem abs_bForceL_le (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) {Cb : ℝ} (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb) (x : Torus d)
    (k : Fin d) : |bForceL W ρ x k| ≤ Cb := by
  have hρi := integrable_of_integral_eq_one' hρ1
  unfold bForceL
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |bGrad W x y k * ρ y| ∂haar d ≤ ∫ y, Cb * ρ y ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hρi.const_mul Cb)
          (Eventually.of_forall fun y => by
            show |bGrad W x y k * ρ y| ≤ Cb * ρ y
            rw [abs_mul, abs_of_nonneg (hρ0 y)]
            exact mul_le_mul_of_nonneg_right (hCb x y k) (hρ0 y))
    _ = Cb := by rw [integral_const_mul, hρ1, mul_one]

theorem lintegral_sqrt_sq_eq {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    ∫⁻ x, ‖Real.sqrt (ρ x)‖ₑ ^ 2 ∂haar d = 1 := by
  have hρi := integrable_of_integral_eq_one' hρ1
  have : ∀ x, ‖Real.sqrt (ρ x)‖ₑ ^ 2 = ENNReal.ofReal (ρ x) := fun x => by
    rw [← ofReal_sq_eq_enorm_sq, Real.sq_sqrt (hρ0 x)]
  simp_rw [this]
  rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1, ENNReal.ofReal_one]

/-- **Smooth approximation of admissible densities with `limsup D ≤ D(ρ)`.** -/
theorem approx_dissipation (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    ∃ ρs : ℕ → Torus d → ℝ, (∀ j, IsSmoothT (ρs j) ∧ (∀ x, 0 < ρs j x) ∧
        ∫ x, ρs j x ∂haar d = 1) ∧
      Tendsto (fun j => ∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d) atTop (𝓝 0) ∧
      (∀ᵐ x ∂haar d, Tendsto (fun j => ρs j x) atTop (𝓝 (ρ x))) ∧
      limsup (fun j => dissipation V W (ρs j)) atTop ≤ dissipation V W ρ := by
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hudef
  have hu0 : ∀ x, 0 ≤ u x := fun x => Real.sqrt_nonneg _
  have hρi : Integrable ρ (haar d) := integrable_of_integral_eq_one' hρ1
  have hu2 : MemLp u 2 (haar d) := hH1.2.1
  have hui : Integrable u (haar d) := hu2.integrable one_le_two
  have hgw : IsWeakGrad u (weakGrad u) := isWeakGrad_weakGrad hH1.1
  set gu := weakGrad u with hgudef
  have hg2 : ∀ k, MemLp (fun y => gu y k) 2 (haar d) := fun k =>
    hH1.2.2.of_le (hgw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hgi : ∀ k, Integrable (fun y => gu y k) (haar d) := fun k => (hg2 k).integrable one_le_two
  have hu2f := memLp_two_lintegral_ne_top hu2
  have hg2f := fun k => memLp_two_lintegral_ne_top (hg2 k)
  have huL2 : ∫⁻ x, ‖u x‖ₑ ^ 2 ∂haar d = 1 := lintegral_sqrt_sq_eq hρ0 hρ1
  obtain ⟨ns, -, hae⟩ := exists_subseq_moll_ae hui hgi
  have haeu : ∀ᵐ y ∂haar d, Tendsto (fun j => moll (ns j) u y) atTop (𝓝 (u y)) :=
    hae.mono fun y hy => hy.1
  have hnorm := tendsto_moll_sq_norm hui hu2f haeu
  rw [huL2] at hnorm
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp
    (hnorm.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ≥0∞) < 1)))
  have hshift : Tendsto (fun j : ℕ => j + J₀) atTop atTop := tendsto_add_atTop_nat J₀
  set v : ℕ → Torus d → ℝ := fun j => moll (ns (j + J₀)) u with hvdef
  set w : ℕ → Torus d → Fin d → ℝ := fun j y k => moll (ns (j + J₀)) (fun z => gu z k) y
    with hwdef
  have hvae : ∀ᵐ y ∂haar d, Tendsto (fun j => v j y) atTop (𝓝 (u y)) :=
    haeu.mono fun y hy => hy.comp hshift
  have hvL2 : L2Tendsto (haar d) v u := by
    have := L2Tendsto_moll hui hu2f haeu
    unfold L2Tendsto at this ⊢
    exact this.comp hshift
  have hwL2 : ∀ k, L2Tendsto (haar d) (fun j y => w j y k) (fun y => gu y k) := fun k => by
    have := L2Tendsto_moll (hgi k) (hg2f k) (hae.mono fun y hy => hy.2 k)
    unfold L2Tendsto at this ⊢
    exact this.comp hshift
  have hvi : ∀ j, Integrable (v j) (haar d) := fun j => integrable_moll _ hui
  have hvc : ∀ j, Continuous (v j) := fun j => continuous_moll' _ hui
  have hwi : ∀ j k, Integrable (fun y => w j y k) (haar d) := fun j k => integrable_moll _ (hgi k)
  have hwc : ∀ j k, Continuous (fun y => w j y k) := fun j k => continuous_moll' _ (hgi k)
  -- the normalizations
  set m : ℕ → ℝ := fun j => (∫⁻ y, ‖v j y‖ₑ ^ 2 ∂haar d).toReal with hmdef
  have hvle : ∀ j, ∫⁻ y, ‖v j y‖ₑ ^ 2 ∂haar d ≤ 1 := fun j => by
    rw [← huL2]; exact lintegral_moll_sq_le _ hui
  have hvgt : ∀ j, 1 / 2 < ∫⁻ y, ‖v j y‖ₑ ^ 2 ∂haar d := fun j => hJ₀ (j + J₀) (by omega)
  have hm : ∀ j, 1 / 2 ≤ m j := fun j => by
    have h1 := hvgt j
    have hne : ∫⁻ y, ‖v j y‖ₑ ^ 2 ∂haar d ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hvle j)
    rw [hmdef]
    have := (ENNReal.toReal_le_toReal (by norm_num) hne).mpr h1.le
    simpa using this
  have hml : Tendsto m atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp (hnorm.comp hshift)
    simp only [ENNReal.toReal_one] at this
    exact this.congr fun j => rfl
  set t : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with htdef
  have ht0 : ∀ j, 0 < t j := fun j => by simp only [htdef]; positivity
  have htl : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set c : ℕ → ℝ := fun j => m j + t j with hcdef
  have hc : ∀ j, 1 / 2 ≤ c j := fun j => by simp only [hcdef]; linarith [hm j, ht0 j]
  have hcpos : ∀ j, 0 < c j := fun j => lt_of_lt_of_le (by norm_num) (hc j)
  have hcl : Tendsto c atTop (𝓝 1) := by simpa using hml.add htl
  set ρs : ℕ → Torus d → ℝ := fun j x => (v j x ^ 2 + t j) / c j with hρsdef
  have hρsc : ∀ j, Continuous (ρs j) := fun j => (((hvc j).pow 2).add continuous_const).div_const _
  have hρs0 : ∀ j x, 0 < ρs j x := fun j x => div_pos (by positivity) (hcpos j)
  have hvint : ∀ j, ∫ x, v j x ^ 2 ∂haar d = m j := fun j => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      ((hvc j).pow 2).aestronglyMeasurable]
    simp_rw [ofReal_sq_eq_enorm_sq]
    rfl
  have hρs1 : ∀ j, ∫ x, ρs j x ∂haar d = 1 := fun j => by
    simp only [hρsdef]
    rw [integral_div, integral_add (f := fun x => v j x ^ 2) (g := fun _ => t j)
      (integrable_of_continuous ((hvc j).pow 2)) (integrable_const _), hvint j]
    have := (hcpos j).ne'
    simp only [hcdef] at this
    simp [hcdef, this]
  have hρss : ∀ j, IsSmoothT (ρs j) := fun j => by
    have h := moll_comp_liftT_contDiff (ns (j + J₀)) hui
    have e : ρs j ∘ liftT = fun x => ((moll (ns (j + J₀)) u ∘ liftT) x ^ 2 + t j) / c j := rfl
    show ContDiff ℝ ∞ (ρs j ∘ liftT)
    rw [e]
    exact ((h.pow 2).add contDiff_const).div_const _
  refine ⟨ρs, fun j => ⟨hρss j, hρs0 j, hρs1 j⟩, ?_⟩
  -- `√ρⱼ → u` in `L²`, `ρⱼ → ρ` in `L¹` and a.e.
  have hsq : ∀ j x, Real.sqrt (ρs j x) = sqrtShift (t j) (v j x) / Real.sqrt (c j) := fun j x => by
    simp only [hρsdef, sqrtShift]
    exact Real.sqrt_div (by positivity) _
  have hsqrtL2 : L2Tendsto (haar d) (fun j x => Real.sqrt (ρs j x)) u := by
    have h := L2Tendsto_sqrt_approx (μ := haar d) hu0 hc (fun j => (ht0 j).le) htl hcl hvL2
      (fun j => (hvc j).measurable.aemeasurable) hui.aemeasurable hu2f
    refine h.of_le fun j x => le_of_eq ?_
    rw [hsq]
  have hsqL2 : ∀ j, ∫⁻ x, ‖Real.sqrt (ρs j x)‖ₑ ^ 2 ∂haar d = 1 := fun j =>
    lintegral_sqrt_sq_eq (fun x => (hρs0 j x).le) (hρs1 j)
  have hL1 : Tendsto (fun j => ∫⁻ x, ‖ρs j x - ρ x‖ₑ ∂haar d) atTop (𝓝 0) := by
    have h := tendsto_lintegral_sq_sub hsqrtL2 ENNReal.one_ne_top (fun j => (hsqL2 j).le)
      huL2.le (fun j => (Real.continuous_sqrt.comp (hρsc j)).measurable.aemeasurable)
      hui.aemeasurable
    refine h.congr fun j => ?_
    refine lintegral_congr fun x => ?_
    rw [Real.sq_sqrt (hρs0 j x).le, hudef, Real.sq_sqrt (hρ0 x)]
  have hρsae : ∀ᵐ x ∂haar d, Tendsto (fun j => ρs j x) atTop (𝓝 (ρ x)) := by
    filter_upwards [hvae] with x hx
    have := ((hx.pow 2).add htl).div hcl one_ne_zero
    rw [add_zero, div_one, hudef, Real.sq_sqrt (hρ0 x)] at this
    exact this
  refine ⟨hL1, hρsae, ?_⟩
  -- constants
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  have hgz : ∀ᵐ y ∂haar d, u y = 0 → ∀ k, gu y k = 0 := ae_grad_eq_zero_of_eq_zero hgw hui hgi
  have hρsi : ∀ j, Integrable (ρs j) (haar d) := fun j => integrable_of_continuous (hρsc j)
  -- weak gradients of `√ρⱼ`
  set G : ℕ → Torus d → Fin d → ℝ := fun j x k =>
    (1 / Real.sqrt (c j) * (v j x / Real.sqrt (v j x ^ 2 + t j))) * w j x k with hGdef
  have hG : ∀ j, IsWeakGrad (fun x => Real.sqrt (ρs j x)) (G j) := fun j => by
    have hvw : IsWeakGrad (v j) (w j) := isWeakGrad_moll hgw hui _
    have hd : ∀ s, |deriv (sqrtShift (t j)) s| ≤ 1 := fun s => by
      rw [deriv_sqrtShift (ht0 j)]; exact abs_div_sqrtShift_le (ht0 j) s
    have h1 := isWeakGrad_comp hvw (hvi j) (hwi j) ((contDiff_sqrtShift (ht0 j)).of_le (by simp)) hd
    have h2 := h1.cmul (1 / Real.sqrt (c j))
    have e1 : (fun x => 1 / Real.sqrt (c j) * sqrtShift (t j) (v j x)) =
        fun x => Real.sqrt (ρs j x) := funext fun x => by rw [hsq]; ring
    have e2 : (fun x k => 1 / Real.sqrt (c j) * (deriv (sqrtShift (t j)) (v j x) * w j x k)) =
        G j := funext fun x => funext fun k => by simp only [hGdef, deriv_sqrtShift (ht0 j)]; ring
    rw [e1, e2] at h2; exact h2
  have hH1s : ∀ j, MemH1 (haar d) (fun x => Real.sqrt (ρs j x)) := fun j => by
    obtain ⟨B1, hB1⟩ := exists_bound_of_continuous (Real.continuous_sqrt.comp (hρsc j))
    choose B hB using fun k => exists_bound_of_continuous (hwc j k)
    set Bw := ∑ k, |B k|
    have hBw : ∀ y k, |w j y k| ≤ Bw := fun y k => (hB k y).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)))
    have hGb : ∀ y k, |G j y k| ≤ 2 * Bw := fun y k => by
      simp only [hGdef, abs_mul]
      have h1 := abs_inv_sqrt_le_two (hc j)
      have h2 := abs_div_sqrtShift_le (ht0 j) (v j y)
      have h3 := hBw y k
      have : |1 / Real.sqrt (c j)| * |v j y / Real.sqrt (v j y ^ 2 + t j)| ≤ 2 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      calc |1 / Real.sqrt (c j)| * |v j y / Real.sqrt (v j y ^ 2 + t j)| * |w j y k|
          ≤ (2 * 1) * Bw := mul_le_mul this h3 (abs_nonneg _) (by norm_num)
        _ = 2 * Bw := by ring
    refine ⟨⟨_, hG j⟩, MemLp.of_bound (Real.continuous_sqrt.comp (hρsc j)).aestronglyMeasurable B1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB1 x), ?_⟩
    refine MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hG j⟩).aestronglyMeasurable_sqNorm)
      (Real.sqrt (Fintype.card (Fin d) * (2 * Bw) ^ 2)) ?_
    filter_upwards [weakGrad_ae_eq (hG j)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
    refine Real.sqrt_le_sqrt ?_
    unfold sqNorm
    calc ∑ k, G j x k ^ 2 ≤ ∑ _k : Fin d, (2 * Bw) ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hGb x k) 2
      _ = _ := by simp
  rw [dissipation_eq_of hyp hρi hH1 hgw]
  simp_rw [fun j => dissipation_eq_of hyp (hρsi j) (hH1s j) (hG j)]
  -- componentwise `L²` convergence
  have hΨ : ∀ k, L2Tendsto (haar d)
      (fun j x => 2 * G j x k + Real.sqrt (ρs j x) * (lipGrad V x k + bForceL W (ρs j) x k))
      (fun x => 2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k)) := fun k => by
    have h1 : L2Tendsto (haar d) (fun j x => G j x k) (fun x => gu x k) :=
      L2Tendsto_grad_approx hc ht0 htl hcl hu0 hvae (hgz.mono fun y hy h0 => hy h0 k) (hwL2 k)
        (fun j => (hvc j).measurable.aemeasurable) (fun j => (hwc j k).measurable.aemeasurable)
        (hgw.aestronglyMeasurable_grad k).aemeasurable (hg2f k)
    have hmb : ∀ j x, |lipGrad V x k + bForceL W (ρs j) x k| ≤ LV + Cb := fun j x =>
      (abs_add_le _ _).trans (add_le_add (hLV x k)
        (abs_bForceL_le hyp (fun x => (hρs0 j x).le) (hρs1 j) hCb x k))
    have hmb0 : ∀ x, |lipGrad V x k + bForceL W ρ x k| ≤ LV + Cb := fun x =>
      (abs_add_le _ _).trans (add_le_add (hLV x k) (abs_bForceL_le hyp hρ0 hρ1 hCb x k))
    have hmm : ∀ j, Measurable fun x => lipGrad V x k + bForceL W (ρs j) x k := fun j =>
      (measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp (hρsi j) k)
    have hmm0 : Measurable fun x => lipGrad V x k + bForceL W ρ x k :=
      (measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp hρi k)
    have hez : Tendsto (fun j => Cb * (∫⁻ y, ‖ρs j y - ρ y‖ₑ ∂haar d).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1).const_mul Cb
      simpa using this
    have h2 := L2Tendsto.mul_bdd (μ := haar d)
      (m := fun j x => lipGrad V x k + bForceL W (ρs j) x k)
      (m₀ := fun x => lipGrad V x k + bForceL W ρ x k) (M := LV + Cb) hsqrtL2 hmb hmb0
      (fun j => (hmm j).aemeasurable.mul
        ((Real.continuous_sqrt.comp (hρsc j)).measurable.aemeasurable.sub hui.aemeasurable))
      (fun j => ((hmm j).sub hmm0).aemeasurable.mul hui.aemeasurable)
      (Eventually.of_forall fun x => by
        have hb : ∀ j, |((lipGrad V x k + bForceL W (ρs j) x k) -
            (lipGrad V x k + bForceL W ρ x k)) * u x| ≤
            Cb * (∫⁻ y, ‖ρs j y - ρ y‖ₑ ∂haar d).toReal * |u x| := fun j => by
          rw [abs_mul, add_sub_add_left_eq_sub]
          exact mul_le_mul_of_nonneg_right
            (abs_bForceL_sub_le hyp (hρsi j) hρi hCb x k) (abs_nonneg _)
        have hz := hez.mul_const |u x|
        rw [zero_mul] at hz
        exact squeeze_zero_norm (fun j => by rw [Real.norm_eq_abs]; exact hb j) hz) hu2f
    have hGm : ∀ j, AEMeasurable (fun x => 2 * G j x k - 2 * gu x k) (haar d) := fun j =>
      (((hG j).aestronglyMeasurable_grad k).aemeasurable.const_mul 2).sub
        ((hgw.aestronglyMeasurable_grad k).aemeasurable.const_mul 2)
    have h3 := (h1.const_mul 2).add h2 hGm
    refine h3.of_le fun j x => le_of_eq ?_
    congr 2; ring
  have hΨm : ∀ k, AEMeasurable (fun x => 2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k))
      (haar d) := fun k =>
    ((hgw.aestronglyMeasurable_grad k).aemeasurable.const_mul 2).add (hui.aemeasurable.mul
      ((measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp hρi k)).aemeasurable)
  have hΨf : ∀ k, ∫⁻ x, ‖2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2 ∂haar d ≠ ⊤ :=
    fun k => by
    have hb : ∀ x, ‖2 * gu x k + u x * (lipGrad V x k + bForceL W ρ x k)‖ₑ ^ 2 ≤
        2 * (‖(2 : ℝ)‖ₑ ^ 2 * ‖gu x k‖ₑ ^ 2) + 2 * (‖LV + Cb‖ₑ ^ 2 * ‖u x‖ₑ ^ 2) := fun x => by
      refine (enorm_add_sq_le _ _).trans ?_
      rw [enorm_mul, enorm_mul, mul_pow, mul_pow, mul_comm (‖u x‖ₑ ^ 2)]
      gcongr
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      exact ((abs_add_le _ _).trans (add_le_add (hLV x k) (abs_bForceL_le hyp hρ0 hρ1 hCb x k))).trans
        (le_abs_self _)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hb)
    rw [lintegral_add_left' (((((hgw.aestronglyMeasurable_grad k).enorm).pow_const 2).const_mul _).const_mul 2),
      lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by simp)
      (hg2f k)), ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top (by simp) hu2f)⟩
  exact L2Tendsto.limsup_le_sum Finset.univ (fun k _ => hΨ k) (fun k _ => hΨm k) (fun k _ => hΨf k)

end SharpLSI
