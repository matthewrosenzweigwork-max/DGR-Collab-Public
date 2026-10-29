import DGPS.Model.SpeciesRate
import DGPS.Model.ScalarRate

/-!
# Square root mixture and score decompositions (LIP003)

Frozen statement LIP003: for a finite species family with roots `u_s`, weights `θ_s` and
barycenter `ρ̄ = ∑ θ_s u_s²`, `h = √ρ̄ ∈ H¹`; `∇h = (∑ θ_s u_s ∇u_s)/h` on `{h > 0}` and all `u_s`,
`∇u_s` vanish a.e. on `{h = 0}`; with the score `σ = 2 ∇h / h` on `{h > 0}` (zero elsewhere) the
score differences `2 ∇u_s - u_s σ` lie in `L²`, and
`G_θ = G(ρ̄) + ∑ θ_s H(ρ_s | ρ̄)`, `D_θ = D(ρ̄) + ∑ θ_s I_s`, `I_s = ∫ |2 ∇u_s - u_s σ|²`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.SpeciesFamily

variable {d : ℕ}

/-- The score `σ = 2 ∇h / h` of the barycenter, zero off `{h > 0}`. -/
noncomputable def score (F : SpeciesFamily d) (x : Torus d) : Tangent d :=
  if 0 < (barycenter F).sqrt x then
    (2 / (barycenter F).sqrt x) • weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem x
  else 0

/-- The score difference `2 ∇u_s - u_s σ`. -/
noncomputable def scoreDifference (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    Tangent d :=
  (2 : ℝ) • F.sqrtGradient s x - (F.density s).sqrt x • F.score x

/-- The information `I_s = ∫ |2 ∇u_s - u_s σ|² dm ∈ [0, ∞]`. -/
noncomputable def scoreInformation (F : SpeciesFamily d) (s : Fin F.count) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖F.scoreDifference s x‖ ^ 2) ∂haar d

/-- The canonical weak gradient of the barycenter root `h`. -/
noncomputable def barycenterWeakGrad (F : SpeciesFamily d) : Torus d → Tangent d :=
  weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem

theorem isWeakGradient_barycenterWeakGrad (F : SpeciesFamily d) :
    IsWeakGradient (barycenter F).sqrt F.barycenterWeakGrad :=
  isWeakGradient_weakGradient _

theorem barycenterWeakGrad_ae_eq (F : SpeciesFamily d) :
    F.barycenterWeakGrad =ᵐ[haar d] F.barycenterGrad :=
  F.isWeakGradient_barycenterWeakGrad.ae_eq F.isWeakGradient_barycenterSqrt

theorem barycenter_sqrt_nonneg (F : SpeciesFamily d) (x : Torus d) :
    0 ≤ (barycenter F).sqrt x := F.barycenterSqrt_nonneg x

theorem weight_mul_sq_le (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    F.weight s * (F.density s).sqrt x ^ 2 ≤ ((barycenter F).sqrt x) ^ 2 := by
  have h1 : F.weight s * (F.density s).sqrt x ^ 2 ≤ F.barycenterDensity x :=
    Finset.single_le_sum (f := fun s => F.weight s * (F.density s).sqrt x ^ 2)
      (fun i _ => mul_nonneg (F.weight_nonneg i) (sq_nonneg _)) (Finset.mem_univ s)
  exact h1.trans_eq (F.barycenterSqrt_sq x).symm

theorem sqrt_eq_zero_of_barycenter_eq_zero (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d)
    (hx : (barycenter F).sqrt x = 0) : (F.density s).sqrt x = 0 := by
  have h := F.weight_mul_sq_le s x
  rw [hx] at h
  have hθ := F.weight_pos s
  have h0 : (F.density s).sqrt x ^ 2 ≤ 0 := by
    by_contra hc
    have hc := lt_of_not_ge hc
    have := mul_pos hθ hc
    simp at h
    linarith
  exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (sq_nonneg _))

theorem sqrt_weight_mul_abs_le (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    Real.sqrt (F.weight s) * |(F.density s).sqrt x| ≤ (barycenter F).sqrt x := by
  have hθ := F.weight_pos s
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hθ.le]
  exact Real.sqrt_le_sqrt (F.weight_mul_sq_le s x) |>.trans_eq
    (Real.sqrt_sq (F.barycenter_sqrt_nonneg x))

theorem barycenterWeakGrad_zero_ae (F : SpeciesFamily d) :
    ∀ᵐ x ∂haar d, (barycenter F).sqrt x = 0 → F.barycenterWeakGrad x = 0 := by
  filter_upwards [F.barycenterWeakGrad_ae_eq] with x hx h0
  rw [hx]
  exact (barycenter_gradient F).2.2.1 x h0

theorem sqrtGradient_zero_ae (F : SpeciesFamily d) :
    ∀ᵐ x ∂haar d, (barycenter F).sqrt x = 0 → ∀ s, F.sqrtGradient s x = 0 := by
  have h : ∀ s, ∀ᵐ x ∂haar d, (F.density s).sqrt x = 0 → F.sqrtGradient s x = 0 :=
    fun s => gradient_zero_on_zero_set (F.isWeakGradient_sqrtGradient s)
  filter_upwards [ae_all_iff.2 h] with x hx h0 s
  exact hx s (F.sqrt_eq_zero_of_barycenter_eq_zero s x h0)

theorem score_eq (F : SpeciesFamily d) (x : Torus d) :
    F.score x = (2 * ((barycenter F).sqrt x)⁻¹) • F.barycenterWeakGrad x := by
  unfold score barycenterWeakGrad
  split_ifs with h
  · rw [div_eq_mul_inv]
  · have : (barycenter F).sqrt x = 0 :=
      le_antisymm (not_lt.1 h) (F.barycenter_sqrt_nonneg x)
    simp [this]

theorem two_smul_grad_eq_ae (F : SpeciesFamily d) :
    ∀ᵐ x ∂haar d, (2 : ℝ) • F.barycenterWeakGrad x = (barycenter F).sqrt x • F.score x := by
  filter_upwards [F.barycenterWeakGrad_zero_ae] with x hx
  rw [F.score_eq x, smul_smul]
  by_cases h0 : (barycenter F).sqrt x = 0
  · simp [h0, hx h0]
  · rw [mul_comm ((barycenter F).sqrt x), mul_assoc, inv_mul_cancel₀ h0, mul_one]

theorem sum_smul_grad_ae (F : SpeciesFamily d) :
    ∀ᵐ x ∂haar d, ∑ s, F.weight s • (F.density s).sqrt x • F.sqrtGradient s x
      = (barycenter F).sqrt x • F.barycenterWeakGrad x := by
  filter_upwards [F.barycenterWeakGrad_ae_eq, F.sqrtGradient_zero_ae] with x hx hz
  rw [hx]
  by_cases h0 : (barycenter F).sqrt x = 0
  · rw [h0, zero_smul]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [hz h0 s]; simp
  · unfold barycenterGrad
    show _ = F.barycenterSqrt x • (F.barycenterSqrt x)⁻¹ • _
    have h0' : F.barycenterSqrt x ≠ 0 := h0
    rw [smul_smul, mul_inv_cancel₀ h0', one_smul]

/-- Pointwise expansion of the weighted square with vanishing cross term. -/
theorem sum_mul_norm_add_smul_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (θ u : Fin n → ℝ) (w : Fin n → E) (v : E)
    (hc : ∑ s, θ s • u s • w s = 0) :
    ∑ s, θ s * ‖w s + u s • v‖ ^ 2
      = ∑ s, θ s * ‖w s‖ ^ 2 + (∑ s, θ s * u s ^ 2) * ‖v‖ ^ 2 := by
  have h1 : ∑ s, θ s * (u s * inner ℝ (w s) v) = 0 := by
    have := congrArg (fun z => inner ℝ z v) hc
    simp only [sum_inner, inner_smul_left, inner_zero_left, conj_trivial] at this
    rw [← this]
  have h2 : ∀ s, θ s * ‖w s + u s • v‖ ^ 2
      = θ s * ‖w s‖ ^ 2 + 2 * (θ s * (u s * inner ℝ (w s) v)) + θ s * u s ^ 2 * ‖v‖ ^ 2 := by
    intro s
    rw [norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, Finset.sum_mul]
  ring

end DGPS.SpeciesFamily

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem aestronglyMeasurable_sqrt (F : SpeciesFamily d) (s : Fin F.count) :
    AEStronglyMeasurable (F.density s).sqrt (haar d) :=
  (F.density s).memLp_sqrt.aestronglyMeasurable

theorem aestronglyMeasurable_sqrtGradient (F : SpeciesFamily d) (s : Fin F.count) :
    AEStronglyMeasurable (F.sqrtGradient s) (haar d) :=
  (F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable

theorem aestronglyMeasurable_barycenterWeakGrad (F : SpeciesFamily d) :
    AEStronglyMeasurable F.barycenterWeakGrad (haar d) :=
  F.isWeakGradient_barycenterWeakGrad.memLp_grad.aestronglyMeasurable

theorem aestronglyMeasurable_score (F : SpeciesFamily d) :
    AEStronglyMeasurable F.score (haar d) := by
  have hh : AEStronglyMeasurable (barycenter F).sqrt (haar d) :=
    (barycenter F).memLp_sqrt.aestronglyMeasurable
  have : F.score = fun x => (2 * ((barycenter F).sqrt x)⁻¹) • F.barycenterWeakGrad x :=
    funext F.score_eq
  rw [this]
  exact ((hh.aemeasurable.inv.const_mul 2).aestronglyMeasurable).smul
    F.aestronglyMeasurable_barycenterWeakGrad

theorem aestronglyMeasurable_scoreDifference (F : SpeciesFamily d) (s : Fin F.count) :
    AEStronglyMeasurable (F.scoreDifference s) (haar d) := by
  show AEStronglyMeasurable
    (fun x => (2 : ℝ) • F.sqrtGradient s x - (F.density s).sqrt x • F.score x) (haar d)
  exact ((F.aestronglyMeasurable_sqrtGradient s).const_smul (2 : ℝ)).sub
    ((F.aestronglyMeasurable_sqrt s).smul F.aestronglyMeasurable_score)

theorem sum_smul_scoreDifference_ae (F : SpeciesFamily d) :
    ∀ᵐ x ∂haar d, ∑ s, F.weight s • (F.density s).sqrt x • F.scoreDifference s x = 0 := by
  filter_upwards [F.sum_smul_grad_ae, F.two_smul_grad_eq_ae] with x h1 h2
  have e : ∑ s, F.weight s • (F.density s).sqrt x • F.scoreDifference s x
      = (2 : ℝ) • ∑ s, F.weight s • (F.density s).sqrt x • F.sqrtGradient s x
        - (∑ s, F.weight s * (F.density s).sqrt x ^ 2) • F.score x := by
    rw [Finset.smul_sum, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold scoreDifference
    module
  have hs : ∑ s, F.weight s * (F.density s).sqrt x ^ 2 = (barycenter F).sqrt x ^ 2 :=
    (F.barycenterSqrt_sq x).symm
  rw [e, h1, hs, smul_comm (2 : ℝ), h2, ← mul_smul, ← pow_two, sub_self]

theorem memLp_scoreDifference (F : SpeciesFamily d) (s : Fin F.count) :
    MemLp (F.scoreDifference s) 2 (haar d) := by
  have hg := (F.isWeakGradient_sqrtGradient s).memLp_grad
  have hG := F.isWeakGradient_barycenterWeakGrad.memLp_grad
  have hθ := F.weight_pos s
  have hsθ : 0 < Real.sqrt (F.weight s) := Real.sqrt_pos.2 hθ
  have h2 : MemLp (fun x => (F.density s).sqrt x • F.score x) 2 (haar d) := by
    refine hG.of_le_mul (c := 2 * (Real.sqrt (F.weight s))⁻¹)
      ((F.aestronglyMeasurable_sqrt s).smul F.aestronglyMeasurable_score)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [F.score_eq x, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hh := F.barycenter_sqrt_nonneg x
    have hb := F.sqrt_weight_mul_abs_le s x
    set h := (barycenter F).sqrt x
    set u := (F.density s).sqrt x
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * h⁻¹), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (F.barycenterWeakGrad x))
    rcases hh.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · calc |u| * (2 * h⁻¹) = 2 * (|u| * h⁻¹) := by ring
        _ ≤ 2 * (Real.sqrt (F.weight s))⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [← div_eq_mul_inv, div_le_iff₀ h0, inv_mul_eq_div, le_div_iff₀ hsθ]
          nlinarith
  exact (hg.const_smul (2 : ℝ)).sub h2

theorem integrable_sq_norm_scoreDifference (F : SpeciesFamily d) (s : Fin F.count) :
    Integrable (fun x => ‖F.scoreDifference s x‖ ^ 2) (haar d) :=
  (memLp_two_iff_integrable_sq_norm (F.aestronglyMeasurable_scoreDifference s)).1
    (F.memLp_scoreDifference s)

theorem scoreInformation_ne_top (F : SpeciesFamily d) (s : Fin F.count) :
    F.scoreInformation s ≠ ⊤ ∧
      (F.scoreInformation s).toReal = ∫ x, ‖F.scoreDifference s x‖ ^ 2 ∂haar d := by
  have h : F.scoreInformation s
      = ENNReal.ofReal (∫ x, ‖F.scoreDifference s x‖ ^ 2 ∂haar d) := by
    unfold scoreInformation
    exact (ofReal_integral_eq_lintegral_ofReal (F.integrable_sq_norm_scoreDifference s)
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  rw [h]
  exact ⟨ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)⟩

end DGPS.SpeciesFamily

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem sum_ofReal_mul_ofReal {n : ℕ} (θ q : Fin n → ℝ) (hθ : ∀ s, 0 ≤ θ s) (hq : ∀ s, 0 ≤ q s) :
    ∑ s, ENNReal.ofReal (θ s) * ENNReal.ofReal (q s) = ENNReal.ofReal (∑ s, θ s * q s) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (hθ s) (hq s)]
  exact Finset.sum_congr rfl fun s _ => (ENNReal.ofReal_mul (hθ s)).symm

theorem aemeasurable_ofReal_sq_norm {f : Torus d → Tangent d}
    (hf : AEStronglyMeasurable f (haar d)) :
    AEMeasurable (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) (haar d) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (hf.norm.aemeasurable.pow_const 2)

/-- DEF015 / LIP003: `D_θ = D(ρ̄) + ∑ θ_s I_s` in `ℝ≥0∞`. -/
theorem speciesDissipation_decomposition (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) :
    speciesDissipation A b F = scalarDissipation A b (barycenter F) +
      ∑ s, ENNReal.ofReal (F.weight s) * F.scoreInformation s := by
  have hc : AEStronglyMeasurable (b.force (barycenter F)) (haar d) :=
    (b.measurable_force (barycenter F)).aestronglyMeasurable
  have ha : ∀ s, AEStronglyMeasurable
      (fun x => (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x)
      (haar d) := fun s =>
    ((F.aestronglyMeasurable_sqrtGradient s).const_smul (2 : ℝ)).add
      ((F.aestronglyMeasurable_sqrt s).smul hc)
  have hscore : AEStronglyMeasurable (scalarScore A b (barycenter F)) (haar d) :=
    ((F.aestronglyMeasurable_barycenterWeakGrad).const_smul (2 : ℝ)).add
      (((barycenter F).memLp_sqrt.aestronglyMeasurable).smul hc)
  have hL : speciesDissipation A b F = ∫⁻ x, ∑ s, ENNReal.ofReal (F.weight s) *
      ENNReal.ofReal (‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2) ∂haar d := by
    rw [lintegral_finsetSum' _ fun s _ => (aemeasurable_ofReal_sq_norm (ha s)).const_mul _]
    unfold speciesDissipation
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hR : ∑ s, ENNReal.ofReal (F.weight s) * F.scoreInformation s
      = ∫⁻ x, ∑ s, ENNReal.ofReal (F.weight s) *
        ENNReal.ofReal (‖F.scoreDifference s x‖ ^ 2) ∂haar d := by
    rw [lintegral_finsetSum' _ fun s _ =>
      (aemeasurable_ofReal_sq_norm (F.aestronglyMeasurable_scoreDifference s)).const_mul _]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hL, hR]
  unfold scalarDissipation
  rw [← lintegral_add_left' (aemeasurable_ofReal_sq_norm hscore)]
  refine lintegral_congr_ae ?_
  filter_upwards [F.sum_smul_scoreDifference_ae, F.two_smul_grad_eq_ae] with x hx h2
  set c := b.force (barycenter F) x with hcdef
  set h := (barycenter F).sqrt x with hh
  have hθ : ∀ s, 0 ≤ F.weight s := F.weight_nonneg
  have hsq : ∀ s, 0 ≤ ‖F.scoreDifference s x‖ ^ 2 := fun s => sq_nonneg _
  have key := sum_mul_norm_add_smul_sq F.weight (fun s => (F.density s).sqrt x)
    (fun s => F.scoreDifference s x) (F.score x + c) hx
  have hform : ∀ s, (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c
      = F.scoreDifference s x + (F.density s).sqrt x • (F.score x + c) := by
    intro s
    unfold scoreDifference
    module
  have hss : scalarScore A b (barycenter F) x = h • (F.score x + c) := by
    show (2 : ℝ) • F.barycenterWeakGrad x + h • c = _
    rw [h2, smul_add]
  have hnorm : ‖scalarScore A b (barycenter F) x‖ ^ 2 = h ^ 2 * ‖F.score x + c‖ ^ 2 := by
    rw [hss, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hbar : ∑ s, F.weight s * (F.density s).sqrt x ^ 2 = h ^ 2 :=
    (F.barycenterSqrt_sq x).symm
  simp_rw [hform]
  rw [sum_ofReal_mul_ofReal _ _ hθ (fun s => sq_nonneg _),
    sum_ofReal_mul_ofReal _ _ hθ hsq, key, hbar, hnorm,
    ENNReal.ofReal_add (Finset.sum_nonneg fun s _ => mul_nonneg (hθ s) (hsq s))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)), add_comm]

end DGPS.SpeciesFamily

namespace DGPS.SpeciesFamily

variable {d : ℕ}

/-- The density ratio `ρ_s / ρ̄` (zero where `ρ̄ = 0`, by `div_zero`). -/
noncomputable def densityRatio (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) : ℝ :=
  (F.density s).density x / (barycenter F).density x

theorem weight_mul_density_le (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    F.weight s * (F.density s).density x ≤ (barycenter F).density x :=
  F.weight_mul_sq_le s x

theorem density_eq_zero_of_barycenter (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d)
    (h : (barycenter F).density x = 0) : (F.density s).density x = 0 := by
  have h1 := F.weight_mul_density_le s x
  rw [h] at h1
  have hθ := F.weight_pos s
  have h2 := (F.density s).density_nonneg x
  by_contra hne
  have : 0 < (F.density s).density x := lt_of_le_of_ne h2 (Ne.symm hne)
  have := mul_pos hθ this
  linarith

theorem densityRatio_nonneg (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    0 ≤ F.densityRatio s x :=
  div_nonneg ((F.density s).density_nonneg x) ((barycenter F).density_nonneg x)

theorem barycenter_mul_densityRatio (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    (barycenter F).density x * F.densityRatio s x = (F.density s).density x := by
  unfold densityRatio
  by_cases h : (barycenter F).density x = 0
  · rw [h, F.density_eq_zero_of_barycenter s x h]; simp
  · field_simp

theorem aemeasurable_density (ρ : AbsoluteDensity d) :
    AEMeasurable ρ.density (haar d) :=
  ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2

theorem aemeasurable_densityRatio (F : SpeciesFamily d) (s : Fin F.count) :
    AEMeasurable (F.densityRatio s) (haar d) :=
  (aemeasurable_density (F.density s)).div (aemeasurable_density (barycenter F))

theorem densityMeasure_eq_withDensity_ratio (F : SpeciesFamily d) (s : Fin F.count) :
    (densityMeasure (F.density s) : Measure (Torus d)) =
      (densityMeasure (barycenter F) : Measure (Torus d)).withDensity
        (fun x => ENNReal.ofReal (F.densityRatio s x)) := by
  rw [densityMeasure_coe, densityMeasure_coe]
  have hf : AEMeasurable (fun x => ENNReal.ofReal ((barycenter F).sqrt x ^ 2)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density (barycenter F))
  have hg : AEMeasurable (fun x => ENNReal.ofReal (F.densityRatio s x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (F.aemeasurable_densityRatio s)
  rw [← withDensity_mul₀ hf hg]
  congr 1
  funext x
  show ENNReal.ofReal ((F.density s).density x) =
    ENNReal.ofReal ((barycenter F).density x) * ENNReal.ofReal (F.densityRatio s x)
  rw [← ENNReal.ofReal_mul ((barycenter F).density_nonneg x), F.barycenter_mul_densityRatio]

theorem integrable_density_mul_log_barycenter (F : SpeciesFamily d) (s : Fin F.count) :
    Integrable (fun x => (F.density s).density x * Real.log ((barycenter F).density x))
      (haar d) := by
  have hb := (absoluteDensity_entropy_finite (barycenter F)).2.1
  have hθ := F.weight_pos s
  refine (hb.const_mul (F.weight s)⁻¹).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (aemeasurable_density (F.density s)).aestronglyMeasurable.mul
      (aemeasurable_density (barycenter F)).log.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((F.density s).density_nonneg x),
      abs_mul, abs_of_nonneg ((barycenter F).density_nonneg x)] 
    have h1 : (F.density s).density x ≤ (F.weight s)⁻¹ * (barycenter F).density x := by
      rw [inv_mul_eq_div, le_div_iff₀ hθ, mul_comm]
      exact F.weight_mul_density_le s x
    calc (F.density s).density x * |Real.log ((barycenter F).density x)|
        ≤ ((F.weight s)⁻¹ * (barycenter F).density x) * |Real.log ((barycenter F).density x)| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = _ := by ring

end DGPS.SpeciesFamily

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem densityMeasure_barycenter_eq (F : SpeciesFamily d) :
    (densityMeasure (barycenter F) : Measure (Torus d)) =
      (haar d).withDensity (ENNReal.ofReal ∘ (barycenter F).density) := rfl

theorem integral_densityRatio (F : SpeciesFamily d) (s : Fin F.count) :
    ∫ x, F.densityRatio s x ∂(densityMeasure (barycenter F) : Measure (Torus d)) = 1 := by
  rw [densityMeasure_barycenter_eq,
    integral_withDensity_eq_integral_toReal_smul₀
      (ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density (barycenter F)))
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have : ∀ x, ((ENNReal.ofReal ∘ (barycenter F).density) x).toReal • F.densityRatio s x
      = (F.density s).density x := fun x => by
    show (ENNReal.ofReal ((barycenter F).density x)).toReal • _ = _
    rw [ENNReal.toReal_ofReal ((barycenter F).density_nonneg x), smul_eq_mul,
      F.barycenter_mul_densityRatio]
  simp_rw [this]
  exact (F.density s).integral_density

theorem pointwise_entropy_kernel (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    (barycenter F).density x *
        (F.densityRatio s x * Real.log (F.densityRatio s x) - F.densityRatio s x + 1) =
      (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x + (barycenter F).density x := by
  by_cases h : (barycenter F).density x = 0
  · rw [h, F.density_eq_zero_of_barycenter s x h]; simp
  · have hpos : 0 < (barycenter F).density x :=
      lt_of_le_of_ne ((barycenter F).density_nonneg x) (Ne.symm h)
    have hr := F.barycenter_mul_densityRatio s x
    by_cases h0 : (F.density s).density x = 0
    · have : F.densityRatio s x = 0 := by
        rcases mul_eq_zero.mp (hr.trans h0) with h1 | h1
        · exact absurd h1 h
        · exact h1
      rw [this, h0]; simp
    · have hr' : F.densityRatio s x = (F.density s).density x / (barycenter F).density x := rfl
      have hlog : Real.log (F.densityRatio s x) =
          Real.log ((F.density s).density x) - Real.log ((barycenter F).density x) := by
        rw [hr']; exact Real.log_div h0 h
      rw [hlog]
      have : (barycenter F).density x * F.densityRatio s x = (F.density s).density x := hr
      linear_combination (Real.log ((F.density s).density x) -
        Real.log ((barycenter F).density x) - 1) * this

theorem kernel_nonneg (F : SpeciesFamily d) (s : Fin F.count) (x : Torus d) :
    0 ≤ (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x + (barycenter F).density x := by
  rw [← F.pointwise_entropy_kernel s x]
  exact mul_nonneg ((barycenter F).density_nonneg x)
    (self_mul_log_sub_add_one_nonneg (F.densityRatio_nonneg s x))

theorem relativeEntropy_species (F : SpeciesFamily d) (s : Fin F.count) :
    (densityMeasure (F.density s) : Measure (Torus d)) ≪
        (densityMeasure (barycenter F) : Measure (Torus d)) ∧
    relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d)) ≠ ⊤ ∧
    (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal =
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal
        - ∫ x, (F.density s).density x * Real.log ((barycenter F).density x) ∂haar d := by
  have hac : (densityMeasure (F.density s) : Measure (Torus d)) ≪
      (densityMeasure (barycenter F) : Measure (Torus d)) := by
    rw [densityMeasure_eq_withDensity_ratio]; exact withDensity_absolutelyContinuous _ _
  refine ⟨hac, ?_⟩
  have hPm : (densityMeasure (barycenter F) : Measure (Torus d)) ≪ haar d := by
    rw [densityMeasure_barycenter_eq]; exact withDensity_absolutelyContinuous _ _
  have hH : relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (densityMeasure (barycenter F) : Measure (Torus d)) =
      ENNReal.ofReal (∫ x, (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x + (barycenter F).density x ∂haar d) := by
    rw [densityMeasure_eq_withDensity_ratio F s,
      relativeEntropy_withDensity (Filter.Eventually.of_forall (F.densityRatio_nonneg s))
        ((F.aemeasurable_densityRatio s).mono_ac hPm),
      entropy_mass_one (F.integral_densityRatio s), densityMeasure_barycenter_eq,
      lintegral_withDensity_eq_lintegral_mul₀
        (ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density (barycenter F)))
        (by
          have := F.aemeasurable_densityRatio s
          exact ENNReal.measurable_ofReal.comp_aemeasurable
            ((this.mul (this.log)).sub this |>.add_const 1)),
      ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      funext x
      show ENNReal.ofReal ((barycenter F).density x) * ENNReal.ofReal _ = _
      rw [← ENNReal.ofReal_mul ((barycenter F).density_nonneg x), F.pointwise_entropy_kernel s x]
    · have h1 := (absoluteDensity_entropy_finite (F.density s)).1
      have h2 := F.integrable_density_mul_log_barycenter s
      exact ((h1.sub h2).sub (F.density s).integrable_density).add
        (barycenter F).integrable_density
    · exact Filter.Eventually.of_forall (F.kernel_nonneg s)
  have h1 := (absoluteDensity_entropy_finite (F.density s))
  have h2 := F.integrable_density_mul_log_barycenter s
  have hint : ∫ x, (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x + (barycenter F).density x ∂haar d =
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal
        - ∫ x, (F.density s).density x * Real.log ((barycenter F).density x) ∂haar d := by
    have i1 : Integrable (fun x => (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)) (haar d) := h1.1.sub h2
    have i2 : Integrable (fun x => (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x) (haar d) := i1.sub (F.density s).integrable_density
    rw [integral_add i2 (barycenter F).integrable_density,
      integral_sub i1 (F.density s).integrable_density, integral_sub h1.1 h2,
      (F.density s).integral_density, (barycenter F).integral_density, h1.2.2.2]
    ring
  have hnn : 0 ≤ ∫ x, (F.density s).density x * Real.log ((F.density s).density x)
        - (F.density s).density x * Real.log ((barycenter F).density x)
        - (F.density s).density x + (barycenter F).density x ∂haar d := by
    exact integral_nonneg (F.kernel_nonneg s)
  refine ⟨?_, ?_⟩
  · rw [hH]; exact ENNReal.ofReal_ne_top
  · rw [hH, ENNReal.toReal_ofReal hnn, hint]

end DGPS.SpeciesFamily

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem barycenter_density_eq_sum (F : SpeciesFamily d) (x : Torus d) :
    (barycenter F).density x = ∑ s, F.weight s * (F.density s).density x :=
  F.barycenterSqrt_sq x

theorem sum_weight_integral_density_mul_log (F : SpeciesFamily d) :
    ∑ s, F.weight s * ∫ x, (F.density s).density x * Real.log ((barycenter F).density x) ∂haar d
      = (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) (haar d)).toReal := by
  have hint : ∀ s, Integrable (fun x => F.weight s *
      ((F.density s).density x * Real.log ((barycenter F).density x))) (haar d) :=
    fun s => (F.integrable_density_mul_log_barycenter s).const_mul _
  have h1 : ∑ s, F.weight s * ∫ x, (F.density s).density x *
        Real.log ((barycenter F).density x) ∂haar d =
      ∫ x, ∑ s, F.weight s * ((F.density s).density x * Real.log ((barycenter F).density x))
        ∂haar d := by
    rw [integral_finsetSum _ fun s _ => hint s]
    exact Finset.sum_congr rfl fun s _ => (integral_const_mul _ _).symm
  rw [h1, (absoluteDensity_entropy_finite (barycenter F)).2.2.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show _ = (barycenter F).density x * Real.log ((barycenter F).density x)
  calc ∑ s, F.weight s * ((F.density s).density x * Real.log ((barycenter F).density x))
      = (∑ s, F.weight s * (F.density s).density x) * Real.log ((barycenter F).density x) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
    _ = _ := by rw [← F.barycenter_density_eq_sum x]

theorem speciesGap_decomposition (A : InteractionData d) (F : SpeciesFamily d) :
    (speciesGap A F : ℝ) = (scalarGap A (barycenter F) : ℝ) +
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal := by
  have hfin := (absoluteDensity_entropy_finite (barycenter F)).2.2.1
  have hE : densityFreeEnergy A (barycenter F) =
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) (haar d)).toReal +
        potentialEnergy A (densityMeasure (barycenter F)) +
        (1 / 2 : ℝ) * interactionEnergy A (densityMeasure (barycenter F)) := by
    have h := coe_densityFreeEnergy A (barycenter F)
    rw [freeEnergy_eq_real A _ hfin] at h
    exact EReal.coe_eq_coe_iff.mp h
  have hsum : ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (haar d)).toReal -
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) (haar d)).toReal := by
    rw [← F.sum_weight_integral_density_mul_log, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [(F.relativeEntropy_species s).2.2]; ring
  rw [coe_speciesGap, speciesRawGap_eq, coe_scalarGap, hE, hsum]

end DGPS.SpeciesFamily

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- LIP003 (square root mixture and score decompositions). -/
theorem square_root_mixture_and_score_decompositions (A : InteractionData d)
    (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    (barycenter F).sqrt ∈ H1Haar d ∧
    (∀ᵐ x ∂haar d, 0 < (barycenter F).sqrt x →
      weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem x =
        ((barycenter F).sqrt x)⁻¹ •
          ∑ s, F.weight s • (F.density s).sqrt x • F.sqrtGradient s x) ∧
    (∀ᵐ x ∂haar d, (barycenter F).sqrt x = 0 →
      ∀ s, (F.density s).sqrt x = 0 ∧ F.sqrtGradient s x = 0) ∧
    (∀ s, MemLp (F.scoreDifference s) 2 (haar d)) ∧
    (∀ s, F.scoreInformation s ≠ ⊤ ∧
      (F.scoreInformation s).toReal = ∫ x, ‖F.scoreDifference s x‖ ^ 2 ∂haar d) ∧
    (∀ s, (densityMeasure (F.density s) : Measure (Torus d)) ≪
        (densityMeasure (barycenter F) : Measure (Torus d)) ∧
      relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d)) ≠ ⊤) ∧
    (speciesGap A F : ℝ) = (scalarGap A (barycenter F) : ℝ) +
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (densityMeasure (barycenter F) : Measure (Torus d))).toReal ∧
    speciesDissipation A b F = scalarDissipation A b (barycenter F) +
      ∑ s, ENNReal.ofReal (F.weight s) * F.scoreInformation s := by
  refine ⟨(barycenter F).sqrt_mem, ?_, ?_, F.memLp_scoreDifference, F.scoreInformation_ne_top,
    fun s => ⟨(F.relativeEntropy_species s).1, (F.relativeEntropy_species s).2.1⟩,
    F.speciesGap_decomposition A, F.speciesDissipation_decomposition A b⟩
  · filter_upwards [F.barycenterWeakGrad_ae_eq] with x hx hpos
    exact hx.trans ((barycenter_gradient F).2.1 x hpos)
  · filter_upwards [F.sqrtGradient_zero_ae] with x hx h0 s
    exact ⟨F.sqrt_eq_zero_of_barycenter_eq_zero s x h0, hx h0 s⟩

end DGPS.Lipschitz
