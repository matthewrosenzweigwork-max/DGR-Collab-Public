import SharpSymmetricLSI.Paper.ULimit4

/-!
# Approximation in distribution (Phase 3, lane D; R26)

If `W^R_N ⇒ Y^R` for each `R`, and `V_N`, `Y` are uniformly `L¹`-close to `W^R_N`, `Y^R` with an
error `δ_R → 0`, then `V_N ⇒ Y` (bounded Lipschitz test functions and the Portmanteau theorem).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

section approx
variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P'] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]

/-- `|∫ f∘A - ∫ f∘B| ≤ L ∫ ‖A - B‖` for a bounded `L`-Lipschitz `f`. -/
theorem abs_integral_lip_sub_le {Ω₀ : Type*} [MeasurableSpace Ω₀] {Q : Measure Ω₀}
    [IsProbabilityMeasure Q] {f : E → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {L : NNReal}
    (hL : LipschitzWith L f) {A B : Ω₀ → E} (hA : AEMeasurable A Q) (hB : AEMeasurable B Q)
    (hAB : Integrable (fun ω => ‖A ω - B ω‖) Q) :
    |∫ ω, f (A ω) ∂Q - ∫ ω, f (B ω) ∂Q| ≤ L * ∫ ω, ‖A ω - B ω‖ ∂Q := by
  have hfm : Measurable f := hL.continuous.measurable
  have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
    have := hC x 0; rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (f x) (f 0); linarith
  have hiA : Integrable (fun ω => f (A ω)) Q :=
    Integrable.of_bound (hfm.comp_aemeasurable hA).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd _)
  have hiB : Integrable (fun ω => f (B ω)) Q :=
    Integrable.of_bound (hfm.comp_aemeasurable hB).aestronglyMeasurable (|f 0| + C)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd _)
  rw [← integral_sub hiA hiB, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (hiA.sub hiB).abs
    (hAB.const_mul _) fun ω => ?_)
  have := hL.dist_le_mul (A ω) (B ω)
  rw [Real.dist_eq, dist_eq_norm] at this
  exact this

set_option backward.isDefEq.respectTransparency.types false in
theorem tendstoInDistribution_of_approx {V : ℕ → Ω → E} {W : ℕ → ℕ → Ω → E} {Y : Ω' → E}
    {Yr : ℕ → Ω' → E} {δ : ℕ → ℝ} (hV : ∀ N, AEMeasurable (V N) P) (hY : AEMeasurable Y P')
    (hW : ∀ R, TendstoInDistribution (W R) atTop (Yr R) (fun _ => P) P')
    (hδ : Tendsto δ atTop (𝓝 0))
    (hVW : ∀ R, ∀ᶠ N in atTop, Integrable (fun ω => ‖V N ω - W R N ω‖) P ∧
      ∫ ω, ‖V N ω - W R N ω‖ ∂P ≤ δ R)
    (hYY : ∀ R, Integrable (fun ω => ‖Y ω - Yr R ω‖) P' ∧ ∫ ω, ‖Y ω - Yr R ω‖ ∂P' ≤ δ R) :
    TendstoInDistribution V atTop Y (fun _ => P) P' := by
  refine ⟨hV, hY, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f ⟨C, hC⟩ ⟨L, hL⟩
  have hfm : Measurable f := hL.continuous.measurable
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_map hY hfm.aestronglyMeasurable]
  simp_rw [fun N => integral_map (hV N) hfm.aestronglyMeasurable]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨R, hR⟩ : ∃ R, (L : ℝ) * δ R < ε / 3 := by
    have h := (hδ.const_mul (L : ℝ)).eventually (eventually_lt_nhds
      (show (L : ℝ) * 0 < ε / 3 by rw [mul_zero]; exact div_pos hε (by norm_num)))
    exact h.exists
  have hWR := (tendsto_iff_forall_lipschitz_integral_tendsto.mp (hW R).tendsto) f ⟨C, hC⟩ ⟨L, hL⟩
  simp only [ProbabilityMeasure.coe_mk] at hWR
  rw [integral_map (hW R).aemeasurable_limit hfm.aestronglyMeasurable] at hWR
  simp_rw [fun N => integral_map ((hW R).forall_aemeasurable N) hfm.aestronglyMeasurable] at hWR
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hWR (ε / 3) (by positivity)
  obtain ⟨N2, hN2⟩ := (hVW R).exists_forall_of_atTop
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have h1 := hN1 N (le_of_max_le_left hN)
  obtain ⟨hi2, hb2⟩ := hN2 N (le_of_max_le_right hN)
  have e1 := abs_integral_lip_sub_le hC hL (hV N) ((hW R).forall_aemeasurable N) hi2
  have e3 := abs_integral_lip_sub_le hC hL hY (hW R).aemeasurable_limit (hYY R).1
  have hL0 : (0 : ℝ) ≤ L := L.2
  have e1' : |∫ ω, f (V N ω) ∂P - ∫ ω, f (W R N ω) ∂P| < ε / 3 :=
    e1.trans_lt ((mul_le_mul_of_nonneg_left hb2 hL0).trans_lt hR)
  have e3' : |∫ ω, f (Y ω) ∂P' - ∫ ω, f (Yr R ω) ∂P'| < ε / 3 :=
    e3.trans_lt ((mul_le_mul_of_nonneg_left (hYY R).2 hL0).trans_lt hR)
  rw [Real.dist_eq] at h1 ⊢
  calc |∫ ω, f (V N ω) ∂P - ∫ ω, f (Y ω) ∂P'|
      ≤ |∫ ω, f (V N ω) ∂P - ∫ ω, f (W R N ω) ∂P| +
        |∫ ω, f (W R N ω) ∂P - ∫ ω, f (Yr R ω) ∂P'| +
        |∫ ω, f (Y ω) ∂P' - ∫ ω, f (Yr R ω) ∂P'| := by
        rw [abs_sub_comm (∫ ω, f (Y ω) ∂P')]
        refine (abs_sub_le _ (∫ ω, f (Yr R ω) ∂P') _).trans ?_
        gcongr
        exact abs_sub_le _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by gcongr
    _ = ε := by ring

set_option backward.isDefEq.respectTransparency.types false in
/-- Convergence in distribution gives convergence of integrals of bounded continuous functions. -/
theorem TendstoInDistribution.tendsto_integral_bcf {V : ℕ → Ω → E} {Y : Ω' → E}
    (h : TendstoInDistribution V atTop Y (fun _ => P) P') (g : E →ᵇ ℝ) :
    Tendsto (fun N => ∫ ω, g (V N ω) ∂P) atTop (𝓝 (∫ ω, g (Y ω) ∂P')) := by
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto) g
  simp only [ProbabilityMeasure.coe_mk] at h1
  rw [integral_map h.aemeasurable_limit g.continuous.aestronglyMeasurable] at h1
  simp_rw [fun N => integral_map (h.forall_aemeasurable N) g.continuous.aestronglyMeasurable] at h1
  exact h1

end approx

end SharpLSI
