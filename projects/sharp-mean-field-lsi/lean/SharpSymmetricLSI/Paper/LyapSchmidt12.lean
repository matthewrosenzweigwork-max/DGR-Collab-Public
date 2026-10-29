import SharpSymmetricLSI.Paper.LyapSchmidt11

/-!
# Section 4.2 (lane s42; R14): the reduced energy is the free-energy gap

For a minimizer `μ = p m` and `h ∈ C(𝕋^d)` with `1 + h > 0`, `μ(h) = 0`, the probability
`ρ = p(1+h) m` has `G(ρ) = ∫ (1+h) log(1+h) dμ + ½ ∫ h T h dμ = PsiC h` (via (4.15):
`G = H(·|μ) + J`, `H(ρ|μ) = ∫ klFun(1+h) dμ`, `2J(ρ) = K(ρ,ρ) = ⟨h, T h⟩_μ`).
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section gapid
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

theorem graph_density_props {h : CT d} (hpos : h ∈ posSet)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    (∀ x, 0 < elDens V W (μ : Measure (Torus d)) x * (1 + h x)) ∧
    ∫ x, elDens V W (μ : Measure (Torus d)) x * (1 + h x) ∂haar d = 1 := by
  obtain ⟨-, hp0, -⟩ := elDensity_props hyp (μ : Measure (Torus d))
  refine ⟨fun x => mul_pos (hp0 x) (hpos x), ?_⟩
  have e := integral_minimizer hyp hμ (fun x => 1 + h x)
  rw [← e, integral_add (integrable_const _) (integrable_of_continuous h.continuous), hh0]
  simp

/-- `∫ F dρ = ∫ (1+h) F dμ` for `ρ = p(1+h) m`. -/
theorem integral_graph_density {h : CT d} (hpos : h ∈ posSet)
    (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (F : Torus d → ℝ) :
    ∫ x, F x ∂densMeasure (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + h x)) =
      ∫ x, (1 + h x) * F x ∂(μ : Measure (Torus d)) := by
  obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
  rw [integral_densMeasure' (fun x => (h0 x).le) h1, integral_minimizer hyp hμ]
  congr 1; funext x; ring

/-- The graph density as `μ` with density `1 + h`. -/
theorem densMeasure_graph {h : CT d} (hpos : h ∈ posSet) :
    densMeasure (fun x => elDens V W (μ : Measure (Torus d)) x * (1 + h x)) =
      (μ : Measure (Torus d)).withDensity fun x => ENNReal.ofReal (1 + h x) := by
  set p := elDens V W (μ : Measure (Torus d)) with hp
  obtain ⟨hpm, hp0, -⟩ := elDensity_props hyp (μ : Measure (Torus d))
  have hμp : (μ : Measure (Torus d)) = densMeasure p := minimizer_eq_elDensity hyp hμ
  have hf : Measurable fun x => ENNReal.ofReal (p x) := ENNReal.measurable_ofReal.comp hpm
  have hg : Measurable fun x => ENNReal.ofReal (1 + h x) :=
    ENNReal.measurable_ofReal.comp (continuous_const.add h.continuous).measurable
  have e : (fun x => ENNReal.ofReal (p x * (1 + h x))) =
      (fun x => ENNReal.ofReal (p x)) * fun x => ENNReal.ofReal (1 + h x) := by
    funext x
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ p x from (hp0 x).le)]
  conv_rhs => rw [hμp]
  unfold densMeasure
  rw [e, withDensity_mul _ hf hg]

/-- **The reduced energy is the gap.** -/
theorem gap_graph {h : CT d} (hpos : h ∈ posSet) (hh0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    haveI := isProbabilityMeasure_densMeasure'
      (fun x => (graph_density_props hyp hμ hpos hh0).1 x |>.le)
      (graph_density_props hyp hμ hpos hh0).2
    gap V W (densMeasure fun x => elDens V W (μ : Measure (Torus d)) x * (1 + h x)) =
      ((PsiC hyp (μ : Measure (Torus d)) h : ℝ) : EReal) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨h0, h1⟩ := graph_density_props hyp hμ hpos hh0
  haveI hρp := isProbabilityMeasure_densMeasure' (fun x => (h0 x).le) h1
  set ρ : ProbabilityMeasure (Torus d) :=
    ⟨densMeasure fun x => elDens V W μm x * (1 + h x), hρp⟩
  have hgap := gap_eq_aux hyp hμ ρ
  -- the relative entropy
  have hkl : klDiv (ρ : Measure (Torus d)) μm =
      ENNReal.ofReal (∫ x, klFun (1 + h x) ∂μm) := by
    have hρ : (ρ : Measure (Torus d)) = μm.withDensity fun x => ENNReal.ofReal (1 + h x) :=
      densMeasure_graph hyp hμ hpos
    have hm : AEMeasurable (fun x => ENNReal.ofReal (1 + h x)) μm :=
      (ENNReal.measurable_ofReal.comp (continuous_const.add h.continuous).measurable).aemeasurable
    haveI : IsFiniteMeasure (μm.withDensity fun x => ENNReal.ofReal (1 + h x)) := by
      rw [← hρ]; infer_instance
    rw [hρ, klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous _ _)]
    have hint : Integrable (fun x => klFun (1 + h x)) μm :=
      integrable_of_continuous (continuous_klFun.comp (continuous_const.add h.continuous))
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => klFun_nonneg (hpos x).le)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_withDensity₀ μm hm] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpos x).le]
  have hklr : ∫ x, klFun (1 + h x) ∂μm = ∫ x, ((1 + h) * logC h) x ∂μm := by
    have e : ∀ x, klFun (1 + h x) = ((1 + h) * logC h) x - h x := fun x => by
      rw [klFun_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
        logC_apply hpos]
      ring
    simp_rw [e]
    rw [integral_sub (integrable_of_continuous ((1 + h) * logC h).continuous)
      (integrable_of_continuous h.continuous), hh0, sub_zero]
  -- the interaction
  have hJ : 2 * Jfun W μm ρ = ∫ x, h x * TC hyp μm h x ∂μm := by
    have hK := continuous_centeredKernel hyp μm
    unfold Jfun interE
    have hin : ∀ y, ∫ x, centeredKernel W μm x y ∂(ρ : Measure (Torus d)) =
        TC hyp μm h y := fun y => by
      show ∫ x, centeredKernel W μm x y ∂(densMeasure _) = _
      rw [integral_graph_density hyp hμ hpos hh0]
      have i1 : Integrable (fun x => centeredKernel W μm x y) μm :=
        integrable_of_continuous (cont_left hK y)
      have i2 : Integrable (fun x => h x * centeredKernel W μm x y) μm :=
        integrable_of_continuous (h.continuous.mul (cont_left hK y))
      have e : (fun x => (1 + h x) * centeredKernel W μm x y) =
          fun x => centeredKernel W μm x y + h x * centeredKernel W μm x y := by
        funext x; ring
      rw [e, integral_add i1 i2, TC_apply,
        Top_eq_integral hyp μm (memL20_CT hyp μm hh0) y]
      have h0' : ∫ x, centeredKernel W μm x y ∂μm = 0 := by
        simp_rw [centeredKernel_symm_coerc hyp μm _ y]; exact integral_centeredKernel hyp μm y
      rw [h0', zero_add]
      congr 1; funext x; rw [centeredKernel_symm_coerc hyp μm x y, mul_comm]
    simp_rw [hin]
    show 2 * ((∫ y, TC hyp μm h y ∂densMeasure _) / 2) = _
    rw [integral_graph_density hyp hμ hpos hh0]
    have i1 : Integrable (fun y => TC hyp μm h y) μm :=
      integrable_of_continuous (TC hyp μm h).continuous
    have i2 : Integrable (fun y => h y * TC hyp μm h y) μm :=
      integrable_of_continuous (h.continuous.mul (TC hyp μm h).continuous)
    have e : (fun y => (1 + h y) * TC hyp μm h y) =
        fun y => TC hyp μm h y + h y * TC hyp μm h y := by funext y; ring
    rw [e, integral_add i1 i2]
    have hT0 : ∫ y, TC hyp μm h y ∂μm = 0 := integral_Top hyp μm (integrable_CT hyp μm h)
    rw [hT0]; ring
  show gap V W (ρ : Measure (Torus d)) = _
  have hnn : 0 ≤ ∫ x, klFun (1 + h x) ∂μm := integral_nonneg fun x => klFun_nonneg (hpos x).le
  rw [hgap, hkl, EReal.coe_ennreal_ofReal, max_eq_left hnn, ← EReal.coe_add, hklr]
  congr 1
  simp only [PsiC, meanC_apply, ContinuousMap.mul_apply]
  linarith

end gapid

end SharpLSI
