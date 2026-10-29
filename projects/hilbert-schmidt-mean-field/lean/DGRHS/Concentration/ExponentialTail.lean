import DGRHS.Concentration.IidOperator
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Concentration

/-- The exponential moment is constructed from a tail estimate by layer cake;
no exponential integrability is assumed. -/
theorem exponential_integrable_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEMeasurable X μ) (u₀ L : ℝ) (hL : 0 ≤ L)
    (hTail : ∀ u, u₀ < u → μ {ω | u ≤ X ω} ≤ ENNReal.ofReal (L*Real.exp (-2*u))) :
    Integrable (fun ω ↦ Real.exp (X ω)) μ ∧
      (∫ ω, Real.exp (X ω) ∂μ) ≤ Real.exp u₀ + L*Real.exp (-u₀) := by
  let F : Ω → ℝ := fun ω ↦ max (X ω-u₀) 0
  let J : Ω → ℝ := fun ω ↦ Real.exp u₀*(Real.exp (F ω)-1)
  have hF : AEMeasurable F μ := (hX.sub aemeasurable_const).max aemeasurable_const
  have hFnn : ∀ ω, 0 ≤ F ω := fun ω ↦ le_max_right _ _
  have hJnn : ∀ ω, 0 ≤ J ω := by
    intro ω
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (hFnn ω)))
  have hJm : AEStronglyMeasurable J μ :=
    (aemeasurable_const.mul ((Real.measurable_exp.comp_aemeasurable hF).sub aemeasurable_const)).aestronglyMeasurable
  have hPrimitive : ∀ ω, (∫ t in 0..F ω, Real.exp u₀*Real.exp t) = J ω := by
    intro ω
    simp only [intervalIntegral.integral_const_mul,integral_exp,Real.exp_zero,J]
  have hLayer := lintegral_comp_eq_lintegral_meas_le_mul μ
    (Eventually.of_forall hFnn) hF
    (fun t _ ↦ intervalIntegral.intervalIntegrable_exp.const_mul (Real.exp u₀))
    (Eventually.of_forall fun _ ↦ mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  simp_rw [hPrimitive] at hLayer
  have hBound : (∫⁻ ω, ENNReal.ofReal (J ω) ∂μ) ≤ ENNReal.ofReal (L*Real.exp (-u₀)) := by
    rw [hLayer]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (L*Real.exp (-u₀)*Real.exp (-t)) := by
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        have he : {ω | t ≤ F ω} = {ω | t+u₀ ≤ X ω} := by
          ext ω
          simp only [mem_ofPred_eq,F,le_max_iff]
          constructor
          · intro h
            rcases h with h | h
            · linarith
            · exact (not_le_of_gt ht h).elim
          · intro h
            exact Or.inl (by linarith)
        rw [he]
        calc
          _ ≤ ENNReal.ofReal (L*Real.exp (-2*(t+u₀))) * ENNReal.ofReal (Real.exp u₀*Real.exp t) :=
            mul_le_mul (hTail (t+u₀) (lt_add_of_pos_left u₀ ht)) le_rfl zero_le zero_le
          _ = ENNReal.ofReal (L*Real.exp (-u₀)*Real.exp (-t)) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg hL (Real.exp_pos _).le)]
            congr 1
            simp only [mul_assoc,← Real.exp_add]
            congr 2
            ring
      _ = ENNReal.ofReal (L*Real.exp (-u₀)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_exp_neg_Ioi 0).const_mul (L*Real.exp (-u₀)))
          (Eventually.of_forall fun _ ↦ mul_nonneg (mul_nonneg hL (Real.exp_pos _).le) (Real.exp_pos _).le)]
        rw [integral_const_mul,integral_exp_neg_Ioi_zero,mul_one]
  have hJi : Integrable J μ := ⟨hJm,(hasFiniteIntegral_iff_ofReal (Eventually.of_forall hJnn)).mpr
    (hBound.trans_lt ENNReal.ofReal_lt_top)⟩
  have hPoint : ∀ ω, Real.exp (X ω) ≤ Real.exp u₀+J ω := by
    intro ω
    calc
      _ ≤ Real.exp (u₀+F ω) := Real.exp_le_exp.mpr (by
        have := le_max_left (X ω-u₀) 0
        dsimp [F]
        linarith)
      _ = _ := by rw [Real.exp_add]; dsimp [J]; ring
  have hExp : Integrable (fun ω ↦ Real.exp (X ω)) μ :=
    ((integrable_const (Real.exp u₀)).add hJi).mono'
      (Real.measurable_exp.comp_aemeasurable hX).aestronglyMeasurable
      (Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Pi.add_apply] using hPoint ω)
  refine ⟨hExp,?_⟩
  calc
    _ ≤ ∫ ω, Real.exp u₀+J ω ∂μ := integral_mono hExp ((integrable_const _).add hJi) hPoint
    _ = Real.exp u₀+∫ ω,J ω ∂μ := by rw [integral_add (integrable_const _) hJi]; simp
    _ ≤ Real.exp u₀+L*Real.exp (-u₀) := by
      apply add_le_add le_rfl
      have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBound
      rw [← ofReal_integral_eq_lintegral_ofReal hJi (Eventually.of_forall hJnn)] at hb
      simpa only [ENNReal.toReal_ofReal (integral_nonneg hJnn),ENNReal.toReal_ofReal (mul_nonneg hL (Real.exp_pos _).le)] using hb

#print axioms DGRHS.Concentration.exponential_integrable_of_tail
#check @DGRHS.Concentration.exponential_integrable_of_tail
end DGRHS.Concentration
