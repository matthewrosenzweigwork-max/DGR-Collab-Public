import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

/-! RECORDS-ONLY UNCOMPILED DRAFT. The actual Beta-law Mellin moment is proved
by a density shift, deriving properness from the normalized shifted Beta law.
Native source: Probability/Distributions/Beta.lean, pin
 d13f23b723b8a846827a245b89c10fc7d3f11612 (Apache-2.0).
No desired circular integral or desired moment identity is a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace DGRHS.Periodic

lemma periodicD1_betaPDFReal_nonneg (α β : ℝ) (hα : 0<α) (hβ : 0<β) (x : ℝ) :
    0≤betaPDFReal α β x := by
  by_cases hx : 0<x ∧ x<1
  · exact (betaPDFReal_pos hx.1 hx.2 hα hβ).le
  · simp [betaPDFReal,hx]

lemma periodicD1_betaPDFReal_integrable (α β : ℝ) (hα : 0<α) (hβ : 0<β) :
    Integrable (betaPDFReal α β) volume := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_betaPDFReal α β).aestronglyMeasurable
    (Eventually.of_forall (periodicD1_betaPDFReal_nonneg α β hα hβ))).mp
  change (∫⁻ x,betaPDF α β x)≠⊤
  rw [lintegral_betaPDF_eq_one hα hβ]
  exact ENNReal.one_ne_top

lemma periodicD1_betaPDFReal_integral (α β : ℝ) (hα : 0<α) (hβ : 0<β) :
    (∫ x,betaPDFReal α β x)=1 := by
  have h := ofReal_integral_eq_lintegral_ofReal
    (periodicD1_betaPDFReal_integrable α β hα hβ)
    (Eventually.of_forall (periodicD1_betaPDFReal_nonneg α β hα hβ))
  change ENNReal.ofReal (∫ x,betaPDFReal α β x)=∫⁻ x,betaPDF α β x at h
  rw [lintegral_betaPDF_eq_one hα hβ] at h
  have hnonneg : 0≤∫ x,betaPDFReal α β x :=
    MeasureTheory.integral_nonneg (f := betaPDFReal α β) (μ := volume)
      (periodicD1_betaPDFReal_nonneg α β hα hβ)
  have ht := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal hnonneg,ENNReal.toReal_one] using ht

/-- Pointwise density shift, including the vanishing density outside (0,1). -/
lemma periodicD1_betaPDFReal_mul_rpow (α β s : ℝ)
    (hα : 0<α) (hβ : 0<β) (hs : 0<α+s) (x : ℝ) :
    betaPDFReal α β x*x^s =
      (beta (α+s) β / beta α β)*betaPDFReal (α+s) β x := by
  by_cases hx : 0<x ∧ x<1
  · simp only [betaPDFReal,if_pos hx]
    have hp : x^(α-1)*x^s=x^(α+s-1) := by
      rw [←Real.rpow_add hx.1]
      congr 1
      ring
    have hb0 := (beta_pos hα hβ).ne'
    have hb1 := (beta_pos hs hβ).ne'
    calc
      _ = (1/beta α β)*(x^(α-1)*x^s)*(1-x)^(β-1) := by ring
      _ = (1/beta α β)*x^(α+s-1)*(1-x)^(β-1) := by rw [hp]
      _ = _ := by field_simp [hb0,hb1]
  · simp [betaPDFReal,hx]

/-- Properness of every admissible real moment of the actual native Beta law. -/
lemma periodicD1_betaMeasure_rpow_integrable (α β s : ℝ)
    (hα : 0<α) (hβ : 0<β) (hs : 0<α+s) :
    Integrable (fun x : ℝ => x^s) (betaMeasure α β) := by
  unfold betaMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (measurable_betaPDFReal α β).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have h := (periodicD1_betaPDFReal_integrable (α+s) β hs hβ).const_mul
    (beta (α+s) β / beta α β)
  apply h.congr
  filter_upwards [] with x
  change (beta (α+s) β/beta α β)*betaPDFReal (α+s) β x=
    (ENNReal.ofReal (betaPDFReal α β x)).toReal*x^s
  rw [ENNReal.toReal_ofReal (periodicD1_betaPDFReal_nonneg α β hα hβ x)]
  exact (periodicD1_betaPDFReal_mul_rpow α β s hα hβ hs x).symm

/-- The moment value is derived by genuine integration of the shifted density. -/
theorem periodicD1_betaMeasure_rpow_integral (α β s : ℝ)
    (hα : 0<α) (hβ : 0<β) (hs : 0<α+s) :
    (∫ x : ℝ,x^s ∂betaMeasure α β)=beta (α+s) β/beta α β := by
  unfold betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (f := betaPDF α β)
    (measurable_betaPDFReal α β).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hfun : (fun x : ℝ => (betaPDF α β x).toReal • x^s)=
      fun x => (beta (α+s) β/beta α β)*betaPDFReal (α+s) β x := by
    funext x
    rw [betaPDF,ENNReal.toReal_ofReal (periodicD1_betaPDFReal_nonneg α β hα hβ x),smul_eq_mul]
    exact periodicD1_betaPDFReal_mul_rpow α β s hα hβ hs x
  rw [hfun,integral_const_mul,periodicD1_betaPDFReal_integral (α+s) β hs hβ,mul_one]

/-- The special shapes used for the circular-product comparison law. -/
theorem periodicD1_betaMeasure_complement_rpow_integral (a s : ℝ)
    (ha : 0<a) (ha1 : a<1) (hs : 0<a+s) :
    Integrable (fun x : ℝ => x^s) (betaMeasure a (1-a)) ∧
      (∫ x : ℝ,x^s ∂betaMeasure a (1-a))=
        Real.Gamma (a+s)/(Real.Gamma a*Real.Gamma (1+s)) := by
  have hb : 0<1-a := sub_pos.mpr ha1
  have hs1 : 0<1+s := by linarith
  refine ⟨periodicD1_betaMeasure_rpow_integrable a (1-a) s ha hb hs,?_⟩
  rw [periodicD1_betaMeasure_rpow_integral a (1-a) s ha hb hs,beta,beta]
  rw [show a+(1-a)=1 by ring,show a+s+(1-a)=1+s by ring,Real.Gamma_one]
  field_simp [(Real.Gamma_pos_of_pos ha).ne',
    (Real.Gamma_pos_of_pos hb).ne',(Real.Gamma_pos_of_pos hs1).ne']

end DGRHS.Periodic
