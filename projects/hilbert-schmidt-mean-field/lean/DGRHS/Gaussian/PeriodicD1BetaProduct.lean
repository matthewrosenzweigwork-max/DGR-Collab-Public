import DGRHS.Gaussian.PeriodicD1BetaMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! RECORDS-ONLY UNCOMPILED DRAFT. The actual finite product of complementary
Beta laws, its support, bounded variable, and proper real Mellin moment.
The Gamma-product cancellation, moment-law comparison and original circle
partition identification remain separate. The BetaMoment import is itself an
uncompiled records-only successor, not a checked premise or available module. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Classical
namespace DGRHS.Periodic

lemma periodicD1_betaMeasure_support (α β : ℝ) :
    ∀ᵐ x : ℝ ∂betaMeasure α β,0<x ∧ x<1 := by
  apply ae_iff.mpr
  change (volume.withDensity (betaPDF α β)) (Ioo (0:ℝ) 1)ᶜ=0
  rw [withDensity_apply _ measurableSet_Ioo.compl]
  apply setLIntegral_eq_zero measurableSet_Ioo.compl
  intro x hx
  simp only [Set.mem_compl_iff,Set.mem_Ioo] at hx
  simp [betaPDF,betaPDFReal,hx]

def periodicD1BetaShape (N : ℕ) (j : Fin (N-1)) : ℝ :=
  ((j:ℕ)+1:ℝ)/(N:ℝ)

lemma periodicD1BetaShape_bounds (N : ℕ) (hN : 0<N) (j : Fin (N-1)) :
    0<periodicD1BetaShape N j ∧ periodicD1BetaShape N j<1 := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hj : (j:ℕ)+1<N := by have := j.isLt;omega
  constructor
  · exact div_pos (by positivity) hNr
  · apply (div_lt_one hNr).mpr
    exact_mod_cast hj

lemma periodicD1BetaShape_shift_pos (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) (j : Fin (N-1)) : 0<periodicD1BetaShape N j+s := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hj : 0≤(j:ℝ) := Nat.cast_nonneg _
  have hnum : 0<(j:ℝ)+1+(N:ℝ)*s := by linarith
  have h := div_pos hnum hNr
  convert h using 1
  unfold periodicD1BetaShape
  field_simp [hNr.ne']

def periodicD1BetaProductLaw (N : ℕ) : Measure (Fin (N-1) → ℝ) :=
  Measure.pi (fun j => betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j))

lemma periodicD1BetaProductLaw_probability (N : ℕ) (hN : 0<N) :
    IsProbabilityMeasure (periodicD1BetaProductLaw N) := by
  letI : ∀ j : Fin (N-1),IsProbabilityMeasure
      (betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j)) :=
    fun j => isProbabilityMeasureBeta (periodicD1BetaShape_bounds N hN j).1
      (sub_pos.mpr (periodicD1BetaShape_bounds N hN j).2)
  unfold periodicD1BetaProductLaw
  infer_instance

def periodicD1BetaProductVariable (N : ℕ) (x : Fin (N-1) → ℝ) : ℝ :=
  (N:ℝ)^N*∏j,x j

lemma periodicD1BetaProductVariable_continuous (N : ℕ) :
    Continuous (periodicD1BetaProductVariable N) := by
  unfold periodicD1BetaProductVariable
  exact continuous_const.mul (continuous_finsetProd _ (fun j _ => continuous_apply j))

lemma periodicD1BetaProductLaw_support (N : ℕ) (hN : 0<N) :
    ∀ᵐ x : Fin (N-1) → ℝ ∂periodicD1BetaProductLaw N,∀j,0<x j ∧ x j<1 := by
  letI : ∀ j : Fin (N-1),IsProbabilityMeasure
      (betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j)) :=
    fun j => isProbabilityMeasureBeta (periodicD1BetaShape_bounds N hN j).1
      (sub_pos.mpr (periodicD1BetaShape_bounds N hN j).2)
  apply ae_all_iff.mpr
  intro j
  have hEval := measurePreserving_eval
    (fun j => betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j)) j
  exact hEval.quasiMeasurePreserving.ae (periodicD1_betaMeasure_support _ _)

lemma periodicD1BetaProductVariable_bounds (N : ℕ) (hN : 0<N) :
    ∀ᵐ x ∂periodicD1BetaProductLaw N,
      0<periodicD1BetaProductVariable N x ∧ periodicD1BetaProductVariable N x≤(N:ℝ)^N := by
  filter_upwards [periodicD1BetaProductLaw_support N hN] with x hx
  have hp : 0<∏j,x j := Finset.prod_pos (fun j _ => (hx j).1)
  have hle : (∏j,x j)≤1 := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ) (f := x)
      (g := fun _ => (1:ℝ)) (fun j _ => (hx j).1.le) (fun j _ => (hx j).2.le)
    simpa only [Finset.prod_const_one] using h
  have hNpow : 0<(N:ℝ)^N := pow_pos (Nat.cast_pos.mpr hN) _
  refine ⟨mul_pos hNpow hp,?_⟩
  exact (mul_le_mul_of_nonneg_left hle hNpow.le).trans_eq (mul_one _)

lemma periodicD1_finite_product_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀i∈s,0≤x i) (t : ℝ) : (∏i∈s,x i)^t=∏i∈s,(x i)^t :=
  (Real.finsetProd_rpow s x hx t).symm

lemma periodicD1BetaProductVariable_rpow (N : ℕ) (hN : 0<N) (s : ℝ) :
    (fun x => (periodicD1BetaProductVariable N x)^s)=ᵐ[periodicD1BetaProductLaw N]
      fun x => ((N:ℝ)^N)^s*∏j,(x j)^s := by
  filter_upwards [periodicD1BetaProductLaw_support N hN] with x hx
  unfold periodicD1BetaProductVariable
  rw [Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _)
    (Finset.prod_nonneg (fun j _ => (hx j).1.le)),
    periodicD1_finite_product_rpow _ x (fun j _ => (hx j).1.le) s]

/-- Proper real moments of the literal Beta product, before Gamma cancellation. -/
theorem periodicD1BetaProductVariable_moment (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) :
    Integrable (fun x => (periodicD1BetaProductVariable N x)^s) (periodicD1BetaProductLaw N) ∧
      (∫x,(periodicD1BetaProductVariable N x)^s ∂periodicD1BetaProductLaw N)=
        ((N:ℝ)^N)^s*∏j : Fin (N-1),
          Real.Gamma (periodicD1BetaShape N j+s)/
            (Real.Gamma (periodicD1BetaShape N j)*Real.Gamma (1+s)) := by
  letI : ∀ j : Fin (N-1),IsProbabilityMeasure
      (betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j)) :=
    fun j => isProbabilityMeasureBeta (periodicD1BetaShape_bounds N hN j).1
      (sub_pos.mpr (periodicD1BetaShape_bounds N hN j).2)
  have hc (j : Fin (N-1)) := periodicD1_betaMeasure_complement_rpow_integral
    (periodicD1BetaShape N j) s (periodicD1BetaShape_bounds N hN j).1
    (periodicD1BetaShape_bounds N hN j).2 (periodicD1BetaShape_shift_pos N hN s hs j)
  have hp : Integrable (fun x : Fin (N-1) → ℝ => ∏j,(x j)^s)
      (periodicD1BetaProductLaw N) := Integrable.fintype_prod (fun j => (hc j).1)
  have he := periodicD1BetaProductVariable_rpow N hN s
  refine ⟨(hp.const_mul _).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_const_mul]
  unfold periodicD1BetaProductLaw
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin (N-1)) (x : ℝ) => x^s)
    (μ := fun j => betaMeasure (periodicD1BetaShape N j) (1-periodicD1BetaShape N j))]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact (hc j).2

end DGRHS.Periodic
