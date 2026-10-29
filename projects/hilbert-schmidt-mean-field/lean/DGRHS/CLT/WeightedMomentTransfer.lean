/- Bounded continuous tests times an actual nonnegative continuous weight:
changing-law expectation transfer from a genuine higher moment bound. -/
import DGRHS.CLT.SignedMomentTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT

variable {E S : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace S] {ρ : Measure S}

lemma weighted_test_bound (F w : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ x, |F x| ≤ M) (hw : ∀ x, 0 ≤ w x) (x : E) :
    |F x*w x| ≤ M*w x := by
  rw [abs_mul, abs_of_nonneg (hw x)]
  exact mul_le_mul_of_nonneg_right (hF x) (hw x)

lemma integrable_weighted_test (F w : E → ℝ) (hFcont : Continuous F)
    (hwcont : Continuous w) (M : ℝ) (hM : 0 ≤ M)
    (hF : ∀ x, |F x| ≤ M) (hw : ∀ x, 0 ≤ w x)
    (X : S → E) (hX : AEMeasurable X ρ) (hW : Integrable (fun x => w (X x)) ρ) :
    Integrable (fun x => F (X x)*w (X x)) ρ := by
  apply (hW.const_mul M).mono'
    ((hFcont.mul hwcont).measurable.comp_aemeasurable hX).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change |F (X x)*w (X x)| ≤ M*w (X x)
    exact weighted_test_bound F w M hM hF hw _

lemma integrable_weighted_test_moment (F w : E → ℝ) (hFcont : Continuous F)
    (hwcont : Continuous w) (M p : ℝ) (hM : 0 ≤ M) (hp : 0 ≤ p)
    (hF : ∀ x, |F x| ≤ M) (hw : ∀ x, 0 ≤ w x)
    (X : S → E) (hX : AEMeasurable X ρ)
    (hW : Integrable (fun x => (w (X x))^p) ρ) :
    Integrable (fun x => |F (X x)*w (X x)|^p) ρ := by
  have hc : Continuous (fun x => |F x*w x|^p) :=
    (Real.continuous_rpow_const hp).comp (hFcont.mul hwcont).abs
  apply (hW.const_mul (M^p)).mono' (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change |(|F (X x)*w (X x)|^p)| ≤ M^p*(w (X x))^p
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      _ ≤ (M*w (X x))^p := Real.rpow_le_rpow (abs_nonneg _)
        (weighted_test_bound F w M hM hF hw _) hp
      _ = _ := Real.mul_rpow hM (hw _)

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma weighted_integral_tendsto_of_distribution_moment
    (X : ∀ n, Ω n → E) (Z : Ω' → E)
    (hweak : TendstoInDistribution X atTop Z μ ν)
    (F w : E → ℝ) (hFcont : Continuous F) (hwcont : Continuous w)
    (M p C : ℝ) (hM : 0 ≤ M) (hp : 1 < p)
    (hF : ∀ x, |F x| ≤ M) (hw : ∀ x, 0 ≤ w x)
    (hW : ∀ n, Integrable (fun x => w (X n x)) (μ n))
    (hZ : Integrable (fun z => w (Z z)) ν)
    (hmom : ∀ n, Integrable (fun x => (w (X n x))^p) (μ n))
    (hC : ∀ n, (∫ x, (w (X n x))^p ∂μ n) ≤ C) :
    Tendsto (fun n => ∫ x, F (X n x)*w (X n x) ∂μ n) atTop
      (𝓝 (∫ z, F (Z z)*w (Z z) ∂ν)) := by
  have hp0 : 0 ≤ p := (lt_trans zero_lt_one hp).le
  have hi := fun n => integrable_weighted_test F w hFcont hwcont M hM hF hw
    (X n) (hweak.forall_aemeasurable n) (hW n)
  have him := fun n => integrable_weighted_test_moment F w hFcont hwcont M p hM hp0 hF hw
    (X n) (hweak.forall_aemeasurable n) (hmom n)
  apply integral_tendsto_of_distribution_absolute_moment
    (fun n x => F (X n x)*w (X n x)) (fun z => F (Z z)*w (Z z))
    (hweak.continuous_comp (g := fun x => F x*w x) (hFcont.mul hwcont)) hi
    (integrable_weighted_test F w hFcont hwcont M hM hF hw Z hweak.aemeasurable_limit hZ)
    p (M^p*C) hp him
  intro n
  calc
    _ ≤ ∫ x, M^p*(w (X n x))^p ∂μ n := by
      apply integral_mono (him n) ((hmom n).const_mul _)
      intro x
      calc
        _ ≤ (M*w (X n x))^p := Real.rpow_le_rpow (abs_nonneg _)
          (weighted_test_bound F w M hM hF hw _) hp0
        _ = _ := Real.mul_rpow hM (hw _)
    _ = M^p*(∫ x, (w (X n x))^p ∂μ n) := integral_const_mul _ _
    _ ≤ M^p*C := mul_le_mul_of_nonneg_left (hC n) (Real.rpow_nonneg hM _)

end DGRHS.CLT
#print axioms DGRHS.CLT.integrable_weighted_test
#print axioms DGRHS.CLT.integrable_weighted_test_moment
#print axioms DGRHS.CLT.weighted_integral_tendsto_of_distribution_moment
#check @DGRHS.CLT.weighted_integral_tendsto_of_distribution_moment
