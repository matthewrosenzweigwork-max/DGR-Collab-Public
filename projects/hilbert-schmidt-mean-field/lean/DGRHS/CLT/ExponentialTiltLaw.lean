/- Actual normalized tilted probability laws and changing-domain weak limit.
This is a generic transfer theorem; paper applications must derive the supplied
proper higher exponential moment bound from their physical assumptions. -/
import DGRHS.CLT.ExponentialTiltMeasure
import DGRHS.CLT.WeightedMomentTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT

variable {S : Type*} [MeasurableSpace S]
def exponentialTiltProbability (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → ℝ) (hi : Integrable (fun x => Real.exp (Y x)) μ) : ProbabilityMeasure S :=
  ⟨exponentialTiltMeasure μ Y, exponentialTiltMeasure_probability Y hi⟩

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma exponentialTilt_tendstoInDistribution
    (X : ∀ n, Ω n → E) (Z : Ω' → E)
    (hweak : TendstoInDistribution X atTop Z μ ν)
    (g : E → ℝ) (hg : Continuous g)
    (hi : ∀ n, Integrable (fun x => Real.exp (g (X n x))) (μ n))
    (hz : Integrable (fun z => Real.exp (g (Z z))) ν)
    (p C : ℝ) (hp : 1 < p)
    (hmom : ∀ n, Integrable (fun x => Real.exp (p*g (X n x))) (μ n))
    (hC : ∀ n, (∫ x, Real.exp (p*g (X n x)) ∂μ n) ≤ C) :
    TendstoInDistribution X atTop Z
      (fun n => (exponentialTiltProbability (μ n) (fun x => g (X n x)) (hi n) : Measure (Ω n)))
      (exponentialTiltProbability ν (fun z => g (Z z)) hz : Measure Ω') := by
  let μt : ∀ n, Measure (Ω n) := fun n =>
    exponentialTiltProbability (μ n) (fun x => g (X n x)) (hi n)
  let νt : Measure Ω' := exponentialTiltProbability ν (fun z => g (Z z)) hz
  have hx : ∀ n, AEMeasurable (X n) (μt n) := by
    intro n
    exact (hweak.forall_aemeasurable n).mono_ac (withDensity_absolutelyContinuous _ _)
  have hzmeas : AEMeasurable Z νt :=
    hweak.aemeasurable_limit.mono_ac (withDensity_absolutelyContinuous _ _)
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hx hzmeas).mpr
  intro F
  have hweight : Continuous (fun e => Real.exp (g e)) := Real.continuous_exp.comp hg
  have hwpos : ∀ e, 0 ≤ Real.exp (g e) := fun e => (Real.exp_pos _).le
  have hpow : ∀ e : E, (Real.exp (g e))^p = Real.exp (p*g e) := by
    intro e
    rw [← Real.exp_mul, mul_comm]
  have hm : ∀ n, Integrable (fun x => (Real.exp (g (X n x)))^p) (μ n) := by
    intro n
    simpa only [hpow] using hmom n
  have hmC : ∀ n, (∫ x, (Real.exp (g (X n x)))^p ∂μ n) ≤ C := by
    intro n
    simpa only [hpow] using hC n
  have hn := weighted_integral_tendsto_of_distribution_moment X Z hweak F
    (fun e => Real.exp (g e)) F.continuous hweight ‖F‖ p C (norm_nonneg _) hp
    (fun e => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm e)
    hwpos hi hz hm hmC
  have hd := exponential_integral_tendsto_of_distribution_moment
    (fun n x => g (X n x)) (fun z => g (Z z))
    (hweak.continuous_comp (g := g) hg) hz p C hp hmom hC
  have ht := hn.div hd (integral_exp_pos hz).ne'
  have heqn : ∀ n, (∫ x, F (X n x) ∂μt n) =
      (∫ x, F (X n x)*Real.exp (g (X n x)) ∂μ n)/(∫ x, Real.exp (g (X n x)) ∂μ n) := by
    intro n
    exact integral_exponentialTiltMeasure _ (hg.measurable.comp_aemeasurable
      (hweak.forall_aemeasurable n)) (hi n) _
  have heqz : (∫ z, F (Z z) ∂νt) =
      (∫ z, F (Z z)*Real.exp (g (Z z)) ∂ν)/(∫ z, Real.exp (g (Z z)) ∂ν) :=
    integral_exponentialTiltMeasure _ (hg.measurable.comp_aemeasurable
      hweak.aemeasurable_limit) hz _
  rw [heqz]
  apply ht.congr
  intro n
  exact (heqn n).symm

end DGRHS.CLT
#print axioms DGRHS.CLT.exponentialTiltProbability
#print axioms DGRHS.CLT.exponentialTilt_tendstoInDistribution
#check @DGRHS.CLT.exponentialTilt_tendstoInDistribution
