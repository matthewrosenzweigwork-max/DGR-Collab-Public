/- Source one-body LLN: proper L1 only, including AE measurable representatives.
All iid/product laws and source-integral identification are constructed. -/
import DGRHS.CLT.FiniteIIDFeaturesCLT
import Mathlib.Probability.StrongLaw
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

lemma tendstoInMeasure_iid_average_measurable (F : S → ℝ) (hm : Measurable F)
    (hi : Integrable F μ) :
    TendstoInMeasure (Measure.infinitePi (fun _ : ℕ => μ))
      (fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F (ω i)) atTop
      (fun _ => ∫ x, F x ∂μ) := by
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  have hid : ∀ n, IdentDistrib (fun ω : ℕ → S => F (ω n)) (fun ω => F (ω 0)) P P :=
    fun n => (iid_feature_identDistrib μ F hm n).trans (iid_feature_identDistrib μ F hm 0).symm
  have hind : iIndepFun (fun n (ω : ℕ → S) => F (ω n)) P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => F) (fun _ => hm)
  have hint : Integrable (fun ω : ℕ → S => F (ω 0)) P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0).integrable_comp_of_integrable hi
  have hsl := strong_law_ae (fun n (ω : ℕ → S) => F (ω n)) hint
    (fun i j hij => hind.indepFun hij) hid
  rw [(iid_feature_identDistrib μ F hm 0).integral_eq] at hsl
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    apply Measurable.aestronglyMeasurable
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact hm.comp (measurable_pi_apply i)
  · simpa only [smul_eq_mul] using hsl

lemma tendstoInMeasure_iid_average_L1 (F : S → ℝ) (hi : Integrable F μ) :
    TendstoInMeasure (Measure.infinitePi (fun _ : ℕ => μ))
      (fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, F (ω i)) atTop
      (fun _ => ∫ x, F x ∂μ) := by
  let G := hi.aestronglyMeasurable.mk F
  have hG : Measurable G := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hFG : F =ᵐ[μ] G := hi.aestronglyMeasurable.ae_eq_mk
  have hiG : Integrable G μ := hi.congr hFG
  have ht := tendstoInMeasure_iid_average_measurable μ G hG hiG
  rw [← integral_congr_ae hFG] at ht
  apply ht.congr_left
  intro n
  have heq : ∀ i : ℕ, (fun ω : ℕ → S => F (ω i)) =ᵐ[Measure.infinitePi (fun _ : ℕ => μ)]
      fun ω => G (ω i) := fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i).quasiMeasurePreserving.ae_eq_comp hFG
  filter_upwards [ae_all_iff.mpr heq] with ω hω
  congr 1
  exact Finset.sum_congr rfl (fun i _ => (hω i).symm)
end DGRHS.CLT
#print axioms DGRHS.CLT.tendstoInMeasure_iid_average_measurable
#print axioms DGRHS.CLT.tendstoInMeasure_iid_average_L1
#check @DGRHS.CLT.tendstoInMeasure_iid_average_L1
