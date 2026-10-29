import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Martingale.Basic
import Mathlib.Tactic

/-! Conditional Brownian increments for a SUPPLIED full filtration.
The driver law is native IsPreBrownianReal, and the independence hypothesis
is the original filtered Brownian property relative to that filtration.
It is not restricted to the natural filtration of one scalar coordinate.
The argument adapts the elementary conditioning calculation in Raphael
Coelho's Apache-2.0 MathFin BrownianMartingale/PointwiseBracket at revision
f085fd572075c934827f1eb92c4a085941cd21e5; immutable source/license evidence
is in records/commutator/astra-stochastic-native-reassessment.
These lemmas are elementary stochastic groundwork, not an Ito integral
construction or a finite-N particle martingale verdict. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sourceRiesz_conditional_independent_transform
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m≤mΩ)
    (Y : Ω→ℝ) (hY : Measurable[mΩ] Y)
    (hi : Indep (MeasurableSpace.comap Y (borel ℝ)) m P)
    (g : ℝ→ℝ) (hg : Measurable g) :
    (P[fun ω=>g (Y ω) | m])=ᵐ[P] fun _=>∫ ω,g (Y ω) ∂P := by
  haveI : IsFiniteMeasure (P.trim hm) := MeasureTheory.isFiniteMeasure_trim _
  have hc : Measurable[MeasurableSpace.comap Y (borel ℝ)] (fun ω=>g (Y ω)) :=
    hg.comp (Measurable.of_comap_le le_rfl)
  exact condExp_indep_eq hY.comap_le hm hc.stronglyMeasurable hi

theorem sourceRiesz_brownian_increment_conditional
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBm : ∀ r,Measurable (B r))
    (s t : ℝ≥0) (hst : s≤t)
    (hind : Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P) :
    MemLp (fun ω=>B t ω-B s ω) 2 P ∧
    (P[fun ω=>B t ω-B s ω | F s])=ᵐ[P] (fun _=>0) ∧
    (P[fun ω=>(B t ω-B s ω)^2 | F s])=ᵐ[P] (fun _=>(t:ℝ)-(s:ℝ)) := by
  have hLaw := hB.hasLaw_sub t s
  have hL2 : MemLp (fun ω=>B t ω-B s ω) 2 P := hLaw.hasGaussianLaw.memLp_two
  have hmean : (∫ ω,B t ω-B s ω ∂P)=0 := by
    change (∫ ω,(B t-B s) ω ∂P)=0
    rw [hLaw.integral_eq,integral_id_gaussianReal]
  have hsq : (∫ ω,(B t ω-B s ω)^2 ∂P)=(t:ℝ)-(s:ℝ) := by
    have hv := hLaw.variance_eq
    rw [variance_id_gaussianReal,variance_eq_integral hLaw.aemeasurable] at hv
    simp only [Pi.sub_apply] at hv
    simp only [hmean,sub_zero,coe_nndist] at hv
    change (∫ ω,(B t ω-B s ω)^2 ∂P)=|(t:ℝ)-(s:ℝ)| at hv
    rw [abs_of_nonneg (sub_nonneg.mpr (show (s:ℝ)≤(t:ℝ) from hst))] at hv
    exact hv
  refine ⟨hL2,?_,?_⟩
  · simpa only [id_eq,hmean] using sourceRiesz_conditional_independent_transform P (F s) (F.le s)
      (fun ω=>B t ω-B s ω) ((hBm t).sub (hBm s)) hind id measurable_id
  · have he := sourceRiesz_conditional_independent_transform P (F s) (F.le s)
      (fun ω=>B t ω-B s ω) ((hBm t).sub (hBm s)) hind (fun x=>x^2) (measurable_id.pow_const 2)
    filter_upwards [he] with ω hh
    exact hh.trans hsq

theorem sourceRiesz_brownian_adapted_step
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBm : ∀ r,Measurable (B r))
    (s t : ℝ≥0) (hst : s≤t)
    (hind : Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)
    (H : Ω→ℝ) (hH : StronglyMeasurable[F s] H) (K : ℝ) (hK : 0≤K)
    (hb : ∀ᵐ ω ∂P,|H ω|≤K) :
    Integrable (fun ω=>H ω*(B t ω-B s ω)) P ∧
    Integrable (fun ω=>(H ω*(B t ω-B s ω))^2) P ∧
    (P[fun ω=>H ω*(B t ω-B s ω) | F s])=ᵐ[P] (fun _=>0) ∧
    (P[fun ω=>(H ω*(B t ω-B s ω))^2 | F s])=ᵐ[P]
      (fun ω=>H ω^2*((t:ℝ)-(s:ℝ))) := by
  obtain ⟨hL2,hmean,hsq⟩ := sourceRiesz_brownian_increment_conditional P F B hB hBm s t hst hind
  have hΔi := hL2.integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hHs : AEStronglyMeasurable H P := (hH.mono (F.le s)).aestronglyMeasurable
  have hbn : ∀ᵐ ω ∂P,‖H ω‖≤K := by simpa only [Real.norm_eq_abs] using hb
  have hbsq : ∀ᵐ ω ∂P,‖H ω^2‖≤K^2 := by
    filter_upwards [hb] with ω hh
    simpa only [Real.norm_eq_abs,abs_pow] using pow_le_pow_left₀ (abs_nonneg (H ω)) hh 2
  have hi := hΔi.bdd_mul hHs hbn
  have hi2 := hL2.integrable_sq.bdd_mul (hHs.pow 2) hbsq
  refine ⟨hi,?_,?_,?_⟩
  · simpa only [Pi.mul_apply,Pi.pow_apply,mul_pow] using hi2
  · have he := condExp_stronglyMeasurable_mul_of_bound (F.le s) hH hΔi K hbn
    change (P[fun ω=>H ω*(B t ω-B s ω) | F s])=ᵐ[P]
      (fun ω=>H ω*(P[fun ω=>B t ω-B s ω | F s]) ω) at he
    filter_upwards [he,hmean] with ω hh hz
    simpa only [hz,mul_zero] using hh
  · have he := condExp_stronglyMeasurable_mul_of_bound (F.le s) (hH.pow 2)
      hL2.integrable_sq (K^2) hbsq
    change (P[fun ω=>H ω^2*(B t ω-B s ω)^2 | F s])=ᵐ[P]
      (fun ω=>H ω^2*(P[fun ω=>(B t ω-B s ω)^2 | F s]) ω) at he
    simp_rw [←mul_pow] at he
    filter_upwards [he,hsq] with ω hh hs
    simpa only [hs] using hh

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_conditional_independent_transform
#print axioms DGRHS.Commutator.sourceRiesz_conditional_independent_transform
#check @DGRHS.Commutator.sourceRiesz_brownian_increment_conditional
#print axioms DGRHS.Commutator.sourceRiesz_brownian_increment_conditional
#check @DGRHS.Commutator.sourceRiesz_brownian_adapted_step
#print axioms DGRHS.Commutator.sourceRiesz_brownian_adapted_step
