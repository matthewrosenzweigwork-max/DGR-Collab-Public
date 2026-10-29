import LeanResearch.PeriodicAttractiveLogGas.ReferenceExponentialComparison
import LeanResearch.PeriodicAttractiveLogGas.ReferenceConditionalNormalization
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The real log-density change of reference in source lines 2672--2699.
Actual density laws and integrability are retained, including density zeros
and beta zero. The integrated conditional-KL identification and finite-product
tensorization are separate dependencies, not hypotheses of a claimed final
conditional entropy inequality in this unit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.RelativeEntropyReferenceChange

section DensityLaws

variable {Ω : Type*} [MeasurableSpace Ω] {Q P R : Measure Ω} {q r : Ω → ℝ}

/-- A real density is strictly positive almost everywhere under its own
density law. Values zero or negative off that law cause no missing log case. -/
theorem ae_density_pos
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x))) (hq : Measurable q) :
    ∀ᵐ x ∂Q, 0 < q x := by
  rw [hQ]
  apply (ae_withDensity_iff hq.ennreal_ofReal).mpr
  exact Eventually.of_forall fun x hx => by
    by_contra h
    exact hx (ENNReal.ofReal_of_nonpos (le_of_not_gt h))

/-- The actual Radon--Nikodym logarithm equals the explicit log density
almost everywhere under the tilted law. -/
theorem llr_eq_log_density [SigmaFinite P]
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x))) (hq : Measurable q)
    (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) :
    llr Q P =ᵐ[Q] fun x => Real.log (q x) := by
  have hac : Q ≪ P := by rw [hQ]; exact withDensity_absolutelyContinuous _ _
  have hd : Q.rnDeriv P =ᵐ[P] fun x => ENNReal.ofReal (q x) := by
    rw [hQ]
    exact Measure.rnDeriv_withDensity P hq.ennreal_ofReal
  filter_upwards [hac.ae_le hd, hac.ae_le hq0] with x hx h0
  simp only [llr, hx, ENNReal.toReal_ofReal h0]

/-- The true finite KL value of an explicit probability density, without a
boundedness assumption on that density. Log-integrability is explicit. -/
theorem klDiv_eq_log_density [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x))) (hq : Measurable q)
    (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) (hlog : Integrable (fun x => Real.log (q x)) Q) :
    klDiv Q P = ENNReal.ofReal (∫ x, Real.log (q x) ∂Q) := by
  have hac : Q ≪ P := by rw [hQ]; exact withDensity_absolutelyContinuous _ _
  have he := llr_eq_log_density hQ hq hq0
  rw [klDiv_of_ac_of_integrable hac (hlog.congr he.symm), integral_congr_ae he]
  simp

theorem klDiv_ne_top_of_log_density [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x))) (hq : Measurable q)
    (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) (hlog : Integrable (fun x => Real.log (q x)) Q) :
    klDiv Q P ≠ ∞ := by
  rw [klDiv_eq_log_density hQ hq hq0 hlog]
  exact ENNReal.ofReal_ne_top

/-- Strict positivity of the reference density gives the reverse absolute
continuity needed to transfer almost-everywhere bounds to the base law. -/
theorem positive_reference_ac
    (hP : P = R.withDensity (fun x => ENNReal.ofReal (r x))) (hr : Measurable r)
    (hr0 : ∀ x, 0 < r x) : R ≪ P := by
  rw [hP]
  exact withDensity_absolutelyContinuous' hr.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hr0 x)).ne')

/-- Compose the two literal density changes, in the same original space. -/
theorem compose_density
    (hP : P = R.withDensity (fun x => ENNReal.ofReal (r x)))
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hr : Measurable r) (hq : Measurable q) (hr0 : ∀ x, 0 ≤ r x) :
    Q = R.withDensity (fun x => ENNReal.ofReal (q x * r x)) := by
  rw [hQ, hP, ← withDensity_mul _ hr.ennreal_ofReal hq.ennreal_ofReal]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal (r x) * ENNReal.ofReal (q x) = ENNReal.ofReal (q x * r x)
    rw [← ENNReal.ofReal_mul (hr0 x), mul_comm]

/-- The log-density chain rule holds under the actual tilted law, with
the zero-density exceptional set removed by its proved nullity. -/
theorem log_density_chain
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) (hr0 : ∀ x, 0 < r x) :
    (fun x => Real.log (q x * r x)) =ᵐ[Q] fun x => Real.log (q x) + Real.log (r x) := by
  filter_upwards [ae_density_pos hQ hq] with x hx
  exact Real.log_mul hx.ne' (hr0 x).ne'

/-- True real-integral change of reference. No difference of infinities is
taken, and the composed product-reference density need not be bounded. -/
theorem integral_log_density_chain
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) (hr0 : ∀ x, 0 < r x)
    (hlogq : Integrable (fun x => Real.log (q x)) Q)
    (hlogr : Integrable (fun x => Real.log (r x)) Q) :
    Integrable (fun x => Real.log (q x * r x)) Q ∧
    (∫ x, Real.log (q x * r x) ∂Q) =
      (∫ x, Real.log (q x) ∂Q) + ∫ x, Real.log (r x) ∂Q := by
  have he := log_density_chain hQ hq hr0
  exact ⟨(hlogq.add hlogr).congr he.symm,
    (integral_congr_ae he).trans (integral_add hlogq hlogr)⟩

/-- Bounded tilts of the actual probability P have finite KL against P.
Only integrability of the reference log density under Q remains as a
genuine intermediate analytic hypothesis, discharged below for the source. -/
theorem bounded_tilt_change [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hP : P = R.withDensity (fun x => ENNReal.ofReal (r x)))
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hr : Measurable r) (hr0 : ∀ x, 0 < r x) (hq : Measurable q)
    {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K)
    (hlogr : Integrable (fun x => Real.log (r x)) Q) :
    Q = R.withDensity (fun x => ENNReal.ofReal (q x * r x)) ∧
    Integrable (fun x => Real.log (q x)) Q ∧
    Integrable (fun x => Real.log (q x * r x)) Q ∧
    klDiv Q P = ENNReal.ofReal (∫ x, Real.log (q x) ∂Q) ∧
    klDiv Q R = ENNReal.ofReal
      ((∫ x, Real.log (q x) ∂Q) + ∫ x, Real.log (r x) ∂Q) := by
  have hc := compose_density hP hQ hr hq (fun x => (hr0 x).le)
  have hlogq := (RelativeEntropyVariational.bounded_tilt_entropy_eq hQ hq hb).1
  have hlog := integral_log_density_chain hQ hq hr0 hlogq hlogr
  have hq0 := hb.mono fun _ hx => hx.1
  have hqR : ∀ᵐ x ∂R, 0 ≤ q x := (positive_reference_ac hP hr hr0).ae_le hq0
  have hqr0 : ∀ᵐ x ∂R, 0 ≤ q x * r x :=
    hqR.mono fun x hx => mul_nonneg hx (hr0 x).le
  refine ⟨hc, hlogq, hlog.1, klDiv_eq_log_density hQ hq hq0 hlogq, ?_⟩
  rw [klDiv_eq_log_density hc (hq.mul hr) hqr0 hlog.1, hlog.2]

/-- The real value of finite KL, using its actual integrable likelihood
ratio rather than the totalized value of an infinite KL divergence. -/
theorem toReal_klDiv_eq_log_density [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x))) (hq : Measurable q)
    (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) (hlog : Integrable (fun x => Real.log (q x)) Q) :
    (klDiv Q P).toReal = ∫ x, Real.log (q x) ∂Q := by
  have hac : Q ≪ P := by rw [hQ]; exact withDensity_absolutelyContinuous _ _
  have he := llr_eq_log_density hQ hq hq0
  rw [InformationTheory.toReal_klDiv hac (hlog.congr he.symm), integral_congr_ae he]
  simp

/-- Finite real KL changes by the expected log reference density. Both
finiteness conclusions are proved before the real equality is stated. -/
theorem bounded_tilt_real_change [IsProbabilityMeasure R] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hP : P = R.withDensity (fun x => ENNReal.ofReal (r x)))
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hr : Measurable r) (hr0 : ∀ x, 0 < r x) (hq : Measurable q)
    {K : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K)
    (hlogr : Integrable (fun x => Real.log (r x)) Q) :
    klDiv Q P ≠ ∞ ∧ klDiv Q R ≠ ∞ ∧
    (klDiv Q R).toReal = (klDiv Q P).toReal + ∫ x, Real.log (r x) ∂Q := by
  obtain ⟨hc, hqI, hqrI, _, _⟩ := bounded_tilt_change hP hQ hr hr0 hq hb hlogr
  have hq0 := hb.mono fun _ hx => hx.1
  have hqR : ∀ᵐ x ∂R, 0 ≤ q x := (positive_reference_ac hP hr hr0).ae_le hq0
  have hqr0 : ∀ᵐ x ∂R, 0 ≤ q x * r x :=
    hqR.mono fun x hx => mul_nonneg hx (hr0 x).le
  refine ⟨klDiv_ne_top_of_log_density hQ hq hq0 hqI,
    klDiv_ne_top_of_log_density hc (hq.mul hr) hqr0 hqrI, ?_⟩
  rw [toReal_klDiv_eq_log_density hc (hq.mul hr) hqr0 hqrI,
    toReal_klDiv_eq_log_density hQ hq hq0 hqI]
  exact (integral_log_density_chain hQ hq hr0 hqI hlogr).2

/-- An actual square-integrable density has an integrable log under its own
law. This will be applied to the proved one-site L4 density, not assumed as
a conditional entropy endpoint. -/
theorem log_density_integrable_of_memLp_two [IsFiniteMeasure P]
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) (hq0 : ∀ᵐ x ∂P, 0 ≤ q x) (h2 : MemLp q 2 P) :
    Integrable (fun x => Real.log (q x)) Q := by
  apply (RelativeEntropyVariational.integrable_density_iff hQ hq hq0).mpr
  apply ((integrable_const (1 : ℝ)).add h2.integrable_sq).mono'
    (Real.continuous_mul_log.measurable.comp hq).aestronglyMeasurable
  filter_upwards [hq0] with x hx
  simpa only [Real.norm_eq_abs, Pi.add_apply, Function.comp_apply] using!
    RelativeEntropyVariational.abs_mul_log_le_one_add_sq hx

/-- Transfer an already integrable observable to a bounded-density tilt.
The density may vanish, and its bound is needed only almost everywhere. -/
theorem integrable_bounded_tilt [IsFiniteMeasure P] {G : Ω → ℝ}
    (hQ : Q = P.withDensity (fun x => ENNReal.ofReal (q x)))
    (hq : Measurable q) (hG : Measurable G) {K : ℝ}
    (hb : ∀ᵐ x ∂P, 0 ≤ q x ∧ q x ≤ K) (hGi : Integrable G P) :
    Integrable G Q :=
  (RelativeEntropyVariational.integrable_density_iff hQ hq (hb.mono fun _ hx => hx.1)).mpr
    (RelativeEntropyVariational.integrable_bounded_density_mul hq hG hb hGi)

/-- A finite family with a common lower bound cannot hide a nonintegrable
summand inside an integrable sum. The proof dominates the shifted
nonnegative summands by their full sum. -/
theorem integrable_component_of_lower_bound [IsFiniteMeasure P]
    {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {B : ℝ} (hlo : ∀ i x, B ≤ f i x)
    (hs : Integrable (fun x => ∑ i, f i x) P) : ∀ i, Integrable (f i) P := by
  classical
  intro i
  have hdom : Integrable (fun x => (∑ j, f j x) - (Fintype.card ι : ℝ) * B) P :=
    hs.sub (integrable_const _)
  have hm : Measurable (fun x => f i x - B) := (hf i).sub measurable_const
  have hi : Integrable (fun x => f i x - B) P := by
    apply hdom.mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sub_nonneg.mpr (hlo i x))]
      have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j => f j x - B)
        (fun j _ => sub_nonneg.mpr (hlo j x)) (Finset.mem_univ i)
      simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  apply (hi.add (integrable_const B)).congr
  exact Eventually.of_forall fun x => by
    change f i x - B + B = f i x
    ring

end DensityLaws

open MeshCells LabelOccupations CellRestrictions ReferenceResidual ReferenceSelfTerms
  ReferenceDensityChange ReferencePotentialBounds ReferenceExponentialComparison
  ReferenceConditionalNormalization ResidualExponential ResidualNearExponential
  ResidualFarExponential GreenGradientOscillation MovingPoleCalculus

/-- Global bounds on the actual one-body potentials give true integrability
of the self term under every finite law, including arbitrary bounded tilts. -/
theorem selfTerm_integrable {J N : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J N) (Q : Measure (Configuration N)) [IsFiniteMeasure Q] :
    Integrable (selfTerm μ η) Q := by
  have hi (i : Fin N) : Integrable (fun X : Configuration N => potential (μ (η i)) (X i)) Q := by
    apply Integrable.of_bound
      ((ReferenceDensityChange.measurable_potential (μ (η i))).comp
        (measurable_pi_apply i)).aestronglyMeasurable (globalPotentialBound J)
    exact Eventually.of_forall fun X => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using!
        (global_potential_bound hJ (η i) _ (hμ (η i)) (X i)).2
  exact (integrable_finsetSum _ (fun i _ => hi i)).div_const (N : ℝ)

/-- Pointwise log of the strictly positive reference density, with the
source self coefficient retained literally. -/
theorem log_reference_density {J N : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J N) (β : ℝ) (hZ : 0 < referenceNormalizer μ η β)
    (X : Configuration N) :
    Real.log (referenceTilt μ η β X / referenceNormalizer μ η β) =
      β * residualSum μ η X - β * selfTerm μ η X - Real.log (referenceNormalizer μ η β) := by
  simp only [referenceTilt, Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp]

/-- Every source bounded tilt has genuine integrability of the full
reference log density. The beta-weighted residual is used throughout, so
beta zero needs no division by beta or unproved unweighted moment. -/
theorem source_reference_log_integrable {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (ht : 0 ≤ t) (hη : OccupationCap t η)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (Q : Measure (Configuration N)) [IsProbabilityMeasure Q]
    (q : Configuration N → ℝ) (hq : Measurable q) {K : ℝ}
    (hQ : Q = (labelGibbsMeasure hJ η β).withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂labelGibbsMeasure hJ η β, 0 ≤ q X ∧ q X ≤ K) :
    0 < referenceNormalizer μ η β ∧
    Integrable (fun X => β * residualSum μ η X) Q ∧
    Integrable (selfTerm μ η) Q ∧
    Integrable (fun X => Real.log (q X)) Q ∧
    Integrable (fun X => Real.log (referenceTilt μ η β X / referenceNormalizer μ η β)) Q ∧
    (∫ X, Real.log (referenceTilt μ η β X / referenceNormalizer μ η β) ∂Q) =
      (∫ X, β * residualSum μ η X ∂Q) - β * (∫ X, selfTerm μ η X ∂Q) -
        Real.log (referenceNormalizer μ η β) := by
  have hz := referenceNormalizer_pos hJ hN μ η hβ (hβle.trans_lt hsub) hformula
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have hs := selfTerm_integrable hJ μ hμ η Q
  have hr := bounded_tilt_remaining_term hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq hQ hb
  have hY : Integrable (fun X => β * residualSum μ η X) Q := by
    have he : (fun X => (1 / 2 : ℝ) * (2 * β * residualSum μ η X)) =
        fun X => β * residualSum μ η X := by funext X; ring
    simpa only [he] using hr.1.const_mul (1 / 2 : ℝ)
  have hE : Integrable (fun X => β * residualSum μ η X - β * selfTerm μ η X) Q :=
    hY.sub (hs.const_mul β)
  have hlog : Integrable
      (fun X => Real.log (referenceTilt μ η β X / referenceNormalizer μ η β)) Q := by
    simpa only [Pi.sub_apply, log_reference_density μ η β hz] using!
      hE.sub (integrable_const (Real.log (referenceNormalizer μ η β)))
  refine ⟨hz, hY, hs, hr.2.1, hlog, ?_⟩
  simp_rw [log_reference_density μ η β hz]
  rw [integral_sub hE (integrable_const _), integral_sub hY (hs.const_mul β)]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

/-- The actual source KL change of reference. Both KL divergences are finite
before their real values are used; the product-reference density is derived
from the original Gibbs density, with the self term and normalizer retained.
No conditional-KL identification is assumed here. -/
theorem source_kl_change {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N) (ht : 0 ≤ t) (hη : OccupationCap t η)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (Q : Measure (Configuration N)) [IsProbabilityMeasure Q]
    (q : Configuration N → ℝ) (hq : Measurable q) {K : ℝ}
    (hQ : Q = (labelGibbsMeasure hJ η β).withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂labelGibbsMeasure hJ η β, 0 ≤ q X ∧ q X ≤ K) :
    Q = (Measure.pi (fun i => μ (η i))).withDensity (fun X =>
      ENNReal.ofReal (q X * (referenceTilt μ η β X / referenceNormalizer μ η β))) ∧
    Integrable (fun X => Real.log (q X *
      (referenceTilt μ η β X / referenceNormalizer μ η β))) Q ∧
    klDiv Q (labelGibbsMeasure hJ η β) ≠ ∞ ∧
    klDiv Q (Measure.pi (fun i => μ (η i))) ≠ ∞ ∧
    (klDiv Q (Measure.pi (fun i => μ (η i)))).toReal =
      (klDiv Q (labelGibbsMeasure hJ η β)).toReal +
        (∫ X, β * residualSum μ η X ∂Q) - β * (∫ X, selfTerm μ η X ∂Q) -
          Real.log (referenceNormalizer μ η β) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η hβ (hβle.trans_lt hsub)
  have hc := change_of_reference hJ hN μ η hβ (hβle.trans_lt hsub) hformula
  have hi := source_reference_log_integrable hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq hQ hb
  have hm : Measurable (fun X => referenceTilt μ η β X / referenceNormalizer μ η β) :=
    (measurable_referenceTilt μ η β).div_const _
  have hp : ∀ X, 0 < referenceTilt μ η β X / referenceNormalizer μ η β :=
    fun X => div_pos (Real.exp_pos _) hc.2.1
  have hd := bounded_tilt_change hc.2.2 hQ hm hp hq hb hi.2.2.2.2.1
  have hr := bounded_tilt_real_change hc.2.2 hQ hm hp hq hb hi.2.2.2.2.1
  refine ⟨hd.1, hd.2.2.1, hr.1, hr.2.1, ?_⟩
  rw [hr.2.2, hi.2.2.2.2.2]
  ring

/-- At beta zero the literal reference tilt and normalizer are one, and
the actual Gibbs reference identity becomes the product law. No residual
integrability assertion is needed in this endpoint. -/
theorem source_reference_zero {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J N)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (0 * averagePotential μ η z) / cellNormalizer hJ μ η 0 a))) :
    referenceTilt μ η 0 = (fun _ => 1) ∧ referenceNormalizer μ η 0 = 1 ∧
    labelGibbsMeasure hJ η 0 = Measure.pi (fun i => μ (η i)) := by
  have ht : referenceTilt μ η 0 = (fun _ => 1) := by
    funext X
    simp [referenceTilt]
  have hz : referenceNormalizer μ η 0 = 1 := by simp [referenceNormalizer, ht]
  refine ⟨ht, hz, ?_⟩
  have hc := (change_of_reference hJ hN μ η (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) < 4) hformula).2.2
  simpa only [ht, hz, div_one, ENNReal.ofReal_one, withDensity_const, one_smul] using hc

open OneCoordinateConditionals GreenPointWeights

/-- Multiplication by the actual reference-cell density cancels the
one-body centering in the normalized conditional density. The normalizer
identity is proved by the actual density integral; no partition identity or
conditional-law equality is a premise. -/
theorem section_cell_density_identity {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) (β : ℝ)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y) *
      (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β (η i)) =
        pointDensity (meshCellMeasure J hJ (η i)) Y (fun _ => β / (n + 1 : ℕ)) z := by
  let A := Real.exp ((β / (n + 1 : ℕ)) * ∑ j : Fin n,
    (pairAverage (μ (η i)) (μ (η (i.succAbove j))) - potential (μ (η i)) (Y j))) /
      cellNormalizer hJ μ η β (η i)
  have hz := cellNormalizer_pos_of_formula hJ μ η β (η i) (hformula (η i))
  have hA : 0 < A := div_pos (Real.exp_pos _) hz
  have hD : Measurable (fun z => Real.exp (β * averagePotential μ η z) /
      cellNormalizer hJ μ η β (η i)) :=
    ((ReferenceDensityChange.measurable_averagePotential μ η).const_mul β).exp.div_const _
  have hZ : sectionNormalizer μ η i β Y =
      A * ∫ z, OneCoordinateConditionals.sourceWeight β Y z ∂meshCellMeasure J hJ (η i) := by
    unfold sectionNormalizer
    rw [DensityMoments.integral_density (hformula (η i)) hD
      (Eventually.of_forall fun z => div_nonneg (Real.exp_pos _).le hz.le)]
    simp_rw [density_mul_sectionWeight]
    exact integral_const_mul _ _
  change _ = OneCoordinateConditionals.sourceWeight β Y z /
    ∫ u, OneCoordinateConditionals.sourceWeight β Y u ∂meshCellMeasure J hJ (η i)
  rw [mul_comm, ← mul_div_assoc, density_mul_sectionWeight, hZ]
  exact mul_div_mul_left _ _ hA.ne'

/-- Pointwise section log identity at every genuinely finite positive
normalizer. Its beta-weighted form includes beta zero. -/
theorem log_section_density {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (β : ℝ) (Y : Configuration n)
    (hZ : 0 < sectionNormalizer μ η i β Y) (z : Torus) :
    Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y) =
      β * residualSection μ η i Y z - (β / (n + 1 : ℕ)) * potential (μ (η i)) z -
        Real.log (sectionNormalizer μ η i β Y) := by
  simp only [sectionWeight, Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp]

/-- Every admissible fixed outside placement has a genuinely integrable
log density for its actual reference conditional. The proof uses the actual
one-site L4 estimate, the pointwise composed density identity, and the
two-sided reference-cell density bound. Outside coordinates may coincide. -/
theorem source_section_log_integrable {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (ht : t ≤ ConditionalLawEstimates.occupationBound β₀) (hη : OccupationCap t η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    0 < sectionNormalizer μ η i β Y ∧
    Integrable (fun z => Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y))
      (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
        (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y) := by
  let τ := meshCellMeasure J hJ (η i)
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y
  let : IsMarkovKernel (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i) :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  let : IsProbabilityMeasure κ := by dsimp [κ]; infer_instance
  let σ := fun z => Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β (η i)
  let r := fun z => sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y
  have hz := (sectionWeight_integrable hJ μ η hβ hβ₀ hformula hmesh (hη.mono ht) i Y hY).2
  have hc := cellNormalizer_pos_of_formula hJ μ η β (η i) (hformula (η i))
  have hσ : Measurable σ :=
    ((ReferenceDensityChange.measurable_averagePotential μ η).const_mul β).exp.div_const _
  have hσ0 : ∀ z, 0 < σ z := fun z => div_pos (Real.exp_pos _) hc
  have hr : Measurable r := (measurable_sectionWeight μ η i β Y).div_const _
  have hr0 : ∀ z, 0 < r z := fun z => div_pos (Real.exp_pos _) hz
  have hκ : κ = (μ (η i)).withDensity (fun z => ENNReal.ofReal (r z)) :=
    conditionalKernel_eq_reference_density hJ μ η hβ hβ₀ hformula hmesh (hη.mono ht) i Y hY
  have hκτ : κ = τ.withDensity (fun z => ENNReal.ofReal (r z * σ z)) :=
    compose_density (hformula (η i)) hκ hσ hr (fun z => (hσ0 z).le)
  have hpoint := ConditionalLawEstimates.capped_patch_law hJ hβ hβ₀ ht hmesh η hη i Y hY
    (η i) Patch.cell
  have h4 : MemLp (pointDensity τ Y (fun _ => β / (n + 1 : ℕ))) 4 τ := by
    have he := ConditionalLawEstimates.pointDensity_ae_rawDensity hJ
      (ConditionalLawEstimates.mesh_two_le hmesh) (η i) Patch.cell β Y
    exact (memLp_congr_ae he).mpr hpoint.density_memLp
  have h2 : MemLp (fun z => r z * σ z) 2 τ := by
    have he : (fun z => r z * σ z) =ᵐ[τ]
        pointDensity τ Y (fun _ => β / (n + 1 : ℕ)) :=
      Eventually.of_forall fun z => section_cell_density_identity hJ μ η β hformula i Y z
    exact (memLp_congr_ae he).mpr (h4.mono_exponent (by norm_num))
  have hprod := log_density_integrable_of_memLp_two hκτ (hr.mul hσ)
    (Eventually.of_forall fun z => mul_nonneg (hr0 z).le (hσ0 z).le) h2
  have hac : κ ≪ τ := by rw [hκτ]; exact withDensity_absolutelyContinuous _ _
  have hσlog (z : Torus) : Real.log (σ z) =
      β * averagePotential μ η z - Real.log (cellNormalizer hJ μ η β (η i)) := by
    simp only [σ, Real.log_div (Real.exp_ne_zero _) hc.ne', Real.log_exp]
  have hmσlog : Measurable (fun z => Real.log (σ z)) := by
    simp_rw [hσlog]
    exact ((ReferenceDensityChange.measurable_averagePotential μ η).const_mul β).sub measurable_const
  have hiσlog : Integrable (fun z => Real.log (σ z)) κ := by
    apply Integrable.of_bound hmσlog.aestronglyMeasurable 1
    filter_upwards [hac.ae_le (hdensity (η i))] with z hzσ
    have hlo := Real.log_le_log (Real.exp_pos (-1)) hzσ.1
    have hhi := Real.log_le_log (hσ0 z) hzσ.2
    simp only [Real.log_exp] at hlo hhi
    exact abs_le.mpr ⟨hlo, hhi⟩
  have he : (fun z => Real.log (r z)) =ᵐ[κ]
      fun z => Real.log (r z * σ z) - Real.log (σ z) := by
    filter_upwards [log_density_chain hκ hr hσ0] with z hzlog
    linarith only [hzlog]
  refine ⟨hz, ?_⟩
  exact (hprod.sub hiσlog).congr he.symm

/-- The fixed-section source change and lower bound for every bounded
probability tilt of the actual reference conditional. All log and weighted
residual integrability is derived above; the source Jensen lower bound is
applied only after both KL divergences are proved finite. This is a
fixed-placement statement, not an integrated conditional-entropy theorem. -/
theorem source_section_tilt_kl_change {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (ht : t ≤ ConditionalLawEstimates.occupationBound β₀) (hη : OccupationCap t η)
    (i : Fin (n + 1)) (Y : Configuration n) (hY : PrescribedOutside hJ η i Y)
    (Q : Measure Torus) [IsProbabilityMeasure Q] (q : Torus → ℝ) (hq : Measurable q) {K : ℝ}
    (hQ : Q = (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y).withDensity
        (fun z => ENNReal.ofReal (q z)))
    (hb : ∀ᵐ z ∂PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y, 0 ≤ q z ∧ q z ≤ K) :
    let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y
    Integrable (fun z => β * residualSection μ η i Y z) Q ∧
    Integrable (potential (μ (η i))) Q ∧
    Integrable (fun z => Real.log (q z)) Q ∧
    Integrable (fun z => Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y)) Q ∧
    klDiv Q κ ≠ ∞ ∧ klDiv Q (μ (η i)) ≠ ∞ ∧
    (klDiv Q (μ (η i))).toReal = (klDiv Q κ).toReal +
      (∫ z, β * residualSection μ η i Y z ∂Q) -
        (β / (n + 1 : ℕ)) * (∫ z, potential (μ (η i)) z ∂Q) -
          Real.log (sectionNormalizer μ η i β Y) ∧
    (klDiv Q (μ (η i))).toReal - (∫ z, β * residualSection μ η i Y z ∂Q) +
      (β / (n + 1 : ℕ)) * (∫ z, potential (μ (η i)) z ∂Q) -
        (β / (n + 1 : ℕ)) * pairAverage (μ (η i)) (μ (η i)) ≤ (klDiv Q κ).toReal := by
  let κ := PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
    (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i Y
  let : IsMarkovKernel (PositiveProductConditionals.conditionalKernel (μ (η i)) (referenceTilt μ η β)
      (measurable_referenceTilt μ η β) (fun _ => Real.exp_pos _) i) :=
    PositiveProductConditionals.isMarkovKernel_conditionalKernel _ _ _ _ _
  let : IsProbabilityMeasure κ := by dsimp [κ]; infer_instance
  have hi := source_section_log_integrable hJ μ η hβ hβ₀ hformula hdensity hmesh ht hη i Y hY
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have hpot : Integrable (potential (μ (η i))) Q := by
    apply Integrable.of_bound (ReferenceDensityChange.measurable_potential _).aestronglyMeasurable
      (globalPotentialBound J)
    exact Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using (global_potential_bound hJ (η i) _ (hμ (η i)) z).2
  have hr : Measurable (fun z => sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y) :=
    (measurable_sectionWeight μ η i β Y).div_const _
  have hr0 : ∀ z, 0 < sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y :=
    fun z => div_pos (Real.exp_pos _) hi.1
  have hκ : κ = (μ (η i)).withDensity (fun z =>
      ENNReal.ofReal (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y)) :=
    conditionalKernel_eq_reference_density hJ μ η hβ hβ₀ hformula hmesh (hη.mono ht) i Y hY
  have hlog : Integrable
      (fun z => Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y)) Q :=
    integrable_bounded_tilt hQ hq hr.log hb hi.2
  have hR : Integrable (fun z => β * residualSection μ η i Y z) Q := by
    apply ((hlog.add (hpot.const_mul (β / (n + 1 : ℕ)))).add
      (integrable_const (Real.log (sectionNormalizer μ η i β Y)))).congr
    exact Eventually.of_forall fun z => by
      change Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y) +
        (β / (n + 1 : ℕ)) * potential (μ (η i)) z + Real.log (sectionNormalizer μ η i β Y) = _
      rw [log_section_density μ η i β Y hi.1]
      ring
  have hE : Integrable (fun z => β * residualSection μ η i Y z -
      (β / (n + 1 : ℕ)) * potential (μ (η i)) z) Q :=
    hR.sub (hpot.const_mul _)
  have hI : (∫ z, Real.log (sectionWeight μ η i β Y z / sectionNormalizer μ η i β Y) ∂Q) =
      (∫ z, β * residualSection μ η i Y z ∂Q) -
        (β / (n + 1 : ℕ)) * (∫ z, potential (μ (η i)) z ∂Q) -
          Real.log (sectionNormalizer μ η i β Y) := by
    simp_rw [log_section_density μ η i β Y hi.1]
    rw [integral_sub hE (integrable_const _),
      integral_sub hR (hpot.const_mul _)]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  have hc := bounded_tilt_real_change hκ hQ hr hr0 hq hb hlog
  have hEq : (klDiv Q (μ (η i))).toReal = (klDiv Q κ).toReal +
      (∫ z, β * residualSection μ η i Y z ∂Q) -
        (β / (n + 1 : ℕ)) * (∫ z, potential (μ (η i)) z ∂Q) -
          Real.log (sectionNormalizer μ η i β Y) := by
    rw [hc.2.2, hI]
    ring
  refine ⟨hR, hpot, (RelativeEntropyVariational.bounded_tilt_entropy_eq hQ hq hb).1,
    hlog, hc.1, hc.2.1, hEq, ?_⟩
  have hlo := (conditional_normalizer_lower hJ μ hμ η hβ hβ₀ hformula hmesh
    (hη.mono ht) i Y hY).2.2
  linarith only [hEq, hlo]

/-- The logarithmic conditional reference correction is identically zero
at beta zero, at every placement. -/
theorem log_section_density_zero {J n : ℕ} (μ : MeshIndex J → Measure Torus)
    [∀ a, IsProbabilityMeasure (μ a)] (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    Real.log (sectionWeight μ η i 0 Y z / sectionNormalizer μ η i 0 Y) = 0 := by
  simp

/-- Measurability of the actual section evaluated at the removed and
retained coordinates of the same original configuration. -/
theorem measurable_evaluated_residualSection {J n : ℕ}
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) :
    Measurable (fun X : Configuration (n + 1) => residualSection μ η i (removeSite i X) (X i)) := by
  have hm (j : Fin n) : Measurable (fun X : Configuration (n + 1) =>
      residual (μ (η i)) (μ (η (i.succAbove j))) (X i) (X (i.succAbove j))) := by
    have hk : Measurable (Function.uncurry (residual (μ (η i)) (μ (η (i.succAbove j))))) :=
      ResidualDoubleCentering.measurable_doubleCenter (μ (η i)) (μ (η (i.succAbove j)))
        greenKernel measurable_greenKernel
    have hp : Measurable (fun X : Configuration (n + 1) => (X i, X (i.succAbove j))) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply (i.succAbove j))
    simpa only [Function.comp_def, Function.uncurry] using hk.comp hp
  change Measurable (fun X : Configuration (n + 1) =>
    (∑ j : Fin n, residual (μ (η i)) (μ (η (i.succAbove j))) (X i) (X (i.succAbove j))) /
      (n + 1 : ℕ))
  exact (Finset.measurable_sum _ (fun j _ => hm j)).div_const _

/-- Every residual section has a uniform fixed-mesh lower bound, including
all diagonal/collision placements of its outside particles. -/
theorem residualSection_lower_bound {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (Y : Configuration n) (z : Torus) :
    -(greenLowerConstant + 3 * globalPotentialBound J) ≤ residualSection μ η i Y z := by
  let D := greenLowerConstant + 3 * globalPotentialBound J
  have hD : 0 ≤ D := add_nonneg greenLowerConstant_pos.le
    (mul_nonneg (by norm_num) (globalPotentialBound_nonneg J))
  have hr (j : Fin n) : -D ≤ residual (μ (η i)) (μ (η (i.succAbove j))) z (Y j) := by
    have hp₁ := abs_le.mp (global_potential_bound hJ (η i) _ (hμ (η i)) (Y j)).2
    have hp₂ := abs_le.mp (global_potential_bound hJ (η (i.succAbove j)) _
      (hμ (η (i.succAbove j))) z).2
    have hc := abs_le.mp (global_pairAverage_bound hJ (η (i.succAbove j))
      (μ (η i)) (μ (η (i.succAbove j))) (hμ (η (i.succAbove j)))).2
    have hg : -greenLowerConstant ≤ greenKernel z (Y j) := green_lower_bound _
    rw [residual_eq_source_order]
    dsimp [D]
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) fun j _ => hr j
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  change -D ≤ (∑ j : Fin n, residual (μ (η i)) (μ (η (i.succAbove j))) z (Y j)) / (n + 1 : ℕ)
  apply (le_div_iff₀ hn).mpr
  push_cast
  nlinarith only [hs, hD]

/-- Once the genuinely integrable weighted full residual has been proved,
every weighted section is integrable under the same original joint law,
and the finite sum can be integrated with the exact factor two. -/
theorem weighted_section_integrals_of_residual_integrable {J n : ℕ} (hJ : 0 < J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (hμ : ∀ a, μ a ≤ ENNReal.ofReal (Real.exp 1) • meshCellMeasure J hJ a)
    (η : LabelVector J (n + 1)) {β : ℝ} (hβ : 0 ≤ β)
    (Q : Measure (Configuration (n + 1))) [IsFiniteMeasure Q]
    (hY : Integrable (fun X => β * residualSum μ η X) Q) :
    (∀ i, Integrable (fun X => β * residualSection μ η i (removeSite i X) (X i)) Q) ∧
    (∑ i, ∫ X, β * residualSection μ η i (removeSite i X) (X i) ∂Q) =
      2 * ∫ X, β * residualSum μ η X ∂Q := by
  have he (X : Configuration (n + 1)) :
      (∑ i, β * residualSection μ η i (removeSite i X) (X i)) = 2 * (β * residualSum μ η X) := by
    rw [← Finset.mul_sum, sum_residualSection hJ μ hμ η X]
    ring
  have hs : Integrable (fun X => ∑ i, β * residualSection μ η i (removeSite i X) (X i)) Q :=
    (hY.const_mul 2).congr (Eventually.of_forall fun X => (he X).symm)
  have hlo (i : Fin (n + 1)) (X : Configuration (n + 1)) :
      -(β * (greenLowerConstant + 3 * globalPotentialBound J)) ≤
        β * residualSection μ η i (removeSite i X) (X i) := by
    simpa only [mul_neg] using mul_le_mul_of_nonneg_left
      (residualSection_lower_bound hJ μ hμ η i (removeSite i X) (X i)) hβ
  have hi := integrable_component_of_lower_bound
    (fun i X => β * residualSection μ η i (removeSite i X) (X i))
    (fun i => (measurable_evaluated_residualSection μ η i).const_mul β) hlo hs
  refine ⟨hi, ?_⟩
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  exact integral_const_mul _ _

/-- Full source bounded-tilt endpoint for the finite residual sum. Its
weighted moment premise is discharged by the actual exponential estimate
under the original Gibbs law, with the same original particle count. -/
theorem source_weighted_section_integrals {J n : ℕ} (hJ : 0 < J) (hN : 2 ≤ n + 1)
    {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (μ : MeshIndex J → Measure Torus) [∀ a, IsProbabilityMeasure (μ a)]
    (η : LabelVector J (n + 1)) (ht : 0 ≤ t) (hη : OccupationCap t η)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hformula : ∀ a, μ a = (meshCellMeasure J hJ a).withDensity (fun z =>
      ENNReal.ofReal (Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a)))
    (hdensity : ∀ a, ∀ᵐ z ∂meshCellMeasure J hJ a,
      Real.exp (-1) ≤ Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ∧
      Real.exp (β * averagePotential μ η z) / cellNormalizer hJ μ η β a ≤ Real.exp 1)
    (Q : Measure (Configuration (n + 1))) [IsProbabilityMeasure Q]
    (q : Configuration (n + 1) → ℝ) (hq : Measurable q) {K : ℝ}
    (hQ : Q = (labelGibbsMeasure hJ η β).withDensity (fun X => ENNReal.ofReal (q X)))
    (hb : ∀ᵐ X ∂labelGibbsMeasure hJ η β, 0 ≤ q X ∧ q X ≤ K) :
    (∀ i, Integrable (fun X => β * residualSection μ η i (removeSite i X) (X i)) Q) ∧
    (∑ i, ∫ X, β * residualSection μ η i (removeSite i X) (X i) ∂Q) =
      2 * ∫ X, β * residualSum μ η X ∂Q := by
  have hμ := source_reference_domination hJ μ η β hformula hdensity
  have hi := source_reference_log_integrable hJ hN hβ hβle hsub hC hk hmesh μ η ht hη hcap
    hformula hdensity Q q hq hQ hb
  exact weighted_section_integrals_of_residual_integrable hJ μ hμ η hβ Q hi.2.1

end PeriodicAttractiveLogGas.RelativeEntropyReferenceChange
