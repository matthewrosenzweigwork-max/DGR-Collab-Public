import DGRHS.Commutator.SourceLogTransportEnergy
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace DGRHS.Commutator
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

def transportEmpiricalLaw (N : ℕ) (x : Fin N → X) : Measure X :=
  (N : ℝ≥0)⁻¹ • Measure.sum (fun i : Fin N => Measure.dirac (x i))

instance transportEmpiricalLaw_finite (N : ℕ) (x : Fin N → X) :
    IsFiniteMeasure (transportEmpiricalLaw N x) := by
  unfold transportEmpiricalLaw
  infer_instance

omit [MeasurableSingletonClass X] in
lemma transportEmpiricalLaw_probability {N : ℕ} (hN : 0 < N) (x : Fin N → X) :
    IsProbabilityMeasure (transportEmpiricalLaw N x) := by
  constructor
  have hm : (Measure.sum (fun i : Fin N => Measure.dirac (x i))) univ = (N : ℝ≥0∞) := by simp
  rw [transportEmpiricalLaw, Measure.coe_nnreal_smul_apply, hm]
  change (↑((N : ℝ≥0)⁻¹) : ℝ≥0∞) * ↑(N : ℝ≥0) = 1
  rw [← ENNReal.coe_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne')]
  rfl

lemma integral_transportEmpiricalLaw (N : ℕ) (x : Fin N → X) (f : X → ℝ)
    (hf : Measurable f) (L : ℝ) (hb : ∀ z, |f z| ≤ L) :
    (∫ z, f z ∂transportEmpiricalLaw N x) = (N : ℝ)⁻¹ * ∑ i : Fin N, f (x i) := by
  have hi : Integrable f (Measure.sum (fun i : Fin N => Measure.dirac (x i))) :=
    (integrable_const L).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z)
  rw [transportEmpiricalLaw, integral_smul_nnreal_measure, integral_sum_measure hi]
  simp [tsum_fintype, NNReal.smul_def, NNReal.coe_inv]

/-- Excluding spatial collision is exact for the zero representative under any measure. -/
lemma integral_restrict_offCollision {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure (E × E)) (n : ℕ) (v : E → E) :
    (∫ p in {p : E × E | p.1 ≠ p.2}, sourceLogTransportKernel n v p ∂ν) =
      ∫ p, sourceLogTransportKernel n v p ∂ν := by
  classical
  have hs : MeasurableSet {p : E × E | p.1 ≠ p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  rw [← integral_indicator hs]
  congr 1
  funext p
  by_cases hp : p.1 = p.2 <;> simp [Set.indicator, hp, sourceLogTransportKernel]

/-- Direct product Fubini and actual empirical atoms, retaining repeated configurations. -/
lemma integral_transportEmpirical_pair (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : X × X → ℝ) (hh : Measurable h)
    (L : ℝ) (hb : ∀ z, |h z| ≤ L) (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    (∫ p, h p ∂(transportEmpiricalLaw N x).prod ν) =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∫ b, h (x i,b) ∂ν := by
  have := transportEmpiricalLaw_probability hN x
  have hi := integrable_of_abs_bound ((transportEmpiricalLaw N x).prod ν) hh hb
  rw [integral_prod _ hi]
  exact integral_transportEmpiricalLaw N x _ hh.stronglyMeasurable.integral_prod_right'.measurable
    L (fun a => abs_integral_le_bound ν
      (hh.comp (measurable_const.prodMk measurable_id)) (fun b => hb (a,b)))

lemma integral_transportEmpirical_square (h : X × X → ℝ) (hh : Measurable h)
    (L : ℝ) (hb : ∀ z, |h z| ≤ L) (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    (∫ p, h p ∂(transportEmpiricalLaw N x).prod (transportEmpiricalLaw N x)) =
      ((N : ℝ)^2)⁻¹ * ∑ i : Fin N, ∑ j : Fin N, h (x i,x j) := by
  have := transportEmpiricalLaw_probability hN x
  rw [integral_transportEmpirical_pair (transportEmpiricalLaw N x) (transportEmpiricalLaw N x)
    h hh L hb N hN x]
  have hrow (a : X) : (∫ b, h (a,b) ∂transportEmpiricalLaw N x) =
      (N : ℝ)⁻¹ * ∑ j : Fin N, h (a,x j) :=
    integral_transportEmpiricalLaw N x _
      (hh.comp (measurable_const.prodMk measurable_id)) L (fun b => hb (a,b))
  simp_rw [hrow]
  rw [← Finset.mul_sum]
  simp only [pow_two, mul_inv_rev]
  ring

/-- The four genuine probability integrals defining the signed empirical square equal literal An. -/
theorem sourceTransportEnergy_empirical_integrals (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (L : ℝ) (hb : ∀ z, |h z| ≤ L)
    (hs : ∀ a b, h (a,b) = h (b,a)) (hz : ∀ a, h (a,a) = 0)
    (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    sourceTransportEnergy μ h N x =
      (∫ p, h p ∂(transportEmpiricalLaw N x).prod (transportEmpiricalLaw N x)) -
      (∫ p, h p ∂(transportEmpiricalLaw N x).prod μ) -
      (∫ p, h p ∂μ.prod (transportEmpiricalLaw N x)) + (∫ p, h p ∂μ.prod μ) := by
  rw [sourceTransportEnergy_raw μ h hs N hN,
    integral_transportEmpirical_square h hh L hb N hN x,
    integral_transportEmpirical_pair μ μ h hh L hb N hN x]
  have hswap : (∫ p, h p ∂μ.prod (transportEmpiricalLaw N x)) =
      ∫ p, h p ∂(transportEmpiricalLaw N x).prod μ := by
    rw [← integral_prod_swap]
    congr 1
    funext p
    exact hs p.2 p.1
  rw [hswap, integral_transportEmpirical_pair μ μ h hh L hb N hN x]
  have hsum : DGRHS.CanonicalVariance.offDiagonalSum h x =
      ∑ i : Fin N, ∑ j : Fin N, h (x i,x j) := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    have hdiag := Finset.sum_union (f := fun p : Fin N × Fin N => h (x p.1,x p.2))
      (Finset.disjoint_diag_offDiag (Finset.univ : Finset (Fin N)))
    rw [Finset.diag_union_offDiag, Finset.sum_product] at hdiag
    have hd : (∑ p ∈ (Finset.univ : Finset (Fin N)).diag, h (x p.1,x p.2)) = 0 := by
      simp [Finset.diag, hz]
    rw [hd, zero_add] at hdiag
    exact hdiag.symm
  rw [hsum]
  unfold DGRHS.potential
  ring

section Physical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma integrable_sourceLogTransport_kernel_pair (n : ℕ) (hn : 0 < n)
    {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (sourceLogTransportKernel n v) (μ.prod ν) := by
  obtain ⟨C, _, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  exact integrable_of_abs_bound (μ.prod ν) (measurable_sourceLogTransportKernel n hv) (hb hv)

/-- Literal offcollision signed empirical-square observable, with every physical hypothesis derived. -/
theorem sourceLogTransportEnergy_offCollision (n : ℕ) (hn : 0 < n)
    {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (μ : Measure E) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0 < N) (x : Fin N → E) :
    sourceTransportEnergy μ (sourceLogTransportKernel n v) N x =
      (∫ p in {p : E × E | p.1 ≠ p.2}, sourceLogTransportKernel n v p
        ∂(transportEmpiricalLaw N x).prod (transportEmpiricalLaw N x)) -
      (∫ p in {p : E × E | p.1 ≠ p.2}, sourceLogTransportKernel n v p
        ∂(transportEmpiricalLaw N x).prod μ) -
      (∫ p in {p : E × E | p.1 ≠ p.2}, sourceLogTransportKernel n v p
        ∂μ.prod (transportEmpiricalLaw N x)) +
      (∫ p in {p : E × E | p.1 ≠ p.2}, sourceLogTransportKernel n v p ∂μ.prod μ) := by
  simp_rw [integral_restrict_offCollision]
  obtain ⟨C, _, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  apply sourceTransportEnergy_empirical_integrals μ _ (measurable_sourceLogTransportKernel n hv)
    (C * (K : ℝ) ^ n) (hb hv)
    (fun a b => (sourceLogTransportKernel_swap n v (a,b)).symm) _ N hN x
  intro a
  simp [sourceLogTransportKernel]
end Physical

#print axioms integrable_sourceLogTransport_kernel_pair
#print axioms sourceLogTransportEnergy_offCollision
#check @sourceLogTransportEnergy_offCollision
#print axioms integral_restrict_offCollision
#print axioms integral_transportEmpirical_square
#print axioms sourceTransportEnergy_empirical_integrals
#check @sourceTransportEnergy_empirical_integrals
end DGRHS.Commutator
