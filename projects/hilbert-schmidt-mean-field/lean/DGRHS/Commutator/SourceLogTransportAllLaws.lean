/- Global physical transport measurability and properness for arbitrary
probability competitors, including competitors concentrated on collisions. -/
import DGRHS.Commutator.SourceLogTransportEmpirical
import DGRHS.CLT.SourceEnergyMeasurable
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator

theorem stronglyMeasurable_sourceTransportEnergy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (h : X × X → ℝ)
    (hh : Measurable h) (N : ℕ) :
    StronglyMeasurable (sourceTransportEnergy μ h N) := by
  have hc := DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ h hh.stronglyMeasurable
  have hp : StronglyMeasurable (DGRHS.potential μ (fun a b => h (a,b))) :=
    hh.stronglyMeasurable.integral_prod_right'
  exact (DGRHS.CLT.stronglyMeasurable_sourceCanonicalModulatedEnergy _ _ _ hc hp N).const_mul 2

theorem abs_sourceTransportEnergy_le {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (L : ℝ) (hb : ∀ z, |h z| ≤ L)
    (hs : ∀ a b, h (a,b) = h (b,a)) (hz : ∀ a, h (a,a) = 0)
    (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    |sourceTransportEnergy μ h N x| ≤ 4 * L := by
  let e := transportEmpiricalLaw N x
  have he : IsProbabilityMeasure e := transportEmpiricalLaw_probability hN x
  have h1 := abs_integral_le_bound (e.prod e) hh hb
  have h2 := abs_integral_le_bound (e.prod μ) hh hb
  have h3 := abs_integral_le_bound (μ.prod e) hh hb
  have h4 := abs_integral_le_bound (μ.prod μ) hh hb
  rw [sourceTransportEnergy_empirical_integrals μ h hh L hb hs hz N hN x]
  have ht1 := abs_sub (∫ p, h p ∂e.prod e) (∫ p, h p ∂e.prod μ)
  have ht2 := abs_sub ((∫ p, h p ∂e.prod e) - (∫ p, h p ∂e.prod μ))
    (∫ p, h p ∂μ.prod e)
  have ht3 := abs_add_le ((∫ p, h p ∂e.prod e) - (∫ p, h p ∂e.prod μ) -
    (∫ p, h p ∂μ.prod e)) (∫ p, h p ∂μ.prod μ)
  change |(∫ p, h p ∂e.prod e) - (∫ p, h p ∂e.prod μ) -
    (∫ p, h p ∂μ.prod e) + (∫ p, h p ∂μ.prod μ)| ≤ 4 * L
  linarith

theorem sourceLogTransport_all_law_proper {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (n : ℕ) (hn : 0 < n) {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (μ : Measure E) [IsProbabilityMeasure μ] (N : ℕ) (hN : 0 < N) :
    StronglyMeasurable (fun x : Fin N → E =>
      (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x) ∧
    ∃ A : ℝ, (∀ x, |(N : ℝ) * sourceTransportEnergy μ
      (sourceLogTransportKernel n v) N x| ≤ A) ∧
      ∀ (ν : Measure (Fin N → E)) [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy μ
        (sourceLogTransportKernel n v) N x) ν := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  have hm := measurable_sourceLogTransportKernel n hv
  have ha := (stronglyMeasurable_sourceTransportEnergy μ _ hm N).const_mul (N : ℝ)
  let A := (N : ℝ) * (4 * (C * (K : ℝ)^n))
  have hab (x : Fin N → E) : |(N : ℝ) * sourceTransportEnergy μ
      (sourceLogTransportKernel n v) N x| ≤ A := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    exact abs_sourceTransportEnergy_le μ _ hm _ (hb hv)
      (fun a b => (sourceLogTransportKernel_swap n v (a,b)).symm)
      (fun a => by simp [sourceLogTransportKernel]) N hN x
  refine ⟨ha, A, hab, ?_⟩
  intro ν hν
  exact integrable_of_abs_bound ν ha.measurable hab

end DGRHS.Commutator
#check @DGRHS.Commutator.stronglyMeasurable_sourceTransportEnergy
#check @DGRHS.Commutator.abs_sourceTransportEnergy_le
#check @DGRHS.Commutator.sourceLogTransport_all_law_proper
#print axioms DGRHS.Commutator.stronglyMeasurable_sourceTransportEnergy
#print axioms DGRHS.Commutator.abs_sourceTransportEnergy_le
#print axioms DGRHS.Commutator.sourceLogTransport_all_law_proper
