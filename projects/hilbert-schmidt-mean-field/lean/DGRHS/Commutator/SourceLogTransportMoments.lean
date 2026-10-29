import DGRHS.Commutator.SourceLogTransportMeasurable
import DGRHS.Attractive.CanonicalExponential
import DGRHS.Gaussian.HoeffdingLinearity

noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator
variable {X : Type*} [MeasurableSpace X]

/-- Bounded measurable kernels have genuine proper sections and pair integrals. -/
lemma integrable_of_abs_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {L : ℝ} (hb : ∀ x, |f x| ≤ L) :
    Integrable f μ :=
  (integrable_const L).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma abs_integral_le_bound (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {L : ℝ} (hb : ∀ x, |f x| ≤ L) :
    |∫ x, f x ∂μ| ≤ L := by
  have hi := integrable_of_abs_bound μ hf hb
  calc
    _ ≤ ∫ x, |f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _ : X, L ∂μ := integral_mono_ae hi.abs (integrable_const L)
      (Filter.Eventually.of_forall hb)
    _ = L := by simp

lemma bounded_kernel_rowFactorial (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ z, |h z| ≤ L) : DGRHS.Attractive.RowFactorialMoments μ h L := by
  have hp (p : ℕ) (y : X) : ∀ x, |h (x,y)| ^ p ≤ L ^ p :=
    fun x => pow_le_pow_left₀ (abs_nonneg _) (hb _) p
  have hm (p : ℕ) (y : X) : Measurable (fun x => |h (x,y)| ^ p) :=
    (continuous_abs.measurable.comp (hh.comp (measurable_id.prodMk measurable_const))).pow_const p
  have hi (p : ℕ) (y : X) : Integrable (fun x => |h (x,y)| ^ p) μ :=
    integrable_of_abs_bound μ (hm p y) (L := L ^ p) (fun x => by
      simpa only [abs_pow, abs_abs] using hp p y x)
  refine ⟨hL, fun p _ y => hi p y, ?_⟩
  intro p _ y
  have hbint : (∫ x, |h (x,y)| ^ p ∂μ) ≤ L ^ p := by
    simpa using integral_mono_ae (hi p y) (integrable_const (L ^ p))
      (Filter.Eventually.of_forall (hp p y))
  have hfac : (1 : ℝ) ≤ (p.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_pos p)
  exact hbint.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hfac (pow_nonneg hL p))

lemma abs_hoeffdingCentered_le (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (L : ℝ) (hb : ∀ z, |h z| ≤ L) :
    ∀ z, |DGRHS.Gaussian.hoeffdingCentered μ h z| ≤ 4 * L := by
  have hp (x : X) := abs_integral_le_bound μ
    (hh.comp (measurable_const.prodMk measurable_id)) (fun y => hb (x,y))
  have hq (y : X) := abs_integral_le_bound μ
    (hh.comp (measurable_id.prodMk measurable_const)) (fun x => hb (x,y))
  have hm := abs_integral_le_bound (μ.prod μ) hh hb
  intro z
  unfold DGRHS.Gaussian.hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change |h z - (∫ y, h (z.1,y) ∂μ) - (∫ x, h (x,z.2) ∂μ) +
    (∫ p, h p ∂μ.prod μ)| ≤ 4 * L
  exact (abs_add_le _ _).trans (by
    have h1 := abs_sub (h z - (∫ y, h (z.1,y) ∂μ)) (∫ x, h (x,z.2) ∂μ)
    have h2 := abs_sub (h z) (∫ y, h (z.1,y) ∂μ)
    have hpx : |∫ y, h (z.1,y) ∂μ| ≤ L := hp z.1
    have hqy : |∫ x, h (x,z.2) ∂μ| ≤ L := hq z.2
    linarith [hb z])

section Physical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Actual proper canonical factorial rows of the physical contracted logarithmic derivative. -/
theorem exists_sourceLogTransport_centered_rows (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      ∀ (μ : Measure E) [IsProbabilityMeasure μ],
      DGRHS.Attractive.RowFactorialMoments μ
        (DGRHS.Gaussian.hoeffdingCentered μ (sourceLogTransportKernel n v))
        (4 * C * (K : ℝ) ^ n) := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  refine ⟨C, hC, ?_⟩
  intro K v hv μ hμ
  have hm := measurable_sourceLogTransportKernel n hv
  have hc := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ _ hm.stronglyMeasurable).measurable
  apply bounded_kernel_rowFactorial μ _ hc _ (by positivity)
  intro z
  simpa only [mul_assoc] using abs_hoeffdingCentered_le μ _ hm _ (hb hv) z

/-- Proper all-particle canonical exponential moment with the actual physical derivative kernel. -/
theorem exists_sourceLogTransport_canonical_exponential (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      ∀ (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ),
      |t| * (DGRHS.Attractive.attractiveMomentConstant * (4 * C * (K : ℝ) ^ n)) < 1 →
      ∀ N : ℕ,
      Integrable (fun x : Fin N → E => Real.exp (t *
        DGRHS.Attractive.attractiveNormalizedStatistic N
          (DGRHS.Gaussian.hoeffdingCentered μ (sourceLogTransportKernel n v)) x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, Real.exp (t * DGRHS.Attractive.attractiveNormalizedStatistic N
        (DGRHS.Gaussian.hoeffdingCentered μ (sourceLogTransportKernel n v)) x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
        2 / (1 - (t * (DGRHS.Attractive.attractiveMomentConstant *
          (4 * C * (K : ℝ) ^ n))) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  refine ⟨C, hC, ?_⟩
  intro K v hv μ hμ t ht N
  let h := sourceLogTransportKernel n v
  have hm : Measurable h := measurable_sourceLogTransportKernel n hv
  have hi : Integrable h (μ.prod μ) := integrable_of_abs_bound (μ.prod μ) hm (hb hv)
  have hc := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ h hm.stronglyMeasurable).measurable
  have hr := bounded_kernel_rowFactorial μ _ hc (4 * C * (K : ℝ) ^ n) (by positivity)
    (fun z => by simpa only [mul_assoc] using abs_hoeffdingCentered_le μ h hm _ (hb hv) z)
  have hs : ∀ x y, h (x,y) = h (y,x) := fun x y =>
    (sourceLogTransportKernel_swap n v (x,y)).symm
  exact DGRHS.Attractive.attractiveCanonical_uniform_exponential μ _ hc _ hr
    (DGRHS.centeredKernel_symmetric μ (fun x y => h (x,y)) hs)
    (DGRHS.integral_centeredKernel_left μ (fun x y => h (x,y)) hi) t ht N
end Physical

#print axioms bounded_kernel_rowFactorial
#print axioms abs_hoeffdingCentered_le
#print axioms exists_sourceLogTransport_centered_rows
#print axioms exists_sourceLogTransport_canonical_exponential
#check @exists_sourceLogTransport_canonical_exponential
end DGRHS.Commutator
