import DGRHS.Gaussian.PeriodicMeanFieldTimeTested
import DGRHS.Gaussian.PeriodicMeanFieldMollify
import DGRHS.Commutator.SourceScalarDistributionalTrace

/-!
Packet P11e, unit 1 (part 6): the torus weak mean-field class (Theorem 2.13, hypothesis (i); Remark 2.1;
owner convention `OWNER_DECISIONS_20261006.md` 1.2) and its bridge to the time-tested form.

`PeriodicDistributionalWeakMeanField` is the torus form of the Euclidean
`SourceRieszDistributionalWeakMeanField` / `SourceLogDistributionalWeakMeanField`: for every smooth torus
test `ψ` the drift `periodicStaticMeanTestDrift` (the symmetrized weak identity of TeX 3897-3904) is
integrable on `[0,T]` and is the distributional derivative of `r ↦ ∫ψ dμ^r` on `(0,T)`.
`PeriodicMeanFieldWeak` adds the narrow continuity of `r ↦ μ^r` on `[0,T]` required by the owner
convention.  The chain is: narrow continuity gives the every-time primitive identity for smooth tests
(`source_scalar_trace_eq_primitive`); periodic mollification extends it to `C²` tests; the static `C²`
class gives the time-tested identity (`periodicStaticWeak_timeTested`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal RealInnerProductSpace ENNReal Topology Classical Interval ContDiff
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Distributional-in-time weak formulation of the mean-field equation (2.32), in its symmetrized weak
form `eq:dynamicMeanFieldWeakIdentity`, against smooth torus tests. -/
def PeriodicDistributionalWeakMeanField (F : PeriodicTorus ι → E) (β T : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) : Prop :=
  ∀ ψ : PeriodicTorus ι → ℝ, ContDiff ℝ ∞ (periodicLiftFn ψ) →
    IntervalIntegrable (fun r => periodicStaticMeanTestDrift F β (ρ r) ψ) volume 0 T ∧
    SourceScalarDistributionalDerivOn
      (fun r => ∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r))
      (fun r => periodicStaticMeanTestDrift F β (ρ r) ψ) 0 T

/-- The torus weak mean-field solution class: a narrowly continuous (on `[0,T]`) path of probability
measures with bounded densities `ρ^r`, satisfying the mean-field equation in its symmetrized weak form
`eq:dynamicMeanFieldWeakIdentity`, in the distributional sense against smooth tests. -/
structure PeriodicMeanFieldWeak (F : PeriodicTorus ι → E) (β : ℝ) (T : ℝ≥0)
    (ρ : ℝ → PeriodicTorus ι → ℝ) : Prop where
  narrow : ∃ μ : ℝ → ProbabilityMeasure (PeriodicTorus ι), ContinuousOn μ (Icc 0 (T : ℝ)) ∧
    ∀ r ∈ Icc 0 (T : ℝ), (μ r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r)
  distributional : PeriodicDistributionalWeakMeanField F β (T : ℝ) ρ

/-- Narrow continuity makes the pairing with a continuous torus test continuous. -/
lemma periodic_pairing_continuousOn_of_narrow (T : ℝ) (ρ : ℝ → PeriodicTorus ι → ℝ)
    (μ : ℝ → ProbabilityMeasure (PeriodicTorus ι)) (hμ : ContinuousOn μ (Icc 0 T))
    (hρμ : ∀ r ∈ Icc 0 T, (μ r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r))
    (ψ : PeriodicTorus ι → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun r => ∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) (Icc 0 T) := by
  let f : BoundedContinuousFunction (PeriodicTorus ι) ℝ := BoundedContinuousFunction.mkOfCompact ⟨ψ, hψ⟩
  have hcont : ContinuousOn (fun r => ∫ x, f x ∂(μ r : Measure (PeriodicTorus ι))) (Icc 0 T) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp_continuousOn hμ
  refine hcont.congr (fun r hr => ?_)
  show (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) = ∫ x, ψ x ∂(μ r : Measure (PeriodicTorus ι))
  rw [hρμ r hr]

/-- Smooth tests: the every-time primitive identity (the trace step). -/
theorem PeriodicDistributionalWeakMeanField.smooth_static {F : PeriodicTorus ι → E} {β T : ℝ}
    (hT : 0 ≤ T) {ρ : ℝ → PeriodicTorus ι → ℝ}
    (μ : ℝ → ProbabilityMeasure (PeriodicTorus ι)) (hμ : ContinuousOn μ (Icc 0 T))
    (hρμ : ∀ r ∈ Icc 0 T, (μ r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r))
    (hd : PeriodicDistributionalWeakMeanField F β T ρ)
    (ψ : PeriodicTorus ι → ℝ) (hψ : ContDiff ℝ ∞ (periodicLiftFn ψ)) :
    IntervalIntegrable (fun r => periodicStaticMeanTestDrift F β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T, (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) =
      (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0)) +
        ∫ u in 0..r, periodicStaticMeanTestDrift F β (ρ u) ψ := by
  obtain ⟨hi, hdd⟩ := hd ψ hψ
  have hψc : Continuous ψ := by
    apply continuous_of_continuous_periodicLift
    exact (hψ.of_le (by exact WithTop.coe_le_coe.mpr (show (0 : ℕ∞) ≤ ⊤ from le_top))).continuous
  exact ⟨hi, source_scalar_trace_eq_primitive hT _ _
    (periodic_pairing_continuousOn_of_narrow T ρ μ hμ hρμ ψ hψc) hi hdd⟩

lemma periodic_integral_sub_le (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    {f g : PeriodicTorus ι → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) {ε : ℝ}
    (h : ∀ z, |f z - g z| ≤ ε) : |(∫ z, f z ∂μ) - ∫ z, g z ∂μ| ≤ ε := by
  rw [← integral_sub hf hg]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun z => f z - g z) (C := ε)
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact h z)
  simpa [Real.norm_eq_abs] using this

/-- The torus test is integrable against a finite measure when its lift is continuous. -/
lemma periodic_integrable_of_continuous_lift {ψ : PeriodicTorus ι → ℝ}
    (hψ : Continuous (periodicLiftFn ψ)) (μ : Measure (PeriodicTorus ι)) [IsFiniteMeasure μ] :
    Integrable ψ μ := by
  obtain ⟨C, hC0, hC⟩ := exists_value_bound hψ
  refine (integrable_const C).mono'
    (measurable_of_contDiff_lift (contDiff_zero.mpr hψ)).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have := hC (periodicCenteredLift z)
  simpa only [Real.norm_eq_abs, periodicLiftFn_centeredLift] using this

/-- **Smooth tests to `C²` tests.**  The distributional class, narrow continuity and the density cap
give the integrated static weak formulation against every `C²` torus test. -/
theorem PeriodicDistributionalWeakMeanField.to_staticC2 (D : PeriodicForceData ι) {β : ℝ} {T : ℝ≥0}
    {ρ : ℝ → PeriodicTorus ι → ℝ} (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (μ : ℝ → ProbabilityMeasure (PeriodicTorus ι)) (hμ : ContinuousOn μ (Icc 0 (T : ℝ)))
    (hρμ : ∀ r ∈ Icc 0 (T : ℝ),
      (μ r : Measure (PeriodicTorus ι)) = periodicCappedDensityMeasure (ρ r))
    (hd : PeriodicDistributionalWeakMeanField D.F β (T : ℝ) ρ) :
    PeriodicStaticWeakMeanFieldC2 D.F β (T : ℝ) ρ := by
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  obtain ⟨Cs', hCs'0, hCs'⟩ := periodicStaticMeanTestDrift_sub_le D β M hM
  obtain ⟨Cs, hCs0, hCs⟩ := periodicStaticMeanTestDrift_bound D β M hM
  intro ψ hψ
  choose χ hχs hχ0 hχ2 using fun n : ℕ =>
    exists_periodic_smooth_approx ψ hψ (1 / ((n : ℝ) + 1)) (by positivity)
  have hS := fun n => PeriodicDistributionalWeakMeanField.smooth_static hT0 μ hμ hρμ hd (χ n) (hχs n)
  have hχ2d : ∀ n, ContDiff ℝ 2 (periodicLiftFn (χ n)) := fun n =>
    (hχs n).of_le (by exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- uniform convergence of the drifts
  have hunif : ∀ n, ∀ u ∈ Icc 0 (T : ℝ),
      |periodicStaticMeanTestDrift D.F β (ρ u) (χ n) - periodicStaticMeanTestDrift D.F β (ρ u) ψ| ≤
        Cs' * (1 / ((n : ℝ) + 1)) := fun n u hu =>
    hCs' (ρ u) (hρ u hu) (hprob u hu) (χ n) ψ (hχ2d n) hψ _ (by positivity) (hχ2 n)
  -- boundedness of the limit drift
  obtain ⟨Kψ, hKψ⟩ := exists_hessian_bound hψ
  have hbd : ∀ u ∈ Icc 0 (T : ℝ), |periodicStaticMeanTestDrift D.F β (ρ u) ψ| ≤ Cs * Kψ :=
    fun u hu => hCs (ρ u) (hρ u hu) (hprob u hu) ψ hψ _ (NNReal.coe_nonneg _) hKψ
  -- integrability of the limit drift
  have hint : IntervalIntegrable (fun r => periodicStaticMeanTestDrift D.F β (ρ r) ψ) volume 0 (T : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    have hmeas : AEStronglyMeasurable (fun r => periodicStaticMeanTestDrift D.F β (ρ r) ψ)
        (volume.restrict (Ioc 0 (T : ℝ))) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop
        (f := fun n r => periodicStaticMeanTestDrift D.F β (ρ r) (χ n))
        (fun n => ((hS n).1.1).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu' : u ∈ Icc 0 (T : ℝ) := ⟨hu.1.le, hu.2⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa only [mul_zero] using hε.const_mul Cs')
      rw [Real.norm_eq_abs]
      exact hunif n u hu'
    refine (integrable_const (Cs * Kψ)).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs]
    exact hbd u ⟨hu.1.le, hu.2⟩
  refine ⟨hint, fun r hr => ?_⟩
  -- the identity, by the approximation estimates
  set Q : ℝ := (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) -
    ((∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0)) +
      ∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) ψ) with hQ
  have hr0 : (0 : ℝ) ≤ r := hr.1
  have hr0T : (0 : ℝ) ∈ Icc 0 (T : ℝ) := ⟨le_rfl, hT0⟩
  have hbound : ∀ n : ℕ, |Q| ≤ (2 + T * Cs') * (1 / ((n : ℝ) + 1)) := by
    intro n
    haveI := hprob r hr
    haveI := hprob 0 hr0T
    have hlift := (hχ2d n).continuous
    have hψc : Continuous (periodicLiftFn ψ) := hψ.continuous
    have hpt : ∀ z, |χ n z - ψ z| ≤ 1 / ((n : ℝ) + 1) := by
      intro z
      have := hχ0 n (periodicCenteredLift z)
      simpa only [periodicLiftFn_centeredLift] using this
    have e1 := periodic_integral_sub_le (periodicCappedDensityMeasure (ρ r))
      (periodic_integrable_of_continuous_lift hlift _) (periodic_integrable_of_continuous_lift hψc _)
      hpt
    have e0 := periodic_integral_sub_le (periodicCappedDensityMeasure (ρ 0))
      (periodic_integrable_of_continuous_lift hlift _) (periodic_integrable_of_continuous_lift hψc _)
      hpt
    obtain ⟨hSi, hSe⟩ := hS n
    have hSr := hSe r hr
    -- difference of the primitives
    have hsubI : IntervalIntegrable (fun u => periodicStaticMeanTestDrift D.F β (ρ u) (χ n)) volume 0 r :=
      hSi.mono_set (by rw [uIcc_of_le hr0, uIcc_of_le hT0]; exact Icc_subset_Icc le_rfl hr.2)
    have hsubψ : IntervalIntegrable (fun u => periodicStaticMeanTestDrift D.F β (ρ u) ψ) volume 0 r :=
      hint.mono_set (by rw [uIcc_of_le hr0, uIcc_of_le hT0]; exact Icc_subset_Icc le_rfl hr.2)
    have e2 : |(∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) (χ n)) -
        ∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) ψ| ≤
        Cs' * (1 / ((n : ℝ) + 1)) * r := by
      rw [← intervalIntegral.integral_sub hsubI hsubψ]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
        (f := fun u => periodicStaticMeanTestDrift D.F β (ρ u) (χ n) -
          periodicStaticMeanTestDrift D.F β (ρ u) ψ) (C := Cs' * (1 / ((n : ℝ) + 1)))
        (fun u hu => by
          rw [uIoc_of_le hr0] at hu
          rw [Real.norm_eq_abs]
          exact hunif n u ⟨hu.1.le, hu.2.trans hr.2⟩)
      rwa [Real.norm_eq_abs, sub_zero, abs_of_nonneg hr0] at this
    have hrT : r ≤ T := hr.2
    have : |Q| ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) + Cs' * (1 / ((n : ℝ) + 1)) * r := by
      have hQ' : Q = ((∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) -
          ∫ x, χ n x ∂periodicCappedDensityMeasure (ρ r)) -
          ((∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0)) -
            ∫ x, χ n x ∂periodicCappedDensityMeasure (ρ 0)) +
          ((∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) (χ n)) -
            ∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) ψ) := by
        rw [hQ]; linarith
      rw [hQ']
      calc _ ≤ |(∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) -
            ∫ x, χ n x ∂periodicCappedDensityMeasure (ρ r)| +
          |(∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0)) -
            ∫ x, χ n x ∂periodicCappedDensityMeasure (ρ 0)| +
          |(∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) (χ n)) -
            ∫ u in 0..r, periodicStaticMeanTestDrift D.F β (ρ u) ψ| := by
            exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ _ := by
            rw [abs_sub_comm (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)),
              abs_sub_comm (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0))]
            exact add_le_add (add_le_add e1 e0) e2
    refine this.trans ?_
    have hCs'r : Cs' * (1 / ((n : ℝ) + 1)) * r ≤ Cs' * (1 / ((n : ℝ) + 1)) * T :=
      mul_le_mul_of_nonneg_left hrT (by positivity)
    nlinarith
  have hlim : Tendsto (fun n : ℕ => (2 + T * Cs') * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul (2 + T * Cs')
  have hQ0 : |Q| ≤ 0 := ge_of_tendsto' hlim hbound
  have : Q = 0 := abs_nonpos_iff.mp hQ0
  linarith

/-- **The bridge** (the torus form of the Euclidean narrow-class derivation of the time-tested identity):
the weak mean-field class implies the mean-field identity tested against every classical backward
solution `f^r`, in the form used by the proof of Proposition 8.2 (TeX 3897-3904, 3922-3924). -/
theorem periodicMeanFieldWeak_timeTested (D : PeriodicForceData ι) (β : ℝ) (T : ℝ≥0)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (Dtest : Submodule ℝ (PeriodicTorus ι → ℝ))
    (hweak : PeriodicMeanFieldWeak D.F β T ρ) :
    PeriodicMeanFieldTimeTested T D.F β ρ Dtest := by
  obtain ⟨μ, hμ, hρμ⟩ := hweak.narrow
  have hstat := hweak.distributional.to_staticC2 D M hM hprob hρ μ hμ hρμ
  intro t ht φ _ f hf
  exact periodicStaticWeak_timeTested D β T ρ M hM hprob hρ μ hμ hρμ hstat t ht φ f hf

end DGRHS.Periodic
