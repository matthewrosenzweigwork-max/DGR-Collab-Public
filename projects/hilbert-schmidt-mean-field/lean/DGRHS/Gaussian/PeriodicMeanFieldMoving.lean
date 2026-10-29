import DGRHS.Gaussian.PeriodicMeanFieldDrift
import DGRHS.Gaussian.PeriodicMeanFieldTwoParameter
import DGRHS.Commutator.SourceMovingLawIntegral

/-!
Packet P11e, unit 1 (part 3): the moving-test step (TeX 3922-3924) on the torus.

`PeriodicStaticWeakMeanFieldC2` is the integrated static weak formulation of the mean-field equation
against every `C²` torus test: the drift `periodicStaticMeanTestDrift` is integrable on `[0,T]` and
`∫ψ dμ^r = ∫ψ dμ^0 + ∫_0^r drift`.  `periodicStaticWeak_timeTested` shows that the static class and a
narrowly continuous probability path imply `PeriodicMeanFieldTimeTested`, i.e. the identity tested
against the classical backward solutions.  This is the torus form of
`SourceRieszStaticWeakMeanField.classical_tested`; the chain rule for `r ↦ ∫ f^r dμ^r` is obtained
from `two_parameter_chain_rule` (the frozen-test derivative of the static class and the time
derivative of the test), without differentiating the static drift in time.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal RealInnerProductSpace ENNReal Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The integrated static weak formulation of the mean-field equation against `C²` torus tests. -/
def PeriodicStaticWeakMeanFieldC2 (F : PeriodicTorus ι → E) (β T : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) : Prop :=
  ∀ ψ : PeriodicTorus ι → ℝ, ContDiff ℝ 2 (periodicLiftFn ψ) →
    IntervalIntegrable (fun r => periodicStaticMeanTestDrift F β (ρ r) ψ) volume 0 T ∧
    ∀ r ∈ Icc 0 T,
      (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ r)) =
        (∫ x, ψ x ∂periodicCappedDensityMeasure (ρ 0)) +
          ∫ u in 0..r, periodicStaticMeanTestDrift F β (ρ u) ψ

/-- Clamping to `[0,t]`. -/
def periodicClamp (t u : ℝ) : ℝ := max 0 (min t u)

lemma continuous_periodicClamp (t : ℝ) : Continuous (periodicClamp t) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma periodicClamp_mem {t : ℝ} (ht : 0 ≤ t) (u : ℝ) : periodicClamp t u ∈ Icc 0 t :=
  ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩

lemma periodicClamp_eq {t u : ℝ} (hu : u ∈ Icc 0 t) : periodicClamp t u = u := by
  unfold periodicClamp
  rw [min_eq_right hu.2, max_eq_right hu.1]

lemma periodicLiftFn_centeredLift (f : PeriodicTorus ι → ℝ) (z : PeriodicTorus ι) :
    periodicLiftFn f (periodicCenteredLift z) = f z := by
  simp [periodicLiftFn, periodicLift_centeredLift]

/-- Continuity of the clamped time derivative on `ℝ × 𝕋^d`. -/
lemma continuous_clamped_of_continuousOn_lift (t : ℝ≥0) (δ : ℝ → PeriodicTorus ι → ℝ)
    (hδc : ContinuousOn (fun p : ℝ × E => δ p.1 (periodicLift p.2)) (Icc 0 (t : ℝ) ×ˢ univ)) :
    Continuous (fun p : ℝ × PeriodicTorus ι => δ (periodicClamp t p.1) p.2) := by
  apply continuous_prod_of_continuous_periodicLift
  have hc : Continuous (fun p : ℝ × E => (periodicClamp t p.1, p.2)) :=
    ((continuous_periodicClamp t).comp continuous_fst).prodMk continuous_snd
  exact hδc.comp_continuous hc (fun p => ⟨periodicClamp_mem t.coe_nonneg _, mem_univ _⟩)

/-- Continuity (in `ℝ × 𝕋^d`) of the clamped Hessian of the lifts. -/
lemma continuous_clamped_hessian (t : ℝ≥0) (f : ℝ → PeriodicTorus ι → ℝ)
    (hH : ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ 2 (periodicLiftFn (f p.1)) p.2)
      (Icc 0 (t : ℝ) ×ˢ univ)) :
    Continuous (fun p : ℝ × PeriodicTorus ι =>
      iteratedFDeriv ℝ 2 (periodicLiftFn (f (periodicClamp t p.1))) (periodicCenteredLift p.2)) := by
  apply continuous_prod_of_continuous_periodicLift
  have hc : Continuous (fun p : ℝ × E => (periodicClamp t p.1, p.2)) :=
    ((continuous_periodicClamp t).comp continuous_fst).prodMk continuous_snd
  have h := hH.comp_continuous hc (fun p => ⟨periodicClamp_mem t.coe_nonneg _, mem_univ _⟩)
  refine h.congr (fun p => ?_)
  obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) p.2
  simp only [hm]
  exact ((isLatticePeriodic_periodicLiftFn (f (periodicClamp t p.1))).iteratedFDeriv_add 2 p.2 m).symm

/-- Uniform (in space) continuity of the Hessians of the lifts of a classical solution in time. -/
lemma hessian_uniformly_continuous_in_time (t : ℝ≥0) (f : ℝ → PeriodicTorus ι → ℝ)
    (hH : ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ 2 (periodicLiftFn (f p.1)) p.2)
      (Icc 0 (t : ℝ) ×ˢ univ)) :
    ∀ δ > 0, ∃ η > 0, ∀ s ∈ Icc 0 (t : ℝ), ∀ s' ∈ Icc 0 (t : ℝ), |s - s'| < η → ∀ x : E,
      ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f s)) x - iteratedFDeriv ℝ 2 (periodicLiftFn (f s')) x‖ < δ := by
  have hc := continuous_clamped_hessian t f hH
  have huc : UniformContinuousOn (fun p : ℝ × PeriodicTorus ι =>
      iteratedFDeriv ℝ 2 (periodicLiftFn (f (periodicClamp t p.1))) (periodicCenteredLift p.2))
      (Icc 0 (t : ℝ) ×ˢ (univ : Set (PeriodicTorus ι))) :=
    (isCompact_Icc.prod isCompact_univ).uniformContinuousOn_of_continuous hc.continuousOn
  intro δ hδ
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.mp huc δ hδ
  refine ⟨η, hη, fun s hs s' hs' hss x => ?_⟩
  have hx : ∀ r ∈ Icc 0 (t : ℝ), iteratedFDeriv ℝ 2 (periodicLiftFn (f r)) x =
      iteratedFDeriv ℝ 2 (periodicLiftFn (f (periodicClamp t r))) (periodicCenteredLift (periodicLift x)) := by
    intro r hr
    obtain ⟨m, hm⟩ := periodicCenteredLift_periodicLift (ι := ι) x
    rw [periodicClamp_eq hr, hm]
    exact ((isLatticePeriodic_periodicLiftFn (f r)).iteratedFDeriv_add 2 x m).symm
  rw [hx s hs, hx s' hs', ← dist_eq_norm]
  refine h (s, periodicLift x) ⟨hs, mem_univ _⟩ (s', periodicLift x) ⟨hs', mem_univ _⟩ ?_
  rw [Prod.dist_eq, dist_self, Real.dist_eq]
  exact max_lt hss hη

/-- The static drift of the zero test vanishes. -/
lemma periodicStaticMeanTestDrift_zero (F : PeriodicTorus ι → E) (β : ℝ) (ρ : PeriodicTorus ι → ℝ) :
    periodicStaticMeanTestDrift F β ρ (fun _ => 0) = 0 := by
  have e : periodicLiftFn (fun _ : PeriodicTorus ι => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
  have h1 : periodicLap (fun _ : PeriodicTorus ι => (0 : ℝ)) = fun _ => 0 := by
    funext z
    simp only [periodicLap, e]
    simp
  have h2 : periodicGrad (fun _ : PeriodicTorus ι => (0 : ℝ)) = fun _ => 0 := by
    funext z
    simp only [periodicGrad, e]
    simp
  simp [periodicStaticMeanTestDrift, h1, h2, periodicForcePair]

/-- Uniform bound on the static drift of a test with bounded Hessian. -/
theorem periodicStaticMeanTestDrift_bound (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (ρ : PeriodicTorus ι → ℝ), (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      IsProbabilityMeasure (periodicCappedDensityMeasure ρ) →
      ∀ (φ : PeriodicTorus ι → ℝ), ContDiff ℝ 2 (periodicLiftFn φ) → ∀ δ : ℝ, 0 ≤ δ →
        (∀ x, ‖iteratedFDeriv ℝ 2 (periodicLiftFn φ) x‖ ≤ δ) →
        |periodicStaticMeanTestDrift D.F β ρ φ| ≤ Cs * δ := by
  obtain ⟨Cs, hCs, h⟩ := periodicStaticMeanTestDrift_sub_le D β M hM
  refine ⟨Cs, hCs, fun ρ hρ hprob φ hφ δ hδ hH => ?_⟩
  have h0 : ContDiff ℝ 2 (periodicLiftFn (fun _ : PeriodicTorus ι => (0 : ℝ))) := contDiff_const
  have := h ρ hρ hprob φ (fun _ => 0) hφ h0 δ hδ (fun x => by
    have : iteratedFDeriv ℝ 2 (periodicLiftFn (fun _ : PeriodicTorus ι => (0 : ℝ))) x = 0 := by
      have e : periodicLiftFn (fun _ : PeriodicTorus ι => (0 : ℝ)) = fun _ => (0 : ℝ) := rfl
      rw [e, iteratedFDeriv_fun_zero]; rfl
    rw [this, sub_zero]; exact hH x)
  rwa [periodicStaticMeanTestDrift_zero, sub_zero] at this

end DGRHS.Periodic
