import DGRHS.Gaussian.PeriodicDynamicDrift
import DGRHS.Commutator.SourceRieszTimeRemainder
import DGRHS.Dynamics.SourceDensityKernel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Prod
import DGRHS.Commutator.SourceRieszFiniteTerminal

/-!
Packet P11c, unit 3 (part 2): Proposition 8.2 (`prop:finiteNAdjointDuality`, TeX 3859-3877) on the torus,
for an abstract periodic interaction force: the instantaneous physical drift, its time integrals, the
remainder `R = -(√N/2) ∫_0^t A_1(∇f^r, X^r, μ^r) dr`, the adjoint time identity, and the finite-family
terminal representation.  Lemma 8.1(ii) enters as the `L¹` bound hypothesis `hA1` on the transport energy
(the kernel-specific wrappers `periodicRiesz_finite_terminal_representation` and
`periodicLog_finite_terminal_representation` discharge it from Lemma 8.1).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Dynamics
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Actual particle test drift for a time-dependent torus test, with the collision-zero force. -/
def periodicEmpiricalTestDrift (F : PeriodicTorus ι → E) (β : ℝ) (q : ℝ → PeriodicTorus ι → ℝ)
    (N : ℕ) (r : ℝ) (x : Fin N → PeriodicTorus ι) : ℝ :=
  (∫ z, deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z ∂sourceRieszLocalEmpiricalLaw N x) -
    ((N : ℝ) ^ 2)⁻¹ * (∑ i : Fin N, ∑ j : Fin N, ⟪F (x i - x j), periodicGrad (q r) (x i)⟫)

/-- Actual mean-field test drift with the combined difference kernel. -/
def periodicMeanTestDrift (F : PeriodicTorus ι → E) (β : ℝ) (ρ : PeriodicTorus ι → ℝ)
    (q : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) : ℝ :=
  (∫ z, deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z ∂periodicCappedDensityMeasure ρ) -
    (1 / 2 : ℝ) * (∫ p, periodicForcePair F (periodicGrad (q r)) p
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))

/-- The backward equation in its a.e.-in-time form, pointwise in space. -/
def PeriodicBackwardEq (F : PeriodicTorus ι → E) (β : ℝ) (ρ : PeriodicTorus ι → ℝ)
    (q : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) : Prop :=
  ∀ z, deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z =
    ∫ y, ⟪F (z - y), periodicGrad (q r) z - periodicGrad (q r) y⟫ ∂periodicCappedDensityMeasure ρ

/-- The instantaneous physical drift identity of Proposition 8.2 (TeX 3890-3914). -/
theorem periodic_adjoint_physical_drift (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ z ∂periodicHaar ι, ρ z ≤ M)
    (q : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) (hq : ContDiff ℝ 2 (periodicLiftFn (q r))) (K : ℝ≥0)
    (hK : ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (q r)) z‖ ≤ (K : ℝ))
    (hback : PeriodicBackwardEq D.F β ρ q r) (N : ℕ) (hN : 0 < N) (x : Fin N → PeriodicTorus ι) :
    Integrable (fun z => deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z)
      (sourceRieszLocalEmpiricalLaw N x) ∧
    Integrable (fun z => deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z)
      (periodicCappedDensityMeasure ρ) ∧
    periodicEmpiricalTestDrift D.F β q N r x - periodicMeanTestDrift D.F β ρ q r =
      -(1 / 2 : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicForcePair D.F (periodicGrad (q r))) N x := by
  have hv := periodicGrad_lipschitz hq K hK
  obtain ⟨C, hC, hsec⟩ := D.section_density (K * (Fintype.card ι : ℝ≥0))
  obtain ⟨C', hC', hpair⟩ := D.pair_density_integrable (K * (Fintype.card ι : ℝ≥0))
  let μ := periodicCappedDensityMeasure ρ
  let L := fun z => deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z
  have hL : ∀ z, L z = ∫ y, periodicForcePair D.F (periodicGrad (q r)) (z, y) ∂μ := fun z => hback z
  have hpi := (hpair hv ρ M hM hρ).1
  have hsc := fun z => (hsec hv ρ M hM hρ z).1
  have hLμ : Integrable L μ := by
    have h := hpi.integral_prod_left
    exact h.congr (Filter.Eventually.of_forall fun z => (hL z).symm)
  have hLe : Integrable L (sourceRieszLocalEmpiricalLaw N x) :=
    integrable_sourceRieszLocalEmpiricalLaw N x L
  refine ⟨hLe, hLμ, ?_⟩
  have halg := periodic_drift_algebra D hv μ hsc hpi L hL N hN x
  unfold periodicEmpiricalTestDrift periodicMeanTestDrift
  exact halg

/-- The mean drift is half the pair integral, by the backward equation. -/
theorem periodic_mean_drift_eq_half_pair (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ z ∂periodicHaar ι, ρ z ≤ M)
    (q : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) (hq : ContDiff ℝ 2 (periodicLiftFn (q r))) (K : ℝ≥0)
    (hK : ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (q r)) z‖ ≤ (K : ℝ))
    (hback : PeriodicBackwardEq D.F β ρ q r) :
    periodicMeanTestDrift D.F β ρ q r =
      (1 / 2 : ℝ) * ∫ p, periodicForcePair D.F (periodicGrad (q r)) p
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) := by
  have hv := periodicGrad_lipschitz hq K hK
  obtain ⟨C', hC', hpair⟩ := D.pair_density_integrable (K * (Fintype.card ι : ℝ≥0))
  have hpi := (hpair hv ρ M hM hρ).1
  have he : (fun z => deriv (fun t => q t z) r + β⁻¹ * periodicLap (q r) z) =
      (fun z => ∫ y, periodicForcePair D.F (periodicGrad (q r)) (z, y)
        ∂periodicCappedDensityMeasure ρ) := funext fun z => hback z
  unfold periodicMeanTestDrift
  rw [he, ← integral_prod _ hpi]
  ring


/-! ### Stopped gradients and joint measurability in time -/

/-- The measurable zero extension of the gradient of a time-dependent test beyond `[0,t]`. -/
def periodicStoppedGrad (t : ℝ) (f : ℝ → PeriodicTorus ι → ℝ) (r : ℝ) (z : PeriodicTorus ι) : E :=
  if r ∈ Icc 0 t then periodicGrad (f r) z else 0

lemma measurable_periodicStoppedGrad (t : ℝ) (f : ℝ → PeriodicTorus ι → ℝ)
    (hf : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f p.1)) p.2) (Icc 0 t ×ˢ univ)) :
    Measurable (fun p : ℝ × PeriodicTorus ι => periodicStoppedGrad t f p.1 p.2) := by
  have hz : ContinuousOn (fun _ : ℝ × E => (0 : E)) (Icc 0 t ×ˢ (univ : Set E))ᶜ := continuousOn_const
  have hh := hf.measurable_piecewise hz (measurableSet_Icc.prod MeasurableSet.univ)
  have hm : Measurable (fun p : ℝ × PeriodicTorus ι => (p.1, periodicCenteredLift p.2)) :=
    measurable_fst.prodMk (measurable_periodicCenteredLift.comp measurable_snd)
  have heq : (fun p : ℝ × PeriodicTorus ι => periodicStoppedGrad t f p.1 p.2) =
      fun p => (Icc 0 t ×ˢ (univ : Set E)).piecewise
        (fun p : ℝ × E => gradient (periodicLiftFn (f p.1)) p.2) (fun _ => (0 : E))
          (p.1, periodicCenteredLift p.2) := by
    funext p
    by_cases h : p.1 ∈ Icc 0 t
    · have hmem : (p.1, periodicCenteredLift p.2) ∈ Icc 0 t ×ˢ (univ : Set E) := ⟨h, mem_univ _⟩
      rw [Set.piecewise_eq_of_mem _ _ _ hmem]
      simp [periodicStoppedGrad, h, periodicGrad]
    · have hmem : (p.1, periodicCenteredLift p.2) ∉ Icc 0 t ×ˢ (univ : Set E) := fun hh => h hh.1
      rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
      simp [periodicStoppedGrad, h]
  rw [heq]
  exact hh.comp hm

lemma norm_periodicStoppedGrad_le (t : ℝ) (f : ℝ → PeriodicTorus ι → ℝ) (G : ℝ≥0)
    (hb : ∀ r ∈ Icc 0 t, ∀ z, ‖periodicGrad (f r) z‖ ≤ (G : ℝ)) (r : ℝ) (z : PeriodicTorus ι) :
    ‖periodicStoppedGrad t f r z‖ ≤ (G : ℝ) := by
  by_cases hr : r ∈ Icc 0 t
  · simpa [periodicStoppedGrad, hr] using hb r hr z
  · simp [periodicStoppedGrad, hr]

lemma measurable_periodicForcePair_time (D : PeriodicForceData ι) {τ : Type*} [MeasurableSpace τ]
    (v : τ → PeriodicTorus ι → E) (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ × (PeriodicTorus ι × PeriodicTorus ι) => periodicForcePair D.F (v p.1) p.2) := by
  have hz : Measurable (fun p : τ × (PeriodicTorus ι × PeriodicTorus ι) => p.2.1 - p.2.2) :=
    measurable_snd.fst.sub measurable_snd.snd
  have h1 : Measurable (fun p : τ × (PeriodicTorus ι × PeriodicTorus ι) => v p.1 p.2.1) :=
    hv.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : Measurable (fun p : τ × (PeriodicTorus ι × PeriodicTorus ι) => v p.1 p.2.2) :=
    hv.comp (measurable_fst.prodMk measurable_snd.snd)
  exact (D.measurable.comp hz).inner (h1.sub h2)

lemma measurable_periodicTransportPotential_time (D : PeriodicForceData ι) {τ : Type*}
    [MeasurableSpace τ] (κ : Kernel τ (PeriodicTorus ι)) [IsSFiniteKernel κ]
    (v : τ → PeriodicTorus ι → E) (hv : Measurable (Function.uncurry v)) :
    Measurable (fun p : τ × PeriodicTorus ι => ∫ y, periodicForcePair D.F (v p.1) (p.2, y) ∂κ p.1) := by
  have hk := measurable_periodicForcePair_time D v hv
  have hf := hk.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ.comap Prod.fst measurable_fst)).measurable

set_option maxHeartbeats 800000 in
lemma measurable_periodicTransportEnergy_time (D : PeriodicForceData ι) {τ Ω : Type*}
    [MeasurableSpace τ] [MeasurableSpace Ω]
    (ρ : τ → PeriodicTorus ι → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (v : τ → PeriodicTorus ι → E) (hv : Measurable (Function.uncurry v))
    (N : ℕ) (hN : 0 < N) (X : τ × Ω → Fin N → PeriodicTorus ι) (hX : Measurable X) :
    Measurable (fun p : τ × Ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ p.1))
      (periodicForcePair D.F (v p.1)) N (X p)) := by
  classical
  let κ := DGRHS.Dynamics.sourceDensityKernel (periodicHaar ι) ρ
  letI := DGRHS.Dynamics.sourceDensityKernel_sfinite (periodicHaar ι) ρ
  have hκ (r : τ) : κ r = periodicCappedDensityMeasure (ρ r) :=
    DGRHS.Dynamics.sourceDensityKernel_apply (periodicHaar ι) ρ hρ r
  have hk := measurable_periodicForcePair_time D v hv
  have hp := measurable_periodicTransportPotential_time D κ v hv
  have hI : Measurable (fun r => ∫ z, periodicForcePair D.F (v r) z ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ := κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  have hXi : ∀ i : Fin N, Measurable (fun p : τ × Ω => X p i) := fun i => (measurable_pi_apply i).comp hX
  have hterm : ∀ ij : Fin N × Fin N, Measurable (fun p : τ × Ω =>
      periodicForcePair D.F (v p.1) (X p ij.1, X p ij.2)) := fun ij =>
    hk.comp (measurable_fst.prodMk ((hXi ij.1).prodMk (hXi ij.2)))
  have hsum : Measurable (fun p : τ × Ω => DGRHS.CanonicalVariance.offDiagonalSum
      (periodicForcePair D.F (v p.1)) (X p)) := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    exact Finset.measurable_sum _ (fun ij _ => hterm ij)
  have hpterm : ∀ i : Fin N, Measurable (fun p : τ × Ω =>
      ∫ y, periodicForcePair D.F (v p.1) (X p i, y) ∂κ p.1) := fun i =>
    hp.comp (measurable_fst.prodMk (hXi i))
  have hpSum : Measurable (fun p : τ × Ω => ∑ i : Fin N,
      ∫ y, periodicForcePair D.F (v p.1) (X p i, y) ∂κ p.1) :=
    Finset.measurable_sum _ (fun i _ => hpterm i)
  have heq : (fun p : τ × Ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ p.1))
      (periodicForcePair D.F (v p.1)) N (X p)) =
      (fun p => ((N : ℝ) ^ 2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum
        (periodicForcePair D.F (v p.1)) (X p) -
        2 * (N : ℝ)⁻¹ * (∑ i : Fin N, ∫ y, periodicForcePair D.F (v p.1) (X p i, y) ∂κ p.1) +
        (∫ z, periodicForcePair D.F (v p.1) z ∂(κ p.1).prod (κ p.1))) := by
    funext p
    have hsym : ∀ a b, periodicForcePair D.F (v p.1) (a, b) = periodicForcePair D.F (v p.1) (b, a) :=
      fun a b => (D.pair_swap (v p.1) (a, b)).symm
    have h := sourceTransportEnergy_raw (periodicCappedDensityMeasure (ρ p.1))
      (periodicForcePair D.F (v p.1)) hsym N hN (X p)
    simp only [hκ]
    simp only [DGRHS.potential] at h
    exact h
  rw [heq]
  exact ((hsum.const_mul _).sub (hpSum.const_mul _)).add (hI.comp measurable_fst)

/-! ### Time integrability of the mean drift -/

theorem periodic_mean_drift_time_integrable (D : PeriodicForceData ι) (β T M : ℝ) (hM : 0 ≤ M)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (q : ℝ → PeriodicTorus ι → ℝ) (K : ℝ≥0)
    (hq : ∀ r ∈ Icc 0 T, ContDiff ℝ 2 (periodicLiftFn (q r)))
    (hK : ∀ r ∈ Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (q r)) z‖ ≤ (K : ℝ))
    (hgrad : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (q p.1)) p.2) (Icc 0 T ×ˢ univ))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T), PeriodicBackwardEq D.F β (ρ r) q r) :
    Integrable (fun r => periodicMeanTestDrift D.F β (ρ r) q r) (volume.restrict (Ioc 0 T)) := by
  let v := periodicStoppedGrad T q
  have hv : Measurable (Function.uncurry v) := measurable_periodicStoppedGrad T q hgrad
  have hvr (r : ℝ) (hr : r ∈ Icc 0 T) : v r = periodicGrad (q r) := by
    funext z
    simp [v, periodicStoppedGrad, hr]
  let κ := DGRHS.Dynamics.sourceDensityKernel (periodicHaar ι) ρ
  letI := DGRHS.Dynamics.sourceDensityKernel_sfinite (periodicHaar ι) ρ
  have hκ (r : ℝ) : κ r = periodicCappedDensityMeasure (ρ r) :=
    DGRHS.Dynamics.sourceDensityKernel_apply (periodicHaar ι) ρ hρm r
  have hk := measurable_periodicForcePair_time D v hv
  have hI : Measurable (fun r => ∫ p, periodicForcePair D.F (v r) p ∂(κ r).prod (κ r)) := by
    have ht := hk.stronglyMeasurable.integral_kernel_prod_right' (κ := κ.prod κ)
    simpa only [Kernel.prod_apply] using ht.measurable
  obtain ⟨C, hC, hpair⟩ := D.pair_density_integrable (K * (Fintype.card ι : ℝ≥0))
  have hi : Integrable (fun r => (1 / 2 : ℝ) * ∫ p, periodicForcePair D.F (v r) p ∂(κ r).prod (κ r))
      (volume.restrict (Ioc 0 T)) := by
    apply (integrable_const ((1 / 2 : ℝ) * (M * C))).mono' (hI.const_mul _).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2⟩
    haveI := hprob r hr'
    have hL := periodicGrad_lipschitz (hq r hr') K (hK r hr')
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), hκ r, hvr r hr']
    exact mul_le_mul_of_nonneg_left (hpair hL (ρ r) M hM (hρ r hr')).2 (by norm_num)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hback] with r hr hb
  have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2⟩
  haveI := hprob r hr'
  rw [hκ r, hvr r hr']
  exact (periodic_mean_drift_eq_half_pair D β M hM (ρ r) (hρ r hr') q r (hq r hr') K (hK r hr') hb).symm

/-! ### The time remainder -/

set_option maxHeartbeats 800000 in
theorem periodic_time_commutator_remainder_of_bound (D : PeriodicForceData ι) (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (hN : 1 ≤ N) (Dc : ℝ) (hDc : 0 ≤ Dc) {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (v : ℝ → PeriodicTorus ι → E) (hvm : Measurable (Function.uncurry v))
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hA1 : ∀ r ∈ Icc 0 T,
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (v r)) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (v r)) N (X r ω)| ∂ν) ≤ Dc / (N : ℝ)) :
    let A := fun r ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
      (periodicForcePair D.F (v r)) N (X r ω)
    Measurable (Function.uncurry A) ∧
    Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
    (∀ᵐ ω ∂ν, Integrable (fun r => A r ω) (volume.restrict (Ioc 0 T))) ∧
    Integrable (fun ω => (Real.sqrt N / 2) * (∫ r in Ioc 0 T, A r ω)) ν ∧
    (∫ ω, |(Real.sqrt N / 2) * (∫ r in Ioc 0 T, A r ω)| ∂ν) ≤ T * Dc / (2 * Real.sqrt N) := by
  intro A
  let η := volume.restrict (Ioc 0 T)
  have hAm : Measurable (Function.uncurry A) :=
    measurable_periodicTransportEnergy_time D ρ hρm v hvm N (by omega) (Function.uncurry X) hXm
  have hslice : ∀ᵐ r ∂η, Integrable (A r) ν ∧ (∫ ω, |A r ω| ∂ν) ≤ Dc / (N : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hA1 r ⟨hr.1.le, hr.2⟩
  obtain ⟨hi, hiT, hb⟩ := sourceRiesz_time_integral_from_slices η ν A hAm
    (Dc / (N : ℝ)) (hslice.mono fun r hr => hr.1) (hslice.mono fun r hr => hr.2)
  have hmass : η.real univ = T := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hT, sub_zero]
  rw [hmass] at hb
  refine ⟨hAm, hi, hi.prod_left_ae, hiT.const_mul _, ?_⟩
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hsq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt hn.le
  calc
    (∫ ω, |(Real.sqrt N / 2) * (∫ r, A r ω ∂η)| ∂ν) =
        (Real.sqrt N / 2) * (∫ ω, |∫ r, A r ω ∂η| ∂ν) := by
      simp_rw [abs_mul, abs_of_nonneg (div_nonneg hsqrt.le (by norm_num : (0 : ℝ) ≤ 2))]
      exact integral_const_mul _ _
    _ ≤ (Real.sqrt N / 2) * (T * (Dc / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hsqrt.le (by norm_num))
    _ = T * Dc / (2 * Real.sqrt N) := by
      field_simp
      rw [hsq]
      ring

/-- The actual classical backward-test remainder is proper in time and sample. -/
theorem periodic_adjoint_time_remainder_of_bound (D : PeriodicForceData ι) (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (hN : 1 ≤ N) (Dc : ℝ) (hDc : 0 ≤ Dc) {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (q : ℝ → PeriodicTorus ι → ℝ)
    (hgrad : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (q p.1)) p.2) (Icc 0 T ×ˢ univ))
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hA1 : ∀ r ∈ Icc 0 T,
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)| ∂ν) ≤ Dc / (N : ℝ)) :
    let A := fun r ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
      (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)
    let R := fun ω => -((Real.sqrt N / 2) * (∫ r in Ioc 0 T, A r ω))
    Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
    (∀ᵐ ω ∂ν, Integrable (fun r => A r ω) (volume.restrict (Ioc 0 T))) ∧
    Measurable R ∧ Integrable R ν ∧ (∫ ω, |R ω| ∂ν) ≤ T * Dc / (2 * Real.sqrt N) := by
  intro A R
  let v := periodicStoppedGrad T q
  have hvm : Measurable (Function.uncurry v) := measurable_periodicStoppedGrad T q hgrad
  have hvr (r : ℝ) (hr : r ∈ Icc 0 T) : v r = periodicGrad (q r) := by
    funext z
    simp [v, periodicStoppedGrad, hr]
  obtain ⟨hAm, hi, _, hRi, hRb⟩ := periodic_time_commutator_remainder_of_bound D T hT N hN Dc hDc ν
    ρ hρm v hvm X hXm (fun r hr => by rw [hvr r hr]; exact hA1 r hr)
  let η := volume.restrict (Ioc 0 T)
  let Ae := fun r ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
    (periodicForcePair D.F (v r)) N (X r ω)
  have htime : ∀ᵐ p : ℝ × Ω ∂η.prod ν, p.1 ∈ Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall fun _ => hr
  have heq : Function.uncurry Ae =ᵐ[η.prod ν] Function.uncurry A := by
    filter_upwards [htime] with p hp
    change sourceTransportEnergy (periodicCappedDensityMeasure (ρ p.1))
      (periodicForcePair D.F (v p.1)) N (X p.1 p.2) =
      sourceTransportEnergy (periodicCappedDensityMeasure (ρ p.1))
        (periodicForcePair D.F (periodicGrad (q p.1))) N (X p.1 p.2)
    rw [hvr p.1 ⟨hp.1.le, hp.2⟩]
  have hint (ω : Ω) : (∫ r, Ae r ω ∂η) = ∫ r, A r ω ∂η := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp only [Ae, A]
    rw [hvr r ⟨hr.1.le, hr.2⟩]
  have hiA : Integrable (Function.uncurry A) (η.prod ν) := hi.congr heq
  have hRm : Measurable (fun ω => -((Real.sqrt N / 2) * (∫ r, A r ω ∂η))) := by
    have hh : Measurable (fun ω => -((Real.sqrt N / 2) * (∫ r, Ae r ω ∂η))) :=
      ((hAm.stronglyMeasurable.integral_prod_left' (μ := η)).measurable.const_mul _).neg
    simpa only [hint] using hh
  change Integrable (fun ω => (Real.sqrt N / 2) * (∫ r, Ae r ω ∂η)) ν at hRi
  change (∫ ω, |(Real.sqrt N / 2) * (∫ r, Ae r ω ∂η)| ∂ν) ≤ T * Dc / (2 * Real.sqrt N) at hRb
  simp_rw [hint] at hRi hRb
  refine ⟨hiA, hiA.prod_left_ae, hRm, hRi.neg, ?_⟩
  show (∫ ω, |-((Real.sqrt N / 2) * (∫ r, A r ω ∂η))| ∂ν) ≤ T * Dc / (2 * Real.sqrt N)
  simpa only [abs_neg] using hRb

/-- The pathwise adjoint time identity (TeX 3879-3914, with the additional time-derivative drift). -/
theorem periodic_adjoint_time_identity (D : PeriodicForceData ι) (β T M : ℝ) (hM : 0 ≤ M)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (q : ℝ → PeriodicTorus ι → ℝ) (K : ℝ≥0)
    (hq : ∀ r ∈ Icc 0 T, ContDiff ℝ 2 (periodicLiftFn (q r)))
    (hK : ∀ r ∈ Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (q r)) z‖ ≤ (K : ℝ))
    (hgrad : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (q p.1)) p.2) (Icc 0 T ×ˢ univ))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T), PeriodicBackwardEq D.F β (ρ r) q r)
    (N : ℕ) (hN : 0 < N) (X : ℝ → Fin N → PeriodicTorus ι) (m : ℝ)
    (hiA : Integrable (fun r => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
      (periodicForcePair D.F (periodicGrad (q r))) N (X r)) (volume.restrict (Ioc 0 T)))
    (hIto : (∫ z, q T z ∂sourceRieszLocalEmpiricalLaw N (X T)) -
      (∫ z, q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0)) =
      (∫ r in Ioc 0 T, periodicEmpiricalTestDrift D.F β q N r (X r)) + m)
    (hweak : (∫ z, q T z ∂periodicCappedDensityMeasure (ρ T)) -
      (∫ z, q 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
      ∫ r in Ioc 0 T, periodicMeanTestDrift D.F β (ρ r) q r) :
    Integrable (fun r => periodicEmpiricalTestDrift D.F β q N r (X r)) (volume.restrict (Ioc 0 T)) ∧
    Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ T)) (q T) N (X T) =
      Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (q 0) N (X 0) +
      Real.sqrt N * m - (Real.sqrt N / 2) * (∫ r in Ioc 0 T,
        sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicForcePair D.F (periodicGrad (q r))) N (X r)) := by
  let η := volume.restrict (Ioc 0 T)
  let ge := fun r => periodicEmpiricalTestDrift D.F β q N r (X r)
  let gm := fun r => periodicMeanTestDrift D.F β (ρ r) q r
  let A := fun r => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
    (periodicForcePair D.F (periodicGrad (q r))) N (X r)
  have him : Integrable gm η := periodic_mean_drift_time_integrable D β T M hM ρ hρm hprob hρ q K hq hK
    hgrad hback
  have he : ∀ᵐ r ∂η, ge r - gm r = -(1 / 2 : ℝ) * A r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hback] with r hr hb
    have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2⟩
    haveI := hprob r hr'
    exact (periodic_adjoint_physical_drift D β M hM (ρ r) (hρ r hr') q r (hq r hr') K (hK r hr') hb N
      hN (X r)).2.2
  have hie : Integrable ge η := (him.sub (hiA.const_mul (1 / 2 : ℝ))).congr
    (he.mono fun r hr => by
      change gm r - (1 / 2 : ℝ) * A r = ge r
      linarith)
  have hdint : (∫ r, ge r ∂η) - (∫ r, gm r ∂η) = -(1 / 2 : ℝ) * (∫ r, A r ∂η) := by
    rw [← integral_sub hie him]
    calc
      _ = ∫ r, -(1 / 2 : ℝ) * A r ∂η := integral_congr_ae he
      _ = _ := integral_const_mul _ _
  refine ⟨hie, ?_⟩
  unfold dynEmpiricalDifference
  change (∫ z, q T z ∂sourceRieszLocalEmpiricalLaw N (X T)) -
    (∫ z, q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0)) = (∫ r, ge r ∂η) + m at hIto
  change (∫ z, q T z ∂periodicCappedDensityMeasure (ρ T)) -
    (∫ z, q 0 z ∂periodicCappedDensityMeasure (ρ 0)) = (∫ r, gm r ∂η) at hweak
  linear_combination (Real.sqrt N) * hIto - (Real.sqrt N) * hweak + (Real.sqrt N) * hdint

lemma measurable_of_contDiff_lift {f : PeriodicTorus ι → ℝ} (hf : ContDiff ℝ 0 (periodicLiftFn f)) :
    Measurable f := by
  have : f = fun z => periodicLiftFn f (periodicCenteredLift z) := by
    funext z
    simp [periodicLiftFn, periodicLift_centeredLift]
  rw [this]
  exact hf.continuous.measurable.comp measurable_periodicCenteredLift

/-- Single-test terminal representation (TeX 3863-3877): the representation and the `L¹` rate of the
remainder, from the primitive particle and mean-field identities. -/
theorem periodic_physical_adjoint_time_identity (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M)
    (K : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) (N : ℕ) (hN : 1 ≤ N) (Dc : ℝ) (hDc : 0 ≤ Dc)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (q : ℝ → PeriodicTorus ι → ℝ) (hq : ∀ r ∈ Icc 0 T, ContDiff ℝ 2 (periodicLiftFn (q r)))
    (hK : ∀ r ∈ Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (q r)) z‖ ≤ (K : ℝ))
    (hgrad : ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (q p.1)) p.2) (Icc 0 T ×ˢ univ))
    (L : ℝ) (hqB : ∀ r ∈ Icc 0 T, ∀ z, |q r z| ≤ L)
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T), PeriodicBackwardEq D.F β (ρ r) q r)
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hA1 : ∀ r ∈ Icc 0 T,
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)| ∂ν) ≤ Dc / (N : ℝ))
    (m : Ω → ℝ)
    (hIto : ∀ᵐ ω ∂ν, (∫ z, q T z ∂sourceRieszLocalEmpiricalLaw N (X T ω)) -
      (∫ z, q 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
      (∫ r in Ioc 0 T, periodicEmpiricalTestDrift D.F β q N r (X r ω)) + m ω)
    (hweak : (∫ z, q T z ∂periodicCappedDensityMeasure (ρ T)) -
      (∫ z, q 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
      ∫ r in Ioc 0 T, periodicMeanTestDrift D.F β (ρ r) q r) :
    let A := fun r ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
      (periodicForcePair D.F (periodicGrad (q r))) N (X r ω)
    let R := fun ω => -((Real.sqrt N / 2) * (∫ r in Ioc 0 T, A r ω))
    (∀ r ∈ Icc 0 T, Integrable (q r) (periodicCappedDensityMeasure (ρ r)) ∧
      ∀ x : Fin N → PeriodicTorus ι, Integrable (q r) (sourceRieszLocalEmpiricalLaw N x)) ∧
    Integrable (fun r => periodicMeanTestDrift D.F β (ρ r) q r) (volume.restrict (Ioc 0 T)) ∧
    (∀ᵐ ω ∂ν, Integrable (fun r => A r ω) (volume.restrict (Ioc 0 T)) ∧
      Integrable (fun r => periodicEmpiricalTestDrift D.F β q N r (X r ω))
        (volume.restrict (Ioc 0 T)) ∧
      Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ T)) (q T) N (X T ω) =
        Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (q 0) N (X 0 ω) +
          Real.sqrt N * m ω + R ω) ∧
    Measurable R ∧ Integrable R ν ∧ (∫ ω, |R ω| ∂ν) ≤ T * Dc / (2 * Real.sqrt N) := by
  intro A R
  obtain ⟨hAi, hAae, hRm, hRi, hRb⟩ := periodic_adjoint_time_remainder_of_bound D T hT N hN Dc hDc ν ρ
    hρm q hgrad X hXm hA1
  refine ⟨?_, periodic_mean_drift_time_integrable D β T M hM ρ hρm hprob hρ q K hq hK hgrad hback, ?_,
    hRm, hRi, hRb⟩
  · intro r hr
    haveI := hprob r hr
    have hqm : Measurable (q r) := measurable_of_contDiff_lift ((hq r hr).of_le (by norm_num))
    have hi (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] : Integrable (q r) μ := by
      apply (integrable_const L).mono' hqm.aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hqB r hr z
    refine ⟨hi _, ?_⟩
    intro x
    exact integrable_sourceRieszLocalEmpiricalLaw N x _
  · filter_upwards [hAae, hIto] with ω ha hit
    obtain ⟨hie, he⟩ := periodic_adjoint_time_identity D β T M hM ρ hρm hprob hρ q K hq hK hgrad hback N
      (by omega) (fun r => X r ω) (m ω) ha hit hweak
    exact ⟨ha, hie, by simpa only [sub_eq_add_neg] using he⟩

/-- Finite-family terminal representation: `Z = A₀ + Σ θ_a √N m_a + R` with `E|R| ≲ N^{-1/2}`
(TeX 3933-3946). -/
theorem periodic_finite_terminal_representation (D : PeriodicForceData ι) (β M : ℝ) (hM : 0 ≤ M)
    (K : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) (k : ℕ) (t θ : Fin k → ℝ) (ht : ∀ a, t a ∈ Icc 0 T)
    (N : ℕ) (hN : 1 ≤ N) (Dc : ℝ) (hDc : 0 ≤ Dc)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hf : ∀ a, ∀ r ∈ Icc 0 (t a), ContDiff ℝ 2 (periodicLiftFn (f a r)))
    (hK : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ (K : ℝ))
    (hgrad : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (L : ℝ) (hL : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L)
    (hback : ∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)), PeriodicBackwardEq D.F β (ρ r) (f a) r)
    (X : ℝ → Ω → Fin N → PeriodicTorus ι) (hXm : Measurable (Function.uncurry X))
    (hA1 : ∀ a, ∀ r ∈ Icc 0 (t a),
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)| ∂ν) ≤ Dc / (N : ℝ))
    (m : Fin k → Ω → ℝ)
    (hIto : ∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
      (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
      (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift D.F β (f a) N r (X r ω)) + m a ω)
    (hweak : ∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
      (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
      ∫ r in Ioc 0 (t a), periodicMeanTestDrift D.F β (ρ r) (f a) r) :
    let R := fun ω => ∑ a, θ a * (-((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
      sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω))))
    let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
      dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
    let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
      dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
    Measurable A₀ ∧ Measurable Z ∧ Measurable R ∧ Integrable R ν ∧
    (∫ ω, |R ω| ∂ν) ≤ T * Dc * (∑ a, |θ a|) / (2 * Real.sqrt N) ∧
    Z =ᵐ[ν] (fun ω => A₀ ω + (∑ a, θ a * (Real.sqrt N * m a ω)) + R ω) := by
  intro R A₀ Z
  have hsub (a : Fin k) {r : ℝ} (hr : r ∈ Icc 0 (t a)) : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans (ht a).2⟩
  have hsingle (a : Fin k) := periodic_physical_adjoint_time_identity D β M hM K (t a) (ht a).1 N hN Dc hDc
    ν ρ hρm (fun r hr => hprob r (hsub a hr)) (fun r hr => hρ r (hsub a hr)) (f a) (hf a) (hK a)
    (hgrad a) L (hL a) (hback a) X hXm (hA1 a) (m a) (hIto a) (hweak a)
  have hRi (a : Fin k) : Integrable (fun ω => -((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
      sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)))) ν := (hsingle a).2.2.2.2.1
  have hRb (a : Fin k) : (∫ ω, |-((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
      sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)))| ∂ν) ≤
      T * Dc / (2 * Real.sqrt N) :=
    (hsingle a).2.2.2.2.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ht a).2 hDc) (by positivity))
  obtain ⟨hi, hb⟩ := sourceRiesz_finite_remainder_L1 ν k θ (fun a ω => -((Real.sqrt N / 2) *
    (∫ r in Ioc 0 (t a), sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
      (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)))) (T * Dc / (2 * Real.sqrt N)) hRi hRb
  have hXm' (r : ℝ) : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
  have hqm (a : Fin k) (r : ℝ) (hr : r ∈ Icc 0 (t a)) : Measurable (f a r) :=
    measurable_of_contDiff_lift ((hf a r hr).of_le (by norm_num))
  refine ⟨?_, ?_, ?_, hi, by convert hb using 1 <;> ring, ?_⟩
  · refine Finset.measurable_sum _ fun a _ => ?_
    haveI := hprob 0 (hsub a ⟨le_rfl, (ht a).1⟩)
    exact (((measurable_dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0)
      (hqm a 0 ⟨le_rfl, (ht a).1⟩) N hN).comp (hXm' 0)).const_mul _).const_mul _
  · refine Finset.measurable_sum _ fun a _ => ?_
    haveI := hprob (t a) (hsub a ⟨(ht a).1, le_rfl⟩)
    exact (((measurable_dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a))
      (hqm a (t a) ⟨(ht a).1, le_rfl⟩) N hN).comp (hXm' (t a))).const_mul _).const_mul _
  · exact Finset.measurable_sum _ fun a _ => ((hsingle a).2.2.2.1).const_mul _
  · filter_upwards [ae_all_iff.mpr (fun a => (hsingle a).2.2.1)] with ω hω
    calc
      _ = ∑ a, θ a * (Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0))
          (f a 0) N (X 0 ω) + Real.sqrt N * m a ω + -((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
            sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
              (periodicForcePair D.F (periodicGrad (f a r))) N (X r ω)))) :=
        Finset.sum_congr rfl fun a _ => congrArg (fun z => θ a * z) (hω a).2.2
      _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]; rfl

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_adjoint_physical_drift
#print axioms DGRHS.Periodic.periodic_mean_drift_eq_half_pair
#print axioms DGRHS.Periodic.measurable_periodicTransportEnergy_time
#print axioms DGRHS.Periodic.periodic_mean_drift_time_integrable
#print axioms DGRHS.Periodic.periodic_time_commutator_remainder_of_bound
#print axioms DGRHS.Periodic.periodic_adjoint_time_remainder_of_bound
#print axioms DGRHS.Periodic.periodic_adjoint_time_identity
#print axioms DGRHS.Periodic.periodic_physical_adjoint_time_identity
#print axioms DGRHS.Periodic.periodic_finite_terminal_representation
