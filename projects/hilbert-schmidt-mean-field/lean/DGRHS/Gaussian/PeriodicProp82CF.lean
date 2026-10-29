import DGRHS.Gaussian.PeriodicDynamicCF
import DGRHS.Gaussian.PeriodicProp82Terminal

/-!
Packet P11c, unit 3: Proposition 8.2, characteristic-function comparison, on the flat torus (Remark 2.1),
both kernels.  Torus forms of `exists_sourceRiesz_finite_terminal_CF_comparison` and
`exists_sourceLog_finite_terminal_CF_comparison`: constants `Dc, Dl` are chosen before the horizon, the
finite family, `N`, the probability space, the densities, the tests and the process; the comparison

`|E e^{iZ} - E e^{iA₀} exp(-(1/β) ∫_0^T ∫ S^r dμ^r dr)| ≤ T Dc Σ|θ|/(2√N)
   + exp((Gmax Σ|θ|)²T/β) T Dl (Σ|θ|)²/√N`

is derived from the terminal representation (Lemma 8.1(ii)), the bracket replacement (Lemma 8.1(iii) for
the pair tests `⟪∇̃f_a, ∇̃f_b⟫`) and the literal finite Itô formula for the phase (`hphase`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Dynamics
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Riesz: Proposition 8.2, characteristic-function comparison. -/
theorem exists_periodicRiesz_finite_terminal_CF_comparison
    (s β M Bmax Cpart C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax) (K Gmax : ℝ≥0) :
    ∃ Dc Dl : ℝ, 0 ≤ Dc ∧ 0 ≤ Dl ∧ ∀ (T : ℝ) (hT : 0 ≤ T), ∀ (k : ℕ) (t θ : Fin k → ℝ),
      (∀ a, t a ∈ Icc 0 T) → ∀ (N : ℕ), 1 ≤ N →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ → PeriodicTorus ι → ℝ), Measurable (Function.uncurry ρ) →
      ∀ (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r))),
      (∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M) →
      (∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' → (periodicRieszSingularPartition s β hs2 (ρ r) N').toReal ≤ Cpart) →
      (∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' →
        (periodicRieszSingularPartition s (2 * β) hs2 (ρ r) N').toReal ≤ C₂) →
      ∀ (f : Fin k → ℝ → PeriodicTorus ι → ℝ),
      (∀ a, ∀ r ∈ Icc 0 (t a), ContDiff ℝ 2 (periodicLiftFn (f a r))) →
      (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ (K : ℝ)) →
      (∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
        (Icc 0 (t a) ×ˢ univ)) →
      (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ)) →
      ∀ (L : ℝ), (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L) →
      (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),
        PeriodicBackwardEq (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) →
      ∀ (X : ℝ → Ω → Fin N → PeriodicTorus ι), Measurable (Function.uncurry X) →
      ∀ (G B : ℝ → ℝ), (∀ r ∈ Icc 0 T, 0 ≤ G r) → (∀ r ∈ Icc 0 T, B r ≤ Bmax) →
      (∀ r (hr : r ∈ Icc 0 T), haveI := hprob r hr; haveI := hprob 0 ⟨le_rfl, hT⟩;
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N (ν.map (X r)) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (B r / (N : ℝ) : ℝ)) →
      ∀ (m : Fin k → ℝ → Ω → ℝ), (∀ a, Measurable (Function.uncurry (m a))) →
      (∀ a ω, m a 0 ω = 0) →
      (∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
        (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
        (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift (periodicRieszForceData s hs hs2).F β (f a) N r
          (X r ω)) + m a (t a) ω) →
      (∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
        (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t a), periodicMeanTestDrift (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) →
      let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
      let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
      let W := fun r ω => ∑ a, θ a * (Real.sqrt N * m a (min r (t a)) ω)
      let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
      let Φ := fun r ω => sourceRieszFinitePhase (A₀ ω + W r ω)
      let chi := fun r => ∫ ω, Φ r ω ∂ν
      (∀ r ∈ Icc 0 T, chi r = chi 0 - (1 / β : ℝ) •
        (∫ u in 0..r, ∫ ω, Φ u ω * ((∫ z, S u z ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ) : ℂ) ∂ν)) →
      ‖(∫ ω, sourceRieszFinitePhase (Z ω) ∂ν) -
        (∫ ω, sourceRieszFinitePhase (A₀ ω) ∂ν) *
          (Real.exp (-(1 / β) * (∫ r in 0..T, ∫ z, S r z ∂periodicCappedDensityMeasure (ρ r))) : ℂ)‖ ≤
        T * Dc * (∑ a, |θ a|) / (2 * Real.sqrt N) +
          Real.exp ((((Gmax : ℝ) * (∑ a, |θ a|)) ^ 2 / β) * T) *
            (T * Dl * (∑ a, |θ a|) ^ 2 / Real.sqrt N) := by
  let K' : ℝ≥0 := K * (Fintype.card ι : ℝ≥0)
  obtain ⟨H, Dc, Dl, hH, hDc, hDl, htrans⟩ := periodicRieszDynamic_entropy_transfers (ι := ι) s β M Bmax
    (2 * (Gmax : ℝ) ^ 2) Cpart C₂ hs hβ hs2 hM hBmax (by positivity) K'
  have hc : 0 < (2 : ℝ) / β := div_pos (by norm_num) hβ
  refine ⟨Dc, (2 / β) * Dl, hDc, mul_nonneg hc.le hDl, ?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hCp hC₂ f hfd hK hgrad hfB L hL hback X hXm G B hG hB hE
    m hmm hm0 hIto hweak
  have hA1 : ∀ a, ∀ r ∈ Icc 0 (t a),
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r))) N (X r ω)| ∂ν) ≤
        Dc / (N : ℝ) := by
    intro a r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans (ht a).2⟩
    haveI := hprob r hr'
    haveI := hprob 0 ⟨le_rfl, hT⟩
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    haveI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := htrans (ρ 0) (ρ r) (hρ 0 ⟨le_rfl, hT⟩) (hρ r hr')
      (hCp r hr') (hC₂ r hr') N hN (ν.map (X r)) (G r) (B r) (hG r hr') (hB r hr') (hE r hr')
    have hv : LipschitzWith K' (periodicGrad (f a r)) :=
      periodicGrad_lipschitz (hfd a r hr) K (hK a r hr)
    obtain ⟨hai, hb⟩ := hcomm hv
    have hrw : periodicRieszTransportEnergy s 1 (periodicGrad (f a r)) (ρ r) N =
        sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r))) N := by
      funext ω
      change sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicRieszTransportKernel 1 s (periodicGrad (f a r))) N ω = _
      rw [periodicRieszTransportKernel_one]
      rfl
    rw [hrw] at hai hb
    have hi : Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r))) N (X r ω)) ν :=
      (integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact ⟨hi, hb⟩
  have hlin : ∀ r ∈ Icc 0 T, ∀ q : PeriodicTorus ι → ℝ, Measurable q → BddBelow (range q) →
      BddAbove (range q) → sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 →
      Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)| ∂ν) ≤
        Dl / Real.sqrt N := by
    intro r hr q hq hlo hup hosc
    haveI := hprob r hr
    haveI := hprob 0 ⟨le_rfl, hT⟩
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    haveI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨-, -, -, -, -, -, -, hlinear⟩ := htrans (ρ 0) (ρ r) (hρ 0 ⟨le_rfl, hT⟩) (hρ r hr)
      (hCp r hr) (hC₂ r hr) N hN (ν.map (X r)) (G r) (B r) (hG r hr) (hB r hr) (hE r hr)
    obtain ⟨-, -, -, hai, hb⟩ := hlinear q hq hlo hup hosc
    have hm := measurable_dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q hq N hN
    refine ⟨(integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai, ?_⟩
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact hb
  have h := periodic_finite_terminal_CF_comparison (periodicRieszForceData s hs hs2) β M hβ hM K Gmax T hT
    k t θ ht N hN Dc Dl hDc hDl ν ρ hρm hprob hρ f hfd hK hgrad hfB L hL hback X hXm hA1 hlin m hmm hm0
    hIto hweak
  intro A₀ Z W S Φ chi hphase
  have := h hphase
  convert this using 3

/-- LOG: Proposition 8.2, characteristic-function comparison. -/
theorem exists_periodicLog_finite_terminal_CF_comparison
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (M Amax Bmax Cpart C₂ : ℝ) (hM : 0 ≤ M) (hAmax : 0 ≤ Amax)
    (hBmax : 0 ≤ Bmax) (hCpart : 0 < Cpart) (K Gmax : ℝ≥0) :
    ∃ Dc Dl : ℝ, 0 ≤ Dc ∧ 0 ≤ Dl ∧ ∀ (T : ℝ) (hT : 0 ≤ T), ∀ (k : ℕ) (t θ : Fin k → ℝ),
      (∀ a, t a ∈ Icc 0 T) → ∀ (N : ℕ), 1 ≤ N →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ → PeriodicTorus ι → ℝ), Measurable (Function.uncurry ρ) →
      ∀ (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r))),
      (∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M) →
      (∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' → (periodicLogSingularPartition (β : ℝ) (ρ r) N').toReal ≤ Cpart) →
      (∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' →
        (periodicLogSingularPartition (2 * (β : ℝ)) (ρ r) N').toReal ≤ C₂) →
      ∀ (f : Fin k → ℝ → PeriodicTorus ι → ℝ),
      (∀ a, ∀ r ∈ Icc 0 (t a), ContDiff ℝ 2 (periodicLiftFn (f a r))) →
      (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ (K : ℝ)) →
      (∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
        (Icc 0 (t a) ×ˢ univ)) →
      (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ)) →
      ∀ (L : ℝ), (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L) →
      (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),
        PeriodicBackwardEq periodicLogForceData.F (β : ℝ) (ρ r) (f a) r) →
      ∀ (X : ℝ → Ω → Fin N → PeriodicTorus ι), Measurable (Function.uncurry X) →
      ∀ (G B : ℝ → ℝ), (∀ r ∈ Icc 0 T, 0 ≤ G r) → (∀ r ∈ Icc 0 T, G r ≤ Amax) →
      (∀ r ∈ Icc 0 T, B r ≤ Bmax) →
      (∀ r (hr : r ∈ Icc 0 T), haveI := hprob r hr; haveI := hprob 0 ⟨le_rfl, hT⟩;
        periodicLogTransportExtendedFreeEnergy (ρ r) M (β : ℝ) N (ν.map (X r)) ≤
        (G r : EReal) * periodicLogTransportExtendedFreeEnergy (ρ 0) M (β : ℝ) N
          (periodicLogSingularGibbs (β : ℝ) (ρ 0) N) + (B r / (N : ℝ) : ℝ)) →
      ∀ (m : Fin k → ℝ → Ω → ℝ), (∀ a, Measurable (Function.uncurry (m a))) →
      (∀ a ω, m a 0 ω = 0) →
      (∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
        (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
        (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift periodicLogForceData.F (β : ℝ) (f a) N r
          (X r ω)) + m a (t a) ω) →
      (∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
        (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t a), periodicMeanTestDrift periodicLogForceData.F (β : ℝ) (ρ r) (f a) r) →
      let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
      let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
      let W := fun r ω => ∑ a, θ a * (Real.sqrt N * m a (min r (t a)) ω)
      let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
      let Φ := fun r ω => sourceRieszFinitePhase (A₀ ω + W r ω)
      let chi := fun r => ∫ ω, Φ r ω ∂ν
      (∀ r ∈ Icc 0 T, chi r = chi 0 - (1 / (β : ℝ) : ℝ) •
        (∫ u in 0..r, ∫ ω, Φ u ω * ((∫ z, S u z ∂sourceRieszLocalEmpiricalLaw N (X u ω) : ℝ) : ℂ) ∂ν)) →
      ‖(∫ ω, sourceRieszFinitePhase (Z ω) ∂ν) -
        (∫ ω, sourceRieszFinitePhase (A₀ ω) ∂ν) *
          (Real.exp (-(1 / (β : ℝ)) * (∫ r in 0..T, ∫ z, S r z ∂periodicCappedDensityMeasure (ρ r))) : ℂ)‖ ≤
        T * Dc * (∑ a, |θ a|) / (2 * Real.sqrt N) +
          Real.exp ((((Gmax : ℝ) * (∑ a, |θ a|)) ^ 2 / (β : ℝ)) * T) *
            (T * Dl * (∑ a, |θ a|) ^ 2 / Real.sqrt N) := by
  let K' : ℝ≥0 := K * (Fintype.card ι : ℝ≥0) + 1
  have hK' : 0 < (K' : ℝ) := by
    have : (0 : ℝ) ≤ (K : ℝ) * (Fintype.card ι : ℝ) := by positivity
    simp only [K', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one]
    linarith
  obtain ⟨H, Dc, Dl, hH, hDc, hDl, htrans⟩ := periodicLogDynamic_entropy_transfers (ι := ι) β hβ K' hK' M hM
    Cpart C₂ Amax Bmax (2 * (Gmax : ℝ) ^ 2) hCpart hAmax hBmax (by positivity)
  have hc : 0 < (2 : ℝ) / (β : ℝ) := div_pos (by norm_num) hβ
  refine ⟨Dc, (2 / (β : ℝ)) * Dl, hDc, mul_nonneg hc.le hDl, ?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hCp hC₂ f hfd hK hgrad hfB L hL hback X hXm G B hG hGA hB hE
    m hmm hm0 hIto hweak
  have hA1 : ∀ a, ∀ r ∈ Icc 0 (t a),
      Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair periodicLogForceData.F (periodicGrad (f a r))) N (X r ω)) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair periodicLogForceData.F (periodicGrad (f a r))) N (X r ω)| ∂ν) ≤
        Dc / (N : ℝ) := by
    intro a r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans (ht a).2⟩
    haveI := hprob r hr'
    haveI := hprob 0 ⟨le_rfl, hT⟩
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    haveI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨-, -, -, -, -, -, hcomm, -⟩ := htrans (ρ 0) (ρ r) (hρ 0 ⟨le_rfl, hT⟩) (hρ r hr')
      (hCp r hr') (hC₂ r hr') N hN (ν.map (X r)) (G r) (B r) (hG r hr') (hGA r hr') (hB r hr') (hE r hr')
    have hv : LipschitzWith K' (periodicGrad (f a r)) :=
      (periodicGrad_lipschitz (hfd a r hr) K (hK a r hr)).weaken
        (by simp only [K']; exact le_add_of_nonneg_right zero_le)
    obtain ⟨hai, hb⟩ := hcomm hv
    have hrw : sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicLogTransportKernel 1 (periodicGrad (f a r))) N =
        sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicForcePair periodicLogForceData.F (periodicGrad (f a r))) N := by
      rw [periodicLogTransportKernel_one]
      rfl
    rw [hrw] at hai hb
    have hi : Integrable (fun ω => sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
        (periodicForcePair periodicLogForceData.F (periodicGrad (f a r))) N (X r ω)) ν :=
      (integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact ⟨hi, hb⟩
  have hlin : ∀ r ∈ Icc 0 T, ∀ q : PeriodicTorus ι → ℝ, Measurable q → BddBelow (range q) →
      BddAbove (range q) → sSup (range q) - sInf (range q) ≤ 2 * (Gmax : ℝ) ^ 2 →
      Integrable (fun ω => dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure (ρ r)) q N (X r ω)| ∂ν) ≤
        Dl / Real.sqrt N := by
    intro r hr q hq hlo hup hosc
    haveI := hprob r hr
    haveI := hprob 0 ⟨le_rfl, hT⟩
    have hXr : Measurable (X r) := hXm.comp (measurable_const.prodMk measurable_id)
    haveI : IsProbabilityMeasure (ν.map (X r)) :=
      (Measure.isProbabilityMeasure_map_iff hXr.aemeasurable).mpr inferInstance
    obtain ⟨-, -, -, -, -, -, -, hlinear⟩ := htrans (ρ 0) (ρ r) (hρ 0 ⟨le_rfl, hT⟩) (hρ r hr)
      (hCp r hr) (hC₂ r hr) N hN (ν.map (X r)) (G r) (B r) (hG r hr) (hGA r hr) (hB r hr) (hE r hr)
    obtain ⟨-, -, -, hai, hb⟩ := hlinear q hq hlo hup hosc
    refine ⟨(integrable_map_measure hai.aestronglyMeasurable hXr.aemeasurable).mp hai, ?_⟩
    rw [integral_map hXr.aemeasurable hai.abs.aestronglyMeasurable] at hb
    exact hb
  have h := periodic_finite_terminal_CF_comparison periodicLogForceData (β : ℝ) M hβ hM K Gmax T hT
    k t θ ht N hN Dc Dl hDc hDl ν ρ hρm hprob hρ f hfd hK hgrad hfB L hL hback X hXm hA1 hlin m hmm hm0
    hIto hweak
  intro A₀ Z W S Φ chi hphase
  have := h hphase
  convert this using 3

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicRiesz_finite_terminal_CF_comparison
#print axioms DGRHS.Periodic.exists_periodicLog_finite_terminal_CF_comparison
