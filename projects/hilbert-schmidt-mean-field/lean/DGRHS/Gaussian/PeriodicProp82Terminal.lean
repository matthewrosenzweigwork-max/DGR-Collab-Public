import DGRHS.Gaussian.PeriodicDynamicTerminal
import DGRHS.Gaussian.PeriodicForceData
import DGRHS.Gaussian.PeriodicRieszDynamicTransfers
import DGRHS.Gaussian.PeriodicLogDynamicTransfers

/-!
Packet P11c, unit 3: Proposition 8.2 (`prop:finiteNAdjointDuality`, TeX 3859-3877), terminal
representation, on the flat torus (Remark 2.1), both kernels.

Torus forms of `exists_sourceRiesz_finite_terminal_representation` and
`exists_sourceLog_finite_terminal_representation`: one constant `D` is chosen before the horizon, the
finite family, the particle number, the probability space, the density family, the tests and the process;
the terminal representation `Z = A₀ + Σ θ_a √N m_a + R` and the `L¹` rate `E|R| ≤ T D Σ|θ|/(2√N)` are
derived from the primitive particle Itô identity (`hIto`), the mean-field weak identity (`hweak`), the
backward equation (`hback`) and the free-energy Gronwall estimate (`hE`), through Lemma 8.1(ii).
Tests are differentiated through their lifts (`periodicLiftFn`, `periodicGrad`, `periodicLap`); the Hessian
bound `K` is for the lift and the torus sup-metric Lipschitz constant of `∇f` is `K d` (`d = card ι`).
The partition bounds (ii) enter as `K_{N,β}(μ^r) ≤ Cpart`, `K_{N,2β}(μ^r) ≤ C₂` (printed, `N`-uniform).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Laplacian Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Riesz: Proposition 8.2, terminal representation. -/
theorem exists_periodicRiesz_finite_terminal_representation
    (s β M Bmax Cpart C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax) (K : ℝ≥0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : ℝ) (hT : 0 ≤ T), ∀ (k : ℕ) (t θ : Fin k → ℝ), (∀ a, t a ∈ Icc 0 T) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (Ω : Type v) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
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
      ∀ (L : ℝ), (∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L) →
      (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),
        PeriodicBackwardEq (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) →
      ∀ (X : ℝ → Ω → Fin N → PeriodicTorus ι), Measurable (Function.uncurry X) →
      ∀ (G B : ℝ → ℝ), (∀ r ∈ Icc 0 T, 0 ≤ G r) → (∀ r ∈ Icc 0 T, B r ≤ Bmax) →
      (∀ r (hr : r ∈ Icc 0 T), haveI := hprob r hr; haveI := hprob 0 ⟨le_rfl, hT⟩;
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N (ν.map (X r)) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (B r / (N : ℝ) : ℝ)) →
      ∀ (m : Fin k → Ω → ℝ),
      (∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
        (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
        (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift (periodicRieszForceData s hs hs2).F β (f a) N r
          (X r ω)) + m a ω) →
      (∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
        (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t a), periodicMeanTestDrift (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) →
      let R := fun ω => ∑ a, θ a * (-((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
        sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicRieszTransportKernel 1 s (periodicGrad (f a r))) N (X r ω))))
      let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
      let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
      Measurable A₀ ∧ Measurable Z ∧ Measurable R ∧ Integrable R ν ∧
      (∫ ω, |R ω| ∂ν) ≤ T * D * (∑ a, |θ a|) / (2 * Real.sqrt N) ∧
      Z =ᵐ[ν] (fun ω => A₀ ω + (∑ a, θ a * (Real.sqrt N * m a ω)) + R ω) := by
  let K' : ℝ≥0 := K * (Fintype.card ι : ℝ≥0)
  obtain ⟨H, Dc, Dl, hH, hDc, hDl, htrans⟩ := periodicRieszDynamic_entropy_transfers (ι := ι) s β M Bmax 0
    Cpart C₂ hs hβ hs2 hM hBmax le_rfl K'
  refine ⟨Dc, hDc, ?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hCp hC₂ f hf hK hgrad L hL hback X hXm G B hG hB hE m
    hIto hweak
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
      periodicGrad_lipschitz (hf a r hr) K (hK a r hr)
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
  have h := periodic_finite_terminal_representation (periodicRieszForceData s hs hs2) β M hM K T hT k t θ
    ht N hN Dc hDc ν ρ hρm hprob hρ f hf hK hgrad L hL hback X hXm hA1 m hIto hweak
  have hrw (a : Fin k) (r : ℝ) : periodicRieszTransportKernel 1 s (periodicGrad (f a r)) =
      periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r)) :=
    periodicRieszTransportKernel_one s _
  simp only [hrw]
  exact h

/-- LOG: Proposition 8.2, terminal representation.  The torus LOG kernel is bounded below, so the
extended-energy hypothesis of Theorem 2.13 (`eq:dynamicUniformLogEnergy`) and the lower partition bound
`c` are theorems here, not hypotheses (see `periodicLogDynamic_entropy_transfers`). -/
theorem exists_periodicLog_finite_terminal_representation
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (M Amax Bmax Cpart C₂ : ℝ) (hM : 0 ≤ M) (hAmax : 0 ≤ Amax)
    (hBmax : 0 ≤ Bmax) (hCpart : 0 < Cpart) (K : ℝ≥0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : ℝ) (hT : 0 ≤ T), ∀ (k : ℕ) (t θ : Fin k → ℝ), (∀ a, t a ∈ Icc 0 T) →
      ∀ (N : ℕ), 1 ≤ N → ∀ (Ω : Type v) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
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
      ∀ (m : Fin k → Ω → ℝ),
      (∀ a, ∀ᵐ ω ∂ν, (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω)) -
        (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
        (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift periodicLogForceData.F (β : ℝ) (f a) N r
          (X r ω)) + m a ω) →
      (∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
        (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t a), periodicMeanTestDrift periodicLogForceData.F (β : ℝ) (ρ r) (f a) r) →
      let R := fun ω => ∑ a, θ a * (-((Real.sqrt N / 2) * (∫ r in Ioc 0 (t a),
        sourceTransportEnergy (periodicCappedDensityMeasure (ρ r))
          (periodicLogTransportKernel 1 (periodicGrad (f a r))) N (X r ω))))
      let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X 0 ω))
      let Z := fun ω => ∑ a, θ a * (Real.sqrt N *
        dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X (t a) ω))
      Measurable A₀ ∧ Measurable Z ∧ Measurable R ∧ Integrable R ν ∧
      (∫ ω, |R ω| ∂ν) ≤ T * D * (∑ a, |θ a|) / (2 * Real.sqrt N) ∧
      Z =ᵐ[ν] (fun ω => A₀ ω + (∑ a, θ a * (Real.sqrt N * m a ω)) + R ω) := by
  let K' : ℝ≥0 := K * (Fintype.card ι : ℝ≥0) + 1
  have hK' : 0 < (K' : ℝ) := by
    have : (0 : ℝ) ≤ (K : ℝ) * (Fintype.card ι : ℝ) := by positivity
    simp only [K', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_one]
    linarith
  obtain ⟨H, Dc, Dl, hH, hDc, hDl, htrans⟩ := periodicLogDynamic_entropy_transfers (ι := ι) β hβ K' hK' M hM
    Cpart C₂ Amax Bmax 0 hCpart hAmax hBmax le_rfl
  refine ⟨Dc, hDc, ?_⟩
  intro T hT k t θ ht N hN Ω _ ν _ ρ hρm hprob hρ hCp hC₂ f hf hK hgrad L hL hback X hXm G B hG hGA hB hE m
    hIto hweak
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
      (periodicGrad_lipschitz (hf a r hr) K (hK a r hr)).weaken
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
  have h := periodic_finite_terminal_representation periodicLogForceData (β : ℝ) M hM K T hT k t θ
    ht N hN Dc hDc ν ρ hρm hprob hρ f hf hK hgrad L hL hback X hXm hA1 m hIto hweak
  have hrw (a : Fin k) (r : ℝ) : periodicLogTransportKernel 1 (periodicGrad (f a r)) =
      periodicForcePair periodicLogForceData.F (periodicGrad (f a r)) :=
    periodicLogTransportKernel_one _
  simp only [hrw]
  exact h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicRiesz_finite_terminal_representation
#print axioms DGRHS.Periodic.exists_periodicLog_finite_terminal_representation
