import DGRHS.Gaussian.PeriodicMeanFieldWeak
import DGRHS.Gaussian.PeriodicLogNamedDynamicCLT

/-!
Packet P11e, unit 1 (LOG): Theorem 2.13 (`thm:dynamicLinearStatisticsCLT`, TeX 862-914) on the flat torus
(Remark 2.1), LOG case `s = 0`, with the mean-field trajectory in the printed class.

The hypotheses are exactly those of `exists_periodicLog_named_Uprop_dynamic_joint_CLT` except that
`PeriodicMeanFieldTimeTested` is replaced by `PeriodicMeanFieldWeak` (narrowly continuous path of
probability measures with bounded densities satisfying the mean-field equation (2.32) in the distributional
sense against smooth tests, owner convention `OWNER_DECISIONS_20261006.md` 1.2).  The time-tested
identity is derived by `periodicMeanFieldWeak_timeTested`; the extended log energy is part of the class
(it is a theorem on the torus, `periodicLog_interaction_ge`).  The conclusion is that of the named theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- **Theorem 2.13 on the torus, LOG case, with the mean-field trajectory in the weak class**
(`thm:dynamicLinearStatisticsCLT`, TeX 862-914; Remark 2.1; narrow continuity, owner convention). -/
theorem exists_periodicLog_original_class_dynamic_joint_CLT
    (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (T : ℝ≥0) (M Amax Bmax Cpart C₂ : ℝ) (hM : 0 ≤ M)
    (hAmax : 0 ≤ Amax) (hBmax : 0 ≤ Bmax) (hCpart : 0 < Cpart)
    (k : ℕ) (t : Fin k → ℝ≥0) (ht : ∀ a, t a ≤ T)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (hCp : ∀ r ∈ Icc 0 (T : ℝ), ∀ N' : ℕ, 1 ≤ N' →
      (periodicLogSingularPartition (β : ℝ) (ρ r) N').toReal ≤ Cpart)
    (hC₂ : ∀ r ∈ Icc 0 (T : ℝ), ∀ N' : ℕ, 1 ≤ N' →
      (periodicLogSingularPartition (2 * (β : ℝ)) (ρ r) N').toReal ≤ C₂)
    (Dtest : Submodule ℝ (PeriodicTorus ι → ℝ))
    (hwp : PeriodicBackwardClassicalWellPosed T periodicLogForceData.F (β : ℝ) ρ Dtest)
    (hweak : PeriodicMeanFieldWeak periodicLogForceData.F (β : ℝ) T ρ)
    (φ : Fin k → PeriodicTorus ι → ℝ) (hφD : ∀ a, φ a ∈ Dtest) :
    let f := fun a => periodicUprop T periodicLogForceData.F (β : ℝ) ρ Dtest hwp (t a) (ht a)
      (φ a) (hφD a)
    ((∀ a, ∀ r ∈ Icc 0 (t a : ℝ),
      Integrable (f a r) (periodicCappedDensityMeasure (ρ r)) ∧
      (∀ z, Integrable (fun y => ⟪periodicLogForceData.F (z - y),
        periodicGrad (f a r) z - periodicGrad (f a r) y⟫) (periodicCappedDensityMeasure (ρ r))) ∧
      Integrable (periodicForcePair periodicLogForceData.F (periodicGrad (f a r)))
        ((periodicCappedDensityMeasure (ρ r)).prod (periodicCappedDensityMeasure (ρ r)))) ∧
    (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a : ℝ)),
      Integrable (fun z => deriv (fun u => f a u z) r + (β : ℝ)⁻¹ * periodicLap (f a r) z)
        (periodicCappedDensityMeasure (ρ r)))) ∧
    let μ := periodicCappedDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    let hh := periodicLogCentered_memLp (ρ 0) M (hρ 0 ⟨le_rfl, T.coe_nonneg⟩)
    ∃ (hφ : ∀ a, MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R0 v + (β : ℝ) • integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + (β : ℝ) • integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b =>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ +
          (2 / (β : ℝ)) * (∫ r in Ioc 0 (min (t a : ℝ) (t b : ℝ)),
            ∫ z, ⟪periodicGrad (f a r) z, periodicGrad (f b r) z⟫ ∂periodicCappedDensityMeasure (ρ r))
      let P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k, (∫ z, z a ∂P) = 0) ∧
      (∀ a b : Fin k, Integrable (fun z => z a * z b) P ∧ (∫ z, z a * z b ∂P) = C a b) ∧
      ∀ (Ω : ℕ → Type v) [∀ N, MeasurableSpace (Ω N)] (ν : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (ν N)]
        (Fil : ∀ N, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω N)))
        (X : ∀ N, ℝ → Ω N → Fin N → E) (B : ∀ N, (Fin N × ι) → ℝ≥0 → Ω N → ℝ),
      (∀ N, 1 ≤ N → PeriodicFiniteHorizonWeakSDE periodicLogForceData.F (ν N) (Fil N) T (β : ℝ) N
        (X N) (B N)) →
      (∀ N, 1 ≤ N → PeriodicInitialGibbsBrownianData (ν N) (periodicLogSingularGibbs (β : ℝ) (ρ 0) N)
        (X N 0) (B N)) →
      ∀ (G D : ℝ → ℝ), (∀ r ∈ Icc 0 (T : ℝ), 0 ≤ G r) → (∀ r ∈ Icc 0 (T : ℝ), G r ≤ Amax) →
      (∀ r ∈ Icc 0 (T : ℝ), D r ≤ Bmax) →
      (∀ N, 1 ≤ N → ∀ r (hr : r ∈ Icc 0 (T : ℝ)), haveI := hprob r hr;
        haveI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩;
        periodicLogTransportExtendedFreeEnergy (ρ r) M (β : ℝ) N
          ((ν N).map (fun ω => periodicProj N (X N r ω))) ≤
        (G r : EReal) * periodicLogTransportExtendedFreeEnergy (ρ 0) M (β : ℝ) N
          (periodicLogSingularGibbs (β : ℝ) (ρ 0) N) + (D r / (N : ℝ) : ℝ)) →
      (∀ Gmax : ℝ≥0, (∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ)) →
        ∀ N, 1 ≤ N → PeriodicItoAdmissibility periodicLogForceData.F (ν N) (Fil N) T (β : ℝ) N k t
          μ f Gmax (X N) (B N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
          Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (φ a) N
            (periodicProj N (X N (t a) ω))))
        atTop id ν P :=
  exists_periodicLog_named_Uprop_dynamic_joint_CLT β hβ T M Amax Bmax Cpart C₂ hM hAmax hBmax hCpart k t ht ρ
    hρm hprob hρ hCp hC₂ Dtest hwp
    (periodicMeanFieldWeak_timeTested periodicLogForceData (β : ℝ) T ρ M hM hprob hρ Dtest hweak)
    φ hφD

end DGRHS.Periodic
