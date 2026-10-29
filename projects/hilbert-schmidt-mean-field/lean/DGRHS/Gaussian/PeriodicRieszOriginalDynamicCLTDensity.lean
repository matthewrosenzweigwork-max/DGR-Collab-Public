import DGRHS.Gaussian.PeriodicRieszOriginalDynamicCLT
import DGRHS.Gaussian.PeriodicRieszCommon

/-!
Packet P11e, unit 2 (Riesz): the torus Theorem 2.13 original-class export with the uniform partition
bounds `K_{N,β}(μ^t) ≤ C_{β,T}` and `K_{N,2β}(μ^t) ≤ C_{2β,T}` (hypothesis (ii), TeX 877-881) derived
instead of assumed.

For `0 < s < d/2` the P11a constants `periodicRieszCommon_particle_weight` are chosen before the density
and depend on `(s, β, M, d)` only, hence also work for `2β`; the singular partition function is the
Gibbs weight (`periodicRieszSingularPartition_toReal_eq`).  This matches the Euclidean Riesz export, which
derives the same bounds from the density-uniform Theorem 2.2(i) constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- **Theorem 2.13 on the torus, positive Riesz case, weak mean-field class, partition bounds
derived.** -/
theorem exists_periodicRiesz_original_class_dynamic_joint_CLT_of_density
    (s β : ℝ) (T : ℝ≥0) (M Bmax : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax)
    (k : ℕ) (t : Fin k → ℝ≥0) (ht : ∀ a, t a ≤ T)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (Dtest : Submodule ℝ (PeriodicTorus ι → ℝ))
    (hwp : PeriodicBackwardClassicalWellPosed T (periodicRieszForceData s hs hs2).F β ρ Dtest)
    (hweak : PeriodicMeanFieldWeak (periodicRieszForceData s hs hs2).F β T ρ)
    (φ : Fin k → PeriodicTorus ι → ℝ) (hφD : ∀ a, φ a ∈ Dtest) :
    let f := fun a => periodicUprop T (periodicRieszForceData s hs hs2).F β ρ Dtest hwp (t a) (ht a)
      (φ a) (hφD a)
    ((∀ a, ∀ r ∈ Icc 0 (t a : ℝ),
      Integrable (f a r) (periodicCappedDensityMeasure (ρ r)) ∧
      (∀ z, Integrable (fun y => ⟪(periodicRieszForceData s hs hs2).F (z - y),
        periodicGrad (f a r) z - periodicGrad (f a r) y⟫) (periodicCappedDensityMeasure (ρ r))) ∧
      Integrable (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r)))
        ((periodicCappedDensityMeasure (ρ r)).prod (periodicCappedDensityMeasure (ρ r)))) ∧
    (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a : ℝ)),
      Integrable (fun z => deriv (fun u => f a u z) r + β⁻¹ * periodicLap (f a r) z)
        (periodicCappedDensityMeasure (ρ r)))) ∧
    let μ := periodicCappedDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let hh := periodicRieszCentered_memLp s hs2 (ρ 0) M (hρ 0 ⟨le_rfl, T.coe_nonneg⟩)
    ∃ (hφ : ∀ a, MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R0 v + β • integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b =>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ +
          (2 / β) * (∫ r in Ioc 0 (min (t a : ℝ) (t b : ℝ)),
            ∫ z, ⟪periodicGrad (f a r) z, periodicGrad (f b r) z⟫ ∂periodicCappedDensityMeasure (ρ r))
      let P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k, (∫ z, z a ∂P) = 0) ∧
      (∀ a b : Fin k, Integrable (fun z => z a * z b) P ∧ (∫ z, z a * z b ∂P) = C a b) ∧
      ∀ (Ω : ℕ → Type v) [∀ N, MeasurableSpace (Ω N)] (ν : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (ν N)]
        (Fil : ∀ N, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω N)))
        (X : ∀ N, ℝ → Ω N → Fin N → E) (B : ∀ N, (Fin N × ι) → ℝ≥0 → Ω N → ℝ),
      (∀ N, 1 ≤ N → PeriodicFiniteHorizonWeakSDE (periodicRieszForceData s hs hs2).F (ν N) (Fil N) T β N
        (X N) (B N)) →
      (∀ N, 1 ≤ N → PeriodicInitialGibbsBrownianData (ν N) (periodicRieszSingularGibbs s β hs2 (ρ 0) N)
        (X N 0) (B N)) →
      ∀ (G D : ℝ → ℝ), (∀ r ∈ Icc 0 (T : ℝ), 0 ≤ G r) → (∀ r ∈ Icc 0 (T : ℝ), D r ≤ Bmax) →
      (∀ N, 1 ≤ N → ∀ r (hr : r ∈ Icc 0 (T : ℝ)), haveI := hprob r hr;
        haveI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩;
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N
          ((ν N).map (fun ω => periodicProj N (X N r ω))) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (D r / (N : ℝ) : ℝ)) →
      (∀ Gmax : ℝ≥0, (∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ)) →
        ∀ N, 1 ≤ N → PeriodicItoAdmissibility (periodicRieszForceData s hs hs2).F (ν N) (Fil N) T β N k t
          μ f Gmax (X N) (B N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
          Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (φ a) N
            (periodicProj N (X N (t a) ω))))
        atTop id ν P := by
  obtain ⟨Cpart, -, hCpart⟩ := periodicRieszCommon_particle_weight (ι := ι) s β hs hβ.le hs2 M hM
  obtain ⟨C₂, -, hC₂⟩ := periodicRieszCommon_particle_weight (ι := ι) s (2 * β) hs (by linarith) hs2 M hM
  refine exists_periodicRiesz_original_class_dynamic_joint_CLT s β T M Bmax Cpart C₂ hs hβ hs2 hM hBmax k t
    ht ρ hρm hprob hρ ?_ ?_ Dtest hwp hweak φ hφD
  · intro r hr N' hN'
    haveI := hprob r hr
    rw [periodicRieszSingularPartition_toReal_eq s β hs hβ.le hs2 (ρ r) M hM (hρ r hr) N' hN']
    exact (hCpart (ρ r) (hρ r hr) N' hN').2.2
  · intro r hr N' hN'
    haveI := hprob r hr
    rw [periodicRieszSingularPartition_toReal_eq s (2 * β) hs (by linarith) hs2 (ρ r) M hM (hρ r hr) N' hN']
    exact (hC₂ (ρ r) (hρ r hr) N' hN').2.2

end DGRHS.Periodic
