import DGRHS.Gaussian.PeriodicRieszTheorem211
import DGRHS.Gaussian.PeriodicLogTheorem211
import DGRHS.Gaussian.PeriodicEquilibriumGeneric
import DGRHS.Gaussian.PeriodicRieszEquilibrium
import DGRHS.Gaussian.PeriodicLogEquilibrium
import DGRHS.Kernel.PositiveResolventBounds
import DGRHS.Kernel.FullNormCovarianceBounds
import DGRHS.CLT.EquilibriumZeroParticle

/-!
Packet P11b, unit 1: Remark 2.12 (`rem:staticCLTInterpretation`, TeX 832-845) on the flat torus
(Remark 2.1, TeX 492-496), for both the periodic Riesz kernel `0 < s < d/2` and the periodic LOG
kernel, in the exact shapes of the Euclidean exports

* `DGRHS.CLT.exists_sourceRieszCovarianceBounds`, `DGRHS.CLT.exists_sourceLogCovarianceBounds`
  (`CLT/SourceStaticCovarianceBounds.lean`): the two-sided covariance comparison
  `‖φ̄‖² / (1 + β ‖T_μ‖) ≤ Σ_{β,μ}(φ,φ) ≤ ‖φ̄‖²`, from the positivity of `T_μ` and the SAME
  constructed mean-zero inverse `(Id + β T_μ)^{-1}` of the torus static CLT;
* `DGRHS.CLT.sourceRiesz_equilibrium_canonical`, `sourceLog_equilibrium_canonical`,
  `sourceRiesz_equilibrium_law_allN`, `sourceLog_equilibrium_law_allN`
  (`CLT/SourceEquilibriumPhysical.lean`, `CLT/SourceEquilibriumAllN.lean`): under the thermal
  Euler-Lagrange relation `μ_β = Z⁻¹ e^{-β(V + h_{μ_β})}` (relative to normalized Haar measure) the
  literal modulated singular Gibbs law `Q_{N,β}(μ_β)` IS the collision-zero canonical ensemble
  `P_{N,β}` (`canonicalSingularLaw`), for every `N` including `N = 0`;
* `DGRHS.CLT.exists_sourceRieszCanonicalStatic`, `exists_sourceLogCanonicalStatic`
  (`CLT/SourceCanonicalStatic.lean`): the static linear-statistics CLT of Proposition 2.11 for the
  original canonical ensemble, together with the printed FULL-`L²` operator-norm covariance bounds.

Hypotheses: exactly those of the torus Proposition 2.11 exports (`0 ≤ β`, or `0 < β` where the
equilibrium relation is used, a probability density `ρ ≤ M` Haar-almost everywhere; for the LOG kernel
the Euclidean `hpair` is automatic on the torus), plus the Euler-Lagrange relation in the equilibrium
statements, which is the printed hypothesis `μ = μ_β` of the remark.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-! ### Riesz kernel -/

/-- Remark 2.12 on the torus (Riesz, `0 < s < d/2`): the two-sided covariance comparison, with the
mean-zero operator norm.  Shape of `DGRHS.CLT.exists_sourceRieszCovarianceBounds`. -/
theorem periodicRiesz_covarianceBounds (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R v) = v) ∧
      (∀ v, R (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      ∀ φ : Lp ℝ 2 μ,
        ‖DGRHS.Kernel.sourceCenteredL2 φ‖ ^ 2 /
            (1 + β * ‖DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan‖) ≤
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ) (R (DGRHS.Kernel.sourceCenteredL2 φ)) ∧
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ) (R (DGRHS.Kernel.sourceCenteredL2 φ)) ≤
          ‖DGRHS.Kernel.sourceCenteredL2 φ‖ ^ 2 := by
  intro μ h hh
  obtain ⟨hSym, hCan, R, hR1, hR2, -⟩ := exists_periodicRieszStatic 0 s β hs0 hβ hs2 ρ M hM hρ
  obtain ⟨-, -, hpos⟩ := periodicRieszKernel_properties s hs0 hs2 ρ M hM hρ
  exact ⟨hSym, hCan, R, hR1, hR2, fun φ => DGRHS.Kernel.meanZero_kernel_resolvent_quadratic_bounds
    _ _ hSym hCan hpos β hβ R hR1 (DGRHS.Kernel.sourceCenteredL2 φ)⟩

/-- Remark 2.12 on the torus (Riesz): under the thermal Euler-Lagrange relation the literal modulated
singular Gibbs law `Q_{N,β}(μ_β)` equals the collision-zero canonical ensemble `P_{N,β}` (positive
`N`), with proper canonical weight and positive finite normalizer.  Shape of
`DGRHS.CLT.sourceRiesz_equilibrium_canonical`. -/
theorem periodicRiesz_equilibrium_canonical (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicRieszKernel s hs2 (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    Integrable (fun x => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
    canonicalSingularPartition (periodicHaar ι) W V β N < ∞ ∧
    periodicRieszSingularGibbs s β hs2 ρ N = canonicalSingularLaw (periodicHaar ι) W V β N := by
  intro W
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hW : ∀ x y, W x y = W y x := by
    intro x y
    show periodicRieszKernel s hs2 (x - y) = periodicRieszKernel s hs2 (y - x)
    rw [← neg_sub y x, periodicRieszKernel_even]
  have hi := periodicRieszEnergyWeight_integrable s β hs hβ.le hs2 ρ M hM hρ N
  have hproper := equilibrium_modulated_eq_canonical (μ := μ) W hW V β N (by omega) hEL hi
  have href := equilibrium_product_reference (periodicHaar ι) μ
    (fun x => -β * (V x + DGRHS.potential μ W x)) hEL N
  letI : NeZero (Measure.pi (fun _ : Fin N => periodicHaar ι)) := ⟨href.2⟩
  have hcollision := href.1.ae_le (periodic_iid_collision_free ρ N)
  obtain ⟨hp, hfinite, hlaw⟩ := canonicalSingularLaw_eq_tilted (periodicHaar ι) W V β N
    hproper.1 hcollision
  refine ⟨hproper.1, hp, hfinite, ?_⟩
  rw [hlaw, ← hproper.2]
  rw [periodicRieszSingularGibbs_eq s β hs hβ.le hs2 ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  rfl

/-- Remark 2.12 on the torus (Riesz): the identification `Q_{N,β}(μ_β) = P_{N,β}` for EVERY `N`,
including the empty product convention `N = 0`.  Shape of
`DGRHS.CLT.sourceRiesz_equilibrium_law_allN`. -/
theorem periodicRiesz_equilibrium_law_allN (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicRieszKernel s hs2 (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) :
    periodicRieszSingularGibbs s β hs2 ρ N = canonicalSingularLaw (periodicHaar ι)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) V β N := by
  by_cases hz : N = 0
  · subst N
    rw [periodicRieszSingularGibbs_eq s β hs hβ.le hs2 ρ M hM hρ 0,
      ← sourceEnergyTilt_eq _ _ _ β 0, canonicalSingularLaw_zero]
    norm_num only [Nat.cast_zero]
    exact sourceEnergyTilt_zero (periodicHaar ι) (periodicCappedDensityMeasure ρ)
      (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)))
      (DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
      (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) β
  · exact (periodicRiesz_equilibrium_canonical s β hs hβ hs2 ρ M hM hρ V hEL N
      (Nat.one_le_iff_ne_zero.mpr hz)).2.2.2

/-- Remark 2.12 on the torus (Riesz): the printed static CLT for the ORIGINAL canonical ensemble
`P_{N,β}` (collision-zero canonical Gibbs law of the periodic Riesz Hamiltonian) under the thermal
Euler-Lagrange relation, with full `L²` tests, the characteristic-function limit, the bounded-test MGF
limit, and the printed FULL-`L²` operator-norm covariance bounds for the SAME constructed inverse.
Shape of `DGRHS.CLT.exists_sourceRieszCanonicalStatic`. -/
theorem exists_periodicRieszCanonicalStatic
    (m : ℕ) (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicRieszKernel s hs2 (a - b)) x)) = periodicCappedDensityMeasure ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R0 v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      (∀ ψ : Lp ℝ 2 μ,
        ‖DGRHS.Kernel.sourceCenteredL2 ψ‖ ^ 2 / (1 + β * ‖DGRHS.Kernel.integralOperator h hh‖) ≤
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ) (R0 (DGRHS.Kernel.sourceCenteredL2 ψ)) ∧
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ) (R0 (DGRHS.Kernel.sourceCenteredL2 ψ)) ≤
          ‖DGRHS.Kernel.sourceCenteredL2 ψ‖ ^ 2) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (canonicalSingularLaw (periodicHaar ι) W V β N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => canonicalSingularLaw (periodicHaar ι) W V β N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂canonicalSingularLaw (periodicHaar ι) W V β N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (canonicalSingularLaw (periodicHaar ι) W V β N)) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂canonicalSingularLaw (periodicHaar ι) W V β N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, R0, hR1, hR2, hStat⟩ :=
    exists_periodicRieszSingularStatic m s β hs hβ.le hs2 ρ M hM hρ
  obtain ⟨-, -, hpos⟩ := periodicRieszKernel_properties s hs hs2 ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, ?_, fun φ => ?_⟩
  · intro ψ
    exact DGRHS.Kernel.meanZero_kernel_resolvent_fullnorm_bounds _ _ hSym hCan hpos β hβ.le R0 hR1
      (DGRHS.Kernel.sourceCenteredL2 ψ)
  · obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, hMGF⟩ := hStat φ
    have he (N : ℕ) : periodicRieszSingularGibbs s β hs2 ρ N =
        canonicalSingularLaw (periodicHaar ι) W V β N :=
      periodicRiesz_equilibrium_law_allN s β hs hβ hs2 ρ M hM hρ V hEL N
    have hPN' (N : ℕ) : IsProbabilityMeasure (canonicalSingularLaw (periodicHaar ι) W V β N) := by
      rw [← he N]
      exact hPN N
    refine ⟨ν, Z, hν, hPN', ?_⟩
    simp only [he] at hw hCF hMGF
    exact ⟨hw, hG, hMean, hCov, hCF, hMGF⟩

/-! ### LOG kernel -/

/-- Remark 2.12 on the torus (LOG): the two-sided covariance comparison, with the mean-zero operator
norm.  Shape of `DGRHS.CLT.exists_sourceLogCovarianceBounds`; the Euclidean hypothesis `hpair` is
automatic on the torus. -/
theorem periodicLog_covarianceBounds (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    let hh := periodicLogCentered_memLp ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R v) = v) ∧
      (∀ v, R (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      ∀ φ : Lp ℝ 2 μ,
        ‖DGRHS.Kernel.sourceCenteredL2 φ‖ ^ 2 /
            (1 + β * ‖DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan‖) ≤
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ) (R (DGRHS.Kernel.sourceCenteredL2 φ)) ∧
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 φ) (R (DGRHS.Kernel.sourceCenteredL2 φ)) ≤
          ‖DGRHS.Kernel.sourceCenteredL2 φ‖ ^ 2 := by
  intro μ h hh
  obtain ⟨hSym, hCan, R, hR1, hR2, -⟩ := exists_periodicLogStatic 0 β hβ ρ M hM hρ
  obtain ⟨-, -, hpos⟩ := periodicLogKernel_properties ρ M hM hρ
  exact ⟨hSym, hCan, R, hR1, hR2, fun φ => DGRHS.Kernel.meanZero_kernel_resolvent_quadratic_bounds
    _ _ hSym hCan hpos β hβ R hR1 (DGRHS.Kernel.sourceCenteredL2 φ)⟩

/-- Remark 2.12 on the torus (LOG): under the thermal Euler-Lagrange relation the literal modulated
singular Gibbs law `Q_{N,β}(μ_β)` equals the collision-zero canonical ensemble `P_{N,β}` (positive
`N`).  Shape of `DGRHS.CLT.sourceLog_equilibrium_canonical`. -/
theorem periodicLog_equilibrium_canonical (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    Integrable (fun x => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
    canonicalSingularPartition (periodicHaar ι) W V β N < ∞ ∧
    periodicLogSingularGibbs β ρ N = canonicalSingularLaw (periodicHaar ι) W V β N := by
  intro W
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hW : ∀ x y, W x y = W y x := by
    intro x y
    show periodicLogKernel (x - y) = periodicLogKernel (y - x)
    rw [← neg_sub y x, periodicLogKernel_even]
  have hi := periodicLogEnergyWeight_integrable β hβ.le ρ M hM hρ N
  have hproper := equilibrium_modulated_eq_canonical (μ := μ) W hW V β N (by omega) hEL hi
  have href := equilibrium_product_reference (periodicHaar ι) μ
    (fun x => -β * (V x + DGRHS.potential μ W x)) hEL N
  letI : NeZero (Measure.pi (fun _ : Fin N => periodicHaar ι)) := ⟨href.2⟩
  have hcollision := href.1.ae_le (periodic_iid_collision_free ρ N)
  obtain ⟨hp, hfinite, hlaw⟩ := canonicalSingularLaw_eq_tilted (periodicHaar ι) W V β N
    hproper.1 hcollision
  refine ⟨hproper.1, hp, hfinite, ?_⟩
  rw [hlaw, ← hproper.2]
  rw [periodicLogSingularGibbs_eq β hβ.le ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  rfl

/-- Remark 2.12 on the torus (LOG): the identification `Q_{N,β}(μ_β) = P_{N,β}` for EVERY `N`,
including the empty product convention `N = 0`.  Shape of
`DGRHS.CLT.sourceLog_equilibrium_law_allN`. -/
theorem periodicLog_equilibrium_law_allN (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) :
    periodicLogSingularGibbs β ρ N = canonicalSingularLaw (periodicHaar ι)
      (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) V β N := by
  by_cases hz : N = 0
  · subst N
    rw [periodicLogSingularGibbs_eq β hβ.le ρ M hM hρ 0,
      ← sourceEnergyTilt_eq _ _ _ β 0, canonicalSingularLaw_zero]
    norm_num only [Nat.cast_zero]
    exact sourceEnergyTilt_zero (periodicHaar ι) (periodicCappedDensityMeasure ρ)
      (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
      (DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
      (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) β
  · exact (periodicLog_equilibrium_canonical β hβ ρ M hM hρ V hEL N
      (Nat.one_le_iff_ne_zero.mpr hz)).2.2.2

/-- Remark 2.12 on the torus (LOG): the printed static CLT for the ORIGINAL canonical ensemble
`P_{N,β}` under the thermal Euler-Lagrange relation, with the printed FULL-`L²` operator-norm
covariance bounds.  Shape of `DGRHS.CLT.exists_sourceLogCanonicalStatic`. -/
theorem exists_periodicLogCanonicalStatic
    (m : ℕ) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := periodicLogCentered_memLp ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R0 v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      (∀ ψ : Lp ℝ 2 μ,
        ‖DGRHS.Kernel.sourceCenteredL2 ψ‖ ^ 2 / (1 + β * ‖DGRHS.Kernel.integralOperator h hh‖) ≤
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ) (R0 (DGRHS.Kernel.sourceCenteredL2 ψ)) ∧
        inner ℝ (DGRHS.Kernel.sourceCenteredL2 ψ) (R0 (DGRHS.Kernel.sourceCenteredL2 ψ)) ≤
          ‖DGRHS.Kernel.sourceCenteredL2 ψ‖ ^ 2) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (canonicalSingularLaw (periodicHaar ι) W V β N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => canonicalSingularLaw (periodicHaar ι) W V β N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂canonicalSingularLaw (periodicHaar ι) W V β N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (canonicalSingularLaw (periodicHaar ι) W V β N)) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂canonicalSingularLaw (periodicHaar ι) W V β N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, R0, hR1, hR2, hStat⟩ := exists_periodicLogSingularStatic m β hβ.le ρ M hM hρ
  obtain ⟨-, -, hpos⟩ := periodicLogKernel_properties ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, ?_, fun φ => ?_⟩
  · intro ψ
    exact DGRHS.Kernel.meanZero_kernel_resolvent_fullnorm_bounds _ _ hSym hCan hpos β hβ.le R0 hR1
      (DGRHS.Kernel.sourceCenteredL2 ψ)
  · obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, hMGF⟩ := hStat φ
    have he (N : ℕ) : periodicLogSingularGibbs β ρ N =
        canonicalSingularLaw (periodicHaar ι) W V β N :=
      periodicLog_equilibrium_law_allN β hβ ρ M hM hρ V hEL N
    have hPN' (N : ℕ) : IsProbabilityMeasure (canonicalSingularLaw (periodicHaar ι) W V β N) := by
      rw [← he N]
      exact hPN N
    refine ⟨ν, Z, hν, hPN', ?_⟩
    simp only [he] at hw hCF hMGF
    exact ⟨hw, hG, hMean, hCov, hCF, hMGF⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRiesz_covarianceBounds
#print axioms DGRHS.Periodic.periodicRiesz_equilibrium_canonical
#print axioms DGRHS.Periodic.periodicRiesz_equilibrium_law_allN
#print axioms DGRHS.Periodic.exists_periodicRieszCanonicalStatic
#print axioms DGRHS.Periodic.periodicLog_covarianceBounds
#print axioms DGRHS.Periodic.periodicLog_equilibrium_canonical
#print axioms DGRHS.Periodic.periodicLog_equilibrium_law_allN
#print axioms DGRHS.Periodic.exists_periodicLogCanonicalStatic
