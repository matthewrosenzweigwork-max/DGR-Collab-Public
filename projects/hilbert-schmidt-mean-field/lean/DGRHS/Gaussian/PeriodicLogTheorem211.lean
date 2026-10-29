import DGRHS.Gaussian.PeriodicLogOperatorPositive
import DGRHS.Gaussian.PeriodicLogTheorem22i
import DGRHS.CLT.SourceStaticCharacteristic
import DGRHS.CLT.SourceFiniteMGF
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Kernel.MeanZeroResolventUnique

/-!
Packet P9g, unit 1: Proposition 2.11 (static linear-statistics CLT, TeX 805-831, proof 3617-3760)
for the torus LOG gas (Remark 2.1), the exact torus transcription of
`DGRHS.CLT.exists_sourceLogStatic` / `exists_sourceLogSingularStatic` (CLT/SourceLogStatic.lean,
CLT/SourceLogLiteralStatic.lean), mirroring the torus Riesz transcription `exists_periodicRieszStatic`.
The generic CLT machinery (`exists_sourceStaticCharacteristic`, `exists_sourceFiniteMGF`,
`meanZeroResolvent_unique`) is reused unchanged; the torus inputs are the LOG kernel properties
(symmetry, canonicity, positivity of `T_μ` via the heat-shift `L²` limit), the proper doubled moments
of the modulated weights (`periodicLogKernel_uniform_exponential`) and the literal singular Gibbs law.
Hypotheses: `0 ≤ β`, a probability density `ρ ≤ M` Haar-a.e.; the Euclidean `hpair`
(`eq:logEnergyAssumption`) is automatic on the torus (`periodicLogKernel ∈ L²(Haar)`), and
`T_μ ≥ 0` holds with no tail assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Centered exact periodic LOG kernel (the periodic `h̃`). -/
abbrev periodicLogCentered (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))

lemma periodicLogCentered_memLp
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (periodicLogCentered (periodicCappedDensityMeasure ρ)) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  periodicCenteredPair_memLp_of_density_cap ρ M hρ _ periodicLogKernel_measurable.stronglyMeasurable
    periodicLogKernel_memLp

lemma periodicLogCentered_data
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Measurable (periodicLogCentered (periodicCappedDensityMeasure ρ)) ∧
    (∀ᵐ p ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ),
      periodicLogCentered (periodicCappedDensityMeasure ρ) p.swap =
        periodicLogCentered (periodicCappedDensityMeasure ρ) p) ∧
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, periodicLogCentered (periodicCappedDensityMeasure ρ) (x, y)
        ∂periodicCappedDensityMeasure ρ) = 0) := by
  refine ⟨(stronglyMeasurable_hoeffdingCentered _ _
    (periodicLogKernel_measurable.stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd))).measurable, ?_, ?_⟩
  · apply Filter.Eventually.of_forall
    intro p
    exact DGRHS.centeredKernel_symmetric (periodicCappedDensityMeasure ρ)
      (fun a b => periodicLogKernel (a - b))
      (fun a b => by rw [← periodicLogKernel_even (b - a), neg_sub]) p.2 p.1
  · exact DGRHS.integral_centeredKernel_right (periodicCappedDensityMeasure ρ)
      (fun a b => periodicLogKernel (a - b))
      (periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable)

/-- Kernel properties used by the static CLT. -/
theorem periodicLogKernel_properties (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicLogCentered μ
    let hh := periodicLogCentered_memLp ρ M hρ
    (∀ᵐ p ∂μ.prod μ, h p.swap = h p) ∧ (∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0) ∧
    (∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) := by
  obtain ⟨_, hSym, hCan⟩ := periodicLogCentered_data ρ M hρ
  exact ⟨hSym, hCan, periodicLogOperator_positive_all ρ M hM hρ _⟩

/-- Proper modulated weights with uniform moments (torus form of `sourceLogWeight_uniform`). -/
theorem periodicLogWeight_uniform (γ : ℝ) (hγ : 0 ≤ γ) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := periodicLogCentered μ
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ, ∀ N,
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (sourceParticleExponent h F I γ N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  intro μ W h F I
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicLogKernel_integrable)
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicLogKernel_potential_abs_le ρ M hM hρ x)
  obtain ⟨C, hC⟩ := periodicLogKernel_uniform_exponential γ hγ ρ M hM hρ
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (γ * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
    intro N hN
    have hb := (hC N hN).2
    rw [he N] at hb
    exact hb
  exact ⟨hF, max (Real.exp (γ * ((M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι) - I)) * C)
    (Real.exp (-γ * I)), sourceWeight_of_canonical_moments h F hF _ hK I γ hγ C hProper hBound⟩

theorem periodicLogWeight_higher (β p : ℝ) (hβ : 0 ≤ β) (hp : 0 ≤ p) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := periodicLogCentered μ
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ, ∀ N,
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (p * sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (p * sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  simpa only [sourceParticleExponent_mul_parameter] using
    periodicLogWeight_uniform (p * β) (mul_nonneg hp hβ) ρ M hM hρ

/-- The literal singular Gibbs law `Q_{N,β}(μ)` on the torus, including `β = 0`, `N = 0` and the
collision-zero convention. -/
def periodicLogSingularGibbs (β : ℝ)
    (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : Measure (Fin N → PeriodicTorus ι) :=
  (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).withDensity
    (fun x => periodicLogSingularWeight β ρ N x / periodicLogSingularPartition β ρ N)

lemma periodicLogSingularGibbs_eq (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    periodicLogSingularGibbs β ρ N = (Measure.pi (fun _ : Fin N => μ)).tilted
      (sourceParticleExponent (periodicLogCentered μ)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) β N) := by
  dsimp only
  rw [← sourceEnergyTilt_eq _ _ _ β N]
  have hi := periodicLogEnergyWeight_integrable β hβ ρ M hM hρ N
  unfold periodicLogSingularGibbs Measure.tilted
  apply withDensity_congr_ae
  filter_upwards [periodicLogSingularWeight_ae β ρ N] with x hx
  rw [hx, periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N]
  unfold periodicLogSourcePartition
  exact (ENNReal.ofReal_div_of_pos (integral_exp_pos hi)).symm

lemma periodicLogSingularGibbs_probability (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    IsProbabilityMeasure (periodicLogSingularGibbs β ρ N) := by
  rw [periodicLogSingularGibbs_eq β hβ ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  exact isProbabilityMeasure_tilted (periodicLogEnergyWeight_integrable β hβ ρ M hM hρ N)


/-- Proposition 2.11 on the torus (LOG), for the physical canonical tilt. -/
theorem exists_periodicLogStatic
    (m : ℕ) (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
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
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x)))),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => ((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x)))) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, hPos⟩ := periodicLogKernel_properties ρ M hM hρ
  obtain ⟨R0, hR1, hR2, hStat⟩ := exists_sourceStaticCharacteristic m h hh hSym hCan hPos β hβ
  obtain ⟨T0, hT1, hT2, hMGF⟩ := exists_sourceFiniteMGF h hh hSym hCan hPos β hβ
  have hRT : R0 = T0 := DGRHS.Kernel.meanZeroResolvent_unique h hh hSym hCan β R0 T0 hR1 hT2
  rw [← hRT] at hMGF
  obtain ⟨hF, C2, hC2⟩ := periodicLogWeight_higher β 2 hβ (by norm_num) ρ M hM hρ
  obtain ⟨_, C4, hC4⟩ := periodicLogWeight_higher β 4 hβ (by norm_num) ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, fun φ => ?_⟩
  obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF⟩ := hStat φ F hF I 2 C2 (by norm_num)
    (fun N => (hC2 N).1) (fun N => (hC2 N).2)
  refine ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, fun K θ hK => ?_⟩
  exact hMGF m φ K θ hK F hF I 2 C4 (by norm_num)
    (fun N => by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using (hC4 N).1)
    (fun N => by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using (hC4 N).2)

/-- Proposition 2.11 on the torus (LOG) under the literal singular Gibbs law
`Q_{N,β}(μ)` (collision weight `0` for `β > 0`, `1` for `β = 0`), with full `L²` tests, the
characteristic-function limit and the bounded-test MGF limit (TeX 805-831). -/
theorem exists_periodicLogSingularStatic
    (m : ℕ) (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
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
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (periodicLogSingularGibbs β ρ N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => periodicLogSingularGibbs β ρ N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂periodicLogSingularGibbs β ρ N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (periodicLogSingularGibbs β ρ N)) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂periodicLogSingularGibbs β ρ N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, R0, hR1, hR2, hStat⟩ := exists_periodicLogStatic m β hβ ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, fun φ => ?_⟩
  obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, hMGF⟩ := hStat φ
  have he (N : ℕ) : periodicLogSingularGibbs β ρ N =
      (Measure.pi (fun _ : Fin N => μ)).tilted
        (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x) := by
    rw [periodicLogSingularGibbs_eq β hβ ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  have hPN' (N : ℕ) : IsProbabilityMeasure (periodicLogSingularGibbs β ρ N) :=
    periodicLogSingularGibbs_probability β hβ ρ M hM hρ N
  refine ⟨ν, Z, hν, hPN', ?_⟩
  simpa only [he] using ⟨hw, hG, hMean, hCov, hCF, hMGF⟩


end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogCentered
#print axioms DGRHS.Periodic.periodicLogCentered_memLp
#print axioms DGRHS.Periodic.periodicLogCentered_data
#print axioms DGRHS.Periodic.periodicLogKernel_properties
#print axioms DGRHS.Periodic.periodicLogWeight_uniform
#print axioms DGRHS.Periodic.periodicLogWeight_higher
#print axioms DGRHS.Periodic.periodicLogSingularGibbs
#print axioms DGRHS.Periodic.periodicLogSingularGibbs_eq
#print axioms DGRHS.Periodic.periodicLogSingularGibbs_probability
#print axioms DGRHS.Periodic.exists_periodicLogStatic
#print axioms DGRHS.Periodic.exists_periodicLogSingularStatic
