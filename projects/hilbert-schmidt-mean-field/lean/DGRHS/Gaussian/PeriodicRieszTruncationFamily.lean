import DGRHS.Gaussian.PeriodicRieszTruncatedFeature
import DGRHS.Gaussian.PeriodicHeatGaussianField
import DGRHS.Gaussian.OriginalFeatureProposition
import DGRHS.Concentration.SourcePartitionRate
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2
import DGRHS.Gaussian.FeatureKernel
import DGRHS.Kernel.PositiveLimit

/-!
Packet P12c (technical-debt cleanup, no mathematical change): the generic torus truncation family.

A `PeriodicRieszTruncationFamily ι s` bundles a family `τ ↦ coeff τ` of nonnegative, summable,
square-root-summable Fourier coefficients on the torus with the diagonal bound
`Σ_k coeff τ k ≤ C τ^{-s/2}` (`0 < τ ≤ 1`).  Its continuous positive Fourier kernel is
`fam.kernel τ`, its Hoeffding-centered kernel is `fam.centered μ τ`.  The heat-shift family of
Packet P9d (`periodicRieszTruncCoeff`) and the lower-cut family of Packet P9f
(`periodicRieszLCCoeff`) are two instances.

This module proves, once and for all, the family-independent assembly steps of Proposition 5.5 on the
torus that P9d and P9f had duplicated: the centered feature, the canonical data and positivity of
the truncated operators (TeX 487-489), the fixed-scale Laplace estimate (Step 1, `eq:truncatedLaplaceRateEta`)
and the positivity of the full centered periodic Riesz operator as the `L²` limit of the truncated
ones.  The remainder/residual input and the uniform exponential moments enter as hypotheses
(`ResidualBound`), since they are family-specific.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u

/-- A family of positive-definite periodic truncations of the Riesz kernel, given by Fourier
coefficients: nonnegative, summable, square-root summable, with the diagonal bound
`Σ_k coeff τ k ≲ τ^{-s/2}` for `0 < τ ≤ 1`. -/
structure PeriodicRieszTruncationFamily (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) where
  coeff : ℝ → PeriodicFrequency ι → ℝ
  coeff_nonneg : ∀ τ : ℝ, 0 < τ → ∀ k, 0 ≤ coeff τ k
  coeff_summable : ∀ τ : ℝ, 0 < τ → Summable (coeff τ)
  coeff_sqrt_summable : ∀ τ : ℝ, 0 < τ → Summable (fun k => Real.sqrt (coeff τ k))
  coeff_tsum_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ∑' k : PeriodicFrequency ι, coeff τ k ≤ C * τ ^ (-s / 2)

namespace PeriodicRieszTruncationFamily
variable {ι : Type u} [Fintype ι] [Nonempty ι] {s : ℝ} (fam : PeriodicRieszTruncationFamily ι s)

/-- The continuous positive Fourier kernel of the family. -/
abbrev kernel (τ : ℝ) : PeriodicTorus ι → ℝ :=
  periodicPositiveFourierKernel (fam.coeff τ)

/-- Hoeffding-centered truncated periodic kernel of the family. -/
abbrev centered (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (τ : ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => fam.kernel τ (q.1 - q.2))

/-- The centered Fourier feature of the family at scale `τ > 0`. -/
def feature (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 0 < τ) :
    PeriodicTorus ι → PeriodicHeatFeatureSpace ι :=
  periodicCenteredPositiveFourierFeature (fam.coeff τ) (fam.coeff_nonneg τ hτ)
    (fam.coeff_summable τ hτ) μ

lemma centered_eq_featureKernel (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    fam.centered μ τ = featureKernel (fam.feature μ τ hτ) := by
  funext p
  exact (periodicCenteredPositiveFourierFeature_gram _ _ _
    (fam.coeff_sqrt_summable τ hτ) μ p.1 p.2).symm

lemma feature_stronglyMeasurable (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    StronglyMeasurable (fam.feature μ τ hτ) :=
  ((periodicPositiveFourierFeature_continuous _
    (fam.coeff_nonneg τ hτ) (fam.coeff_summable τ hτ)
    (fam.coeff_sqrt_summable τ hτ)).stronglyMeasurable).sub
      stronglyMeasurable_const

lemma feature_norm_le (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) (x : PeriodicTorus ι) :
    ‖fam.feature μ τ hτ x‖ ≤ 2 * Real.sqrt (∑' j, fam.coeff τ j) :=
  periodicCenteredPositiveFourierFeature_norm_le _ _ _ (fam.coeff_sqrt_summable τ hτ) μ x

lemma feature_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) (p : ℝ≥0∞) :
    MemLp (fam.feature μ τ hτ) p μ := by
  apply (memLp_const (2 * Real.sqrt (∑' j, fam.coeff τ j))).of_le
    (fam.feature_stronglyMeasurable μ τ hτ).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
  exact fam.feature_norm_le μ τ hτ x

lemma feature_integral (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    (∫ x, fam.feature μ τ hτ x ∂μ) = 0 := by
  have hi := periodicPositiveFourierFeature_integrable _
    (fam.coeff_nonneg τ hτ) (fam.coeff_summable τ hτ) (fam.coeff_sqrt_summable τ hτ) μ
  show (∫ x, (periodicPositiveFourierFeature _
    (fam.coeff_nonneg τ hτ) (fam.coeff_summable τ hτ) x -
      ∫ y, periodicPositiveFourierFeature _
    (fam.coeff_nonneg τ hτ) (fam.coeff_summable τ hτ) y ∂μ) ∂μ) = 0
  rw [integral_sub hi (integrable_const _)]
  simp

lemma centered_memLp (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    MemLp (fam.centered μ τ) 2 (μ.prod μ) := by
  rw [fam.centered_eq_featureKernel μ τ hτ]
  exact memLp_featureKernel _ (fam.feature_stronglyMeasurable μ τ hτ)
    (fam.feature_memLp μ τ hτ 2)

/-- Torus form of `riesz_cutoff_canonical_data`. -/
lemma centered_data (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ) :
    Measurable (fam.centered μ τ) ∧
      (∀ᵐ p ∂μ.prod μ, fam.centered μ τ p.swap = fam.centered μ τ p) ∧
      (∀ᵐ x ∂μ, (∫ y, fam.centered μ τ (x, y) ∂μ) = 0) := by
  have hk := fam.feature_stronglyMeasurable μ τ hτ
  rw [fam.centered_eq_featureKernel μ τ hτ]
  refine ⟨((hk.comp_measurable measurable_fst).inner
    (hk.comp_measurable measurable_snd)).measurable,
    Filter.Eventually.of_forall (featureKernel_symmetric _), ?_⟩
  exact Filter.Eventually.of_forall (integral_featureKernel_right _
    (fam.feature_memLp μ τ hτ 2) (fam.feature_integral μ τ hτ))

lemma centered_positive (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (τ : ℝ) (hτ : 0 < τ)
    (hq : MemLp (fam.centered μ τ) 2 (μ.prod μ)) :
    ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator (fam.centered μ τ) hq v) := by
  intro v
  have he := fam.centered_eq_featureKernel μ τ hτ
  have hp := integralOperator_featureKernel_nonneg _
    (fam.feature_stronglyMeasurable μ τ hτ) (fam.feature_memLp μ τ hτ 2) v
  have hc : DGRHS.Kernel.integralOperator (fam.centered μ τ) hq =
      DGRHS.Kernel.integralOperator (featureKernel (fam.feature μ τ hτ))
        (memLp_featureKernel _ (fam.feature_stronglyMeasurable μ τ hτ)
          (fam.feature_memLp μ τ hτ 2)) :=
    gaussian_integralOperator_congr μ _ _ _ _ (Filter.Eventually.of_forall (fun p => by rw [he]))
  rw [hc, real_inner_comm]
  exact hp

/-- Feature-space Laplace estimate at a fixed scale `τ > 0` (TeX Step 1 of Proposition 5.5,
`eq:truncatedLaplaceRateEta`), a direct instance of the generic Proposition 5.4
`original_boundedFeatureQuadLaplace_of_memLp_top`. -/
theorem laplace_diag (β τ : ℝ) (hβ : 0 ≤ β) (hτ : 0 < τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    ∃ (hh : MemLp (fam.centered μ τ) 2 (μ.prod μ))
      (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
      Countable σ ∧
      (∀ i, DGRHS.Kernel.integralOperator (fam.centered μ τ) hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (fam.centered μ τ) x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β (fam.centered μ τ) N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, fam.coeff τ k)) / (N : ℝ) := by
  borelize ↥(PeriodicHeatFeatureSpace ι)
  have ha := fam.coeff_nonneg τ hτ
  let a := fam.coeff τ
  let k := fam.feature μ τ hτ
  have hk : StronglyMeasurable k := fam.feature_stronglyMeasurable μ τ hτ
  have hμ : μ ≠ 0 := by
    intro hzero
    have hm : μ Set.univ = 1 := measure_univ
    simp [hzero] at hm
  have hkbound (x : PeriodicTorus ι) : ‖k x‖ ≤ 2 * Real.sqrt (∑' j, a j) :=
    fam.feature_norm_le μ τ hτ x
  have hkinf : MemLp k ∞ μ := fam.feature_memLp μ τ hτ ∞
  have hmean : (∫ x, k x ∂μ) = 0 := fam.feature_integral μ τ hτ
  have heq : fam.centered μ τ =ᵐ[μ.prod μ] featureKernel k := by
    filter_upwards with p
    exact congrFun (fam.centered_eq_featureKernel μ τ hτ) p
  obtain ⟨hh, σ, eig, e, hi, he, hnn, hsm, htr, hP, hD, hC, hRate⟩ :=
    original_boundedFeatureQuadLaplace_of_memLp_top β hβ (fam.centered μ τ) k hk hkinf hmean heq
  have hnorm : (lpNorm k ∞ μ) ^ 2 ≤ 4 * ∑' j, a j := by
    have hsumnn : 0 ≤ ∑' j, a j := tsum_nonneg ha
    have hbound := lpNorm_mono_real
      (memLp_const (2 * Real.sqrt (∑' j, a j)) :
        MemLp (fun _ : PeriodicTorus ι => 2 * Real.sqrt (∑' j, a j)) ∞ μ)
      (fun x => hkbound x)
    rw [lpNorm_const (p := ∞) (by simp) hμ (2 * Real.sqrt (∑' j, a j))] at hbound
    have hn : lpNorm k ∞ μ ≤ 2 * Real.sqrt (∑' j, a j) := by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (∑' j, a j))] using hbound
    have hh2 := pow_le_pow_left₀ lpNorm_nonneg hn 2
    simpa only [mul_pow, Real.sq_sqrt hsumnn, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh2
  refine ⟨hh, σ, eig, e, hi, he, hnn, hsm, hP, hD, ?_⟩
  intro N hN
  have hC0 := featureBoundedRateConstant_pos β hβ
  refine ⟨?_, ?_⟩
  · have := (hRate N hN).1
    simpa only [sourceKernelParticleStatistic_eq_normalized] using this
  · have hb := (hRate N hN).2
    simp_rw [sourceKernelParticleStatistic_eq_normalized] at hb
    change |canonicalPartition μ β (fam.centered μ τ) N - _| ≤ _
    refine hb.trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply mul_le_mul_of_nonneg_left _ hC0.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC0.le hβ)

/-- Laplace constant of the family: `L exp(L τ^{-s/2}) / N`. -/
theorem laplace (β : ℝ) (hβ : 0 ≤ β) :
    ∃ L : ℝ, 0 < L ∧ ∀ (τ : ℝ), 0 < τ → τ ≤ 1 →
      ∀ (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ],
      ∃ (hh : MemLp (fam.centered μ τ) 2 (μ.prod μ))
        (σ : Type u) (eig : σ → ℝ) (e : HilbertBasis σ ℝ (Lp ℝ 2 μ)),
        Countable σ ∧
        (∀ i, DGRHS.Kernel.integralOperator (fam.centered μ τ) hh (e i) = eig i • e i) ∧
        0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
        Tendsto (canonicalPartition μ β (fam.centered μ τ)) atTop
          (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
        ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β / 2 *
            DGRHS.CanonicalVariance.normalizedOffDiagonalSum (fam.centered μ τ) x))
            (Measure.pi (fun _ : Fin N => μ)) ∧
          |canonicalPartition μ β (fam.centered μ τ) N -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
            L * Real.exp (L * τ ^ (-s / 2)) / (N : ℝ) := by
  obtain ⟨CD, hCD0, hCD⟩ := fam.coeff_tsum_le
  have hC0 := featureBoundedRateConstant_pos β hβ
  refine ⟨featureBoundedRateConstant β + 4 * featureBoundedRateConstant β * β * CD, by positivity, ?_⟩
  intro τ hτ hτ1 μ _
  obtain ⟨hh, σ, eig, e, hi, he, hnn, hsm, hP, hD, hR⟩ :=
    fam.laplace_diag β τ hβ hτ μ
  refine ⟨hh, σ, eig, e, hi, he, hD, ?_, fun N hN => ⟨(hR N hN).1, ?_⟩⟩
  · apply partition_tendsto_of_reciprocal_error _ _
      (featureBoundedRateConstant β * Real.exp (featureBoundedRateConstant β * β *
            (4 * ∑' k, fam.coeff τ k)))
    intro N hN
    exact (hR N hN).2
  · refine (hR N hN).2.trans ?_
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    have hdiag := hCD τ hτ hτ1
    have hτp : 0 ≤ τ ^ (-s / 2) := Real.rpow_nonneg hτ.le _
    have hLge : featureBoundedRateConstant β ≤
        featureBoundedRateConstant β + 4 * featureBoundedRateConstant β * β * CD := by
      have : 0 ≤ 4 * featureBoundedRateConstant β * β * CD := by positivity
      linarith
    apply mul_le_mul hLge _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    calc featureBoundedRateConstant β * β * (4 * ∑' k, fam.coeff τ k)
        ≤ featureBoundedRateConstant β * β * (4 * (CD * τ ^ (-s / 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC0.le hβ)
      _ = (4 * featureBoundedRateConstant β * β * CD) * τ ^ (-s / 2) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hτp
        have : 0 ≤ featureBoundedRateConstant β := hC0.le
        linarith

/-- The centered `L²(μ⊗μ)` residual bound `‖h̃ - h̃_τ‖ ≲ τ^{θ/2}` of the family against the exact
centered periodic Riesz kernel (family-specific input of the operator positivity and of the rate). -/
abbrev ResidualBound (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ∀ (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
      (hq : MemLp (fam.centered (periodicCappedDensityMeasure ρ) τ) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))),
    ‖(hh.sub hq).toLp (fun p => hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
          fam.centered (periodicCappedDensityMeasure ρ) τ p)‖ ≤ A * τ ^ (θ / 2)

/-- Positivity of the full centered periodic Riesz operator as the `L²`-limit of the truncated ones
(TeX 487-489), from the residual bound of the family. -/
theorem operator_positive (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hres : fam.ResidualBound hs2 θ ρ)
    (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    ∀ v : Lp ℝ 2 (periodicCappedDensityMeasure ρ), 0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))) hh v) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  obtain ⟨A, hA0, hA⟩ := hres
  let τ : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1)
  have hτ : ∀ N, 0 < τ N := fun N => by dsimp [τ]; positivity
  have hτ1 : ∀ N, τ N ≤ 1 := fun N => by
    dsimp [τ]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hq : ∀ N, MemLp (fam.centered μ (τ N)) 2 (μ.prod μ) := fun N =>
    fam.centered_memLp μ (τ N) (hτ N)
  apply DGRHS.Kernel.integralOperator_nonnegative_of_toLp_limit _ hh
    (fun N => fam.centered μ (τ N)) hq
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hne : θ / 2 ≠ 0 := by positivity
    have hle : 0 ≤ θ / 2 := by positivity
    have hpow : Tendsto (fun N => (τ N) ^ (θ / 2)) atTop (𝓝 0) := by
      simpa only [τ, Function.comp_def, Real.zero_rpow hne] using
        ((Real.continuousAt_rpow_const 0 (θ / 2) (Or.inr hle)).tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    apply squeeze_zero (fun N => norm_nonneg _) _ (by simpa using hpow.const_mul A)
    intro N
    have hb := hA (τ N) (hτ N) (hτ1 N) hh (hq N)
    calc _ = ‖hh.toLp _ - (hq N).toLp (fam.centered μ (τ N))‖ := norm_sub_rev _ _
      _ = ‖(hh.sub (hq N)).toLp (fun p => hoeffdingCentered μ
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)) p -
        fam.centered μ (τ N) p)‖ := by
          exact congrArg norm (MemLp.toLp_sub hh (hq N)).symm
      _ ≤ _ := hb
  · intro N v
    exact fam.centered_positive μ (τ N) (hτ N) (hq N) v

end PeriodicRieszTruncationFamily

end DGRHS.Periodic
