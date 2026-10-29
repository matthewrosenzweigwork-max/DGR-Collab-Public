import DGRHS.Gaussian.PeriodicRieszTruncationFamily
import DGRHS.Concentration.SourceRateAssembly
import DGRHS.Concentration.SourceAffineLog
import DGRHS.Concentration.SourceCutoffRate
import DGRHS.CLT.SourceWeightCorrection
import DGRHS.Gaussian.SourceRepulsiveRieszRateSpectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Packet P12c (technical-debt cleanup, no mathematical change): the generic torus Riesz rate assembly
for a `PeriodicRieszTruncationFamily` (TeX Steps 1-4 of Proposition 5.5, 1941-2087, Lemma 5.6 and the
assembly 2093-2159, `thm:partitionFunctionBound`(ii), on the torus by Remark 2.1), proved once.

The canonical (centered, mean-zero) partition rate `canonical_rate`, the affine one-body rate
`affine_partition_rate`, and the rate for the literal singular partition `singular_rate`, from the
family-specific inputs `ResidualBound` (the centered `L²` residual `‖h̃ - h̃_τ‖ ≲ τ^{θ/2}`) and
`UniformExponential` (uniform exponential moments of the centered truncations for `0 < τ ≤ a`,
`0 < a ≤ 1`).  The family-independent facts about the exact centered periodic Riesz kernel
(`periodicRieszCentered`, its `L²` membership and canonical data, the one-body potential and the
doubled-moment inputs) live here too, since the assembly needs them.  Both the heat-shift family of
Packet P9d and the lower-cut family of Packet P9f are re-derived from it as thin wrappers.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Centered exact periodic Riesz kernel (the periodic `h̃`). -/
abbrev periodicRieszCentered (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))

lemma periodicRieszCentered_memLp (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ)) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  periodicCenteredPair_memLp_of_density_cap ρ M hρ _ (periodicRieszKernel_stronglyMeasurable s hs2)
    (periodicRieszKernel_memLp s hs2)

lemma periodicRieszCentered_data (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Measurable (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ)) ∧
    (∀ᵐ p ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ),
      periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ) p.swap =
        periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ) p) ∧
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ) (x, y)
        ∂periodicCappedDensityMeasure ρ) = 0) := by
  refine ⟨(stronglyMeasurable_hoeffdingCentered _ _
    ((periodicRieszKernel_stronglyMeasurable s hs2).comp_measurable
      (measurable_fst.sub measurable_snd))).measurable, ?_, ?_⟩
  · apply Filter.Eventually.of_forall
    intro p
    exact DGRHS.centeredKernel_symmetric (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszKernel s hs2 (a - b))
      (fun a b => by rw [← periodicRieszKernel_even s hs2 (b - a), neg_sub]) p.2 p.1
  · exact DGRHS.integral_centeredKernel_right (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszKernel s hs2 (a - b))
      (periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2))

lemma periodic_partition_tendsto_of_log_error (Z : ℕ → ℝ) (z C q : ℝ) (hq : 0 < q)
    (h : ∀ N, 1 ≤ N → |Z N - z| ≤ C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q)) :
    Tendsto Z atTop (𝓝 z) := by
  have hbase : Tendsto (fun N : ℕ => Real.exp 1 + (N : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_left (Real.exp_pos _).le) tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_neg_atTop hq).comp (Real.tendsto_log_atTop.comp hbase)
  have hc := tendsto_const_nhds.mul ht (a := C)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg (Z N - z))
    ((eventually_ge_atTop 1).mono fun N hN => ?_) (by simpa using hc)
  simpa only [Real.norm_eq_abs] using h N hN

/-- The one-body potential of a bounded-density law is a bounded `L²` function (torus `h_μ ∈ L^∞`). -/
lemma periodicRieszPotential_memLp (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) 2
      (periodicCappedDensityMeasure ρ) := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hF := DGRHS.integrable_potential μ W hW
  apply (memLp_const (M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι)).of_le
    hF.aestronglyMeasurable
  filter_upwards [] with x
  have hb := periodicRieszKernel_potential_abs_le s hs2 ρ M hM hρ x
  have hnn : 0 ≤ M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
    mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hnn]
  exact hb

/-- The two doubled-exponential moment inputs of the generic affine one-body comparison
(torus form of `gaussianRieszPhysical_oneBodyComparison_inputs`). -/
theorem periodicRiesz_oneBodyComparison_inputs (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (F : PeriodicTorus ι → ℝ)
    (hF : MemLp F 2 (periodicCappedDensityMeasure ρ)) (K I : ℝ)
    (hK : ∀ᵐ x ∂periodicCappedDensityMeasure ρ, F x ≤ K) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    ∃ (_hh : MemLp h 2 (μ.prod μ)) (MS MC : ℝ),
      (∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (2 * DGRHS.CLT.sourceParticleExponent h F I β N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        (∫ x : Fin N → PeriodicTorus ι, Real.exp
          (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ MS) ∧
      (∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        (∫ x : Fin N → PeriodicTorus ι, Real.exp
          (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC) := by
  intro μ h
  have hh : MemLp h 2 (μ.prod μ) := periodicRieszCentered_memLp s hs2 ρ M hρ
  obtain ⟨MC, hMC⟩ := periodicRieszKernel_uniform_exponential s (2 * β) hs (by positivity) hs2 ρ M hM hρ
  have hC (N : ℕ) (hN : 1 ≤ N) :
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
        (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp
        (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC := by
    have he : (fun x : Fin N → PeriodicTorus ι => Real.exp ((2 * β) * iidNegativeStatistic N h x)) =
        (fun x => Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
      funext x
      rw [DGRHS.CLT.iidCanonicalExponent_eq]
      congr 1; ring
    have hbound := hMC N hN
    change Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
      ((2 * β) * iidNegativeStatistic N h x)) (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp ((2 * β) * iidNegativeStatistic N h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MC at hbound
    rw [he] at hbound
    exact hbound
  let MS := max (Real.exp ((2 * β) * (K - I)) * MC) (Real.exp (-(2 * β) * I))
  have hS := DGRHS.CLT.sourceWeight_of_canonical_moments h F
    (hF.integrable (by norm_num)) K hK I (2 * β) (by positivity) MC
    (fun N hN => by
      convert (hC N hN).1 using 1
      funext x
      congr 1
      ring)
    (fun N hN => by
      convert (hC N hN).2 using 1
      congr 1
      funext x
      congr 1
      ring)
  have hS' (N : ℕ) :
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
        (2 * DGRHS.CLT.sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp
        (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ MS := by
    simpa only [DGRHS.CLT.sourceParticleExponent_mul_parameter] using hS N
  exact ⟨hh, MS, MC, fun N hN => hS' N, hC⟩

namespace PeriodicRieszTruncationFamily
variable {s : ℝ} (fam : PeriodicRieszTruncationFamily ι s)

/-- Uniform exponential moments of the centered truncations of the family, for `0 < τ ≤ a` with some
`0 < a ≤ 1` (continuous representative). -/
abbrev UniformExponential (β : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] : Prop :=
  ∃ (C a : ℝ), 0 < a ∧ a ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ a → ∀ n : ℕ, 1 ≤ n →
    Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
      (fam.centered (periodicCappedDensityMeasure ρ) τ) ω))
      (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
    (∫ ω, Real.exp (β * iidNegativeStatistic n
      (fam.centered (periodicCappedDensityMeasure ρ) τ) ω)
      ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C

/-- The canonical periodic Riesz partition `K_N^{can}` converges to `det₂^{-1/2}` with the rate
`(log(e+N))^{-θ/s}`, where `θ` is the exponent of the scale-`η=√τ` remainder
`‖h̃ - h̃_τ‖ ≲ η^θ` of the family (`τ = η²`). -/
theorem canonical_rate (β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hres : fam.ResidualBound hs2 θ ρ) (hunif : fam.UniformExponential (2 * β) ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (canonicalPartition μ β h) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β h N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (canonicalPartition μ β h N) -
          Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  intro μ h
  have hh : MemLp h 2 (μ.prod μ) := periodicRieszCentered_memLp s hs2 ρ M hρ
  obtain ⟨hhm, hSym, hCan⟩ := periodicRieszCentered_data s hs2 ρ M hρ
  have hPos := fam.operator_positive hs2 θ hθ ρ hres hh
  -- moments of the exact centered kernel
  obtain ⟨MF, hF⟩ := periodicRieszKernel_uniform_exponential s (2 * β) hs0 (by positivity) hs2 ρ M hM hρ
  have hEF (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp ((2 * β) * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
    congr 1; ring
  have hMF : 1 ≤ MF := by
    have hb := (hF 1 le_rfl).2
    simpa [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum] using hb
  have hDouble : ∀ N, Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
      (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N => μ)) := by
    intro N
    by_cases hN : N = 0
    · subst N
      simp [DGRHS.CanonicalVariance.normalizedOffDiagonalSum]
    · have hb := (hF N (by omega)).1
      rw [hEF N] at hb
      exact hb
  have bDouble : ∀ N, (∫ x : Fin N → PeriodicTorus ι, Real.exp
      (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ MF := by
    intro N
    by_cases hN : N = 0
    · subst N
      simpa [DGRHS.CanonicalVariance.normalizedOffDiagonalSum] using hMF
    · have hb := (hF N (by omega)).2
      rw [hEF N] at hb
      exact hb
  -- moments of the truncations
  obtain ⟨MK, a, ha, ha1, hK⟩ := hunif
  have hEK (τ : ℝ) (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp ((2 * β) *
      iidNegativeStatistic N (fam.centered μ τ) x)) =
      (fun x => Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fam.centered μ τ) x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
    congr 1; ring
  have kDouble : ∀ τ : ℝ, 0 < τ → τ ≤ a → ∀ N : ℕ, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fam.centered μ τ) x)) (Measure.pi (fun _ : Fin N => μ)) := by
    intro τ hτ hτa N hN
    have hb := (hK τ hτ hτa N hN).1
    rw [hEK τ N] at hb
    exact hb
  have bkDouble : ∀ τ : ℝ, 0 < τ → τ ≤ a → ∀ N : ℕ, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (fam.centered μ τ) x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ MK := by
    intro τ hτ hτa N hN
    have hb := (hK τ hτ hτa N hN).2
    rw [hEK τ N] at hb
    exact hb
  obtain ⟨A, hA0, hRes⟩ := hres
  obtain ⟨κ, eig, e, hκ, he, hD, _, hT, hLog, hAll⟩ :=
    exists_canonicalMeanZero_log_partition_limit μ β hβ h hh hSym hCan hPos MF hDouble bDouble
  set z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ with hz
  obtain ⟨L, hL, hLap⟩ := fam.laplace β hβ
  have hr : 0 < θ := hθ
  set B := (|β| / 2 * Real.sqrt 2) * (Real.sqrt MF + Real.sqrt MK) * A with hBdef
  have hB : 0 ≤ B := by
    dsimp [B]; positivity
  set D := 2 * B * (2 * L) ^ (θ / s) * (1 + Real.log (Real.exp 1 + 1) / Real.log 2) ^ (θ / s) +
    L * (Real.log (Real.exp 1 + 1) + 2 * (θ / s)) ^ (θ / s) with hDdef
  obtain ⟨N₀, hN₀⟩ := sourceRieszRateCutoff_eventually_small L s (Real.sqrt a) hL hs0 (Real.sqrt_pos.mpr ha)
  set f := fun N : ℕ => (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) with hf_def
  have hf : ∀ N, 0 < f N := by
    intro N
    apply Real.rpow_pos_of_pos
    apply Real.log_pos
    have he1 : 1 < Real.exp (1 : ℝ) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hLarge : ∀ N, 1 ≤ N → N₀ ≤ N → |canonicalPartition μ β h N - z| ≤ D * f N := by
    intro N hN hNN
    obtain ⟨hN2, hη, hηsmall⟩ := hN₀ N hNN
    set η := sourceRieszRateCutoff L s (N : ℝ) with hηdef
    have hτ : 0 < η ^ 2 := by positivity
    have hτa : η ^ 2 ≤ a := by
      have h2 := pow_le_pow_left₀ hη.le hηsmall 2
      rwa [Real.sq_sqrt ha.le] at h2
    have hτ1 : η ^ 2 ≤ 1 := hτa.trans ha1
    obtain ⟨hq, σ, c, b, hσ, hb, hDc, hY, hRate⟩ := hLap (η ^ 2) hτ hτ1 μ
    obtain ⟨hqm, hqs, hqc⟩ := fam.centered_data μ (η ^ 2) hτ
    have hητ : (η ^ 2) ^ (θ / 2) = η ^ θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      congr 1; push_cast; ring
    have hresid := hRes (η ^ 2) hτ hτ1 hh hq
    rw [hητ] at hresid
    have hComp := canonicalPartition_comparison μ β h (fam.centered μ (η ^ 2)) hhm hqm hh hq
      hSym hqs hCan hqc (A * η ^ θ) MF MK hresid
      (fun n _ => hDouble n) (fun n hn => kDouble (η ^ 2) hτ hτa n hn)
      (fun n _ => bDouble n) (fun n hn => bkDouble (η ^ 2) hτ hτa n hn)
    have hComp' : ∀ n, 1 ≤ n → |canonicalPartition μ β h n -
        canonicalPartition μ β (fam.centered μ (η ^ 2)) n| ≤ B * η ^ θ := by
      intro n hn
      convert hComp n hn using 1
      dsimp [B]
      ring
    have hError := partition_error_assembly (canonicalPartition μ β h)
      (canonicalPartition μ β (fam.centered μ (η ^ 2)))
      z ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * c i)))⁻¹) (B * η ^ θ) hT hY hComp' N hN
    have hOpt := sourceRieszRateCutoff_bound B L s θ (N : ℝ) hB hL hs0 hr (by exact_mod_cast hN2)
    have hηs : (η ^ 2) ^ (-s / 2) = η ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      congr 1; push_cast; ring
    have hR := (hRate N hN).2
    rw [hηs] at hR
    apply (hError.trans (add_le_add le_rfl hR)).trans
    convert hOpt using 1
    dsimp [η, D, f]
    ring
  obtain ⟨hC, hRateAll⟩ := partition_rate_all_positive (canonicalPartition μ β h) z f hf D N₀ hLarge
  set C := max D 0 + ∑ j ∈ Finset.range N₀, |canonicalPartition μ β h j - z| / f j with hCdef
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, C, hC, ?_⟩
  intro N hN
  exact ⟨(hAll N).1, hRateAll N hN, ((hAll N).2.2).trans (hRateAll N hN)⟩

/-- Torus affine (one-body) partition rate for the family: the canonical rate transfers to the
partition with the affine one-body correction, with the extra `N^{-1/2}` error absorbed by
`half_power_le_log_rate`. -/
theorem affine_partition_rate (β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hres : fam.ResidualBound hs2 θ ρ) (hunif : fam.UniformExponential (2 * β) ρ)
    (F : PeriodicTorus ι → ℝ) (hF : MemLp F 2 (periodicCappedDensityMeasure ρ))
    (K I : ℝ) (hK : ∀ᵐ x ∂periodicCappedDensityMeasure ρ, F x ≤ K) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    let c := β * (∫ y, F y ∂μ) - β * I
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (sourceAffinePartition μ β I h F) atTop
        (𝓝 (Real.exp c * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (sourceAffinePartition μ β I h F N)) atTop
        (𝓝 (c + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        Real.exp c ≤ sourceAffinePartition μ β I h F N ∧
        |sourceAffinePartition μ β I h F N -
          Real.exp c * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (sourceAffinePartition μ β I h F N) -
          (c + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  intro μ h c
  set q := θ / s with hqdef
  have hq : 0 < q := div_pos hθ hs0
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, CR, hCR, hRate⟩ :=
    fam.canonical_rate β hs0 hβ hs2 θ hθ ρ M hM hρ hres hunif
  set z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ with hz_def
  obtain ⟨hhInputs, MS, MC, hS', hC⟩ :=
    periodicRiesz_oneBodyComparison_inputs s β hs0 hβ hs2 ρ M hM hρ F hF K I hK
  set L := |β| * Real.sqrt (ProbabilityTheory.variance F μ) *
    (Real.sqrt MS + Real.exp c * Real.sqrt MC) with hL_def
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hComp (N : ℕ) (hN : 1 ≤ N) :=
    sourceAffinePartition_comparison μ β I h hhInputs F hF N hN MS MC
      (hS' N hN).1 (hC N hN).1 (hS' N hN).2 (hC N hN).2
  have hOne (N : ℕ) (hN : 1 ≤ N) : 1 ≤ canonicalPartition μ β h N := by
    have hb := sourceAffinePartition_lower μ β 0 h hh hCan (fun _ => 0) (memLp_const 0) N hN
      (by simpa [DGRHS.CLT.sourceParticleExponent] using (hRate N hN).1)
    simpa [sourceAffinePartition, DGRHS.CLT.sourceParticleExponent, canonicalPartition] using hb
  have hz : 1 ≤ z := ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun N hN => hOne N hN)
  set H := (Real.log (Real.exp 1 + 1) + 2 * q) ^ q with hH_def
  set D := L * H + Real.exp c * CR with hD_def
  have hH : 0 ≤ H := by
    apply Real.rpow_nonneg
    have hb : 0 < Real.log (Real.exp 1 + 1) := Real.log_pos (by linarith [Real.exp_pos (1 : ℝ)])
    linarith
  have hD0 : 0 ≤ D := add_nonneg (mul_nonneg hL hH) (mul_nonneg (Real.exp_pos c).le hCR)
  set C := (1 + Real.exp (-c)) * D with hC_def
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hMain (N : ℕ) (hN : 1 ≤ N) :
      |sourceAffinePartition μ β I h F N - Real.exp c * z| ≤
        D * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q) := by
    have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hab := half_power_le_log_rate (N : ℝ) q hn1 hq
    have he' : L / Real.sqrt (N : ℝ) = L * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hn.le]
      ring
    have hcmp : |sourceAffinePartition μ β I h F N - Real.exp c * canonicalPartition μ β h N| ≤
        L * H * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q) := by
      have hb := (hComp N hN).2.2
      change _ ≤ L / Real.sqrt (N : ℝ) at hb
      rw [he'] at hb
      exact hb.trans (by simpa only [H, mul_assoc] using mul_le_mul_of_nonneg_left hab hL)
    have hcan : |Real.exp c * canonicalPartition μ β h N - Real.exp c * z| ≤
        Real.exp c * CR * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q) := by
      rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left (hRate N hN).2.1 (Real.exp_pos c).le)
    calc
      _ ≤ |sourceAffinePartition μ β I h F N - Real.exp c * canonicalPartition μ β h N| +
          |Real.exp c * canonicalPartition μ β h N - Real.exp c * z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hcmp hcan
      _ = _ := by dsimp [D]; ring
  have hLow (N : ℕ) (hN : 1 ≤ N) : Real.exp c ≤ sourceAffinePartition μ β I h F N :=
    sourceAffinePartition_lower μ β I h hh hCan F hF N hN (hComp N hN).1
  have hLogRate (N : ℕ) (hN : 1 ≤ N) :
      |Real.log (sourceAffinePartition μ β I h F N) - (c + Real.log z)| ≤
        (Real.exp (-c) * D) * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q) := by
    calc
      _ ≤ Real.exp (-c) * |sourceAffinePartition μ β I h F N - Real.exp c * z| :=
        affine_log_difference_le c _ z (hLow N hN) hz
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hMain N hN) (Real.exp_pos (-c)).le
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD,
    periodic_partition_tendsto_of_log_error _ (Real.exp c * z) D q hq hMain,
    periodic_partition_tendsto_of_log_error _ (c + Real.log z) (Real.exp (-c) * D) q hq hLogRate,
    C, hC0, ?_⟩
  intro N hN
  have hE : (fun x : Fin N → PeriodicTorus ι => Real.exp
      (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)) =
      (fun x => Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)) := by
    funext x
    congr 1
    exact congrFun (DGRHS.CLT.sourceEnergyExponent_eq (N := N) h F I β (by omega)) x
  have hw : 0 ≤ (Real.log (Real.exp 1 + (N : ℝ))) ^ (-q) := by
    apply Real.rpow_nonneg
    apply Real.log_nonneg
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [Real.exp_pos (1 : ℝ)]
  refine ⟨by rw [hE]; exact (hComp N hN).1, hLow N hN, ?_, ?_⟩
  · exact (hMain N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; nlinarith [Real.exp_pos (-c)]) hw)
  · exact (hLogRate N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; nlinarith [Real.exp_pos (-c)]) hw)

/-- Torus Theorem 2.2(ii) (Riesz branch) for the literal singular partition, with exponent `θ/s`
for the family whose centered residual is `≲ η^θ` at scale `η = √τ`. -/
theorem singular_rate (β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (θ : ℝ) (hθ : 0 < θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hres : fam.ResidualBound hs2 θ ρ) (hunif : fam.UniformExponential (2 * β) ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Tendsto (fun N => (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal) atTop
        (𝓝 (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < periodicRieszSingularPartition s β hs2 ρ N ∧
          periodicRieszSingularPartition s β hs2 ρ N < ⊤) ∧
        Real.exp (β * I) ≤ (periodicRieszSingularPartition s β hs2 ρ N).toReal ∧
        |(periodicRieszSingularPartition s β hs2 ρ N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) ∧
        |Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal -
          (β * I + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.log (Real.exp 1 + (N : ℝ))) ^ (-(θ / s)) := by
  intro μ W h I
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hFm := periodicRieszPotential_memLp s hs2 ρ M hM hρ
  have hK : ∀ᵐ x ∂μ, DGRHS.potential μ W x ≤ M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicRieszKernel_potential_abs_le s hs2 ρ M hM hρ x)
  have hc : β * (∫ y, DGRHS.potential μ W y ∂μ) - β * I = β * I := by
    rw [DGRHS.integral_potential μ W hW]
    ring
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, C, hC, hRate⟩ :=
    fam.affine_partition_rate β hs0 hβ hs2 θ hθ ρ M hM hρ hres hunif
      (DGRHS.potential μ W) hFm _ I hK
  rw [hc] at hT hLog hRate
  have hpos := fam.operator_positive hs2 θ hθ ρ hres hh
  have hP := DGRHS.SourceRepulsiveRieszRate.hasProd_actual_meanZero_spectrum _ hh hSym hCan hpos
    eig e he β hβ
  have hEq (N : ℕ) (hN : 1 ≤ N) : periodicRieszSourcePartition s β hs2 ρ N =
      sourceAffinePartition μ β I h (DGRHS.potential μ W) N :=
    sourceEnergy_partition_eq_affine μ β I h (DGRHS.potential μ W) N hN
  have hEv : periodicRieszSourcePartition s β hs2 ρ =ᶠ[atTop]
      sourceAffinePartition μ β I h (DGRHS.potential μ W) :=
    (eventually_ge_atTop 1).mono fun N hN => hEq N hN
  have hToReal (N : ℕ) : (periodicRieszSingularPartition s β hs2 ρ N).toReal =
      periodicRieszSourcePartition s β hs2 ρ N := by
    rw [periodicRieszSingularPartition_eq_integral s β hs0 hβ hs2 ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold periodicRieszSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  have hEv' : (fun N => (periodicRieszSingularPartition s β hs2 ρ N).toReal) =ᶠ[atTop]
      sourceAffinePartition μ β I h (DGRHS.potential μ W) :=
    hEv.mono (fun N hN => by show (periodicRieszSingularPartition s β hs2 ρ N).toReal = _; rw [hToReal N]; exact hN)
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hP, hT.congr' hEv'.symm,
    hLog.congr' (hEv'.symm.mono fun N hN => congrArg Real.log hN), C, hC, ?_⟩
  intro N hN
  refine ⟨periodicRieszSingularPartition_pos_finite s β hs0 hβ hs2 ρ M hM hρ N, ?_⟩
  rw [hToReal N, hEq N hN]
  exact (hRate N hN).2

end PeriodicRieszTruncationFamily

end DGRHS.Periodic
