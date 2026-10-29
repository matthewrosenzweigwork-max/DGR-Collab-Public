import DGRHS.Gaussian.PeriodicLogCanonicalRate
import DGRHS.Concentration.SourceAffineLog
import DGRHS.Concentration.SourceCutoffRate
import DGRHS.CLT.SourceWeightCorrection
import DGRHS.Gaussian.SourceRepulsiveRieszRateSpectrum
import DGRHS.Gaussian.SourceRepulsiveLogRateOneBody

/-!
Packet P9g, unit 2 (part 6): one-body reduction and the torus LOG rate for the partition function
(TeX Lemma 5.6 and the assembly 2093-2159, `thm:partitionFunctionBound`(ii), `s = 0`, on the torus by
Remark 2.1), mirroring `DGRHS.SourceRepulsiveLogRate.exists_source_partition_rate` and the torus
Riesz `periodicRieszPhysical_affine_partition_rate`.  The potential `h_μ` of a bounded-density law is
bounded on the torus, so no `e^{-4βh_μ}` tail hypothesis is needed.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The one-body potential of a bounded-density law is a bounded `L²` function (torus `h_μ ∈ L^∞`). -/
lemma periodicLogPotential_memLp
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) 2
      (periodicCappedDensityMeasure ρ) := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hF := DGRHS.integrable_potential μ W hW
  apply (memLp_const (M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι)).of_le
    hF.aestronglyMeasurable
  filter_upwards [] with x
  have hb := periodicLogKernel_potential_abs_le ρ M hM hρ x
  have hnn : 0 ≤ M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι :=
    mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hnn]
  exact hb

/-- The two doubled-exponential moment inputs of the generic affine one-body comparison
(torus form of `gaussianRieszPhysical_oneBodyComparison_inputs`, LOG kernel). -/
theorem periodicLog_oneBodyComparison_inputs (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (F : PeriodicTorus ι → ℝ)
    (hF : MemLp F 2 (periodicCappedDensityMeasure ρ)) (K I : ℝ)
    (hK : ∀ᵐ x ∂periodicCappedDensityMeasure ρ, F x ≤ K) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicLogCentered μ
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
  have hh : MemLp h 2 (μ.prod μ) := periodicLogCentered_memLp ρ M hρ
  obtain ⟨MC, hMC⟩ := periodicLogKernel_uniform_exponential (2 * β) (by positivity) ρ M hM hρ
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

/-- Torus affine (one-body) partition rate for the LOG gas: the canonical polynomial rate transfers
to the partition with the affine one-body correction, with the extra `N^{-1/2}` error absorbed by
`half_power_le_shifted_power`. -/
theorem periodicLogPhysical_affine_partition_rate (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (F : PeriodicTorus ι → ℝ) (hF : MemLp F 2 (periodicCappedDensityMeasure ρ))
    (K I : ℝ) (hK : ∀ᵐ x ∂periodicCappedDensityMeasure ρ, F x ≤ K) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicLogCentered μ
    let a := β * (∫ y, F y ∂μ) - β * I
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (sourceAffinePartition μ β I h F) atTop
        (𝓝 (Real.exp a * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (sourceAffinePartition μ β I h F N)) atTop
        (𝓝 (a + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        Real.exp a ≤ sourceAffinePartition μ β I h F N ∧
        |sourceAffinePartition μ β I h F N -
          Real.exp a * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) ∧
        |Real.log (sourceAffinePartition μ β I h F N) -
          (a + Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
  intro μ h a
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, c, CR, hc0, hc1, hCR, hRate⟩ :=
    exists_periodic_log_canonical_rate β hβ θ hθ hrem ρ M hM hρ
  set z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ with hz_def
  obtain ⟨hhInputs, MS, MC, hS', hC⟩ :=
    periodicLog_oneBodyComparison_inputs β hβ ρ M hM hρ F hF K I hK
  set L := |β| * Real.sqrt (ProbabilityTheory.variance F μ) *
    (Real.sqrt MS + Real.exp a * Real.sqrt MC) with hL_def
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hComp (N : ℕ) (hN : 1 ≤ N) :=
    sourceAffinePartition_comparison μ β I h hhInputs F hF N hN MS MC
      (hS' N hN).1 (hC N hN).1 (hS' N hN).2 (hC N hN).2
  have hOne (N : ℕ) (hN : 1 ≤ N) : 1 ≤ canonicalPartition μ β h N := by
    have hb := sourceAffinePartition_lower μ β 0 h hh hCan (fun _ => 0) (memLp_const 0) N hN
      (by simpa [DGRHS.CLT.sourceParticleExponent] using (hRate N hN).1)
    simpa [sourceAffinePartition, DGRHS.CLT.sourceParticleExponent, canonicalPartition] using hb
  have hz : 1 ≤ z := ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun N hN => hOne N hN)
  set D := L * (Real.exp 1 + 1) ^ c + Real.exp a * CR with hD_def
  have hD0 : 0 ≤ D := add_nonneg (mul_nonneg hL (by positivity))
    (mul_nonneg (Real.exp_pos a).le hCR)
  set C := (1 + Real.exp (-a)) * D with hC_def
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hMain (N : ℕ) (hN : 1 ≤ N) :
      |sourceAffinePartition μ β I h F N - Real.exp a * z| ≤
        D * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hab := DGRHS.SourceRepulsiveLogRate.half_power_le_shifted_power (N : ℝ) c hn1 hc0.le hc1
    have hcmp : |sourceAffinePartition μ β I h F N - Real.exp a * canonicalPartition μ β h N| ≤
        L * (Real.exp 1 + 1) ^ c * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
      have hb := (hComp N hN).2.2
      change _ ≤ L / Real.sqrt (N : ℝ) at hb
      have he' : L / Real.sqrt (N : ℝ) = L * (1 / Real.sqrt (N : ℝ)) := by ring
      rw [he'] at hb
      exact hb.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hab hL)
    have hcan : |Real.exp a * canonicalPartition μ β h N - Real.exp a * z| ≤
        Real.exp a * CR * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
      rw [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left (hRate N hN).2.1 (Real.exp_pos a).le)
    calc
      _ ≤ |sourceAffinePartition μ β I h F N - Real.exp a * canonicalPartition μ β h N| +
          |Real.exp a * canonicalPartition μ β h N - Real.exp a * z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hcmp hcan
      _ = _ := by dsimp [D]; ring
  have hLow (N : ℕ) (hN : 1 ≤ N) : Real.exp a ≤ sourceAffinePartition μ β I h F N :=
    sourceAffinePartition_lower μ β I h hh hCan F hF N hN (hComp N hN).1
  have hLogRate (N : ℕ) (hN : 1 ≤ N) :
      |Real.log (sourceAffinePartition μ β I h F N) - (a + Real.log z)| ≤
        (Real.exp (-a) * D) * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
    calc
      _ ≤ Real.exp (-a) * |sourceAffinePartition μ β I h F N - Real.exp a * z| :=
        affine_log_difference_le a _ z (hLow N hN) hz
      _ ≤ _ := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (hMain N hN) (Real.exp_pos (-a)).le
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD,
    DGRHS.SourceRepulsiveLogRate.partition_tendsto_of_power_error _ (Real.exp a * z) D c hc0 hMain,
    DGRHS.SourceRepulsiveLogRate.partition_tendsto_of_power_error _ (a + Real.log z)
      (Real.exp (-a) * D) c hc0 hLogRate,
    c, C, hc0, hc1, hC0, ?_⟩
  intro N hN
  have hE : (fun x : Fin N → PeriodicTorus ι => Real.exp
      (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)) =
      (fun x => Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)) := by
    funext x
    congr 1
    exact congrFun (DGRHS.CLT.sourceEnergyExponent_eq (N := N) h F I β (by omega)) x
  have hw : 0 ≤ (Real.exp 1 + (N : ℝ)) ^ (-c) := by
    apply Real.rpow_nonneg
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith [Real.exp_pos (1 : ℝ)]
  refine ⟨by rw [hE]; exact (hComp N hN).1, hLow N hN, ?_, ?_⟩
  · exact (hMain N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; nlinarith [Real.exp_pos (-a)]) hw)
  · exact (hLogRate N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C]; nlinarith [Real.exp_pos (-a)]) hw)

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogPotential_memLp
#print axioms DGRHS.Periodic.periodicLog_oneBodyComparison_inputs
#print axioms DGRHS.Periodic.periodicLogPhysical_affine_partition_rate
