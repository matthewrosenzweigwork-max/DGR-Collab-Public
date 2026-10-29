import DGRHS.CLT.SourceLogSingularRate
import DGRHS.Concentration.SourceAffineLog

/-! Original logarithmic singular partition: derived positive lower bound and
logarithmic quantitative error. The hypotheses are the positive-beta original
physical hypotheses and its stated quantitative potential tail. No partition
lower bound, logarithmic rate or determinant bound is supplied as a premise.
This prepares the canonical correction; it does not identify macroscopic
differential entropy or enlarge the thermal equilibrium domain. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

lemma sourceLogSingularPartition_lower (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-4 * (β : ℝ) *
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ))
    (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a, b)
    Real.exp ((β : ℝ) * DGRHS.interactionEnergy μ W) ≤ (sourceLogSingularPartition β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a, b)
  let h := hoeffdingCentered μ logPhysicalPair
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hh : MemLp h 2 (μ.prod μ) := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  have hc : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0 :=
    DGRHS.integral_centeredKernel_right μ W hpair
  have hF : MemLp F 2 μ := DGRHS.SourceRepulsiveLogRate.physicalPotential_memLp_two
    (β : ℝ) hβ hd ρ M hM hρ hpair htail
  have hi : Integrable (fun x : Fin N → EuclideanSpace ℝ ι =>
      Real.exp (sourceParticleExponent h F I (β : ℝ) N x)) (Measure.pi (fun _ : Fin N => μ)) := by
    have he : (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp (-(β : ℝ) * (N : ℝ) *
        sourceCanonicalModulatedEnergy h F I N x)) =
        (fun x => Real.exp (sourceParticleExponent h F I (β : ℝ) N x)) := by
      funext x
      congr 1
      exact sourceCanonicalModulatedEnergy_exponent h F I (β : ℝ) (by omega) x
    rw [← he]
    exact sourceLogEnergyWeight_integrable (β : ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  have hl := sourceAffinePartition_lower μ (β : ℝ) I h hh hc F hF N hN hi
  rw [DGRHS.SourceRepulsiveLogRate.physical_affine_prefactor (β : ℝ) ρ hpair] at hl
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le),
    sourceEnergy_partition_eq_affine μ (β : ℝ) I h F N hN]
  exact hl

theorem sourceLogSingularPartition_original_log_rate (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-4 * (β : ℝ) *
      logPhysicalPotential (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a, b)
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p) (hc : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i) ∧
      HasProd (fun i => (1 + (β : ℝ) * eig i) * Real.exp (-((β : ℝ) * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)) ∧
      Tendsto (fun N => Real.log (sourceLogSingularPartition β ρ N).toReal) atTop
        (𝓝 ((β : ℝ) * DGRHS.interactionEnergy μ W +
          Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))⁻¹))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < sourceLogSingularPartition β ρ N ∧ sourceLogSingularPartition β ρ N < ∞) ∧
        Real.exp ((β : ℝ) * DGRHS.interactionEnergy μ W) ≤ (sourceLogSingularPartition β ρ N).toReal ∧
        |(sourceLogSingularPartition β ρ N).toReal -
          Real.exp ((β : ℝ) * DGRHS.interactionEnergy μ W) *
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))⁻¹| ≤
          C * (Real.exp 1 + (N : ℝ))^(-c) ∧
        |Real.log (sourceLogSingularPartition β ρ N).toReal -
          ((β : ℝ) * DGRHS.interactionEnergy μ W +
            Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))⁻¹))| ≤
          C * (Real.exp 1 + (N : ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a, b)
  let a := (β : ℝ) * DGRHS.interactionEnergy μ W
  obtain ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT,c,C,hc0,hc1,hC,hRate⟩ :=
    sourceLogSingularPartition_original_rate β hd ρ M hM hρ hpair htail
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => (β : ℝ) * eig i)))⁻¹
  have hLow N (hN : 1 ≤ N) : Real.exp a ≤ (sourceLogSingularPartition β ρ N).toReal :=
    sourceLogSingularPartition_lower β hβ hd ρ M hM hρ hpair htail N hN
  have hLimit : Real.exp a ≤ Real.exp a * z :=
    ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun N hN => hLow N hN)
  have hz : 1 ≤ z := by nlinarith [Real.exp_pos a]
  have hLog N (hN : 1 ≤ N) :
      |Real.log (sourceLogSingularPartition β ρ N).toReal - (a + Real.log z)| ≤
        (Real.exp (-a) * C) * (Real.exp 1 + (N : ℝ))^(-c) := by
    calc
      _ ≤ Real.exp (-a) * |(sourceLogSingularPartition β ρ N).toReal - Real.exp a * z| :=
        affine_log_difference_le a _ z (hLow N hN) hz
      _ ≤ _ := by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hRate N hN).2 (Real.exp_pos (-a)).le
  let D := (1 + Real.exp (-a)) * C
  refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,
    DGRHS.SourceRepulsiveLogRate.partition_tendsto_of_power_error _ (a + Real.log z)
      (Real.exp (-a) * C) c hc0 hLog,c,D,hc0,hc1,by dsimp [D]; positivity,?_⟩
  intro N hN
  have hweight : 0 ≤ (Real.exp 1 + (N : ℝ))^(-c) := Real.rpow_nonneg (by positivity) _
  refine ⟨(hRate N hN).1,hLow N hN,?_,?_⟩
  · exact (hRate N hN).2.trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; nlinarith [Real.exp_pos (-a)]) hweight)
  · exact (hLog N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; nlinarith [Real.exp_pos (-a)]) hweight)

end DGRHS.CLT
#check @DGRHS.CLT.sourceLogSingularPartition_lower
#print axioms DGRHS.CLT.sourceLogSingularPartition_lower
#check @DGRHS.CLT.sourceLogSingularPartition_original_log_rate
#print axioms DGRHS.CLT.sourceLogSingularPartition_original_log_rate
