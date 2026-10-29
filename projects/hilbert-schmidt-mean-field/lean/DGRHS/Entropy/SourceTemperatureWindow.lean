/- Original fixed-temperature window bound, derived from genuine endpoint
partition control. The growing-temperature conclusion still needs the
separate sharp pointwise energy lower bound. -/
import DGRHS.Entropy.SourceLogForcingNormalization
import DGRHS.Concentration.MasterInterpolation
import DGRHS.CLT.SourceRieszSingularIdentification
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

theorem exponential_temperature_window {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (X : S → ℝ) (B : ℝ) (hB : 0 < B)
    (hi : Integrable (fun x => Real.exp (B * X x)) μ)
    (C : ℝ) (hC : 1 ≤ C) (hb : (∫ x, Real.exp (B * X x) ∂μ) ≤ C)
    (β : ℝ) (hβ : 0 ≤ β) (hβB : β ≤ B) :
    Integrable (fun x => Real.exp (β * X x)) μ ∧
      (∫ x, Real.exp (β * X x) ∂μ) ≤ C := by
  let t := β / B
  have ht0 : 0 ≤ t := div_nonneg hβ hB.le
  have ht1 : t ≤ 1 := (div_le_one hB).mpr hβB
  have hm : AEMeasurable (fun x => B * X x) μ := by
    simpa only [Function.comp_def, Real.log_exp] using
      Real.measurable_log.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  obtain ⟨hproper, hbound⟩ := DGRHS.Concentration.interpolated_exp_integral μ
    (fun _ => 0) (fun x => B * X x) aemeasurable_const hm (by simp) hi t ht0 ht1
  have he (x : S) : (1-t)*0+t*(B*X x) = β*X x := by
    dsimp [t]
    field_simp
    ring
  simp_rw [he] at hproper hbound
  have hzero : (∫ x : S, Real.exp (0 : ℝ) ∂μ) = 1 := by simp
  rw [hzero] at hbound
  refine ⟨hproper, hbound.trans ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hC (by linarith : 0 ≤ 1-t)
  have h2 := mul_le_mul_of_nonneg_left hb ht0
  nlinarith

open DGRHS.Gaussian DGRHS.CLT DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

theorem sourceLogPartition_fixed_temperature_window (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ≥0, (β : ℝ) ≤ (B : ℝ) → ∀ N : ℕ, 1 ≤ N →
      (sourceLogSingularPartition β ρ N).toReal ≤ C := by
  obtain ⟨C, hC, hcap⟩ := sourceLogPartition_original_bounds_one_le B hd ρ M hM hρ hpair
  refine ⟨C, hC, ?_⟩
  intro β hβB N hN
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ (fun a b => logPhysicalPair (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))) N
  let X := fun x => -(N : ℝ) * E x
  have he (b : ℝ) : (fun x => Real.exp (b*X x)) =
      (fun x => Real.exp (-b*(N : ℝ)*E x)) := by
    funext x
    congr 1
    dsimp [X]
    ring
  have hi : Integrable (fun x => Real.exp ((B : ℝ)*X x)) P := by
    rw [he]
    exact sourceLogEnergyWeight_integrable (B : ℝ) B.coe_nonneg hd ρ M hM hρ hpair N
  have hb := (hcap N hN).2
  rw [sourceLogSingularPartition_eq_integral B hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)] at hb
  have hb' : (∫ x, Real.exp ((B : ℝ)*X x) ∂P) ≤ C := by rw [he]; exact hb
  obtain ⟨_, hout⟩ := exponential_temperature_window P X (B : ℝ) hB hi C hC hb'
    (β : ℝ) β.coe_nonneg hβB
  rw [he] at hout
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)]
  exact hout

theorem sourceRieszPartition_fixed_temperature_window (s B : ℝ) (hs : 0 < s)
    (hB : 0 < B) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ B → ∀ N : ℕ, 1 ≤ N →
      (sourceRieszSingularPartition s β ρ N).toReal ≤ C := by
  obtain ⟨Cb, _, hcap⟩ := sourceRieszPartition_uniform s B hs hB.le ha ρ M hM hρ
  let C := max Cb 1
  refine ⟨C, le_max_right _ _, ?_⟩
  intro β hβ hβB N hN
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
    (DGRHS.potential μ (fun a b => gaussianRieszPhysicalPair s (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => gaussianRieszPhysicalPair s (a,b))) N
  let X := fun x => -(N : ℝ) * E x
  have he (b : ℝ) : (fun x => Real.exp (b*X x)) =
      (fun x => Real.exp (-b*(N : ℝ)*E x)) := by
    funext x
    congr 1
    dsimp [X]
    ring
  obtain ⟨hi, hb⟩ := hcap N hN
  have hi' : Integrable (fun x => Real.exp (B*X x)) P := by rw [he]; exact hi
  have hb' : (∫ x, Real.exp (B*X x) ∂P) ≤ C := by
    rw [he]
    exact hb.trans (le_max_left _ _)
  obtain ⟨_, hout⟩ := exponential_temperature_window P X B hB hi' C (le_max_right _ _) hb'
    β hβ hβB
  rw [he] at hout
  rw [sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N]
  have hp : 0 ≤ physicalRieszSourcePartition s β ρ N := by
    unfold physicalRieszSourcePartition
    exact integral_nonneg fun x => (Real.exp_pos _).le
  rw [ENNReal.toReal_ofReal hp]
  exact hout

end DGRHS.Entropy
#check @DGRHS.Entropy.exponential_temperature_window
#check @DGRHS.Entropy.sourceLogPartition_fixed_temperature_window
#check @DGRHS.Entropy.sourceRieszPartition_fixed_temperature_window
#print axioms DGRHS.Entropy.exponential_temperature_window
#print axioms DGRHS.Entropy.sourceLogPartition_fixed_temperature_window
#print axioms DGRHS.Entropy.sourceRieszPartition_fixed_temperature_window
