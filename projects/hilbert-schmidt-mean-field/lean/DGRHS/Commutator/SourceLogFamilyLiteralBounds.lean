/- Common literal partition and temperature-window constants are chosen
before the density. The singular iid equality and properness are applied
for each law, retaining the same common bound through normalization. -/
import DGRHS.Commutator.SourceLogTransportFamilyPartition
import DGRHS.Entropy.SourceTemperatureWindow
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_log_family_literal_cap (β : ℝ≥0)
    (hd : 0 < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : EuclideanSpace ℝ ι → ℝ,
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∀ N : ℕ, 1 ≤ N → (sourceLogSingularPartition β ρ N).toReal ≤ C := by
  obtain ⟨C, _, hcap⟩ := exists_log_family_source_cap (ι := ι) (β : ℝ) β.coe_nonneg hd M hM
  refine ⟨max C 1, le_max_right _ _, ?_⟩
  intro ρ hμ hρ hpair N hN
  have hb := (hcap ρ hρ hpair N hN).2
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)]
  calc
    _ ≤ C := by simpa only [sourceLogTransportNumerator, zero_mul, add_zero] using hb
    _ ≤ max C 1 := le_max_left _ _

theorem exists_log_family_literal_window (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ρ : EuclideanSpace ℝ ι → ℝ,
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∀ β : ℝ≥0, (β : ℝ) ≤ (B : ℝ) → ∀ N : ℕ, 1 ≤ N →
      (sourceLogSingularPartition β ρ N).toReal ≤ C := by
  obtain ⟨C, hC, hcap⟩ := exists_log_family_literal_cap (ι := ι) B hd M hM
  refine ⟨C, hC, ?_⟩
  intro ρ hμ hρ hpair β hβB N hN
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ (fun a b => logPhysicalPair (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))) N
  let X := fun x => -(N : ℝ)*E x
  have he (b : ℝ) : (fun x => Real.exp (b*X x)) =
      (fun x => Real.exp (-b*(N : ℝ)*E x)) := by
    funext x
    congr 1
    dsimp [X]
    ring
  have hi : Integrable (fun x => Real.exp ((B : ℝ)*X x)) P := by
    rw [he]
    exact sourceLogEnergyWeight_integrable (B : ℝ) B.coe_nonneg hd ρ M hM hρ hpair N
  have hb := hcap ρ hρ hpair N hN
  rw [sourceLogSingularPartition_eq_integral B hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)] at hb
  have hb' : (∫ x, Real.exp ((B : ℝ)*X x) ∂P) ≤ C := by rw [he]; exact hb
  obtain ⟨_, hout⟩ := exponential_temperature_window P X (B : ℝ) hB hi C hC hb'
    (β : ℝ) β.coe_nonneg hβB
  rw [he] at hout
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)]
  exact hout

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_log_family_literal_cap
#check @DGRHS.Commutator.exists_log_family_literal_window
#print axioms DGRHS.Commutator.exists_log_family_literal_cap
#print axioms DGRHS.Commutator.exists_log_family_literal_window
