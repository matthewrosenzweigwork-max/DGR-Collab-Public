import LeanResearch.PeriodicAttractiveLogGas.FibreEntropy

/-! Source 3095–3103: the elementary uniform finite entropy bound and its
actual occupation-fibre consequence. No sparse drift or multislice inequality
is an input to this unit. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace PeriodicAttractiveLogGas.FiniteFibreEntropyBound
open MeshCells LabelOccupations CellRestrictions DiscreteOccupationIdentities FibreProjection FibreEntropy

/-- The finite-probability estimate follows by comparing every positive
summand with the total mass; zero summands need no logarithm positivity. -/
theorem sum_mul_log_le {α : Type*} [Fintype α] (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ x, F x * Real.log (F x)) ≤ (∑ x, F x) * Real.log (∑ x, F x) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : F x = 0
  · simp only [hx, zero_mul, le_refl]
  · have hp : 0 < F x := lt_of_le_of_ne (hF x) (Ne.symm hx)
    have hs : F x ≤ ∑ y, F y := Finset.single_le_sum (fun y _ => hF y) (Finset.mem_univ x)
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hp hs) (hF x)

/-- Uniform finite entropy, including zero mean and singleton types. -/
theorem finiteEntropy_uniform_le {α : Type*} [Fintype α]
    (hc : 0 < Fintype.card α) (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) :
    finiteEntropy (fun _ : α => (Fintype.card α : ℝ)⁻¹) F ≤
      ((∑ x, F x) / Fintype.card α) * Real.log (Fintype.card α) := by
  let M : ℝ := Fintype.card α
  let S : ℝ := ∑ x, F x
  have hM : 0 < M := by
    change 0 < (Fintype.card α : ℝ)
    exact_mod_cast hc
  have hn : finiteEntropy (fun _ : α => (Fintype.card α : ℝ)⁻¹) F =
      (∑ x, F x * Real.log (F x)) / M - (S / M) * Real.log (S / M) := by
    simp only [finiteEntropy, ← Finset.mul_sum]
    simp only [M, S, div_eq_mul_inv, mul_comm]
  rw [hn]
  have hb : (∑ x, F x * Real.log (F x)) / M ≤ (S / M) * Real.log S := by
    convert div_le_div_of_nonneg_right (sum_mul_log_le F hF) hM.le using 1; dsimp [S]; ring
  calc
    _ ≤ (S / M) * Real.log S - (S / M) * Real.log (S / M) := by linarith only [hb]
    _ = _ := by
      change (S / M) * Real.log S - (S / M) * Real.log (S / M) = (S / M) * Real.log M
      by_cases hs : S = 0
      · simp only [hs, zero_div, zero_mul, sub_zero]
      · rw [Real.log_div hs hM.ne']
        ring

/-- The same bound for the existing extended entropy of the literal uniform
probability measure; finiteness is supplied by the actual finite measure. -/
theorem entropy_uniform_le {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hc : 0 < Fintype.card α)
    (F : α → ℝ) (hF : ∀ x, 0 ≤ F x) :
    entropy (finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)) F ≤
      (((∫ x, F x ∂finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹)) *
        Real.log (Fintype.card α) : ℝ) : EReal) := by
  rw [entropy_finiteMeasure (fun _ : α => (Fintype.card α : ℝ)⁻¹) F
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hF,
    integral_uniform_finiteMeasure]
  exact_mod_cast finiteEntropy_uniform_le hc F hF

variable {J N : ℕ} {t : ℝ}

/-- Actual fibre words inject into all length-N words on the J² mesh cells. -/
theorem fibre_card_le (m : OccupationState J N t) :
    Fintype.card (Fibre m) ≤ (J ^ 2) ^ N := by
  have hi : Function.Injective (fun η : Fibre m => η.val.val) := by
    intro η ζ h
    apply Subtype.ext
    exact Subtype.ext h
  have hh := Fintype.card_le_of_injective (fun η : Fibre m => η.val.val) hi
  simpa only [LabelVector, Fintype.card_fun, Fintype.card_fin, card_meshIndex] using hh

theorem fibre_log_card_le (hJ : 0 < J) (m : OccupationState J N t) :
    Real.log (Fintype.card (Fibre m)) ≤ 2 * (N : ℝ) * Real.log J := by
  have hc : (0 : ℝ) < Fintype.card (Fibre m) := by exact_mod_cast fibre_card_pos m
  have hb : (Fintype.card (Fibre m) : ℝ) ≤ ((J : ℝ) ^ 2) ^ N := by
    exact_mod_cast fibre_card_le m
  have hp : (0 : ℝ) < ((J : ℝ) ^ 2) ^ N :=
    pow_pos (pow_pos (by exact_mod_cast hJ) _) _
  have hh := (Real.log_le_log_iff hc hp).mpr hb
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith only [hh]

/-- Source finite-fibre entropy bound with the exact coefficient 2 N log J. -/
theorem uniformFibreEntropy_le (hJ : 0 < J) (F : LabelState J N t → ℝ)
    (hF : ∀ η, 0 ≤ F η) (m : OccupationState J N t) :
    uniformFibreEntropy F m ≤ (2 * (N : ℝ) * Real.log J) * fibreAverage F m := by
  have hh := finiteEntropy_uniform_le (fibre_card_pos m) (fun η : Fibre m => F η.val)
    (fun η => hF η.val)
  have he : finiteEntropy (fun _ : Fibre m => (Fintype.card (Fibre m) : ℝ)⁻¹)
      (fun η => F η.val) = uniformFibreEntropy F m := by
    simp only [finiteEntropy, uniformFibreEntropy, fibreAverage, div_eq_mul_inv, ← Finset.mul_sum]
    simp only [mul_comm]
  rw [he] at hh
  change uniformFibreEntropy F m ≤ fibreAverage F m * Real.log (Fintype.card (Fibre m)) at hh
  calc
    _ ≤ fibreAverage F m * Real.log (Fintype.card (Fibre m)) := hh
    _ ≤ fibreAverage F m * (2 * (N : ℝ) * Real.log J) :=
      mul_le_mul_of_nonneg_left (fibre_log_card_le hJ m) (fibreAverage_nonneg hF m)
    _ = _ := mul_comm _ _

theorem actual_fibre_entropy_le (hJ : 0 < J) (F : LabelState J N t → ℝ)
    (hF : ∀ η, 0 ≤ F η) (m : OccupationState J N t) :
    entropy (finiteMeasure (fun _ : Fibre m => (Fintype.card (Fibre m) : ℝ)⁻¹))
      (fun η => F η.val) ≤ (((2 * (N : ℝ) * Real.log J) * fibreAverage F m : ℝ) : EReal) := by
  rw [entropy_uniform_fibre F hF m]
  exact_mod_cast uniformFibreEntropy_le hJ F hF m

/-- Arbitrary chosen occupation classes with their original unnormalized
occupation weights, including sparse/empty-cell profiles. No drift is presumed. -/
theorem weighted_fibre_entropy_le (hJ : 0 < J) (β : ℝ) (F : LabelState J N t → ℝ)
    (hF : ∀ η, 0 ≤ F η) (S : Finset (OccupationState J N t)) :
    (∑ m ∈ S, occupationWeight hJ β m * uniformFibreEntropy F m) ≤
      (2 * (N : ℝ) * Real.log J) * ∑ m ∈ S, occupationWeight hJ β m * fibreAverage F m := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  have hh := mul_le_mul_of_nonneg_left (uniformFibreEntropy_le hJ F hF m)
    (show 0 ≤ occupationWeight hJ β m from ENNReal.toReal_nonneg)
  calc
    _ ≤ occupationWeight hJ β m * ((2 * (N : ℝ) * Real.log J) * fibreAverage F m) := hh
    _ = _ := by ring

end PeriodicAttractiveLogGas.FiniteFibreEntropyBound
