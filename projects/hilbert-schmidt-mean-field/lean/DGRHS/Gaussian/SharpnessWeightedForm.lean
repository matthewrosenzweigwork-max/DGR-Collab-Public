import DGRHS.Gaussian.SharpnessFiniteForm

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι α : Type*} [Fintype ι] [Fintype α]

lemma sharpnessAtomStep_sq_of_disjoint {X : Type*} (A : α → Set X)
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (z : α → ℝ) (x : X) :
    (sharpnessAtomStep A z x)^2 = ∑ i, (A i).indicator (fun _ => (z i)^2) x := by
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := hx
    have hn (j : α) (hji : j ≠ i) : x ∉ A j := by
      intro hj
      exact (Set.disjoint_left.mp (hdisjoint hji)) hj hi
    have heF : (∑ j, (A j).indicator (fun _ => z j) x) = z i := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        simp [hn j hji]
      · simp
    have heS : (∑ j, (A j).indicator (fun _ => (z j)^2) x) = (z i)^2 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        simp [hn j hji]
      · simp
    change (∑ j, (A j).indicator (fun _ => z j) x)^2 = _
    rw [heF, heS]
  · have hn : ∀ i, x ∉ A i := not_exists.mp hx
    simp [sharpnessAtomStep, hn]

lemma sharpness_atom_step_sq_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (A : α → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (z : α → ℝ) :
    (∫ x, (sharpnessAtomStep A z x)^2 ∂μ) = ∑ i, (z i)^2*(μ (A i)).toReal := by
  have he : (fun x => (sharpnessAtomStep A z x)^2) =
      (fun x => ∑ i, (A i).indicator (fun _ => (z i)^2) x) := by
    funext x
    exact sharpnessAtomStep_sq_of_disjoint A hdisjoint z x
  rw [he, integral_finsetSum _ (fun i _ => (integrable_const ((z i)^2)).indicator (hA i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hA i), setIntegral_const]
  simp [Measure.real, mul_comm]

/-- The actual finite compression form has a scale-independent Schur cap
in the exact probability weights of its disjoint atoms. -/
theorem sharpness_finite_atom_form_le (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j))) (z : α → ℝ) :
    |∑ i, ∑ j, z i*z j * sharpnessAtomIntegral (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) (A i) (A j)| ≤
    (4*gaussianRieszPhysicalPotentialConstant s M ι) *
      ∑ i, (z i)^2*(gaussianRieszDensityMeasure ρ (A i)).toReal := by
  have hf := stronglyMeasurable_sharpnessAtomStep A hA z
  have hK : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hb := sharpness_centered_riesz_bounded_form_le s hs ha ρ M hM hρ
    (sharpnessAtomStep A z) hf (∑ i, |z i|) hK (norm_sharpnessAtomStep_le A z)
  have he := sharpness_atom_form_identity _ _
    (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ) A hA z
  rw [he, sharpness_atom_step_sq_integral _ A hA hdisjoint z] at hb
  exact hb

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_finite_atom_form_le
#check @DGRHS.Gaussian.sharpness_finite_atom_form_le
