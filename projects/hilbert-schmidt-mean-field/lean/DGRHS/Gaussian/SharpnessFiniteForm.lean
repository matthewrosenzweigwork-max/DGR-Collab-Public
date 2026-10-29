import DGRHS.Gaussian.SharpnessSchur

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι α : Type*} [Fintype ι] [Fintype α]

def sharpnessAtomIntegral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (H : X × X → ℝ) (A B : Set X) : ℝ :=
  ∫ p, H p ∂(μ.restrict A).prod (μ.restrict B)

def sharpnessAtomStep {X : Type*} (A : α → Set X) (z : α → ℝ) (x : X) : ℝ :=
  ∑ i, (A i).indicator (fun _ => z i) x

lemma sharpness_atom_integral_indicator {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (H : X × X → ℝ)
    (A B : Set X) (_hA : MeasurableSet A) (_hB : MeasurableSet B) (a b : ℝ) :
    (fun p => H p * A.indicator (fun _ => a) p.1 * B.indicator (fun _ => b) p.2) =
      (A ×ˢ B).indicator (fun p => (a*b)*H p) := by
  funext p
  by_cases ha : p.1 ∈ A <;> by_cases hb : p.2 ∈ B <;> simp [ha, hb]; ring

lemma stronglyMeasurable_sharpnessAtomStep {X : Type*} [MeasurableSpace X]
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (z : α → ℝ) :
    StronglyMeasurable (sharpnessAtomStep A z) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact stronglyMeasurable_const.indicator (hA i)

lemma norm_sharpnessAtomStep_le {X : Type*} (A : α → Set X) (z : α → ℝ) (x : X) :
    ‖sharpnessAtomStep A z x‖ ≤ ∑ i, |z i| := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x ∈ A i <;> simp [hx, Real.norm_eq_abs]

/-- Actual finite-product Fubini identity for the block form. -/
lemma sharpness_atom_form_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (H : X × X → ℝ) (hiH : Integrable H (μ.prod μ))
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) (z : α → ℝ) :
    (∫ p, H p*sharpnessAtomStep A z p.1*sharpnessAtomStep A z p.2 ∂μ.prod μ) =
      ∑ i, ∑ j, z i*z j*sharpnessAtomIntegral μ H (A i) (A j) := by
  let T := fun i j (p : X × X) =>
    H p*(A i).indicator (fun _ => z i) p.1*(A j).indicator (fun _ => z j) p.2
  have hiT (i j : α) : Integrable (T i j) (μ.prod μ) := by
    change Integrable (fun p => H p*(A i).indicator (fun _ => z i) p.1*
      (A j).indicator (fun _ => z j) p.2) (μ.prod μ)
    rw [sharpness_atom_integral_indicator μ H (A i) (A j) (hA i) (hA j) (z i) (z j)]
    exact (hiH.const_mul (z i*z j)).indicator ((hA i).prod (hA j))
  have heT (i j : α) : (∫ p, T i j p ∂μ.prod μ) =
      z i*z j*sharpnessAtomIntegral μ H (A i) (A j) := by
    change (∫ p, H p*(A i).indicator (fun _ => z i) p.1*
      (A j).indicator (fun _ => z j) p.2 ∂μ.prod μ) = _
    rw [sharpness_atom_integral_indicator μ H (A i) (A j) (hA i) (hA j) (z i) (z j),
      integral_indicator ((hA i).prod (hA j)), integral_const_mul]
    rw [sharpnessAtomIntegral, Measure.prod_restrict]
  have he : (fun p : X × X => H p*sharpnessAtomStep A z p.1*sharpnessAtomStep A z p.2) =
      (fun p => ∑ i, ∑ j, T i j p) := by
    funext p
    dsimp [sharpnessAtomStep, T]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, integral_finsetSum _ (fun i _ => by
    simpa only [Finset.sum_apply] using integrable_finsetSum Finset.univ (fun j _ => hiT i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hiT i j)]
  exact Finset.sum_congr rfl (fun j _ => heT i j)

/-- The actual finite block matrix is positive, with no full-kernel L2 or
supplied positivity premise. This is the genuine finite compression form. -/
theorem sharpness_finite_atom_form_nonneg (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (A : α → Set (EuclideanSpace ℝ ι)) (hA : ∀ i, MeasurableSet (A i)) (z : α → ℝ) :
    0 ≤ ∑ i, ∑ j, z i*z j * sharpnessAtomIntegral (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) (A i) (A j) := by
  have hf := stronglyMeasurable_sharpnessAtomStep A hA z
  have hK : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hn := (sharpness_centered_riesz_bounded_form_nonneg s hs ha ρ M hM hρ
    (sharpnessAtomStep A z) hf (∑ i, |z i|) hK (norm_sharpnessAtomStep_le A z)).2
  exact hn.trans_eq (sharpness_atom_form_identity _ _
    (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ) A hA z)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_finite_atom_form_nonneg
#check @DGRHS.Gaussian.sharpness_finite_atom_form_nonneg

#print axioms DGRHS.Gaussian.sharpness_atom_form_identity
