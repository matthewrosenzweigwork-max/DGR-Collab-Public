import DGRHS.Gaussian.SharpnessAtomNormalized
import DGRHS.Gaussian.SharpnessWeightedForm

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {α X : Type*} [Fintype α] [MeasurableSpace X]

def sharpnessAtomAverage (μ : Measure X) (H : X × X → ℝ) (A B : Set X) : ℝ :=
  sharpnessAtomIntegral μ H A B / ((μ A).toReal*(μ B).toReal)

/-- Actual finite atom averaging kernel, with the original two-coordinate
conditional-average normalization. The remainder is another actual atom. -/
def sharpnessCompression (μ : Measure X) (H : X × X → ℝ) (A : α → Set X) : X × X → ℝ :=
  sharpnessAtomStep (fun ij : α × α => A ij.1 ×ˢ A ij.2)
    (fun ij => sharpnessAtomAverage μ H (A ij.1) (A ij.2))

lemma stronglyMeasurable_sharpnessCompression (μ : Measure X) (H : X × X → ℝ)
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    StronglyMeasurable (sharpnessCompression μ H A) :=
by
  exact stronglyMeasurable_sharpnessAtomStep (fun ij : α × α => A ij.1 ×ˢ A ij.2)
    (fun ij : α × α => (hA ij.1).prod (hA ij.2))
    (fun ij : α × α => sharpnessAtomAverage μ H (A ij.1) (A ij.2))

lemma sharpnessCompression_memLp (μ : Measure X) [IsFiniteMeasure μ] (H : X × X → ℝ)
    (A : α → Set X) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (sharpnessCompression μ H A) 2 (μ.prod μ) := by
  let K := ∑ ij : α × α, |sharpnessAtomAverage μ H (A ij.1) (A ij.2)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  exact (memLp_const K).of_le (stronglyMeasurable_sharpnessCompression μ H A hA).aestronglyMeasurable
    (Eventually.of_forall fun p => by
      simpa only [Real.norm_of_nonneg hK, sharpnessCompression, K] using
        norm_sharpnessAtomStep_le (fun ij : α × α => A ij.1 ×ˢ A ij.2)
          (fun ij => sharpnessAtomAverage μ H (A ij.1) (A ij.2)) p)

lemma sharpnessCompression_on_atom (μ : Measure X) (H : X × X → ℝ) (A : α → Set X)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) {i j : α} {x y : X}
    (hx : x ∈ A i) (hy : y ∈ A j) :
    sharpnessCompression μ H A (x,y) = sharpnessAtomAverage μ H (A i) (A j) := by
  have hu (ij : α × α) (hp : (x,y) ∈ A ij.1 ×ˢ A ij.2) : ij = (i,j) := by
    apply Prod.ext
    · by_contra hne
      exact (Set.disjoint_left.mp (hd hne)) hp.1 hx
    · by_contra hne
      exact (Set.disjoint_left.mp (hd hne)) hp.2 hy
  unfold sharpnessCompression sharpnessAtomStep
  rw [Finset.sum_eq_single (i,j)]
  · simp [hx, hy]
  · intro ij _ hne
    have hn : (x,y) ∉ A ij.1 ×ˢ A ij.2 := fun hp => hne (hu ij hp)
    simp [hn]
  · simp

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpnessCompression_memLp
#print axioms DGRHS.Gaussian.sharpnessCompression_on_atom
#check @DGRHS.Gaussian.sharpnessCompression_memLp
