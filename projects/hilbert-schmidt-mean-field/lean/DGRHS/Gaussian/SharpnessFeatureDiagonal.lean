import DGRHS.Gaussian.SharpnessFiniteFeatureMean

noncomputable section
open MeasureTheory Set Matrix Filter BoxIntegral
open scoped ENNReal Classical InnerProductSpace
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The remainder needs no geometric lower density: its actual half-mass
and the proper full-kernel Schur bound give a uniform diagonal cap. -/
lemma sharpness_remainder_average_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : Set (EuclideanSpace ℝ ι))
    (hA : MeasurableSet A) (hhalf : (1/2:ℝ) ≤ (gaussianRieszDensityMeasure ρ A).toReal) :
    sharpnessAtomAverage (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) A A ≤
      8*gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let t := (μ A).toReal
  have ht : 0 < t := by dsimp [t,μ]; linarith
  have hd : Pairwise (fun i j : Unit => Disjoint ((fun _ : Unit => A) i) ((fun _ : Unit => A) j)) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hb := sharpness_finite_atom_form_le s hs ha ρ M hM hρ
    (fun _ : Unit => A) (fun _ => hA) hd (fun _ => 1)
  have hblock : sharpnessAtomIntegral μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) A A ≤ 4*B*t := by
    simpa only [Finset.univ_unique,Finset.sum_singleton,one_mul,one_pow] using
      (le_abs_self _).trans hb
  have hB : 0 ≤ B := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (EuclideanSpace ℝ ι))
    exact ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ x).2.1).trans
      (sharpness_riesz_potential_bound s hs ha ρ M hM hρ x).2.2
  unfold sharpnessAtomAverage
  change _ / (t*t) ≤ 8*B
  apply (div_le_iff₀ (mul_pos ht ht)).mpr
  have hht : (1/2:ℝ) ≤ t := hhalf
  have hg := mul_le_mul_of_nonneg_left hht (by positivity : 0 ≤ 8*B*t)
  nlinarith

def sharpnessGoodDiagonalCoefficient (s M a : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  2*(M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι:ℝ)/2) /
    ((Fintype.card ι:ℝ)-s)))/a + gaussianRieszSourceCoefficient s/s

lemma sharpness_partition_diagonal_bound (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : Box ι) (L : ℝ) (hL : 0 < L) (hw : ∀ i, I.upper i-I.lower i = L)
    (hI : gaussianRieszDensityMeasure ρ (WithLp.ofLp ⁻¹' (I : Set (ι → ℝ))) ≤ ENNReal.ofReal (1/2:ℝ))
    (m : ℕ) (i : sharpnessAtomIndex ρ a (sharpnessDyadicPartition I m)) :
    sharpnessAtomAverage (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m) i)
      (sharpnessPartitionAtom ρ a (sharpnessDyadicPartition I m) i) ≤
        sharpnessGoodDiagonalCoefficient s M a ι*(L/(2:ℝ)^m)^(-s) +
          8*gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let P := sharpnessDyadicPartition I m
  have hB : 0 ≤ B := by
    exact ((sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.1).trans
      (sharpness_riesz_potential_bound s hs ha ρ M hM hρ 0).2.2
  have hC : 0 ≤ sharpnessGoodDiagonalCoefficient s M a ι := by
    unfold sharpnessGoodDiagonalCoefficient
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    positivity
  have hδ : 0 < L/(2:ℝ)^m := by positivity
  cases i with
  | none =>
    have hr := sharpness_remainder_mass_lower ρ hρm a P hI
    have hhr := ENNReal.toReal_mono (measure_ne_top μ _) hr
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1/2:ℝ))] at hhr
    have hb := sharpness_remainder_average_bound s hs ha ρ M hM hρ
      (sharpnessRemainder ρ a P) (measurableSet_sharpnessGoodUnion ρ hρm a P).compl hhr
    exact hb.trans (by have hp := Real.rpow_nonneg hδ.le (-s); nlinarith)
  | some J =>
    have hJ := Finset.mem_filter.mp J.2
    have hb := (sharpness_good_atom_diagonal_bound s (L/(2:ℝ)^m) hs hδ ha ρ hρm M hM hρ a ha0 J.1
      (fun j => by rw [sharpnessDyadicPartition_width I m hJ.1,hw]) hJ.2).2
    change sharpnessAtomAverage μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
      (sharpnessGoodAtom ρ a J.1) (sharpnessGoodAtom ρ a J.1) ≤ _
    have he : sharpnessAtomAverage μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
      (sharpnessGoodAtom ρ a J.1) (sharpnessGoodAtom ρ a J.1) =
      (∫ p,hoeffdingCentered μ (gaussianRieszPhysicalPair s) p ∂(μ.restrict (sharpnessGoodAtom ρ a J.1)).prod
        (μ.restrict (sharpnessGoodAtom ρ a J.1)))/(μ (sharpnessGoodAtom ρ a J.1)).toReal^2 := by
      simp only [sharpnessAtomAverage,sharpnessAtomIntegral,pow_two]
    rw [he]
    exact hb.trans (by
      dsimp only [sharpnessGoodDiagonalCoefficient]
      change _ + B ≤ _ + 8*B
      linarith)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_remainder_average_bound
#print axioms DGRHS.Gaussian.sharpness_partition_diagonal_bound
#check @DGRHS.Gaussian.sharpness_partition_diagonal_bound
