import DGRHS.Gaussian.SharpnessAtomAverage
import DGRHS.Gaussian.SharpnessCellMass

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- The genuine block-diagonal average is nonnegative and has a bound in
terms of its actual positive atom mass. -/
theorem sharpness_centered_atom_average_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A)
    (hmass : 0 < (gaussianRieszDensityMeasure ρ A).toReal) :
    0 ≤ (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict A).prod ((gaussianRieszDensityMeasure ρ).restrict A)) /
        (gaussianRieszDensityMeasure ρ A).toReal^2 ∧
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict A).prod ((gaussianRieszDensityMeasure ρ).restrict A)) /
        (gaussianRieszDensityMeasure ρ A).toReal^2 ≤
      (M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s))) /
          (gaussianRieszDensityMeasure ρ A).toReal +
      gaussianRieszSourceCoefficient s/s * δ^(-s) + gaussianRieszPhysicalPotentialConstant s M ι := by
  let t := (gaussianRieszDensityMeasure ρ A).toReal
  let S := M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
    ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s))
  let D := gaussianRieszSourceCoefficient s/s * δ^(-s)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  have ht : t ≠ 0 := ne_of_gt hmass
  have hpair := (sharpness_centered_atom_pair_bound s δ hs hδ ha ρ M hM hρ A).2
  constructor
  · exact div_nonneg (sharpness_centered_atom_pair_nonneg s hs ha ρ M hM hρ A hA) (sq_nonneg _)
  · calc
      _ ≤ (t*S+(D+B)*t^2)/t^2 := div_le_div_of_nonneg_right hpair (sq_nonneg _)
      _ = S/t+D+B := by field_simp; ring


/-- Source good-cell diagonal cap, derived from the genuine geometric cell
predicate and the actual bounded density. The coefficient is explicit. -/
theorem sharpness_good_atom_diagonal_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (a : ℝ) (ha0 : 0 < a)
    (I : BoxIntegral.Box ι) (hwidth : ∀ i, I.upper i-I.lower i = δ)
    (hgood : sharpnessGoodCell ρ a I) :
    0 ≤ (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict (sharpnessGoodAtom ρ a I)).prod
        ((gaussianRieszDensityMeasure ρ).restrict (sharpnessGoodAtom ρ a I))) /
          (gaussianRieszDensityMeasure ρ (sharpnessGoodAtom ρ a I)).toReal^2 ∧
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict (sharpnessGoodAtom ρ a I)).prod
        ((gaussianRieszDensityMeasure ρ).restrict (sharpnessGoodAtom ρ a I))) /
          (gaussianRieszDensityMeasure ρ (sharpnessGoodAtom ρ a I)).toReal^2 ≤
      (2 * (M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
        ((Fintype.card ι : ℝ)-s))) / a + gaussianRieszSourceCoefficient s/s) * δ^(-s) +
        gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  let A := sharpnessGoodAtom ρ a I
  let t := (μ A).toReal
  let V := M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
    ((Fintype.card ι : ℝ)-s))
  have hvol : volume (I : Set (ι → ℝ)) = ENNReal.ofReal δ ^ Fintype.card ι := by
    rw [volume_sharpnessBox]
    simp_rw [hwidth]
    simp
  have hlow := (sharpness_good_atom_mass_bounds ρ hρm a M hρ I hgood).1
  rw [hvol] at hlow
  have hreal := ENNReal.toReal_mono (measure_ne_top μ A) hlow
  have htlow : (a/2)*δ^Fintype.card ι ≤ t := by
    have hhalf : (1/2 : ℝ≥0∞).toReal = (1/2 : ℝ) := by norm_num
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0.le,
      ENNReal.toReal_mul, hhalf, ENNReal.toReal_pow, ENNReal.toReal_ofReal hδ.le] at hreal
    convert hreal using 1
    ring
  have htpos : 0 < t := lt_of_lt_of_le
    (mul_pos (div_pos ha0 (by norm_num)) (pow_pos hδ _)) htlow
  have hV : 0 ≤ V := by
    have hc := (gaussianRieszSourceCoefficient_pos s hs).le
    dsimp [V]
    positivity
  have hpower : δ^((Fintype.card ι : ℝ)-s) = δ^Fintype.card ι * δ^(-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ]
    congr 1
  have hterm : V*δ^((Fintype.card ι : ℝ)-s)/t ≤ (2*V/a)*δ^(-s) := by
    apply (div_le_iff₀ htpos).mpr
    have hg : (2*V/a)*δ^(-s)*((a/2)*δ^Fintype.card ι) ≤ (2*V/a)*δ^(-s)*t :=
      mul_le_mul_of_nonneg_left htlow
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hV) ha0.le) (Real.rpow_nonneg hδ.le _))
    have he : (2*V/a)*δ^(-s)*((a/2)*δ^Fintype.card ι) = V*δ^((Fintype.card ι : ℝ)-s) := by
      rw [hpower]
      have hane : a ≠ 0 := ne_of_gt ha0
      field_simp
    rw [he] at hg
    exact hg
  have hb := sharpness_centered_atom_average_bound s δ hs hδ ha ρ M hM hρ A
    (measurableSet_sharpnessGoodAtom ρ hρm a I) htpos
  refine ⟨hb.1, ?_⟩
  have heS : M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
      ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s)) = V*δ^((Fintype.card ι : ℝ)-s) := by
    dsimp [V]
    ring
  rw [heS] at hb
  dsimp [t, A, μ, V] at hterm
  calc
    _ ≤ _ := hb.2
    _ ≤ _ := by linarith [hterm]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_centered_atom_average_bound
#check @DGRHS.Gaussian.sharpness_centered_atom_average_bound

#print axioms DGRHS.Gaussian.sharpness_good_atom_diagonal_bound
#check @DGRHS.Gaussian.sharpness_good_atom_diagonal_bound
