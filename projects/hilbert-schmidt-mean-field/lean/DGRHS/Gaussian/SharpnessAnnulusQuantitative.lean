import DGRHS.Gaussian.SharpnessAnnulusPhysical

noncomputable section
open MeasureTheory Set BoxIntegral
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessAnnularEpsilon (d : ℕ) : ℝ := ((2:ℝ)^d-1)/(12*(4:ℝ)^d)

lemma sharpnessAnnularEpsilon_bounds {d : ℕ} (hd : 1 ≤ d) :
    0 < sharpnessAnnularEpsilon d ∧ sharpnessAnnularEpsilon d < 1 := by
  have h2 : (2:ℝ) ≤ 2^d := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hd
  have h4 : (4:ℝ)^d = ((2:ℝ)^d)^2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hden : 0 < 12*(4:ℝ)^d := by positivity
  constructor
  · exact div_pos (by linarith) hden
  · rw [sharpnessAnnularEpsilon, div_lt_iff₀ hden, one_mul, h4]
    nlinarith [sq_nonneg ((2:ℝ)^d)]

lemma sharpness_annular_coefficient_identity (d : ℕ) (q R : ℝ) :
    q^d*((2*R)^d-R^d)-6*sharpnessAnnularEpsilon d*(2*q)^d*(2*R)^d =
      (((2:ℝ)^d-1)/2)*q^d*R^d := by
  have h4 : (4:ℝ)^d = ((2:ℝ)^d)^2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  simp only [sharpnessAnnularEpsilon, mul_pow]
  rw [h4]
  have hn : (2:ℝ)^d ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Genuine bounded probability density yields a positive annular pair-mass
constant, simultaneously at every physical dyadic refinement. This is the
geometric input for the critical logarithmic HS divergence. -/
theorem sharpness_exists_uniform_good_annular_mass (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ q : ℝ, ∃ hq : 0 < q, ∃ c : ℝ, 0 < c ∧
      gaussianRieszDensityMeasure ρ (sharpnessCenteredCube z q) ≤ ENNReal.ofReal (1/2 : ℝ) ∧
      (∀ x y : EuclideanSpace ℝ ι, x ∈ sharpnessCenteredCube z q →
        y ∈ sharpnessCenteredCube z q → x ≠ y →
        gaussianRieszPhysicalPair s (x,y)/2 ≤
          hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) (x,y)) ∧
      ∀ (m : ℕ) (R : ℝ), 0 ≤ R → R ≤ q/2 →
        let I := sharpnessInitialBox z q hq
        let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a (sharpnessDyadicPartition I m)
        c*R^Fintype.card ι ≤
        ((volume.prod volume) (sharpnessAnnularPairs z q R ∩ (G ×ˢ G))).toReal := by
  have hd : 1 ≤ Fintype.card ι := by
    have hc : (0:ℝ) < Fintype.card ι := by linarith
    have hn : 0 < Fintype.card ι := by exact_mod_cast hc
    omega
  obtain ⟨heps,heps1⟩ := sharpnessAnnularEpsilon_bounds hd
  obtain ⟨a,hap,z,q,hq,hmass,hlocal,hann⟩ :=
    sharpness_exists_physical_annular_data s hs ha ρ hρm M hM hρ
      (sharpnessAnnularEpsilon (Fintype.card ι)) heps heps1
  have h2 : (2:ℝ) ≤ 2^Fintype.card ι := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hd
  refine ⟨a,hap,z,q,hq,(((2:ℝ)^Fintype.card ι-1)/2)*q^Fintype.card ι,
    mul_pos (div_pos (by linarith) (by norm_num)) (pow_pos hq _),hmass,hlocal,?_⟩
  intro m R hR hRq
  have hb := hann m R hR hRq
  dsimp only at hb ⊢
  rw [sharpness_annular_coefficient_identity] at hb
  simpa only [mul_assoc] using hb

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpnessAnnularEpsilon_bounds
#print axioms DGRHS.Gaussian.sharpness_annular_coefficient_identity
#print axioms DGRHS.Gaussian.sharpness_exists_uniform_good_annular_mass
#check @DGRHS.Gaussian.sharpness_exists_uniform_good_annular_mass
