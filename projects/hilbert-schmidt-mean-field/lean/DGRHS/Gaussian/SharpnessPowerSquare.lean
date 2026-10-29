import DGRHS.Gaussian.SharpnessAnnularSquare
import DGRHS.Gaussian.SharpnessAnnularScales

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_annular_coefficient_power (d : ℕ) (s C R : ℝ)
    (hC : 0 < C) (hR : 0 < R) :
    ((C*R)^(-s)/(2*s))^2*R^d = C^(-2*s)/(4*s^2)*R^((d:ℝ)-2*s) := by
  have hCsq : (C^(-s))^2 = C^(-2*s) := by
    rw [← Real.rpow_mul_natCast hC.le]; congr 1; ring
  have hRsq : (R^(-s))^2 = R^(-2*s) := by
    rw [← Real.rpow_mul_natCast hR.le]; congr 1; ring
  have hcombine : R^(-2*s)*R^d = R^((d:ℝ)-2*s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  rw [Real.mul_rpow hC.le hR.le,div_pow,mul_pow,hCsq,hRsq,
    show (2*s)^2 = 4*s^2 by ring]
  calc
    _ = (C^(-2*s)/(4*s^2))*(R^(-2*s)*R^d) := by ring
    _ = _ := by rw [hcombine]

/-- Actual source supercritical power lower bound. The statement is valid
throughout 0<s<d; it diverges precisely when d-2s is negative. No compression
mass, integral bound or spectral conclusion is assumed. -/
theorem sharpness_exists_compression_power (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ q : ℝ, ∃ hq : 0 < q, ∃ K : ℝ, 0 < K ∧
      ∀ m : ℕ, 4 ≤ m →
        let P := sharpnessDyadicPartition (sharpnessInitialBox z q hq) m
        let κ := sharpnessCompression (gaussianRieszDensityMeasure ρ)
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (sharpnessPartitionAtom ρ a P)
        K*((2*q)/(2:ℝ)^m)^((Fintype.card ι : ℝ)-2*s) ≤
          ∫ p,κ p^2 ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) := by
  have hd : (0:ℝ) < Fintype.card ι := by linarith
  obtain ⟨a,ha0,z,q,hq,c,hc,hmass,hlocal,hann⟩ :=
    sharpness_exists_uniform_good_annular_mass s hs ha ρ hρm M hM hρ
  let C := (3/2:ℝ)*(Fintype.card ι : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  let K := (C^(-2*s)/(4*s^2)*a^2*c)*(4:ℝ)^((Fintype.card ι : ℝ)-2*s)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨a,ha0,z,q,hq,K,hK,?_⟩
  intro m hm
  dsimp only
  let P := sharpnessDyadicPartition (sharpnessInitialBox z q hq) m
  let A := sharpnessPartitionAtom ρ a P
  let μ := gaussianRieszDensityMeasure ρ
  let κ := sharpnessCompression μ (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) A
  let G := WithLp.toLp 2 ⁻¹' sharpnessGoodUnion ρ a P
  let f := fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => (WithLp.ofLp p.1,WithLp.ofLp p.2)
  let R := sharpnessAnnularRadius q (m-4)
  let S := f ⁻¹' (sharpnessAnnularPairs z q R ∩ (G ×ˢ G))
  have hR : 0 < R := sharpnessAnnularRadius_pos hq _
  have hRq : R ≤ q/2 := sharpnessAnnularRadius_le_core hq.le _
  have hδR := sharpness_dyadic_cell_le_annular_quarter hq.le
    (show (m-4)+4 ≤ m by omega)
  have hb := sharpness_compression_annular_square_lower s hs ha ρ hρm M hM hρ a ha0 z q hq
    hmass hlocal m R hR hδR
  have hv := hann m R hR.le hRq
  dsimp only at hb hv
  have hp : 0 ≤ ((C*R)^(-s)/(2*s))^2*a^2 := by positivity
  have hh := mul_le_mul_of_nonneg_left hv hp
  have he : ((C*R)^(-s)/(2*s))^2*a^2*(c*R^Fintype.card ι) =
      (C^(-2*s)/(4*s^2)*a^2*c)*R^((Fintype.card ι : ℝ)-2*s) := by
    calc
      _ = (((C*R)^(-s)/(2*s))^2*R^Fintype.card ι)*a^2*c := by ring
      _ = _ := by rw [sharpness_annular_coefficient_power _ s C R hC hR]; ring
  rw [he] at hh
  have hpow : (2:ℝ)^m = 8*2^((m-4)+1) := by
    rw [← Nat.sub_add_cancel hm,show (m-4)+4 = ((m-4)+1)+3 by omega,pow_add]
    norm_num
    <;> ring
  have heR : R = 4*((2*q)/(2:ℝ)^m) := by
    dsimp [R,sharpnessAnnularRadius]
    rw [hpow]
    field_simp
    <;> ring
  have hiκ : Integrable (fun p => κ p^2) (μ.prod μ) :=
    (sharpnessCompression_memLp μ _ A (measurableSet_sharpnessPartitionAtom ρ hρm a P)).integrable_sq
  have hset : ∫ p in S,κ p^2 ∂μ.prod μ ≤ ∫ p,κ p^2 ∂μ.prod μ :=
    setIntegral_le_integral hiκ (Eventually.of_forall (fun p => sq_nonneg (κ p)))
  have hall := (hh.trans hb).trans hset
  rw [heR,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity)] at hall
  change K*((2*q)/(2:ℝ)^m)^((Fintype.card ι : ℝ)-2*s) ≤ _
  simpa only [K,mul_assoc] using hall

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_annular_coefficient_power
#print axioms DGRHS.Gaussian.sharpness_exists_compression_power
#check @DGRHS.Gaussian.sharpness_exists_compression_power
