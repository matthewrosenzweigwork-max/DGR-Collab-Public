import DGRHS.Gaussian.SharpnessAnnularSquare
import DGRHS.Gaussian.SharpnessAnnularScales

noncomputable section
open MeasureTheory Set Filter BoxIntegral
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sharpness_critical_annular_coefficient (d : ℕ) (s C R : ℝ)
    (hC : 0 < C) (hR : 0 < R) (hcrit : 2*s = (d : ℝ)) :
    ((C*R)^(-s)/(2*s))^2*R^d = C^(-2*s)/(4*s^2) := by
  have hCsq : (C^(-s))^2 = C^(-2*s) := by
    rw [← Real.rpow_mul_natCast hC.le]
    congr 1
    ring
  have hRsq : (R^(-s))^2 = R^(-2*s) := by
    rw [← Real.rpow_mul_natCast hR.le]
    congr 1
    ring
  have hcancel : R^(-2*s)*R^d = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR,
      show -2*s+(d:ℝ) = 0 by linarith,Real.rpow_zero]
  rw [Real.mul_rpow hC.le hR.le,div_pow,mul_pow,hCsq,hRsq,
    show (2*s)^2 = 4*s^2 by ring]
  calc
    _ = (C^(-2*s)/(4*s^2))*(R^(-2*s)*R^d) := by ring
    _ = _ := by rw [hcancel,mul_one]

/-- Actual physical compression HS square grows at least linearly in the
number of dyadic levels at the critical exponent. The source logarithm follows
from the exact dyadic scale; no HS divergence is a premise. -/
theorem sharpness_exists_critical_compression_square (s : ℝ) (hs : 0 < s)
    (hcrit : 2*s = (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ a : ℝ, 0 < a ∧ ∃ z : ι → ℝ, ∃ q : ℝ, ∃ hq : 0 < q, ∃ K : ℝ, 0 < K ∧
      ∀ m : ℕ, 4 ≤ m →
        let P := sharpnessDyadicPartition (sharpnessInitialBox z q hq) m
        let κ := sharpnessCompression (gaussianRieszDensityMeasure ρ)
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
          (sharpnessPartitionAtom ρ a P)
        K*((m-3 : ℕ):ℝ) ≤
          ∫ p,κ p^2 ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) := by
  have ha : 0 < (Fintype.card ι : ℝ)-s := by linarith
  have hd : (0:ℝ) < Fintype.card ι := by linarith
  obtain ⟨a,ha0,z,q,hq,c,hc,hmass,hlocal,hann⟩ :=
    sharpness_exists_uniform_good_annular_mass s hs ha ρ hρm M hM hρ
  let C := (3/2:ℝ)*(Fintype.card ι : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  let K := C^(-2*s)/(4*s^2)*a^2*c
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
  let S := fun j : ℕ => f ⁻¹' (sharpnessAnnularPairs z q (sharpnessAnnularRadius q j) ∩ (G ×ˢ G))
  have hiκ : Integrable (fun p => κ p^2) (μ.prod μ) :=
    (sharpnessCompression_memLp μ _ A (measurableSet_sharpnessPartitionAtom ρ hρm a P)).integrable_sq
  have hf : Measurable f := ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_fst).prodMk
    ((PiLp.volume_preserving_ofLp ι).measurable.comp measurable_snd)
  have hG : MeasurableSet G := (measurableSet_sharpnessGoodUnion ρ hρm a P).preimage
    (PiLp.volume_preserving_toLp ι).measurable
  have hS (j : ℕ) : MeasurableSet (S j) :=
    ((measurableSet_sharpnessAnnularPairs z q _).inter (hG.prod hG)).preimage hf
  have hdisj : Set.Pairwise (↑(Finset.range (m-3))) (fun j k => Disjoint (S j) (S k)) := by
    intro j hj k hk hne
    rw [Set.disjoint_left]
    intro p hpj hpk
    exact (Set.disjoint_left.mp (sharpness_dyadic_annular_pairs_pairwise z hq.le hne)) hpj.1 hpk.1
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m-3)) : K ≤ ∫ p in S j,κ p^2 ∂μ.prod μ := by
    let R := sharpnessAnnularRadius q j
    have hR : 0 < R := sharpnessAnnularRadius_pos hq j
    have hRq : R ≤ q/2 := sharpnessAnnularRadius_le_core hq.le j
    have hjm : j+4 ≤ m := by have hj' := Finset.mem_range.mp hj; omega
    have hδR := sharpness_dyadic_cell_le_annular_quarter hq.le hjm
    have hb := sharpness_compression_annular_square_lower s hs ha ρ hρm M hM hρ a ha0 z q hq
      hmass hlocal m R hR hδR
    have hv := hann m R hR.le hRq
    dsimp only at hb hv
    have hp : 0 ≤ ((C*R)^(-s)/(2*s))^2*a^2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hv hp
    have he : ((C*R)^(-s)/(2*s))^2*a^2*(c*R^Fintype.card ι) = K := by
      calc
        _ = (((C*R)^(-s)/(2*s))^2*R^Fintype.card ι)*a^2*c := by ring
        _ = _ := by rw [sharpness_critical_annular_coefficient _ s C R hC hR hcrit]
    rw [he] at hh
    change K ≤ ∫ p in S j,κ p^2 ∂μ.prod μ
    exact hh.trans hb
  have hU := MeasureTheory.integral_biUnion_finset (μ := μ.prod μ) (f := fun p => κ p^2)
    (Finset.range (m-3)) (fun j _ => hS j) hdisj (fun _ _ => hiκ.restrict)
  change K*((m-3:ℕ):ℝ) ≤ ∫ p,κ p^2 ∂μ.prod μ
  calc
    _ = ∑ j ∈ Finset.range (m-3), K := by simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range (m-3), ∫ p in S j,κ p^2 ∂μ.prod μ := Finset.sum_le_sum hterm
    _ = ∫ p in ⋃ j ∈ Finset.range (m-3), S j,κ p^2 ∂μ.prod μ := hU.symm
    _ ≤ _ := setIntegral_le_integral hiκ (Eventually.of_forall (fun p => sq_nonneg (κ p)))

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_critical_annular_coefficient
#print axioms DGRHS.Gaussian.sharpness_exists_critical_compression_square
#check @DGRHS.Gaussian.sharpness_exists_critical_compression_square
