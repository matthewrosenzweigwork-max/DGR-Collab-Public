import DGRHS.Gaussian.SharpnessAnnulusGeometry

noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def sharpnessAnnularRadius (q : ℝ) (j : ℕ) : ℝ := q/(2:ℝ)^(j+1)

lemma sharpnessAnnularRadius_pos {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 < sharpnessAnnularRadius q j := by unfold sharpnessAnnularRadius; positivity

lemma sharpnessAnnularRadius_le_core {q : ℝ} (hq : 0 ≤ q) (j : ℕ) :
    sharpnessAnnularRadius q j ≤ q/2 := by
  have hp : (2:ℝ) ≤ 2^(j+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 1 ≤ j+1)
  exact div_le_div_of_nonneg_left hq (by norm_num) hp

lemma sharpnessAnnularRadius_separated {q : ℝ} (hq : 0 ≤ q) {j k : ℕ} (hjk : j < k) :
    sharpnessAnnularRadius q k ≤ sharpnessAnnularRadius q j/2 := by
  unfold sharpnessAnnularRadius
  rw [div_div]
  apply div_le_div_of_nonneg_left hq (by positivity)
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show j+2 ≤ k+1 by omega)
  have he : (2:ℝ)^(j+2) = 2^(j+1)*2 := by
    rw [show j+2 = (j+1)+1 by omega,pow_succ]
  rwa [he] at hp

lemma sharpness_dyadic_cell_le_annular_quarter {q : ℝ} (hq : 0 ≤ q)
    {m j : ℕ} (hjm : j+4 ≤ m) :
    (2*q)/(2:ℝ)^m ≤ sharpnessAnnularRadius q j/4 := by
  unfold sharpnessAnnularRadius
  rw [div_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjm
  have he : (2:ℝ)^(j+4) = 8*2^(j+1) := by
    rw [show j+4 = (j+1)+3 by omega,pow_add]
    norm_num
    <;> ring
  rw [he] at hp
  nlinarith [mul_le_mul_of_nonneg_left hp hq]

lemma sharpnessAnnularPairs_disjoint (z : ι → ℝ) (q : ℝ) {R T : ℝ}
    (hTR : T ≤ R/2) : Disjoint (sharpnessAnnularPairs z q R) (sharpnessAnnularPairs z q T) := by
  rw [Set.disjoint_left]
  intro p hpR hpT
  apply hpR.2.2
  exact le_trans hpT.2.1 hTR

lemma sharpness_dyadic_annular_pairs_pairwise (z : ι → ℝ) {q : ℝ} (hq : 0 ≤ q) :
    Pairwise (fun j k : ℕ => Disjoint (sharpnessAnnularPairs z q (sharpnessAnnularRadius q j))
      (sharpnessAnnularPairs z q (sharpnessAnnularRadius q k))) := by
  intro j k hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · exact sharpnessAnnularPairs_disjoint z q (sharpnessAnnularRadius_separated hq hjk)
  · exact (sharpnessAnnularPairs_disjoint z q (sharpnessAnnularRadius_separated hq hkj)).symm

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_dyadic_cell_le_annular_quarter
#print axioms DGRHS.Gaussian.sharpness_dyadic_annular_pairs_pairwise
#check @DGRHS.Gaussian.sharpness_dyadic_cell_le_annular_quarter
