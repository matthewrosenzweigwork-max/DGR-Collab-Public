/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ElevenEuclideanMass
import DGRHS.Gaussian.D11Imported.LatticeMajorant

/-! A summable majorant for the exact periodization, uniform on each bounded
cube. No truncation or normalization is introduced into the profile. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven
open DGRHS.Gaussian.D11Imported.LatticeMajorant

lemma translated_profile_majorant (y : Fin 11 → ℝ) (n : Frequency 11) {R : ℝ}
    (hR : 0 ≤ R) (hy : ∀ i, |y i| ≤ R) :
    euclideanProfile (fun i => y i + (n i : ℝ)) ≤
      ((5:ℝ)^11 * (122880 / Real.pi^6) * (2+22*R^2)^11) * productMajorant n := by
  let S : ℝ := ∑ i : Fin 11, (y i + (n i : ℝ))^2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hN : radiusSq n ≤ 2*S+22*R^2 := by
    have hterm (i : Fin 11) : (n i : ℝ)^2 ≤ 2*(y i+(n i : ℝ))^2+2*R^2 := by
      have hi : (y i)^2 ≤ R^2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr (hy i)
      nlinarith [sq_nonneg (y i + (y i+(n i : ℝ)))]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 11))) => hterm i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at h
    change (∑ i, (n i:ℝ)^2) ≤ 2*(∑ i, (y i+(n i:ℝ))^2)+22*R^2
    linarith
  have hA : 0 < 1+radiusSq n := by have := radiusSq_nonneg n; positivity
  have hB : 0 ≤ 2+22*R^2 := by positivity
  have hC : 0 < 1+25*S := by positivity
  have hinv : (1+25*S)⁻¹ ≤ (2+22*R^2)*(1+radiusSq n)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hC hA).2
    nlinarith [mul_nonneg (sq_nonneg R) hS]
  have hp := pow_le_pow_left₀ (inv_nonneg.mpr hC.le) hinv 11
  rw [mul_pow] at hp
  have hmajor := shifted_radial_inv_le_product n
  have ht := hp.trans (mul_le_mul_of_nonneg_left hmajor (pow_nonneg hB 11))
  have hcoef : 0 ≤ (5:ℝ)^11 * (122880 / Real.pi^6) := by positivity
  have h := mul_le_mul_of_nonneg_left ht hcoef
  simpa only [euclideanProfile, zpow_neg, zpow_ofNat, zpow_natCast, inv_pow, S, mul_assoc] using h

lemma translated_profile_summable (y : Fin 11 → ℝ) :
    Summable (fun n : Frequency 11 => euclideanProfile (fun i => y i+(n i:ℝ))) := by
  apply Summable.of_nonneg_of_le
    (fun n => (euclideanProfile_pos _).le)
    (fun n => translated_profile_majorant y n (norm_nonneg _) (fun i => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm y i))
    ((summable_productMajorant 11).mul_left _)

lemma periodizedProfile_summable (x : Torus 11) :
    Summable (fun n : Frequency 11 => euclideanProfile (fun i => representative (x i)+(n i:ℝ))) :=
  translated_profile_summable _

lemma periodizedProfile_pos (x : Torus 11) : 0 < periodizedProfile x := by
  exact (euclideanProfile_pos (fun i => representative (x i)+((0 : Frequency 11) i : ℝ))).trans_le
    ((periodizedProfile_summable x).le_tsum (0 : Frequency 11)
      (fun n _ => (euclideanProfile_pos _).le))

#print axioms periodizedProfile_summable
#print axioms periodizedProfile_pos
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
