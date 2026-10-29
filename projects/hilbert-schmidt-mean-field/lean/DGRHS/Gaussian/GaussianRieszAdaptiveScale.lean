import DGRHS.Gaussian.GaussianRieszParticleComparison
import DGRHS.Concentration.MasterSize

/-! Actual adaptive scale arithmetic. The cutoff is capped by one fixed scale;
the lower physical cutoff can only improve the essential norm and cap. -/
noncomputable section
open Real
namespace DGRHS.Gaussian

def gaussianRieszAdaptiveScale (δ A n u d s : ℝ) : ℝ :=
  min δ ((u/(A*n))^(1/(d-s)))

lemma gaussianRieszAdaptiveScale_pos_le (δ A n u d s : ℝ) (hδ : 0 < δ)
    (hA : 0 < A) (hn : 0 < n) (hu : 0 < u) :
    0 < gaussianRieszAdaptiveScale δ A n u d s ∧
      gaussianRieszAdaptiveScale δ A n u d s ≤ δ := by
  exact ⟨lt_min hδ (Real.rpow_pos_of_pos (div_pos hu (mul_pos hA hn)) _),min_le_left _ _⟩

lemma gaussianRieszAdaptiveScale_power_le (δ A n u d s : ℝ) (hδ : 0 < δ)
    (hA : 0 < A) (hn : 0 < n) (hu : 0 < u) (hd : 0 < d-s) :
    (gaussianRieszAdaptiveScale δ A n u d s)^(d-s) ≤ u/(A*n) := by
  have hp := (gaussianRieszAdaptiveScale_pos_le δ A n u d s hδ hA hn hu).1
  calc
    _ ≤ ((u/(A*n))^(1/(d-s)))^(d-s) :=
      Real.rpow_le_rpow hp.le (min_le_right _ _) hd.le
    _ = u/(A*n) := by
      rw [← Real.rpow_mul (div_pos hu (mul_pos hA hn)).le]
      have he : (1/(d-s))*(d-s)=1 := by field_simp
      rw [he,Real.rpow_one]

lemma gaussianRieszAdaptiveScale_inverse_power_le (δ A n u d s η : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) (hn : 0 < n) (hu : 0 < u)
    (hs : 0 < s) (hd : 0 < d-s) :
    (max (gaussianRieszAdaptiveScale δ A n u d s) η)^(-s) ≤
      δ^(-s)+A^(s/(d-s))*(n/u)^(s/(d-s)) := by
  let t := (u/(A*n))^(1/(d-s))
  have ht : 0 < t := Real.rpow_pos_of_pos (div_pos hu (mul_pos hA hn)) _
  have hpow : t^(-s)=A^(s/(d-s))*(n/u)^(s/(d-s)) := by
    unfold t
    rw [← Real.rpow_mul (div_pos hu (mul_pos hA hn)).le]
    have he : (1/(d-s))*(-s)= -(s/(d-s)) := by ring
    rw [he,Real.rpow_neg_eq_inv_rpow]
    have hi : (u/(A*n))⁻¹=A*(n/u) := by field_simp <;> ring
    rw [hi,Real.mul_rpow hA.le (div_pos hn hu).le]
  have hp := (gaussianRieszAdaptiveScale_pos_le δ A n u d s hδ hA hn hu).1
  calc
    _ ≤ (gaussianRieszAdaptiveScale δ A n u d s)^(-s) :=
      Real.rpow_le_rpow_of_nonpos hp (le_max_left _ _) (by linarith)
    _ ≤ δ^(-s)+t^(-s) := by
      unfold gaussianRieszAdaptiveScale
      by_cases h : δ ≤ t
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (Real.rpow_nonneg ht.le _)
      · rw [min_eq_right (le_of_not_ge h)]
        exact le_add_of_nonneg_left (Real.rpow_nonneg hδ.le _)
    _ = _ := by rw [hpow]

lemma gaussianRieszAdaptive_exponents (d s : ℝ) (hs : 0 < s) (ha : s < d/2) :
    0 < s/(d-s) ∧ s/(d-s) < 1 ∧
      2*((s/(d-s))/(1+s/(d-s)))=2*s/d := by
  have hd : 0 < d-s := by linarith
  have hd0 : 0 < d := by linarith
  refine ⟨div_pos hs hd,(div_lt_one hd).2 (by linarith),?_⟩
  field_simp
  ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszAdaptiveScale
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveScale

#check DGRHS.Gaussian.gaussianRieszAdaptiveScale_pos_le
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveScale_pos_le

#check DGRHS.Gaussian.gaussianRieszAdaptiveScale_power_le
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveScale_power_le

#check DGRHS.Gaussian.gaussianRieszAdaptiveScale_inverse_power_le
#print axioms DGRHS.Gaussian.gaussianRieszAdaptiveScale_inverse_power_le

#check DGRHS.Gaussian.gaussianRieszAdaptive_exponents
#print axioms DGRHS.Gaussian.gaussianRieszAdaptive_exponents
