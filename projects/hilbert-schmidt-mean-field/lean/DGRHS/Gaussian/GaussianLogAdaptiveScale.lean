import DGRHS.Gaussian.GaussianLogScaleSplit
import DGRHS.Concentration.MasterSize

/-! Genuine logarithmic adaptive scale and its common
cap/essential size arithmetic. Beta is never divided by, so beta=0 is included. -/
noncomputable section
open Real
namespace DGRHS.Gaussian

def gaussianLogAdaptiveScale (δ A β n u d : ℝ) : ℝ :=
  min δ ((u/(A*(1+β*n)))^(1/d))

lemma gaussianLogAdaptiveScale_pos_le (δ A β n u d : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hu : 0 < u) :
    0 < gaussianLogAdaptiveScale δ A β n u d ∧ gaussianLogAdaptiveScale δ A β n u d ≤ δ := by
  have hz : 0 < 1+β*n := by positivity
  exact ⟨lt_min hδ (Real.rpow_pos_of_pos (div_pos hu (mul_pos hA hz)) _),min_le_left _ _⟩

lemma gaussianLogAdaptiveScale_power_le (δ A β n u d : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hu : 0 < u) (hd : 0 < d) :
    (gaussianLogAdaptiveScale δ A β n u d)^d ≤ u/(A*(1+β*n)) := by
  have hp := (gaussianLogAdaptiveScale_pos_le δ A β n u d hδ hA hβ hn hu).1
  have hz : 0 < 1+β*n := by positivity
  calc
    _ ≤ ((u/(A*(1+β*n)))^(1/d))^d := Real.rpow_le_rpow hp.le (min_le_right _ _) hd.le
    _ = u/(A*(1+β*n)) := by
      rw [← Real.rpow_mul (div_pos hu (mul_pos hA hz)).le]
      have he : (1/d)*d = 1 := by field_simp
      rw [he,Real.rpow_one]

lemma gaussianLogAdaptiveScale_near_error_le (δ A β n u d C : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hu : 0 < u) (hd : 0 < d)
    (hC : 0 ≤ C) (hAC : 8*C ≤ A) :
    β*n*C*(gaussianLogAdaptiveScale δ A β n u d)^d ≤ u/8 := by
  have hp := gaussianLogAdaptiveScale_power_le δ A β n u d hδ hA hβ hn hu hd
  have hz : 0 < A*(1+β*n) := by positivity
  have hc : 8*β*n*C ≤ A*(1+β*n) := by
    have h := mul_le_mul_of_nonneg_left hAC (mul_nonneg hβ hn)
    nlinarith
  have hdiv : (8*β*n*C)/(A*(1+β*n)) ≤ 1 := (div_le_iff₀ hz).mpr (by simpa using hc)
  have h1 := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 8*β*n*C)
  have h2 := mul_le_mul_of_nonneg_right hdiv hu.le
  have he : (8*β*n*C)*(u/(A*(1+β*n))) = ((8*β*n*C)/(A*(1+β*n)))*u := by ring
  rw [he] at h1
  nlinarith

lemma gaussianLogAdaptiveScale_log_mass_le (δ A β n u d : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 1 ≤ n) (hu : 0 < u) (hd : 0 < d) :
    Real.log (δ/gaussianLogAdaptiveScale δ A β n u d) ≤
      (2/d)*(A*(1+β))^(1/2 : ℝ)*(n/u)^(1/2 : ℝ) := by
  let t := (u/(A*(1+β*n)))^(1/d)
  have hn0 : 0 ≤ n := by linarith
  have hz : 0 < u/(A*(1+β*n)) := by positivity
  have ht : 0 < t := Real.rpow_pos_of_pos hz _
  by_cases hcap : δ ≤ t
  · unfold gaussianLogAdaptiveScale
    rw [min_eq_left hcap,div_self hδ.ne',Real.log_one]
    positivity
  · have hα : gaussianLogAdaptiveScale δ A β n u d = t := min_eq_right (le_of_not_ge hcap)
    rw [hα]
    have hr : (δ/t)^(d/2) ≤ (1/t)^(d/2) :=
      Real.rpow_le_rpow (div_pos hδ ht).le (div_le_div_of_nonneg_right hδ1 ht.le) (by positivity)
    have hrpow : (1/t)^(d/2) = (A*(1+β*n)/u)^(1/2 : ℝ) := by
      rw [one_div,← Real.rpow_neg_eq_inv_rpow]
      unfold t
      rw [← Real.rpow_mul hz.le]
      have he : (1/d)*(-(d/2)) = -(1/2 : ℝ) := by field_simp <;> ring
      rw [he,Real.rpow_neg_eq_inv_rpow]
      congr 1
      field_simp <;> ring
    have hbase : A*(1+β*n)/u ≤ A*(1+β)*(n/u) := by
      have h : 1+β*n ≤ (1+β)*n := by nlinarith
      have hm := mul_le_mul_of_nonneg_left h hA.le
      calc
        _ ≤ (A*((1+β)*n))/u := div_le_div_of_nonneg_right hm hu.le
        _ = _ := by ring
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ A*(1+β*n)/u) hbase (by norm_num : (0 : ℝ) ≤ 1/2)
    rw [Real.mul_rpow (by positivity : 0 ≤ A*(1+β)) (by positivity : 0 ≤ n/u)] at hpow
    have hlog := Real.log_le_rpow_div (div_pos hδ ht).le (div_pos hd (by norm_num : (0 : ℝ) < 2))
    have hden : 0 ≤ 1/(d/2) := by positivity
    have hcombined : (δ/t)^(d/2) ≤ (A*(1+β))^(1/2 : ℝ)*(n/u)^(1/2 : ℝ) :=
      hr.trans (by rw [hrpow]; exact hpow)
    have hb := mul_le_mul_of_nonneg_left hcombined hden
    have he : (δ/t)^(d/2)/(d/2) = (1/(d/2))*(δ/t)^(d/2) := by ring
    rw [he] at hlog
    have he2 : 1/(d/2) = 2/d := by ring
    exact hlog.trans (by simpa only [he2,mul_assoc] using hb)

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLogAdaptiveScale
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveScale
#check DGRHS.Gaussian.gaussianLogAdaptiveScale_pos_le
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveScale_pos_le
#check DGRHS.Gaussian.gaussianLogAdaptiveScale_power_le
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveScale_power_le
#check DGRHS.Gaussian.gaussianLogAdaptiveScale_near_error_le
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveScale_near_error_le
#check DGRHS.Gaussian.gaussianLogAdaptiveScale_log_mass_le
#print axioms DGRHS.Gaussian.gaussianLogAdaptiveScale_log_mass_le
