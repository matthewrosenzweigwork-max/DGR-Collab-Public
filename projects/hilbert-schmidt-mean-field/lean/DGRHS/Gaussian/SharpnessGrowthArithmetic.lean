import DGRHS.Gaussian.SharpnessScaleArithmetic

noncomputable section
namespace DGRHS.Gaussian

/-- Critical HS-level growth becomes a positive power of the logarithmic
scale variable. Constants and positivity are explicit. -/
theorem sharpness_critical_scale_growth (b v t τ : ℝ)
    (hb : 1 < b) (hv : 0 < v) (ht : 0 < t) (hτ : 0 < τ) :
    ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧ ∀ m : ℕ,3 ≤ m →
      ∀ X : ℝ,0 ≤ X → t*X < b*(v*b^m) →
        C*X^c ≤ Real.exp (τ*((m-3:ℕ):ℝ)) := by
  let c := τ/Real.log b
  let C := Real.exp (-3*τ)*(t/(b*v))^c
  have hlog : 0 < Real.log b := Real.log_pos hb
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨c,hc,C,hC,?_⟩
  intro m hm X hX hscale
  have hbase : t/(b*v)*X ≤ b^m := by
    have hh : t/(b*v)*X = (t*X)/(b*v) := by ring
    rw [hh]
    exact (div_le_iff₀ (by positivity : 0 < b*v)).mpr (by nlinarith)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ t/(b*v)*X) hbase hc.le
  rw [Real.mul_rpow (by positivity : 0 ≤ t/(b*v)) hX] at hpow
  have he : (b^m)^c = Real.exp (τ*(m:ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity : 0 < b^m),Real.log_pow]
    congr 1
    dsimp [c]
    field_simp [hlog.ne']
  rw [he] at hpow
  have hecast : ((m-3:ℕ):ℝ) = (m:ℝ)-3 := by
    rw [Nat.cast_sub hm]
    norm_num
  calc
    C*X^c ≤ Real.exp (-3*τ)*Real.exp (τ*(m:ℝ)) := by
      dsimp [C]
      convert mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _) using 1 <;> ring
    _ = _ := by rw [←Real.exp_add,hecast]; congr 1; ring

/-- Supercritical physical square growth in the inverse-s scale gives the
source exponent 2-d/s, with no desired asymptotic premise. -/
lemma sharpness_supercritical_scale_power (L s d : ℝ) (hL : 0 < L) (hs : 0 < s) (m : ℕ) :
    ((L/(2:ℝ)^m)^(-s))^(2-d/s) = (L/(2:ℝ)^m)^(d-2*s) := by
  rw [←Real.rpow_mul (by positivity : 0 ≤ L/(2:ℝ)^m)]
  congr 1
  field_simp [hs.ne']
  <;> ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_critical_scale_growth
#print axioms DGRHS.Gaussian.sharpness_supercritical_scale_power
