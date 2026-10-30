import DGPS.Frontier.STR029.T09
import DGPS.Examples.PolynomialFiniteProfileIH
import DGPS.Examples.PolynomialSpeciesRangeHalfTurn

/-! Exact physical normalization of the genuine cos-one finite-profile
information. The reference tilt is independently zero; selected-root transport
and the nonlocal terms are separate steps. -/

noncomputable section
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem profile_argument (A B C D h t : ℝ) :
    h * Real.cos t + uFun_STR02945 A B C D 0 0 h t =
      expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t := by
  unfold uFun_STR02945 expArg_STR02944 pFun_STR02945
  ring

private theorem partition_eq (A B C D h : ℝ) (u : PeriodicC2_STR02969)
    (hu : ∀ t, u.val t = uFun_STR02945 A B C D 0 0 h t) :
    Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, 0)) + e0_STR02955 u) =
      normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h := by
  rw [Z_eq_meanT_STR02954, meanT_eq_normInt_STR02909]
  apply normInt_congr_STR02945
  intro t
  simp only [zero_mul, zero_add, PeriodicHolder_STR02968.val_add, Pi.add_apply,
    e0_val_STR02955, polynomialRangeLogWeight_val_explicit, zero_mul, sub_zero, hu]
  rw [profile_argument]

private theorem reference_partition_eq (h : ℝ) :
    Z_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (h, 0))) =
      normalizer_STR02944 Real.cos (fun _ => 0) h := by
  rw [Z_eq_meanT_STR02954, meanT_eq_normInt_STR02909]
  apply normInt_congr_STR02945
  intro t
  simp only [zero_mul, zero_add, e0_val_STR02955, polynomialRangeLogWeight_val_explicit,
    sub_zero, expArg_STR02944, mul_zero, add_zero]

/-- Pointwise normalized-density identification with the actual independent
reference chart. The premise identifies a concrete finite Fourier profile,
not an entropy, information or Euler conclusion. -/
theorem polynomialFiniteProfile_core_density (A B C D h : ℝ) (u : PeriodicC2_STR02969)
    (hu : ∀ t, u.val t = uFun_STR02945 A B C D 0 0 h t) (t : ℝ) :
    (eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, 0))) u).val t =
      polynomialFiniteProfileDensity A B C D h t := by
  rw [eulerDensity, rho_val_STR02954]
  unfold rhoT_STR02901 polynomialFiniteProfileDensity
  simp only [zero_mul, zero_add, PeriodicHolder_STR02968.val_add, Pi.add_apply,
    e0_val_STR02955, polynomialRangeLogWeight_val_explicit, zero_mul, sub_zero, hu]
  simp_rw [profile_argument]
  rw [meanT_eq_normInt_STR02909]
  rfl

/-- Exact angular-to-physical information and exact relative entropy. Both
partition functions are proved positive internally before the logarithms are
identified. No nonlocal or selected-root claim is included. -/
theorem polynomialFiniteProfile_core_information (A B C D h : ℝ)
    (u : PeriodicC2_STR02969)
    (hu : ∀ t, u.val t = uFun_STR02945 A B C D 0 0 h t) :
    eulerFisher (e0_STR02955 (polynomialRangeLogWeight (h, 0))) u =
      DGPS.Circle.AngularNormalization.a0 * polynomialFiniteProfileFisher A B C D h ∧
    eulerEntropy (e0_STR02955 (polynomialRangeLogWeight (h, 0))) u =
      polynomialFiniteProfileEntropy A B C D h := by
  have huFun : u.val = uFun_STR02945 A B C D 0 0 h := funext hu
  have hZ := partition_eq A B C D h u hu
  have hZb := reference_partition_eq h
  have hZpos : 0 < normalizer_STR02944 (pFun_STR02945 (1 + A) B)
      (qFun_STR02945 C D 0 0) h := by
    rw [← hZ]
    exact Z_pos_STR02954 _
  have hZbpos : 0 < normalizer_STR02944 Real.cos (fun _ => 0) h := by
    rw [← hZb]
    exact Z_pos_STR02954 _
  constructor
  · unfold eulerFisher eulerMean polynomialFiniteProfileFisher
    rw [meanCLM_apply_STR02954, meanT_eq_normInt_STR02909]
    congr 1
    apply normInt_congr_STR02945
    intro t
    simp only [val_mul_STR02954, Pi.mul_apply, e1_val_STR02955,
      polynomialFiniteProfile_core_density A B C D h u hu, huFun]
    ring
  · rw [polynomialFiniteProfileEntropy_eq A B C D h hZpos hZbpos]
    unfold eulerEntropy eulerMean
    rw [meanCLM_apply_STR02954, meanT_eq_normInt_STR02909, hZ, hZb]
    congr 2
    have he : (fun t => (e0_STR02955 u *
        eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, 0))) u).val t) =
        fun t => (normalizer_STR02944 (pFun_STR02945 (1 + A) B)
          (qFun_STR02945 C D 0 0) h)⁻¹ *
            (uFun_STR02945 A B C D 0 0 h t *
              Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B)
                (qFun_STR02945 C D 0 0) h t)) := by
      funext t
      simp only [val_mul_STR02954, Pi.mul_apply, e0_val_STR02955,
        polynomialFiniteProfile_core_density A B C D h u hu, hu]
      unfold polynomialFiniteProfileDensity
      ring
    change (e0_STR02955 u * eulerDensity (e0_STR02955 (polynomialRangeLogWeight (h, 0))) u).val = _ at he
    rw [he, normInt_mul_const_STR02933, div_eq_inv_mul]

end DGPS.Examples.PolynomialSpecies
