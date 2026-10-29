import DGPS.Circle.BesselMoments

/-!
# EX009: angular Fourier moments for the quasimode Gram
-/

open MeasureTheory Real
open DGPS.Circle.AngularNormalization

namespace DGPS.Circle.FirstClusterFourierEX009

noncomputable def cosMode_EX009 (n : ℤ) : AngCircle → ℝ :=
  Function.Periodic.lift (f := fun x : ℝ => Real.cos ((n : ℝ) * x)) (c := 2 * π) (by
    intro x
    change Real.cos ((n : ℝ) * (x + 2 * π)) = Real.cos ((n : ℝ) * x)
    rw [show (n : ℝ) * (x + 2 * π) = (n : ℝ) * x + (n : ℝ) * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi])

noncomputable def sinMode_EX009 (n : ℤ) : AngCircle → ℝ :=
  Function.Periodic.lift (f := fun x : ℝ => Real.sin ((n : ℝ) * x)) (c := 2 * π) (by
    intro x
    change Real.sin ((n : ℝ) * (x + 2 * π)) = Real.sin ((n : ℝ) * x)
    rw [show (n : ℝ) * (x + 2 * π) = (n : ℝ) * x + (n : ℝ) * (2 * π) by ring,
      Real.sin_add_int_mul_two_pi])

theorem cosMode_coe_EX009 (n : ℤ) (x : ℝ) :
    cosMode_EX009 n (x : AngCircle) = Real.cos ((n : ℝ) * x) := rfl

theorem sinMode_coe_EX009 (n : ℤ) (x : ℝ) :
    sinMode_EX009 n (x : AngCircle) = Real.sin ((n : ℝ) * x) := rfl

theorem continuous_cosMode_EX009 (n : ℤ) : Continuous (cosMode_EX009 n) := by
  unfold cosMode_EX009
  refine Continuous.quotient_lift (by fun_prop) ?_

theorem continuous_sinMode_EX009 (n : ℤ) : Continuous (sinMode_EX009 n) := by
  unfold sinMode_EX009
  refine Continuous.quotient_lift (by fun_prop) ?_

theorem cosMode_zero_EX009 : cosMode_EX009 0 = fun _ => 1 := by
  ext theta
  induction theta using QuotientAddGroup.induction_on with
  | H x => rw [cosMode_coe_EX009]; simp

theorem sinMode_zero_EX009 : sinMode_EX009 0 = fun _ => 0 := by
  ext theta
  induction theta using QuotientAddGroup.induction_on with
  | H x => rw [sinMode_coe_EX009]; simp

theorem abs_cosMode_EX009 (n : ℤ) (theta : AngCircle) : |cosMode_EX009 n theta| ≤ 1 := by
  induction theta using QuotientAddGroup.induction_on with
  | H x => rw [cosMode_coe_EX009]; exact Real.abs_cos_le_one _

theorem abs_sinMode_EX009 (n : ℤ) (theta : AngCircle) : |sinMode_EX009 n theta| ≤ 1 := by
  induction theta using QuotientAddGroup.induction_on with
  | H x => rw [sinMode_coe_EX009]; exact Real.abs_sin_le_one _

theorem integrable_cosMode_EX009 (n : ℤ) : Integrable (cosMode_EX009 n) angHaar :=
  DGPS.Circle.BesselMoments.integrable_cont (continuous_cosMode_EX009 n) 1
    (abs_cosMode_EX009 n)

theorem integrable_sinMode_EX009 (n : ℤ) : Integrable (sinMode_EX009 n) angHaar :=
  DGPS.Circle.BesselMoments.integrable_cont (continuous_sinMode_EX009 n) 1
    (abs_sinMode_EX009 n)

theorem cosMode_mean_EX009 (n : ℤ) :
    ∫ theta, cosMode_EX009 n theta ∂angHaar = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst n
    rw [cosMode_zero_EX009]
    simp
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [DGPS.Circle.BesselMoments.integral_ang
    (fun x => Real.cos ((n : ℝ) * x)) (cosMode_EX009 n) (cosMode_coe_EX009 n)]
  have hd (x : ℝ) :
      HasDerivAt (fun y => Real.sin ((n : ℝ) * y) / (n : ℝ))
        (Real.cos ((n : ℝ) * x)) x := by
    have ht : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hh := ((hasDerivAt_sin ((n : ℝ) * x)).comp x ht).div_const (n : ℝ)
    change HasDerivAt (fun y => Real.sin ((n : ℝ) * y) / (n : ℝ))
      (Real.cos ((n : ℝ) * x) * (n : ℝ) / (n : ℝ)) x at hh
    convert hh using 1
    field_simp [hnr]
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * π) (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => Real.cos ((n : ℝ) * x))).intervalIntegrable _ _)
  have hs : Real.sin ((n : ℝ) * (2 * π)) = 0 := by
    calc
      Real.sin ((n : ℝ) * (2 * π)) =
          Real.sin (((2 * n : ℤ) : ℝ) * π) := by
            congr 1
            push_cast
            ring
      _ = 0 := Real.sin_int_mul_pi (2 * n)
  rw [hI, hs]
  simp

theorem sinMode_mean_EX009 (n : ℤ) :
    ∫ theta, sinMode_EX009 n theta ∂angHaar = 0 := by
  by_cases hn : n = 0
  · subst n
    rw [sinMode_zero_EX009]
    simp
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [DGPS.Circle.BesselMoments.integral_ang
    (fun x => Real.sin ((n : ℝ) * x)) (sinMode_EX009 n) (sinMode_coe_EX009 n)]
  have hd (x : ℝ) :
      HasDerivAt (fun y => -Real.cos ((n : ℝ) * y) / (n : ℝ))
        (Real.sin ((n : ℝ) * x)) x := by
    have ht : HasDerivAt (fun y : ℝ => (n : ℝ) * y) (n : ℝ) x := by
      simpa using (hasDerivAt_id x).const_mul (n : ℝ)
    have hh := (((hasDerivAt_cos ((n : ℝ) * x)).comp x ht).neg).div_const (n : ℝ)
    change HasDerivAt (fun y => -Real.cos ((n : ℝ) * y) / (n : ℝ))
      (-(-Real.sin ((n : ℝ) * x) * (n : ℝ)) / (n : ℝ)) x at hh
    convert hh using 1
    field_simp [hnr]
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 2 * π) (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => Real.sin ((n : ℝ) * x))).intervalIntegrable _ _)
  rw [hI, Real.cos_int_mul_two_pi]
  simp

theorem cosMode_product_EX009 (m n : ℤ) (theta : AngCircle) :
    2 * (cosMode_EX009 m theta * cosMode_EX009 n theta) =
      cosMode_EX009 (m + n) theta + cosMode_EX009 (m - n) theta := by
  induction theta using QuotientAddGroup.induction_on with
  | H x =>
    simp only [cosMode_coe_EX009, Int.cast_add, Int.cast_sub, add_mul, sub_mul,
      Real.cos_add, Real.cos_sub]
    ring

theorem sinMode_product_EX009 (m n : ℤ) (theta : AngCircle) :
    2 * (sinMode_EX009 m theta * sinMode_EX009 n theta) =
      cosMode_EX009 (m - n) theta - cosMode_EX009 (m + n) theta := by
  induction theta using QuotientAddGroup.induction_on with
  | H x =>
    simp only [sinMode_coe_EX009, cosMode_coe_EX009, Int.cast_add, Int.cast_sub,
      add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring

theorem sinMode_cosMode_product_EX009 (m n : ℤ) (theta : AngCircle) :
    2 * (sinMode_EX009 m theta * cosMode_EX009 n theta) =
      sinMode_EX009 (m + n) theta + sinMode_EX009 (m - n) theta := by
  induction theta using QuotientAddGroup.induction_on with
  | H x =>
    simp only [sinMode_coe_EX009, cosMode_coe_EX009, Int.cast_add, Int.cast_sub,
      add_mul, sub_mul, Real.sin_add, Real.sin_sub]
    ring

theorem cosMode_inner_EX009 (m n : ℤ) :
    ∫ theta, cosMode_EX009 m theta * cosMode_EX009 n theta ∂angHaar =
      ((if m + n = 0 then (1 : ℝ) else 0) + (if m - n = 0 then 1 else 0)) / 2 := by
  have he := congrArg (fun f : AngCircle → ℝ => ∫ theta, f theta ∂angHaar)
    (funext (cosMode_product_EX009 m n))
  rw [integral_const_mul, integral_add (integrable_cosMode_EX009 _) (integrable_cosMode_EX009 _),
    cosMode_mean_EX009, cosMode_mean_EX009] at he
  linarith

theorem sinMode_inner_EX009 (m n : ℤ) :
    ∫ theta, sinMode_EX009 m theta * sinMode_EX009 n theta ∂angHaar =
      ((if m - n = 0 then (1 : ℝ) else 0) - (if m + n = 0 then 1 else 0)) / 2 := by
  have he := congrArg (fun f : AngCircle → ℝ => ∫ theta, f theta ∂angHaar)
    (funext (sinMode_product_EX009 m n))
  rw [integral_const_mul, integral_sub (integrable_cosMode_EX009 _) (integrable_cosMode_EX009 _),
    cosMode_mean_EX009, cosMode_mean_EX009] at he
  linarith

theorem sinMode_cosMode_inner_EX009 (m n : ℤ) :
    ∫ theta, sinMode_EX009 m theta * cosMode_EX009 n theta ∂angHaar = 0 := by
  have he := congrArg (fun f : AngCircle → ℝ => ∫ theta, f theta ∂angHaar)
    (funext (sinMode_cosMode_product_EX009 m n))
  rw [integral_const_mul, integral_add (integrable_sinMode_EX009 _) (integrable_sinMode_EX009 _),
    sinMode_mean_EX009, sinMode_mean_EX009] at he
  linarith


theorem cosMode_sinMode_inner_EX009 (m n : ℤ) :
    ∫ theta, cosMode_EX009 m theta * sinMode_EX009 n theta ∂angHaar = 0 := by
  have he : (fun theta => cosMode_EX009 m theta * sinMode_EX009 n theta) =
      (fun theta => sinMode_EX009 n theta * cosMode_EX009 m theta) := by
    ext theta
    ring
  rw [he, sinMode_cosMode_inner_EX009]

/-- Real Haar modes through frequency3, with the constant mode first. -/
noncomputable def basis_EX009 : Fin 7 → AngCircle → ℝ :=
  ![fun _ => 1, cosMode_EX009 1, sinMode_EX009 1, cosMode_EX009 2,
    sinMode_EX009 2, cosMode_EX009 3, sinMode_EX009 3]

theorem continuous_basis_EX009 (i : Fin 7) : Continuous (basis_EX009 i) := by
  fin_cases i
  · exact continuous_const
  · exact continuous_cosMode_EX009 1
  · exact continuous_sinMode_EX009 1
  · exact continuous_cosMode_EX009 2
  · exact continuous_sinMode_EX009 2
  · exact continuous_cosMode_EX009 3
  · exact continuous_sinMode_EX009 3

theorem abs_basis_EX009 (i : Fin 7) (theta : AngCircle) : |basis_EX009 i theta| ≤ 1 := by
  fin_cases i
  · norm_num [basis_EX009]
  · exact abs_cosMode_EX009 1 theta
  · exact abs_sinMode_EX009 1 theta
  · exact abs_cosMode_EX009 2 theta
  · exact abs_sinMode_EX009 2 theta
  · exact abs_cosMode_EX009 3 theta
  · exact abs_sinMode_EX009 3 theta

theorem memLp_basis_EX009 (i : Fin 7) : MemLp (basis_EX009 i) 2 angHaar :=
  MemLp.of_bound (continuous_basis_EX009 i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun theta => by simpa using abs_basis_EX009 i theta)

theorem basis_inner_EX009 (i j : Fin 7) :
    ∫ theta, basis_EX009 i theta * basis_EX009 j theta ∂angHaar =
      if i = j then (if i = 0 then 1 else 1 / 2) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [basis_EX009, cosMode_inner_EX009, sinMode_inner_EX009,
      cosMode_sinMode_inner_EX009, sinMode_cosMode_inner_EX009,
      cosMode_mean_EX009, sinMode_mean_EX009]

noncomputable def angularPolynomial_EX009 (a : Fin 7 → ℝ) (theta : AngCircle) : ℝ :=
  ∑ i, a i * basis_EX009 i theta

theorem angularPolynomial_inner_EX009 (a b : Fin 7 → ℝ) :
    ∫ theta, angularPolynomial_EX009 a theta * angularPolynomial_EX009 b theta ∂angHaar =
      ∑ i, a i * b i * (if i = 0 then 1 else 1 / 2) := by
  have hfun : (fun theta => angularPolynomial_EX009 a theta * angularPolynomial_EX009 b theta) =
      (fun theta => ∑ i, ∑ j, (a i * b j) * (basis_EX009 i theta * basis_EX009 j theta)) := by
    ext theta
    unfold angularPolynomial_EX009
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun]
  have hint (i j : Fin 7) : Integrable
      (fun theta => (a i * b j) * (basis_EX009 i theta * basis_EX009 j theta)) angHaar :=
    ((memLp_basis_EX009 i).integrable_mul (memLp_basis_EX009 j)).const_mul _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  calc
    ∑ i, ∫ theta, ∑ j, (a i * b j) * (basis_EX009 i theta * basis_EX009 j theta) ∂angHaar =
        ∑ i, ∑ j, (a i * b j) * (∫ theta, basis_EX009 i theta * basis_EX009 j theta ∂angHaar) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hint i j)]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_const_mul _ _
    _ = _ := by
      simp_rw [basis_inner_EX009]
      apply Finset.sum_congr rfl
      intro i _
      simp

noncomputable def secondCosCoefficient_EX009 (A B C : ℝ) : ℝ :=
  (A ^ 2 - B ^ 2) / 96 + C / 8

noncomputable def secondSinCoefficient_EX009 (A B D : ℝ) : ℝ :=
  A * B / 48 + D / 8

noncomputable def quasiCosCoefficients_EX009 (h A B C D : ℝ) : Fin 7 → ℝ :=
  ![-h * A / 4, 1, 0, h * A / 12, h * B / 12,
    h ^ 2 * secondCosCoefficient_EX009 A B C,
    h ^ 2 * secondSinCoefficient_EX009 A B D]

noncomputable def quasiSinCoefficients_EX009 (h A B C D : ℝ) : Fin 7 → ℝ :=
  ![-h * B / 4, 0, 1, -h * B / 12, h * A / 12,
    -h ^ 2 * secondSinCoefficient_EX009 A B D,
    h ^ 2 * secondCosCoefficient_EX009 A B C]

noncomputable def quasiCos_EX009 (h A B C D : ℝ) : AngCircle → ℝ :=
  angularPolynomial_EX009 (quasiCosCoefficients_EX009 h A B C D)

noncomputable def quasiSin_EX009 (h A B C D : ℝ) : AngCircle → ℝ :=
  angularPolynomial_EX009 (quasiSinCoefficients_EX009 h A B C D)

theorem quasi_gram_cos_EX009 (h A B C D : ℝ) :
    ∫ theta, quasiCos_EX009 h A B C D theta * quasiCos_EX009 h A B C D theta ∂angHaar =
      1 / 2 + h ^ 2 * (A ^ 2 / 16 + (A ^ 2 + B ^ 2) / 288) +
      h ^ 4 * ((secondCosCoefficient_EX009 A B C) ^ 2 +
        (secondSinCoefficient_EX009 A B D) ^ 2) / 2 := by
  unfold quasiCos_EX009
  rw [angularPolynomial_inner_EX009]
  norm_num [quasiCosCoefficients_EX009, Fin.sum_univ_succ]
  ring

theorem quasi_gram_sin_EX009 (h A B C D : ℝ) :
    ∫ theta, quasiSin_EX009 h A B C D theta * quasiSin_EX009 h A B C D theta ∂angHaar =
      1 / 2 + h ^ 2 * (B ^ 2 / 16 + (A ^ 2 + B ^ 2) / 288) +
      h ^ 4 * ((secondCosCoefficient_EX009 A B C) ^ 2 +
        (secondSinCoefficient_EX009 A B D) ^ 2) / 2 := by
  unfold quasiSin_EX009
  rw [angularPolynomial_inner_EX009]
  norm_num [quasiSinCoefficients_EX009, Fin.sum_univ_succ]
  ring

theorem quasi_gram_cross_EX009 (h A B C D : ℝ) :
    ∫ theta, quasiCos_EX009 h A B C D theta * quasiSin_EX009 h A B C D theta ∂angHaar =
      h ^ 2 * A * B / 16 := by
  unfold quasiCos_EX009 quasiSin_EX009
  rw [angularPolynomial_inner_EX009]
  norm_num [quasiCosCoefficients_EX009, quasiSinCoefficients_EX009, Fin.sum_univ_succ]
  ring



theorem memLp_angularPolynomial_EX009 (a : Fin 7 → ℝ) :
    MemLp (angularPolynomial_EX009 a) 2 angHaar :=
  memLp_finsetSum _ (fun i _ => (memLp_basis_EX009 i).const_mul (a i))

theorem quasi_gram_combination_EX009 (h A B C D u v : ℝ) :
    ∫ theta, (u * quasiCos_EX009 h A B C D theta +
      v * quasiSin_EX009 h A B C D theta) ^ 2 ∂angHaar =
      (u ^ 2 + v ^ 2) / 2 +
      h ^ 2 * ((A * u + B * v) ^ 2 / 16 +
        (A ^ 2 + B ^ 2) * (u ^ 2 + v ^ 2) / 288) +
      h ^ 4 * ((secondCosCoefficient_EX009 A B C) ^ 2 +
        (secondSinCoefficient_EX009 A B D) ^ 2) * (u ^ 2 + v ^ 2) / 2 := by
  let coeff : Fin 7 → ℝ := fun i =>
    u * quasiCosCoefficients_EX009 h A B C D i +
      v * quasiSinCoefficients_EX009 h A B C D i
  have hfun (theta : AngCircle) :
      u * quasiCos_EX009 h A B C D theta + v * quasiSin_EX009 h A B C D theta =
      angularPolynomial_EX009 coeff theta := by
    unfold quasiCos_EX009 quasiSin_EX009 angularPolynomial_EX009 coeff
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp_rw [hfun]
  simp only [pow_two]
  rw [angularPolynomial_inner_EX009]
  norm_num [coeff, quasiCosCoefficients_EX009, quasiSinCoefficients_EX009, Fin.sum_univ_succ]
  ring

theorem quasi_gram_lower_EX009 (h A B C D u v : ℝ) :
    (u ^ 2 + v ^ 2) / 2 ≤
      ∫ theta, (u * quasiCos_EX009 h A B C D theta +
        v * quasiSin_EX009 h A B C D theta) ^ 2 ∂angHaar := by
  rw [quasi_gram_combination_EX009]
  have h1 : 0 ≤ h ^ 2 * ((A * u + B * v) ^ 2 / 16 +
      (A ^ 2 + B ^ 2) * (u ^ 2 + v ^ 2) / 288) := by positivity
  have h2 : 0 ≤ h ^ 4 * ((secondCosCoefficient_EX009 A B C) ^ 2 +
      (secondSinCoefficient_EX009 A B D) ^ 2) * (u ^ 2 + v ^ 2) / 2 := by positivity
  linarith

theorem quasi_gram_upper_error_EX009 {h : ℝ} (hh : |h| ≤ 1) (A B C D u v : ℝ) :
    (∫ theta, (u * quasiCos_EX009 h A B C D theta +
      v * quasiSin_EX009 h A B C D theta) ^ 2 ∂angHaar) -
      (u ^ 2 + v ^ 2) / 2 ≤
      h ^ 2 * (19 * (A ^ 2 + B ^ 2) / 288 +
        ((secondCosCoefficient_EX009 A B C) ^ 2 +
          (secondSinCoefficient_EX009 A B D) ^ 2) / 2) * (u ^ 2 + v ^ 2) := by
  rw [quasi_gram_combination_EX009]
  have hq : (A * u + B * v) ^ 2 ≤ (A ^ 2 + B ^ 2) * (u ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (A * v - B * u)]
  have hq' := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ h ^ 2 / 16)
  have h2 : h ^ 2 ≤ 1 := by
    calc
      h ^ 2 = |h| ^ 2 := (sq_abs h).symm
      _ ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg h) hh 2
      _ = 1 := by norm_num
  have h4 : h ^ 4 ≤ h ^ 2 := by
    have he := mul_le_mul_of_nonneg_left h2 (sq_nonneg h)
    nlinarith
  have h4' := mul_le_mul_of_nonneg_right h4
    (by positivity : 0 ≤ ((secondCosCoefficient_EX009 A B C) ^ 2 +
      (secondSinCoefficient_EX009 A B D) ^ 2) * (u ^ 2 + v ^ 2) / 2)
  nlinarith


end DGPS.Circle.FirstClusterFourierEX009
