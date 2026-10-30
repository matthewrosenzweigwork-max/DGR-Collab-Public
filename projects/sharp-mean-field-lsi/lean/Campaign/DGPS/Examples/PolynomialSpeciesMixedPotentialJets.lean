import DGPS.Examples.PolynomialSpeciesMixedNonlocalSecond

/-! The actual complete mixed Euler potential: ordinary log-drift terms and
all nonlocal moments. These are genuine function jets, before density-weighted
mean subtraction. No prescribed Fourier jet is a premise. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem amplitude_second (a b : ℝ) :
    e2_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) =
      (-1 : ℝ) • e0_STR02955 (a • cosC2_STR02915 + b • sinC2_STR02915) := by
  have hc : e2_STR02955 cosC2_STR02915 = (-1 : ℝ) • e0_STR02955 cosC2_STR02915 := by
    apply ext_STR02954
    funext x
    rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
    simp only [cosC2_val_STR02915, e0_val_STR02955, Pi.smul_apply, smul_eq_mul]
    rw [Real.deriv_cos']
    change deriv (-Real.sin) x = _
    rw [((Real.hasDerivAt_sin x).neg).deriv]
    ring
  have hs : e2_STR02955 sinC2_STR02915 = (-1 : ℝ) • e0_STR02955 sinC2_STR02915 := by
    apply ext_STR02954
    funext x
    rw [e2_val_STR02955, PeriodicHolder_STR02968.val_smul]
    simp only [sinC2_val_STR02915, e0_val_STR02955, Pi.smul_apply, smul_eq_mul]
    rw [Real.deriv_sin]
    simp [Real.deriv_cos']
  rw [map_add, map_smul, map_smul, hc, hs, map_add, map_smul, map_smul]
  apply ext_STR02954
  funext x
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_smul,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem log_line (t : ℝ) : polynomialRangeLogWeight (t, 0) = t • cosC2_STR02915 := by
  apply Subtype.ext
  funext x
  change (polynomialRangeLogWeight (t, 0)).val x = (t • cosC2_STR02915).val x
  rw [polynomialRangeLogWeight_val_explicit, PeriodicC2_STR02969.val_smul,
    Pi.smul_apply, smul_eq_mul, cosC2_val_STR02915]
  ring

private theorem expectation_smooth (a b : ℝ) (F : (ℝ × ℝ) → PeriodicHolder_STR02968)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (fun t : ℝ =>
      eulerMean (e0_STR02955 (polynomialRangeLogWeight (t, 0)))
        (t • (a • cosC2_STR02915 + b • sinC2_STR02915)) (F (t, 0))) := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  have hu : ContDiff ℝ ∞ (fun t : ℝ => t • (a • cosC2_STR02915 + b • sinC2_STR02915)) :=
    contDiff_id.smul contDiff_const
  have hR : ContDiff ℝ ∞ (fun t : ℝ => rho_STR02954 (0, e0_STR02955 (polynomialRangeLogWeight (t, 0)) + e0_STR02955 (t • (a • cosC2_STR02915 + b • sinC2_STR02915)))) := rho_smooth_STR02954.comp (contDiff_const.prodMk
    ((e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp hp)).add (e0_STR02955.contDiff.comp hu)))
  exact meanCLM_STR02954.contDiff.comp ((hF.comp hp).mul hR)

private theorem nonlocal_smooth (a b : ℝ) : ContDiff ℝ ∞ (polynomialMixedNonlocalPotential a b) := by
  have hp : ContDiff ℝ ∞ (fun t : ℝ => (t, (0 : ℝ))) := contDiff_id.prodMk contDiff_const
  have hm := expectation_smooth a b _ (e0_STR02955.contDiff.comp polynomialRange_data_smooth.2.2.2.1)
  have hA := expectation_smooth a b _ polynomialRange_data_smooth.2.2.2.2.1
  have hJ := expectation_smooth a b _ polynomialRange_data_smooth.2.2.2.2.2
  have hφ := (e0_STR02955.contDiff.comp polynomialRange_data_smooth.2.2.2.1).comp hp
  have hB := polynomialRange_data_smooth.2.2.2.2.1.comp hp
  have hj := polynomialRange_data_smooth.2.2.2.2.2.comp hp
  exact (((contDiff_const.mul ((hA.add (contDiff_const.mul (hm.mul hJ))).sub
    (contDiff_const.mul hm))).smul hφ).add ((contDiff_const.mul hm).smul hB)).add
      ((contDiff_const.mul (hm.mul hm)).smul hj)

/-- Exact ordinary/nonlocal decomposition on the true mixed line. -/
theorem polynomialMixedPotential_identity (a b t : ℝ) :
    let v := a • cosC2_STR02915 + b • sinC2_STR02915
    polynomialRangeEulerPotential (t, 0) DGPS.Circle.AngularNormalization.a0 (t • v) =
      (-2 * DGPS.Circle.AngularNormalization.a0 * t ^ 2) • (e1_STR02955 cosC2_STR02915 * e1_STR02955 v) +
        (-DGPS.Circle.AngularNormalization.a0 * t ^ 2) • (e1_STR02955 v * e1_STR02955 v) +
          polynomialMixedNonlocalPotential a b t := by
  unfold polynomialRangeEulerPotential polynomialMixedNonlocalPotential
    polynomialMixedFeatureMoment polynomialMixedGeneratorMoment
  simp only [log_line, map_smul, amplitude_second]
  apply ext_STR02954
  funext x
  simp only [PeriodicHolder_STR02968.val_add, PeriodicHolder_STR02968.val_sub,
    PeriodicHolder_STR02968.val_smul, val_mul_STR02954,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- All jets of the complete potential needed for the normalized Euler second
derivative are derived from the actual ordinary/nonlocal decomposition. -/
theorem polynomialMixedPotential_jets (a b : ℝ) :
    let v := a • cosC2_STR02915 + b • sinC2_STR02915
    let K := fun t : ℝ => polynomialRangeEulerPotential (t, 0) DGPS.Circle.AngularNormalization.a0 (t • v)
    ContDiff ℝ ∞ K ∧ K 0 = 0 ∧ deriv K 0 = 0 ∧
      iteratedDeriv 2 K 0 =
        (-4 * DGPS.Circle.AngularNormalization.a0) • (e1_STR02955 cosC2_STR02915 * e1_STR02955 v) +
          (-2 * DGPS.Circle.AngularNormalization.a0) • (e1_STR02955 v * e1_STR02955 v) +
            (6 * DGPS.Circle.AngularNormalization.a0 *
              (Real.sqrt 2 * ((a ^ 2 - b ^ 2) / 4 + a / 6))) • e0_STR02955 polynomialOriginMode := by
  let v := a • cosC2_STR02915 + b • sinC2_STR02915
  let H := e1_STR02955 cosC2_STR02915 * e1_STR02955 v
  let Q := e1_STR02955 v * e1_STR02955 v
  let f := fun t : ℝ => (-2 * DGPS.Circle.AngularNormalization.a0 * t ^ 2) • H
  let g := fun t : ℝ => (-DGPS.Circle.AngularNormalization.a0 * t ^ 2) • Q
  let X := polynomialMixedNonlocalPotential a b
  have hfs : ContDiff ℝ ∞ (fun t : ℝ => -2 * DGPS.Circle.AngularNormalization.a0 * t ^ 2) := contDiff_const.mul (contDiff_id.pow 2)
  have hgs : ContDiff ℝ ∞ (fun t : ℝ => -DGPS.Circle.AngularNormalization.a0 * t ^ 2) := contDiff_const.mul (contDiff_id.pow 2)
  have hf : ContDiff ℝ ∞ f := (contDiff_const.mul (contDiff_id.pow 2)).smul contDiff_const
  have hg : ContDiff ℝ ∞ g := (contDiff_const.mul (contDiff_id.pow 2)).smul contDiff_const
  have hX : ContDiff ℝ ∞ X := nonlocal_smooth a b
  obtain ⟨hX0, hX1, hX2⟩ := polynomialMixedNonlocalPotential_jets a b
  have he : (fun t : ℝ => polynomialRangeEulerPotential (t, 0)
      DGPS.Circle.AngularNormalization.a0 (t • v)) = fun t : ℝ => f t + g t + X t :=
    funext (polynomialMixedPotential_identity a b)
  have hfD : HasDerivAt f 0 0 := by
    have hd := (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (-2 * DGPS.Circle.AngularNormalization.a0)).smul_const H
    simpa [f] using hd
  have hgD : HasDerivAt g 0 0 := by
    have hd := (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (-DGPS.Circle.AngularNormalization.a0)).smul_const Q
    simpa [g] using hd
  have hXD : HasDerivAt X 0 0 := (hX.differentiable (by simp) 0).hasDerivAt.congr_deriv hX1
  dsimp only
  rw [he]
  refine ⟨(hf.add hg).add hX, ?_, ?_, ?_⟩
  · simp only [zero_smul]
    rw [show polynomialRangeEulerPotential (0, 0) DGPS.Circle.AngularNormalization.a0 0 = f 0 + g 0 + X 0 by simpa only [zero_smul] using congrFun he 0]
    simp only [f, g, X, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_smul, hX0, zero_add]
  · simpa only [Pi.add_def, zero_add] using ((hfD.add hgD).add hXD).deriv
  · rw [iteratedDeriv_fun_add ((hf.add hg).of_le (by simp)).contDiffAt (hX.of_le (by simp)).contDiffAt,
      iteratedDeriv_fun_add (hf.of_le (by simp)).contDiffAt (hg.of_le (by simp)).contDiffAt]
    rw [show f = fun t : ℝ => (-2 * DGPS.Circle.AngularNormalization.a0 * t ^ 2) • H from rfl,
      iteratedDeriv_smul_const (hfs.of_le (by simp)).contDiffAt,
      show g = fun t : ℝ => (-DGPS.Circle.AngularNormalization.a0 * t ^ 2) • Q from rfl,
      iteratedDeriv_smul_const (hgs.of_le (by simp)).contDiffAt,
      iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hX2]
    norm_num [iteratedDeriv_fun_pow_zero]
    dsimp only [H, Q, v]
    rw [show 2 * DGPS.Circle.AngularNormalization.a0 * 2 = 4 * DGPS.Circle.AngularNormalization.a0 by ring,
      show DGPS.Circle.AngularNormalization.a0 * 2 = 2 * DGPS.Circle.AngularNormalization.a0 by ring]
    simp only [map_add, map_smul]

end DGPS.Examples.PolynomialSpecies
