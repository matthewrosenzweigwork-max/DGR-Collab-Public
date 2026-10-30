import DGPS.FiniteN.AnisotropicQuarticConditionalLSI
import DGPS.FiniteN.Tools.Linearization

/-!
# Field-uniform Poincare bound for the actual latent quartic conditional law

The genuine uniform LSI is linearized using the existing finite entropy expansion.
One small bounded smooth path suffices; no new Taylor theorem or oscillation bound is
introduced. Native smooth tensorization gives exactly the FIN060 transfer domain.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.BoundedComparison
open DGPS.FiniteN.Tools.AuxiliaryTransferTorus DGPS.FiniteN.Tools.ConditionalMeanDerivative
open DGPS.FiniteN.Tools.WeightedSobolev

namespace DGPS.FiniteN

private theorem smooth_memLp_probability (μ : Measure (Torus 1)) [IsProbabilityMeasure μ]
    (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) : MemLp f 2 μ := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuous_torus.continuousOn
  exact memLp_of_bounded (a := -B) (b := B)
    (Eventually.of_forall fun x => abs_le.mp (by simpa only [Real.norm_eq_abs] using hB x (Set.mem_univ x)))
    hf.continuous_torus.aestronglyMeasurable 2

private theorem smooth_lsi_implies_poincare_real (μ : Measure (Torus 1)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 < C)
    (hLS : ∀ f : Torus 1 → ℝ, IsSmoothPeriodic f →
      homogeneousEntropy μ (fun x => f x ^ 2) ≤
        ENNReal.ofReal (C * ∫ x, coordPartial 0 f x ^ 2 ∂μ))
    (f : Torus 1 → ℝ) (hf : IsSmoothPeriodic f) :
    variance f μ ≤ C * ∫ x, coordPartial 0 f x ^ 2 ∂μ := by
  let m := ∫ x, f x ∂μ
  let F := fun x => f x - m
  have hFs : IsSmoothPeriodic F := hf.sub contDiff_const
  have hfm := smooth_memLp_probability μ f hf
  have hFm := smooth_memLp_probability μ F hFs
  have hmean : (∫ x, F x ∂μ) = 0 := by
    change (∫ x, (f x - m) ∂μ) = 0
    rw [integral_sub (hfm.integrable one_le_two) (integrable_const m)]
    simp [m]
  let V := ∫ x, F x ^ 2 ∂μ
  let E := ∫ x, coordPartial 0 f x ^ 2 ∂μ
  have hV : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hvar : variance f μ = V := by
    calc
      _ = variance F μ := (variance_sub_const hfm.aestronglyMeasurable m).symm
      _ = V := variance_of_integral_eq_zero hFm.aestronglyMeasurable.aemeasurable hmean
  rw [hvar]
  by_cases hVzero : V = 0
  · rw [hVzero]
    exact mul_nonneg hC.le hE
  have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hVzero)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hFs.continuous_torus.continuousOn
  have hMb : ∀ x, |F x| ≤ M := fun x => by
    simpa only [Real.norm_eq_abs] using hM x (Set.mem_univ x)
  have hM0 : 0 ≤ M := (abs_nonneg (F 0)).trans (hMb 0)
  let ε := min (1 / (2 * (M + 1))) (V / (20 * (M ^ 3 + 1)))
  have hε : 0 < ε := lt_min (div_pos (by norm_num) (by positivity))
    (div_pos hVp (by positivity))
  have hsmall : |ε| * M ≤ 1 / 2 := by
    have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (M + 1))).mp
      (show ε ≤ 1 / (2 * (M + 1)) from min_le_left _ _)
    rw [abs_of_pos hε]
    nlinarith
  have hcoef : 10 * M ^ 3 * ε ≤ V := by
    have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * (M ^ 3 + 1))).mp
      (show ε ≤ V / (20 * (M ^ 3 + 1)) from min_le_right _ _)
    have hp := mul_nonneg (pow_nonneg hM0 3) hε.le
    nlinarith
  obtain ⟨hHfinite, hTaylor⟩ := linearization_entropy_expansion hFm.aestronglyMeasurable hMb hmean hsmall
  rw [abs_of_pos hε] at hTaylor
  have hErr : 10 * M ^ 3 * ε ^ 3 ≤ ε ^ 2 * V := by
    have hm := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ε)
    nlinarith
  let P := fun x => 1 + ε * F x
  have hPs : IsSmoothPeriodic P := contDiff_const.add (contDiff_const.mul hFs)
  have hD : ∀ x, coordPartial 0 P x = ε * coordPartial 0 f x := by
    intro x
    have hd := ((((hf.differentiable (by simp)) (SharpLSI.secT x)).hasFDerivAt.sub_const m).const_mul ε).const_add 1
    have he := congrArg (fun L => L (Pi.single (0 : Fin 1) (1 : ℝ))) hd.fderiv
    simpa [coordPartial, P, F, Function.comp_def] using he
  have hLS := hLS P hPs
  have hEnergy : (∫ x, coordPartial 0 P x ^ 2 ∂μ) = ε ^ 2 * E := by
    have he : (fun x => coordPartial 0 P x ^ 2) = fun x => ε ^ 2 * coordPartial 0 f x ^ 2 := by
      funext x
      rw [hD]
      ring
    rw [he, integral_const_mul]
  rw [hEnergy] at hLS
  have hLSr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLS
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ C * (ε ^ 2 * E))] at hLSr
  have hlo := (abs_le.mp hTaylor).1
  have hineq : ε ^ 2 * V ≤ C * (ε ^ 2 * E) := by
    change |(homogeneousEntropy μ (fun x => (1 + ε * F x) ^ 2)).toReal -
      2 * ε ^ 2 * V| ≤ 10 * M ^ 3 * ε ^ 3 at hTaylor
    dsimp only [P] at hLSr
    have hlo := (abs_le.mp hTaylor).1
    nlinarith
  have he : C * (ε ^ 2 * E) = ε ^ 2 * (C * E) := by ring
  rw [he] at hineq
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos hε)).mp hineq

/-- The actual quartic one-site law has a field-independent native Poincare constant.
Only the genuine uniform LSI and its proved finite entropy linearization are used. -/
theorem quartic_site_uniform_poincare :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Fin 2 → ℝ,
      PoincareAt (siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w)
        IsSmoothPeriodic TiltedXY.Fin050.gam1_FIN050 C := by
  obtain ⟨C, hC, hLS⟩ := quartic_site_uniform_lsi
  refine ⟨C, hC, fun w f hf => ?_⟩
  let μ := siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_siteLaw quartic_hubbard_hyp w
  have hfm := smooth_memLp_probability μ f hf
  have hi := (smooth_memLp_probability μ (coordPartial 0 f)
    (hf.isSmoothPeriodic_coordPartial 0)).integrable_sq
  have hreal := smooth_lsi_implies_poincare_real μ C hC (hLS w) f hf
  rw [← hfm.ofReal_variance_eq]
  unfold TiltedXY.Fin050.gam1_FIN050
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _),
    ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The exact latent Hubbard conditional product has the SAME constant for every
auxiliary field and every positive particle number, on the native FIN060 test domain. -/
theorem quartic_conditional_uniform_poincare :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, ∀ w : Fin 2 → ℝ,
      PoincareAt (condLaw quarticHubbardU quarticHubbardFeature (haar 1) N w)
        IsSmoothPeriodicParticle smoothGamma C := by
  obtain ⟨C, hC, hsite⟩ := quartic_site_uniform_poincare
  refine ⟨C, hC, fun N w f hf => ?_⟩
  have hp := isProbabilityMeasure_siteLaw quartic_hubbard_hyp (m := haar 1) w
  have hb := measurable_bounded_of_smooth hf
  unfold condLaw
  have hT : TP IsSmoothPeriodic TiltedXY.Fin050.gam1_FIN050
      (fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w) f :=
    { meas := hb.1
      memLp := by
        obtain ⟨B, hB⟩ := hb.2
        exact memLp_of_bounded (a := -B) (b := B)
          (Eventually.of_forall fun x => abs_le.mp (hB x)) hb.1.aestronglyMeasurable 2
      sm := fun x i => TiltedXY.Fin050.isSmoothPeriodic_slice_FIN050 hf x i
      aem := fun i => by
        have he : dens TiltedXY.Fin050.gam1_FIN050 f i =
            fun x => ENNReal.ofReal (particlePartial i 0 f x ^ 2) := by
          funext x
          unfold dens TiltedXY.Fin050.gam1_FIN050
          rw [TiltedXY.Fin050.coordPartial_slice_FIN050 hf x i]
        rw [he]
        exact ((measurable_bounded_partial_of_smooth hf i 0).1.pow_const 2).ennreal_ofReal.aemeasurable }
  have hm := poincare_tensorization
    (fun _ : Fin N => siteLaw quarticHubbardU quarticHubbardFeature (haar 1) w)
    (fun _ => hsite w) f hT
  refine hm.trans (le_of_eq ?_)
  congr 1
  apply lintegral_congr
  intro x
  unfold smoothGamma
  have he : ∀ i, TiltedXY.Fin050.gam1_FIN050 (slice i f x) (x i) =
      ENNReal.ofReal (particlePartial i 0 f x ^ 2) := by
    intro i
    unfold TiltedXY.Fin050.gam1_FIN050
    rw [TiltedXY.Fin050.coordPartial_slice_FIN050 hf x i]
  simp_rw [he]
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _]
  apply Finset.sum_congr rfl
  intro i hi
  simp

end DGPS.FiniteN
