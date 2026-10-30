import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderFeedbackCoefficients
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackSpatialRegularity

/-! Actual first spatial derivative control of the nonlinear correction, from
the factual finite expansion and its bounded probability coefficients. This
does not infer derivative control from a C0 Holder estimate. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem point_bound (F : PeriodicHolder_STR02968) (t : ℝ) : |F.val t| ≤ ‖F‖ := by
  rw [PeriodicHolder_STR02968.norm_def]
  exact (F.isPerHolder.abs_le_supNorm t).trans
    (le_add_of_nonneg_right (holderSemi_nonneg_STR02968 _ _))

private theorem combination_bound (c m : Fin 3 → ℝ) (f : Fin 3 → ℝ)
    {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hm : ∀ i, |m i| ≤ B) (hf : ∀ i, |f i| ≤ U) :
    |∑ i : Fin 3, (c i * m i) * f i| ≤ (∑ i : Fin 3, |c i|) * B * U := by
  calc
    _ ≤ ∑ i : Fin 3, |(c i * m i) * f i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, |c i| * B * U := Finset.sum_le_sum fun i _ => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hm i) (abs_nonneg _)) (hf i)
        (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

private theorem combination_derivative (c m : Fin 3 → ℝ)
    (F : Fin 3 → PeriodicHolder_STR02968) (hF : ∀ i, ContDiff ℝ ∞ (F i).val) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ∑ i : Fin 3, (c i * m i) * (F i).val s)
      (∑ i : Fin 3, (c i * m i) * deriv (F i).val t) t :=
  HasDerivAt.fun_sum fun i _ =>
    (((hF i).differentiable (by simp)) t).hasDerivAt.const_mul _

/-- The first ANGULAR derivative of the actual correction is O(epsilon),
uniformly on ALL original absolute densities and bounded real rates. Genuine
spatial differentiability is supplied alongside the bound. -/
theorem elementaryEulerHolder_derivative_uniform_bound {h : ℝ} (hh : 0 < h)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1, ∀ r : ℝ, |r| ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Differentiable ℝ (elementaryEulerHolder h ε r ρ).val ∧
          ∀ t : ℝ, |deriv (elementaryEulerHolder h ε r ρ).val t| ≤ K * ε := by
  classical
  obtain ⟨B, M, hB, hM, hcoef⟩ := elementaryEulerHolder_coefficient_bounds hh
  obtain ⟨U, hU, hbasis⟩ := interactingHolderBasis_derivative_bounds hh
  let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
  let C := ∑ i : Fin 3, |c i|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let V := 1 + ∑ i : Fin 3, ‖interactingHolderDerivative h i‖
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hvalues (i : Fin 3) (t : ℝ) : |(interactingHolderDerivative h i).val t| ≤ V := by
    have hi : ‖interactingHolderDerivative h i‖ ≤ ∑ j : Fin 3, ‖interactingHolderDerivative h j‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have hv := point_bound (interactingHolderDerivative h i) t
    dsimp only [V]
    linarith
  let T := C * B * U
  let L := C * B * V
  have hT : 0 ≤ T := mul_nonneg (mul_nonneg hC hB.le) hU.le
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hC hB.le) hV
  let K := 1 + 2 * (2 + R) * T + 2 * (L + M) * T
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun ρ r hr ε hε he => ?_⟩
  let m := elementaryFeedbackMoment h ρ
  let a := elementaryFeedbackGeneratorMoment h ρ
  let p := elementaryFeedbackForceMoment h ρ
  let k := fun t : ℝ => ∑ i : Fin 3, (c i * m i) * (interactingHolderFeature h i).val t
  let d := fun t : ℝ => ∑ i : Fin 3, (c i * m i) * (interactingHolderDerivative h i).val t
  let A := fun t : ℝ => ∑ i : Fin 3, (c i * m i) * (interactingHolderGenerator h i).val t
  let LA := fun t : ℝ => ∑ i : Fin 3, (c i * a i) * (interactingHolderFeature h i).val t
  let LP := fun t : ℝ => ∑ i : Fin 3, (c i * p i) * (interactingHolderFeature h i).val t
  have hm (i : Fin 3) : |m i| ≤ B := (hcoef ρ i).1
  have ha (i : Fin 3) : |a i| ≤ B := (hcoef ρ i).2.1
  have hp (i : Fin 3) : |p i| ≤ M * B := (hcoef ρ i).2.2
  have hf (i : Fin 3) := (interactingHolderBasis_smooth hh i).1
  have hd (i : Fin 3) := (interactingHolderBasis_smooth hh i).2.1
  have hA (i : Fin 3) := (interactingHolderBasis_smooth hh i).2.2
  have hkD (t : ℝ) := combination_derivative c m (interactingHolderFeature h) hf t
  have hdD (t : ℝ) := combination_derivative c m (interactingHolderDerivative h) hd t
  have hAD (t : ℝ) := combination_derivative c m (interactingHolderGenerator h) hA t
  have hLAD (t : ℝ) := combination_derivative c a (interactingHolderFeature h) hf t
  have hLPD (t : ℝ) := combination_derivative c p (interactingHolderFeature h) hf t
  have heq : (elementaryEulerHolder h ε r ρ).val = fun t : ℝ =>
      (2 * ε) * (A t + LA t - r * k t) + ε ^ 2 * (d t * d t + 2 * LP t) := by
    rw [elementaryEulerHolder_finite_expansion]
    funext t
    simp only [Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_mul_STR02954, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    simp only [A, LA, k, d, LP, c, m, a, p, Fin.sum_univ_three]
  have hhas (t : ℝ) := (((hAD t).add (hLAD t)).sub ((hkD t).const_mul r)).const_mul (2 * ε)
    |>.add ((((hdD t).mul (hdD t)).add ((hLPD t).const_mul 2)).const_mul (ε ^ 2))
  have hsmooth : Differentiable ℝ (elementaryEulerHolder h ε r ρ).val := by
    rw [heq]
    exact fun t => (hhas t).differentiableAt
  refine ⟨hsmooth, fun t => ?_⟩
  have hkB : |deriv k t| ≤ T := by
    rw [(hkD t).deriv]
    exact combination_bound c m _ hB.le hU.le hm (fun i => (hbasis i t).1)
  have hdB : |deriv d t| ≤ T := by
    rw [(hdD t).deriv]
    exact combination_bound c m _ hB.le hU.le hm (fun i => (hbasis i t).2.1)
  have hAB : |deriv A t| ≤ T := by
    rw [(hAD t).deriv]
    exact combination_bound c m _ hB.le hU.le hm (fun i => (hbasis i t).2.2)
  have hLAB : |deriv LA t| ≤ T := by
    rw [(hLAD t).deriv]
    exact combination_bound c a _ hB.le hU.le ha (fun i => (hbasis i t).1)
  have hLPB : |deriv LP t| ≤ M * T := by
    rw [(hLPD t).deriv]
    have hb := combination_bound c p _ (mul_nonneg hM hB.le) hU.le hp (fun i => (hbasis i t).1)
    calc _ ≤ C * (M * B) * U := hb
      _ = M * T := by dsimp only [T]; ring
  have hdvalue : |d t| ≤ L := combination_bound c m _ hB.le hV hm (fun i => hvalues i t)
  have hfirst : |deriv A t + deriv LA t - r * deriv k t| ≤ (2 + R) * T := by
    calc
      _ ≤ |deriv A t| + |deriv LA t| + |r| * |deriv k t| := by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) (by rw [abs_mul]))
      _ ≤ T + T + R * T := by gcongr
      _ = _ := by ring
  have hsecond : |deriv d t * d t + d t * deriv d t + 2 * deriv LP t| ≤
      2 * (L + M) * T := by
    calc
      _ ≤ |deriv d t| * |d t| + |d t| * |deriv d t| + 2 * |deriv LP t| := by
        simpa only [abs_mul, abs_two] using
          (abs_add_le (deriv d t * d t + d t * deriv d t) (2 * deriv LP t)).trans
            (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ T * L + L * T + 2 * (M * T) := by gcongr
      _ = _ := by ring
  have hder : deriv (elementaryEulerHolder h ε r ρ).val t =
      (2 * ε) * (deriv A t + deriv LA t - r * deriv k t) +
        ε ^ 2 * (deriv d t * d t + d t * deriv d t + 2 * deriv LP t) := by
    rw [heq]
    have ht := (hhas t).deriv
    rw [← (hAD t).deriv, ← (hLAD t).deriv, ← (hkD t).deriv,
      ← (hdD t).deriv, ← (hLPD t).deriv] at ht
    exact ht
  rw [hder]
  have he2 : ε ^ 2 ≤ ε := by nlinarith
  calc
    _ ≤ (2 * ε) * |deriv A t + deriv LA t - r * deriv k t| +
        ε ^ 2 * |deriv d t * d t + d t * deriv d t + 2 * deriv LP t| := by
      refine (abs_add_le _ _).trans_eq (congrArg₂ (fun x y : ℝ => x + y) ?_ ?_)
      · rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)]
      · rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
    _ ≤ (2 * ε) * ((2 + R) * T) + ε * (2 * (L + M) * T) := by gcongr
    _ ≤ K * ε := by dsimp only [K]; nlinarith

private theorem angular_point (t : ℝ) :
    angEquiv.symm (t : AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : AngCircle) = angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [angRescale_mk]
  congr 1
  field_simp

/-- The actual PHYSICAL first coordinate derivative has its uniform O(epsilon)
bound. The factor 2*pi is proved by differentiating the true native dictionary. -/
theorem elementaryEulerCorrection_derivative_uniform_bound {h : ℝ} (hh : 0 < h)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1, ∀ r : ℝ, |r| ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : Torus 1,
        |coordPartial 0 (elementaryEulerCorrection h ε r ρ) x| ≤ K * ε := by
  obtain ⟨K, hK, hbound⟩ := elementaryEulerHolder_derivative_uniform_bound hh R hR
  let p := 2 * Real.pi
  have hp : 0 < p := by dsimp only [p]; positivity
  refine ⟨p * K, mul_pos hp hK, fun ρ r hr ε hε he x => ?_⟩
  obtain ⟨hd, hdb⟩ := hbound ρ r hr ε hε he
  obtain ⟨t, rfl⟩ := bs_exists_pt x
  have heq : (fun s : ℝ => elementaryEulerCorrection h ε r ρ (pt s)) =
      fun s => (elementaryEulerHolder h ε r ρ).val (p * s) := by
    funext s
    rw [elementaryEulerHolder_native hh, angular_point]
    have hs : p * s / (2 * Real.pi) = s := by dsimp only [p]; field_simp
    rw [hs]
  have hnative := hasDerivAt_smooth_one (isSmooth_elementaryEulerCorrection h ε r ρ) t
  have hcomp := ((hd (p * t)).hasDerivAt).comp t ((hasDerivAt_id t).const_mul p)
  rw [heq] at hnative
  have hder := hnative.unique hcomp
  rw [hder, mul_one, abs_mul, abs_of_pos hp]
  calc
    _ ≤ (K * ε) * p := mul_le_mul_of_nonneg_right (hdb (p * t)) hp.le
    _ = _ := by ring

end DGPS.Examples.ThreeSpeciesCircle
