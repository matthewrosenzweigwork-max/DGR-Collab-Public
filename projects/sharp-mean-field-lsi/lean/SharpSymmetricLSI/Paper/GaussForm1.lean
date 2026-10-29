import Mathlib

/-!
# R32 (A1): Gaussian integration by parts in one variable

`∫ x f(x) dN(0,1) = ∫ f'(x) dN(0,1)` for `f ∈ C¹` with `f`, `f'` bounded (`stein_gaussianReal`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace SharpLSI

/-- `φ' = -x φ` for the standard Gaussian density. -/
theorem hasDerivAt_stdGaussPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : gaussianPDFReal 0 1 = fun x => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) := by
    funext y; simp [gaussianPDFReal]
  rw [h]
  have := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.const_mul (√(2 * π))⁻¹
  convert this using 1
  simp; ring

theorem integrable_id_mul_stdGaussPDF : Integrable fun x : ℝ => x * gaussianPDFReal 0 1 x := by
  have h := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * π))⁻¹
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [gaussianPDFReal]
  push_cast
  ring_nf

/-- **Stein's lemma for `N(0,1)`.** -/
theorem stein_gaussianReal {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf'm : Measurable f') {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (hf'B : ∀ x, |f' x| ≤ B) :
    ∫ x, x * f x ∂gaussianReal 0 1 = ∫ x, f' x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  set φ := gaussianPDFReal 0 1 with hφ
  have hφi : Integrable φ := integrable_gaussianPDFReal 0 1
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hb : ∀ {g : ℝ → ℝ}, (∀ x, |g x| ≤ B) → ∀ᵐ x, ‖g x‖ ≤ B := fun {g} h =>
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x
  have huv' : Integrable (f * fun x => -x * φ x) :=
    integrable_id_mul_stdGaussPDF.neg.bdd_mul (c := B) hfc.aestronglyMeasurable (hb hfB)
      |>.congr (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have hu'v : Integrable (f' * φ) := hφi.bdd_mul (c := B) hf'm.aestronglyMeasurable (hb hf'B)
  have huv : Integrable (f * φ) := hφi.bdd_mul (c := B) hfc.aestronglyMeasurable (hb hfB)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := φ) (u' := f')
    (v' := fun x => -x * φ x) (fun x _ => hf x) (fun x _ => hasDerivAt_stdGaussPDF x)
    huv' hu'v huv
  have e1 : ∫ x, φ x * (x * f x) = -∫ x, f x * (-x * φ x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, φ x * f' x = ∫ x, f' x * φ x := by congr 1; funext x; ring
  rw [e1, key, e2, neg_neg]

theorem insertNth_eq_add {n : ℕ} (k : Fin (n + 1)) (a : ℝ) (w : Fin n → ℝ) :
    Fin.insertNth k a w = Fin.insertNth k 0 w + a • (Pi.single k 1 : Fin (n + 1) → ℝ) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
  · simp
  · simp [Pi.single_apply, Fin.succAbove_ne]

theorem hasDerivAt_insertNth {n : ℕ} (k : Fin (n + 1)) (w : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => (Fin.insertNth k a w : Fin (n + 1) → ℝ)) (Pi.single k 1) a := by
  have h := ((hasDerivAt_id a).smul_const (Pi.single k 1 : Fin (n + 1) → ℝ)).const_add
    (Fin.insertNth k 0 w : Fin (n + 1) → ℝ)
  simp only [id, one_smul] at h
  convert h using 1
  funext a; exact insertNth_eq_add k a w

/-- **Stein's lemma for the standard Gaussian on `ℝ^{n+1}`.** -/
theorem stein_pi {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ} (hF : Differentiable ℝ F)
    (hFc : Continuous fun y => fderiv ℝ F y) {B : ℝ} (hFB : ∀ y, |F y| ≤ B)
    (hdB : ∀ y, ‖fderiv ℝ F y‖ ≤ B) (k : Fin (n + 1)) :
    ∫ y, y k * F y ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∫ y, fderiv ℝ F y (Pi.single k 1) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  set P := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  set Q := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k
  have hmp : MeasurePreserving e P ((gaussianReal 0 1).prod Q) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) k
  have htrans : ∀ H : (Fin (n + 1) → ℝ) → ℝ,
      ∫ y, H y ∂P = ∫ p, H (Fin.insertNth k p.1 p.2) ∂((gaussianReal 0 1).prod Q) := fun H => by
    rw [← hmp.integral_comp' (g := fun p => H (Fin.insertNth k p.1 p.2))]
    congr 1; funext y
    exact congrArg H ((Fin.insertNthEquiv (fun _ => ℝ) k).apply_symm_apply y).symm
  have hFm : Continuous F := hF.continuous
  have hD : Continuous fun y => fderiv ℝ F y (Pi.single k 1) := hFc.clm_apply continuous_const
  have hins : Continuous fun p : ℝ × (Fin n → ℝ) => (Fin.insertNth k p.1 p.2 : Fin (n + 1) → ℝ) := by
    refine continuous_pi fun j => ?_
    rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨i, rfl⟩
    · simpa using continuous_fst
    · simp only [Fin.insertNth_apply_succAbove]
      exact (continuous_apply i).comp continuous_snd
  have hdB' : ∀ y, |fderiv ℝ F y (Pi.single k 1)| ≤ B := fun y => by
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖(Pi.single k 1 : Fin (n + 1) → ℝ)‖ = 1 := by simp [Pi.norm_single]
    rw [this, mul_one]; exact hdB y
  rw [htrans, htrans]
  simp only [Fin.insertNth_apply_same]
  -- integrability on the product
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 0)
  have i1 : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1 * F (Fin.insertNth k p.1 p.2))
      ((gaussianReal 0 1).prod Q) := by
    have ha : Integrable (fun p : ℝ × (Fin n → ℝ) => p.1) ((gaussianReal 0 1).prod Q) :=
      ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).comp_fst Q
    refine (ha.abs.mul_const B).mono' (continuous_fst.mul (hFm.comp hins)).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hFB _) (abs_nonneg _)
  have i2 : Integrable (fun p : ℝ × (Fin n → ℝ) => fderiv ℝ F (Fin.insertNth k p.1 p.2) (Pi.single k 1))
      ((gaussianReal 0 1).prod Q) :=
    (integrable_const B).mono' (hD.comp hins).aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hdB' _)
  rw [integral_prod_symm _ i1, integral_prod_symm _ i2]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  exact stein_gaussianReal (f := fun a => F (Fin.insertNth k a w))
    (f' := fun a => fderiv ℝ F (Fin.insertNth k a w) (Pi.single k 1))
    (fun a => (hF _).hasFDerivAt.comp_hasDerivAt a (hasDerivAt_insertNth k w a))
    (hD.comp (hins.comp (continuous_id.prodMk continuous_const))).measurable
    (fun a => hFB _) (fun a => hdB' _)

end SharpLSI
