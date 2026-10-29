import DGPS.FiniteN.Tools.BoundedComparison
import Mathlib

/-!
# Strong convexity LSI: bounded correction and dilation (FIN025, partial)

Proved here: the two reduction steps of FIN025 that do not need the Bakry-Emery estimate.

* `hasLSIRate_of_bounded_correction`: removal of a bounded correction `q` with oscillation `≤ b`
  from the Gibbs law, at the price of a factor `e^{-b}` in the rate (uses FIN004);
* `hasLSIRate_map_smul`: the dilation `y = s z` multiplies the rate of the `z`-law by `s²`.

The Euclidean strongly convex LSI itself (`D²U ≥ λ I ⇒ rate λ`) is not proved here.
-/

open MeasureTheory
open scoped ENNReal ContDiff

namespace DGPS.FiniteN.Tools.StrongConvexityLSI

variable {k : ℕ}

/-- Smooth compactly supported test functions on `ℝ^k`. -/
def TestFn (f : EuclideanSpace ℝ (Fin k) → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f

/-- The Euclidean carre-du-champ `|∇f|²`. -/
noncomputable def gradSq (f : EuclideanSpace ℝ (Fin k) → ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    ℝ≥0∞ :=
  ‖fderiv ℝ f x‖ₑ ^ 2

/-- `μ` satisfies `Ent(f²) ≤ (2/lam) ∫ |∇f|²` for all smooth compactly supported `f`. -/
def HasLSIRate (μ : Measure (EuclideanSpace ℝ (Fin k))) (lam : ℝ) : Prop :=
  DGPS.FiniteN.Tools.BoundedComparison.LogSobolevAt μ TestFn gradSq (2 / lam)

/-- The Gibbs probability law `e^{-U} / ∫ e^{-U}` on `ℝ^k`. -/
noncomputable def gibbs (U : EuclideanSpace ℝ (Fin k) → ℝ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x) / ∫ y, Real.exp (-U y)))

section Dilation

variable (s : ℝ) (hs : 0 < s)

/-- The dilation `z ↦ s • z` as a measurable equivalence. -/
noncomputable def dil : EuclideanSpace ℝ (Fin k) ≃ᵐ EuclideanSpace ℝ (Fin k) :=
  (Homeomorph.smulOfNeZero s hs.ne').toMeasurableEquiv

include hs in
theorem hasLSIRate_map_smul {μ : Measure (EuclideanSpace ℝ (Fin k))} {κ : ℝ} (hκ : 0 < κ)
    (h : HasLSIRate μ κ) : HasLSIRate (μ.map (dil s hs).symm) (s ^ 2 * κ) := by
  intro f hf
  set e := dil s hs with he
  have hes : ∀ y, e.symm y = s⁻¹ • y := fun y => rfl
  have hee : ∀ z, e z = s • z := fun z => rfl
  set g : EuclideanSpace ℝ (Fin k) → ℝ := fun y => f (s⁻¹ • y) with hg
  have hgt : TestFn g := by
    refine ⟨hf.1.comp (contDiff_const_smul s⁻¹), ?_⟩
    exact hf.2.comp_homeomorph (Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs.ne'))
  have hmp : MeasurePreserving e (μ.map e.symm) μ :=
    ⟨e.measurable, by rw [Measure.map_map e.measurable e.symm.measurable]; simp⟩
  have hent := DGPS.FiniteN.Tools.BoundedComparison.homogeneousEntropy_comp_equiv e hmp
    (fun y => g y ^ 2)
  have hlhs : DGPS.homogeneousEntropy (μ.map e.symm) (fun z => f z ^ 2) =
      DGPS.homogeneousEntropy μ (fun y => g y ^ 2) := by
    rw [← hent]
    congr 1
    funext z
    simp [hg, hee, smul_smul, hs.ne']
  have hder : ∀ z, gradSq g (e z) = ENNReal.ofReal (s⁻¹ ^ 2) * gradSq f z := by
    intro z
    have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin k) => s⁻¹ • y)
        (s⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) (e z) :=
      (hasFDerivAt_id (e z)).const_smul s⁻¹
    have hfd : DifferentiableAt ℝ f (s⁻¹ • e z) :=
      (hf.1.differentiable (by simp)) _
    have hcomp := (hfd.hasFDerivAt).comp (e z) hd
    have hz : s⁻¹ • e z = z := by simp [hee, smul_smul, hs.ne']
    rw [hz] at hcomp
    have hgd : fderiv ℝ g (e z) = s⁻¹ • fderiv ℝ f z := by
      have h1 : fderiv ℝ g (e z) = _ := hcomp.fderiv
      rw [h1]
      ext v
      simp
    unfold gradSq
    rw [hgd, enorm_smul, mul_pow, Real.enorm_eq_ofReal (inv_nonneg.2 hs.le),
      ENNReal.ofReal_pow (inv_nonneg.2 hs.le)]
  have hen : ∫⁻ y, gradSq g y ∂μ =
      ENNReal.ofReal (s⁻¹ ^ 2) * ∫⁻ z, gradSq f z ∂(μ.map e.symm) := by
    rw [← hmp.lintegral_comp_emb e.measurableEmbedding (gradSq g)]
    simp_rw [hder]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have := h g hgt
  rw [hlhs]
  refine this.trans ?_
  rw [hen, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 2
  field_simp

end Dilation

section BoundedCorrection

theorem integral_exp_neg_pos {V : EuclideanSpace ℝ (Fin k) → ℝ}
    (h : Integrable (fun x => Real.exp (-V x))) : 0 < ∫ x, Real.exp (-V x) := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) h]
  have : Function.support (fun x => Real.exp (-V x)) = Set.univ :=
    Set.eq_univ_of_forall fun x => (Real.exp_pos _).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

theorem gibbs_isProbabilityMeasure {V : EuclideanSpace ℝ (Fin k) → ℝ}
    (h : Integrable (fun x => Real.exp (-V x))) : IsProbabilityMeasure (gibbs V) := by
  have hZ := integral_exp_neg_pos h
  refine ⟨?_⟩
  rw [gibbs, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (h.div_const _)
      (Filter.Eventually.of_forall fun x => by positivity)]
  rw [integral_div, div_self hZ.ne']
  simp

theorem hasLSIRate_of_bounded_correction {U q : EuclideanSpace ℝ (Fin k) → ℝ} {b lam : ℝ}
    (hlam : 0 < lam) (hU : Continuous U) (hq : Measurable q) (hosc : ∀ x y, q x - q y ≤ b)
    (hint : Integrable (fun x => Real.exp (-U x)))
    (hQ : HasLSIRate (gibbs fun x => U x + q x) lam) :
    HasLSIRate (gibbs U) (lam * Real.exp (-b)) := by
  have hUm : Measurable U := hU.measurable
  obtain ⟨y0⟩ : Nonempty (EuclideanSpace ℝ (Fin k)) := inferInstance
  have hint' : Integrable (fun x => Real.exp (-(U x + q x))) := by
    refine (hint.mul_const (Real.exp (b - q y0))).mono' ?_ ?_
    · exact (Real.measurable_exp.comp (hUm.add hq).neg).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith [hosc y0 x])
  have := gibbs_isProbabilityMeasure hint
  have := gibbs_isProbabilityMeasure hint'
  have hZ := integral_exp_neg_pos hint
  have hZ' := integral_exp_neg_pos hint'
  set Z := ∫ x, Real.exp (-U x)
  set Z' := ∫ x, Real.exp (-(U x + q x))
  set ρ : EuclideanSpace ℝ (Fin k) → ℝ := fun x => Z' / Z * Real.exp (q x) with hρ
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => by positivity
  have hP : gibbs U = (gibbs fun x => U x + q x).withDensity (fun x => ENNReal.ofReal (ρ x)) := by
    have hm1 : Measurable fun x => ENNReal.ofReal (Real.exp (-(U x + q x)) / Z') :=
      ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (hUm.add hq).neg).div_const _)
    have hm2 : Measurable fun x => ENNReal.ofReal (ρ x) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.mul (Real.measurable_exp.comp hq)))
    rw [gibbs, gibbs, ← withDensity_mul _ hm1 hm2]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : Real.exp (-(U x + q x)) = Real.exp (-U x) * Real.exp (-q x) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (q x) * Real.exp (-q x) = 1 := by rw [← Real.exp_add]; simp
    rw [h1]
    have hZe : (∫ y, Real.exp (-U y)) = Z := rfl
    rw [hZe]
    simp only [hρ]
    field_simp
    rw [mul_comm]
    exact h2.symm
  have hosc' : ∀ x y, ρ x ≤ Real.exp b * ρ y := by
    intro x y
    simp only [hρ]
    have : Real.exp (q x) ≤ Real.exp b * Real.exp (q y) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [hosc x y])
    have hc : 0 ≤ Z' / Z := by positivity
    calc Z' / Z * Real.exp (q x) ≤ Z' / Z * (Real.exp b * Real.exp (q y)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hmem : ∀ f, TestFn f → MemLp f 2 (gibbs fun x => U x + q x) :=
    fun f hf => hf.1.continuous.memLp_of_hasCompactSupport hf.2
  have key := (DGPS.FiniteN.Tools.BoundedComparison.bounded_comparison_tensorization_and_covariance.{0}).1
    hP hρ0 hosc' (Sm := TestFn) (Γ := gradSq) hmem (C := 2 / lam)
  have := (key.2 hQ)
  unfold HasLSIRate
  have hc : Real.exp b * (2 / lam) = 2 / (lam * Real.exp (-b)) := by
    rw [Real.exp_neg]; field_simp
  rw [hc] at this
  exact this

end BoundedCorrection

end DGPS.FiniteN.Tools.StrongConvexityLSI
