import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# EX049.34: AC products and H1 bounds on an interval

Task id: EX049.34 (node EX049, shared infrastructure, no prerequisites inside the frontier).

If `u` and `v` are absolutely continuous on `[a, b]` and their a.e. derivatives lie in
`L²(a, b)`, then `u * v` is absolutely continuous, `(u * v)' = u' * v + u * v'` almost
everywhere, the `L²(a, b)` norm of `(u * v)'` is at most `‖v‖∞ ‖u'‖₂ + ‖u‖∞ ‖v'‖₂`, and the
derivative identity also holds as a weak-derivative identity against test functions with
compact support in `(a, b)`.

## Provides

- `DGPS.Frontier.EX049.ex049_34_ac_products_h1_bounds_interval`: the full specification
  statement, as a conjunction of five claims (product is absolutely continuous, a.e. Leibniz
  rule, product derivative in `L²(a, b)`, the `‖(u v)'‖₂` bound in `ℝ≥0∞`, and the weak
  identity).
- `DGPS.Frontier.EX049.ex049_34_ac_products_h1_bounds_interval_real`: real-number form of the norm
  bound, with explicit pointwise bounds `Mu`, `Mv` on `[a, b]` in place of the two
  essential suprema (no sign hypothesis on `Mu`, `Mv` is needed).

## R5 notes

- Absolute continuity on `[a, b]` is Mathlib's `AbsolutelyContinuousOnInterval f a b` (the
  epsilon-delta condition on `uIcc a b`). No hypothesis `a ≤ b` is added. For `b ≤ a` the open
  interval `Ioo a b` is empty, so every `L²(a, b)` and `∞`-norm statement is vacuous, while the
  absolute continuity of the product still holds on `uIcc a b`.
- "A.e. derivative" is Mathlib's total function `deriv`. By `ae_differentiableAt` an absolutely
  continuous function is differentiable at almost every point of the interval, so `deriv` is
  its a.e. derivative; any other a.e. representative of the derivative agrees with it a.e.
- `L²(a, b)` membership of the derivative is `MemLp (deriv u) 2 (volume.restrict (Ioo a b))`.
  This is the only hypothesis on the derivatives, as in the specification.
- The norms are `eLpNorm` over `volume.restrict (Ioo a b)` with values in `ℝ≥0∞`. The sup norm
  `‖·‖∞` is therefore the essential supremum on `(a, b)`. For continuous functions and `a < b` it
  equals the supremum over `[a, b]`. The bound is proved in the `ℝ≥0∞` form (no finiteness side
  condition is needed there); the `_real` corollary passes to real numbers and accepts any pointwise
  bounds on `Icc a b`.
- Additional conclusion (not literally in the specification, but used to make the norm bound
  meaningful): `deriv (u * v)` is itself in `L²(a, b)`.
- The a.e. identity is quantified as `∀ᵐ x, x ∈ Ioo a b → ...`, that is, almost everywhere on the
  open interval `(a, b)`. The statement uses `deriv (fun y => u y * v y)` on the left.
- Weak identity: for every `φ : ℝ → ℝ` with `ContDiff ℝ ∞ φ`, `HasCompactSupport φ` and
  `tsupport φ ⊆ Ioo a b`, the integral over `Ioo a b` of `(u v) φ'` equals minus the integral of
  `(u' v + u v') φ`. The compact support hypothesis is implied by the other support condition
  once `a`, `b` are finite and is kept only to mirror the usual test-function class. The
  right-hand side uses `u' v + u v'` rather than `deriv (u * v)`; the two agree a.e. by the
  second conjunct.
- Proof route (a shorter one than the one sketched in the specification, since the pinned Mathlib
  already contains the needed AC facts): product absolutely continuous by
  `AbsolutelyContinuousOnInterval.fun_mul`; derivative by `HasDerivAt.mul` on the intersection of
  the two full-measure differentiability sets; each summand is in `L²` by bounded-multiplier
  estimates (boundedness from `AbsolutelyContinuousOnInterval.exists_bound`, measurability from
  continuity); the norm bound is Holder with an `L∞` factor plus `eLpNorm_add_le`; the weak
  identity is Mathlib's AC integration by parts
  (`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`) with both boundary terms
  zero because `φ` vanishes at `a` and `b`.
- No dependency on any other EX049 task.
-/

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace DGPS.Frontier.EX049

lemma Ioo_subset_uIcc_EX04934 (a b : ℝ) : Ioo a b ⊆ uIcc a b := by
  rcases lt_or_ge a b with h | h
  · rw [uIcc_of_le h.le]; exact Ioo_subset_Icc_self
  · rw [Ioo_eq_empty (not_lt.mpr h)]; exact empty_subset _

lemma deriv_mul_ae_EX04934 {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo a b →
      deriv (fun y => u y * v y) x = deriv u x * v x + u x * deriv v x := by
  filter_upwards [hu.ae_differentiableAt, hv.ae_differentiableAt] with x hx₁ hx₂ hx
  have hx' := Ioo_subset_uIcc_EX04934 a b hx
  exact ((hx₁ hx').hasDerivAt.mul (hx₂ hx').hasDerivAt).deriv

lemma exists_bound_EX04934 {u : ℝ → ℝ} {a b : ℝ} (hu : AbsolutelyContinuousOnInterval u a b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Ioo a b, |u x| ≤ M := by
  obtain ⟨C, hC⟩ := hu.exists_bound
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (by simpa using hC x (Ioo_subset_uIcc_EX04934 a b hx) : |u x| ≤ C).trans (le_max_left _ _)⟩

lemma essSup_le_EX04934 {u : ℝ → ℝ} {a b M : ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (Ioo a b))) (hM : ∀ x ∈ Ioo a b, |u x| ≤ M) :
    eLpNorm u ∞ (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal M := by
  rw [eLpNorm_exponent_top hu]
  refine eLpNormEssSup_le_of_ae_bound ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun x hx => by simpa using hM x hx

lemma continuousOn_Ioo_EX04934 {u : ℝ → ℝ} {a b : ℝ} (hu : AbsolutelyContinuousOnInterval u a b) :
    AEStronglyMeasurable u (volume.restrict (Ioo a b)) :=
  (hu.continuousOn.mono (Ioo_subset_uIcc_EX04934 a b)).aestronglyMeasurable measurableSet_Ioo

lemma memLp_mul_EX04934 {f w : ℝ → ℝ} {a b M : ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hw : AEStronglyMeasurable w (volume.restrict (Ioo a b)))
    (hM : ∀ x ∈ Ioo a b, |w x| ≤ M) :
    MemLp (fun x => f x * w x) 2 (volume.restrict (Ioo a b)) := by
  refine hf.of_le_mul (c := M) (hf.aestronglyMeasurable.mul hw) ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Filter.Eventually.of_forall fun x hx => ?_
  rw [norm_mul, mul_comm]
  gcongr
  simpa using hM x hx

lemma eLpNorm_mul_le_EX04934 {f w : ℝ → ℝ} {a b : ℝ}
    (hw : AEStronglyMeasurable w (volume.restrict (Ioo a b))) :
    eLpNorm (fun x => f x * w x) 2 (volume.restrict (Ioo a b)) ≤
      eLpNorm w ∞ (volume.restrict (Ioo a b)) * eLpNorm f 2 (volume.restrict (Ioo a b)) := by
  have h2 : (fun x => f x * w x) = w • f := by ext x; simp [mul_comm]
  rw [h2]
  exact eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm 2 hw

lemma weak_identity_EX04934 {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo a b) :
    ∫ x in Ioo a b, (u x * v x) * deriv φ x =
      -∫ x in Ioo a b, (deriv u x * v x + u x * deriv v x) * φ x := by
  rcases lt_or_ge a b with hab | hab
  swap
  · rw [Ioo_eq_empty (not_lt.mpr hab)]; simp
  have hAC : AbsolutelyContinuousOnInterval (fun x => u x * v x) a b := hu.fun_mul hv
  have hφAC : AbsolutelyContinuousOnInterval φ a b :=
    ((hφ.of_le (by exact_mod_cast le_top)).contDiffOn).absolutelyContinuousOnInterval
  have hφa : φ a = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => lt_irrefl a (hs h).1
  have hφb : φ b = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => lt_irrefl b (hs h).2
  have key := hAC.integral_mul_deriv_eq_deriv_mul hφAC
  rw [hφa, hφb] at key
  simp only [mul_zero, sub_zero, zero_sub] at key
  have e2 : ∫ x in Ioo a b, deriv (fun y => u y * v y) x * φ x =
      ∫ x in Ioo a b, (deriv u x * v x + u x * deriv v x) * φ x := by
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioo).mpr ?_)
    filter_upwards [deriv_mul_ae_EX04934 hu hv] with x hx hxm
    rw [hx hxm]
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, e2] at key
  exact key

theorem ex049_34_ac_products_h1_bounds_interval {u v : ℝ → ℝ} {a b : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hu' : MemLp (deriv u) 2 (volume.restrict (Ioo a b)))
    (hv' : MemLp (deriv v) 2 (volume.restrict (Ioo a b))) :
    AbsolutelyContinuousOnInterval (fun x => u x * v x) a b ∧
    (∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo a b →
      deriv (fun y => u y * v y) x = deriv u x * v x + u x * deriv v x) ∧
    MemLp (deriv fun y => u y * v y) 2 (volume.restrict (Ioo a b)) ∧
    eLpNorm (deriv fun y => u y * v y) 2 (volume.restrict (Ioo a b)) ≤
      eLpNorm v ∞ (volume.restrict (Ioo a b)) * eLpNorm (deriv u) 2 (volume.restrict (Ioo a b)) +
      eLpNorm u ∞ (volume.restrict (Ioo a b)) * eLpNorm (deriv v) 2 (volume.restrict (Ioo a b)) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, (u x * v x) * deriv φ x =
        -∫ x in Ioo a b, (deriv u x * v x + u x * deriv v x) * φ x := by
  obtain ⟨Mu, -, hMu⟩ := exists_bound_EX04934 hu
  obtain ⟨Mv, -, hMv⟩ := exists_bound_EX04934 hv
  have hae : deriv (fun y => u y * v y) =ᵐ[volume.restrict (Ioo a b)]
      fun x => deriv u x * v x + u x * deriv v x :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (deriv_mul_ae_EX04934 hu hv)
  have h1 : MemLp (fun x => deriv u x * v x) 2 (volume.restrict (Ioo a b)) :=
    memLp_mul_EX04934 hu' (continuousOn_Ioo_EX04934 hv) hMv
  have h2 : MemLp (fun x => deriv v x * u x) 2 (volume.restrict (Ioo a b)) :=
    memLp_mul_EX04934 hv' (continuousOn_Ioo_EX04934 hu) hMu
  have h2' : (fun x => deriv v x * u x) = fun x => u x * deriv v x := by
    funext x; exact mul_comm _ _
  rw [h2'] at h2
  have hsum : MemLp (fun x => deriv u x * v x + u x * deriv v x) 2
      (volume.restrict (Ioo a b)) := h1.add h2
  refine ⟨hu.fun_mul hv, deriv_mul_ae_EX04934 hu hv, hsum.ae_eq hae.symm, ?_, ?_⟩
  · rw [eLpNorm_congr_ae hae]
    calc eLpNorm (fun x => deriv u x * v x + u x * deriv v x) 2 (volume.restrict (Ioo a b))
        ≤ eLpNorm (fun x => deriv u x * v x) 2 (volume.restrict (Ioo a b)) +
          eLpNorm (fun x => u x * deriv v x) 2 (volume.restrict (Ioo a b)) :=
          eLpNorm_add_le (f := fun x => deriv u x * v x) (g := fun x => u x * deriv v x) one_le_two
      _ ≤ _ := by
          gcongr
          · exact eLpNorm_mul_le_EX04934 (continuousOn_Ioo_EX04934 hv)
          · have h3 := eLpNorm_mul_le_EX04934 (f := deriv v) (continuousOn_Ioo_EX04934 hu)
            simpa only [mul_comm] using h3
  · intro φ hφ _ hs
    exact weak_identity_EX04934 hu hv hφ hs

theorem ex049_34_ac_products_h1_bounds_interval_real {u v : ℝ → ℝ} {a b Mu Mv : ℝ}
    (hu : AbsolutelyContinuousOnInterval u a b) (hv : AbsolutelyContinuousOnInterval v a b)
    (hu' : MemLp (deriv u) 2 (volume.restrict (Ioo a b)))
    (hv' : MemLp (deriv v) 2 (volume.restrict (Ioo a b)))
    (hMu : ∀ x ∈ Icc a b, |u x| ≤ Mu) (hMv : ∀ x ∈ Icc a b, |v x| ≤ Mv) :
    (eLpNorm (deriv fun y => u y * v y) 2 (volume.restrict (Ioo a b))).toReal ≤
      Mv * (eLpNorm (deriv u) 2 (volume.restrict (Ioo a b))).toReal +
      Mu * (eLpNorm (deriv v) 2 (volume.restrict (Ioo a b))).toReal := by
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Ioo_eq_empty (not_lt.mpr hab.le)]
    simp
  have hMu0 : 0 ≤ Mu := (abs_nonneg _).trans (hMu a ⟨le_rfl, hab⟩)
  have hMv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv a ⟨le_rfl, hab⟩)
  obtain ⟨-, -, -, hnorm, -⟩ := ex049_34_ac_products_h1_bounds_interval hu hv hu' hv'
  have e1 : eLpNorm v ∞ (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal Mv :=
    essSup_le_EX04934 (continuousOn_Ioo_EX04934 hv) fun x hx => hMv x (Ioo_subset_Icc_self hx)
  have e2 : eLpNorm u ∞ (volume.restrict (Ioo a b)) ≤ ENNReal.ofReal Mu :=
    essSup_le_EX04934 (continuousOn_Ioo_EX04934 hu) fun x hx => hMu x (Ioo_subset_Icc_self hx)
  have hfin : ENNReal.ofReal Mv * eLpNorm (deriv u) 2 (volume.restrict (Ioo a b)) +
      ENNReal.ofReal Mu * eLpNorm (deriv v) 2 (volume.restrict (Ioo a b)) ≠ (⊤ : ℝ≥0∞) :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu'.eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv'.eLpNorm_ne_top⟩
  have h := ENNReal.toReal_mono hfin (hnorm.trans (by gcongr))
  rwa [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu'.eLpNorm_ne_top)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv'.eLpNorm_ne_top), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hMv0, ENNReal.toReal_ofReal hMu0] at h

end DGPS.Frontier.EX049
