import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Remote critical points persist by contraction (RUF024)

For `f g : E → ℝ` of class `C²` on a finite-dimensional real inner product space, a point `a`
with `Hinv` a right inverse (via the Riesz map) of `D²f(a)`, a ball on which both Hessian
perturbations are at most `1 / (4 ‖Hinv‖)`, and a small Newton displacement
`‖Hinv ∇g(a)‖ ≤ r / 2`, the map `t ↦ t - Hinv ∇g(t)` contracts the closed ball. Hence `g` has a
unique critical point there, within `2 ‖Hinv ∇g(a)‖` of `a`, and its Hessian has the same
inertia (`sigPos`, `sigNeg`) as `D²f(a)`.
-/

namespace DGPS.Examples.RoughBoundary.Landscape

open Module

section quad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form `x ↦ B x x` of a continuous bilinear form. -/
def hessQuad (B : E →L[ℝ] E →L[ℝ] ℝ) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap
    (LinearMap.mk₂ ℝ (fun x y => B x y) (fun x₁ x₂ y => by simp) (fun c x y => by simp)
      (fun x y₁ y₂ => by simp) (fun c x y => by simp))

lemma hessQuad_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) : hessQuad B x = B x x := rfl

end quad

section grad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz map as a real continuous linear map. -/
noncomputable def rieszL : StrongDual ℝ E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun φ => (InnerProductSpace.toDual ℝ E).symm φ
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by simp } 1 (fun φ => by simp)

lemma gradient_eq_rieszL (g : E → ℝ) : gradient g = fun t => rieszL (fderiv ℝ g t) := rfl

lemma inner_rieszL (φ : StrongDual ℝ E) (k : E) : inner ℝ (rieszL φ) k = φ k :=
  InnerProductSpace.toDual_symm_apply

lemma hessian_gradient {g : E → ℝ} (hg : ContDiff ℝ 2 g) (t : E) :
    DifferentiableAt ℝ (gradient g) t ∧
      ∀ h k, inner ℝ (fderiv ℝ (gradient g) t h) k = fderiv ℝ (fderiv ℝ g) t h k := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) t :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) t
  have hG : HasFDerivAt (gradient g) (rieszL.comp (fderiv ℝ (fderiv ℝ g) t)) t := by
    rw [gradient_eq_rieszL]
    exact rieszL.hasFDerivAt.comp t hd.hasFDerivAt
  refine ⟨hG.differentiableAt, fun h k => ?_⟩
  have h1 := hG.inner ℝ (hasFDerivAt_const k t)
  have h2 : HasFDerivAt (fun y => fderiv ℝ g y k)
      ((ContinuousLinearMap.apply ℝ ℝ k).comp (fderiv ℝ (fderiv ℝ g) t)) t :=
    (ContinuousLinearMap.apply ℝ ℝ k).hasFDerivAt.comp t hd.hasFDerivAt
  have e : (fun y => inner ℝ (gradient g y) k) = fun y => fderiv ℝ g y k := by
    funext y; exact inner_rieszL _ _
  rw [show (fun y => inner ℝ (gradient g y) k) = fun y => fderiv ℝ g y k from e] at h1
  have := congrArg (fun L => L h) (h1.unique h2)
  rw [hG.fderiv]
  simpa [fderivInnerCLM_apply] using this

end grad

section fd

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Spectral splitting of a self-adjoint operator all of whose eigenvalues have `|μ| ≥ m > 0`. -/
lemma exists_spectral_split (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (m : ℝ)
    (hm : ∀ (μ : ℝ) (x : E), x ≠ 0 → S x = μ • x → m ≤ |μ|) (hm0 : 0 < m) :
    ∃ Vp Vn : Submodule ℝ E, finrank ℝ Vp + finrank ℝ Vn = finrank ℝ E ∧
      (∀ x ∈ Vp, m * ‖x‖ ^ 2 ≤ inner ℝ (S x) x) ∧
      (∀ x ∈ Vn, inner ℝ (S x) x ≤ -(m * ‖x‖ ^ 2)) := by
  classical
  obtain ⟨b, μ, hSb⟩ : ∃ (b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E) (μ : Fin (finrank ℝ E) → ℝ),
      ∀ i, S (b i) = μ i • b i :=
    ⟨hS.eigenvectorBasis rfl, hS.eigenvalues rfl, fun i => hS.apply_eigenvectorBasis rfl i⟩
  have hbne : ∀ i, b i ≠ 0 := fun i => b.toBasis.ne_zero i
  have hμm : ∀ i, m ≤ |μ i| := fun i => hm _ _ (hbne i) (hSb i)
  have hli := b.orthonormal.linearIndependent
  have hcoef : ∀ x : E, inner ℝ (S x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
    intro x
    have h1 := b.sum_inner_mul_inner (S x) x
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : inner ℝ (S x) (b i) = μ i * inner ℝ x (b i) := by
      rw [hS x, hSb, inner_smul_right]
    rw [this, real_inner_comm x (b i)]; ring
  have hnorm : ∀ x : E, ‖x‖ ^ 2 = ∑ i, (inner ℝ (b i) x) ^ 2 := by
    intro x
    have h1 := b.sum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]; ring
  have hzero : ∀ (P : Fin (finrank ℝ E) → Prop) (x : E),
      x ∈ Submodule.span ℝ (Set.range fun i : {i // P i} => b i.1) →
      ∀ j, ¬ P j → inner ℝ (b j) x = 0 := by
    intro P x hx j hj
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
    rw [inner_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : j ≠ i.1 := by rintro rfl; exact hj i.2
    rw [inner_smul_right, b.inner_eq_ite]; simp [hne]
  refine ⟨Submodule.span ℝ (Set.range fun i : {i // 0 < μ i} => b i.1),
    Submodule.span ℝ (Set.range fun i : {i // ¬ 0 < μ i} => b i.1), ?_, ?_, ?_⟩
  · have e1 : finrank ℝ (Submodule.span ℝ (Set.range fun i : {i // 0 < μ i} => b i.1)) =
        Fintype.card {i // 0 < μ i} := finrank_span_eq_card (hli.comp _ Subtype.val_injective)
    have e2 : finrank ℝ (Submodule.span ℝ (Set.range fun i : {i // ¬ 0 < μ i} => b i.1)) =
        Fintype.card {i // ¬ 0 < μ i} := finrank_span_eq_card (hli.comp _ Subtype.val_injective)
    rw [e1, e2, Fintype.card_subtype_compl]
    have : Fintype.card {i : Fin (finrank ℝ E) // 0 < μ i} ≤ Fintype.card (Fin (finrank ℝ E)) :=
      Fintype.card_subtype_le _
    simp only [Fintype.card_fin] at this ⊢
    omega
  · intro x hx
    rw [hcoef, hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : 0 < μ i
    · have := hμm i
      rw [abs_of_pos hi] at this
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    · have h0 := hzero (fun j => 0 < μ j) x hx i hi
      rw [h0]; simp
  · intro x hx
    rw [hcoef, hnorm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : 0 < μ i
    · have h0 := hzero (fun j => ¬ 0 < μ j) x hx i (not_not.2 hi)
      rw [h0]; simp
    · have hneg : μ i < 0 := lt_of_le_of_ne (not_lt.1 hi) (fun h => by
        have := hμm i; rw [h, abs_zero] at this; linarith)
      have := hμm i
      rw [abs_of_neg hneg] at this
      nlinarith [sq_nonneg (inner ℝ (b i) x)]


/-- Perturbation lemma for the signature of a quadratic form. -/
lemma sigPos_eq_of_perturb (Q Q0 : QuadraticForm ℝ E) (Vp Vn : Submodule ℝ E) (m : ℝ)
    (hm : 0 < m) (hsum : finrank ℝ Vp + finrank ℝ Vn = finrank ℝ E)
    (hp : ∀ x ∈ Vp, m * ‖x‖ ^ 2 ≤ Q0 x) (hn : ∀ x ∈ Vn, Q0 x ≤ -(m * ‖x‖ ^ 2))
    (hd : ∀ x, |Q x - Q0 x| ≤ m / 2 * ‖x‖ ^ 2) :
    sigPos Q = finrank ℝ Vp := by
  apply le_antisymm
  · have h1 : sigPos Q + finrank ℝ Vn ≤ finrank ℝ E :=
      QuadraticForm.sigPos_add_finrank_le_of_nonpos (fun x hx => by
        have h2 := hn x hx
        have h3 := (abs_le.1 (hd x)).2
        nlinarith [sq_nonneg ‖x‖])
    omega
  · refine le_sigPos_of_posDef Q (V := Vp) ?_
    intro x hx
    rw [QuadraticMap.restrict_apply]
    have h0 : x.1 ≠ 0 := fun h => hx (Subtype.ext h)
    have h2 := hp x.1 x.2
    have h3 := (abs_le.1 (hd x.1)).1
    have h4 : 0 < ‖x.1‖ ^ 2 := by positivity
    nlinarith


open Metric in
/-- Derivative estimate for the contraction `T_P(t) = t - H_a⁻¹ ∇Ψ_P(t)`. -/
lemma contraction_derivative_bound {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (a : E) (Hinv : E →L[ℝ] E)
    (hHinvS : ∀ v, Hinv (fderiv ℝ (gradient f) a v) = v) (t : E)
    (hΔ : ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a‖ ≤ 1 / (2 * ‖Hinv‖)) (h : E) :
    ‖h - Hinv (fderiv ℝ (gradient g) t h)‖ ≤ 1 / 2 * ‖h‖ := by
  set u : E := fderiv ℝ (gradient f) a h - fderiv ℝ (gradient g) t h with hu
  have hinner : ∀ k, inner ℝ u k =
      -((fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a) h k) := by
    intro k
    rw [hu, inner_sub_left, (hessian_gradient hf a).2, (hessian_gradient hg t).2]
    simp
  have hu_le : ‖u‖ ≤ ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a‖ * ‖h‖ := by
    have h1 : ‖u‖ ^ 2 ≤ ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a‖ * ‖h‖ * ‖u‖ := by
      have h2 : inner ℝ u u = -((fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a) h u) :=
        hinner u
      rw [real_inner_self_eq_norm_sq] at h2
      rw [h2]
      calc -((fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a) h u)
          ≤ ‖(fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a) h u‖ := neg_le_abs _
        _ ≤ ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a‖ * ‖h‖ * ‖u‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
    by_cases hu0 : ‖u‖ = 0
    · rw [hu0]; positivity
    · have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
      nlinarith
  have hdt : h - Hinv (fderiv ℝ (gradient g) t h) = Hinv u := by
    rw [hu, map_sub, hHinvS]
  rw [hdt]
  calc ‖Hinv u‖ ≤ ‖Hinv‖ * ‖u‖ := Hinv.le_opNorm u
    _ ≤ ‖Hinv‖ * (1 / (2 * ‖Hinv‖) * ‖h‖) := by
        gcongr
        exact hu_le.trans (by gcongr)
    _ ≤ 1 / 2 * ‖h‖ := by
        rcases eq_or_lt_of_le (norm_nonneg Hinv) with h0 | h0
        · rw [← h0, zero_mul]; positivity
        · have : ‖Hinv‖ * (1 / (2 * ‖Hinv‖) * ‖h‖) = 1 / 2 * ‖h‖ := by
            field_simp
          rw [this]

open Metric in
/-- **RUF024, remote critical points persist by contraction.**

Let `f = Ψ∞` and `g = Ψ_P` be `C²` on a finite-dimensional real inner product space, `a` a point
at which the Hessian `H_a = D²f(a)` is invertible with inverse `Hinv` (`A_a = ‖Hinv‖`), and `r`
a radius such that on `B̄(a, r)`: `‖D²f - H_a‖ ≤ 1/(4 A_a)` and `‖D²g - D²f‖ ≤ 1/(4 A_a)`, and
`‖Hinv ∇g(a)‖ ≤ r/2`.  Then the ball contains exactly one critical point `a_P` of `g`,
`‖a_P - a‖ ≤ 2 ‖Hinv ∇g(a)‖`, and the Hessian of `g` at `a_P` has the same inertia
(`sigPos`, `sigNeg` of the Hessian quadratic form, Mathlib's signature) as `H_a`. -/
theorem remote_critical_points_persist_by_contraction
    (f g : E → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (a : E) (r : ℝ) (hr : 0 < r)
    (Hinv : E →L[ℝ] E)
    (hHinv : ∀ v w, fderiv ℝ (fderiv ℝ f) a (Hinv v) w = inner ℝ v w)
    (hfball : ∀ x ∈ closedBall a r,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) a‖ ≤ 1 / (4 * ‖Hinv‖))
    (hgball : ∀ x ∈ closedBall a r,
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ 1 / (4 * ‖Hinv‖))
    (hdisp : ‖Hinv (gradient g a)‖ ≤ r / 2) :
    ∃ aP : E, (aP ∈ closedBall a r ∧ fderiv ℝ g aP = 0 ∧
        ∀ x ∈ closedBall a r, fderiv ℝ g x = 0 → x = aP) ∧
      ‖aP - a‖ ≤ 2 * ‖Hinv (gradient g a)‖ ∧
      sigPos (hessQuad (fderiv ℝ (fderiv ℝ g) aP)) = sigPos (hessQuad (fderiv ℝ (fderiv ℝ f) a)) ∧
      sigNeg (hessQuad (fderiv ℝ (fderiv ℝ g) aP)) = sigNeg (hessQuad (fderiv ℝ (fderiv ℝ f) a)) := by
  have _ := hr
  -- the Hessian operator `S` of `f` at `a` and its inverse
  have hSinv : ∀ v, fderiv ℝ (gradient f) a (Hinv v) = v := by
    intro v
    refine ext_inner_right ℝ fun w => ?_
    rw [(hessian_gradient hf a).2, hHinv]
  have hHinvS : ∀ v, Hinv (fderiv ℝ (gradient f) a v) = v := by
    have h1 : ((fderiv ℝ (gradient f) a : E →L[ℝ] E) : E →ₗ[ℝ] E) *
        (Hinv : E →ₗ[ℝ] E) = 1 := LinearMap.ext hSinv
    have h2 := mul_eq_one_comm.1 h1
    exact fun v => LinearMap.congr_fun h2 v
  have hΔ : ∀ t ∈ closedBall a r,
      ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) a‖ ≤ 1 / (2 * ‖Hinv‖) := by
    intro t ht
    have h1 := hfball t ht
    have h2 := hgball t ht
    refine (norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) t)
      (fderiv ℝ (fderiv ℝ f) t) (fderiv ℝ (fderiv ℝ f) a)).trans ?_
    have : 1 / (4 * ‖Hinv‖) + 1 / (4 * ‖Hinv‖) = 1 / (2 * ‖Hinv‖) := by
      rcases eq_or_lt_of_le (norm_nonneg Hinv) with h0 | h0
      · rw [← h0]; simp
      · field_simp; norm_num
    linarith
  -- the contraction
  set T : E → E := fun t => t - Hinv (gradient g t) with hT
  have hTderiv : ∀ t, HasFDerivAt T
      (ContinuousLinearMap.id ℝ E - Hinv.comp (fderiv ℝ (gradient g) t)) t := fun t =>
    (hasFDerivAt_id t).sub (Hinv.hasFDerivAt.comp t (hessian_gradient hg t).1.hasFDerivAt)
  have hTlip : ∀ x ∈ closedBall a r, ∀ y ∈ closedBall a r, ‖T x - T y‖ ≤ 1 / 2 * ‖x - y‖ := by
    intro x hx y hy
    have := (convex_closedBall a r).norm_image_sub_le_of_norm_fderiv_le
      (f := T) (C := 1 / 2) (fun t _ => (hTderiv t).differentiableAt)
      (fun t ht => by
        rw [(hTderiv t).fderiv]
        refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
        simpa using contraction_derivative_bound hf hg a Hinv hHinvS t (hΔ t ht) h) hy hx
    simpa [norm_sub_rev] using this
  have haball : a ∈ closedBall a r := mem_closedBall_self (by linarith [norm_nonneg (Hinv (gradient g a))])
  have hTmaps : Set.MapsTo T (closedBall a r) (closedBall a r) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hTlip x hx a haball
    have h2 : ‖T a - a‖ ≤ r / 2 := by
      have : T a - a = -Hinv (gradient g a) := by simp [hT]
      rw [this, norm_neg]; exact hdisp
    have h3 : ‖x - a‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hx
    calc ‖T x - a‖ = ‖(T x - T a) + (T a - a)‖ := by congr 1; abel
      _ ≤ ‖T x - T a‖ + ‖T a - a‖ := norm_add_le _ _
      _ ≤ 1 / 2 * ‖x - a‖ + r / 2 := add_le_add h1 h2
      _ ≤ r := by linarith
  have hcontr : ContractingWith (1 / 2 : NNReal) (hTmaps.restrict T (closedBall a r) (closedBall a r)) := by
    refine ⟨by rw [NNReal.coe_lt_coe.symm]; norm_num, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
    have := hTlip x.1 x.2 y.1 y.2
    simpa using this
  obtain ⟨aP, haP, hfix, -, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hTmaps
    haball (edist_ne_top _ _)
  have hGzero : ∀ x, gradient g x = 0 ↔ fderiv ℝ g x = 0 := by
    intro x
    show rieszL (fderiv ℝ g x) = 0 ↔ _
    constructor
    · intro h
      ext k
      rw [← inner_rieszL, h]; simp
    · intro h; simp [h]
  have hcrit : ∀ x, fderiv ℝ g x = 0 ↔ T x = x := by
    intro x
    have hT' : T x = x ↔ Hinv (gradient g x) = 0 := by simp [hT]
    rw [hT', ← hGzero]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := hSinv (gradient g x)
      rw [h, map_zero] at this
      exact this.symm
  have hunique : ∀ x ∈ closedBall a r, T x = x → x = aP := by
    intro x hx hxf
    have h1 := hTlip x hx aP haP
    rw [hxf, hfix.eq] at h1
    have : ‖x - aP‖ ≤ 0 := by linarith [norm_nonneg (x - aP)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 this)
  have hbound : ‖aP - a‖ ≤ 2 * ‖Hinv (gradient g a)‖ := by
    have h1 := hTlip aP haP a haball
    have h2 : aP - a = (T aP - T a) + (T a - a) := by rw [hfix.eq]; abel
    have h3 : ‖T a - a‖ = ‖Hinv (gradient g a)‖ := by
      have : T a - a = -Hinv (gradient g a) := by simp [hT]
      rw [this, norm_neg]
    have h5 : ‖aP - a‖ ≤ ‖T aP - T a‖ + ‖T a - a‖ := by
      calc ‖aP - a‖ = ‖(T aP - T a) + (T a - a)‖ := by rw [← h2]
        _ ≤ _ := norm_add_le _ _
    linarith
  refine ⟨aP, ⟨haP, (hcrit aP).2 hfix.eq, fun x hx hc => hunique x hx ((hcrit x).1 hc)⟩,
    hbound, ?_⟩
  -- inertia
  have hdiff : ∀ x : E, |fderiv ℝ (fderiv ℝ g) aP x x - fderiv ℝ (fderiv ℝ f) a x x| ≤
      1 / (2 * ‖Hinv‖) * ‖x‖ ^ 2 := by
    intro x
    have h1 : fderiv ℝ (fderiv ℝ g) aP x x - fderiv ℝ (fderiv ℝ f) a x x =
        (fderiv ℝ (fderiv ℝ g) aP - fderiv ℝ (fderiv ℝ f) a) x x := rfl
    rw [h1, ← Real.norm_eq_abs]
    calc ‖(fderiv ℝ (fderiv ℝ g) aP - fderiv ℝ (fderiv ℝ f) a) x x‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) aP - fderiv ℝ (fderiv ℝ f) a‖ * ‖x‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ 1 / (2 * ‖Hinv‖) * ‖x‖ * ‖x‖ := by gcongr; exact hΔ aP haP
      _ = 1 / (2 * ‖Hinv‖) * ‖x‖ ^ 2 := by ring
  rcases eq_or_lt_of_le (norm_nonneg Hinv) with h0 | hA
  · have hsub : Subsingleton E := by
      refine ⟨fun x y => ?_⟩
      have hz : Hinv = 0 := norm_eq_zero.1 h0.symm
      rw [← hSinv x, ← hSinv y, hz]; simp
    have : hessQuad (fderiv ℝ (fderiv ℝ g) aP) = hessQuad (fderiv ℝ (fderiv ℝ f) a) := by
      ext x
      rw [Subsingleton.elim x 0]; simp
    rw [this]; exact ⟨rfl, rfl⟩
  · have hsymm : (fderiv ℝ (gradient f) a : E →ₗ[ℝ] E).IsSymmetric := by
      intro x y
      have hs := (hf.contDiffAt (x := a)).isSymmSndFDerivAt (by simp)
      show inner ℝ (fderiv ℝ (gradient f) a x) y = inner ℝ x (fderiv ℝ (gradient f) a y)
      rw [(hessian_gradient hf a).2, real_inner_comm, (hessian_gradient hf a).2]
      exact hs x y
    have hm : ∀ (μ : ℝ) (x : E), x ≠ 0 → (fderiv ℝ (gradient f) a : E →ₗ[ℝ] E) x = μ • x →
        1 / ‖Hinv‖ ≤ |μ| := by
      intro μ x hx hμ
      have h1 : x = μ • Hinv x := by
        have := hHinvS x
        simp only [ContinuousLinearMap.coe_coe] at hμ
        rw [hμ, map_smul] at this
        exact this.symm
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h2 : ‖x‖ ≤ |μ| * (‖Hinv‖ * ‖x‖) := by
        calc ‖x‖ = ‖μ • Hinv x‖ := by rw [← h1]
          _ = |μ| * ‖Hinv x‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |μ| * (‖Hinv‖ * ‖x‖) := by gcongr; exact Hinv.le_opNorm x
      rw [div_le_iff₀ hA]
      nlinarith
    have hm0 : 0 < 1 / ‖Hinv‖ := one_div_pos.2 hA
    obtain ⟨Vp, Vn, hsum, hp, hn⟩ := exists_spectral_split
      (fderiv ℝ (gradient f) a : E →ₗ[ℝ] E) hsymm (1 / ‖Hinv‖) hm hm0
    have hinner : ∀ x : E, inner ℝ (fderiv ℝ (gradient f) a x) x =
        hessQuad (fderiv ℝ (fderiv ℝ f) a) x := fun x => (hessian_gradient hf a).2 x x
    have hp' : ∀ x ∈ Vp, 1 / ‖Hinv‖ * ‖x‖ ^ 2 ≤ hessQuad (fderiv ℝ (fderiv ℝ f) a) x := by
      intro x hx; rw [← hinner]; exact hp x hx
    have hn' : ∀ x ∈ Vn, hessQuad (fderiv ℝ (fderiv ℝ f) a) x ≤ -(1 / ‖Hinv‖ * ‖x‖ ^ 2) := by
      intro x hx; rw [← hinner]; exact hn x hx
    have hm2 : 1 / ‖Hinv‖ / 2 = 1 / (2 * ‖Hinv‖) := by field_simp
    have hd1 : ∀ x : E, |hessQuad (fderiv ℝ (fderiv ℝ g) aP) x -
        hessQuad (fderiv ℝ (fderiv ℝ f) a) x| ≤ 1 / ‖Hinv‖ / 2 * ‖x‖ ^ 2 := by
      intro x; rw [hm2]; exact hdiff x
    have hd0 : ∀ x : E, |hessQuad (fderiv ℝ (fderiv ℝ f) a) x -
        hessQuad (fderiv ℝ (fderiv ℝ f) a) x| ≤ 1 / ‖Hinv‖ / 2 * ‖x‖ ^ 2 := by
      intro x; rw [sub_self, abs_zero]; positivity
    have hsum' : finrank ℝ Vn + finrank ℝ Vp = finrank ℝ E := by omega
    have hpn' : ∀ x ∈ Vn, 1 / ‖Hinv‖ * ‖x‖ ^ 2 ≤ (-hessQuad (fderiv ℝ (fderiv ℝ f) a)) x := by
      intro x hx; rw [neg_apply]; linarith [hn' x hx]
    have hnp' : ∀ x ∈ Vp, (-hessQuad (fderiv ℝ (fderiv ℝ f) a)) x ≤ -(1 / ‖Hinv‖ * ‖x‖ ^ 2) := by
      intro x hx; rw [neg_apply]; linarith [hp' x hx]
    have hdn1 : ∀ x : E, |(-hessQuad (fderiv ℝ (fderiv ℝ g) aP)) x -
        (-hessQuad (fderiv ℝ (fderiv ℝ f) a)) x| ≤ 1 / ‖Hinv‖ / 2 * ‖x‖ ^ 2 := by
      intro x
      simp only [neg_apply]
      rw [show -hessQuad (fderiv ℝ (fderiv ℝ g) aP) x - -hessQuad (fderiv ℝ (fderiv ℝ f) a) x =
        -(hessQuad (fderiv ℝ (fderiv ℝ g) aP) x - hessQuad (fderiv ℝ (fderiv ℝ f) a) x) by ring,
        abs_neg]
      exact hd1 x
    have hdn0 : ∀ x : E, |(-hessQuad (fderiv ℝ (fderiv ℝ f) a)) x -
        (-hessQuad (fderiv ℝ (fderiv ℝ f) a)) x| ≤ 1 / ‖Hinv‖ / 2 * ‖x‖ ^ 2 := by
      intro x; rw [sub_self, abs_zero]; positivity
    refine ⟨?_, ?_⟩
    · rw [sigPos_eq_of_perturb _ _ Vp Vn _ hm0 hsum hp' hn' hd1,
        sigPos_eq_of_perturb _ _ Vp Vn _ hm0 hsum hp' hn' hd0]
    · rw [← sigPos_neg, ← sigPos_neg,
        sigPos_eq_of_perturb _ _ Vn Vp _ hm0 hsum' hpn' hnp' hdn1,
        sigPos_eq_of_perturb _ _ Vn Vp _ hm0 hsum' hpn' hnp' hdn0]

end fd

end DGPS.Examples.RoughBoundary.Landscape
