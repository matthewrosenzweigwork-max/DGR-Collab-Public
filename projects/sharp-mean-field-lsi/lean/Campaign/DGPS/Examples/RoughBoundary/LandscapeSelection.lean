import DGPS.Examples.RoughBoundary.LandscapeMargins
import DGPS.Examples.RoughBoundary.LandscapeDerivatives
import DGPS.Examples.RoughBoundary.SymmetryRetention
import DGPS.Examples.RoughBoundary.LandscapePositivity
import DGPS.Examples.RoughBoundary.FeatureMoments

/-!
# RUF026: common finite parameter selection

Inputs: RUF021 (`compact_uniform_convergence_of_parameter_derivatives`), RUF023
(`global_three_region_positivity_persists`), RUF025
(`critical_value_margins_and_exact_rotated_triples`) and RUF006
(`exact_shift_symmetries_and_feature_moments`).  The limit landscape `Ψ∞` supplies explicit
nondegenerate remote critical orbits (`limit_data`); a tolerance `η` is chosen enforcing the
C⁰/C¹/C² margins of RUF023/RUF025, then `ε₀` and `L₀` by RUF021.  The conclusion is stored as
the proved predicate `RoughLandscapeCertificate`.
-/

namespace DGPS.Examples.RoughBoundary.Landscape

open MeasureTheory Set Metric
open scoped ContDiff Real
open DGPS.Examples.RoughBoundary.ThreeState DGPS.Examples.RoughBoundary.Feature

lemma rot120_eq (x : E2) :
    rot120 x = !₂[-(1 / 2) * x 0 - √3 / 2 * x 1, √3 / 2 * x 0 - 1 / 2 * x 1] := by
  have a : 2 * π / 3 = π - π / 3 := by ring
  have hc : Real.cos (2 * π / 3) = -(1 / 2) := by
    rw [a, Real.cos_pi_sub, Real.cos_pi_div_three]
  have hs : Real.sin (2 * π / 3) = √3 / 2 := by
    rw [a, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp only [rot120, hc, hs]
  congr 2
  all_goals (try norm_num); try ring

lemma rot120_cube (x : E2) : rot120 (rot120 (rot120 x)) = x := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i
  · simp [rot120_eq]
    linear_combination (3 / 8 * x.ofLp 0 + √3 / 8 * x.ofLp 1) * h3
  · simp [rot120_eq]
    linear_combination (-√3 / 8 * x.ofLp 0 + 3 / 8 * x.ofLp 1) * h3

lemma rot120_vertex (i : Fin 3) : rot120 (vertex i) = vertex (i + 1) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · show rot120 (vertex 0) = vertex 1
    rw [vertex_zero, vertex_one, rot120_eq]
    simp
    norm_num
  · show rot120 (vertex 1) = vertex 2
    rw [vertex_two, vertex_one, rot120_eq]
    ext j
    fin_cases j
    · simp; linear_combination (-1 / 4) * h3
    · simp; ring
  · show rot120 (vertex 2) = vertex 0
    rw [vertex_zero, vertex_two, rot120_eq]
    ext j
    fin_cases j
    · simp; linear_combination (1 / 4) * h3
    · simp; ring

lemma logPartition_rot (t : E2) : logPartition (rot120 t) = logPartition t := by
  unfold logPartition
  congr 2
  have h : ∀ i : Fin 3, inner ℝ (rot120 t) (vertex (i + 1)) = inner ℝ t (vertex i) := by
    intro i
    rw [← rot120_vertex, Semicontinuity.inner_rot120]
  calc ∑ i, Real.exp (inner ℝ (rot120 t) (vertex i))
      = ∑ i, Real.exp (inner ℝ (rot120 t) (vertex (i + 1))) :=
        (Equiv.sum_comp (Equiv.addRight (1 : Fin 3))
          (fun i => Real.exp (inner ℝ (rot120 t) (vertex i)))).symm
    _ = _ := by simp only [h]

lemma orderPotential_rot (t : E2) : orderPotential (rot120 t) = orderPotential t := by
  unfold orderPotential
  rw [logPartition_rot, Semicontinuity.norm_rot120]

lemma exists_hinv (B : E2 →L[ℝ] E2 →L[ℝ] ℝ) (hB : ∀ v, (∀ w, B v w = 0) → v = 0) :
    ∃ H : E2 →L[ℝ] E2, ∀ v w, B (H v) w = inner ℝ v w := by
  let φ : E2 →ₗ[ℝ] E2 := (rieszL : StrongDual ℝ E2 →L[ℝ] E2).toLinearMap ∘ₗ B.toLinearMap
  have hφ : ∀ v w, inner ℝ (φ v) w = B v w := fun v w => inner_rieszL (B v) w
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine hB v fun w => ?_
    rw [← hφ, hv]; simp
  let e := LinearEquiv.ofInjectiveEndo φ hinj
  refine ⟨LinearMap.toContinuousLinearMap e.symm.toLinearMap, fun v w => ?_⟩
  rw [← hφ]
  have : φ (LinearMap.toContinuousLinearMap e.symm.toLinearMap v) = v := e.apply_symm_apply v
  simp only [this]

lemma hessian_rot {g : E2 → ℝ} (hg : ContDiff ℝ 2 g) (hsym : ∀ x, g (rot120 x) = g x)
    (x v w : E2) :
    fderiv ℝ (fderiv ℝ g) (rot120 x) (rot120 v) (rot120 w) = fderiv ℝ (fderiv ℝ g) x v w := by
  have hdiff : ∀ y, DifferentiableAt ℝ (fderiv ℝ g) y := fun y =>
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have hF : ∀ y, (fderiv ℝ g (rot120CL y)).comp rot120CL = fderiv ℝ g y := by
    intro y
    have hd : DifferentiableAt ℝ g (rot120CL y) := (hg.differentiable (by norm_num)) _
    have hc : fderiv ℝ (g ∘ rot120CL) y = (fderiv ℝ g (rot120CL y)).comp rot120CL :=
      fderiv_comp y hd rot120CL.differentiableAt |>.trans (by rw [rot120CL.fderiv])
    have hgc : g ∘ rot120CL = g := funext hsym
    rw [hgc] at hc
    exact hc.symm
  let P : (E2 →L[ℝ] ℝ) →L[ℝ] (E2 →L[ℝ] ℝ) := (ContinuousLinearMap.compL ℝ E2 E2 ℝ).flip rot120CL
  have hP : ∀ φ, P φ = φ.comp rot120CL := fun φ => rfl
  have h1 : HasFDerivAt (fun y => P (fderiv ℝ g (rot120CL y)))
      (P.comp ((fderiv ℝ (fderiv ℝ g) (rot120CL x)).comp rot120CL)) x :=
    P.hasFDerivAt.comp x ((hdiff _).hasFDerivAt.comp x rot120CL.hasFDerivAt)
  have h2 : (fun y => P (fderiv ℝ g (rot120CL y))) = fderiv ℝ g :=
    funext fun y => by rw [hP]; exact hF y
  rw [h2] at h1
  have h3 := congrArg (fun L => L v w) h1.fderiv
  simpa [hP, rot120CL_apply] using h3.symm

lemma hinv_norm_pos {B : E2 →L[ℝ] E2 →L[ℝ] ℝ} {H : E2 →L[ℝ] E2}
    (hH : ∀ v w, B (H v) w = inner ℝ v w) : 0 < ‖H‖ := by
  rcases (norm_nonneg H).eq_or_lt with h0 | h0
  · exfalso
    have : H = 0 := norm_eq_zero.1 h0.symm
    have h1 := hH (vertex 0) (vertex 0)
    rw [this] at h1
    simp [norm_vertex] at h1
  · exact h0

lemma hinv_rot {g : E2 → ℝ} (hg : ContDiff ℝ 2 g) (hsym : ∀ x, g (rot120 x) = g x) (x : E2)
    (H : E2 →L[ℝ] E2) (hH : ∀ v w, fderiv ℝ (fderiv ℝ g) x (H v) w = inner ℝ v w) :
    ∃ H' : E2 →L[ℝ] E2, ∀ v w,
      fderiv ℝ (fderiv ℝ g) (rot120 x) (H' v) w = inner ℝ v w := by
  refine ⟨rot120CL.comp (H.comp (rot120CL.comp rot120CL)), fun v w => ?_⟩
  have h := hessian_rot hg hsym x (H (rot120 (rot120 v))) (rot120 (rot120 w))
  simp only [ContinuousLinearMap.comp_apply, rot120CL_apply]
  conv_lhs => rw [← rot120_cube w]
  rw [h, hH, Semicontinuity.inner_rot120, Semicontinuity.inner_rot120]


lemma inner_tangent_left (k : E2) : inner ℝ tangentDirection k = k 1 := by
  simp [tangentDirection, inner, Fin.sum_univ_two]

lemma norm_sq_E2 (v : E2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

lemma hess_symm_orderPotential (t h k : E2) :
    fderiv ℝ (fderiv ℝ orderPotential) t h k = fderiv ℝ (fderiv ℝ orderPotential) t k h := by
  rw [(fderiv_fderiv_orderPotential t).2, (fderiv_fderiv_orderPotential t).2]
  have hs : ∑ i, orderChart t i * inner ℝ (vertex i) h * inner ℝ (vertex i) k =
      ∑ i, orderChart t i * inner ℝ (vertex i) k * inner ℝ (vertex i) h :=
    Finset.sum_congr rfl fun i _ => by ring
  have hi : inner ℝ k h = inner ℝ h k := real_inner_comm _ _
  simp only [orderCov, hs, hi]
  ring

lemma axis_hess {r : ℝ} (hr : 0 < r) :
    (∀ k, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) (vertex 0) k =
      3 * r / (2 * beta0) * deriv (criticalFunction beta0) r * inner ℝ (vertex 0) k) ∧
    (∀ k, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) tangentDirection k =
      3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) * inner ℝ tangentDirection k) := by
  have h := (order_parameter_hessians_and_coercive_tail).2.2.1 r (axisPoint r) hr
    (orderChart_axisPoint hr)
  exact ⟨h.2.2.1, h.2.2.2.1⟩

lemma quad_diag (B : E2 →L[ℝ] E2 →L[ℝ] ℝ) (l1 l2 : ℝ)
    (h1 : ∀ k, B (vertex 0) k = l1 * inner ℝ (vertex 0) k)
    (h2 : ∀ k, B tangentDirection k = l2 * inner ℝ tangentDirection k) (v : E2) :
    B v v = l1 * v 0 ^ 2 + l2 * v 1 ^ 2 := by
  have hv : v = (v 0) • vertex 0 + (v 1) • tangentDirection := by
    ext i
    fin_cases i <;> simp [vertex_zero, tangentDirection]
  have e1 : inner ℝ (vertex 0) (vertex 0) = (1 : ℝ) := inner_vertex_self 0
  have e2 : inner ℝ (vertex 0) tangentDirection = (0 : ℝ) := by
    rw [inner_vertex_zero_left]; simp [tangentDirection]
  have e3 : inner ℝ tangentDirection (vertex 0) = (0 : ℝ) := by
    rw [inner_tangent_left]; simp [vertex_zero]
  have e4 : inner ℝ tangentDirection tangentDirection = (1 : ℝ) := by
    rw [inner_tangent_left]; simp [tangentDirection]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, add_apply, smul_apply, h1, h2, e1, e2, e3, e4, smul_eq_mul]
  ring

lemma eig_lower (B : E2 →L[ℝ] E2 →L[ℝ] ℝ) (H : E2 →L[ℝ] E2)
    (hH : ∀ v w, B (H v) w = inner ℝ v w) (hs : ∀ a b, B a b = B b a) (e : E2) (he : ‖e‖ = 1)
    (l : ℝ) (h : ∀ k, B e k = l * inner ℝ e k) : 1 ≤ |l| * ‖H‖ := by
  have h1 : (1 : ℝ) = l * inner ℝ e (H e) := by
    have := hH e e
    rw [hs, h, real_inner_self_eq_norm_sq, he] at this
    simpa using this.symm
  calc (1 : ℝ) = |l * inner ℝ e (H e)| := by rw [← h1]; simp
    _ = |l| * |inner ℝ e (H e)| := abs_mul _ _
    _ ≤ |l| * (‖e‖ * ‖H e‖) := by gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ |l| * (1 * ‖H‖) := by
        rw [he]; gcongr; exact H.le_opNorm e |>.trans (by rw [he, mul_one])
    _ = |l| * ‖H‖ := by ring

lemma posdef_of_near (B A : E2 →L[ℝ] E2 →L[ℝ] ℝ) (l1 l2 c : ℝ) (hc : 0 < c)
    (h1 : ∀ k, B (vertex 0) k = l1 * inner ℝ (vertex 0) k)
    (h2 : ∀ k, B tangentDirection k = l2 * inner ℝ tangentDirection k)
    (hl1 : c ≤ l1) (hl2 : c ≤ l2) (hA : ‖A - B‖ ≤ c / 2) (v : E2) (hv : v ≠ 0) :
    0 < A v v := by
  have hq := quad_diag B l1 l2 h1 h2 v
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  have hd : |(A - B) v v| ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    calc ‖(A - B) v v‖ ≤ ‖(A - B) v‖ * ‖v‖ := ((A - B) v).le_opNorm v
      _ ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := by gcongr; exact (A - B).le_opNorm v
  have hd2 : -(c / 2 * ‖v‖ ^ 2) ≤ (A - B) v v := by
    have : ‖A - B‖ * ‖v‖ * ‖v‖ ≤ c / 2 * ‖v‖ ^ 2 := by
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hA (sq_nonneg ‖v‖)]
    linarith [(abs_le.1 hd).1]
  have hsub : (A - B) v v = A v v - B v v := rfl
  have hnq := norm_sq_E2 v
  have h0 : 0 ≤ v 0 ^ 2 := sq_nonneg _
  have h1' : 0 ≤ v 1 ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hl1 h0, mul_le_mul_of_nonneg_right hl2 h1']

lemma saddle_of_near (B A : E2 →L[ℝ] E2 →L[ℝ] ℝ) (l1 l2 c : ℝ) (hc : 0 < c)
    (h1 : ∀ k, B (vertex 0) k = l1 * inner ℝ (vertex 0) k)
    (h2 : ∀ k, B tangentDirection k = l2 * inner ℝ tangentDirection k)
    (hl1 : l1 ≤ -c) (hl2 : c ≤ l2) (hA : ‖A - B‖ ≤ c / 2) :
    ∃ v w : E2, A v v < 0 ∧ 0 < A w w := by
  have key : ∀ v : E2, ‖v‖ = 1 → |(A - B) v v| ≤ c / 2 := by
    intro v hv
    rw [← Real.norm_eq_abs]
    calc ‖(A - B) v v‖ ≤ ‖(A - B) v‖ * ‖v‖ := ((A - B) v).le_opNorm v
      _ ≤ ‖A - B‖ * ‖v‖ * ‖v‖ := by gcongr; exact (A - B).le_opNorm v
      _ ≤ c / 2 := by rw [hv]; linarith
  have n1 : ‖vertex 0‖ = 1 := norm_vertex 0
  have n2 : ‖tangentDirection‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simp [tangentDirection, Fin.sum_univ_two]
  have q1 := quad_diag B l1 l2 h1 h2 (vertex 0)
  have q2 := quad_diag B l1 l2 h1 h2 tangentDirection
  have k1 := (abs_le.1 (key _ n1)).2
  have k2 := (abs_le.1 (key _ n2)).1
  have s1 : (A - B) (vertex 0) (vertex 0) = A (vertex 0) (vertex 0) - B (vertex 0) (vertex 0) := rfl
  have s2 : (A - B) tangentDirection tangentDirection =
    A tangentDirection tangentDirection - B tangentDirection tangentDirection := rfl
  refine ⟨vertex 0, tangentDirection, ?_, ?_⟩
  · have a0 : (vertex 0) 0 = 1 := by simp [vertex_zero]
    have a1 : (vertex 0) 1 = 0 := by simp [vertex_zero]
    rw [a0, a1] at q1
    norm_num at q1
    linarith
  · have a0 : tangentDirection 0 = 0 := by simp [tangentDirection]
    have a1 : tangentDirection 1 = 1 := by simp [tangentDirection]
    rw [a0, a1] at q2
    norm_num at q2
    linarith


lemma norm_tangent : ‖tangentDirection‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [tangentDirection, Fin.sum_univ_two]

lemma axis_eig_data {r : ℝ} (hr : 0 < r) (h2 : beta0 < r + 2) (H : E2 →L[ℝ] E2)
    (hH : ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) (H v) w = inner ℝ v w) :
    1 ≤ |3 * r / (2 * beta0) * deriv (criticalFunction beta0) r| * ‖H‖ ∧
    0 < 3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) ∧
    1 ≤ 3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) * ‖H‖ := by
  obtain ⟨e1, e2⟩ := axis_hess hr
  have hs := hess_symm_orderPotential (axisPoint r)
  have hb : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have hl2 : 0 < 3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) := by
    apply div_pos (by linarith) (by positivity)
  refine ⟨eig_lower _ H hH hs _ (norm_vertex 0) _ e1, hl2, ?_⟩
  have := eig_lower _ H hH hs _ norm_tangent _ e2
  rwa [abs_of_pos hl2] at this

lemma axis_pos_class {r : ℝ} (hr : 0 < r) (h2 : beta0 < r + 2)
    (hd : 0 < deriv (criticalFunction beta0) r) (H : E2 →L[ℝ] E2)
    (hH : ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) (H v) w = inner ℝ v w)
    (A : E2 →L[ℝ] E2 →L[ℝ] ℝ)
    (hA : ‖A - fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r)‖ ≤ 1 / (2 * ‖H‖))
    (v : E2) (hv : v ≠ 0) : 0 < A v v := by
  obtain ⟨e1, e2⟩ := axis_hess hr
  obtain ⟨a1, hl2, a2⟩ := axis_eig_data hr h2 H hH
  have hHp := hinv_norm_pos hH
  have hb : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have hl1 : 0 < 3 * r / (2 * beta0) * deriv (criticalFunction beta0) r := by positivity
  rw [abs_of_pos hl1] at a1
  refine posdef_of_near _ A _ _ (1 / ‖H‖) (by positivity) e1 e2
    ((div_le_iff₀ hHp).2 (by linarith)) ((div_le_iff₀ hHp).2 (by linarith)) ?_ v hv
  calc _ ≤ 1 / (2 * ‖H‖) := hA
    _ = 1 / ‖H‖ / 2 := by field_simp

lemma axis_saddle_class {r : ℝ} (hr : 0 < r) (h2 : beta0 < r + 2)
    (hd : deriv (criticalFunction beta0) r < 0) (H : E2 →L[ℝ] E2)
    (hH : ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) (H v) w = inner ℝ v w)
    (A : E2 →L[ℝ] E2 →L[ℝ] ℝ)
    (hA : ‖A - fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r)‖ ≤ 1 / (2 * ‖H‖)) :
    ∃ v w : E2, A v v < 0 ∧ 0 < A w w := by
  obtain ⟨e1, e2⟩ := axis_hess hr
  obtain ⟨a1, hl2, a2⟩ := axis_eig_data hr h2 H hH
  have hHp := hinv_norm_pos hH
  have hb : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have hl1 : 3 * r / (2 * beta0) * deriv (criticalFunction beta0) r < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hd
  rw [abs_of_neg hl1] at a1
  refine saddle_of_near _ A _ _ (1 / ‖H‖) (by positivity) e1 e2 ?_
    ((div_le_iff₀ hHp).2 (by linarith)) ?_
  · have : 1 / ‖H‖ ≤ -(3 * r / (2 * beta0) * deriv (criticalFunction beta0) r) :=
      (div_le_iff₀ hHp).2 (by linarith)
    linarith
  · calc _ ≤ 1 / (2 * ‖H‖) := hA
      _ = 1 / ‖H‖ / 2 := by field_simp

lemma axis_nondeg {r : ℝ} (hr : 0 < r) (h2 : beta0 < r + 2)
    (hd : deriv (criticalFunction beta0) r ≠ 0) :
    ∃ H : E2 →L[ℝ] E2,
      ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (axisPoint r) (H v) w = inner ℝ v w := by
  obtain ⟨e1, e2⟩ := axis_hess hr
  have hs := hess_symm_orderPotential (axisPoint r)
  have hb : (0 : ℝ) < beta0 := by unfold beta0; norm_num
  have hl1 : 3 * r / (2 * beta0) * deriv (criticalFunction beta0) r ≠ 0 :=
    mul_ne_zero (by positivity) hd
  have hl2 : 3 * (r + 2 - beta0) / (2 * beta0 * (r + 2)) ≠ 0 :=
    (div_pos (by linarith) (by positivity)).ne'
  refine exists_hinv _ (fun v hv => ?_)
  have c0 := hv (vertex 0)
  have c1 := hv tangentDirection
  rw [hs, e1, inner_vertex_zero_left] at c0
  rw [hs, e2, inner_tangent_left] at c1
  have v0 : v 0 = 0 := by
    rcases mul_eq_zero.1 c0 with h | h
    · exact absurd h hl1
    · exact h
  have v1 : v 1 = 0 := by
    rcases mul_eq_zero.1 c1 with h | h
    · exact absurd h hl2
    · exact h
  ext i
  fin_cases i
  · simpa using v0
  · simpa using v1

lemma axis_critical {r : ℝ} (hr : 0 < r) (h : criticalFunction beta0 r = 0) :
    fderiv ℝ orderPotential (axisPoint r) = 0 ∧
      orderPotential (axisPoint r) = freeEnergy beta0 (pointR r) := by
  constructor
  · have h2 : r + 2 ≠ 0 := by positivity
    have hw : kappa0⁻¹ • axisPoint r - ((r - 1) / (r + 2)) • vertex 0 =
        (kappa0⁻¹ * (2 / 3 * Real.log r) - (r - 1) / (r + 2)) • vertex 0 := by
      unfold axisPoint
      rw [smul_smul, ← sub_smul]
    have hl : Real.log r = beta0 * (r - 1) / (r + 2) := by
      unfold criticalFunction at h; linarith
    have hs : kappa0⁻¹ * (2 / 3 * Real.log r) - (r - 1) / (r + 2) = 0 := by
      rw [hl]; unfold kappa0 beta0; field_simp; ring
    rw [fderiv_orderPotential, orderChart_axisPoint hr, meanVector_pointR hr, hw, hs,
      zero_smul, map_zero]
  · rw [orderPotential_axisPoint hr, h]; simp

lemma exists_orbit (x : E2) : ∃ p : Fin 3 → E2, p 0 = x ∧ ∀ i, p (i + 1) = rot120 (p i) := by
  refine ⟨![x, rot120 x, rot120 (rot120 x)], rfl, fun i => ?_⟩
  fin_cases i
  · rfl
  · rfl
  · exact (rot120_cube x).symm

lemma orbit_prop {p : Fin 3 → E2} {P : E2 → Prop} (h0 : P (p 0)) (hP : ∀ y, P y → P (rot120 y))
    (hp : ∀ i, p (i + 1) = rot120 (p i)) : ∀ i, P (p i) := by
  have h1 : P (p 1) := by
    have := hp 0
    simp only [show (0 : Fin 3) + 1 = 1 from rfl] at this
    rw [this]; exact hP _ h0
  have h2 : P (p 2) := by
    have := hp 1
    simp only [show (1 : Fin 3) + 1 = 2 from rfl] at this
    rw [this]; exact hP _ h1
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma root_data :
    ∃ rs rm : ℝ, 2 < rs ∧ rs < rm ∧ 3 < rm ∧ rm < 4 ∧
      criticalFunction beta0 rs = 0 ∧ criticalFunction beta0 rm = 0 ∧
      deriv (criticalFunction beta0) rs < 0 ∧ 0 < deriv (criticalFunction beta0) rm ∧
      0 < freeEnergy beta0 (pointR rm) ∧ freeEnergy beta0 (pointR rm) < freeEnergy beta0 (pointR rs) := by
  have hb : beta0 = 11 / 4 := rfl
  obtain ⟨rs', rm', h2', hlt', h3', h4', hr', -, hF0, hFlt, -⟩ := exact_discrete_path_barrier
  obtain ⟨-, -, rs, rm, h2rs, hrsdp, h3rm, hrm4, hroots, hds, hdm, -⟩ :=
    complete_roots_and_critical_landscape_at_eleven_quarters
  obtain ⟨s5, s6⟩ := sqrt33_bounds
  have hrs3 : rs < 3 := by linarith
  have hrm' : rm' = rm := by
    have hc : criticalFunction (11 / 4) rm' = 0 := (hr' rm' (by linarith)).2 (Or.inr (Or.inr rfl))
    rcases (hroots rm' (by linarith)).1 hc with h | h | h
    · linarith
    · linarith
    · exact h
  have hrs' : rs' = rs := by
    have hc : criticalFunction (11 / 4) rs' = 0 := (hr' rs' (by linarith)).2 (Or.inr (Or.inl rfl))
    rcases (hroots rs' (by linarith)).1 hc with h | h | h
    · linarith
    · exact h
    · linarith
  subst hrm' hrs'
  refine ⟨rs', rm', h2', hlt', h3', h4', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact (hroots rs' (by linarith)).2 (Or.inr (Or.inl rfl))
  · rw [hb]; exact (hroots rm' (by linarith)).2 (Or.inr (Or.inr rfl))
  · rw [hb]; exact hds
  · rw [hb]; exact hdm
  · rw [hb]; exact hF0
  · rw [hb]; exact hFlt


lemma limit_data :
    ∃ (Δ B : ℝ) (m σ : Fin 3 → E2), 0 < Δ ∧ Δ < B ∧
      (∀ i, orderPotential (m i) = Δ) ∧ (∀ i, orderPotential (σ i) = B) ∧
      (∀ i, fderiv ℝ orderPotential (m i) = 0) ∧ (∀ i, fderiv ℝ orderPotential (σ i) = 0) ∧
      (∀ i, m (i + 1) = rot120 (m i)) ∧ (∀ i, σ (i + 1) = rot120 (σ i)) ∧
      (∀ i, ∃ H : E2 →L[ℝ] E2,
        ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (m i) (H v) w = inner ℝ v w) ∧
      (∀ i, ∃ H : E2 →L[ℝ] E2,
        ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (σ i) (H v) w = inner ℝ v w) ∧
      (∀ H : E2 →L[ℝ] E2,
        (∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (m 0) (H v) w = inner ℝ v w) →
        ∀ A : E2 →L[ℝ] E2 →L[ℝ] ℝ,
          ‖A - fderiv ℝ (fderiv ℝ orderPotential) (m 0)‖ ≤ 1 / (2 * ‖H‖) →
          ∀ v : E2, v ≠ 0 → 0 < A v v) ∧
      (∀ H : E2 →L[ℝ] E2,
        (∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (σ 0) (H v) w = inner ℝ v w) →
        ∀ A : E2 →L[ℝ] E2 →L[ℝ] ℝ,
          ‖A - fderiv ℝ (fderiv ℝ orderPotential) (σ 0)‖ ≤ 1 / (2 * ‖H‖) →
          ∃ v w : E2, A v v < 0 ∧ 0 < A w w) := by
  obtain ⟨rs, rm, h2, hlt, h3, h4, hcs, hcm, hds, hdm, hF0, hFlt⟩ := root_data
  have hbeta : beta0 < rm + 2 := by unfold beta0; linarith
  have hbeta' : beta0 < rs + 2 := by unfold beta0; linarith
  have hrm0 : 0 < rm := by linarith
  have hrs0 : 0 < rs := by linarith
  obtain ⟨m, hm0, hm⟩ := exists_orbit (axisPoint rm)
  obtain ⟨σ, hσ0, hσ⟩ := exists_orbit (axisPoint rs)
  obtain ⟨cm1, cm2⟩ := axis_critical hrm0 hcm
  obtain ⟨cs1, cs2⟩ := axis_critical hrs0 hcs
  have hg := contDiff_orderPotential
  have hH : ∀ (x : E2), (∃ H : E2 →L[ℝ] E2,
        ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) x (H v) w = inner ℝ v w) →
      (∃ H : E2 →L[ℝ] E2,
        ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) (rot120 x) (H v) w = inner ℝ v w) :=
    fun x ⟨H, h⟩ => hinv_rot hg orderPotential_rot x H h
  have hcrit : ∀ x : E2, fderiv ℝ orderPotential x = 0 → fderiv ℝ orderPotential (rot120 x) = 0 :=
    fun x hx => fderiv_rot_eq_zero hg orderPotential_rot hx
  refine ⟨freeEnergy beta0 (pointR rm), freeEnergy beta0 (pointR rs), m, σ, hF0, hFlt,
    ?_, ?_, ?_, ?_, hm, hσ, ?_, ?_, ?_, ?_⟩
  · exact orbit_prop (P := fun x => orderPotential x = freeEnergy beta0 (pointR rm)) (by rw [hm0]; exact cm2) (fun y hy => by rw [orderPotential_rot, hy]) hm
  · exact orbit_prop (P := fun x => orderPotential x = freeEnergy beta0 (pointR rs)) (by rw [hσ0]; exact cs2) (fun y hy => by rw [orderPotential_rot, hy]) hσ
  · exact orbit_prop (P := fun x => fderiv ℝ orderPotential x = 0) (by rw [hm0]; exact cm1) hcrit hm
  · exact orbit_prop (P := fun x => fderiv ℝ orderPotential x = 0) (by rw [hσ0]; exact cs1) hcrit hσ
  · exact orbit_prop (P := fun x => ∃ H : E2 →L[ℝ] E2, ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) x (H v) w = inner ℝ v w) (by rw [hm0]; exact axis_nondeg hrm0 hbeta hdm.ne') hH hm
  · exact orbit_prop (P := fun x => ∃ H : E2 →L[ℝ] E2, ∀ v w, fderiv ℝ (fderiv ℝ orderPotential) x (H v) w = inner ℝ v w) (by rw [hσ0]; exact axis_nondeg hrs0 hbeta' hds.ne) hH hσ
  · intro H hH0 A hA v hv
    rw [hm0] at hH0 hA
    exact axis_pos_class hrm0 hbeta hdm H hH0 A hA v hv
  · intro H hH0 A hA
    rw [hσ0] at hH0 hA
    exact axis_saddle_class hrs0 hbeta' hds H hH0 A hA


lemma Ufeat_rot {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    ∀ y, Ufeat L ε (y + Spikes.pt (1 / 6)) = rot120 (Ufeat L ε y) := by
  intro y
  conv_lhs => rw [← pt_secT y]
  rw [← Semicontinuity.spt_add, Ufeat_pt hL,
    (exact_shift_symmetries_and_feature_moments hL ε).1.1 _, ← Ufeat_pt hL, pt_secT]

lemma featurePotential_rot {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : E2) :
    Semicontinuity.featurePotential kappa0 (Ufeat L ε) (rot120 t) =
      Semicontinuity.featurePotential kappa0 (Ufeat L ε) t := by
  unfold Semicontinuity.featurePotential
  rw [Semicontinuity.featureLogPartition_rot (Ufeat_rot hL ε) t, Semicontinuity.norm_rot120]

lemma contDiff_logPartition : ContDiff ℝ ∞ logPartition := by
  unfold logPartition
  refine ContDiff.log ?_ fun t => ?_
  · exact contDiff_const.mul (ContDiff.sum fun i _ =>
      Real.contDiff_exp.comp (contDiff_id.inner ℝ contDiff_const))
  · have := Finset.sum_pos (fun i (_ : i ∈ Finset.univ) =>
      Real.exp_pos (inner ℝ t (vertex i))) Finset.univ_nonempty
    positivity

lemma perturb_bounds {f g h : E2 → ℝ} (hf : ContDiff ℝ 2 f) (hh : ContDiff ℝ ∞ h)
    (hg : g = fun t => f t - h t) {S : Set E2} {M : ℝ} (hb : ckBound S 2 h M) :
    ContDiff ℝ 2 g ∧ (∀ t ∈ S, |g t - f t| ≤ M) ∧
      (∀ t ∈ S, ‖fderiv ℝ g t - fderiv ℝ f t‖ ≤ M) ∧
      (∀ t ∈ S, ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ f) t‖ ≤ M) := by
  subst hg
  have hh2 : ContDiff ℝ 2 h := hh.of_le (by norm_cast)
  have hfd : ∀ t, DifferentiableAt ℝ f t := fun t => hf.differentiable (by norm_num) t
  have hhd : ∀ t, DifferentiableAt ℝ h t := fun t => hh.differentiable (by simp) t
  have hd1 : fderiv ℝ (fun t => f t - h t) = fun t => fderiv ℝ f t - fderiv ℝ h t :=
    funext fun t => fderiv_sub (hfd t) (hhd t)
  have hfd' : ∀ t, DifferentiableAt ℝ (fderiv ℝ f) t := fun t =>
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) t
  have hhd' : ∀ t, DifferentiableAt ℝ (fderiv ℝ h) t := fun t =>
    ((hh.fderiv_right (m := 1) (by simp)).differentiable (by simp)) t
  have hd2 : fderiv ℝ (fderiv ℝ fun t => f t - h t) =
      fun t => fderiv ℝ (fderiv ℝ f) t - fderiv ℝ (fderiv ℝ h) t := by
    rw [hd1]; exact funext fun t => fderiv_sub (hfd' t) (hhd' t)
  have b1 := ckBound_fderiv hb
  have b0 := ckBound_fderiv b1
  refine ⟨hf.sub hh2, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := hb t ht 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    simpa [abs_sub_comm] using this
  · have := b1 t ht 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    rw [hd1]; simpa only [sub_sub_cancel_left, norm_neg] using this
  · have := b0 t ht 0 (by norm_num)
    rw [norm_iteratedFDeriv_zero] at this
    rw [hd2]
    show ‖_ - _ - _‖ ≤ M
    rw [sub_sub_cancel_left]; exact (le_of_eq (norm_neg _)).trans this

lemma exists_pos_le3 (f : Fin 3 → ℝ) (hf : ∀ i, 0 < f i) : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  refine ⟨min (f 0) (min (f 1) (f 2)), lt_min (hf 0) (lt_min (hf 1) (hf 2)), fun i => ?_⟩
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

lemma exists_radius (p : E2) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ x ∈ closedBall p r,
      ‖fderiv ℝ (fderiv ℝ orderPotential) x - fderiv ℝ (fderiv ℝ orderPotential) p‖ ≤ ε := by
  have hc : Continuous (fderiv ℝ (fderiv ℝ orderPotential)) :=
    (contDiff_orderPotential.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hev := hc.continuousAt (x := p) |>.preimage_mem_nhds
    (Metric.closedBall_mem_nhds (fderiv ℝ (fderiv ℝ orderPotential) p) hε)
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hev
  refine ⟨min (δ / 2) 1, lt_min (by positivity) one_pos, min_le_right _ _, fun x hx => ?_⟩
  have hxb : x ∈ Metric.ball p δ := by
    have := mem_closedBall.1 hx
    have := min_le_left (δ / 2) 1
    rw [Metric.mem_ball]
    linarith
  have h2 : fderiv ℝ (fderiv ℝ orderPotential) x ∈
      closedBall (fderiv ℝ (fderiv ℝ orderPotential) p) ε := h hxb
  have h3 := mem_closedBall.1 h2
  exact (dist_eq_norm (fderiv ℝ (fderiv ℝ orderPotential) x)
    (fderiv ℝ (fderiv ℝ orderPotential) p)) ▸ h3

lemma rot_ball_incl (p : E2) (r : ℝ) :
    rot120 '' closedBall p r ⊆ closedBall (rot120 p) r := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  have : rot120 y - rot120 p = rot120CL (y - p) := by
    rw [map_sub]; rfl
  rw [this, rot120CL_apply, Semicontinuity.norm_rot120]
  exact hy

lemma posdef_rot {g : E2 → ℝ} (hg : ContDiff ℝ 2 g) (hsym : ∀ x, g (rot120 x) = g x) (x : E2)
    (h : ∀ v : E2, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ g) x v v) :
    ∀ v : E2, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ g) (rot120 x) v v := by
  intro v hv
  have h1 := hessian_rot hg hsym x (rot120 (rot120 v)) (rot120 (rot120 v))
  rw [rot120_cube] at h1
  rw [h1]
  apply h
  intro h0
  apply hv
  have n : ‖rot120 (rot120 v)‖ = ‖v‖ := by
    rw [Semicontinuity.norm_rot120, Semicontinuity.norm_rot120]
  rw [h0, norm_zero] at n
  exact norm_eq_zero.1 n.symm

lemma indef_rot {g : E2 → ℝ} (hg : ContDiff ℝ 2 g) (hsym : ∀ x, g (rot120 x) = g x) (x : E2)
    (h : ∃ v w : E2, fderiv ℝ (fderiv ℝ g) x v v < 0 ∧ 0 < fderiv ℝ (fderiv ℝ g) x w w) :
    ∃ v w : E2, fderiv ℝ (fderiv ℝ g) (rot120 x) v v < 0 ∧
      0 < fderiv ℝ (fderiv ℝ g) (rot120 x) w w := by
  obtain ⟨v, w, hv, hw⟩ := h
  exact ⟨rot120 v, rot120 w, by rw [hessian_rot hg hsym]; exact hv,
    by rw [hessian_rot hg hsym]; exact hw⟩

lemma norm_gradient_eq (g : E2 → ℝ) (x : E2) : ‖gradient g x‖ = ‖fderiv ℝ g x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ E2).symm.norm_map _


/-- The local (remote-critical-point) part of the landscape certificate for a potential `F`:
an exact `R_{2π/3}`-orbit of three nondegenerate remote minima `aM` and of three
nondegenerate saddles `aS`, with positive gaps `Δ/2` and `(B-Δ)/2`. -/
def LocalLandscapeCertificate (F : E2 → ℝ) : Prop :=
  ∃ (Δ B : ℝ) (aM aS : Fin 3 → E2), 0 < Δ ∧ Δ < B ∧
    (∀ i, aM (i + 1) = rot120 (aM i)) ∧ (∀ i, aS (i + 1) = rot120 (aS i)) ∧
    (∀ i, fderiv ℝ F (aM i) = 0) ∧ (∀ i, fderiv ℝ F (aS i) = 0) ∧
    (∀ i, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ closedBall (aM i) r, fderiv ℝ F x = 0 → x = aM i) ∧
    (∀ i, ∃ r : ℝ, 0 < r ∧ ∀ x ∈ closedBall (aS i) r, fderiv ℝ F x = 0 → x = aS i) ∧
    (∀ i, ∀ v : E2, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ F) (aM i) v v) ∧
    (∀ i, ∃ v w : E2, fderiv ℝ (fderiv ℝ F) (aS i) v v < 0 ∧ 0 < fderiv ℝ (fderiv ℝ F) (aS i) w w) ∧
    (∀ i j, F (aM i) = F (aM j)) ∧ (∀ i j, F (aS i) = F (aS j)) ∧
    (∀ i, Δ / 2 ≤ F (aM i)) ∧ (∀ i j, (B - Δ) / 2 ≤ F (aS i) - F (aM j))

/-- The full landscape certificate for a potential `F` on the order-parameter plane:
smooth, rotation invariant, with the global Haar-potential minimum `0` (unique, `F ≥ 0`),
all critical points in `B̄_κ`, all global minimizers in `B̄_{2κ}`, plus the local certificate. -/
def PotentialLandscapeCertificate (F : E2 → ℝ) : Prop :=
  ContDiff ℝ ∞ F ∧ (∀ x, F (rot120 x) = F x) ∧
  (∀ t, 0 ≤ F t) ∧ (∀ t, F t = 0 ↔ t = 0) ∧
  (∀ t, fderiv ℝ F t = 0 → ‖t‖ ≤ kappa0) ∧
  (∀ t, IsMinOn F Set.univ t → ‖t‖ ≤ 2 * kappa0) ∧
  LocalLandscapeCertificate F

/-- The landscape certificate of a feature `U : Torus 1 → ℝ²`, i.e. of its Haar potential
`Ψ_U(t) = ‖t‖²/(2κ) - Λ_U(t)`. -/
def RoughLandscapeCertificate (U : Torus 1 → E2) : Prop :=
  PotentialLandscapeCertificate (Semicontinuity.featurePotential kappa0 U)

lemma local_selection : ∃ R : ℝ, 2 * kappa0 < R ∧ ∃ η : ℝ, 0 < η ∧
    ∀ g : E2 → ℝ, ContDiff ℝ 2 g → (∀ x, g (rot120 x) = g x) →
      (∀ t ∈ closedBall (0 : E2) R, |g t - orderPotential t| ≤ η) →
      (∀ t ∈ closedBall (0 : E2) R, ‖fderiv ℝ g t - fderiv ℝ orderPotential t‖ ≤ η) →
      (∀ t ∈ closedBall (0 : E2) R,
        ‖fderiv ℝ (fderiv ℝ g) t - fderiv ℝ (fderiv ℝ orderPotential) t‖ ≤ η) →
      LocalLandscapeCertificate g := by
  obtain ⟨Δ, B, m, σ, hΔ, hΔB, hvM, hvS, hcM, hcS, hmr, hσr, hHMex, hHSex, hposM, hindS⟩ :=
    limit_data
  choose HM hHM using hHMex
  choose HS hHS using hHSex
  have hMp : ∀ i, 0 < 1 / (4 * ‖HM i‖) := fun i => by
    have := hinv_norm_pos (hHM i); positivity
  have hSp : ∀ i, 0 < 1 / (4 * ‖HS i‖) := fun i => by
    have := hinv_norm_pos (hHS i); positivity
  choose rM' hrM'0 hrM'1 hrM'b using fun i => exists_radius (m i) (hMp i)
  choose rS' hrS'0 hrS'1 hrS'b using fun i => exists_radius (σ i) (hSp i)
  obtain ⟨cM, hcM0, hcMle⟩ := exists_pos_le3 rM' hrM'0
  obtain ⟨cS, hcS0, hcSle⟩ := exists_pos_le3 rS' hrS'0
  set r : ℝ := min cM cS with hr
  have hr0 : 0 < r := lt_min hcM0 hcS0
  have hrM : ∀ i, r ≤ rM' i := fun i => (min_le_left _ _).trans (hcMle i)
  have hrS : ∀ i, r ≤ rS' i := fun i => (min_le_right _ _).trans (hcSle i)
  have hr1 : r ≤ 1 := (hrM 0).trans (hrM'1 0)
  set R : ℝ := 4 + ∑ i, ‖m i‖ + ∑ i, ‖σ i‖ with hRdef
  have hsm : 0 ≤ ∑ i, ‖m i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hss : 0 ≤ ∑ i, ‖σ i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hk : kappa0 = 11 / 6 := rfl
  have hR : 2 * kappa0 < R := by rw [hk]; linarith
  have hmR : ∀ i, ‖m i‖ ≤ R - 1 := fun i => by
    have := Finset.single_le_sum (f := fun i => ‖m i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  have hσR : ∀ i, ‖σ i‖ ≤ R - 1 := fun i => by
    have := Finset.single_le_sum (f := fun i => ‖σ i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ i)
    linarith
  have hRM : ∀ i, closedBall (m i) r ⊆ closedBall (0 : E2) R := fun i x hx => by
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff]
    have h2 : ‖x‖ ≤ ‖x - m i‖ + ‖m i‖ := by
      have := norm_add_le (x - m i) (m i)
      simpa using this
    linarith [hmR i]
  have hRS : ∀ i, closedBall (σ i) r ⊆ closedBall (0 : E2) R := fun i x hx => by
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff]
    have h2 : ‖x‖ ≤ ‖x - σ i‖ + ‖σ i‖ := by
      have := norm_add_le (x - σ i) (σ i)
      simpa using this
    linarith [hσR i]
  have hrotM : ∀ i, rot120 '' closedBall (m i) r ⊆ closedBall (m (i + 1)) r := fun i => by
    have := rot_ball_incl (m i) r
    rwa [← hmr i] at this
  have hrotS : ∀ i, rot120 '' closedBall (σ i) r ⊆ closedBall (σ (i + 1)) r := fun i => by
    have := rot_ball_incl (σ i) r
    rwa [← hσr i] at this
  obtain ⟨sM, sS, hsM0, hsMr, hsS0, hsSr, hmain⟩ :=
    critical_value_margins_and_exact_rotated_triples Δ B R hΔ hΔB m σ (fun _ => r) (fun _ => r)
      (fun _ => hr0) (fun _ => hr0) HM HS hvM hvS hHM hHS
      (fun i x hx => hrM'b i x (closedBall_subset_closedBall (hrM i) hx))
      (fun i x hx => hrS'b i x (closedBall_subset_closedBall (hrS i) hx))
      hRM hRS hrotM hrotS
  have hfMp : ∀ i, 0 < sM i / (2 * ‖HM i‖) := fun i => by
    have := hinv_norm_pos (hHM i); have := hsM0 i; positivity
  have hfSp : ∀ i, 0 < sS i / (2 * ‖HS i‖) := fun i => by
    have := hinv_norm_pos (hHS i); have := hsS0 i; positivity
  obtain ⟨c1, hc1, hc1le⟩ := exists_pos_le3 _ hfMp
  obtain ⟨c2, hc2, hc2le⟩ := exists_pos_le3 _ hfSp
  obtain ⟨c3, hc3, hc3le⟩ := exists_pos_le3 _ hMp
  obtain ⟨c4, hc4, hc4le⟩ := exists_pos_le3 _ hSp
  set d : ℝ := min (Δ / 2) ((B - Δ) / 4) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  set q : ℝ := min (min c1 c2) (min (min c3 c4) (d / 2)) with hq
  have hq0 : 0 < q := lt_min (lt_min hc1 hc2) (lt_min (lt_min hc3 hc4) (by positivity))
  have hq1 : q ≤ c1 := (min_le_left _ _).trans (min_le_left _ _)
  have hq2 : q ≤ c2 := (min_le_left _ _).trans (min_le_right _ _)
  have hq3 : q ≤ c3 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hq4 : q ≤ c4 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hq5 : q ≤ d / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, hR, q / 2, by positivity, fun g hg hsym hC0 hC1 hC2 => ?_⟩
  have hD2M : ∀ i, ∀ x ∈ closedBall (m i) ((fun _ => r) i),
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ orderPotential) x‖ ≤ 1 / (4 * ‖HM i‖) :=
    fun i x hx => (hC2 x (hRM i hx)).trans (by linarith [hc3le i])
  have hD2S : ∀ i, ∀ x ∈ closedBall (σ i) ((fun _ => r) i),
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ orderPotential) x‖ ≤ 1 / (4 * ‖HS i‖) :=
    fun i x hx => (hC2 x (hRS i hx)).trans (by linarith [hc4le i])
  have hC0' : ∀ t ∈ closedBall (0 : E2) R, |g t - orderPotential t| < min (Δ / 2) ((B - Δ) / 4) / 2 :=
    fun t ht => lt_of_le_of_lt (hC0 t ht) (by linarith)
  have hgradM : ∀ i, ‖gradient g (m i)‖ < sM i / (2 * ‖HM i‖) := fun i => by
    have hmem : m i ∈ closedBall (0 : E2) R := hRM i (mem_closedBall_self hr0.le)
    have := hC1 _ hmem
    rw [hcM i, sub_zero] at this
    rw [norm_gradient_eq]
    linarith [hc1le i]
  have hgradS : ∀ i, ‖gradient g (σ i)‖ < sS i / (2 * ‖HS i‖) := fun i => by
    have hmem : σ i ∈ closedBall (0 : E2) R := hRS i (mem_closedBall_self hr0.le)
    have := hC1 _ hmem
    rw [hcS i, sub_zero] at this
    rw [norm_gradient_eq]
    linarith [hc2le i]
  obtain ⟨aM, aS, hM1, hS1, hnM, hnS, hΔ', hB', hrotaM, hrotaS, heqM, heqS⟩ :=
    hmain g hg hD2M hD2S hC0' hsym hgradM hgradS
  have hnM' : ∀ i, ‖aM i - m i‖ < sM i := hnM
  have hnS' : ∀ i, ‖aS i - σ i‖ < sS i := hnS
  have hM1' : ∀ i, aM i ∈ closedBall (m i) r := fun i => (hM1 i).1
  have hS1' : ∀ i, aS i ∈ closedBall (σ i) r := fun i => (hS1 i).1
  have hdistM : ∀ i, dist (aM i) (m i) < r := fun i => by
    rw [dist_eq_norm]; exact lt_of_lt_of_le (hnM' i) (hsMr i)
  have hdistS : ∀ i, dist (aS i) (σ i) < r := fun i => by
    rw [dist_eq_norm]; exact lt_of_lt_of_le (hnS' i) (hsSr i)
  -- Hessian bounds at the critical points
  have hHessM : ∀ i, ‖fderiv ℝ (fderiv ℝ g) (aM i) - fderiv ℝ (fderiv ℝ orderPotential) (m i)‖ ≤
      1 / (2 * ‖HM i‖) := fun i => by
    have h1 := hD2M i (aM i) (hM1' i)
    have h2 := hrM'b i (aM i) (closedBall_subset_closedBall (hrM i) (hM1' i))
    have h3 := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) (aM i))
      (fderiv ℝ (fderiv ℝ orderPotential) (aM i)) (fderiv ℝ (fderiv ℝ orderPotential) (m i))
    have hp := hinv_norm_pos (hHM i)
    have e : 1 / (4 * ‖HM i‖) + 1 / (4 * ‖HM i‖) = 1 / (2 * ‖HM i‖) := by field_simp; ring
    linarith
  have hHessS : ∀ i, ‖fderiv ℝ (fderiv ℝ g) (aS i) - fderiv ℝ (fderiv ℝ orderPotential) (σ i)‖ ≤
      1 / (2 * ‖HS i‖) := fun i => by
    have h1 := hD2S i (aS i) (hS1' i)
    have h2 := hrS'b i (aS i) (closedBall_subset_closedBall (hrS i) (hS1' i))
    have hp := hinv_norm_pos (hHS i)
    have h3 := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (fderiv ℝ g) (aS i))
      (fderiv ℝ (fderiv ℝ orderPotential) (aS i)) (fderiv ℝ (fderiv ℝ orderPotential) (σ i))
    have e : 1 / (4 * ‖HS i‖) + 1 / (4 * ‖HS i‖) = 1 / (2 * ‖HS i‖) := by field_simp; ring
    linarith
  have hposM' : ∀ i, ∀ v : E2, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ g) (aM i) v v := by
    refine orbit_prop (p := aM)
      (P := fun x => ∀ v : E2, v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ g) x v v) ?_
      (fun y hy => posdef_rot hg hsym y hy) hrotaM
    exact hposM (HM 0) (hHM 0) _ (hHessM 0)
  have hindS' : ∀ i, ∃ v w : E2, fderiv ℝ (fderiv ℝ g) (aS i) v v < 0 ∧
      0 < fderiv ℝ (fderiv ℝ g) (aS i) w w := by
    refine orbit_prop (p := aS)
      (P := fun x => ∃ v w : E2, fderiv ℝ (fderiv ℝ g) x v v < 0 ∧
        0 < fderiv ℝ (fderiv ℝ g) x w w) ?_ (fun y hy => indef_rot hg hsym y hy) hrotaS
    exact hindS (HS 0) (hHS 0) _ (hHessS 0)
  refine ⟨Δ, B, aM, aS, hΔ, hΔB, hrotaM, hrotaS, fun i => (hM1 i).2.1, fun i => (hS1 i).2.1,
    fun i => ⟨r - dist (aM i) (m i), by linarith [hdistM i], fun x hx hx0 => ?_⟩,
    fun i => ⟨r - dist (aS i) (σ i), by linarith [hdistS i], fun x hx hx0 => ?_⟩,
    hposM', hindS', heqM, heqS, hΔ', hB'⟩
  · refine (hM1 i).2.2 x ?_ hx0
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle x (aM i) (m i)
    linarith
  · refine (hS1 i).2.2 x ?_ hx0
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle x (aS i) (σ i)
    linarith


lemma perturbed_certificate {L : ℝ} (hL : 0 < L) (ε : ℝ) {R η M : ℝ}
    (hb : ckBound (closedBall (0 : E2) R) 2
      (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t - logPartition t) M)
    (hM : M ≤ η / 2)
    (hcd : ContDiff ℝ ∞ (Semicontinuity.featureLogPartition (Ufeat L ε))) :
    ContDiff ℝ ∞ (Semicontinuity.featurePotential kappa0 (Ufeat L ε)) ∧
    (∀ x, Semicontinuity.featurePotential kappa0 (Ufeat L ε) (rot120 x) =
      Semicontinuity.featurePotential kappa0 (Ufeat L ε) x) ∧
    (∀ t ∈ closedBall (0 : E2) R,
      |Semicontinuity.featurePotential kappa0 (Ufeat L ε) t - orderPotential t| ≤ η / 2) ∧
    (∀ t ∈ closedBall (0 : E2) R,
      ‖fderiv ℝ (Semicontinuity.featurePotential kappa0 (Ufeat L ε)) t -
        fderiv ℝ orderPotential t‖ ≤ η / 2) ∧
    (∀ t ∈ closedBall (0 : E2) R,
      ‖fderiv ℝ (fderiv ℝ (Semicontinuity.featurePotential kappa0 (Ufeat L ε))) t -
        fderiv ℝ (fderiv ℝ orderPotential) t‖ ≤ η / 2) ∧
    ContDiff ℝ 2 (Semicontinuity.featurePotential kappa0 (Ufeat L ε)) := by
  have hg : Semicontinuity.featurePotential kappa0 (Ufeat L ε) =
      fun t => orderPotential t - (Semicontinuity.featureLogPartition (Ufeat L ε) t -
        logPartition t) := by
    funext t
    unfold Semicontinuity.featurePotential orderPotential
    ring
  have hh : ContDiff ℝ ∞ (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t -
      logPartition t) := hcd.sub contDiff_logPartition
  obtain ⟨h2, h0, h1, h2'⟩ := perturb_bounds contDiff_orderPotential hh hg hb
  refine ⟨?_, featurePotential_rot hL ε, fun t ht => (h0 t ht).trans hM,
    fun t ht => (h1 t ht).trans hM, fun t ht => (h2' t ht).trans hM, h2⟩
  rw [hg]
  have : ContDiff ℝ ∞ orderPotential := by
    unfold orderPotential
    exact ((contDiff_norm_sq ℝ).div_const _).sub contDiff_logPartition
  exact this.sub hh

/-- **RUF026, common finite parameter selection.**  There are `ε₀ > 0` and `L₀ ≥ max {1, 1/ε₀}`
such that for every `L ≥ L₀` and `|ε| ≤ ε₀` the actual feature `U_{L,ε}` has a landscape
certificate (global Haar-potential minimum at `0`, three rotated positive-gap remote minima and
three rotated saddles, exact `R_{2π/3}` invariance); in particular a finite `L_fixed ≥ L₀` with
`1/L_fixed ≤ ε₀` is selected, whose primary feature `U_{L_fixed, 1/L_fixed}` carries the
certificate. -/
theorem common_finite_parameter_selection :
    ∃ ε₀ L₀ : ℝ, 0 < ε₀ ∧ 1 ≤ L₀ ∧ 1 / ε₀ ≤ L₀ ∧
      (∀ L : ℝ, L₀ ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ → RoughLandscapeCertificate (Ufeat L ε)) ∧
      ∃ L_fixed : ℝ, L₀ ≤ L_fixed ∧ 1 / L_fixed ≤ ε₀ ∧
        RoughLandscapeCertificate (Ufeat L_fixed (1 / L_fixed)) := by
  obtain ⟨R, hR, η, hη, hloc⟩ := local_selection
  obtain ⟨γ, -, hγ, hglob⟩ := global_three_region_positivity_persists hR
  obtain ⟨hP1, hP2, hP3⟩ := compact_uniform_convergence_of_parameter_derivatives
  set η1 : ℝ := min η (γ / 2) with hη1def
  have hη10 : 0 < η1 := lt_min hη (by positivity)
  have hη1a : η1 ≤ η := min_le_left _ _
  have hη1b : η1 ≤ γ / 2 := min_le_right _ _
  obtain ⟨C, hC, hCb⟩ := hP2 2 R
  set S : ℝ := ⨆ z : Torus 1, |Spikes.gT z| with hSdef
  have hS : 0 ≤ S := Real.iSup_nonneg fun _ => abs_nonneg _
  have hCS : 0 ≤ C * S := mul_nonneg hC hS
  set ε₀ : ℝ := η1 / (4 * (C * S + 1)) with hε₀def
  have hε₀ : 0 < ε₀ := by positivity
  have hε₀b : C * ε₀ * S ≤ η1 / 4 := by
    have : C * ε₀ * S = C * S * η1 / (4 * (C * S + 1)) := by
      rw [hε₀def]; field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨L1, hL1⟩ := hP1 2 R (η1 / 4) (by positivity)
  have hmain : ∀ L : ℝ, max (max 1 (1 / ε₀)) L1 ≤ L → ∀ ε : ℝ, |ε| ≤ ε₀ →
      RoughLandscapeCertificate (Ufeat L ε) := by
    intro L hL ε hε
    have hL1' : 1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1'
    have hLL1 : L1 ≤ L := (le_max_right _ _).trans hL
    have hcd := hP3 L hLpos ε
    have hcd0 := hP3 L hLpos 0
    have hb1 := hCb L hLpos ε
    have hb0 := hL1 L hLL1
    have hε2 : C * |ε| * S ≤ η1 / 4 :=
      le_trans (by gcongr) hε₀b
    have hbsum := ckBound_add (hcd.sub hcd0) (hcd0.sub contDiff_logPartition) hb1 hb0
    have e : (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t - logPartition t) =
        fun t => (Semicontinuity.featureLogPartition (Ufeat L ε) t -
          Semicontinuity.featureLogPartition (Ufeat L 0) t) +
          (Semicontinuity.featureLogPartition (Ufeat L 0) t - logPartition t) :=
      funext fun t => by ring
    have hb : ckBound (closedBall (0 : E2) R) 2
        (fun t => Semicontinuity.featureLogPartition (Ufeat L ε) t - logPartition t)
        (η1 / 2) := by
      rw [e]
      exact ckBound_mono hbsum (by linarith)
    obtain ⟨hcont, hrot, hv, hd1, hd2, hc2⟩ :=
      perturbed_certificate hLpos ε hb le_rfl hcd
    have hmom := exact_shift_symmetries_and_feature_moments hLpos ε
    obtain ⟨g1, g2, g3, g4⟩ := hglob (Ufeat L ε) (measurable_Ufeat hLpos ε)
      (fun y => (norm_Ufeat L ε y).le) hmom.1.2.2.1 hmom.1.2.2.2 (fun t ht => by
        have := hv t (mem_closedBall_zero_iff.2 ht)
        linarith)
    refine ⟨hcont, hrot, g1, g2, g3, g4, hloc _ hc2 hrot (fun t ht => ?_) (fun t ht => ?_)
      (fun t ht => ?_)⟩
    · exact (hv t ht).trans (by linarith)
    · exact (hd1 t ht).trans (by linarith)
    · exact (hd2 t ht).trans (by linarith)
  have hL0 : 1 ≤ max (max 1 (1 / ε₀)) L1 := (le_max_left _ _).trans (le_max_left _ _)
  have hL0pos : 0 < max (max 1 (1 / ε₀)) L1 := lt_of_lt_of_le one_pos hL0
  have hL0b : 1 / ε₀ ≤ max (max 1 (1 / ε₀)) L1 :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hfix : 1 / max (max 1 (1 / ε₀)) L1 ≤ ε₀ := (one_div_le hL0pos hε₀).2 hL0b
  refine ⟨ε₀, max (max 1 (1 / ε₀)) L1, hε₀, hL0, hL0b, hmain, max (max 1 (1 / ε₀)) L1,
    le_rfl, hfix, hmain _ le_rfl _ ?_⟩
  rw [abs_of_pos (by positivity)]
  exact hfix

end DGPS.Examples.RoughBoundary.Landscape
