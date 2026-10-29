import DGPS.Examples.RoughBoundary.LandscapePositivity
import DGPS.Examples.RoughBoundary.LandscapeRemote
import DGPS.Examples.RoughBoundary.FeatureMoments

/-!
# Critical value margins and exact rotated triples (RUF025)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.3 (3.6).  Let `Δ∞ < B∞` be the values of
`Ψ∞` at the three remote minima and the three saddles, `d = min {Δ∞/2, (B∞-Δ∞)/4}`.  Around each of
the six points `a` fix the data of RUF024 (`Hinv`, radius `r_a`, Hessian bounds).  Radii `s_a ≤ r_a`
are chosen by continuity of `Ψ∞`; a potential `Ψ_P` within `d/2` of `Ψ∞` in `C⁰`, with small
gradient at each `a`, has a unique critical point `a_P` in each ball with `|a_P - a| < s_a`, so
`|Ψ_P(a_P) - Ψ∞(a)| < d`.  Hence remote minimum values are `≥ Δ∞/2` and saddle minus minimum values
are `≥ (B∞-Δ∞)/2`.  If `Ψ_P ∘ R_{2π/3} = Ψ_P` and the balls rotate into each other, uniqueness
makes each triple an exact `R_{2π/3}`-orbit with equal values.
-/

namespace DGPS.Examples.RoughBoundary.Landscape

open Metric DGPS.Examples.RoughBoundary.ThreeState DGPS.Examples.RoughBoundary.Feature
open scoped Real

lemma contDiff_orderPotential : ContDiff ℝ 2 orderPotential := by
  unfold orderPotential logPartition
  refine ContDiff.sub ((contDiff_norm_sq ℝ).div_const _) (ContDiff.log ?_ fun t => ?_)
  · exact contDiff_const.mul (ContDiff.sum fun i _ =>
      Real.contDiff_exp.comp (contDiff_id.inner ℝ contDiff_const))
  · have := Finset.sum_pos (fun i (_ : i ∈ Finset.univ) =>
      Real.exp_pos (inner ℝ t (vertex i))) Finset.univ_nonempty
    positivity

/-- `R_{2π/3}` as a linear map. -/
noncomputable def rot120L : E2 →ₗ[ℝ] E2 where
  toFun := rot120
  map_add' x y := by ext i; fin_cases i <;> simp [rot120] <;> ring
  map_smul' c x := by ext i; fin_cases i <;> simp [rot120] <;> ring

/-- `R_{2π/3}` as a continuous linear map. -/
noncomputable def rot120CL : E2 →L[ℝ] E2 := LinearMap.toContinuousLinearMap rot120L

lemma rot120CL_apply (x : E2) : rot120CL x = rot120 x := rfl

lemma rot120_surjective : Function.Surjective rot120 := by
  have hinj : Function.Injective rot120L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := Real.sin_sq_add_cos_sq (2 * π / 3)
    have h0 := congrFun (congrArg (fun v : E2 => (v : Fin 2 → ℝ)) hx) 0
    have h1 := congrFun (congrArg (fun v : E2 => (v : Fin 2 → ℝ)) hx) 1
    simp [rot120L, rot120] at h0 h1
    ext i
    fin_cases i
    · simp
      linear_combination Real.cos (2 * π / 3) * h0 + Real.sin (2 * π / 3) * h1
        - x.ofLp 0 * h
    · simp
      linear_combination -Real.sin (2 * π / 3) * h0 + Real.cos (2 * π / 3) * h1
        - x.ofLp 1 * h
  exact LinearMap.injective_iff_surjective.1 hinj

/-- Critical points of a rotation-invariant `C¹` function are carried to critical points. -/
lemma fderiv_rot_eq_zero {g : E2 → ℝ} (hg : ContDiff ℝ 2 g) (hsym : ∀ x, g (rot120 x) = g x)
    {x : E2} (hx : fderiv ℝ g x = 0) : fderiv ℝ g (rot120 x) = 0 := by
  have hd : DifferentiableAt ℝ g (rot120CL x) :=
    (hg.differentiable (by norm_num)) _
  have hc : fderiv ℝ (g ∘ rot120CL) x = (fderiv ℝ g (rot120CL x)).comp rot120CL :=
    fderiv_comp x hd rot120CL.differentiableAt |>.trans (by rw [rot120CL.fderiv])
  have hgc : g ∘ rot120CL = g := funext hsym
  rw [hgc, hx] at hc
  ext w
  obtain ⟨v, rfl⟩ := rot120_surjective w
  have := congrArg (fun L => L v) hc
  simpa [rot120CL_apply] using this.symm

/-- One remote point: a unique critical point in the ball, within `s` of `a`. -/
lemma remote_point_within (f g : E2 → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (a : E2)
    (r : ℝ) (hr : 0 < r) (Hinv : E2 →L[ℝ] E2)
    (hHinv : ∀ v w, fderiv ℝ (fderiv ℝ f) a (Hinv v) w = inner ℝ v w)
    (hfball : ∀ x ∈ closedBall a r,
      ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) a‖ ≤ 1 / (4 * ‖Hinv‖))
    (hgball : ∀ x ∈ closedBall a r,
      ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ f) x‖ ≤ 1 / (4 * ‖Hinv‖))
    (s : ℝ) (hsr : s ≤ r) (hgrad : ‖gradient g a‖ < s / (2 * ‖Hinv‖)) :
    ∃ aP : E2, (aP ∈ closedBall a r ∧ fderiv ℝ g aP = 0 ∧
        ∀ x ∈ closedBall a r, fderiv ℝ g x = 0 → x = aP) ∧ ‖aP - a‖ < s := by
  have hn : ‖Hinv (gradient g a)‖ < s / 2 := by
    rcases eq_or_lt_of_le (norm_nonneg Hinv) with h0 | h0
    · rw [← h0] at hgrad; simp at hgrad; linarith [norm_nonneg (gradient g a)]
    · calc ‖Hinv (gradient g a)‖ ≤ ‖Hinv‖ * ‖gradient g a‖ := Hinv.le_opNorm _
        _ < ‖Hinv‖ * (s / (2 * ‖Hinv‖)) := by gcongr
        _ = s / 2 := by field_simp
  obtain ⟨aP, h1, h2, -, -⟩ := remote_critical_points_persist_by_contraction f g hf hg a r hr Hinv
    hHinv hfball hgball (by linarith)
  exact ⟨aP, h1, by linarith⟩

/-- A rotated triple of remote points: radii by continuity of `Ψ∞`, then critical points with
value margin `d` and exact rotation. -/
lemma rotated_triple_values (v d R : ℝ) (hd : 0 < d) (a : Fin 3 → E2) (r : Fin 3 → ℝ)
    (hr : ∀ i, 0 < r i) (Hinv : Fin 3 → E2 →L[ℝ] E2)
    (hv : ∀ i, orderPotential (a i) = v)
    (hHinv : ∀ i v w, fderiv ℝ (fderiv ℝ orderPotential) (a i) (Hinv i v) w = inner ℝ v w)
    (hfball : ∀ i, ∀ x ∈ closedBall (a i) (r i),
      ‖fderiv ℝ (fderiv ℝ orderPotential) x - fderiv ℝ (fderiv ℝ orderPotential) (a i)‖
        ≤ 1 / (4 * ‖Hinv i‖))
    (hR : ∀ i, closedBall (a i) (r i) ⊆ closedBall 0 R)
    (hrot : ∀ i, rot120 '' closedBall (a i) (r i) ⊆ closedBall (a (i + 1)) (r (i + 1))) :
    ∃ s : Fin 3 → ℝ, (∀ i, 0 < s i) ∧ (∀ i, s i ≤ r i) ∧
      ∀ g : E2 → ℝ, ContDiff ℝ 2 g →
        (∀ i, ∀ x ∈ closedBall (a i) (r i),
          ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ orderPotential) x‖
            ≤ 1 / (4 * ‖Hinv i‖)) →
        (∀ t ∈ closedBall (0 : E2) R, |g t - orderPotential t| < d / 2) →
        (∀ x, g (rot120 x) = g x) →
        (∀ i, ‖gradient g (a i)‖ < s i / (2 * ‖Hinv i‖)) →
        ∃ p : Fin 3 → E2,
          (∀ i, p i ∈ closedBall (a i) (r i) ∧ fderiv ℝ g (p i) = 0 ∧
            ∀ x ∈ closedBall (a i) (r i), fderiv ℝ g x = 0 → x = p i) ∧
          (∀ i, ‖p i - a i‖ < s i) ∧
          (∀ i, p (i + 1) = rot120 (p i)) ∧
          (∀ i, |g (p i) - v| < d) ∧ (∀ i j, g (p i) = g (p j)) := by
  have hc := continuous_orderPotential
  have hex : ∀ i, ∃ s : ℝ, 0 < s ∧ s ≤ r i ∧ ∀ t, dist t (a i) < s →
      |orderPotential t - orderPotential (a i)| < d / 2 := by
    intro i
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := a i)) _ (half_pos hd)
    exact ⟨min δ (r i), lt_min hδ (hr i), min_le_right _ _, fun t ht => by
      simpa [Real.dist_eq] using h (lt_of_lt_of_le ht (min_le_left _ _))⟩
  choose s hs0 hsr hsv using hex
  refine ⟨s, hs0, hsr, fun g hg hgball hC0 hsym hgrad => ?_⟩
  have key := fun i => remote_point_within orderPotential g contDiff_orderPotential hg (a i) (r i)
    (hr i) (Hinv i) (hHinv i) (hfball i) (hgball i) (s i) (hsr i) (hgrad i)
  choose p hp hps using key
  have hrotp : ∀ i, p (i + 1) = rot120 (p i) := by
    intro i
    have hmem : rot120 (p i) ∈ closedBall (a (i + 1)) (r (i + 1)) :=
      hrot i ⟨p i, (hp i).1, rfl⟩
    exact ((hp (i + 1)).2.2 _ hmem (fderiv_rot_eq_zero hg hsym (hp i).2.1)).symm
  have hval : ∀ i, |g (p i) - v| < d := by
    intro i
    have h1 := hC0 (p i) (hR i (hp i).1)
    have h2 := hsv i (p i) (by rw [dist_eq_norm]; exact hps i)
    rw [hv i] at h2
    have := abs_sub_lt_iff.1 h1
    have := abs_sub_lt_iff.1 h2
    rw [abs_sub_lt_iff]; constructor <;> linarith [abs_sub_lt_iff.1 h1, abs_sub_lt_iff.1 h2]
  have heq : ∀ i, g (p (i + 1)) = g (p i) := fun i => by rw [hrotp, hsym]
  refine ⟨p, hp, hps, hrotp, hval, fun i j => ?_⟩
  have h0 := heq 0
  have h1 := heq 1
  have h2 := heq 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl] at h0 h1 h2
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- **RUF025, critical value margins and exact rotated triples.**
Let `0 < Δ∞ < B∞` be the values of `Ψ∞` at the three remote minima `m i` and the three saddles
`σ i`, with RUF024 data (`Hinv`, radius, Hessian bound) around each, the balls contained in
`B̄_R`, and the balls of each triple rotated into each other by `R_{2π/3}`.  With
`d = min {Δ∞/2, (B∞-Δ∞)/4}` there are radii `s ≤ r` (depending only on `Ψ∞` and the data) such that
every `C²` potential `Ψ_P` with Hessian error `≤ 1/(4A)` on the balls, `C⁰` error `< d/2` on `B̄_R`,
`Ψ_P ∘ R_{2π/3} = Ψ_P`, and `|∇Ψ_P(a)| < s_a / (2 A_a)` at the six points has unique critical
points `aM i`, `aS i` in the balls with `|a_P - a| < s_a`, such that each triple is an exact
`R_{2π/3}`-orbit with equal values, all `Ψ_P(aM i) ≥ Δ∞/2` and `Ψ_P(aS i) - Ψ_P(aM j) ≥
(B∞-Δ∞)/2`. -/
theorem critical_value_margins_and_exact_rotated_triples
    (Δ B R : ℝ) (hΔ : 0 < Δ) (hΔB : Δ < B)
    (m σ : Fin 3 → E2) (rM rS : Fin 3 → ℝ) (hrM : ∀ i, 0 < rM i) (hrS : ∀ i, 0 < rS i)
    (HM HS : Fin 3 → E2 →L[ℝ] E2)
    (hvM : ∀ i, orderPotential (m i) = Δ) (hvS : ∀ i, orderPotential (σ i) = B)
    (hHM : ∀ i v w, fderiv ℝ (fderiv ℝ orderPotential) (m i) (HM i v) w = inner ℝ v w)
    (hHS : ∀ i v w, fderiv ℝ (fderiv ℝ orderPotential) (σ i) (HS i v) w = inner ℝ v w)
    (hfM : ∀ i, ∀ x ∈ closedBall (m i) (rM i),
      ‖fderiv ℝ (fderiv ℝ orderPotential) x - fderiv ℝ (fderiv ℝ orderPotential) (m i)‖
        ≤ 1 / (4 * ‖HM i‖))
    (hfS : ∀ i, ∀ x ∈ closedBall (σ i) (rS i),
      ‖fderiv ℝ (fderiv ℝ orderPotential) x - fderiv ℝ (fderiv ℝ orderPotential) (σ i)‖
        ≤ 1 / (4 * ‖HS i‖))
    (hRM : ∀ i, closedBall (m i) (rM i) ⊆ closedBall 0 R)
    (hRS : ∀ i, closedBall (σ i) (rS i) ⊆ closedBall 0 R)
    (hrotM : ∀ i, rot120 '' closedBall (m i) (rM i) ⊆ closedBall (m (i + 1)) (rM (i + 1)))
    (hrotS : ∀ i, rot120 '' closedBall (σ i) (rS i) ⊆ closedBall (σ (i + 1)) (rS (i + 1))) :
    ∃ sM sS : Fin 3 → ℝ, (∀ i, 0 < sM i) ∧ (∀ i, sM i ≤ rM i) ∧ (∀ i, 0 < sS i) ∧
      (∀ i, sS i ≤ rS i) ∧
      ∀ g : E2 → ℝ, ContDiff ℝ 2 g →
        (∀ i, ∀ x ∈ closedBall (m i) (rM i),
          ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ orderPotential) x‖
            ≤ 1 / (4 * ‖HM i‖)) →
        (∀ i, ∀ x ∈ closedBall (σ i) (rS i),
          ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ orderPotential) x‖
            ≤ 1 / (4 * ‖HS i‖)) →
        (∀ t ∈ closedBall (0 : E2) R,
          |g t - orderPotential t| < min (Δ / 2) ((B - Δ) / 4) / 2) →
        (∀ x, g (rot120 x) = g x) →
        (∀ i, ‖gradient g (m i)‖ < sM i / (2 * ‖HM i‖)) →
        (∀ i, ‖gradient g (σ i)‖ < sS i / (2 * ‖HS i‖)) →
        ∃ aM aS : Fin 3 → E2,
          (∀ i, aM i ∈ closedBall (m i) (rM i) ∧ fderiv ℝ g (aM i) = 0 ∧
            ∀ x ∈ closedBall (m i) (rM i), fderiv ℝ g x = 0 → x = aM i) ∧
          (∀ i, aS i ∈ closedBall (σ i) (rS i) ∧ fderiv ℝ g (aS i) = 0 ∧
            ∀ x ∈ closedBall (σ i) (rS i), fderiv ℝ g x = 0 → x = aS i) ∧
          (∀ i, ‖aM i - m i‖ < sM i) ∧ (∀ i, ‖aS i - σ i‖ < sS i) ∧
          (∀ i, Δ / 2 ≤ g (aM i)) ∧ (∀ i j, (B - Δ) / 2 ≤ g (aS i) - g (aM j)) ∧
          (∀ i, aM (i + 1) = rot120 (aM i)) ∧ (∀ i, aS (i + 1) = rot120 (aS i)) ∧
          (∀ i j, g (aM i) = g (aM j)) ∧ (∀ i j, g (aS i) = g (aS j)) := by
  set d : ℝ := min (Δ / 2) ((B - Δ) / 4) with hd
  have hd0 : 0 < d := lt_min (by linarith) (by linarith)
  have hd1 : d ≤ Δ / 2 := min_le_left _ _
  have hd2 : d ≤ (B - Δ) / 4 := min_le_right _ _
  obtain ⟨sM, hsM0, hsMr, hM⟩ := rotated_triple_values Δ d R hd0 m rM hrM HM hvM hHM hfM hRM hrotM
  obtain ⟨sS, hsS0, hsSr, hS⟩ := rotated_triple_values B d R hd0 σ rS hrS HS hvS hHS hfS hRS hrotS
  refine ⟨sM, sS, hsM0, hsMr, hsS0, hsSr, fun g hg hgM hgS hC0 hsym hgradM hgradS => ?_⟩
  obtain ⟨aM, hpM, hdM, hrM', hvM', heM⟩ := hM g hg hgM hC0 hsym hgradM
  obtain ⟨aS, hpS, hdS, hrS', hvS', heS⟩ := hS g hg hgS hC0 hsym hgradS
  refine ⟨aM, aS, hpM, hpS, hdM, hdS, fun i => ?_, fun i j => ?_, hrM', hrS', heM, heS⟩
  · have := (abs_sub_lt_iff.1 (hvM' i)).2; linarith
  · have h1 := (abs_sub_lt_iff.1 (hvM' j)).1
    have h2 := (abs_sub_lt_iff.1 (hvS' i)).2
    linarith

end DGPS.Examples.RoughBoundary.Landscape
