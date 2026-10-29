import FullLabeledLSI.Nonvacuity.Prop82.CRegularity
import FullLabeledLSI.Nonvacuity.Prop82.COsgood
import FullLabeledLSI.Nonvacuity.Prop82.Assembly

/-!
# Lane C, module C7: smoothness of the positive solution and the final theorem

Input from `CRegularity.lean` (`regular_representative`): for a `RawOptimizer ρ` there are a
continuous, periodic, nonnegative `C²` function `F` on `ℝ`, a smooth bounded periodic `B`, such that
`F'' = F (B - R log F)` pointwise (`R = realRate`), `∫₀¹ F² = 1` and `√ρ = F ∘ secT` almost
everywhere. Then `COsgood.pos_of_ode` gives `F > 0`, the equation bootstraps `F` to `C^∞`, and
`σ = (F ∘ secT)²` is the required smooth positive representative.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace SharpLSI.FL.Prop82

theorem contDiff_one_deriv_of_two {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) : ContDiff ℝ 1 (deriv F) := by
  have h : ContDiff ℝ ((1 : ℕ) + 1 : ℕ) F := by exact_mod_cast hF
  exact ((contDiff_succ_iff_deriv (n := 1)).1 h).2.2

/-- Bootstrapping: a positive `C²` solution of `F'' = F (B - R log F)` with smooth `B` is `C^∞`. -/
theorem contDiff_top_of_ode {R : ℝ} {B F : ℝ → ℝ} (hB : ContDiff ℝ ∞ B)
    (hF : ContDiff ℝ 2 F) (hpos : ∀ x, 0 < F x)
    (hode : ∀ x, deriv (deriv F) x = F x * (B x - R * Real.log (F x))) :
    ContDiff ℝ ∞ F := by
  have hG : deriv (deriv F) = fun x => F x * (B x - R * Real.log (F x)) := funext hode
  -- `S n : F ∈ C^n`, proved by two-step induction
  have key : ∀ n : ℕ, ContDiff ℝ n F ∧ ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F := by
    intro n
    induction n with
    | zero => exact ⟨hF.of_le (by norm_num), hF.of_le (by norm_num)⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      -- `F ∈ C^n` gives `F'' ∈ C^n`, hence `F ∈ C^(n+2)`
      have hFn : ContDiff ℝ n F := ih.1
      have hGn : ContDiff ℝ n (fun x => F x * (B x - R * Real.log (F x))) :=
        hFn.mul ((hB.of_le (by exact_mod_cast le_top)).sub
          (contDiff_const.mul (hFn.log fun x => (hpos x).ne')))
      have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_one_deriv_of_two hF
      have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
      have hddF : Differentiable ℝ (deriv F) := hF1.differentiable one_ne_zero
      have h1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (deriv F) := by
        refine (contDiff_succ_iff_deriv (n := (n : WithTop ℕ∞))).2 ⟨hddF, ?_, ?_⟩
        · intro h; exact absurd h (by simp)
        · rw [hG]; exact hGn
      refine (contDiff_succ_iff_deriv (n := ((n + 1 : ℕ) : WithTop ℕ∞))).2 ⟨hdF, ?_, h1⟩
      intro h; exact absurd h (by simp)
  exact contDiff_infty.2 fun n => (key n).1

/-- If `∫₀¹ F² = 1` and `F ≥ 0` is a function then `F` is somewhere positive. -/
theorem exists_pos_of_integral_sq {F : ℝ → ℝ} (h : ∫ x in (0 : ℝ)..1, F x ^ 2 = 1) :
    ∃ x, 0 < F x ∨ F x < 0 := by
  by_contra hcon
  have hcon' : ∀ x, ¬(0 < F x ∨ F x < 0) := fun x hx => hcon ⟨x, hx⟩
  simp only [not_or, not_lt] at hcon'
  have hz : ∀ x, F x = 0 := fun x => le_antisymm (hcon' x).1 (hcon' x).2
  have h0 : (fun x => F x ^ 2) = fun _ => (0 : ℝ) := by funext x; rw [hz x]; norm_num
  rw [h0] at h
  simp at h

theorem positive_smooth_representative : PositiveSmoothRepresentative := by
  intro ρ hρ
  obtain ⟨F, B, M, hF2, hper, hnn, hB, hBM, hode, hint, hae⟩ := regular_representative hρ
  have hex : ∃ x, 0 < F x := by
    obtain ⟨x, hx | hx⟩ := exists_pos_of_integral_sq hint
    · exact ⟨x, hx⟩
    · exact absurd (hnn x) (not_le.2 hx)
  have hdF : Differentiable ℝ F := hF2.differentiable (by norm_num)
  have hF1 : ContDiff ℝ 1 (deriv F) := contDiff_one_deriv_of_two hF2
  have hd1 : ∀ x, HasDerivAt F (deriv F x) x := fun x => (hdF x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv F) (deriv (deriv F) x) x :=
    fun x => ((hF1.differentiable one_ne_zero) x).hasDerivAt
  have hpos : ∀ x, 0 < F x := pos_of_ode realRate_pos hBM hd1 hd2 hnn hode hper hex
  have hFtop : ContDiff ℝ ∞ F := contDiff_top_of_ode hB hF2 hpos hode
  refine ⟨fun y => F (secT y 0) ^ 2, ?_, ?_⟩
  · -- `ρ =ᵐ σ`: `ρ = (√ρ)²` since `ρ ≥ 0`
    filter_upwards [hae] with y hy
    rw [← hy, Real.sq_sqrt (hρ.1.1 y)]
  · refine ⟨?_, fun y => pow_pos (hpos _) 2, ?_⟩
    · -- smoothness through periodicity
      have hlift : (fun y : Torus 1 => F (secT y 0) ^ 2) ∘ liftT =
          fun z : Fin 1 → ℝ => F (z 0) ^ 2 := by
        funext z
        obtain ⟨m, hm⟩ := secT_liftT_eq z
        simp only [Function.comp_apply, hm]
        have h0 : (z + intVec m) 0 = z 0 + (m 0 : ℝ) := by simp [intVec]
        rw [h0]
        have h1 := (hper.int_mul (m 0)) (z 0)
        simp only [mul_one] at h1
        rw [h1]
      show ContDiff ℝ ∞ ((fun y : Torus 1 => F (secT y 0) ^ 2) ∘ liftT)
      rw [hlift]
      exact (hFtop.comp (contDiff_apply ℝ ℝ 0)).pow 2
    · -- mass one
      have hmass := hρ.1.2.1
      refine Eq.trans ?_ hmass
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [← hy, Real.sq_sqrt (hρ.1.1 y)]

end SharpLSI.FL.Prop82
