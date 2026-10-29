import Mathlib

/-!
# Section 9 regularity, module B: positivity and smoothness for the Euler--Lagrange ODE

Lane C of the Section 9 formalization (H8).  Pure real analysis.  The declarations
`not_zero_of_ode`, `pos_of_ode` are a COPY (namespace changed from `SharpLSI.FL.Prop82` to
`SharpLSI.FL.Ex.Reg`, otherwise unmodified) of `FullLabeledLSI/Nonvacuity/Prop82/COsgood.lean`, and
`contDiff_one_deriv_of_two`, `contDiff_top_of_ode` are a copy of the corresponding lemmas of
`FullLabeledLSI/Nonvacuity/Prop82/CFinal.lean`; source branch `claude/prop82-lane-c-s8pz05`,
commit `ce7043d`.  New here: `pos_of_linear_ode` (the case `R = 0`, via a Gronwall argument on
`F² + F'²`) and `pos_of_ode_of_nonneg` (both cases `R ≥ 0`).
-/

open Set Filter Topology
open scoped ContDiff

namespace SharpLSI.FL.Ex.Reg

/-- A positive component of a nonnegative `C²` solution cannot start at a zero. The function `F1`
is the derivative of `F` and `F2` the derivative of `F1`; only `F2 x = F x * (B x - R * log (F x))`
and `|B| ≤ M` are used. -/
theorem not_zero_of_ode {R M : ℝ} (hR : 0 < R) {B : ℝ → ℝ} (hB : ∀ x, |B x| ≤ M)
    {F F1 F2 : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x)
    (hode : ∀ x, F2 x = F x * (B x - R * Real.log (F x)))
    {α β : ℝ} (hαβ : α < β) (hα : F α = 0) (hpos : ∀ x ∈ Ioc α β, 0 < F x) : False := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  have hF1c : Continuous F1 := continuous_iff_continuousAt.2 fun x => (hd2 x).continuousAt
  have hM : 0 ≤ M := (abs_nonneg _).trans (hB 0)
  have hR0 : R ≠ 0 := hR.ne'
  -- `α` is a global minimum, so `F1 α = 0`
  have hF1α : F1 α = 0 := by
    have hmin : IsLocalMin F α :=
      Filter.Eventually.of_forall fun x => by rw [hα]; exact hnn x
    exact hmin.hasDerivAt_eq_zero (hd1 α)
  -- a smallness threshold: `R log t < -K` once `t < exp (-K / R)`
  have hlogK : ∀ K t : ℝ, 0 < t → t < Real.exp (-K / R) → R * Real.log t < -K := by
    intro K t ht htc
    have h1 : Real.log t < -K / R := by
      have := Real.log_lt_log ht htc
      rwa [Real.log_exp] at this
    have h2 : R * Real.log t < R * (-K / R) := mul_lt_mul_of_pos_left h1 hR
    have h3 : R * (-K / R) = -K := by field_simp
    linarith
  -- continuity of `F` at `α`: `F < exp (-K/R)` on a right neighbourhood
  have hsmall : ∀ K : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ x, |x - α| < δ → F x < Real.exp (-K / R) := by
    intro K
    have hev : ∀ᶠ y in 𝓝 α, F y < Real.exp (-K / R) :=
      hFc.continuousAt.tendsto.eventually
        (gt_mem_nhds (show F α < Real.exp (-K / R) by rw [hα]; exact Real.exp_pos _))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨δ, hδ, fun x hx => hδ' (by rwa [Real.dist_eq])⟩
  obtain ⟨ε, hε0, hεβ, hεc⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ β - α ∧
      ∀ x ∈ Icc α (α + ε), F x < Real.exp (-(M + 1) / R) := by
    obtain ⟨δ, hδ, hδ'⟩ := hsmall (M + 1)
    refine ⟨min (δ / 2) (β - α), lt_min (by linarith) (by linarith), min_le_right _ _,
      fun x hx => hδ' x ?_⟩
    rw [abs_lt]
    have h1 : min (δ / 2) (β - α) ≤ δ / 2 := min_le_left _ _
    constructor <;> linarith [hx.1, hx.2]
  have hFpos : ∀ x ∈ Ioc α (α + ε), 0 < F x := fun x hx => hpos x ⟨hx.1, by linarith [hx.2]⟩
  have hlogM : ∀ x ∈ Ioc α (α + ε), R * Real.log (F x) < -(M + 1) := fun x hx =>
    hlogK (M + 1) (F x) (hFpos x hx) (hεc x ⟨hx.1.le, hx.2⟩)
  have hSpos : ∀ x ∈ Ioc α (α + ε), 0 < M + R / 2 - R * Real.log (F x) := by
    intro x hx
    have := hlogM x hx
    linarith
  have hBpos : ∀ x ∈ Ioc α (α + ε), 0 < B x - R * Real.log (F x) := by
    intro x hx
    have h1 := hlogM x hx
    have h2 := (abs_le.1 (hB x)).1
    linarith
  have hF2pos : ∀ x ∈ Ioc α (α + ε), 0 < F2 x := fun x hx => by
    rw [hode]
    exact mul_pos (hFpos x hx) (hBpos x hx)
  -- `F1` is strictly increasing on `[α, α + ε]`, hence positive to the right of `α`
  have hmono : StrictMonoOn F1 (Icc α (α + ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hF1c.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd2 x).deriv]
    exact hF2pos x ⟨hx.1, hx.2.le⟩
  have hF1pos : ∀ x ∈ Ioc α (α + ε), 0 < F1 x := by
    intro x hx
    have := hmono ⟨le_refl α, by linarith⟩ ⟨hx.1.le, hx.2⟩ hx.1
    rwa [hF1α] at this
  -- the monotone quantity `E`
  set E : ℝ → ℝ := fun x =>
    F1 x * F1 x - (M + R / 2) * (F x * F x) + R * (F x * (F x * Real.log (F x))) with hE
  have hEc : Continuous E := by
    have h1 : Continuous fun x => F x * Real.log (F x) := Real.continuous_mul_log.comp hFc
    exact ((hF1c.mul hF1c).sub (continuous_const.mul (hFc.mul hFc))).add
      (continuous_const.mul (hFc.mul h1))
  have hEα : E α = 0 := by simp [hE, hα, hF1α]
  have hEd : ∀ x ∈ Ioc α (α + ε), HasDerivAt E (2 * F1 x * F x * (B x - M)) x := by
    intro x hx
    have hF0 : F x ≠ 0 := (hFpos x hx).ne'
    have hl := (hd1 x).log hF0
    have a1 := (hd2 x).mul (hd2 x)
    have a2 := ((hd1 x).mul (hd1 x)).const_mul (M + R / 2)
    have a3 := (hd1 x).mul ((hd1 x).mul hl)
    have h := (a1.sub a2).add (a3.const_mul R)
    refine h.congr_deriv ?_
    rw [hode x]
    simp only [Pi.mul_apply]
    field_simp
    ring
  have hEanti : AntitoneOn E (Icc α (α + ε)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hEc.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hEd x ⟨hx.1, hx.2.le⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Ioc α (α + ε) := ⟨hx.1, hx.2.le⟩
      rw [(hEd x hx').deriv]
      have hb : B x - M ≤ 0 := by linarith [(abs_le.1 (hB x)).2]
      have h1 : 0 ≤ (F1 x * F x) * (-(B x - M)) :=
        mul_nonneg (mul_pos (hF1pos x hx') (hFpos x hx')).le (neg_nonneg.2 hb)
      nlinarith [h1]
  have hEle : ∀ x ∈ Ioc α (α + ε), E x ≤ 0 := by
    intro x hx
    have := hEanti ⟨le_refl α, by linarith⟩ ⟨hx.1.le, hx.2⟩ hx.1.le
    rwa [hEα] at this
  -- `F1 ≤ F * Y`
  have hF1le : ∀ x ∈ Ioc α (α + ε),
      F1 x ≤ F x * Real.sqrt (M + R / 2 - R * Real.log (F x)) := by
    intro x hx
    have hS := hSpos x hx
    have hsq : Real.sqrt (M + R / 2 - R * Real.log (F x)) ^ 2 =
        M + R / 2 - R * Real.log (F x) := Real.sq_sqrt hS.le
    have hY := Real.sqrt_pos.2 hS
    have hF := hFpos x hx
    have hFY : 0 < F x * Real.sqrt (M + R / 2 - R * Real.log (F x)) := mul_pos hF hY
    have h1 := hEle x hx
    have h2 : F1 x ^ 2 ≤ F x ^ 2 * (M + R / 2 - R * Real.log (F x)) := by
      simp only [hE] at h1
      nlinarith [h1]
    by_contra hcon
    push Not at hcon
    have h3 : (F x * Real.sqrt (M + R / 2 - R * Real.log (F x))) ^ 2 < F1 x ^ 2 := by
      nlinarith [mul_pos (sub_pos.2 hcon) (add_pos hFY (hFY.trans hcon))]
    rw [mul_pow, hsq] at h3
    linarith
  -- derivative of `Y`
  have hYd : ∀ x ∈ Ioc α (α + ε),
      HasDerivAt (fun y => Real.sqrt (M + R / 2 - R * Real.log (F y)))
        ((-(R * (F1 x / F x))) / (2 * Real.sqrt (M + R / 2 - R * Real.log (F x)))) x := by
    intro x hx
    have hl := (hd1 x).log (hFpos x hx).ne'
    have hS := (hl.const_mul R).const_sub (M + R / 2)
    exact hS.sqrt (hSpos x hx).ne'
  have hYd' : ∀ x ∈ Ioc α (α + ε),
      -(R / 2) ≤ (-(R * (F1 x / F x))) / (2 * Real.sqrt (M + R / 2 - R * Real.log (F x))) := by
    intro x hx
    have hF := hFpos x hx
    have hY := Real.sqrt_pos.2 (hSpos x hx)
    have h1 := hF1le x hx
    have h2 : F1 x / F x ≤ Real.sqrt (M + R / 2 - R * Real.log (F x)) := by
      rw [div_le_iff₀ hF]
      linarith
    rw [le_div_iff₀ (mul_pos two_pos hY)]
    nlinarith [mul_le_mul_of_nonneg_left h2 hR.le]
  -- `Y + (R/2) x` is nondecreasing: `Y` is bounded on `(α, α + ε]`
  have hbound : ∀ x₁ ∈ Ioo α (α + ε),
      Real.sqrt (M + R / 2 - R * Real.log (F x₁)) ≤
        Real.sqrt (M + R / 2 - R * Real.log (F (α + ε))) + R / 2 * ε := by
    intro x₁ hx₁
    have hsub : Icc x₁ (α + ε) ⊆ Ioc α (α + ε) :=
      fun x hx => ⟨lt_of_lt_of_le hx₁.1 hx.1, hx.2⟩
    have hZd : ∀ x ∈ Ioc α (α + ε),
        HasDerivAt (fun y => Real.sqrt (M + R / 2 - R * Real.log (F y)) + R / 2 * y)
          ((-(R * (F1 x / F x))) / (2 * Real.sqrt (M + R / 2 - R * Real.log (F x))) + R / 2 * 1) x :=
      fun x hx => (hYd x hx).add ((hasDerivAt_id' x).const_mul (R / 2))
    have hZ : MonotoneOn (fun y => Real.sqrt (M + R / 2 - R * Real.log (F y)) + R / 2 * y)
        (Icc x₁ (α + ε)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      · intro x hx
        exact (hZd x (hsub hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hZd x (hsub ⟨hx.1.le, hx.2.le⟩)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hxx := hsub ⟨hx.1.le, hx.2.le⟩
        rw [(hZd x hxx).deriv]
        have := hYd' x hxx
        linarith
    have h := hZ ⟨le_refl x₁, by linarith [hx₁.2]⟩ ⟨hx₁.2.le, le_refl _⟩ hx₁.2.le
    dsimp only at h
    nlinarith [mul_pos hR (sub_pos.2 hx₁.1)]
  -- but `Y → ∞` at `α⁺`
  set Mb : ℝ := Real.sqrt (M + R / 2 - R * Real.log (F (α + ε))) + R / 2 * ε with hMb
  have hMb0 : 0 ≤ Mb := by rw [hMb]; positivity
  obtain ⟨δ, hδ, hδ'⟩ := hsmall (Mb ^ 2 + M + 1)
  set x₁ : ℝ := α + min (δ / 2) (ε / 2) with hx₁
  have hmin0 : 0 < min (δ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  have hmin1 : min (δ / 2) (ε / 2) ≤ δ / 2 := min_le_left _ _
  have hmin2 : min (δ / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
  have hx₁mem : x₁ ∈ Ioo α (α + ε) := ⟨by linarith, by linarith⟩
  have hFx₁ : F x₁ < Real.exp (-(Mb ^ 2 + M + 1) / R) := by
    apply hδ'
    rw [abs_lt]
    constructor <;> linarith
  have hlog := hlogK (Mb ^ 2 + M + 1) (F x₁) (hFpos x₁ ⟨hx₁mem.1, hx₁mem.2.le⟩) hFx₁
  have hSbig : Mb ^ 2 < M + R / 2 - R * Real.log (F x₁) := by linarith
  have hlt : Mb < Real.sqrt (M + R / 2 - R * Real.log (F x₁)) :=
    (Real.lt_sqrt hMb0).2 hSbig
  have := hbound x₁ hx₁mem
  linarith

/-- A nonnegative `C²` solution of the equation which is periodic and not identically zero has no
zero at all. -/
theorem pos_of_ode {R M : ℝ} (hR : 0 < R) {B : ℝ → ℝ} (hB : ∀ x, |B x| ≤ M)
    {F F1 F2 : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x) (hode : ∀ x, F2 x = F x * (B x - R * Real.log (F x)))
    (hper : Function.Periodic F 1) (hnz : ∃ x, 0 < F x) : ∀ x, 0 < F x := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hd1 x).continuousAt
  obtain ⟨β, hβ⟩ := hnz
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  have hx₀0 : F x₀ = 0 := le_antisymm hx₀ (hnn x₀)
  have key : ∃ a : ℝ, a ≤ β ∧ F a = 0 ∧ ∀ x, x ≤ β → F x = 0 → x ≤ a := by
    have hZne : ({x : ℝ | x ≤ β} ∩ {x | F x = 0}).Nonempty := by
      obtain ⟨n, hn⟩ := exists_nat_ge (x₀ - β)
      refine ⟨x₀ - n * 1, ?_, ?_⟩
      · show x₀ - n * 1 ≤ β
        linarith
      · show F (x₀ - n * 1) = 0
        rw [hper.sub_nat_mul_eq]
        exact hx₀0
    have hZbdd : BddAbove ({x : ℝ | x ≤ β} ∩ {x | F x = 0}) := ⟨β, fun x hx => hx.1⟩
    have hZclosed : IsClosed ({x : ℝ | x ≤ β} ∩ {x | F x = 0}) :=
      isClosed_Iic.inter (isClosed_eq hFc continuous_const)
    have hmem := hZclosed.csSup_mem hZne hZbdd
    exact ⟨sSup _, hmem.1, hmem.2, fun x hx h0 => le_csSup hZbdd ⟨hx, h0⟩⟩
  obtain ⟨a, haβ, ha0, hamax⟩ := key
  have hαβ : a < β := by
    refine lt_of_le_of_ne haβ fun h => ?_
    rw [h] at ha0
    linarith
  have hpos : ∀ x ∈ Ioc a β, 0 < F x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have h0 : F x = 0 := le_antisymm hneg (hnn x)
    have := hamax x hx.2 h0
    linarith [hx.1]
  exact not_zero_of_ode hR hB hd1 hd2 hnn hode hαβ ha0 hpos


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


/-- The case `R = 0`: a nonnegative `C²` solution of the linear equation `F'' = B F` with `B`
bounded that is positive somewhere is positive everywhere (Gronwall for `F² + F'²`). -/
theorem pos_of_linear_ode {M : ℝ} {B : ℝ → ℝ} (hB : ∀ x, |B x| ≤ M)
    {F F1 F2 : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x) (hode : ∀ x, F2 x = F x * B x) (hnz : ∃ x, 0 < F x) :
    ∀ x, 0 < F x := by
  obtain ⟨β, hβ⟩ := hnz
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  have hx₀0 : F x₀ = 0 := le_antisymm hx₀ (hnn x₀)
  have hF1 : F1 x₀ = 0 := by
    have hmin : IsLocalMin F x₀ :=
      Filter.Eventually.of_forall fun x => by rw [hx₀0]; exact hnn x
    exact hmin.hasDerivAt_eq_zero (hd1 x₀)
  have hM : 0 ≤ M := (abs_nonneg _).trans (hB 0)
  set K : ℝ := 1 + M with hK
  set E : ℝ → ℝ := fun x => F x * F x + F1 x * F1 x with hE
  have hEd : ∀ x, HasDerivAt E (2 * F x * F1 x * (1 + B x)) x := by
    intro x
    have h := ((hd1 x).mul (hd1 x)).add ((hd2 x).mul (hd2 x))
    refine h.congr_deriv ?_
    rw [hode x]; ring
  have hEbd : ∀ x, |2 * F x * F1 x * (1 + B x)| ≤ K * E x := by
    intro x
    have h1 : |2 * F x * F1 x| ≤ F x * F x + F1 x * F1 x := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (F x + F1 x), sq_nonneg (F x - F1 x)]
    have h2 : |1 + B x| ≤ K := by
      have := abs_add_le (1 : ℝ) (B x)
      rw [abs_one] at this
      linarith [hB x]
    rw [abs_mul]
    calc |2 * F x * F1 x| * |1 + B x| ≤ (F x * F x + F1 x * F1 x) * K :=
          mul_le_mul h1 h2 (abs_nonneg _) (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      _ = K * E x := by simp only [hE]; ring
  have hEnn : ∀ x, 0 ≤ E x := fun x => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have hEx₀ : E x₀ = 0 := by simp [hE, hx₀0, hF1]
  -- `E e^{-Kx}` is antitone, `E e^{Kx}` is monotone
  have hG1 : ∀ x, HasDerivAt (fun y => E y * Real.exp (-K * y))
      (Real.exp (-K * x) * (2 * F x * F1 x * (1 + B x) - K * E x)) x := by
    intro x
    have hexp : HasDerivAt (fun y => Real.exp (-K * y)) (Real.exp (-K * x) * (-K * 1)) x :=
      ((hasDerivAt_id' x).const_mul (-K)).exp
    refine ((hEd x).mul hexp).congr_deriv ?_
    ring
  have hG2 : ∀ x, HasDerivAt (fun y => E y * Real.exp (K * y))
      (Real.exp (K * x) * (2 * F x * F1 x * (1 + B x) + K * E x)) x := by
    intro x
    have hexp : HasDerivAt (fun y => Real.exp (K * y)) (Real.exp (K * x) * (K * 1)) x :=
      ((hasDerivAt_id' x).const_mul K).exp
    refine ((hEd x).mul hexp).congr_deriv ?_
    ring
  have hanti : Antitone (fun y => E y * Real.exp (-K * y)) := by
    refine antitone_of_deriv_nonpos (fun x => (hG1 x).differentiableAt) fun x => ?_
    rw [(hG1 x).deriv]
    have := (abs_le.1 (hEbd x)).2
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith)
  have hmono : Monotone (fun y => E y * Real.exp (K * y)) := by
    refine monotone_of_deriv_nonneg (fun x => (hG2 x).differentiableAt) fun x => ?_
    rw [(hG2 x).deriv]
    have := (abs_le.1 (hEbd x)).1
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hEzero : ∀ x, E x = 0 := by
    intro x
    rcases le_total x₀ x with h | h
    · have := hanti h
      simp only [hEx₀, zero_mul] at this
      have h0 : E x * Real.exp (-K * x) = 0 :=
        le_antisymm this (mul_nonneg (hEnn x) (Real.exp_pos _).le)
      exact (mul_eq_zero.1 h0).resolve_right (Real.exp_pos _).ne'
    · have := hmono h
      simp only [hEx₀, zero_mul] at this
      have h0 : E x * Real.exp (K * x) = 0 :=
        le_antisymm this (mul_nonneg (hEnn x) (Real.exp_pos _).le)
      exact (mul_eq_zero.1 h0).resolve_right (Real.exp_pos _).ne'
  have hFβ : F β = 0 := by
    have h := hEzero β
    simp only [hE] at h
    nlinarith [mul_self_nonneg (F β), mul_self_nonneg (F1 β)]
  linarith

/-- Positivity for `R ≥ 0`: both the nonlinear (`R > 0`) and the linear (`R = 0`) case. -/
theorem pos_of_ode_of_nonneg {R M : ℝ} (hR : 0 ≤ R) {B : ℝ → ℝ} (hB : ∀ x, |B x| ≤ M)
    {F F1 F2 : ℝ → ℝ} (hd1 : ∀ x, HasDerivAt F (F1 x) x) (hd2 : ∀ x, HasDerivAt F1 (F2 x) x)
    (hnn : ∀ x, 0 ≤ F x) (hode : ∀ x, F2 x = F x * (B x - R * Real.log (F x)))
    (hper : Function.Periodic F 1) (hnz : ∃ x, 0 < F x) : ∀ x, 0 < F x := by
  rcases hR.eq_or_lt with h0 | hpos
  · subst h0
    exact pos_of_linear_ode hB hd1 hd2 hnn (fun x => by rw [hode x]; ring) hnz
  · exact pos_of_ode hpos hB hd1 hd2 hnn hode hper hnz

end SharpLSI.FL.Ex.Reg
