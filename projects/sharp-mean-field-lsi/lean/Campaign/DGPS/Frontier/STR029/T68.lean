import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# STR029.68: Completeness of the periodic Hölder space

Task id: STR029.68 (node STR029), "Completeness of the periodic Hölder space".

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_68_completeness_periodic_holder_space`: the concrete real space
  `PeriodicHolder_STR02968` of `2π`-periodic continuous functions with finite circular
  `1/2`-Hölder seminorm, normed by `‖f‖∞ + [f]_{1/2}`, is complete, its norm is the stated formula,
  and the norm has the real normed-space properties (nonnegative, definite, triangle inequality,
  absolute homogeneity).
* `DGPS.Frontier.STR029.str029_68_completeness_periodic_holder_space_mem_iff`: membership in
  `PeriodicHolder_STR02968` is periodicity, continuity and a finite circular Hölder constant.
* `DGPS.Frontier.STR029.PeriodicHolder_STR02968`: the space (a real vector space of functions
  `ℝ → ℝ`) with `NormedAddCommGroup`, `NormedSpace ℝ` and `CompleteSpace` instances.
* `DGPS.Frontier.STR029.circDist_STR02968`, `supNorm_STR02968`, `holderSemi_STR02968`: the
  circular distance, the supremum norm and the circular Hölder seminorm used.

R5 notes:
* Concrete carrier: functions `ℝ → ℝ` with `Function.Periodic f (2π)`; the variable is the angle
  `t` (not the physical `x` with period `1`). The norm is the sum `‖f‖∞ + [f]_α` with
  `α = 1/2`, so this is the specification's norm, not the `PH` space of `x`-periodic functions.
* Circular distance is `dist` in `AddCircle (2π)`. The seminorm is the supremum over all pairs
  `(s, t)` of real representatives of `|f s - f t| / circDist s t ^ α`, with Lean's `x / 0 = 0` on
  pairs representing the same circle point; for periodic `f` this is the supremum over pairs of
  distinct circle points required by the specification (the quotient is `0` on the diagonal).
* The supremum `⨆` is Lean's `iSup` on `ℝ`, with junk value `0` for unbounded families; it is
  never reached because members are continuous and periodic, hence bounded, and have bounded
  Hölder quotients.
* Membership asks for continuity as well as a finite Hölder constant (the specification says
  continuous periodic Hölder); continuity is redundant for `α > 0` but is kept to match the text.
* Helper lemmas are proved for an arbitrary exponent `α > 0` (or any real where no property is needed); the
  space itself and the main statement are for `α = 1/2` only, as specified.
* The instances are attached to the new type `PeriodicHolder_STR02968` only. They are built from
  the Mathlib normed-space core structure; the metric is the one induced by the norm.
* Nothing from the campaign (`Par`, `Wsp`, optimizer chart, entropy, Fisher, the rate
  normalization) enters this task: it is purely a statement about the Hölder space.
-/

open Filter Topology Function

namespace DGPS.Frontier.STR029

/-- Circular distance on `ℝ / 2πℤ`. -/
noncomputable def circDist_STR02968 (s t : ℝ) : ℝ :=
  dist (s : AddCircle (2 * Real.pi)) (t : AddCircle (2 * Real.pi))

/-- The supremum norm (junk `0` for unbounded functions). -/
noncomputable def supNorm_STR02968 (g : ℝ → ℝ) : ℝ := ⨆ x, |g x|

/-- The circular Hölder seminorm. -/
noncomputable def holderSemi_STR02968 (α : ℝ) (g : ℝ → ℝ) : ℝ :=
  ⨆ p : ℝ × ℝ, |g p.1 - g p.2| / circDist_STR02968 p.1 p.2 ^ α

/-- A finite circular Hölder constant. -/
def HolderBdd_STR02968 (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s t, |g s - g t| ≤ C * circDist_STR02968 s t ^ α

/-- Periodic, continuous, with a finite circular Hölder constant. -/
def IsPerHolder_STR02968 (α : ℝ) (g : ℝ → ℝ) : Prop :=
  Periodic g (2 * Real.pi) ∧ Continuous g ∧ HolderBdd_STR02968 α g

theorem circDist_nonneg_STR02968 (s t : ℝ) : 0 ≤ circDist_STR02968 s t := dist_nonneg

theorem eq_of_circDist_eq_zero_STR02968 {g : ℝ → ℝ} (hg : Periodic g (2 * Real.pi)) {s t : ℝ}
    (h : circDist_STR02968 s t = 0) : g s = g t := by
  unfold circDist_STR02968 at h
  rw [dist_eq_zero, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨n, hn⟩ := h
  have : s = t + n * (2 * Real.pi) := by rw [zsmul_eq_mul] at hn; linarith
  rw [this]
  exact (hg.int_mul n) t

theorem supNorm_nonneg_STR02968 (g : ℝ → ℝ) : 0 ≤ supNorm_STR02968 g :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem bdd_of_periodic_STR02968 {g : ℝ → ℝ} (hp : Periodic g (2 * Real.pi)) (hc : Continuous g) :
    ∃ M : ℝ, ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ (by positivity) x
  rw [hxy]
  exact (hM y ⟨hy.1, hy.2.le⟩).trans (le_max_left _ _)

theorem IsPerHolder_STR02968.abs_le_supNorm {α : ℝ} {g : ℝ → ℝ} (h : IsPerHolder_STR02968 α g)
    (x : ℝ) : |g x| ≤ supNorm_STR02968 g := by
  obtain ⟨M, hM⟩ := bdd_of_periodic_STR02968 h.1 h.2.1
  exact le_ciSup (f := fun x => |g x|) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ x

theorem supNorm_le_STR02968 {g : ℝ → ℝ} {M : ℝ} (h : ∀ x, |g x| ≤ M) :
    supNorm_STR02968 g ≤ M := ciSup_le h

theorem holderSemi_nonneg_STR02968 (α : ℝ) (g : ℝ → ℝ) : 0 ≤ holderSemi_STR02968 α g :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (circDist_nonneg_STR02968 _ _) _)

theorem holderSemi_le_STR02968 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ s t, |g s - g t| ≤ C * circDist_STR02968 s t ^ α) : holderSemi_STR02968 α g ≤ C := by
  refine ciSup_le fun p => ?_
  by_cases hp : circDist_STR02968 p.1 p.2 = 0
  · simp [hp, hα.ne', hC]
  · have : 0 < circDist_STR02968 p.1 p.2 ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (circDist_nonneg_STR02968 _ _) (Ne.symm hp)) _
    rw [div_le_iff₀ this]
    exact h _ _

theorem abs_sub_le_holderSemi_mul_STR02968 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ} (hp : Periodic g (2 * Real.pi))
    (hb : HolderBdd_STR02968 α g) (s t : ℝ) :
    |g s - g t| ≤ holderSemi_STR02968 α g * circDist_STR02968 s t ^ α := by
  by_cases hd : circDist_STR02968 s t = 0
  · rw [eq_of_circDist_eq_zero_STR02968 hp hd, sub_self, abs_zero]
    exact mul_nonneg (holderSemi_nonneg_STR02968 _ _)
      (Real.rpow_nonneg (circDist_nonneg_STR02968 _ _) _)
  · have hpos : 0 < circDist_STR02968 s t ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (circDist_nonneg_STR02968 _ _) (Ne.symm hd)) _
    obtain ⟨C, hC, hg⟩ := hb
    have hbdd : BddAbove (Set.range fun p : ℝ × ℝ =>
        |g p.1 - g p.2| / circDist_STR02968 p.1 p.2 ^ α) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨p, rfl⟩
      by_cases hq : circDist_STR02968 p.1 p.2 = 0
      · simp [hq, hα.ne', hC]
      · rw [div_le_iff₀ (Real.rpow_pos_of_pos
          (lt_of_le_of_ne (circDist_nonneg_STR02968 _ _) (Ne.symm hq)) _)]
        exact hg _ _
    rw [← div_le_iff₀ hpos]
    exact le_ciSup hbdd (s, t)

theorem IsPerHolder_STR02968.sub {α : ℝ} {f g : ℝ → ℝ} (hf : IsPerHolder_STR02968 α f)
    (hg : IsPerHolder_STR02968 α g) : IsPerHolder_STR02968 α (f - g) := by
  obtain ⟨C, hC, hfC⟩ := hf.2.2
  obtain ⟨D, hD, hgD⟩ := hg.2.2
  refine ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, C + D, add_nonneg hC hD, fun s t => ?_⟩
  have h1 := hfC s t
  have h2 := hgD s t
  have h3 : |(f - g) s - (f - g) t| ≤ |f s - f t| + |g s - g t| := by
    simp only [Pi.sub_apply]
    calc _ = |(f s - f t) + -(g s - g t)| := by ring_nf
      _ ≤ |f s - f t| + |-(g s - g t)| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  nlinarith

theorem IsPerHolder_STR02968.add {α : ℝ} {f g : ℝ → ℝ} (hf : IsPerHolder_STR02968 α f)
    (hg : IsPerHolder_STR02968 α g) : IsPerHolder_STR02968 α (f + g) := by
  obtain ⟨C, hC, hfC⟩ := hf.2.2
  obtain ⟨D, hD, hgD⟩ := hg.2.2
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, C + D, add_nonneg hC hD, fun s t => ?_⟩
  have h1 := hfC s t
  have h2 := hgD s t
  have h3 : |(f + g) s - (f + g) t| ≤ |f s - f t| + |g s - g t| := by
    simp only [Pi.add_apply]
    calc _ = |(f s - f t) + (g s - g t)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith

theorem IsPerHolder_STR02968.smul {α : ℝ} {f : ℝ → ℝ} (c : ℝ) (hf : IsPerHolder_STR02968 α f) :
    IsPerHolder_STR02968 α (c • f) := by
  obtain ⟨C, hC, hfC⟩ := hf.2.2
  refine ⟨fun x => by simp only [Pi.smul_apply, hf.1 x], hf.2.1.const_smul c, |c| * C, mul_nonneg (abs_nonneg c) hC,
    fun s t => ?_⟩
  have h1 := hfC s t
  have h3 : |(c • f) s - (c • f) t| = |c| * |f s - f t| := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, abs_mul]
  rw [h3, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

theorem IsPerHolder_STR02968.zero (α : ℝ) : IsPerHolder_STR02968 α 0 :=
  ⟨fun _ => rfl, continuous_const, 0, le_rfl, fun s t => by simp⟩

/-- The real vector space of periodic continuous functions with a finite circular Hölder
constant of exponent `1/2`. -/
def holderSubmodule_STR02968 : Submodule ℝ (ℝ → ℝ) where
  carrier := {g | IsPerHolder_STR02968 (1 / 2) g}
  add_mem' := fun ha hb => IsPerHolder_STR02968.add ha hb
  zero_mem' := IsPerHolder_STR02968.zero _
  smul_mem' := fun c _ hf => IsPerHolder_STR02968.smul c hf

/-- The concrete periodic Hölder space `C^{0,1/2}` of `2π`-periodic functions. -/
def PeriodicHolder_STR02968 : Type := ↥holderSubmodule_STR02968

instance : AddCommGroup PeriodicHolder_STR02968 :=
  inferInstanceAs (AddCommGroup ↥holderSubmodule_STR02968)

instance : Module ℝ PeriodicHolder_STR02968 :=
  inferInstanceAs (Module ℝ ↥holderSubmodule_STR02968)

/-- The function underlying an element. -/
def PeriodicHolder_STR02968.val (f : PeriodicHolder_STR02968) : ℝ → ℝ :=
  Subtype.val (p := fun g => g ∈ holderSubmodule_STR02968) f

/-- Build an element from a function with the defining properties. -/
def PeriodicHolder_STR02968.mk (g : ℝ → ℝ) (h : IsPerHolder_STR02968 (1 / 2) g) :
    PeriodicHolder_STR02968 :=
  Subtype.mk (p := fun g => g ∈ holderSubmodule_STR02968) g h

theorem PeriodicHolder_STR02968.isPerHolder (f : PeriodicHolder_STR02968) :
    IsPerHolder_STR02968 (1 / 2) f.val :=
  Subtype.property (p := fun g => g ∈ holderSubmodule_STR02968) f

noncomputable instance : Norm PeriodicHolder_STR02968 :=
  ⟨fun f => supNorm_STR02968 f.val + holderSemi_STR02968 (1 / 2) f.val⟩

theorem PeriodicHolder_STR02968.norm_def (f : PeriodicHolder_STR02968) :
    ‖f‖ = supNorm_STR02968 f.val + holderSemi_STR02968 (1 / 2) f.val := rfl

theorem PeriodicHolder_STR02968.val_sub (f g : PeriodicHolder_STR02968) :
    (f - g).val = f.val - g.val := rfl

theorem PeriodicHolder_STR02968.val_add (f g : PeriodicHolder_STR02968) :
    (f + g).val = f.val + g.val := rfl

theorem PeriodicHolder_STR02968.val_smul (c : ℝ) (f : PeriodicHolder_STR02968) :
    (c • f).val = c • f.val := rfl

theorem PeriodicHolder_STR02968.val_eq_zero {f : PeriodicHolder_STR02968} :
    f.val = 0 ↔ f = 0 :=
  ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

theorem half_pos_STR02968 : (0 : ℝ) < 1 / 2 := by norm_num

theorem normCore_STR02968 : NormedSpace.Core ℝ PeriodicHolder_STR02968 where
  norm_nonneg f := add_nonneg (supNorm_nonneg_STR02968 _) (holderSemi_nonneg_STR02968 _ _)
  norm_smul c f := by
    rw [Real.norm_eq_abs, PeriodicHolder_STR02968.norm_def, PeriodicHolder_STR02968.norm_def,
      PeriodicHolder_STR02968.val_smul, mul_add]
    unfold supNorm_STR02968 holderSemi_STR02968
    rw [Real.mul_iSup_of_nonneg (abs_nonneg c), Real.mul_iSup_of_nonneg (abs_nonneg c)]
    congr 1
    · refine iSup_congr fun x => ?_
      simp [abs_mul]
    · refine iSup_congr fun p => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_sub, abs_mul, mul_div_assoc]
  norm_triangle f g := by
    simp only [PeriodicHolder_STR02968.norm_def, PeriodicHolder_STR02968.val_add]
    have h1 : supNorm_STR02968 (f.val + g.val) ≤ supNorm_STR02968 f.val + supNorm_STR02968 g.val :=
      supNorm_le_STR02968 fun x => by
        simp only [Pi.add_apply]
        exact (abs_add_le _ _).trans (add_le_add (f.isPerHolder.abs_le_supNorm x)
          (g.isPerHolder.abs_le_supNorm x))
    have h2 : holderSemi_STR02968 (1 / 2) (f.val + g.val) ≤
        holderSemi_STR02968 (1 / 2) f.val + holderSemi_STR02968 (1 / 2) g.val := by
      refine holderSemi_le_STR02968 half_pos_STR02968
        (add_nonneg (holderSemi_nonneg_STR02968 _ _) (holderSemi_nonneg_STR02968 _ _))
        fun s t => ?_
      have a1 := abs_sub_le_holderSemi_mul_STR02968 half_pos_STR02968 f.isPerHolder.1
        f.isPerHolder.2.2 s t
      have a2 := abs_sub_le_holderSemi_mul_STR02968 half_pos_STR02968 g.isPerHolder.1
        g.isPerHolder.2.2 s t
      have a3 : |(f.val + g.val) s - (f.val + g.val) t| ≤ |f.val s - f.val t| + |g.val s - g.val t| := by
        simp only [Pi.add_apply]
        calc _ = |(f.val s - f.val t) + (g.val s - g.val t)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      nlinarith
    linarith
  norm_eq_zero_iff f := by
    rw [PeriodicHolder_STR02968.norm_def, ← PeriodicHolder_STR02968.val_eq_zero]
    constructor
    · intro h
      have h1 := supNorm_nonneg_STR02968 f.val
      have h2 := holderSemi_nonneg_STR02968 (1 / 2) f.val
      funext x
      have := f.isPerHolder.abs_le_supNorm x
      have : |f.val x| ≤ 0 := by linarith
      simpa using this
    · intro h
      rw [h]
      have h1 : supNorm_STR02968 (0 : ℝ → ℝ) ≤ 0 := supNorm_le_STR02968 fun x => by simp
      have h2 : holderSemi_STR02968 (1 / 2) (0 : ℝ → ℝ) ≤ 0 :=
        holderSemi_le_STR02968 half_pos_STR02968 le_rfl fun s t => by simp
      linarith [supNorm_nonneg_STR02968 (0 : ℝ → ℝ), holderSemi_nonneg_STR02968 (1 / 2) (0 : ℝ → ℝ)]

noncomputable instance : NormedAddCommGroup PeriodicHolder_STR02968 := NormedAddCommGroup.ofCore normCore_STR02968

noncomputable instance : NormedSpace ℝ PeriodicHolder_STR02968 := NormedSpace.ofCore normCore_STR02968

/-- Cauchy sequences in the full norm have a limit in the full norm. -/
theorem complete_aux_STR02968 (u : ℕ → ℝ → ℝ) (hu : ∀ n, IsPerHolder_STR02968 (1 / 2) (u n))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      supNorm_STR02968 (u m - u n) + holderSemi_STR02968 (1 / 2) (u m - u n) < ε) :
    ∃ F, IsPerHolder_STR02968 (1 / 2) F ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N,
      supNorm_STR02968 (u n - F) + holderSemi_STR02968 (1 / 2) (u n - F) ≤ ε := by
  have hα := half_pos_STR02968
  have hcs : ∀ x, CauchySeq fun n => u n x := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := ((hu m).sub (hu n)).abs_le_supNorm x
    have h2 := hN m hm n hn
    have h3 := holderSemi_nonneg_STR02968 (1 / 2) (u m - u n)
    rw [Real.dist_eq]
    simp only [Pi.sub_apply] at h1
    linarith
  choose F hF using fun x => cauchySeq_tendsto_of_complete (hcs x)
  have hunif : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |u n x - F x| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn x => ?_⟩
    have key : ∀ m ≥ N, |u n x - u m x| ≤ ε := by
      intro m hm
      have h1 := ((hu n).sub (hu m)).abs_le_supNorm x
      have h2 := hN n hn m hm
      have h3 := holderSemi_nonneg_STR02968 (1 / 2) (u n - u m)
      simp only [Pi.sub_apply] at h1
      linarith
    have : Tendsto (fun m => |u n x - u m x|) atTop (𝓝 |u n x - F x|) :=
      (tendsto_const_nhds.sub (hF x)).abs
    exact le_of_tendsto this (eventually_atTop.mpr ⟨N, key⟩)
  have hhol : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ s t,
      |(u n s - F s) - (u n t - F t)| ≤ ε * circDist_STR02968 s t ^ (1 / 2 : ℝ) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn s t => ?_⟩
    have key : ∀ m ≥ N, |(u n s - u m s) - (u n t - u m t)| ≤
        ε * circDist_STR02968 s t ^ (1 / 2 : ℝ) := by
      intro m hm
      have h1 := abs_sub_le_holderSemi_mul_STR02968 hα ((hu n).sub (hu m)).1
        ((hu n).sub (hu m)).2.2 s t
      have h2 : holderSemi_STR02968 (1 / 2) (u n - u m) ≤ ε := by
        have := hN n hn m hm
        linarith [supNorm_nonneg_STR02968 (u n - u m)]
      simp only [Pi.sub_apply] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right h2
        (Real.rpow_nonneg (circDist_nonneg_STR02968 _ _) _))
    have : Tendsto (fun m => |(u n s - u m s) - (u n t - u m t)|) atTop
        (𝓝 |(u n s - F s) - (u n t - F t)|) :=
      (((tendsto_const_nhds.sub (hF s)).sub (tendsto_const_nhds.sub (hF t)))).abs
    exact le_of_tendsto this (eventually_atTop.mpr ⟨N, key⟩)
  have hper : Periodic F (2 * Real.pi) := fun x => by
    have h2 : Tendsto (fun n => u n (x + 2 * Real.pi)) atTop (𝓝 (F x)) := by
      have : (fun n => u n (x + 2 * Real.pi)) = fun n => u n x :=
        funext fun n => (hu n).1 x
      rw [this]; exact hF x
    exact tendsto_nhds_unique (hF (x + 2 * Real.pi)) h2
  have hcont : Continuous F := by
    refine TendstoUniformly.continuous (F := u) (p := atTop) ?_
      (Eventually.of_forall fun n => (hu n).2.1).frequently
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    linarith [hN n hn x]
  have hFmem : IsPerHolder_STR02968 (1 / 2) F := by
    refine ⟨hper, hcont, ?_⟩
    obtain ⟨N, hN⟩ := hhol 1 one_pos
    obtain ⟨C, hC0, hCN⟩ := (hu N).2.2
    refine ⟨C + 1, by linarith, fun s t => ?_⟩
    have h1 := hCN s t
    have h2 := hN N le_rfl s t
    have h3 : |F s - F t| ≤ |u N s - u N t| + |(u N s - F s) - (u N t - F t)| := by
      calc _ = |(u N s - u N t) - ((u N s - F s) - (u N t - F t))| := by ring_nf
        _ ≤ _ := abs_sub _ _
    nlinarith
  refine ⟨F, hFmem, fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hunif (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hhol (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have e1 : supNorm_STR02968 (u n - F) ≤ ε / 2 :=
    supNorm_le_STR02968 fun x => hN₁ n ((le_max_left _ _).trans hn) x
  have e2 : holderSemi_STR02968 (1 / 2) (u n - F) ≤ ε / 2 :=
    holderSemi_le_STR02968 hα (half_pos hε).le fun s t =>
      hN₂ n ((le_max_right _ _).trans hn) s t
  linarith

instance : CompleteSpace PeriodicHolder_STR02968 := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      supNorm_STR02968 ((f m).val - (f n).val) +
        holderSemi_STR02968 (1 / 2) ((f m).val - (f n).val) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hN m hm n hn
    rwa [dist_eq_norm, PeriodicHolder_STR02968.norm_def] at this
  obtain ⟨F, hF, hlim⟩ := complete_aux_STR02968 (fun n => (f n).val) (fun n => (f n).isPerHolder) hC
  refine ⟨PeriodicHolder_STR02968.mk F hF, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, PeriodicHolder_STR02968.norm_def]
  have := hN n hn
  change supNorm_STR02968 ((f n).val - F) + holderSemi_STR02968 (1 / 2) ((f n).val - F) < ε
  linarith

/-- Membership in the space: periodicity, continuity and a finite circular Hölder constant. -/
theorem str029_68_completeness_periodic_holder_space_mem_iff (g : ℝ → ℝ) :
    g ∈ holderSubmodule_STR02968 ↔ Periodic g (2 * Real.pi) ∧ Continuous g ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s t, |g s - g t| ≤ C * circDist_STR02968 s t ^ (1 / 2 : ℝ) :=
  Iff.rfl

/-- STR029.68: the concrete periodic Hölder space with norm `‖f‖∞ + [f]_{1/2}` is complete, and
its norm and vector operations have the real normed-space properties. -/
theorem str029_68_completeness_periodic_holder_space :
    CompleteSpace PeriodicHolder_STR02968 ∧
    (∀ f : PeriodicHolder_STR02968,
      ‖f‖ = supNorm_STR02968 f.val + holderSemi_STR02968 (1 / 2) f.val) ∧
    (∀ f : PeriodicHolder_STR02968, 0 ≤ ‖f‖) ∧
    (∀ f : PeriodicHolder_STR02968, ‖f‖ = 0 ↔ f = 0) ∧
    (∀ f g : PeriodicHolder_STR02968, ‖f + g‖ ≤ ‖f‖ + ‖g‖) ∧
    (∀ (c : ℝ) (f : PeriodicHolder_STR02968), ‖c • f‖ = |c| * ‖f‖) :=
  ⟨inferInstance, fun _ => rfl, fun _ => norm_nonneg _, fun _ => norm_eq_zero,
    fun _ _ => norm_add_le _ _, fun c f => by rw [norm_smul, Real.norm_eq_abs]⟩

end DGPS.Frontier.STR029
