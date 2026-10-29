import DGPS.Frontier.STR029.T53
import DGPS.Frontier.STR029.T68

/-!
# STR029.69: Completeness and closed complements for the range spaces

Task id: STR029.69 (node STR029), "Completeness and closed complements for the range spaces".

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_69_completeness_closed_complements_range_spaces`: the main theorem.
  The concrete periodic `C^{2,1/2}` space `PeriodicC2_STR02969` with norm
  `‖u‖∞ + ‖u'‖∞ + ‖u''‖∞ + [u'']_{1/2}` is complete; its subspace `E_STR02969` cut out by the three
  Haar/Fourier constraints is closed and complete; the subspace `Y_STR02969` of the periodic
  Hölder space `PeriodicHolder_STR02968` cut out by the same three constraints is closed and
  complete.
* `DGPS.Frontier.STR029.str029_69_completeness_closed_complements_range_spaces_complete`: the
  space `PeriodicC2_STR02969` is complete and its norm is the stated formula.
* `DGPS.Frontier.STR029.str029_69_completeness_closed_complements_range_spaces_E`: membership in
  `E_STR02969` is `InE_STR02901`, the subspace is closed and complete.
* `DGPS.Frontier.STR029.str029_69_completeness_closed_complements_range_spaces_Y`: membership in
  `Y_STR02969` is `InE_STR02901`, the subspace is closed and complete.
* `DGPS.Frontier.STR029.PeriodicC2_STR02969`: the concrete real vector space of `2π`-periodic
  `C^{2,1/2}` functions with `NormedAddCommGroup`, `NormedSpace ℝ` and `CompleteSpace` instances.
* `DGPS.Frontier.STR029.E_STR02969`, `DGPS.Frontier.STR029.Y_STR02969`: the two constraint
  subspaces (kernels of the mean and the two first-harmonic pairings).

R5 notes:
* Carriers. No parallel carrier is introduced: the class of functions is `IsC2Alpha_STR02901 (1/2)`
  and the norm is `c2Norm_STR02901 (1/2)` (both from `.01`), and the Hölder space for `Y` is the
  normed space `PeriodicHolder_STR02968` of `.68`. `PeriodicC2_STR02969` is only the normed-space
  structure on the subtype of the class (the earlier packets give predicates, not a normed space).
  The variable is the angle `t` (period `2π`), as in the specification; the identification with the
  packet chart space `Wsp` is the carrier equivalence of `.01`, not repeated here.
* Exponent. Fixed `α = 1/2`, the case of the specification (the earlier packets hold for every
  admissible `α`, but the normed space of `.68` is for `1/2`).
* Constraints. `E` and `Y` are both the kernels of `f ↦ ∫ f dm`, `f ↦ ∫ f cos dm`, `f ↦ ∫ f sin dm`
  (`meanT_STR02901`, `pair_STR02953`), that is the concrete predicate `InE_STR02901` of `.01`;
  `E` lives in `C^{2,α}` and `Y` lives in `C^{0,α}` (the range space). The functionals are
  built here on each normed space from the pointwise lemmas of `.53` (additivity, homogeneity and
  the sup-norm bound), with bound constant `1`: `|∫ f b dm| ≤ ‖f‖∞ ‖b‖∞ ≤ ‖f‖`.
* Closedness is proved as continuity of three bounded linear functionals (preimages of `{0}`);
  completeness of the subspaces is `IsClosed.completeSpace_coe`. "Banach space" is read as
  `NormedAddCommGroup`, `NormedSpace ℝ` (instances of the subspace) together with `CompleteSpace`.
* Proof route. Instead of passing to the limit in the integral identity
  `u(t) - u(0) = ∫_0^t u'`, the proof uses the equivalent Mathlib theorem that uniform limits of
  differentiable functions with uniformly convergent derivatives are differentiable with the limit
  derivative (`hasDerivAt_of_tendstoUniformly`). The convergence of `u_n''` in `C^{0,1/2}` is
  the completeness argument of `.68` (`complete_aux_STR02968`); the periodic identity of the limit
  is the pointwise limit of the periodic identities.
* The sup norm is `supNorm` (value `0` for unbounded functions, never reached here since all
  functions are periodic and continuous), identified with `supNorm_STR02968` by `rfl`; likewise the
  circular distance and Hölder seminorm of `.68` and `.01` are definitionally equal.
-/

open Filter Topology Function DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Bridges between the two earlier conventions -/

theorem second_isPerHolder_STR02969 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsPerHolder_STR02968 (1 / 2) (deriv (deriv u)) :=
  ⟨periodic_deriv_STR02901 (periodic_deriv_STR02901 hu.1), hu.2.2.2.1, hu.2.2.2.2⟩

theorem c0_second_STR02969 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsC0Alpha_STR02953 (1 / 2) (deriv (deriv u)) :=
  ⟨periodic_deriv_STR02901 (periodic_deriv_STR02901 hu.1), hu.2.2.2.2⟩

theorem bdd_parts_STR02969 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    Bdd u ∧ Bdd (deriv u) ∧ Bdd (deriv (deriv u)) :=
  ⟨bdd_of_periodic_continuous_STR02953 hu.1 hu.2.1.continuous,
    bdd_of_periodic_continuous_STR02953 (periodic_deriv_STR02901 hu.1) hu.2.2.1.continuous,
    bdd_of_periodic_continuous_STR02953 (periodic_deriv_STR02901 (periodic_deriv_STR02901 hu.1))
      hu.2.2.2.1⟩

/-! ### Derivatives of sums, differences and multiples -/

theorem deriv_add_fun_STR02969 {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (f + g) = deriv f + deriv g :=
  funext fun x => deriv_add (hf x) (hg x)

theorem deriv_sub_fun_STR02969 {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    deriv (f - g) = deriv f - deriv g :=
  funext fun x => deriv_sub (hf x) (hg x)

theorem deriv_smul_fun_STR02969 (c : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (c • f) = c • deriv f :=
  funext fun x => deriv_const_smul c (hf x)

theorem deriv_zero_fun_STR02969 : deriv (0 : ℝ → ℝ) = 0 := funext fun x => by simp

/-! ### The class `C^{2,1/2}` is a vector space -/

theorem c2_add_STR02969 {f g : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f)
    (hg : IsC2Alpha_STR02901 (1 / 2) g) : IsC2Alpha_STR02901 (1 / 2) (f + g) := by
  have e1 := deriv_add_fun_STR02969 hf.2.1 hg.2.1
  have e2 : deriv (deriv (f + g)) = deriv (deriv f) + deriv (deriv g) := by
    rw [e1]; exact deriv_add_fun_STR02969 hf.2.2.1 hg.2.2.1
  have h := (second_isPerHolder_STR02969 hf).add (second_isPerHolder_STR02969 hg)
  refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, ?_, ?_, ?_⟩
  · rw [e1]; exact hf.2.2.1.add hg.2.2.1
  · rw [e2]; exact h.2.1
  · rw [e2]; exact h.2.2

theorem c2_smul_STR02969 (c : ℝ) {f : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f) :
    IsC2Alpha_STR02901 (1 / 2) (c • f) := by
  have e1 := deriv_smul_fun_STR02969 c hf.2.1
  have e2 : deriv (deriv (c • f)) = c • deriv (deriv f) := by
    rw [e1]; exact deriv_smul_fun_STR02969 c hf.2.2.1
  have h := (second_isPerHolder_STR02969 hf).smul c
  refine ⟨fun x => by simp only [Pi.smul_apply, hf.1 x], hf.2.1.const_smul c, ?_, ?_, ?_⟩
  · rw [e1]; exact hf.2.2.1.const_smul c
  · rw [e2]; exact h.2.1
  · rw [e2]; exact h.2.2

theorem c2_zero_STR02969 : IsC2Alpha_STR02901 (1 / 2) (0 : ℝ → ℝ) := by
  have h := IsPerHolder_STR02968.zero (1 / 2 : ℝ)
  refine ⟨fun _ => rfl, differentiable_const _, ?_, ?_, ?_⟩
  · rw [deriv_zero_fun_STR02969]; exact differentiable_const _
  · rw [deriv_zero_fun_STR02969, deriv_zero_fun_STR02969]; exact h.2.1
  · rw [deriv_zero_fun_STR02969, deriv_zero_fun_STR02969]; exact h.2.2

/-- The real vector space of `2π`-periodic `C^{2,1/2}` functions. -/
def c2Submodule_STR02969 : Submodule ℝ (ℝ → ℝ) where
  carrier := {u | IsC2Alpha_STR02901 (1 / 2) u}
  add_mem' := fun ha hb => c2_add_STR02969 ha hb
  zero_mem' := c2_zero_STR02969
  smul_mem' := fun c _ hf => c2_smul_STR02969 c hf

/-- The concrete periodic `C^{2,1/2}` space. -/
def PeriodicC2_STR02969 : Type := ↥c2Submodule_STR02969

instance : AddCommGroup PeriodicC2_STR02969 :=
  inferInstanceAs (AddCommGroup ↥c2Submodule_STR02969)

instance : Module ℝ PeriodicC2_STR02969 :=
  inferInstanceAs (Module ℝ ↥c2Submodule_STR02969)

/-- The function underlying an element. -/
def PeriodicC2_STR02969.val (f : PeriodicC2_STR02969) : ℝ → ℝ :=
  Subtype.val (p := fun g => g ∈ c2Submodule_STR02969) f

/-- Build an element from a function of the class. -/
def PeriodicC2_STR02969.mk (g : ℝ → ℝ) (h : IsC2Alpha_STR02901 (1 / 2) g) : PeriodicC2_STR02969 :=
  Subtype.mk (p := fun g => g ∈ c2Submodule_STR02969) g h

theorem PeriodicC2_STR02969.isC2 (f : PeriodicC2_STR02969) : IsC2Alpha_STR02901 (1 / 2) f.val :=
  Subtype.property (p := fun g => g ∈ c2Submodule_STR02969) f

theorem PeriodicC2_STR02969.val_sub (f g : PeriodicC2_STR02969) : (f - g).val = f.val - g.val := rfl

theorem PeriodicC2_STR02969.val_add (f g : PeriodicC2_STR02969) : (f + g).val = f.val + g.val := rfl

theorem PeriodicC2_STR02969.val_smul (c : ℝ) (f : PeriodicC2_STR02969) :
    (c • f).val = c • f.val := rfl

theorem PeriodicC2_STR02969.val_eq_zero {f : PeriodicC2_STR02969} : f.val = 0 ↔ f = 0 :=
  ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

/-! ### The norm -/

theorem c2Norm_parts_STR02969 (u : ℝ → ℝ) :
    c2Norm_STR02901 (1 / 2) u = supNorm u + supNorm (deriv u) +
      (supNorm (deriv (deriv u)) + circHolder_STR02901 (1 / 2) (deriv (deriv u))) := by
  unfold c2Norm_STR02901; ring

theorem le_c2Norm_STR02969 (u : ℝ → ℝ) :
    supNorm u ≤ c2Norm_STR02901 (1 / 2) u ∧ supNorm (deriv u) ≤ c2Norm_STR02901 (1 / 2) u ∧
      supNorm (deriv (deriv u)) + circHolder_STR02901 (1 / 2) (deriv (deriv u)) ≤
        c2Norm_STR02901 (1 / 2) u := by
  have h1 := supNorm_nonneg u
  have h2 := supNorm_nonneg (deriv u)
  have h3 := supNorm_nonneg (deriv (deriv u))
  have h4 := circHolder_nonneg_STR02953 (1 / 2) (deriv (deriv u))
  rw [c2Norm_parts_STR02969]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem c2Norm_nonneg_STR02969 (u : ℝ → ℝ) : 0 ≤ c2Norm_STR02901 (1 / 2) u := by
  have h := le_c2Norm_STR02969 u
  linarith [supNorm_nonneg u]

theorem supNorm_smul_eq_STR02969 (c : ℝ) (f : ℝ → ℝ) : supNorm (c • f) = |c| * supNorm f := by
  unfold supNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  refine iSup_congr fun x => ?_
  simp [abs_mul]

theorem circHolder_smul_eq_STR02969 (c : ℝ) (f : ℝ → ℝ) :
    circHolder_STR02901 (1 / 2) (c • f) = |c| * circHolder_STR02901 (1 / 2) f := by
  unfold circHolder_STR02901
  rw [Real.mul_iSup_of_nonneg (abs_nonneg c)]
  refine iSup_congr fun p => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_sub, abs_mul, mul_div_assoc]

theorem c2Norm_smul_STR02969 (c : ℝ) {f : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f) :
    c2Norm_STR02901 (1 / 2) (c • f) = |c| * c2Norm_STR02901 (1 / 2) f := by
  have d1 := deriv_smul_fun_STR02969 c hf.2.1
  have d2 : deriv (deriv (c • f)) = c • deriv (deriv f) := by
    rw [d1]; exact deriv_smul_fun_STR02969 c hf.2.2.1
  rw [c2Norm_parts_STR02969, c2Norm_parts_STR02969, d2, d1, supNorm_smul_eq_STR02969,
    supNorm_smul_eq_STR02969, supNorm_smul_eq_STR02969, circHolder_smul_eq_STR02969]
  ring

theorem c2Norm_add_le_STR02969 {f g : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f)
    (hg : IsC2Alpha_STR02901 (1 / 2) g) :
    c2Norm_STR02901 (1 / 2) (f + g) ≤ c2Norm_STR02901 (1 / 2) f + c2Norm_STR02901 (1 / 2) g := by
  have d1 := deriv_add_fun_STR02969 hf.2.1 hg.2.1
  have d2 : deriv (deriv (f + g)) = deriv (deriv f) + deriv (deriv g) := by
    rw [d1]; exact deriv_add_fun_STR02969 hf.2.2.1 hg.2.2.1
  obtain ⟨bf, bf', bf''⟩ := bdd_parts_STR02969 hf
  obtain ⟨bg, bg', bg''⟩ := bdd_parts_STR02969 hg
  have s0 : supNorm (f + g) ≤ supNorm f + supNorm g := supNorm_add_le bf bg
  have s1 : supNorm (deriv f + deriv g) ≤ supNorm (deriv f) + supNorm (deriv g) :=
    supNorm_add_le bf' bg'
  have s2 := (c0_add_STR02953 (half_pos_STR02968) (c0_second_STR02969 hf)
    (c0_second_STR02969 hg)).2
  unfold c0Norm_STR02953 at s2
  rw [c2Norm_parts_STR02969, c2Norm_parts_STR02969, c2Norm_parts_STR02969, d2, d1]
  linarith

theorem c2Norm_zero_STR02969 : c2Norm_STR02901 (1 / 2) (0 : ℝ → ℝ) = 0 := by
  rw [c2Norm_parts_STR02969]
  simp only [deriv_zero_fun_STR02969]
  have h1 : supNorm (0 : ℝ → ℝ) ≤ 0 := supNorm_le fun x => by simp
  have h2 : circHolder_STR02901 (1 / 2) (0 : ℝ → ℝ) ≤ 0 :=
    circHolder_le_STR02953 half_pos_STR02968 le_rfl fun s t => by simp
  linarith [supNorm_nonneg (0 : ℝ → ℝ), circHolder_nonneg_STR02953 (1 / 2) (0 : ℝ → ℝ)]

noncomputable instance : Norm PeriodicC2_STR02969 := ⟨fun f => c2Norm_STR02901 (1 / 2) f.val⟩

theorem PeriodicC2_STR02969.norm_def (f : PeriodicC2_STR02969) :
    ‖f‖ = c2Norm_STR02901 (1 / 2) f.val := rfl

theorem normCore_STR02969 : NormedSpace.Core ℝ PeriodicC2_STR02969 where
  norm_nonneg f := c2Norm_nonneg_STR02969 _
  norm_smul c f := by
    rw [Real.norm_eq_abs, PeriodicC2_STR02969.norm_def, PeriodicC2_STR02969.norm_def,
      PeriodicC2_STR02969.val_smul]
    exact c2Norm_smul_STR02969 c f.isC2
  norm_triangle f g := by
    rw [PeriodicC2_STR02969.norm_def, PeriodicC2_STR02969.norm_def, PeriodicC2_STR02969.norm_def,
      PeriodicC2_STR02969.val_add]
    exact c2Norm_add_le_STR02969 f.isC2 g.isC2
  norm_eq_zero_iff f := by
    rw [PeriodicC2_STR02969.norm_def, ← PeriodicC2_STR02969.val_eq_zero]
    constructor
    · intro h
      have h1 := (le_c2Norm_STR02969 f.val).1
      funext x
      have := (bdd_parts_STR02969 f.isC2).1.abs_le_supNorm x
      have : |f.val x| ≤ 0 := by linarith
      simpa using this
    · intro h
      rw [h]
      exact c2Norm_zero_STR02969

noncomputable instance : NormedAddCommGroup PeriodicC2_STR02969 :=
  NormedAddCommGroup.ofCore normCore_STR02969

noncomputable instance : NormedSpace ℝ PeriodicC2_STR02969 := NormedSpace.ofCore normCore_STR02969

/-! ### Completeness -/

/-- A uniformly Cauchy sequence of real functions has a uniform limit. -/
theorem unif_limit_STR02969 (f : ℕ → ℝ → ℝ)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x, |f m x - f n x| ≤ ε) :
    ∃ F : ℝ → ℝ, TendstoUniformly f F atTop := by
  have hcs : ∀ x, CauchySeq fun n => f n x := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
    exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; linarith [hN m hm n hn x]⟩
  choose F hF using fun x => cauchySeq_tendsto_of_complete (hcs x)
  refine ⟨F, Metric.tendstoUniformly_iff.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hC (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop N] with n hn x
  have h : Tendsto (fun m => |f n x - f m x|) atTop (𝓝 |f n x - F x|) :=
    (tendsto_const_nhds.sub (hF x)).abs
  have := le_of_tendsto h (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm x⟩)
  rw [Real.dist_eq, abs_sub_comm]
  linarith

theorem abs_le_of_tendstoUniformly_STR02969 {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (h : TendstoUniformly f F atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ x, |f n x - F x| ≤ ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformly_iff.mp h ε hε)
  exact ⟨N, fun n hn x => by have := hN n hn x; rw [Real.dist_eq, abs_sub_comm] at this; exact this.le⟩

theorem c2_sub_STR02969 {f g : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f)
    (hg : IsC2Alpha_STR02901 (1 / 2) g) : IsC2Alpha_STR02901 (1 / 2) (f - g) :=
  c2Submodule_STR02969.sub_mem hf hg

theorem deriv2_sub_STR02969 {f g : ℝ → ℝ} (hf : IsC2Alpha_STR02901 (1 / 2) f)
    (hg : IsC2Alpha_STR02901 (1 / 2) g) :
    deriv (f - g) = deriv f - deriv g ∧
      deriv (deriv (f - g)) = deriv (deriv f) - deriv (deriv g) := by
  have d1 := deriv_sub_fun_STR02969 hf.2.1 hg.2.1
  exact ⟨d1, by rw [d1]; exact deriv_sub_fun_STR02969 hf.2.2.1 hg.2.2.1⟩

theorem third_pos_STR02969 {ε : ℝ} (h : 0 < ε) : 0 < ε / 3 := by positivity

/-- Cauchy sequences in the full `C^{2,1/2}` norm have a limit in the full norm. -/
theorem c2_complete_aux_STR02969 (u : ℕ → ℝ → ℝ) (hu : ∀ n, IsC2Alpha_STR02901 (1 / 2) (u n))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, c2Norm_STR02901 (1 / 2) (u m - u n) < ε) :
    ∃ F, IsC2Alpha_STR02901 (1 / 2) F ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N,
      c2Norm_STR02901 (1 / 2) (u n - F) ≤ ε := by
  -- the function, first and second derivative sequences are Cauchy
  have hs0 : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x, |u m x - u n x| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn x => ?_⟩
    have h1 := ((bdd_parts_STR02969 (c2_sub_STR02969 (hu m) (hu n))).1).abs_le_supNorm x
    have h2 := (le_c2Norm_STR02969 (u m - u n)).1
    have h3 := hN m hm n hn
    simp only [Pi.sub_apply] at h1
    linarith
  have hs1 : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∀ x, |deriv (u m) x - deriv (u n) x| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn x => ?_⟩
    have hmn := c2_sub_STR02969 (hu m) (hu n)
    have h1 := ((bdd_parts_STR02969 hmn).2.1).abs_le_supNorm x
    have h2 := (le_c2Norm_STR02969 (u m - u n)).2.1
    have h3 := hN m hm n hn
    rw [(deriv2_sub_STR02969 (hu m) (hu n)).1] at h1 h2
    simp only [Pi.sub_apply] at h1
    linarith
  have hs2 : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      supNorm_STR02968 (deriv (deriv (u m)) - deriv (deriv (u n))) +
        holderSemi_STR02968 (1 / 2) (deriv (deriv (u m)) - deriv (deriv (u n))) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h2 := (le_c2Norm_STR02969 (u m - u n)).2.2
    have h3 := hN m hm n hn
    rw [(deriv2_sub_STR02969 (hu m) (hu n)).2] at h2
    exact lt_of_le_of_lt h2 h3
  obtain ⟨U, hU⟩ := unif_limit_STR02969 u hs0
  obtain ⟨V, hV⟩ := unif_limit_STR02969 (fun n => deriv (u n)) hs1
  obtain ⟨G, hG, hGlim⟩ := complete_aux_STR02968 (fun n => deriv (deriv (u n)))
    (fun n => second_isPerHolder_STR02969 (hu n)) hs2
  -- G is also the uniform limit of the second derivatives
  have hGu : TendstoUniformly (fun n => deriv (deriv (u n))) G atTop := by
    refine Metric.tendstoUniformly_iff.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := hGlim (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop N] with n hn x
    have h2 : |deriv (deriv (u n)) x - G x| ≤ supNorm_STR02968 (deriv (deriv (u n)) - G) := by
      have hb : Bdd (deriv (deriv (u n)) - G) := by
        obtain ⟨M1, hM1⟩ := (bdd_parts_STR02969 (hu n)).2.2
        obtain ⟨M2, hM2⟩ := bdd_of_periodic_STR02968 hG.1 hG.2.1
        exact ⟨M1 + M2, fun y => by
          simp only [Pi.sub_apply]
          exact (abs_sub _ _).trans (add_le_add (hM1 y) (hM2 y))⟩
      exact hb.abs_le_supNorm x
    have h3 := holderSemi_nonneg_STR02968 (1 / 2) (deriv (deriv (u n)) - G)
    have h4 := hN n hn
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  -- differentiability of the limits
  have hUV : ∀ x, HasDerivAt U (V x) x := fun x =>
    hasDerivAt_of_tendstoUniformly hV (Eventually.of_forall fun n y => (hu n).2.1 y |>.hasDerivAt)
      hU.tendsto_at x
  have hVG : ∀ x, HasDerivAt V (G x) x := fun x =>
    hasDerivAt_of_tendstoUniformly hGu
      (Eventually.of_forall fun n y => (hu n).2.2.1 y |>.hasDerivAt) hV.tendsto_at x
  have dU : deriv U = V := funext fun x => (hUV x).deriv
  have dV : deriv V = G := funext fun x => (hVG x).deriv
  have hUper : Periodic U (2 * Real.pi) := fun x => by
    have h2 : Tendsto (fun n => u n (x + 2 * Real.pi)) atTop (𝓝 (U x)) := by
      have : (fun n => u n (x + 2 * Real.pi)) = fun n => u n x :=
        funext fun n => (hu n).1 x
      rw [this]; exact hU.tendsto_at x
    exact tendsto_nhds_unique (hU.tendsto_at (x + 2 * Real.pi)) h2
  have hUmem : IsC2Alpha_STR02901 (1 / 2) U := by
    refine ⟨hUper, fun x => (hUV x).differentiableAt, ?_, ?_, ?_⟩
    · rw [dU]; exact fun x => (hVG x).differentiableAt
    · rw [dU, dV]; exact hG.2.1
    · rw [dU, dV]; exact hG.2.2
  refine ⟨U, hUmem, fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := abs_le_of_tendstoUniformly_STR02969 hU (third_pos_STR02969 hε)
  obtain ⟨N₁, hN₁⟩ := abs_le_of_tendstoUniformly_STR02969 hV (third_pos_STR02969 hε)
  obtain ⟨N₂, hN₂⟩ := hGlim (ε / 3) (third_pos_STR02969 hε)
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn₀ : n ≥ N₀ := (le_max_left _ _).trans hn
  have hn₁ : n ≥ N₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hn₂ : n ≥ N₂ := ((le_max_right _ _).trans (le_max_right _ _)).trans hn
  obtain ⟨e1, e2⟩ := deriv2_sub_STR02969 (hu n) hUmem
  rw [c2Norm_parts_STR02969, e2, e1, dU, dV]
  have a0 : supNorm (u n - U) ≤ ε / 3 := supNorm_le fun x => hN₀ n hn₀ x
  have a1 : supNorm (deriv (u n) - V) ≤ ε / 3 := supNorm_le fun x => hN₁ n hn₁ x
  have a2 : supNorm (deriv (deriv (u n)) - G) +
      circHolder_STR02901 (1 / 2) (deriv (deriv (u n)) - G) ≤ ε / 3 := hN₂ n hn₂
  linarith

instance : CompleteSpace PeriodicC2_STR02969 := by
  refine Metric.complete_of_cauchySeq_tendsto fun f hf => ?_
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      c2Norm_STR02901 (1 / 2) ((f m).val - (f n).val) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hf ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hN m hm n hn
    rwa [dist_eq_norm, PeriodicC2_STR02969.norm_def] at this
  obtain ⟨F, hF, hlim⟩ := c2_complete_aux_STR02969 (fun n => (f n).val) (fun n => (f n).isC2) hC
  refine ⟨PeriodicC2_STR02969.mk F hF, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hlim (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, PeriodicC2_STR02969.norm_def]
  have := hN n hn
  change c2Norm_STR02901 (1 / 2) ((f n).val - F) < ε
  linarith

/-! ### The three constraint functionals and the closed subspaces -/

/-- A real normed space whose elements carry an underlying real function, with the data needed to
build the three bounded functionals `f ↦ ∫ f b dm`, `b ∈ {1, cos, sin}`. -/
structure RangeData_STR02969 (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] where
  /-- The underlying function. -/
  val : X → ℝ → ℝ
  val_add : ∀ f g, val (f + g) = val f + val g
  val_smul : ∀ (c : ℝ) f, val (c • f) = c • val f
  continuous : ∀ f, Continuous (val f)
  bdd : ∀ f, Bdd (val f)
  supNorm_le : ∀ f, supNorm (val f) ≤ ‖f‖

/-- The linear functional `f ↦ ∫ f b dm`. -/
noncomputable def RangeData_STR02969.pairLin {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : RangeData_STR02969 X) (b : ℝ → ℝ) (hb : Continuous b) : X →ₗ[ℝ] ℝ where
  toFun f := pair_STR02953 b (D.val f)
  map_add' f g := by
    show pair_STR02953 b (D.val (f + g)) = pair_STR02953 b (D.val f) + pair_STR02953 b (D.val g)
    rw [D.val_add]
    exact pair_add_STR02953 hb (D.continuous f) (D.continuous g)
  map_smul' c f := by
    show pair_STR02953 b (D.val (c • f)) = c * pair_STR02953 b (D.val f)
    rw [D.val_smul]
    exact pair_smul_STR02953 b c (D.val f)

/-- The bounded functional `f ↦ ∫ f b dm` for a continuous `b` with `|b| ≤ 1` (bound constant `1`). -/
noncomputable def RangeData_STR02969.pairCLM {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : RangeData_STR02969 X) (b : ℝ → ℝ) (hb : Continuous b) (hB : ∀ t, |b t| ≤ 1) :
    X →L[ℝ] ℝ :=
  LinearMap.mkContinuous (D.pairLin b hb) 1 fun f => by
    have h := abs_pair_le_STR02953 hB (D.bdd f)
    have h2 := D.supNorm_le f
    change ‖pair_STR02953 b (D.val f)‖ ≤ 1 * ‖f‖
    rw [Real.norm_eq_abs]
    linarith

/-- The subspace cut out by the three constraints `∫ f dm = ∫ f cos dm = ∫ f sin dm = 0`. -/
noncomputable def RangeData_STR02969.sub {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : RangeData_STR02969 X) : Submodule ℝ X :=
  LinearMap.ker (D.pairCLM (fun _ => 1) continuous_const (fun _ => by simp) : X →ₗ[ℝ] ℝ) ⊓
    (LinearMap.ker (D.pairCLM Real.cos Real.continuous_cos Real.abs_cos_le_one : X →ₗ[ℝ] ℝ) ⊓
      LinearMap.ker (D.pairCLM Real.sin Real.continuous_sin Real.abs_sin_le_one : X →ₗ[ℝ] ℝ))

theorem RangeData_STR02969.mem_sub_iff {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : RangeData_STR02969 X) (f : X) : f ∈ D.sub ↔ InE_STR02901 (D.val f) := by
  have h1 : pair_STR02953 (fun _ => 1) (D.val f) = meanT_STR02901 (D.val f) := by
    unfold pair_STR02953; simp
  unfold RangeData_STR02969.sub InE_STR02901
  simp only [Submodule.mem_inf, LinearMap.mem_ker]
  change (pair_STR02953 (fun _ => 1) (D.val f) = 0 ∧ pair_STR02953 Real.cos (D.val f) = 0 ∧
    pair_STR02953 Real.sin (D.val f) = 0) ↔ _
  rw [h1]
  rfl

theorem RangeData_STR02969.isClosed_sub {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (D : RangeData_STR02969 X) : IsClosed (D.sub : Set X) := by
  unfold RangeData_STR02969.sub
  rw [Submodule.coe_inf, Submodule.coe_inf]
  exact (ContinuousLinearMap.isClosed_ker _).inter
    ((ContinuousLinearMap.isClosed_ker _).inter (ContinuousLinearMap.isClosed_ker _))

theorem RangeData_STR02969.completeSpace_sub {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (D : RangeData_STR02969 X) : CompleteSpace D.sub :=
  D.isClosed_sub.completeSpace_coe

/-- The data for `C^{2,1/2}`. -/
noncomputable def c2Data_STR02969 : RangeData_STR02969 PeriodicC2_STR02969 where
  val f := f.val
  val_add f g := PeriodicC2_STR02969.val_add f g
  val_smul c f := PeriodicC2_STR02969.val_smul c f
  continuous f := f.isC2.2.1.continuous
  bdd f := (bdd_parts_STR02969 f.isC2).1
  supNorm_le f := (le_c2Norm_STR02969 f.val).1

/-- The data for `C^{0,1/2}`. -/
noncomputable def holderData_STR02969 : RangeData_STR02969 PeriodicHolder_STR02968 where
  val f := f.val
  val_add f g := PeriodicHolder_STR02968.val_add f g
  val_smul c f := PeriodicHolder_STR02968.val_smul c f
  continuous f := f.isPerHolder.2.1
  bdd f := bdd_of_periodic_STR02968 f.isPerHolder.1 f.isPerHolder.2.1
  supNorm_le f := by
    rw [PeriodicHolder_STR02968.norm_def]
    show supNorm_STR02968 f.val ≤ supNorm_STR02968 f.val + holderSemi_STR02968 (1 / 2) f.val
    exact le_add_of_nonneg_right (holderSemi_nonneg_STR02968 _ _)

/-- The closed subspace `E ⊂ C^{2,1/2}` of functions orthogonal to `1`, `cos`, `sin`. -/
noncomputable def E_STR02969 : Submodule ℝ PeriodicC2_STR02969 := c2Data_STR02969.sub

/-- The closed subspace `Y ⊂ C^{0,1/2}` of functions orthogonal to `1`, `cos`, `sin`. -/
noncomputable def Y_STR02969 : Submodule ℝ PeriodicHolder_STR02968 := holderData_STR02969.sub

/-! ### Public statements -/

/-- The space `C^{2,1/2}` is complete, with the stated norm. -/
theorem str029_69_completeness_closed_complements_range_spaces_complete :
    CompleteSpace PeriodicC2_STR02969 ∧
      ∀ f : PeriodicC2_STR02969, IsC2Alpha_STR02901 (1 / 2) f.val ∧
        ‖f‖ = supNorm f.val + supNorm (deriv f.val) + supNorm (deriv (deriv f.val)) +
          circHolder_STR02901 (1 / 2) (deriv (deriv f.val)) :=
  ⟨inferInstance, fun f => ⟨f.isC2, by
    rw [PeriodicC2_STR02969.norm_def, c2Norm_parts_STR02969]; ring⟩⟩

/-- `E` is the set of functions satisfying the three constraints, closed and complete. -/
theorem str029_69_completeness_closed_complements_range_spaces_E :
    (∀ f : PeriodicC2_STR02969, f ∈ E_STR02969 ↔ InE_STR02901 f.val) ∧
      IsClosed (E_STR02969 : Set PeriodicC2_STR02969) ∧ CompleteSpace E_STR02969 :=
  ⟨fun f => c2Data_STR02969.mem_sub_iff f, c2Data_STR02969.isClosed_sub,
    c2Data_STR02969.completeSpace_sub⟩

/-- `Y` is the set of functions satisfying the three constraints, closed and complete. -/
theorem str029_69_completeness_closed_complements_range_spaces_Y :
    (∀ g : PeriodicHolder_STR02968, g ∈ Y_STR02969 ↔ InE_STR02901 g.val) ∧
      IsClosed (Y_STR02969 : Set PeriodicHolder_STR02968) ∧ CompleteSpace Y_STR02969 :=
  ⟨fun g => holderData_STR02969.mem_sub_iff g, holderData_STR02969.isClosed_sub,
    holderData_STR02969.completeSpace_sub⟩

/-- STR029.69: completeness of `C^{2,1/2}`, and closedness and completeness of the subspaces `E`
(in `C^{2,1/2}`) and `Y` (in `C^{0,1/2}`) cut out by the three Haar/Fourier constraints. -/
theorem str029_69_completeness_closed_complements_range_spaces :
    (CompleteSpace PeriodicC2_STR02969 ∧
      ∀ f : PeriodicC2_STR02969, IsC2Alpha_STR02901 (1 / 2) f.val ∧
        ‖f‖ = supNorm f.val + supNorm (deriv f.val) + supNorm (deriv (deriv f.val)) +
          circHolder_STR02901 (1 / 2) (deriv (deriv f.val))) ∧
    ((∀ f : PeriodicC2_STR02969, f ∈ E_STR02969 ↔ InE_STR02901 f.val) ∧
      IsClosed (E_STR02969 : Set PeriodicC2_STR02969) ∧ CompleteSpace E_STR02969) ∧
    ((∀ g : PeriodicHolder_STR02968, g ∈ Y_STR02969 ↔ InE_STR02901 g.val) ∧
      IsClosed (Y_STR02969 : Set PeriodicHolder_STR02968) ∧ CompleteSpace Y_STR02969) :=
  ⟨str029_69_completeness_closed_complements_range_spaces_complete,
    str029_69_completeness_closed_complements_range_spaces_E,
    str029_69_completeness_closed_complements_range_spaces_Y⟩

end DGPS.Frontier.STR029
