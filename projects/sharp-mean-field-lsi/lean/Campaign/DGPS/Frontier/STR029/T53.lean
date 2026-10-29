import DGPS.Frontier.STR029.T01

/-!
# STR029.53: Hölder multiplication and bounded linear operations

Task id: STR029.53. Title: Hölder multiplication and bounded linear operations (node STR029, size L).

Statement (specification): on `C^{0,α}` with norm `‖f‖∞ + [f]_α`, multiplication is bounded bilinear with
`‖f g‖ ≤ ‖f‖ ‖g‖`. The maps `u ↦ u, u', u''` from `C^{2,α}` to `C^{0,α}` are bounded. The Haar mean,
the first-harmonic pairings, their complementary projection `P`, and the inclusion of fixed
trigonometric functions are bounded linear maps.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations`: the main theorem, the
  conjunction of all statements below for every `[HolderExponent α]`.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_half`: the same
  conjunction for the fixed exponent `α = 1/2` of the specification.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_mul`: `C^{0,α}` is closed under
  multiplication, `‖f g‖ ≤ ‖f‖ ‖g‖`, and multiplication is additive and homogeneous in each factor.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_embeddings`: the maps
  `u ↦ u`, `u ↦ u'`, `u ↦ u''` from `C^{2,α}` to `C^{0,α}` are bounded linear, with norm bounds
  `π^{1-α}`, `π^{1-α}` and `1` against the `C^{2,α}` norm.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_mean`: the Haar mean
  `f ↦ ∫ f dm` is a bounded linear functional on `C^{0,α}` of norm at most one.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_pairings`: the pairings
  `f ↦ ∫ f cos dm` and `f ↦ ∫ f sin dm` are bounded linear functionals on `C^{0,α}` of norm at most one.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_projection`: the complementary
  projection `P` maps `C^{0,α}` to itself, is linear, and `‖P f‖ ≤ (2 + 2‖cos‖ + 2‖sin‖) ‖f‖`.
* `DGPS.Frontier.STR029.str029_53_holder_multiplication_bounded_linear_operations_inclusion`: the constants `1`,
  `cos`, `sin` lie in `C^{0,α}`, and `c ↦ c • b` is linear with `‖c • b‖ ≤ |c| ‖b‖`.
* `DGPS.Frontier.STR029.IsC0Alpha_STR02953`, `c0Norm_STR02953`: the concrete carrier and its norm.
* `DGPS.Frontier.STR029.projP_STR02953`: the complementary projection `P`.
* `DGPS.Frontier.STR029.pair_STR02953`: the pairing `f ↦ ∫ f b dm`.
* `DGPS.Frontier.STR029.LinearOn_STR02953`, `IsBoundedLinearOn_STR02953`, `IsBoundedFunctionalOn_STR02953`:
  the predicates "linear", "bounded linear map" and "bounded linear functional" on a concrete carrier.

R5 notes:
* Carriers are concrete functions `ℝ → ℝ` in the variable `t = 2πx`, as the specification requires for this
  task (their identification with the packet carriers is the business of `.01`). `C^{0,α}` is
  `IsC0Alpha_STR02953 α f`: `2π`-periodic and circular-Hölder bounded (`CircHolderBdd_STR02901`, which already
  forces continuity and boundedness). Its norm is `c0Norm_STR02953 α f = supNorm f + circHolder_STR02901 α f`,
  the sup norm plus the circular-distance Hölder seminorm, with the campaign's `supNorm` (junk value `0` for
  unbounded functions, never reached on these carriers). `C^{2,α}` is `IsC2Alpha_STR02901 α` with norm
  `c2Norm_STR02901 α`, both reused from `.01`, not redefined.
* Exponent: the specification fixes `α = 1/2`. As in `.01`, the theorems are proved for every
  `[HolderExponent α]` (`0 < α < 1`), which contains `α = 1/2`; the literal case is
  `..._half`. This is a generalization of the exponent only; no hypothesis is added for `α = 1/2`.
* The Haar mean is `meanT_STR02901` (`(2π)⁻¹ ∫_0^{2π} f dt`, interval integral, Mathlib convention
  for non-integrable integrands), and the pairing is `pair_STR02953 b f = meanT_STR02901 (f · b)`.
* "Bounded linear map" between the concrete carriers (which are predicates on `ℝ → ℝ`, not normed
  spaces) is read as: the map sends the domain carrier into the target carrier, is additive and
  homogeneous on the domain, and satisfies `norm (L u) ≤ C * norm u` for some `C ≥ 0`
  (`IsBoundedLinearOn_STR02953`; for real-valued maps `IsBoundedFunctionalOn_STR02953`). The additive and
  homogeneous clauses are required only for members of the domain carrier. Explicit constants are also
  given. Multiplication is "bounded bilinear" in the sense: closed on the carrier, additive and
  homogeneous in each factor (unconditionally), and `‖f g‖ ≤ ‖f‖ ‖g‖`.
* Norm bounds for `u ↦ u` and `u ↦ u'` use the circular-distance estimate `[a]_α ≤ π^{1-α} ‖a'‖∞`
  (circular distance is at most `π`), as in the specification's proof; the constant is `π^{1-α} ≥ 1`
  (not `1`), because the specification states only boundedness. Bounds in terms of `c2Norm_STR02901`.
* The complementary projection is `P f = f - ∫ f dm - 2 (∫ f cos dm) cos - 2 (∫ f sin dm) sin`, acting on
  `C^{0,α}` (the specification's bound `2 + 2‖cos‖ + 2‖sin‖` is a `C^{0,α}` bound); this is the carrier
  where the stated estimate lives. Idempotence is not claimed. The inclusion of "fixed trigonometric
  functions" is read as the maps `ℝ → C^{0,α}`, `c ↦ c • b` for `b ∈ {1, cos, sin}`.
-/

open Function Filter Topology DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-- The concrete Hölder class `C^{0,α}`: `2π`-periodic with a finite circular Hölder constant. -/
def IsC0Alpha_STR02953 (α : ℝ) (f : ℝ → ℝ) : Prop :=
  Function.Periodic f (2 * Real.pi) ∧ CircHolderBdd_STR02901 α f

/-- The norm `‖f‖∞ + [f]_α` of `C^{0,α}` (circular-distance seminorm). -/
noncomputable def c0Norm_STR02953 (α : ℝ) (f : ℝ → ℝ) : ℝ :=
  supNorm f + circHolder_STR02901 α f

/-- The pairing `f ↦ ∫ f b dm`. -/
noncomputable def pair_STR02953 (b f : ℝ → ℝ) : ℝ :=
  meanT_STR02901 (fun t => f t * b t)

/-- The complementary projection `P f = f - ∫ f - 2 (∫ f cos) cos - 2 (∫ f sin) sin`. -/
noncomputable def projP_STR02953 (f : ℝ → ℝ) : ℝ → ℝ := fun t =>
  f t - meanT_STR02901 f - 2 * pair_STR02953 Real.cos f * Real.cos t
    - 2 * pair_STR02953 Real.sin f * Real.sin t

/-- `L` is additive and homogeneous on the members of the carrier `P`. -/
def LinearOn_STR02953 {M : Type*} [Add M] [SMul ℝ M] (P : (ℝ → ℝ) → Prop) (L : (ℝ → ℝ) → M) : Prop :=
  (∀ u v, P u → P v → L (u + v) = L u + L v) ∧ ∀ (c : ℝ) u, P u → L (c • u) = c • L u

/-- A bounded linear map from the carrier `P` (norm `nP`) to the carrier `Q` (norm `nQ`). -/
def IsBoundedLinearOn_STR02953 (P Q : (ℝ → ℝ) → Prop) (nP nQ : (ℝ → ℝ) → ℝ)
    (L : (ℝ → ℝ) → (ℝ → ℝ)) : Prop :=
  (∀ u, P u → Q (L u)) ∧ LinearOn_STR02953 P L ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u, P u → nQ (L u) ≤ C * nP u

/-- A bounded linear functional on the carrier `P` (norm `nP`). -/
def IsBoundedFunctionalOn_STR02953 (P : (ℝ → ℝ) → Prop) (nP : (ℝ → ℝ) → ℝ)
    (φ : (ℝ → ℝ) → ℝ) : Prop :=
  LinearOn_STR02953 P φ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u, P u → |φ u| ≤ C * nP u

/-! ### Circular distance and the Hölder seminorm -/

theorem circDist_le_pi_STR02953 (s t : ℝ) : circDist_STR02901 s t ≤ Real.pi := by
  unfold circDist_STR02901
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  have h := AddCircle.norm_le_half_period (2 * Real.pi) (x := ((s - t : ℝ) : AddCircle (2 * Real.pi)))
    (by positivity)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
  linarith

theorem circHolder_nonneg_STR02953 (α : ℝ) (g : ℝ → ℝ) : 0 ≤ circHolder_STR02901 α g :=
  Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (circDist_nonneg_STR02901 _ _) _)

theorem circHolder_le_STR02953 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ s t, |f s - f t| ≤ K * circDist_STR02901 s t ^ α) : circHolder_STR02901 α f ≤ K := by
  refine ciSup_le fun p => ?_
  by_cases hp : circDist_STR02901 p.1 p.2 = 0
  · rw [hp, Real.zero_rpow hα.ne', div_zero]
    exact hK
  · have : 0 < circDist_STR02901 p.1 p.2 ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (circDist_nonneg_STR02901 _ _) (Ne.symm hp)) _
    rw [div_le_iff₀ this]
    exact h _ _

theorem abs_sub_le_circHolder_STR02953 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ}
    (hf : CircHolderBdd_STR02901 α f) (s t : ℝ) :
    |f s - f t| ≤ circHolder_STR02901 α f * circDist_STR02901 s t ^ α := by
  obtain ⟨C, hC0, hC⟩ := hf
  by_cases h : circDist_STR02901 s t = 0
  · have h1 := hC s t
    rw [h, Real.zero_rpow hα.ne', mul_zero] at h1
    rw [h, Real.zero_rpow hα.ne', mul_zero]
    exact h1
  · have hpos : 0 < circDist_STR02901 s t ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (circDist_nonneg_STR02901 _ _) (Ne.symm h)) _
    have hb : BddAbove (Set.range fun p : ℝ × ℝ =>
        |f p.1 - f p.2| / circDist_STR02901 p.1 p.2 ^ α) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨p, rfl⟩
      by_cases hp : circDist_STR02901 p.1 p.2 = 0
      · simp only [hp, Real.zero_rpow hα.ne', div_zero]
        exact hC0
      · have : 0 < circDist_STR02901 p.1 p.2 ^ α :=
          Real.rpow_pos_of_pos (lt_of_le_of_ne (circDist_nonneg_STR02901 _ _) (Ne.symm hp)) _
        rw [div_le_iff₀ this]
        exact hC _ _
    have h2 := le_ciSup hb (s, t)
    rw [div_le_iff₀ hpos] at h2
    exact h2

theorem bdd_of_circHolderBdd_STR02953 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ}
    (hf : CircHolderBdd_STR02901 α f) : Bdd f := by
  obtain ⟨C, hC0, hC⟩ := hf
  refine ⟨|f 0| + C * Real.pi ^ α, fun x => ?_⟩
  have h1 := hC x 0
  have h2 : circDist_STR02901 x 0 ^ α ≤ Real.pi ^ α :=
    Real.rpow_le_rpow (circDist_nonneg_STR02901 _ _) (circDist_le_pi_STR02953 _ _) hα.le
  have h3 := mul_le_mul_of_nonneg_left h2 hC0
  have h4 := abs_sub_abs_le_abs_sub (f x) (f 0)
  linarith

theorem continuous_of_circHolderBdd_STR02953 {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ}
    (hf : CircHolderBdd_STR02901 α f) : Continuous f := by
  obtain ⟨C, hC0, hC⟩ := hf
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hcont : Continuous fun s : ℝ => C * |s - x| ^ α :=
    continuous_const.mul
      ((continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const
        (fun _ => Or.inr hα.le))
  have hlim : Tendsto (fun s : ℝ => C * |s - x| ^ α) (𝓝 x) (𝓝 0) := by
    have h0 := hcont.tendsto x
    simpa [hα.ne'] using h0
  refine squeeze_zero (fun _ => dist_nonneg) (fun s => ?_) hlim
  rw [Real.dist_eq]
  calc |f s - f x| ≤ C * circDist_STR02901 s x ^ α := hC s x
    _ ≤ C * |s - x| ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (circDist_nonneg_STR02901 _ _) (circDist_le_abs_STR02901 _ _) hα.le) hC0

theorem bdd_of_periodic_continuous_STR02953 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * Real.pi))
    (hc : Continuous f) : Bdd f := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos x
  rw [hxy]
  simpa using hM y (Set.Ico_subset_Icc_self hy)

theorem circ_lipschitz_STR02953 {f : ℝ → ℝ} (hper : Function.Periodic f (2 * Real.pi))
    (hd : Differentiable ℝ f) {M : ℝ} (hM : ∀ x, |deriv f x| ≤ M) (s t : ℝ) :
    |f s - f t| ≤ M * circDist_STR02901 s t := by
  rw [circDist_eq_STR02901]
  set k : ℤ := round ((2 * Real.pi)⁻¹ * (s - t)) with hk
  have h1 : f (s - k * (2 * Real.pi)) = f s := hper.sub_int_mul_eq k
  have h2 := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := Set.univ)
    (fun x _ => hd x) (fun x _ => by simpa using hM x) convex_univ (Set.mem_univ t)
    (Set.mem_univ (s - k * (2 * Real.pi)))
  rw [h1, Real.norm_eq_abs, Real.norm_eq_abs] at h2
  have e : s - ↑k * (2 * Real.pi) - t = s - t - ↑k * (2 * Real.pi) := by ring
  rw [e] at h2
  exact h2

theorem rpow_pi_ge_one_STR02953 {α : ℝ} (hα1 : α ≤ 1) : 1 ≤ Real.pi ^ (1 - α) :=
  Real.one_le_rpow (by linarith [Real.pi_gt_three]) (by linarith)

theorem circDist_le_pow_STR02953 {α : ℝ} (hα1 : α ≤ 1) (s t : ℝ) :
    circDist_STR02901 s t ≤ Real.pi ^ (1 - α) * circDist_STR02901 s t ^ α := by
  have hd0 := circDist_nonneg_STR02901 s t
  rcases hd0.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (Real.rpow_nonneg le_rfl _)
  · have e : circDist_STR02901 s t
        = circDist_STR02901 s t ^ (1 - α) * circDist_STR02901 s t ^ α := by
      rw [← Real.rpow_add h]
      simp
    calc circDist_STR02901 s t
        = circDist_STR02901 s t ^ (1 - α) * circDist_STR02901 s t ^ α := e
      _ ≤ Real.pi ^ (1 - α) * circDist_STR02901 s t ^ α :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hd0 (circDist_le_pi_STR02953 _ _) (by linarith))
          (Real.rpow_nonneg hd0 _)

/-! ### Closure properties of `C^{0,α}` -/

theorem c0_add_STR02953 {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ} (hf : IsC0Alpha_STR02953 α f)
    (hg : IsC0Alpha_STR02953 α g) :
    IsC0Alpha_STR02953 α (f + g) ∧ c0Norm_STR02953 α (f + g) ≤ c0Norm_STR02953 α f + c0Norm_STR02953 α g := by
  have hK : ∀ s t, |(f + g) s - (f + g) t| ≤
      (circHolder_STR02901 α f + circHolder_STR02901 α g) * circDist_STR02901 s t ^ α := by
    intro s t
    have e : (f + g) s - (f + g) t = (f s - f t) + (g s - g t) := by
      simp only [Pi.add_apply]; ring
    rw [e, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (abs_sub_le_circHolder_STR02953 hα hf.2 s t)
      (abs_sub_le_circHolder_STR02953 hα hg.2 s t))
  have hK0 : 0 ≤ circHolder_STR02901 α f + circHolder_STR02901 α g :=
    add_nonneg (circHolder_nonneg_STR02953 _ _) (circHolder_nonneg_STR02953 _ _)
  refine ⟨⟨hf.1.add hg.1, _, hK0, hK⟩, ?_⟩
  have hbf := bdd_of_circHolderBdd_STR02953 hα hf.2
  have hbg := bdd_of_circHolderBdd_STR02953 hα hg.2
  have hs : supNorm (f + g) ≤ supNorm f + supNorm g :=
    supNorm_le fun x => (abs_add_le _ _).trans (add_le_add (hbf.abs_le_supNorm x) (hbg.abs_le_supNorm x))
  have := circHolder_le_STR02953 hα hK0 hK
  unfold c0Norm_STR02953
  linarith

theorem c0_smul_STR02953 {α : ℝ} (hα : 0 < α) (c : ℝ) {f : ℝ → ℝ} (hf : IsC0Alpha_STR02953 α f) :
    IsC0Alpha_STR02953 α (c • f) ∧ c0Norm_STR02953 α (c • f) ≤ |c| * c0Norm_STR02953 α f := by
  have hK : ∀ s t, |(c • f) s - (c • f) t| ≤
      (|c| * circHolder_STR02901 α f) * circDist_STR02901 s t ^ α := by
    intro s t
    have e : (c • f) s - (c • f) t = c * (f s - f t) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_sub_le_circHolder_STR02953 hα hf.2 s t) (abs_nonneg _)
  have hK0 : 0 ≤ |c| * circHolder_STR02901 α f :=
    mul_nonneg (abs_nonneg _) (circHolder_nonneg_STR02953 _ _)
  have hper : Function.Periodic (c • f) (2 * Real.pi) := fun x => by
    show c • f (x + 2 * Real.pi) = c • f x
    rw [hf.1 x]
  refine ⟨⟨hper, _, hK0, hK⟩, ?_⟩
  have hbf := bdd_of_circHolderBdd_STR02953 hα hf.2
  have hs : supNorm (c • f) ≤ |c| * supNorm f := supNorm_le fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hbf.abs_le_supNorm x) (abs_nonneg _)
  have := circHolder_le_STR02953 hα hK0 hK
  unfold c0Norm_STR02953
  linarith

theorem supNorm_le_c0Norm_STR02953 (α : ℝ) (f : ℝ → ℝ) : supNorm f ≤ c0Norm_STR02953 α f := by
  unfold c0Norm_STR02953
  linarith [circHolder_nonneg_STR02953 α f]

theorem c0Norm_nonneg_STR02953 (α : ℝ) (f : ℝ → ℝ) : 0 ≤ c0Norm_STR02953 α f :=
  (supNorm_nonneg f).trans (supNorm_le_c0Norm_STR02953 α f)

theorem c0_const_STR02953 {α : ℝ} (hα : 0 < α) :
    IsC0Alpha_STR02953 α (fun _ => (1 : ℝ)) ∧ c0Norm_STR02953 α (fun _ => (1 : ℝ)) ≤ 1 := by
  refine ⟨⟨fun _ => rfl, 0, le_rfl, fun s t => by simp⟩, ?_⟩
  have h1 : supNorm (fun _ : ℝ => (1 : ℝ)) ≤ 1 := supNorm_le fun _ => by simp
  have h2 : circHolder_STR02901 α (fun _ : ℝ => (1 : ℝ)) ≤ 0 :=
    circHolder_le_STR02953 hα le_rfl fun s t => by simp
  unfold c0Norm_STR02953
  linarith

theorem c0_of_deriv_STR02953 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ}
    (hper : Function.Periodic f (2 * Real.pi)) (hd : Differentiable ℝ f) (hb' : Bdd (deriv f)) :
    IsC0Alpha_STR02953 α f ∧
      c0Norm_STR02953 α f ≤ supNorm f + Real.pi ^ (1 - α) * supNorm (deriv f) := by
  have hL : ∀ s t, |f s - f t| ≤
      (Real.pi ^ (1 - α) * supNorm (deriv f)) * circDist_STR02901 s t ^ α := fun s t =>
    calc |f s - f t| ≤ supNorm (deriv f) * circDist_STR02901 s t :=
          circ_lipschitz_STR02953 hper hd (fun x => hb'.abs_le_supNorm x) s t
      _ ≤ supNorm (deriv f) * (Real.pi ^ (1 - α) * circDist_STR02901 s t ^ α) :=
          mul_le_mul_of_nonneg_left (circDist_le_pow_STR02953 hα1 s t) (supNorm_nonneg _)
      _ = (Real.pi ^ (1 - α) * supNorm (deriv f)) * circDist_STR02901 s t ^ α := by ring
  have hK : 0 ≤ Real.pi ^ (1 - α) * supNorm (deriv f) :=
    mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _) (supNorm_nonneg _)
  refine ⟨⟨hper, _, hK, hL⟩, ?_⟩
  have := circHolder_le_STR02953 hα0 hK hL
  unfold c0Norm_STR02953
  linarith

theorem c0_cos_sin_STR02953 {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (IsC0Alpha_STR02953 α Real.cos ∧ c0Norm_STR02953 α Real.cos ≤ 1 + Real.pi ^ (1 - α)) ∧
    (IsC0Alpha_STR02953 α Real.sin ∧ c0Norm_STR02953 α Real.sin ≤ 1 + Real.pi ^ (1 - α)) := by
  have hc : supNorm Real.cos ≤ 1 := supNorm_le fun x => Real.abs_cos_le_one x
  have hs : supNorm Real.sin ≤ 1 := supNorm_le fun x => Real.abs_sin_le_one x
  have hdc : supNorm (deriv Real.cos) ≤ 1 := supNorm_le fun x => by
    rw [Real.deriv_cos']; simpa using Real.abs_sin_le_one x
  have hds : supNorm (deriv Real.sin) ≤ 1 := supNorm_le fun x => by
    rw [Real.deriv_sin]; exact Real.abs_cos_le_one x
  have hbc : Bdd (deriv Real.cos) := ⟨1, fun x => by
    rw [Real.deriv_cos']; simpa using Real.abs_sin_le_one x⟩
  have hbs : Bdd (deriv Real.sin) := ⟨1, fun x => by
    rw [Real.deriv_sin]; exact Real.abs_cos_le_one x⟩
  have hp := Real.pi_pos
  obtain ⟨h1, h2⟩ := c0_of_deriv_STR02953 hα0 hα1 Real.cos_periodic Real.differentiable_cos hbc
  obtain ⟨h3, h4⟩ := c0_of_deriv_STR02953 hα0 hα1 Real.sin_periodic Real.differentiable_sin hbs
  have hpa : 0 ≤ Real.pi ^ (1 - α) := Real.rpow_nonneg hp.le _
  exact ⟨⟨h1, by nlinarith [mul_le_mul_of_nonneg_left hdc hpa]⟩,
    ⟨h3, by nlinarith [mul_le_mul_of_nonneg_left hds hpa]⟩⟩

/-! ### Multiplication -/

theorem c0_mul_STR02953 {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ} (hf : IsC0Alpha_STR02953 α f)
    (hg : IsC0Alpha_STR02953 α g) :
    IsC0Alpha_STR02953 α (f * g) ∧ c0Norm_STR02953 α (f * g) ≤ c0Norm_STR02953 α f * c0Norm_STR02953 α g := by
  have hbf := bdd_of_circHolderBdd_STR02953 hα hf.2
  have hbg := bdd_of_circHolderBdd_STR02953 hα hg.2
  have key : ∀ s t, |(f * g) s - (f * g) t| ≤
      (supNorm f * circHolder_STR02901 α g + supNorm g * circHolder_STR02901 α f) *
        circDist_STR02901 s t ^ α := by
    intro s t
    have e : (f * g) s - (f * g) t = f s * (g s - g t) + g t * (f s - f t) := by
      simp only [Pi.mul_apply]; ring
    rw [e, add_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, mul_assoc]
      exact mul_le_mul (hbf.abs_le_supNorm s) (abs_sub_le_circHolder_STR02953 hα hg.2 s t)
        (abs_nonneg _) (supNorm_nonneg _)
    · rw [abs_mul, mul_assoc]
      exact mul_le_mul (hbg.abs_le_supNorm t) (abs_sub_le_circHolder_STR02953 hα hf.2 s t)
        (abs_nonneg _) (supNorm_nonneg _)
  have hK0 : 0 ≤ supNorm f * circHolder_STR02901 α g + supNorm g * circHolder_STR02901 α f :=
    add_nonneg (mul_nonneg (supNorm_nonneg _) (circHolder_nonneg_STR02953 _ _))
      (mul_nonneg (supNorm_nonneg _) (circHolder_nonneg_STR02953 _ _))
  refine ⟨⟨hf.1.mul hg.1, _, hK0, key⟩, ?_⟩
  have hs : supNorm (f * g) ≤ supNorm f * supNorm g := supNorm_le fun x => by
    rw [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hbf.abs_le_supNorm x) (hbg.abs_le_supNorm x) (abs_nonneg _) (supNorm_nonneg _)
  have h1 := circHolder_le_STR02953 hα hK0 key
  have h2 := mul_nonneg (circHolder_nonneg_STR02953 α f) (circHolder_nonneg_STR02953 α g)
  unfold c0Norm_STR02953
  nlinarith

/-! ### Mean and pairings -/

theorem meanT_add_STR02953 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    meanT_STR02901 (f + g) = meanT_STR02901 f + meanT_STR02901 g := by
  unfold meanT_STR02901
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

theorem meanT_smul_STR02953 (c : ℝ) (f : ℝ → ℝ) :
    meanT_STR02901 (c • f) = c * meanT_STR02901 f := by
  unfold meanT_STR02901
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem abs_meanT_le_STR02953 {f : ℝ → ℝ} {M : ℝ} (h : ∀ t, |f t| ≤ M) :
    |meanT_STR02901 f| ≤ M := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (f := f) (C := M) (fun x _ => by simpa using h x)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hp] at h1
  unfold meanT_STR02901
  rw [abs_mul, abs_inv, abs_of_pos hp]
  calc (2 * Real.pi)⁻¹ * |∫ t in (0 : ℝ)..(2 * Real.pi), f t|
      ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hp.le)
    _ = M := by field_simp

theorem pair_add_STR02953 {b f g : ℝ → ℝ} (hb : Continuous b) (hf : Continuous f) (hg : Continuous g) :
    pair_STR02953 b (f + g) = pair_STR02953 b f + pair_STR02953 b g := by
  unfold pair_STR02953
  have e : (fun t => (f + g) t * b t) = (fun t => f t * b t) + (fun t => g t * b t) := by
    funext t; simp only [Pi.add_apply]; ring
  rw [e]
  exact meanT_add_STR02953 (hf.mul hb) (hg.mul hb)

theorem pair_smul_STR02953 (b : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) :
    pair_STR02953 b (c • f) = c * pair_STR02953 b f := by
  unfold pair_STR02953
  have e : (fun t => (c • f) t * b t) = c • (fun t => f t * b t) := by
    funext t; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [e]
  exact meanT_smul_STR02953 _ _

theorem abs_pair_le_STR02953 {b f : ℝ → ℝ} {B : ℝ} (hB : ∀ t, |b t| ≤ B) (hf : Bdd f) :
    |pair_STR02953 b f| ≤ supNorm f * B := by
  refine abs_meanT_le_STR02953 fun t => ?_
  rw [abs_mul]
  exact mul_le_mul (hf.abs_le_supNorm t) (hB t) (abs_nonneg _) (supNorm_nonneg _)

/-! ### Public statements -/

theorem str029_53_holder_multiplication_bounded_linear_operations_mul
    {α : ℝ} [HolderExponent α] :
    (∀ f g, IsC0Alpha_STR02953 α f → IsC0Alpha_STR02953 α g →
      IsC0Alpha_STR02953 α (f * g) ∧ c0Norm_STR02953 α (f * g) ≤ c0Norm_STR02953 α f * c0Norm_STR02953 α g) ∧
    (∀ (f₁ f₂ g : ℝ → ℝ) (c : ℝ),
      (f₁ + f₂) * g = f₁ * g + f₂ * g ∧ (c • f₁) * g = c • (f₁ * g) ∧
      g * (f₁ + f₂) = g * f₁ + g * f₂ ∧ g * (c • f₁) = c • (g * f₁)) :=
  ⟨fun _ _ hf hg => c0_mul_STR02953 (HolderExponent.pos (α := α)) hf hg,
    fun _ _ _ _ => ⟨add_mul _ _ _, smul_mul_assoc _ _ _, mul_add _ _ _, mul_smul_comm _ _ _⟩⟩

theorem str029_53_holder_multiplication_bounded_linear_operations_embeddings
    {α : ℝ} [HolderExponent α] :
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
      (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => u) ∧
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
      (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => deriv u) ∧
    IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
      (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => deriv (deriv u)) := by
  have hα0 : 0 < α := HolderExponent.pos (α := α)
  have hα1 : α ≤ 1 := (HolderExponent.lt_one (α := α)).le
  have hp1 := rpow_pi_ge_one_STR02953 hα1
  have hpa : 0 ≤ Real.pi ^ (1 - α) := by linarith
  -- facts about a `C^{2,α}` function
  have hfacts : ∀ u, IsC2Alpha_STR02901 α u →
      Function.Periodic (deriv u) (2 * Real.pi) ∧
      Function.Periodic (deriv (deriv u)) (2 * Real.pi) ∧
      Bdd u ∧ Bdd (deriv u) ∧ Bdd (deriv (deriv u)) := by
    intro u hu
    obtain ⟨hper, hd, hd1, hc2, _⟩ := hu
    have h1 := periodic_deriv_STR02901 hper
    have h2 := periodic_deriv_STR02901 h1
    exact ⟨h1, h2, bdd_of_periodic_continuous_STR02953 hper hd.continuous,
      bdd_of_periodic_continuous_STR02953 h1 hd1.continuous,
      bdd_of_periodic_continuous_STR02953 h2 hc2⟩
  have hnn : ∀ u, 0 ≤ supNorm u ∧ 0 ≤ supNorm (deriv u) ∧ 0 ≤ supNorm (deriv (deriv u)) ∧
      0 ≤ circHolder_STR02901 α (deriv (deriv u)) := fun u =>
    ⟨supNorm_nonneg _, supNorm_nonneg _, supNorm_nonneg _, circHolder_nonneg_STR02953 _ _⟩
  refine ⟨⟨fun u hu => (c0_of_deriv_STR02953 hα0 hα1 hu.1 hu.2.1 (hfacts u hu).2.2.2.1).1,
      ⟨fun u v _ _ => rfl, fun c u _ => rfl⟩, Real.pi ^ (1 - α), hpa, fun u hu => ?_⟩,
    ⟨fun u hu => (c0_of_deriv_STR02953 hα0 hα1 (hfacts u hu).1 hu.2.2.1
        (hfacts u hu).2.2.2.2).1,
      ⟨fun u v hu hv => ?_, fun c u hu => ?_⟩, Real.pi ^ (1 - α), hpa, fun u hu => ?_⟩,
    ⟨fun u hu => ⟨(hfacts u hu).2.1, hu.2.2.2.2⟩,
      ⟨fun u v hu hv => ?_, fun c u hu => ?_⟩, 1, zero_le_one, fun u hu => ?_⟩⟩
  · have h := (c0_of_deriv_STR02953 hα0 hα1 hu.1 hu.2.1 (hfacts u hu).2.2.2.1).2
    obtain ⟨a, b, c, d⟩ := hnn u
    unfold c2Norm_STR02901
    nlinarith [mul_nonneg (sub_nonneg.2 hp1) a, mul_nonneg hpa b, mul_nonneg hpa c,
      mul_nonneg hpa d]
  · have e : deriv (u + v) = deriv u + deriv v := by
      funext x; exact deriv_add (hu.2.1.differentiableAt) (hv.2.1.differentiableAt)
    show deriv (u + v) = deriv u + deriv v
    exact e
  · show deriv (c • u) = c • deriv u
    funext x
    exact deriv_const_smul c (hu.2.1.differentiableAt)
  · have h := (c0_of_deriv_STR02953 hα0 hα1 (hfacts u hu).1 hu.2.2.1
      (hfacts u hu).2.2.2.2).2
    obtain ⟨a, b, c, d⟩ := hnn u
    unfold c2Norm_STR02901
    nlinarith [mul_nonneg (sub_nonneg.2 hp1) b, mul_nonneg hpa a, mul_nonneg hpa c,
      mul_nonneg hpa d, mul_nonneg (sub_nonneg.2 hp1) c, mul_nonneg (sub_nonneg.2 hp1) d]
  · have e1 : deriv (u + v) = deriv u + deriv v := by
      funext x; exact deriv_add (hu.2.1.differentiableAt) (hv.2.1.differentiableAt)
    have e2 : deriv (deriv u + deriv v) = deriv (deriv u) + deriv (deriv v) := by
      funext x; exact deriv_add (hu.2.2.1.differentiableAt) (hv.2.2.1.differentiableAt)
    show deriv (deriv (u + v)) = deriv (deriv u) + deriv (deriv v)
    rw [e1, e2]
  · have e1 : deriv (c • u) = c • deriv u := by
      funext x; exact deriv_const_smul c (hu.2.1.differentiableAt)
    have e2 : deriv (c • deriv u) = c • deriv (deriv u) := by
      funext x; exact deriv_const_smul c (hu.2.2.1.differentiableAt)
    show deriv (deriv (c • u)) = c • deriv (deriv u)
    rw [e1, e2]
  · obtain ⟨a, b, c, d⟩ := hnn u
    show supNorm (deriv (deriv u)) + circHolder_STR02901 α (deriv (deriv u)) ≤ 1 * c2Norm_STR02901 α u
    unfold c2Norm_STR02901
    linarith

theorem str029_53_holder_multiplication_bounded_linear_operations_mean
    {α : ℝ} [HolderExponent α] :
    IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α) meanT_STR02901 := by
  have hα0 : 0 < α := HolderExponent.pos (α := α)
  have hc : ∀ f, IsC0Alpha_STR02953 α f → Continuous f := fun f hf =>
    continuous_of_circHolderBdd_STR02953 hα0 hf.2
  refine ⟨⟨fun u v hu hv => meanT_add_STR02953 (hc u hu) (hc v hv),
    fun c u _ => meanT_smul_STR02953 c u⟩, 1, zero_le_one, fun u hu => ?_⟩
  have hb := bdd_of_circHolderBdd_STR02953 hα0 hu.2
  rw [one_mul]
  exact (abs_meanT_le_STR02953 fun t => hb.abs_le_supNorm t).trans
    (supNorm_le_c0Norm_STR02953 α u)

theorem str029_53_holder_multiplication_bounded_linear_operations_pairings
    {α : ℝ} [HolderExponent α] :
    IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α)
      (pair_STR02953 Real.cos) ∧
    IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α)
      (pair_STR02953 Real.sin) := by
  have hα0 : 0 < α := HolderExponent.pos (α := α)
  have hc : ∀ f, IsC0Alpha_STR02953 α f → Continuous f := fun f hf =>
    continuous_of_circHolderBdd_STR02953 hα0 hf.2
  refine ⟨⟨⟨fun u v hu hv => pair_add_STR02953 Real.continuous_cos (hc u hu) (hc v hv),
      fun c u _ => pair_smul_STR02953 _ c u⟩, 1, zero_le_one, fun u hu => ?_⟩,
    ⟨⟨fun u v hu hv => pair_add_STR02953 Real.continuous_sin (hc u hu) (hc v hv),
      fun c u _ => pair_smul_STR02953 _ c u⟩, 1, zero_le_one, fun u hu => ?_⟩⟩
  · have := abs_pair_le_STR02953 (b := Real.cos) (B := 1) Real.abs_cos_le_one
      (bdd_of_circHolderBdd_STR02953 hα0 hu.2)
    rw [one_mul]
    linarith [supNorm_le_c0Norm_STR02953 α u]
  · have := abs_pair_le_STR02953 (b := Real.sin) (B := 1) Real.abs_sin_le_one
      (bdd_of_circHolderBdd_STR02953 hα0 hu.2)
    rw [one_mul]
    linarith [supNorm_le_c0Norm_STR02953 α u]

theorem str029_53_holder_multiplication_bounded_linear_operations_inclusion
    {α : ℝ} [HolderExponent α] :
    ∀ b : ℝ → ℝ, (b = (fun _ => (1 : ℝ)) ∨ b = Real.cos ∨ b = Real.sin) →
      IsC0Alpha_STR02953 α b ∧
      (∀ c : ℝ, IsC0Alpha_STR02953 α (c • b) ∧ c0Norm_STR02953 α (c • b) ≤ |c| * c0Norm_STR02953 α b) ∧
      (∀ c d : ℝ, (c + d) • b = c • b + d • b) ∧ (∀ c d : ℝ, (c * d) • b = c • (d • b)) := by
  have hα0 : 0 < α := HolderExponent.pos (α := α)
  have hα1 : α ≤ 1 := (HolderExponent.lt_one (α := α)).le
  intro b hb
  have hmem : IsC0Alpha_STR02953 α b := by
    rcases hb with rfl | rfl | rfl
    · exact (c0_const_STR02953 hα0).1
    · exact (c0_cos_sin_STR02953 hα0 hα1).1.1
    · exact (c0_cos_sin_STR02953 hα0 hα1).2.1
  exact ⟨hmem, fun c => c0_smul_STR02953 hα0 c hmem, fun c d => add_smul c d b,
    fun c d => mul_smul c d b⟩

theorem str029_53_holder_multiplication_bounded_linear_operations_projection
    {α : ℝ} [HolderExponent α] :
    IsBoundedLinearOn_STR02953 (IsC0Alpha_STR02953 α) (IsC0Alpha_STR02953 α)
      (c0Norm_STR02953 α) (c0Norm_STR02953 α) projP_STR02953 ∧
    (∀ f, IsC0Alpha_STR02953 α f →
      c0Norm_STR02953 α (projP_STR02953 f) ≤
        (2 + 2 * c0Norm_STR02953 α Real.cos + 2 * c0Norm_STR02953 α Real.sin) * c0Norm_STR02953 α f) := by
  have hα0 : 0 < α := HolderExponent.pos (α := α)
  have hα1 : α ≤ 1 := (HolderExponent.lt_one (α := α)).le
  obtain ⟨⟨hcos, _⟩, ⟨hsin, _⟩⟩ := c0_cos_sin_STR02953 hα0 hα1
  obtain ⟨hone, hone'⟩ := c0_const_STR02953 (α := α) hα0
  have hc : ∀ f, IsC0Alpha_STR02953 α f → Continuous f := fun f hf =>
    continuous_of_circHolderBdd_STR02953 hα0 hf.2
  -- decomposition of `P f`
  have hdec : ∀ f : ℝ → ℝ, projP_STR02953 f = f + (-meanT_STR02901 f) • (fun _ => (1 : ℝ)) +
      (-2 * pair_STR02953 Real.cos f) • Real.cos + (-2 * pair_STR02953 Real.sin f) • Real.sin := by
    intro f; funext t
    simp only [projP_STR02953, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- membership and the norm bound
  have hbound : ∀ f, IsC0Alpha_STR02953 α f → IsC0Alpha_STR02953 α (projP_STR02953 f) ∧
      c0Norm_STR02953 α (projP_STR02953 f) ≤
        (2 + 2 * c0Norm_STR02953 α Real.cos + 2 * c0Norm_STR02953 α Real.sin) * c0Norm_STR02953 α f := by
    intro f hf
    have hbf := bdd_of_circHolderBdd_STR02953 hα0 hf.2
    have hm : |meanT_STR02901 f| ≤ c0Norm_STR02953 α f :=
      (abs_meanT_le_STR02953 fun t => hbf.abs_le_supNorm t).trans (supNorm_le_c0Norm_STR02953 α f)
    have hpc : |pair_STR02953 Real.cos f| ≤ c0Norm_STR02953 α f := by
      have := abs_pair_le_STR02953 (b := Real.cos) (B := 1) Real.abs_cos_le_one hbf
      linarith [supNorm_le_c0Norm_STR02953 α f]
    have hps : |pair_STR02953 Real.sin f| ≤ c0Norm_STR02953 α f := by
      have := abs_pair_le_STR02953 (b := Real.sin) (B := 1) Real.abs_sin_le_one hbf
      linarith [supNorm_le_c0Norm_STR02953 α f]
    obtain ⟨m1, m2⟩ := c0_smul_STR02953 hα0 (-meanT_STR02901 f) hone
    obtain ⟨c1, c2⟩ := c0_smul_STR02953 hα0 (-2 * pair_STR02953 Real.cos f) hcos
    obtain ⟨s1, s2⟩ := c0_smul_STR02953 hα0 (-2 * pair_STR02953 Real.sin f) hsin
    obtain ⟨a1, a2⟩ := c0_add_STR02953 hα0 hf m1
    obtain ⟨b1, b2⟩ := c0_add_STR02953 hα0 a1 c1
    obtain ⟨d1, d2⟩ := c0_add_STR02953 hα0 b1 s1
    rw [hdec f]
    refine ⟨d1, ?_⟩
    have n0 := c0Norm_nonneg_STR02953 α f
    have n1 := c0Norm_nonneg_STR02953 α Real.cos
    have n2 := c0Norm_nonneg_STR02953 α Real.sin
    have e1 : |-meanT_STR02901 f| = |meanT_STR02901 f| := abs_neg _
    have e2 : |-2 * pair_STR02953 Real.cos f| = 2 * |pair_STR02953 Real.cos f| := by
      rw [abs_mul]; norm_num
    have e3 : |-2 * pair_STR02953 Real.sin f| = 2 * |pair_STR02953 Real.sin f| := by
      rw [abs_mul]; norm_num
    rw [e1] at m2
    rw [e2] at c2
    rw [e3] at s2
    have t1 : |meanT_STR02901 f| * c0Norm_STR02953 α (fun _ => (1 : ℝ)) ≤ c0Norm_STR02953 α f := by
      calc _ ≤ |meanT_STR02901 f| * 1 :=
            mul_le_mul_of_nonneg_left hone' (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hm
    have t2 : 2 * |pair_STR02953 Real.cos f| * c0Norm_STR02953 α Real.cos ≤
        2 * c0Norm_STR02953 α Real.cos * c0Norm_STR02953 α f := by
      nlinarith [mul_le_mul_of_nonneg_left hpc n1]
    have t3 : 2 * |pair_STR02953 Real.sin f| * c0Norm_STR02953 α Real.sin ≤
        2 * c0Norm_STR02953 α Real.sin * c0Norm_STR02953 α f := by
      nlinarith [mul_le_mul_of_nonneg_left hps n2]
    have u1 : |meanT_STR02901 f| * c0Norm_STR02953 α (fun _ => (1 : ℝ)) ≥ 0 :=
      mul_nonneg (abs_nonneg _) (c0Norm_nonneg_STR02953 α _)
    nlinarith
  refine ⟨⟨fun f hf => (hbound f hf).1, ⟨fun u v hu hv => ?_, fun c u hu => ?_⟩,
    2 + 2 * c0Norm_STR02953 α Real.cos + 2 * c0Norm_STR02953 α Real.sin,
    by linarith [c0Norm_nonneg_STR02953 α Real.cos, c0Norm_nonneg_STR02953 α Real.sin],
    fun f hf => (hbound f hf).2⟩, fun f hf => (hbound f hf).2⟩
  · have hu' := hc u hu
    have hv' := hc v hv
    funext t
    simp only [projP_STR02953, Pi.add_apply,
      meanT_add_STR02953 hu' hv', pair_add_STR02953 Real.continuous_cos hu' hv',
      pair_add_STR02953 Real.continuous_sin hu' hv']
    ring
  · funext t
    simp only [projP_STR02953, Pi.smul_apply, smul_eq_mul,
      meanT_smul_STR02953, pair_smul_STR02953]
    ring

/-- The main theorem for every Hölder exponent `0 < α < 1`: multiplication on `C^{0,α}` is bounded
bilinear with `‖f g‖ ≤ ‖f‖ ‖g‖`; `u ↦ u, u', u''` are bounded linear maps `C^{2,α} → C^{0,α}`; the Haar
mean, the first-harmonic pairings, the projection `P` and the inclusions of `1, cos, sin` are bounded
linear maps on the concrete carriers. -/
theorem str029_53_holder_multiplication_bounded_linear_operations
    {α : ℝ} [HolderExponent α] :
    ((∀ f g, IsC0Alpha_STR02953 α f → IsC0Alpha_STR02953 α g →
      IsC0Alpha_STR02953 α (f * g) ∧ c0Norm_STR02953 α (f * g) ≤ c0Norm_STR02953 α f * c0Norm_STR02953 α g) ∧
    (∀ (f₁ f₂ g : ℝ → ℝ) (c : ℝ),
      (f₁ + f₂) * g = f₁ * g + f₂ * g ∧ (c • f₁) * g = c • (f₁ * g) ∧
      g * (f₁ + f₂) = g * f₁ + g * f₂ ∧ g * (c • f₁) = c • (g * f₁))) ∧
    (IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
        (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => u) ∧
      IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
        (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => deriv u) ∧
      IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 α) (IsC0Alpha_STR02953 α)
        (c2Norm_STR02901 α) (c0Norm_STR02953 α) (fun u => deriv (deriv u))) ∧
    IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α) meanT_STR02901 ∧
    (IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α)
        (pair_STR02953 Real.cos) ∧
      IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 α) (c0Norm_STR02953 α)
        (pair_STR02953 Real.sin)) ∧
    (IsBoundedLinearOn_STR02953 (IsC0Alpha_STR02953 α) (IsC0Alpha_STR02953 α)
        (c0Norm_STR02953 α) (c0Norm_STR02953 α) projP_STR02953 ∧
      (∀ f, IsC0Alpha_STR02953 α f →
        c0Norm_STR02953 α (projP_STR02953 f) ≤
          (2 + 2 * c0Norm_STR02953 α Real.cos + 2 * c0Norm_STR02953 α Real.sin) *
            c0Norm_STR02953 α f)) ∧
    (∀ b : ℝ → ℝ, (b = (fun _ => (1 : ℝ)) ∨ b = Real.cos ∨ b = Real.sin) →
      IsC0Alpha_STR02953 α b ∧
      (∀ c : ℝ, IsC0Alpha_STR02953 α (c • b) ∧ c0Norm_STR02953 α (c • b) ≤ |c| * c0Norm_STR02953 α b) ∧
      (∀ c d : ℝ, (c + d) • b = c • b + d • b) ∧ (∀ c d : ℝ, (c * d) • b = c • (d • b))) :=
  ⟨str029_53_holder_multiplication_bounded_linear_operations_mul,
    str029_53_holder_multiplication_bounded_linear_operations_embeddings,
    str029_53_holder_multiplication_bounded_linear_operations_mean,
    str029_53_holder_multiplication_bounded_linear_operations_pairings,
    str029_53_holder_multiplication_bounded_linear_operations_projection,
    str029_53_holder_multiplication_bounded_linear_operations_inclusion⟩

/-- The same conjunction for the fixed exponent `α = 1/2` of the specification. -/
theorem str029_53_holder_multiplication_bounded_linear_operations_half :
    have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
    ((∀ f g, IsC0Alpha_STR02953 (1 / 2 : ℝ) f → IsC0Alpha_STR02953 (1 / 2 : ℝ) g →
      IsC0Alpha_STR02953 (1 / 2 : ℝ) (f * g) ∧
        c0Norm_STR02953 (1 / 2 : ℝ) (f * g) ≤ c0Norm_STR02953 (1 / 2 : ℝ) f * c0Norm_STR02953 (1 / 2 : ℝ) g) ∧
    (IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2 : ℝ)) (IsC0Alpha_STR02953 (1 / 2 : ℝ))
        (c2Norm_STR02901 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ)) (fun u => u) ∧
      IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2 : ℝ)) (IsC0Alpha_STR02953 (1 / 2 : ℝ))
        (c2Norm_STR02901 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ)) (fun u => deriv u) ∧
      IsBoundedLinearOn_STR02953 (IsC2Alpha_STR02901 (1 / 2 : ℝ)) (IsC0Alpha_STR02953 (1 / 2 : ℝ))
        (c2Norm_STR02901 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ)) (fun u => deriv (deriv u))) ∧
    IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ))
      meanT_STR02901 ∧
    (IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ))
        (pair_STR02953 Real.cos) ∧
      IsBoundedFunctionalOn_STR02953 (IsC0Alpha_STR02953 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ))
        (pair_STR02953 Real.sin)) ∧
    IsBoundedLinearOn_STR02953 (IsC0Alpha_STR02953 (1 / 2 : ℝ)) (IsC0Alpha_STR02953 (1 / 2 : ℝ))
      (c0Norm_STR02953 (1 / 2 : ℝ)) (c0Norm_STR02953 (1 / 2 : ℝ)) projP_STR02953) := by
  have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  exact ⟨(str029_53_holder_multiplication_bounded_linear_operations_mul (α := (1 / 2 : ℝ))).1,
    str029_53_holder_multiplication_bounded_linear_operations_embeddings,
    str029_53_holder_multiplication_bounded_linear_operations_mean,
    str029_53_holder_multiplication_bounded_linear_operations_pairings,
    (str029_53_holder_multiplication_bounded_linear_operations_projection (α := (1 / 2 : ℝ))).1⟩

end DGPS.Frontier.STR029
