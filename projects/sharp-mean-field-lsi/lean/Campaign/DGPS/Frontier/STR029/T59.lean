import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# STR029.59: Smooth division by a coordinate power

Task id: STR029.59. Title: Smooth division by a coordinate power (node STR029, size L).

Statement (specification): let the real-valued function `G(h, z)` be smooth on an open subset of
`ℝ × ℝ^m` containing `{0} × U`, and suppose `∂_h^j G(0, z) = 0` for `0 ≤ j ≤ 3`. Locally,
`V(h, z) = (1/3!) ∫_0^1 (1 - t)^3 ∂_h^4 G(t h, z) dt` is smooth, equals `G(h, z) / h^4` for `h ≠ 0`,
and has value `∂_h^4 G(0, z) / 4!` at zero.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_59_smooth_division_coordinate_power`: around each point `(0, z₀)`, `z₀ ∈ U`,
  there is an open neighbourhood `W ⊆ Ω`, stable under `(h, z) ↦ (t h, z)` for `t ∈ [0, 1]`, on which `V` is
  smooth, with `V h z = G (h, z) / h ^ 4` for `h ≠ 0` (`z ∈ U`) and `V 0 z = ∂_h^4 G (0, z) / 4!` (`z ∈ U`).
* `DGPS.Frontier.STR029.quotientRemainder_STR02959`: the function `V`.
* `DGPS.Frontier.STR029.contDiff_param_integral_STR02959`: smoothness of a parameter integral over
  `[0, 1]` of a jointly `C^n` integrand (the library fact used for differentiation under the integral).
* `DGPS.Frontier.STR029.taylor_STR02959`: the integral Taylor identity in one variable with vanishing
  jet of order at most three.
* Helpers: `dh_STR02959` (the partial derivative `∂_h`), `contDiffOn_dh_STR02959`,
  `contDiffOn_dh_iterate_STR02959`, `iteratedDeriv_slice_STR02959`, `iteratedFDeriv_const_STR02959`,
  `star_STR02959`, `smooth_cutoff_STR02959`.

R5 notes:
* Carriers: `ℝ^m` is `Fin m → ℝ` and the base space is `ℝ × (Fin m → ℝ)` with the product (supremum)
  norm, variable order `(h, z)`. "Smooth" is `ContDiffOn ℝ ∞ G Ω` (`C^∞`, not analytic) on the open set `Ω`.
  `∂_h^j G(h, z)` is read as `iteratedDeriv j (fun s => G (s, z)) h`, so the vanishing hypothesis is
  `iteratedDeriv j (fun h => G (h, z)) 0 = 0` for `j ≤ 3` and `z ∈ U`. The Taylor remainder in `V` is
  the interval integral over `[0, 1]` with the literal prefactor `1 / (3! : ℝ)`.
* `U` is not further specified in the specification, so it is an arbitrary subset of `ℝ^m` with
  `(0, z) ∈ Ω` for `z ∈ U` (the hypothesis `hU`); no openness is assumed. Consequently the quotient
  identity and the value at zero are asserted for those points of the neighbourhood with `z ∈ U`
  (the vanishing jet is only known there), while smoothness of `V` holds on the whole neighbourhood
  `W ⊆ Ω`. For open `U` one may intersect `W` with `ℝ × U`.
* "Locally" is read as: for every `z₀ ∈ U` there is an open `W` containing `(0, z₀)`. The set `W` is a
  ball for the product norm, hence closed under shrinking the first coordinate, which makes the
  integrand of `V` evaluate only inside `W ⊆ Ω`. This closure property is part of the conclusion.
* Proof route differs from the written sketch only in the technical device: smoothness of `V` is
  obtained by multiplying the integrand's fourth partial derivative with a smooth bump equal to `1` on
  a smaller ball and supported in `W`, so the parameter-integral lemma
  (`contDiff_param_integral_STR02959`, proved here by induction on the order via
  differentiation under the integral sign) applies on the whole space. On the smaller ball the bump
  is `1`, so the resulting function agrees with `V`; the neighbourhood returned is that smaller ball.
* No normalisation, density, chart or range-map input of the node STR029 is used or assumed; the unit
  is purely a statement about smooth functions of `(h, z)`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace DGPS.Frontier.STR029


theorem contDiff_param_integral_STR02959 {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] :
    ∀ (n : ℕ) {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (Φ : ℝ × X → Y), ContDiff ℝ n Φ →
      ContDiff ℝ n (fun x : X => ∫ t in (0:ℝ)..1, Φ (t, x)) := by
  intro n
  induction n with
  | zero =>
    intro Y _ _ _ Φ hΦ
    have hc : Continuous Φ := by simpa using hΦ
    simp only [Nat.cast_zero, contDiff_zero]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun x t => Φ (t, x)) (by fun_prop) 0 1
  | succ n ih =>
    intro Y _ _ _ Φ hΦ
    have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hdiff : Differentiable ℝ Φ := hΦ1.differentiable (by norm_num)
    have hder : ContDiff ℝ n (fderiv ℝ Φ) := by
      have := (contDiff_succ_iff_fderiv (n := (n : WithTop ℕ∞)) (f := Φ)).1 (by exact_mod_cast hΦ)
      exact this.2.2
    set Ψ : ℝ × X → (X →L[ℝ] Y) := fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ ℝ X) with hΨ
    have hΨc : ContDiff ℝ n Ψ := by
      exact hder.clm_comp contDiff_const
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ t in (0:ℝ)..1, Ψ (t, x), ih (Y := X →L[ℝ] Y) Ψ hΨc, ?_⟩
    intro x₀
    have hΨcont : Continuous Ψ := hΨc.continuous
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).prod
      (isCompact_closedBall x₀ 1) |>.exists_bound_of_continuousOn hΨcont.continuousOn
    have hΦc : Continuous Φ := hΦ1.continuous
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x t => Φ (t, x)) (F' := fun x t => Ψ (t, x)) (bound := fun _ => C)
      (s := Metric.closedBall x₀ 1) (Metric.closedBall_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x => (by fun_prop : Continuous fun t : ℝ => Φ (t, x)).aestronglyMeasurable
    · exact (by fun_prop : Continuous fun t : ℝ => Φ (t, x₀)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun t : ℝ => Ψ (t, x₀)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, hx⟩
      rw [uIoc_of_le zero_le_one] at ht
      exact ⟨ht.1.le, ht.2⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t _ x _ => ?_
      exact (hdiff (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)



noncomputable def dh_STR02959 {m : ℕ} (G : ℝ × (Fin m → ℝ) → ℝ) : ℝ × (Fin m → ℝ) → ℝ :=
  fun p => fderiv ℝ G p ((1 : ℝ), (0 : Fin m → ℝ))

theorem contDiffOn_dh_STR02959 {m : ℕ} {Ω : Set (ℝ × (Fin m → ℝ))} (hΩ : IsOpen Ω)
    {G : ℝ × (Fin m → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) :
    ContDiffOn ℝ ∞ (dh_STR02959 G) Ω := by
  have h1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ G y) Ω := hG.fderiv_of_isOpen hΩ (by simp)
  exact h1.clm_apply contDiffOn_const

theorem contDiffOn_dh_iterate_STR02959 {m : ℕ} {Ω : Set (ℝ × (Fin m → ℝ))} (hΩ : IsOpen Ω)
    {G : ℝ × (Fin m → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) (k : ℕ) :
    ContDiffOn ℝ ∞ (dh_STR02959^[k] G) Ω := by
  induction k with
  | zero => simpa using hG
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact contDiffOn_dh_STR02959 hΩ ih

theorem iteratedDeriv_slice_STR02959 {m : ℕ} {Ω : Set (ℝ × (Fin m → ℝ))} (hΩ : IsOpen Ω)
    {G : ℝ × (Fin m → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) (z : Fin m → ℝ) (k : ℕ) :
    ∀ s : ℝ, (s, z) ∈ Ω → iteratedDeriv k (fun s => G (s, z)) s = (dh_STR02959^[k] G) (s, z) := by
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    have hopen : IsOpen {s' : ℝ | (s', z) ∈ Ω} :=
      hΩ.preimage (by fun_prop : Continuous fun s' : ℝ => (s', z))
    have hev : iteratedDeriv k (fun s => G (s, z)) =ᶠ[𝓝 s]
        fun s' => (dh_STR02959^[k] G) (s', z) :=
      Filter.eventually_of_mem (hopen.mem_nhds hs) fun s' hs' => ih s' hs'
    rw [iteratedDeriv_succ, hev.deriv_eq, Function.iterate_succ_apply']
    have hH := (contDiffOn_dh_iterate_STR02959 hΩ hG k).contDiffAt (hΩ.mem_nhds hs)
    have hd : DifferentiableAt ℝ (dh_STR02959^[k] G) (s, z) :=
      hH.differentiableAt (by simp)
    have hp : HasDerivAt (fun s' : ℝ => (s', z)) ((1 : ℝ), (0 : Fin m → ℝ)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    have := hd.hasFDerivAt.comp_hasDerivAt s hp
    exact this.deriv



theorem iteratedFDeriv_const_STR02959 (f : ℝ → ℝ) (k : ℕ) (x h : ℝ) :
    iteratedFDeriv ℝ k f x (fun _ => h) = h ^ k * iteratedDeriv k f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have : (fun _ : Fin k => h) = fun _ => h • (1 : ℝ) := by simp
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp

theorem taylor_STR02959 (f : ℝ → ℝ) (h : ℝ)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 f (t * h))
    (h0 : ∀ j, j ≤ 3 → iteratedDeriv j f 0 = 0) :
    f h = h ^ 4 * ((1 / (Nat.factorial 3 : ℝ)) *
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 3 * iteratedDeriv 4 f (t * h)) := by
  have key := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := 0) (y := h) (n := 3)
    (fun t ht => by simp only [zero_add, smul_eq_mul]; exact_mod_cast hf t ht)
  simp only [iteratedFDeriv_const_STR02959, zero_add] at key
  have hs : ∑ k ∈ Finset.range (3 + 1), ((k.factorial : ℝ))⁻¹ • (h ^ k * iteratedDeriv k f 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [h0 k (by simpa [Nat.lt_succ_iff] using hk)]
    simp
  rw [hs, zero_add] at key
  rw [key]
  simp only [smul_eq_mul, one_div]
  norm_num
  have hx : ∀ x : ℝ, (1 - x) ^ 3 * (h ^ 4 * iteratedDeriv 4 f (x * h)) =
      h ^ 4 * ((1 - x) ^ 3 * iteratedDeriv 4 f (x * h)) := by
    intro x; ring
  simp_rw [hx]
  rw [intervalIntegral.integral_const_mul]
  ring


noncomputable def quotientRemainder_STR02959 {m : ℕ} (G : ℝ × (Fin m → ℝ) → ℝ) (h : ℝ)
    (z : Fin m → ℝ) : ℝ :=
  (1 / (Nat.factorial 3 : ℝ)) *
    ∫ t in (0 : ℝ)..1, (1 - t) ^ 3 * iteratedDeriv 4 (fun s => G (s, z)) (t * h)

theorem star_STR02959 {m : ℕ} {z₀ z : Fin m → ℝ} {h r t : ℝ}
    (hp : (h, z) ∈ Metric.ball ((0 : ℝ), z₀) r) (ht : t ∈ Icc (0 : ℝ) 1) :
    (t * h, z) ∈ Metric.ball ((0 : ℝ), z₀) r := by
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff] at hp ⊢
  refine ⟨?_, hp.2⟩
  rw [abs_mul, abs_of_nonneg ht.1]
  calc t * |h| ≤ 1 * |h| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)
    _ = |h| := one_mul _
    _ < r := hp.1

theorem smooth_cutoff_STR02959 {m : ℕ} {Ω : Set (ℝ × (Fin m → ℝ))} (hΩ : IsOpen Ω)
    {G : ℝ × (Fin m → ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G Ω) {z₀ : Fin m → ℝ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball ((0 : ℝ), z₀) R ⊆ Ω) :
    ∃ V : ℝ × (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ V ∧
      ∀ p ∈ Metric.ball ((0 : ℝ), z₀) (R / 4), V p = quotientRemainder_STR02959 G p.1 p.2 := by
  set p₀ : ℝ × (Fin m → ℝ) := ((0 : ℝ), z₀) with hp₀
  let χ : ContDiffBump p₀ := ⟨R / 4, R / 2, by positivity, by linarith⟩
  set K : ℝ × (Fin m → ℝ) → ℝ := dh_STR02959^[4] G with hK
  have hKs : ContDiffOn ℝ ∞ K Ω := contDiffOn_dh_iterate_STR02959 hΩ hG 4
  have hKt : ContDiff ℝ ∞ (fun q => χ q * K q) := by
    rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : dist q p₀ ≤ R / 2
    · have hqΩ : q ∈ Ω := hball (by
        rw [Metric.mem_ball]
        have : R / 2 < R := by linarith
        exact lt_of_le_of_lt hq this)
      exact (χ.contDiff.contDiffAt).mul (hKs.contDiffAt (hΩ.mem_nhds hqΩ))
    · replace hq := not_le.1 hq
      have hev : (fun q => χ q * K q) =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
        have hopen : IsOpen {x : ℝ × (Fin m → ℝ) | R / 2 < dist x p₀} :=
          isOpen_lt continuous_const (by fun_prop)
        refine Filter.eventually_of_mem (hopen.mem_nhds hq) fun x hx => ?_
        have : χ x = 0 := χ.zero_of_le_dist (le_of_lt hx)
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  let Φ : ℝ × (ℝ × (Fin m → ℝ)) → ℝ := fun q =>
    ((1 - q.1) ^ 3 / 6) * (χ (q.1 * q.2.1, q.2.2) * K (q.1 * q.2.1, q.2.2))
  have hΦ : ContDiff ℝ ∞ Φ := by
    have h1 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × (Fin m → ℝ)) => (q.1 * q.2.1, q.2.2)) := by
      fun_prop
    have h2 : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × (Fin m → ℝ)) => (1 - q.1) ^ 3 / 6) := by
      fun_prop
    exact h2.mul (hKt.comp h1)
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, Φ (t, x), ?_, ?_⟩
  · exact contDiff_infty.2 fun n =>
      contDiff_param_integral_STR02959 n Φ (contDiff_infty.1 hΦ n)
  · intro p hp
    unfold quotientRemainder_STR02959
    have hcongr : ∀ t ∈ uIcc (0 : ℝ) 1, Φ (t, p) =
        (1 / 6 : ℝ) * ((1 - t) ^ 3 * iteratedDeriv 4 (fun s => G (s, p.2)) (t * p.1)) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hs : (t * p.1, p.2) ∈ Metric.ball p₀ (R / 4) := star_STR02959 hp ht
      have hΩmem : (t * p.1, p.2) ∈ Ω := hball (by
        refine Metric.ball_subset_ball (by linarith) hs)
      have hχ : χ (t * p.1, p.2) = 1 :=
        χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hs)
      rw [iteratedDeriv_slice_STR02959 hΩ hG p.2 4 _ hΩmem]
      simp only [Φ, hχ]
      ring
    show (∫ t in (0 : ℝ)..1, Φ (t, p)) = _
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
    norm_num [Nat.factorial]

theorem str029_59_smooth_division_coordinate_power {m : ℕ}
    {Ω : Set (ℝ × (Fin m → ℝ))} (hΩ : IsOpen Ω) {G : ℝ × (Fin m → ℝ) → ℝ}
    (hG : ContDiffOn ℝ ∞ G Ω) {U : Set (Fin m → ℝ)}
    (hU : ∀ z ∈ U, ((0 : ℝ), z) ∈ Ω)
    (hvanish : ∀ j : ℕ, j ≤ 3 → ∀ z ∈ U, iteratedDeriv j (fun h => G (h, z)) 0 = 0)
    {z₀ : Fin m → ℝ} (hz₀ : z₀ ∈ U) :
    ∃ W : Set (ℝ × (Fin m → ℝ)), IsOpen W ∧ ((0 : ℝ), z₀) ∈ W ∧ W ⊆ Ω ∧
      (∀ h z t, (h, z) ∈ W → t ∈ Icc (0 : ℝ) 1 → (t * h, z) ∈ W) ∧
      ContDiffOn ℝ ∞ (fun p => quotientRemainder_STR02959 G p.1 p.2) W ∧
      (∀ h z, (h, z) ∈ W → z ∈ U → h ≠ 0 →
        quotientRemainder_STR02959 G h z = G (h, z) / h ^ 4) ∧
      (∀ z, ((0 : ℝ), z) ∈ W → z ∈ U →
        quotientRemainder_STR02959 G 0 z = iteratedDeriv 4 (fun h => G (h, z)) 0 / (Nat.factorial 4 : ℝ)) := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 hΩ _ (hU z₀ hz₀)
  obtain ⟨V, hV, hVeq⟩ := smooth_cutoff_STR02959 hΩ hG hR hball
  have hWΩ : Metric.ball ((0 : ℝ), z₀) (R / 4) ⊆ Ω :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  refine ⟨Metric.ball ((0 : ℝ), z₀) (R / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity),
    hWΩ, fun h z t hp ht => star_STR02959 hp ht, ?_, ?_, ?_⟩
  · exact hV.contDiffOn.congr fun p hp => (hVeq p hp).symm
  · intro h z hp hzU hh
    have hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 4 (fun s => G (s, z)) (t * h) := by
      intro t ht
      have hmem := hWΩ (star_STR02959 hp ht)
      have h1 : ContDiffAt ℝ ∞ G (t * h, z) := hG.contDiffAt (hΩ.mem_nhds hmem)
      have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => (s, z)) (t * h) := by fun_prop
      exact (h1.comp (t * h) h2).of_le (by simp)
    have := taylor_STR02959 (fun s => G (s, z)) h hf (fun j hj => hvanish j hj z hzU)
    unfold quotientRemainder_STR02959
    rw [eq_div_iff (pow_ne_zero 4 hh), mul_comm]
    exact this.symm
  · intro z hp hzU
    unfold quotientRemainder_STR02959
    simp only [mul_zero]
    rw [intervalIntegral.integral_mul_const]
    have : ∫ t in (0 : ℝ)..1, (1 - t) ^ 3 = 1 / 4 := by
      rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 3) 1]
      norm_num [integral_pow]
    rw [this]
    have h3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
    have h4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [h3, h4]
    ring

end DGPS.Frontier.STR029
