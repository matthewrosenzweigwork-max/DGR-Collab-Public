import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
Packet P9h, unit 2 (part 2): termwise iterated differentiation of a convergent series of functions
that are smooth only on an open set `U` (e.g. the lattice sum of a kernel with a singularity at the
origin, off the lattice), under summable bounds that are uniform only on a ball around each point of
`U`.  Mathlib's `iteratedFDeriv_tsum` requires global bounds; the proof here is the same induction
but with the local `hasFDerivAt_tsum_of_isPreconnected`.
-/

noncomputable section
open Metric Filter
open scoped Topology
namespace DGRHS.Periodic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : Type*}

theorem iteratedFDeriv_tsum_of_local_bounds (f : α → E → ℝ) (U : Set E) (hU : IsOpen U) (N : ℕ)
    (hdf : ∀ i, ∀ y ∈ U, ∀ k : ℕ, k < N → DifferentiableAt ℝ (iteratedFDeriv ℝ k (f i)) y)
    (hb : ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ ball z r ⊆ U ∧ ∀ k : ℕ, k ≤ N →
      ∃ u : α → ℝ, Summable u ∧ ∀ i, ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ u i) :
    ∀ k : ℕ, k ≤ N → ∀ z ∈ U,
      iteratedFDeriv ℝ k (fun y => ∑' i, f i y) z = ∑' i, iteratedFDeriv ℝ k (f i) z := by
  intro k
  induction k with
  | zero =>
    intro _ z _
    simp_rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).symm.toContinuousLinearEquiv.map_tsum
  | succ k IH =>
    intro hk z hz
    have hkN : k < N := hk
    obtain ⟨r, hr, hrU, hbd⟩ := hb z hz
    obtain ⟨u, hu, hu'⟩ := hbd (k + 1) hk
    obtain ⟨u0, hu0, hu0'⟩ := hbd k (Nat.le_of_succ_le hk)
    have hdiff : ∀ i, ∀ y ∈ ball z r,
        HasFDerivAt (iteratedFDeriv ℝ k (f i)) (fderiv ℝ (iteratedFDeriv ℝ k (f i)) y) y := by
      intro i y hy
      exact (hdf i y (hrU hy) k hkN).hasFDerivAt
    have hbound : ∀ i, ∀ y ∈ ball z r, ‖fderiv ℝ (iteratedFDeriv ℝ k (f i)) y‖ ≤ u i := by
      intro i y hy
      rw [norm_fderiv_iteratedFDeriv]
      exact hu' i y hy
    have hsum0 : Summable fun i => iteratedFDeriv ℝ k (f i) z :=
      .of_norm_bounded hu0 (fun i => hu0' i z (mem_ball_self hr))
    have hF := hasFDerivAt_tsum_of_isPreconnected (f := fun i => iteratedFDeriv ℝ k (f i))
      (f' := fun i y => fderiv ℝ (iteratedFDeriv ℝ k (f i)) y) hu isOpen_ball
      (convex_ball z r).isPreconnected (fun i y hy => hdiff i y hy) (fun i y hy => hbound i y hy)
      (mem_ball_self hr) hsum0 (mem_ball_self hr)
    have heq : iteratedFDeriv ℝ k (fun y => ∑' i, f i y) =ᶠ[𝓝 z]
        fun y => ∑' i, iteratedFDeriv ℝ k (f i) y := by
      filter_upwards [hU.mem_nhds hz] with y hy
      exact IH (Nat.le_of_succ_le hk) y hy
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq, hF.fderiv]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) ℝ).symm.toContinuousLinearEquiv.map_tsum


/-- Differentiability of the iterated derivatives of the series (below the order `N`). -/
theorem differentiableAt_iteratedFDeriv_tsum_of_local_bounds (f : α → E → ℝ) (U : Set E)
    (hU : IsOpen U) (N : ℕ)
    (hdf : ∀ i, ∀ y ∈ U, ∀ k : ℕ, k < N → DifferentiableAt ℝ (iteratedFDeriv ℝ k (f i)) y)
    (hb : ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ ball z r ⊆ U ∧ ∀ k : ℕ, k ≤ N →
      ∃ u : α → ℝ, Summable u ∧ ∀ i, ∀ y ∈ ball z r, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ u i) :
    ∀ k : ℕ, k < N → ∀ z ∈ U,
      DifferentiableAt ℝ (iteratedFDeriv ℝ k (fun y => ∑' i, f i y)) z := by
  intro k hkN z hz
  obtain ⟨r, hr, hrU, hbd⟩ := hb z hz
  obtain ⟨u, hu, hu'⟩ := hbd (k + 1) hkN
  obtain ⟨u0, hu0, hu0'⟩ := hbd k (Nat.le_of_lt hkN)
  have hdiff : ∀ i, ∀ y ∈ ball z r,
      HasFDerivAt (iteratedFDeriv ℝ k (f i)) (fderiv ℝ (iteratedFDeriv ℝ k (f i)) y) y := by
    intro i y hy
    exact (hdf i y (hrU hy) k hkN).hasFDerivAt
  have hbound : ∀ i, ∀ y ∈ ball z r, ‖fderiv ℝ (iteratedFDeriv ℝ k (f i)) y‖ ≤ u i := by
    intro i y hy
    rw [norm_fderiv_iteratedFDeriv]
    exact hu' i y hy
  have hsum0 : Summable fun i => iteratedFDeriv ℝ k (f i) z :=
    .of_norm_bounded hu0 (fun i => hu0' i z (mem_ball_self hr))
  have hF := hasFDerivAt_tsum_of_isPreconnected (f := fun i => iteratedFDeriv ℝ k (f i))
    (f' := fun i y => fderiv ℝ (iteratedFDeriv ℝ k (f i)) y) hu isOpen_ball
    (convex_ball z r).isPreconnected (fun i y hy => hdiff i y hy) (fun i y hy => hbound i y hy)
    (mem_ball_self hr) hsum0 (mem_ball_self hr)
  have heq : iteratedFDeriv ℝ k (fun y => ∑' i, f i y) =ᶠ[𝓝 z]
      fun y => ∑' i, iteratedFDeriv ℝ k (f i) y := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact iteratedFDeriv_tsum_of_local_bounds f U hU N hdf hb k hkN.le y hy
  exact (hF.differentiableAt).congr_of_eventuallyEq heq

end DGRHS.Periodic
#print axioms DGRHS.Periodic.iteratedFDeriv_tsum_of_local_bounds
#print axioms DGRHS.Periodic.differentiableAt_iteratedFDeriv_tsum_of_local_bounds
