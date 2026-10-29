/- Apache-2.0 compatible supporting index-countability adaptation.
From StatLean/Stat-Lean commit86b3823f77fc2b0f5a9923f85b588a4f8a65f94c,
StatLean/AsymptoticStatistics/ForMathlib/Probability/IsonormalProcess.lean,
original SHA eab89af1820ec44fc960b1a702a99f4267ba6f182759504d4b585dcc0bc6c5fa.
MODIFIED: narrow countability proof only, generic basis index and DGRHS namespace.
License preserved alongside as BasisCountability.LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic
namespace DGRHS.Kernel
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
theorem countable_of_separable_index [TopologicalSpace.SeparableSpace H] {ι : Type*}
    (b : HilbertBasis ι ℝ H) : Countable ι := by
  -- pairwise-disjoint open balls of radius `1/2` around the orthonormal vectors
  have hdisj : (Set.univ : Set ι).PairwiseDisjoint
      (fun x : ι => Metric.ball (b x) (1 / 2 : ℝ)) := by
    intro x _ y _ hxy
    have hbxy : b x ≠ b y := fun h =>
      hxy (b.orthonormal.linearIndependent.injective h)
    -- `dist (b x) (b y) = √2`
    have hdist : dist (b x) (b y) = Real.sqrt 2 := by
      rw [dist_eq_norm]
      have hsq : ‖b x - b y‖ ^ 2 = 2 := by
        rw [norm_sub_sq_real, b.orthonormal.1 x, b.orthonormal.1 y]
        have : (inner ℝ (b x) (b y) : ℝ) = 0 := by
          have := b.orthonormal.2 (i := x) (j := y) (by exact fun h => hbxy (by rw [h]))
          simpa using this
        rw [this]; norm_num
      have hnn : (0 : ℝ) ≤ ‖b x - b y‖ := norm_nonneg _
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
        sq_nonneg (‖b x - b y‖ - Real.sqrt 2)]
    refine Metric.ball_disjoint_ball ?_
    rw [hdist]
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hcount : (Set.univ : Set ι).Countable :=
    hdisj.countable_of_isOpen (fun x _ => Metric.isOpen_ball)
      (fun x _ => ⟨b x, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.mp hcount

end DGRHS.Kernel
#print axioms DGRHS.Kernel.countable_of_separable_index
