import DGRHS.Decoupling.Prop33MixedPatternConditionalPrefix
import DGRHS.Decoupling.Prop33HeterogeneousPairSwap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
Checked (AWS development build, P10): pointwise invariance of the all-pattern
sum under a coordinatewise replica swap. The swap convention matches
`Prop33HeterogeneousPairSwap`: `true` keeps a pair fixed and `false` swaps it.
For each fixed ordered tuple, the induced copy-label reindexing is an
involution. No symmetry of the tuple-indexed kernel is assumed.
-/

noncomputable section
open scoped BigOperators

namespace DGRHS.Decoupling.Prop33.CopySwap

variable {S E : Type*} {n k : ℕ}
variable [Fintype (DGRHS.Decoupling.Prop33.OrderedTuple n k)] [AddCommMonoid E]

/-- Values of a fixed ordered tuple under the slot-copy pattern `ell`;
`true` selects the first replica and `false` the second. -/
def sourcePatternArgument (z : Fin n → S × S)
    (t : DGRHS.Decoupling.Prop33.OrderedTuple n k) (ell : Fin k → Bool) : Fin k → S :=
  fun j => if ell j then (z (t.1 j)).1 else (z (t.1 j)).2

/-- Reindex a copy pattern after swapping the replicas selected by `s`.
Since `true` means no swap, only a `false` coordinate complements the slot
label. -/
def sourceSwapRelabel (s : Fin n → Bool) (t : DGRHS.Decoupling.Prop33.OrderedTuple n k)
    (ell : Fin k → Bool) : Fin k → Bool :=
  fun j => if s (t.1 j) then ell j else !(ell j)

/-- For each fixed tuple, relabeling twice recovers the original copy pattern. -/
theorem sourceSwapRelabel_involutive (s : Fin n → Bool)
    (t : DGRHS.Decoupling.Prop33.OrderedTuple n k) (ell : Fin k → Bool) :
    sourceSwapRelabel s t (sourceSwapRelabel s t ell) = ell := by
  funext j
  by_cases hs : s (t.1 j) <;> simp [sourceSwapRelabel, hs]

/-- The tuplewise copy-label change is a finite equivalence. -/
def sourceSwapRelabelEquiv (s : Fin n → Bool) (t : DGRHS.Decoupling.Prop33.OrderedTuple n k) :
    (Fin k → Bool) ≃ (Fin k → Bool) where
  toFun := sourceSwapRelabel s t
  invFun := sourceSwapRelabel s t
  left_inv := sourceSwapRelabel_involutive s t
  right_inv := sourceSwapRelabel_involutive s t

theorem sourcePatternArgument_swap_eq_relabel (s : Fin n → Bool)
    (z : Fin n → S × S) (t : DGRHS.Decoupling.Prop33.OrderedTuple n k)
    (ell : Fin k → Bool) :
    sourcePatternArgument (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected s z) t ell =
      sourcePatternArgument z t (sourceSwapRelabel s t ell) := by
  funext j
  by_cases hs : s (t.1 j) <;> cases hℓ : ell j <;>
    simp [sourcePatternArgument, DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected, sourceSwapRelabel, hs, hℓ]

/-- Statistic for one fixed copy pattern, preserving the original ordered
kernel index and slot order. -/
def sourceCopyPatternStatistic
    (f : DGRHS.Decoupling.Prop33.OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) (ell : Fin k → Bool) : E :=
  ∑ t : DGRHS.Decoupling.Prop33.OrderedTuple n k, f t (sourcePatternArgument z t ell)

/-- The symmetrized all-pattern statistic `T = Σ_ell D_ell`. -/
def sourceAllPatternStatistic
    (f : DGRHS.Decoupling.Prop33.OrderedTuple n k → (Fin k → S) → E)
    (z : Fin n → S × S) : E :=
  ∑ ell : Fin k → Bool, sourceCopyPatternStatistic f z ell

/-- The complete all-pattern statistic is invariant under every fixed
coordinatewise pair swap. This is a pointwise finite-sum identity, independent
of all probability laws and of any permutation symmetry of `f`. -/
theorem sourceAllPatternStatistic_swap_invariant
    (f : DGRHS.Decoupling.Prop33.OrderedTuple n k → (Fin k → S) → E)
    (s : Fin n → Bool) (z : Fin n → S × S) :
    sourceAllPatternStatistic f (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected s z) =
      sourceAllPatternStatistic f z := by
  classical
  unfold sourceAllPatternStatistic sourceCopyPatternStatistic
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ ell : Fin k → Bool,
        f t (sourcePatternArgument (DGRHS.Decoupling.Heterogeneous.heterogeneousSwapSelected s z) t ell)) =
      ∑ ell : Fin k → Bool,
        f t (sourcePatternArgument z t (sourceSwapRelabel s t ell)) := by
          apply Finset.sum_congr rfl
          intro ell hell
          rw [sourcePatternArgument_swap_eq_relabel]
    _ = ∑ ell : Fin k → Bool,
        f t (sourcePatternArgument z t ell) := by
          apply Fintype.sum_equiv (sourceSwapRelabelEquiv s t)
          intro ell
          rfl

end DGRHS.Decoupling.Prop33.CopySwap

#check @DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic_swap_invariant
#print axioms DGRHS.Decoupling.Prop33.CopySwap.sourceAllPatternStatistic_swap_invariant
