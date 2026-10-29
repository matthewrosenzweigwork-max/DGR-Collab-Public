import DGPS.Basic.Tightening
import DGPS.Basic.PositiveEntropyTightening
import DGPS.Basic.VanishingEntropyTaylor

/-!
# Abstract eventual exact LSI after defect removal (LIP084)

Under the abstract tightening hypotheses `TighteningHyp P E S R` (LIP079) and the energy
splitting inequality `E (f ∧ c) + E ((f - c)⁺) ≤ E f` for truncations of nonnegative admissible
tests (an explicit hypothesis, as in LIP081 and LIP083), for every `0 < r < R` there is `N₀`
such that `Ent (f²) ≤ 2 E f / r` for all `n ≥ N₀` and every admissible `f`.

The proof extracts the bounded violating sequence of LIP079; a subsequence has entropies
`h → hinf` with `hinf ≥ 0`.  If `hinf > 0` LIP081 gives `False`; if `hinf = 0` LIP083 does.

Design note: the energy splitting hypothesis `hsplit` is not a consequence of `TighteningHyp`;
it is carried as an explicit hypothesis of the theorem.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Analysis

/-- LIP084.  Abstract eventual exact LSI after defect removal: under `TighteningHyp P E S R` and
energy splitting of truncations, for every `0 < r < R` there is `N₀` such that
`Ent (f²) ≤ 2 E f / r` for all `n ≥ N₀` and all admissible `f ∈ S n`. -/
theorem abstract_eventual_exact_lsi_after_defect_removal
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R)
    (hsplit : ∀ n, ∀ f ∈ S n, (∀ x, 0 ≤ f x) → ∀ c : ℝ, 0 ≤ c →
      E n (fun x => min (f x) c) + E n (fun x => max (f x - c) 0) ≤ E n f)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ N0 : ℕ, ∀ n ≥ N0, ∀ f ∈ S n,
      homogeneousEntropy (P n) (fun x => f x ^ 2) ≤ ENNReal.ofReal (2 * E n f / r) := by
  by_contra hne
  obtain ⟨n, f, h, hn, hf, -, -, -, -, φ, hinf, einf, hφ, hlim, -⟩ :=
    abstract_tightening_hypotheses_and_bounded_violating_sequence hyp hr hrR hne
  have hn' : Tendsto (fun j => n (φ j)) atTop atTop := (hn.comp hφ).tendsto_atTop
  have hf' : ∀ j, f (φ j) ∈ S (n (φ j)) ∧ (∀ x, 0 ≤ f (φ j) x) ∧
      ∫ x, f (φ j) x ^ 2 ∂P (n (φ j)) = 1 ∧
      homogeneousEntropy (P (n (φ j))) (fun x => f (φ j) x ^ 2) = ENNReal.ofReal (h (φ j)) ∧
      0 < h (φ j) ∧ 2 * E (n (φ j)) (f (φ j)) < r * h (φ j) := fun j => hf (φ j)
  have hge : 0 ≤ hinf := ge_of_tendsto' hlim (fun j => (hf (φ j)).2.2.2.2.1.le)
  rcases hge.eq_or_lt with h0 | hpos
  · rw [← h0] at hlim
    exact vanishing_entropy_taylor_inequality_and_tightening hyp hsplit hr hrR
      (fun j => n (φ j)) hn' (fun j => f (φ j)) (fun j => h (φ j)) hf' hlim
  · exact positive_entropy_tightening_by_finitely_many_dyadic_cutoffs hyp hsplit hr hrR
      (fun j => n (φ j)) hn' (fun j => f (φ j)) (fun j => h (φ j)) hf' hpos hlim

end DGPS.Analysis
