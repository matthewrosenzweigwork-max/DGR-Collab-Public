import Mathlib
import DGPS.Frontier.LIP051.T38
import DGPS.Frontier.LIP051.T39
import DGPS.Frontier.LIP051.T40

/-!
# LIP051.09: Covariances of distinct-pair summands

Task id: LIP051.09 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Covariances of distinct-pair summands.

Provides:
* `DGPS.Frontier.LIP051.lip051_09_covariances_distinct_pair_summands`: for a probability measure `μ`
  on `E`, a measurable symmetric real kernel `F` in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost
  every `y`, and labels `i < j`, `k < l` in `Fin N`, under `Q_N = Measure.pi (fun _ => μ)`: the
  product `F(X_i, X_j) F(X_k, X_l)` is integrable; its expectation is `‖F‖²₂` when `(i, j) = (k, l)`
  and zero otherwise; and each summand `F(X_i, X_j)`, `F(X_k, X_l)` is integrable with mean zero.
* Helpers (all suffixed `_LIP05109`): `diagonal_pair_LIP05109` (the identical-pair case, from
  LIP051.38) and `offdiagonal_pairs_LIP05109` (the case of distinct increasing pairs, split into the
  one-overlap cases of LIP051.40 and the disjoint case of LIP051.39).

R5 notes:
* Hypotheses. They are exactly those of LIP051.38 to LIP051.40: `μ` is a probability measure, `F` is
  measurable (`hF`), symmetric (`hsymm`), in `L²(μ ⊗ μ)` (`hL2`), and centered in its first argument
  for almost every second argument (`hcent`). No hypothesis is added. The measurability hypothesis
  is passed on to LIP051.38 and is not otherwise used, as there.
* Labels. "For `i < j` and `k < l` in `Fin N`" is read as the strict order of `Fin N`. The summand
  `F(X_i, X_j)` is the function `x ↦ F (x i) (x j)` on `Fin N → E`, with the coordinate order kept.
* Covariance formula. "`E[F(X_i,X_j)F(X_k,X_l)] = ‖F‖²₂` if `(i,j) = (k,l)`, else `0`" is written as
  `if (i, j) = (k, l) then (eLpNorm (fun p => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2 else 0`. The norm is
  the real `L²(μ ⊗ μ)` norm, squared, as in LIP051.38. The expectation is the Bochner integral under
  `Q_N`. The identical-pair value is the second moment of LIP051.38, with `F · F` rewritten as `F ^ 2`.
* Integrability. "All products below are integrable" is the first conjunct, for the displayed product.
* Mean zero. "Every individual summand has mean zero" is stated as integrability together with zero
  integral, for each of the two summands. Integrability is included so that the mean is meaningful,
  since a Bochner integral of a non-integrable function is zero by convention. It is a conclusion
  supplied by LIP051.38, not a hypothesis.
* Case split. Since `i < j` and `k < l`, two increasing pairs with a common label and different pairs
  share exactly one label. The cases are: identical pairs (diagonal helper); `i = k`; `i = l`; `j = k`;
  `j = l` (one-overlap cases, reordered to the form of LIP051.40 using the symmetry of `F`); and no
  common label (LIP051.39). The reordering uses `hsymm` only to exchange the two arguments of a pair
  evaluation. This is the symmetric kernel class, not a new assumption.
* Mode indexing (FD-002). No mode index occurs in this unit. The indices `i, j, k, l` are particle
  labels in `Fin N`. There is no basis, no coordinate `e_j`, no Gaussian object and no zero mode. The
  positive-mode and mode-zero issue of FD-002 does not arise, and neither reading is adopted.
* No strengthening beyond the specification is claimed. The helpers are internal and the public
  declaration is the single theorem above.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory ENNReal

/-- The identical-pair case: for `i ≠ j`, the square `F(X_i, X_j)²` is integrable under `Q_N`, with
expectation `‖F‖²₂`. This is the second-moment conjunct of LIP051.38. -/
lemma diagonal_pair_LIP05109 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ) (hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    Integrable (fun x : Fin N → E => F (x i) (x j) * F (x i) (x j))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x i) (x j) ∂(Measure.pi (fun _ : Fin N => μ)) =
        (eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2 := by
  have h := lip051_38_mean_coincident_pair_covariance μ F hF hsymm hL2 hcent i j hij
  have e : (fun x : Fin N → E => F (x i) (x j) * F (x i) (x j)) =
      fun x => F (x i) (x j) ^ 2 := funext fun x => (pow_two _).symm
  rw [e]
  exact ⟨h.1.integrable_sq, h.2.2⟩

/-- Distinct increasing pairs: if `i < j`, `k < l` and the pairs differ, then the product
`F(X_i, X_j) F(X_k, X_l)` is integrable under `Q_N` with expectation zero. -/
lemma offdiagonal_pairs_LIP05109 {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (F : E → E → ℝ) (hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l) (hpair : ¬ (i, j) = (k, l)) :
    Integrable (fun x : Fin N → E => F (x i) (x j) * F (x k) (x l))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x k) (x l) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 := by
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := fun h => hpair (by rw [h])
    exact lip051_40_one_overlap_covariance μ F hF hsymm hL2 hcent i j l hij.ne hkl.ne hjl
  by_cases hil : i = l
  · subst l
    have hjk : j ≠ k := (lt_trans hkl hij).ne'
    have hfun : (fun x : Fin N → E => F (x i) (x j) * F (x k) (x i)) =
        fun x => F (x i) (x j) * F (x i) (x k) := by
      funext x
      rw [hsymm (x k) (x i)]
    rw [hfun]
    exact lip051_40_one_overlap_covariance μ F hF hsymm hL2 hcent i j k hij.ne hik hjk
  by_cases hjk : j = k
  · subst k
    have hfun : (fun x : Fin N → E => F (x i) (x j) * F (x j) (x l)) =
        fun x => F (x j) (x i) * F (x j) (x l) := by
      funext x
      rw [hsymm (x i) (x j)]
    rw [hfun]
    exact lip051_40_one_overlap_covariance μ F hF hsymm hL2 hcent j i l hij.ne'
      hkl.ne (lt_trans hij hkl).ne
  by_cases hjl : j = l
  · subst l
    have hfun : (fun x : Fin N → E => F (x i) (x j) * F (x k) (x j)) =
        fun x => F (x j) (x i) * F (x j) (x k) := by
      funext x
      rw [hsymm (x i) (x j), hsymm (x k) (x j)]
    rw [hfun]
    exact lip051_40_one_overlap_covariance μ F hF hsymm hL2 hcent j i k hij.ne' hkl.ne' hik
  exact lip051_39_disjoint_pair_covariance μ F hF hsymm hL2 hcent i j k l hij.ne hkl.ne
    hik hil hjk hjl

/-- **LIP051.09.** Let `μ` be a probability measure on `E`, and `F : E → E → ℝ` a measurable
symmetric kernel in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost every `y`. For labels
`i < j` and `k < l` in `Fin N`, under `Q_N = Measure.pi (fun _ => μ)`, the product
`F(X_i, X_j) F(X_k, X_l)` is integrable, with expectation `‖F‖²₂` when `(i, j) = (k, l)` and zero
otherwise, and each summand `F(X_i, X_j)`, `F(X_k, X_l)` is integrable with mean zero. -/
theorem lip051_09_covariances_distinct_pair_summands
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j k l : Fin N) (hij : i < j) (hkl : k < l) :
    (Integrable (fun x : Fin N → E => F (x i) (x j) * F (x k) (x l))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x k) (x l) ∂(Measure.pi (fun _ : Fin N => μ)) =
        if (i, j) = (k, l) then (eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2
        else 0) ∧
    (Integrable (fun x : Fin N → E => F (x i) (x j)) (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) ∂(Measure.pi (fun _ : Fin N => μ)) = 0) ∧
    (Integrable (fun x : Fin N → E => F (x k) (x l)) (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x k) (x l) ∂(Measure.pi (fun _ : Fin N => μ)) = 0) := by
  have h1 := lip051_38_mean_coincident_pair_covariance μ F hF hsymm hL2 hcent i j (ne_of_lt hij)
  have h2 := lip051_38_mean_coincident_pair_covariance μ F hF hsymm hL2 hcent k l (ne_of_lt hkl)
  refine ⟨?_, ⟨h1.1.integrable (by norm_num), h1.2.1⟩, ⟨h2.1.integrable (by norm_num), h2.2.1⟩⟩
  by_cases hpair : (i, j) = (k, l)
  · simp only [Prod.mk.injEq] at hpair
    obtain ⟨hik, hjl⟩ := hpair
    subst k
    subst l
    simp only [↓reduceIte]
    exact diagonal_pair_LIP05109 μ F hF hsymm hL2 hcent i j (ne_of_lt hij)
  · simp only [hpair, ↓reduceIte]
    exact offdiagonal_pairs_LIP05109 μ F hF hsymm hL2 hcent i j k l hij hkl hpair

end DGPS.Frontier.LIP051
