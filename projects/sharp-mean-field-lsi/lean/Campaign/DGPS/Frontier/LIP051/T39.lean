import Mathlib
import DGPS.Frontier.LIP051.T37
import DGPS.Frontier.LIP051.T38

/-!
# LIP051.39: Disjoint-pair covariance

Task id: LIP051.39 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Disjoint-pair covariance.

Provides:
* `DGPS.Frontier.LIP051.lip051_39_disjoint_pair_covariance`: for a probability measure `μ` on `E`, a
  kernel `F : E → E → ℝ` satisfying the hypotheses of LIP051.38, and four pairwise distinct labels
  `i, j, k, l` in `Fin N`, the product `x ↦ F (x i) (x j) * F (x k) (x l)` on `Fin N → E` is integrable
  under `Q_N = Measure.pi (fun _ => μ)` and has `Q_N`-expectation zero.
* Helpers (all suffixed `_LIP05139`): `range_pair_disjoint_LIP05139` (the ranges of the label pairs
  `![i, j]` and `![k, l]` are disjoint when the four labels are pairwise distinct).

R5 notes:
* Four distinct labels. The specification's "four distinct particle labels" is read as the six
  pairwise inequalities `i ≠ j`, `k ≠ l`, `i ≠ k`, `i ≠ l`, `j ≠ k`, `j ≠ l`. The first two are the
  LIP051.38 hypothesis for each pair; the four cross inequalities make the two label blocks disjoint,
  which LIP051.37 requires. No ordering of the labels is assumed.
* Hypotheses of LIP051.38. `μ` is a probability measure, `F` is measurable (`_hF`), symmetric
  (`_hsymm`), in `L²(μ ⊗ μ)` (`hL2`), and centered (`hcent`), exactly as in LIP051.38. `_hF` and
  `_hsymm` are retained for fidelity to that class and are not used, as in LIP051.38. No hypothesis is
  added.
* Integrability. "Integrable" is Mathlib's `Integrable` for the displayed measure `Q_N`, and the
  expectation is the Bochner integral. The pair functions are integrable because they lie in `L²` on a
  probability space (`MemLp.integrable`); this is the specification's `L¹`–`L²` inequality in substance,
  and no library name for it is cited.
* Block reduction. The two blocks are the label vectors `![i, j]` and `![k, l]` in `Fin 2`-indexed
  form. The block function is `y ↦ F (y 0) (y 1)` on `Fin 2 → E`, and the same function is used for both
  blocks. The identity `F (x i) (x j) = f (restrictCoords_LIP05135 ![i, j] x)` is definitional.
* Mean zero of the block. The block function's zero mean and integrability under `μ^2` are obtained from
  LIP051.38 at `N = 2` with labels `0 ≠ 1`, applied to the same kernel. This uses the same hypotheses; it
  does not change the statement.
* Product expectation. The expectation of the product is the product of the two block integrals by
  LIP051.37, and each factor is zero, so the product is zero. The norm conjunct of LIP051.37 is not
  needed here.
* Mode indexing (FD-002). No mode index occurs in this unit: there is no Gaussian object, no Fourier or
  Hilbert-basis mode, and no coordinate set of positive modes. No positive-mode or mode-zero reading is
  adopted, and the issue recorded in FD-002 is not touched.
* No strengthening beyond the specification is claimed; the conclusion is exactly integrability and zero
  expectation of the displayed product.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory

/-- The ranges of the label pairs `![i, j]` and `![k, l]` are disjoint when the four labels are
pairwise distinct. -/
lemma range_pair_disjoint_LIP05139 {N : ℕ} {i j k l : Fin N}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Disjoint (Set.range (![i, j] : Fin 2 → Fin N)) (Set.range (![k, l] : Fin 2 → Fin N)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  fin_cases a <;> fin_cases b <;> simp_all

/-- **LIP051.39.** Let `μ` be a probability measure on `E`, and `F : E → E → ℝ` a measurable symmetric
kernel in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost every `y`, as in LIP051.38. If `i, j, k, l`
are four pairwise distinct labels in `Fin N`, then under `Q_N = Measure.pi (fun _ => μ)` the product
`F(X_i, X_j) F(X_k, X_l)` is integrable and has expectation zero. -/
theorem lip051_39_disjoint_pair_covariance
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (_hF : Measurable (fun p : E × E => F p.1 p.2))
    (_hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    {N : ℕ} (i j k l : Fin N) (hij : i ≠ j) (hkl : k ≠ l)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    Integrable (fun x : Fin N → E => F (x i) (x j) * F (x k) (x l))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      ∫ x, F (x i) (x j) * F (x k) (x l) ∂(Measure.pi (fun _ : Fin N => μ)) = 0 := by
  -- The block function on `Fin 2 → E`: the LIP051.38 pair function at labels `0`, `1`.
  have h38 := lip051_38_mean_coincident_pair_covariance μ F _hF _hsymm hL2 hcent
    (0 : Fin 2) 1 (by decide)
  have hf : Integrable (fun y : Fin 2 → E => F (y 0) (y 1))
      (Measure.pi (fun _ : Fin 2 => μ)) :=
    h38.1.integrable (by norm_num)
  have hfmean : ∫ y, F (y 0) (y 1) ∂(Measure.pi (fun _ : Fin 2 => μ)) = 0 := h38.2.1
  have hmain := lip051_37_factorization_across_disjoint_blocks μ
    (![i, j] : Fin 2 → Fin N) (![k, l] : Fin 2 → Fin N)
    (injective_pair_LIP05138 hij) (injective_pair_LIP05138 hkl)
    (range_pair_disjoint_LIP05139 hik hil hjk hjl)
    (fun y : Fin 2 → E => F (y 0) (y 1)) (fun y : Fin 2 → E => F (y 0) (y 1)) hf hf
  refine ⟨hmain.1, ?_⟩
  have key : ∫ x, F (x i) (x j) * F (x k) (x l) ∂(Measure.pi (fun _ : Fin N => μ)) =
      (∫ y, F (y 0) (y 1) ∂(Measure.pi (fun _ : Fin 2 => μ))) *
        ∫ y, F (y 0) (y 1) ∂(Measure.pi (fun _ : Fin 2 => μ)) := hmain.2.1
  rw [key, hfmean, zero_mul]

end DGPS.Frontier.LIP051
