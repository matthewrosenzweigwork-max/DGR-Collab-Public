import DGPS.Frontier.STR029.T06
import DGPS.Frontier.STR029.T42

/-!
# STR029.07: Compactness with entropy and energy passage

Task id and title: STR029.07, "Compactness with entropy and energy passage" (node STR029). For fixed
`|h| ≤ 1/1000`, every sequence of STR029.06 data has a subsequence converging uniformly and weakly in
`H¹` to a continuous periodic `G ≥ 0` with `∫ G² q_h dm = 1`, with convergent entropies, and with
`E(G) ≤ liminf E(g n)`, where `E(G)` is the weighted energy of a periodic weak derivative of `G`.

## Provides

* `DGPS.Frontier.STR029.str029_07_compactness_entropy_energy_passage`: the main statement. For
  STR029.06 data `(g n, g' n, E n, H n)` indexed by `n` with common constants `K` and `A`, there are
  continuous periodic representatives `F n` of `g n`, a strictly increasing `σ`, and `G, d` such that
  `F (σ n) → G` uniformly on `ℝ`, `G ≥ 0` with `∫ G² q_h dm = 1`, `d` is a periodic weak derivative of
  `G`, `(g (σ n), g' (σ n)) ⇀ (G, d)` weakly in `H¹`, `H (σ n) → H(G)`, and
  `∫ d'² q_h dm ≤ liminf E` for every periodic weak derivative `d'` of `G`.
* `DGPS.Frontier.STR029.exists_representative_STR02907`: each single STR029.06 datum has a continuous
  periodic representative, obtained from the STR029.06 main statement (EX049.32).

## R5 notes

* Carriers. The normalized integrals and the reference density are the STR029.04 carriers
  `normInt_STR02904` and `qT_STR02904 h`. The periodic weak derivative predicate
  `IsPeriodicWeakDerivative_STR02933` (STR029.33) and the weak-convergence predicate
  `WeaklyConvergesH1_STR02942` (STR029.42) are used unchanged. The mixed carriers on `(0, 2π]` are
  bridged inside STR029.42; this unit does not touch them.
* Hypotheses. For each index `n` the hypotheses are exactly those of
  `str029_06_information_bound_low_quotients` with the fixed `h`, `|h| ≤ 1/1000`, and the shared constants
  `K = 8π² e^{1/500}` and `A = log (K + 2)`. None is added or dropped. The nonnegativity `g n ≥ 0` is used
  for the nonnegativity of `G`.
* Representatives (non-literal reading). Uniform convergence is a statement about continuous
  representatives. The main statement is existential in them: it asserts that there are continuous
  periodic representatives `F n` of `g n`, each supplied by STR029.06 through EX049.32, along which
  `F (σ n) → G` uniformly. Continuous periodic representatives are unique by the EX049.32 uniqueness, so
  the choice does not change the conclusion. That uniqueness is not restated here.
* Subsequence. The subsequence `σ` is the composite produced by STR029.42, a further subsequence of the
  STR029.38 subsequence. Uniform convergence and the convergence of the energies to `liminf E` therefore
  persist along `σ`. The liminf in the statement is the liminf of the original sequence: the energies
  `E (σ n)` converge to `liminf E` (STR029.38), and `Filter.Tendsto.liminf_eq` identifies the liminf
  along `σ` with it.
* Energy. `E(G)` is `∫ d² q_h dm` for a periodic weak derivative `d` of `G`. This value does not depend on
  the choice of `d` (the energy uniqueness lemma of STR029.42), so the bound is stated for every periodic
  weak derivative `d'` of `G`. The energy of `G` is then well defined rather than depending on a choice.
* Weak `H¹` convergence. `WeaklyConvergesH1_STR02942` is the STR029.42 definition: the pairs are periodic
  weak pairs, and the pairing with every periodic weak pair converges. The pairing uses the unweighted
  measure `m`. Since `exp (-2|h|) ≤ q_h ≤ exp (2|h|)`, this is the same as weak convergence in the weighted
  `H¹` norm (STR029.42 records the same equivalence).
* Entropy. `H (G) = ∫ G² log G² q_h dm` with `Real.log 0 = 0`, the convention of STR029.06 for `z log z`
  at zero. The convergence `H (σ n) → H (G)` is the entropy passage of STR029.42.
* Liminf. `liminf` is `Filter.liminf` on `ℝ` along `atTop`. The energies satisfy `0 ≤ E n ≤ 4 (A + 1)`
  (STR029.06), so the liminf is a finite genuine liminf.
* Scope. The sup-norm bound and the Hölder modulus of STR029.06 and STR029.37 are not part of this
  statement. The proof composes STR029.06 (representatives), STR029.42 (passage), and
  `Filter.Tendsto.liminf_eq`; no hypothesis beyond those of STR029.06 is added.
* Helpers. The helper carries the suffix `_STR02907`. The public declaration carries the prefix
  `str029_07_compactness_entropy_energy_passage`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace DGPS.Frontier.STR029

/-- Each single STR029.06 datum has a continuous periodic representative, supplied by the STR029.06
main statement through EX049.32. -/
lemma exists_representative_STR02907 {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hH1 : IsPeriodicWeakDerivative_STR02933 g g')
    (hnorm : normInt_STR02904 (fun t => g t ^ 2 * qT_STR02904 h t) = 1)
    {E H K A : ℝ}
    (hE : E = normInt_STR02904 (fun t => g' t ^ 2 * qT_STR02904 h t))
    (hH : H = normInt_STR02904 (fun t => g t ^ 2 * Real.log (g t ^ 2) * qT_STR02904 h t))
    (hHpos : 0 < H) (hquot : 4 * E / (2 * H) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2)) :
    ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F (2 * π) ∧
      F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g := by
  obtain ⟨-, F, hFc, hFp, -, hFg, -⟩ :=
    str029_06_information_bound_low_quotients hh hg0 hH1 hnorm hE hH hHpos hquot hK hA
  exact ⟨F, hFc, hFp, hFg⟩

/-- **STR029.07.** Fix `|h| ≤ 1/1000` and a sequence of STR029.06 data `(g n, g' n, E n, H n)`. There are
continuous periodic representatives `F n` of `g n`, a strictly increasing `σ`, and a continuous periodic
`G ≥ 0` with `∫ G² q_h dm = 1` and `F (σ n) → G` uniformly, together with a periodic weak derivative `d`
of `G` such that `(g (σ n), g' (σ n)) ⇀ (G, d)` weakly in `H¹`, the entropies `H (σ n)` converge to the
entropy of `G`, and every periodic weak derivative `d'` of `G` has weighted energy at most
`liminf E`. -/
theorem str029_07_compactness_entropy_energy_passage
    {h : ℝ} (hh : |h| ≤ 1 / 1000) {g g' : ℕ → ℝ → ℝ} {E H : ℕ → ℝ} {K A : ℝ}
    (hg0 : ∀ n t, 0 ≤ g n t)
    (hH1 : ∀ n, IsPeriodicWeakDerivative_STR02933 (g n) (g' n))
    (hnorm : ∀ n, normInt_STR02904 (fun t => g n t ^ 2 * qT_STR02904 h t) = 1)
    (hE : ∀ n, E n = normInt_STR02904 (fun t => g' n t ^ 2 * qT_STR02904 h t))
    (hH : ∀ n, H n = normInt_STR02904
      (fun t => g n t ^ 2 * Real.log (g n t ^ 2) * qT_STR02904 h t))
    (hHpos : ∀ n, 0 < H n) (hquot : ∀ n, 4 * E n / (2 * H n) ≤ 2)
    (hK : K = 8 * π ^ 2 * Real.exp (1 / 500)) (hA : A = Real.log (K + 2)) :
    ∃ F : ℕ → ℝ → ℝ, (∀ n, Continuous (F n) ∧ Function.Periodic (F n) (2 * π) ∧
        F n =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ G d : ℝ → ℝ,
        (Continuous G ∧ Function.Periodic G (2 * π) ∧ (∀ t, 0 ≤ G t) ∧
          normInt_STR02904 (fun t => G t ^ 2 * qT_STR02904 h t) = 1 ∧
          TendstoUniformly (fun n => F (σ n)) G atTop) ∧
        IsPeriodicWeakDerivative_STR02933 G d ∧
        WeaklyConvergesH1_STR02942 (fun n => g (σ n)) (fun n => g' (σ n)) G d ∧
        Tendsto (fun n => H (σ n)) atTop
          (𝓝 (normInt_STR02904 (fun t => G t ^ 2 * Real.log (G t ^ 2) * qT_STR02904 h t))) ∧
        ∀ d' : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 G d' →
          normInt_STR02904 (fun t => d' t ^ 2 * qT_STR02904 h t) ≤ liminf E atTop := by
  have hrep : ∀ n : ℕ, ∃ F : ℝ → ℝ, Continuous F ∧ Function.Periodic F (2 * π) ∧
      F =ᵐ[volume.restrict (Ioc 0 (2 * π))] g n := fun n =>
    exists_representative_STR02907 hh (hg0 n) (hH1 n) (hnorm n) (hE n) (hH n) (hHpos n)
      (hquot n) hK hA
  choose F hFc hFp hFg using hrep
  refine ⟨F, fun n => ⟨hFc n, hFp n, hFg n⟩, ?_⟩
  obtain ⟨σ, hσ, G, d, ⟨hGc, hGp, hG0, hGn, hGu, hEσ⟩, hd, hH1lim, -, -, hen, hent⟩ :=
    str029_42_weak_derivative_weighted_energy_entropy_passage hh hg0 hH1 hnorm hE hH hHpos hquot
      hK hA hFc hFp hFg
  refine ⟨σ, hσ, G, d, ⟨hGc, hGp, hG0, hGn, hGu⟩, hd, hH1lim, hent, fun d' hd' => ?_⟩
  rw [hEσ.liminf_eq] at hen
  exact (str029_42_weak_derivative_weighted_energy_entropy_passage_energy_unique h hd hd').symm.trans_le
    hen

end DGPS.Frontier.STR029
