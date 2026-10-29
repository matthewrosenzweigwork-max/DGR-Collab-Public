import DGPS.Frontier.STR029.T67

/-!
# STR029.30: Higher-norm parameter regularity on one common interval

## Provides

`str029_30_higher_norm_parameter_regularity_same_interval` retains the constructed graph,
three branches, full critical-density conclusions, and their higher-norm regularity together.
For every spatial order the parameter map is C3 on the same open interval; its first two
jets agree under the natural inclusions, and its third derivative is bounded on every
smaller closed interval.

## R5 notes

The author directed in FD-006: "Use one common smaller interval; preserve witnesses and
disclose the restriction for R5." This theorem reuses the single interval already chosen
by STR029.67, which restricts STR029.24 to ensure membership in the smooth graph domain.
The restriction is independent of the spatial order. All retained critical-density clauses
and all regularity clauses use exactly the same graph, branches, and interval. No further
restriction is made here. Regularity on the full original STR029.24 interval is not claimed.
The frozen specification is unchanged; correspondence remains pending external R5 review.
-/

open scoped ContDiff
open Topology
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

theorem str029_30_higher_norm_parameter_regularity_same_interval_of_data
    {ψ : Par_STR02916 → E_STR02969} {U : Set Par_STR02916} {Z : ℝ → Fin 3 → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hψ : ContDiffOn ℝ ∞ ψ U) (hZ : ContDiffOn ℝ ∞ Z I)
    (hmem : ∀ h ∈ I, (h * Z h 0, h * Z h 1, h, h ^ 2 * Z h 2) ∈ U)
    (hE : ∀ h ∈ I, ∀ t, deriv (deriv (chartU_STR02924 ψ h (Z h))) t =
      P0_STR02964 (eulerF_STR02964 h (1 + h ^ 2 * Z h 2) (chartU_STR02924 ψ h (Z h))) t) :
    ∃ Uα : ℝ → PeriodicC2_STR02969, ContDiffOn ℝ ∞ Uα I ∧
      (∀ h ∈ I, (Uα h).val = chartU_STR02924 ψ h (Z h)) ∧
      ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k, ContDiffOn ℝ 3 W I ∧
        (∀ h ∈ I, (W h).val = chartU_STR02924 ψ h (Z h)) ∧
        (∀ h ∈ I, ∀ i : ℕ, i ≤ 2 →
          incl0_STR02967 k (iteratedDeriv i W h) = inclα0_STR02967 (iteratedDeriv i Uα h)) ∧
        (∀ a b : ℝ, Set.Icc a b ⊆ I → ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M) :=
  str029_67_bootstrap_parameter_regularity_preserve_jets_branch_regularity
    hI hψ hZ hmem hE

theorem str029_30_higher_norm_parameter_regularity_same_interval :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
                (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
                (h ≠ 0 →
                  0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
                  fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
                    (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
                    1 + h ^ 2 * Z j h 2)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
                rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
                  rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) ∧
              (∀ j : Fin 3, rhoT_STR02901 0 (chartU_STR02924 ψ 0 (Z j 0)) = qT_STR02901 0 ∧
                ∀ t, gradG_STR02950 0 0 (chartU_STR02924 ψ 0 (Z j 0)) t = 0) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ t,
                deriv (deriv (chartU_STR02924 ψ h (Z 0 h))) t =
                  P0_STR02964
                    (eulerF_STR02964 h (1 + h ^ 2 * Z 0 h 2) (chartU_STR02924 ψ h (Z 0 h))) t) ∧
              (∀ j : Fin 3, ∃ Uα : ℝ → PeriodicC2_STR02969,
                ContDiffOn ℝ ∞ Uα (Set.Ioo (-δ) δ) ∧
                (∀ h ∈ Set.Ioo (-δ) δ, (Uα h).val = chartU_STR02924 ψ h (Z j h)) ∧
                ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k, ContDiffOn ℝ 3 W (Set.Ioo (-δ) δ) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, (W h).val = chartU_STR02924 ψ h (Z j h)) ∧
                  (∀ h ∈ Set.Ioo (-δ) δ, ∀ i : ℕ, i ≤ 2 →
                    incl0_STR02967 k (iteratedDeriv i W h) =
                      inclα0_STR02967 (iteratedDeriv i Uα h)) ∧
                  (∀ a b : ℝ, Set.Icc a b ⊆ Set.Ioo (-δ) δ →
                    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M)) :=
  str029_67_bootstrap_parameter_regularity_preserve_jets

end DGPS.Frontier.STR029
