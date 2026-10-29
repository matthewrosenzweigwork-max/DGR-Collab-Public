import DGPS.Frontier.STR029.T67

/-!
# STR029.29: Spatial smoothness from the full Euler equation

## Provides

`str029_29_spatial_smoothness_full_euler_equation` preserves the constructed graph,
three branch witnesses, and every conclusion of STR029.67, and adds spatial
smoothness of their actual normalized densities on the same common interval.
`branches_contDiff_STR02929` provides the same-data transfer for arbitrary
graph and branch witnesses with all finite spatial lifts on one parameter set.

## R5 notes

* The conclusion concerns `rhoT_STR02901`, including its reference exponential
  and scalar normalizer, for every `j : Fin 3` and every field in the interval,
  including zero. It is not merely regularity of a chart representative.
* The full Euler equation enters through STR029.67. Its finite spatial lifts
  give smoothness of the chart logarithm; exponentiation and division by a
  scalar preserve smoothness. No projected equation is used.
* FD-006: the author directed, "Use one common smaller interval; preserve
  witnesses and disclose the restriction for R5." STR029.67 has already
  restricted the STR029.64/STR029.24 interval to ensure parameter membership in
  the smooth graph domain. This theorem preserves exactly those graph and
  branch witnesses and that single smaller interval, independently of spatial
  order, and makes no further restriction. Regularity on the entire earlier
  interval is not asserted. External R5 review and author freeze remain pending.
* The main statement has no hypotheses. Its full existential context is retained
  so downstream results can use smoothness with the same constructed branches.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

/-- All finite spatial lifts of one function imply smoothness of that function. -/
theorem spatial_contDiff_STR02929 {u : ℝ → ℝ}
    (hu : ∀ k : ℕ, ∃ f : PerCm_STR02966 k, f.val = u) :
    ContDiff ℝ ∞ u := by
  apply contDiff_infty.2
  intro k
  obtain ⟨f, hf⟩ := hu k
  rw [← hf]
  exact f.isPerCm.2

/-- Smoothness of the actual normalized density associated with a smooth chart. -/
theorem density_contDiff_STR02929 (h : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (rhoT_STR02901 h u) := by
  exact (Real.contDiff_exp.comp
    ((contDiff_const.mul (Real.contDiff_cos.comp
      (contDiff_const.mul contDiff_id))).add hu)).div_const _

/-- Transfer finite spatial lifts to the normalized densities without changing
any graph, branch witness, or common parameter set. -/
theorem branches_contDiff_STR02929 {ψ : Par_STR02916 → E_STR02969}
    {Z : Fin 3 → ℝ → Fin 3 → ℝ} {I : Set ℝ}
    (hreg : ∀ j : Fin 3, ∀ k : ℕ, ∃ W : ℝ → PerCm_STR02966 k,
      ∀ h ∈ I, (W h).val = chartU_STR02924 ψ h (Z j h)) :
    ∀ h ∈ I, ∀ j : Fin 3,
      ContDiff ℝ ∞ (rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) := by
  intro h hh j
  apply density_contDiff_STR02929
  apply spatial_contDiff_STR02929
  intro k
  obtain ⟨W, hWv⟩ := hreg j k
  exact ⟨W h, hWv h hh⟩

/-- Spatial smoothness of all three constructed normalized branch densities,
with the full STR029.67 context on its one common smaller interval. -/
theorem str029_29_spatial_smoothness_full_euler_equation :
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
                    ∃ M : ℝ, ∀ h ∈ Set.Icc a b, ‖iteratedDeriv 3 W h‖ ≤ M)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                ContDiff ℝ ∞ (rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)))) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC,
    hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1,
    hrot2, hZC, hZN, hZrot, hZs, hKuniq, δ, hδ, hδη, hA, hB, hC, hD, hreg⟩ :=
    str029_67_bootstrap_parameter_regularity_preserve_jets
  refine ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC,
    hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1,
    hrot2, hZC, hZN, hZrot, hZs, hKuniq, δ, hδ, hδη, hA, hB, hC, hD, hreg, ?_⟩
  apply branches_contDiff_STR02929
  intro j k
  obtain ⟨Uα, _, _, hUk⟩ := hreg j
  obtain ⟨W, _, hWv, _, _⟩ := hUk k
  exact ⟨W, hWv⟩

end DGPS.Frontier.STR029
