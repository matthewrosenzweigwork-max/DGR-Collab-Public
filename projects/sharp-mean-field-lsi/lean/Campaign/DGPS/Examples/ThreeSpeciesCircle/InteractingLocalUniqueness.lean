import DGPS.Examples.ThreeSpeciesCircle.InteractingReducedBranches

/-! Full local chart uniqueness from ONE retained complement/reduced graph
packet. Actual neighborhood entry is an explicit factual condition, rather
than a presumed symmetry or an optimizer hypothesis. -/

noncomputable section
open Filter Topology Set Metric
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The retained complement iff and reduced K uniqueness identify both parts
of a full zero chart at the SAME psi. No independent graph selection is made. -/
theorem interactingChart_retained_zero_unique
    (h : ℝ) (U : Set (ℝ × ℝ × ℝ × ℝ)) (V : Set E_STR02969)
    (ψ : (ℝ × ℝ × ℝ × ℝ) → E_STR02969)
    (E : ℝ × (Fin 3 → ℝ) → ℝ) (K : ℝ × (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Z : ℝ → (Fin 3 → ℝ)) (z0 : Fin 3 → ℝ) (r : ℝ)
    (hgraph : ∀ p ∈ U, ∀ w ∈ V, interactingChartRange h (p, w) = 0 ↔ ψ p = w)
    (hform : ∀ x, let u := (h * x.2 0) • cosC2_STR02915 + (h * x.2 1) • sinC2_STR02915 +
              (ψ (x.1, h * x.2 0, h * x.2 1, h ^ 2 * x.2 2) : PeriodicC2_STR02969)
            E x = interactingChartDeficit h (x.1, h ^ 2 * x.2 2, u) / h ^ 4 ∧
            K x = ![(h ^ 3)⁻¹ * meanCLM_STR02954
                (interactingChartGradient h (x.1, h ^ 2 * x.2 2, u) * e0_STR02955 cosC2_STR02915),
              (h ^ 3)⁻¹ * meanCLM_STR02954
                (interactingChartGradient h (x.1, h ^ 2 * x.2 2, u) * e0_STR02955 sinC2_STR02915), E x])
    (hUnique : ∀ x ∈ ball ((0 : ℝ), z0) r, K x = 0 ↔ x.2 = Z x.1)
    (ε : ℝ) (z : Fin 3 → ℝ) (w : E_STR02969)
    (hp : (ε, h * z 0, h * z 1, h ^ 2 * z 2) ∈ U) (hw : w ∈ V)
    (hz : (ε, z) ∈ ball ((0 : ℝ), z0) r)
    (hG : interactingChartGradient h (ε, h ^ 2 * z 2,
      (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
        (w : PeriodicC2_STR02969)) = 0)
    (hF : interactingChartDeficit h (ε, h ^ 2 * z 2,
      (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
        (w : PeriodicC2_STR02969)) = 0) :
    z = Z ε ∧ w = ψ (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) := by
  have hR : interactingChartRange h ((ε, h * z 0, h * z 1, h ^ 2 * z 2), w) = 0 := by
    change PY_STR02955 (interactingChartGradient h (ε, h ^ 2 * z 2,
      (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
        (w : PeriodicC2_STR02969))) = 0
    rw [hG, map_zero]
  have hψw := (hgraph _ hp w hw).mp hR
  obtain ⟨hEform, hKform⟩ := hform (ε, z)
  have hE0 : E (ε, z) = 0 := by
    rw [hEform, hψw, hF, zero_div]
  have hK0 : K (ε, z) = 0 := by
    rw [hKform, hψw, hG]
    simp only [zero_mul, map_zero, mul_zero, hE0]
    ext i
    fin_cases i <;> rfl
  have hzZ : z = Z ε := (hUnique (ε, z) hz).mp hK0
  refine ⟨hzZ, ?_⟩
  rw [← hzZ]
  exact hψw.symm

/-- Smooth full-zero branches and their actual local uniqueness use ONE
ReducedBranches instance. Both neighborhoods and both seed identities are
retained for genuine later full-Holder neighborhood entry. -/
theorem interactingChart_local_unique_branches (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3,
      ∃ (U : Set (ℝ × ℝ × ℝ × ℝ)) (V : Set E_STR02969)
          (ψ : (ℝ × ℝ × ℝ × ℝ) → E_STR02969)
          (Z : ℝ → (Fin 3 → ℝ)) (η r : ℝ),
        IsOpen U ∧ IsOpen V ∧ D.ψ (ptPar_STR02923 h (D.Z j h)) ∈ V ∧
          0 < η ∧ 0 < r ∧ Z 0 = D.Z j h ∧
          ContDiffOn ℝ ∞ ψ U ∧ ContDiffOn ℝ ∞ Z (Ioo (-η) η) ∧
          ψ (0, h * D.Z j h 0, h * D.Z j h 1, h ^ 2 * D.Z j h 2) =
            D.ψ (ptPar_STR02923 h (D.Z j h)) ∧
          (∀ p ∈ U, ψ p ∈ V) ∧
          (∀ p ∈ U, ∀ w ∈ V, interactingChartRange h (p, w) = 0 ↔ ψ p = w) ∧
          (∀ ε : ℝ, |ε| < η →
            (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) ∈ U ∧
            let u := (h * Z ε 0) • cosC2_STR02915 + (h * Z ε 1) • sinC2_STR02915 +
              (ψ (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) : PeriodicC2_STR02969)
            interactingChartGradient h (ε, h ^ 2 * Z ε 2, u) = 0 ∧
              interactingChartDeficit h (ε, h ^ 2 * Z ε 2, u) = 0) ∧
          ∀ (ε : ℝ) (z : Fin 3 → ℝ) (w : E_STR02969),
            (ε, h * z 0, h * z 1, h ^ 2 * z 2) ∈ U → w ∈ V →
            (ε, z) ∈ ball ((0 : ℝ), D.Z j h) r →
            interactingChartGradient h (ε, h ^ 2 * z 2,
              (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
                (w : PeriodicC2_STR02969)) = 0 →
            interactingChartDeficit h (ε, h ^ 2 * z 2,
              (h * z 0) • cosC2_STR02915 + (h * z 1) • sinC2_STR02915 +
                (w : PeriodicC2_STR02969)) = 0 →
            z = Z ε ∧ w = ψ (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) := by
  obtain ⟨δ, hδ, hδr, hbranches⟩ := interactingChartReduced_local_branches D
  refine ⟨δ, hδ, hδr, fun h hh hhd j => ?_⟩
  obtain ⟨U, V, ψ, E, K, S, hUo, hVo, hw0, hψ, hψseed, hψV, hGraph, hRange,
    hSo, hS0, hES, hKS, hform, Z, η, r, hη, hr, hZ0, hZsmooth, hZeq, hUnique⟩ :=
      hbranches h hh hhd j
  refine ⟨U, V, ψ, Z, η, r, hUo, hVo, hw0, hη, hr, hZ0, hψ, hZsmooth,
    hψseed, hψV, hGraph, ?_, ?_⟩
  · intro ε hε
    obtain ⟨hK0, hpU⟩ := hZeq ε hε
    obtain ⟨hEform, hKform⟩ := hform (ε, Z ε)
    let u := (h * Z ε 0) • cosC2_STR02915 + (h * Z ε 1) • sinC2_STR02915 +
      (ψ (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) : PeriodicC2_STR02969)
    have hF0 : interactingChartDeficit h (ε, h ^ 2 * Z ε 2, u) = 0 := by
      have hz := congrArg (fun v : Fin 3 → ℝ => v 2) hK0
      rw [hKform] at hz
      change E (ε, Z ε) = 0 at hz
      rw [hEform] at hz
      change interactingChartDeficit h (ε, h ^ 2 * Z ε 2, u) / h ^ 4 = 0 at hz
      exact (div_eq_zero_iff.mp hz).resolve_right (pow_ne_zero 4 hh.ne')
    have hR0 := hRange (ε, h * Z ε 0, h * Z ε 1, h ^ 2 * Z ε 2) hpU
    change PY_STR02955 (interactingChartGradient h (ε, h ^ 2 * Z ε 2, u)) = 0 at hR0
    have hC0 : meanCLM_STR02954
        (interactingChartGradient h (ε, h ^ 2 * Z ε 2, u) * e0_STR02955 cosC2_STR02915) = 0 := by
      have hz := congrArg (fun v : Fin 3 → ℝ => v 0) hK0
      rw [hKform] at hz
      change (h ^ 3)⁻¹ * meanCLM_STR02954
        (interactingChartGradient h (ε, h ^ 2 * Z ε 2, u) * e0_STR02955 cosC2_STR02915) = 0 at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero 3 hh.ne'))
    have hS0 : meanCLM_STR02954
        (interactingChartGradient h (ε, h ^ 2 * Z ε 2, u) * e0_STR02955 sinC2_STR02915) = 0 := by
      have hz := congrArg (fun v : Fin 3 → ℝ => v 1) hK0
      rw [hKform] at hz
      change (h ^ 3)⁻¹ * meanCLM_STR02954
        (interactingChartGradient h (ε, h ^ 2 * Z ε 2, u) * e0_STR02955 sinC2_STR02915) = 0 at hz
      exact (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero 3 hh.ne'))
    exact ⟨hpU, interactingChartGradient_zero_of_projected h (h ^ 2 * Z ε 2) ε u hR0 hC0 hS0, hF0⟩
  · intro ε z w hp hw hz hG hF
    exact interactingChart_retained_zero_unique h U V ψ E K Z (D.Z j h) r
      hGraph hform hUnique ε z w hp hw hz hG hF

end DGPS.Examples.ThreeSpeciesCircle
