import DGPS.Frontier.STR029.T26s1
import DGPS.Frontier.STR029.T26s2
import DGPS.Frontier.STR029.T26s3
import DGPS.Frontier.STR029.T26s4
import DGPS.Frontier.STR029.T26s5

/-!
# STR029.26: exactly three global positive-entropy optimizers

The parent theorem preserves the saved split-plan signature. The auxiliary theorem proves the
same optimizer conclusions for supplied branch data, so later regularity results can use these
conclusions for their existing witnesses on a common smaller interval.

## R5 notes

The split-plan reading compares absolute densities almost everywhere for distinctness and
exhaustion, but selects pointwise chart representatives for the three branches. The ordinary
quotient uses the fully qualified angular-normalization constant. Attainment is transported from
the real-line weak domain through s1 and s2. The helper adds no assumption to the parent theorem:
its branch hypotheses come from T24 and its uniform identification hypothesis from s5, all for
the same witnesses. The helper's statement is auxiliary and requires external statement review;
its returned radius is explicitly bounded by both supplied positive radii. No regularity statement
is claimed merely by obtaining a separate existential family of branches.
-/

open scoped ContDiff ENNReal
open Filter Topology
open DGPS.Analysis.PeriodicHolder
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

/-! ### Assembly: attainment for the packet problem (uses T11, s1, s2 and T01) -/

theorem attain_STR02926 : ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < |h| → |h| < δ →
    ∃ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ ∧
      ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
        ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
          ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ') := by
  obtain ⟨δ, hδ, -, hmain⟩ := str029_11_positive_entropy_attainment_angular_finite_information
  refine ⟨δ, hδ, fun h h0 hδh => ?_⟩
  obtain ⟨G, d, hd, hGd⟩ := hmain h h0 hδh
  have hd' := hd
  obtain ⟨hG0, hder, hnorm, hent⟩ := hd'
  obtain ⟨hAng, hEnt, hQ⟩ := s1_angDom_to_angular_STR02926 h G d hG0 hder hnorm
  obtain ⟨ρ, hρ⟩ := exists_abs_of_angDomain_STR02901 h hAng
  have hentpos : 0 < angEntropy_STR02901 h (gAng_STR02901 h ρ) := by
    rw [hρ, hEnt]; exact hent
  refine ⟨ρ, (ordinaryEntropy_pos_iff_STR02901 h ρ).2 hentpos, ?_⟩
  have key : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ' := by
    refine (optimizer_transfer_STR02901 h ρ).2 ?_
    intro g' hg' hpos'
    obtain ⟨G', d', hd'', hq'⟩ := s2_angular_to_angDom_STR02926 h g' hg' hpos'
    rw [hρ, hQ hent, ← hq']
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hGd]
    exact csInf_le ⟨0, by rintro q ⟨g₁, d₁, hd₁, rfl⟩; exact angQuot_nonneg_STR02911 hd₁⟩
      ⟨G', d', hd'', rfl⟩
  exact key

/-! ### Assembly: quotient of a chart density -/

theorem quot_of_chart_STR02926 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ))
    (hH : 0 < entropyChart_STR02949 h u) (q : ℝ)
    (hq : fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) = q) :
    ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) = ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal q := by
  obtain ⟨he, hf⟩ := s3b_chart_invariants_STR02926 h hu ρ hρ
  rw [he, hf, ← hq, ENNReal.ofReal_div_of_pos (by positivity), mul_div_assoc]
  congr 2
  rw [ENNReal.ofReal_mul (by norm_num)]
  simp

/-- Optimizer classification for supplied branch data. The conclusion retains both supplied
radius bounds so another result about the same branches can be restricted to this interval. -/
theorem str029_26_exactly_three_global_positive_entropy_optimizers_of_data
    {ψ : Par_STR02916 → E_STR02969} {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    {δbranch δidentify : ℝ} (hδbranch : 0 < δbranch) (hδidentify : 0 < δidentify)
    (hbranch : ∀ h ∈ Set.Ioo (-δbranch) δbranch, ∀ j : Fin 3, h ≠ 0 →
      0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
      fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
        (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
        1 + h ^ 2 * Z j h 2)
    (hZs : ∀ h ∈ Set.Ioo (-δbranch) δbranch, ∀ j : Fin 3, Z j h 2 = Z 0 h 2)
    (hdist : ∀ h ∈ Set.Ioo (-δbranch) δbranch, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)))
    (hidentify : ∀ h : ℝ, h ≠ 0 → |h| < δidentify → ∀ ρ : AbsoluteDensity 1,
      0 < ordinaryEntropy h ρ →
      (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
        ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
          ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) →
      ∃ j : Fin 3, ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δbranch ∧ δ ≤ δidentify ∧
    ∀ h : ℝ, 0 < |h| → |h| < δ →
      ∃ ρ : Fin 3 → AbsoluteDensity 1,
        -- the three densities are the chart densities ρ(h, u_j) of the branches
        (∀ (j : Fin 3) (θ : AngCircle), (ρ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ)) ∧
        -- each has positive entropy and the common quotient `a0 * (1 + h² s_j)` (with `a0 = 4 * π ^ 2`, the angular-normalization constant)
        (∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j)) ∧
        (∀ j : Fin 3, ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j)) =
          ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal (1 + h ^ 2 * Z j h 2)) ∧
        -- each is a global optimizer among all positive-entropy densities
        (∀ (j : Fin 3) (ρ' : AbsoluteDensity 1), 0 < ordinaryEntropy h ρ' →
          ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j)) ≤
            ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) ∧
        -- pairwise distinct (as elements of the almost-everywhere carrier)
        (∀ i j : Fin 3, i ≠ j → ¬ (ρ i).density =ᵐ[haar 1] (ρ j).density) ∧
        -- no other positive-entropy global optimizer
        (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
          (∀ ρ'' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ'' →
            ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ') ≤
              ordinaryFisher h ρ'' / (2 * ordinaryEntropy h ρ'')) →
          ∃ j : Fin 3, ρ'.density =ᵐ[haar 1] (ρ j).density) := by
  obtain ⟨δ₁₁, hδ₁₁, hatt⟩ := attain_STR02926
  refine ⟨min δbranch (min δ₁₁ δidentify), lt_min hδbranch (lt_min hδ₁₁ hδidentify),
    min_le_left _ _, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro h h0 hδ
  have hne : h ≠ 0 := abs_pos.mp h0
  have hlt24 : |h| < δbranch := lt_of_lt_of_le hδ (min_le_left _ _)
  have hlt11 : |h| < δ₁₁ :=
    lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_left _ _))
  have hlt3 : |h| < δidentify :=
    lt_of_lt_of_le hδ ((min_le_right _ _).trans (min_le_right _ _))
  have hmem24 : h ∈ Set.Ioo (-δbranch) δbranch := abs_lt.mp hlt24
  have hC2 : ∀ j : Fin 3, IsC2Alpha_STR02901 (1 / 2) (chartU_STR02924 ψ h (Z j h)) :=
    fun j => chartU_isC2_STR02924 ψ h (Z j h)
  choose ρ hρ using fun j : Fin 3 => s3a_exists_abs_of_chart_STR02926 h (hC2 j)
  have hae : ∀ j : Fin 3, ∀ᵐ θ ∂angHaar, (ρ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ) :=
    fun j => Filter.Eventually.of_forall (hρ j)
  have hq : ∀ j : Fin 3, ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j)) =
      ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal (1 + h ^ 2 * Z j h 2) := fun j =>
    quot_of_chart_STR02926 h (hC2 j) (ρ j) (hae j) (hbranch h hmem24 j hne).1 _
      (hbranch h hmem24 j hne).2
  have hpos : ∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j) := fun j => by
    rw [(s3b_chart_invariants_STR02926 h (hC2 j) (ρ j) (hae j)).1]
    exact ENNReal.ofReal_pos.2 (hbranch h hmem24 j hne).1
  obtain ⟨ρs, hρs, hρsopt⟩ := hatt h h0 hlt11
  obtain ⟨j0, hj0⟩ := hidentify h hne hlt3 ρs hρs hρsopt
  have hqs : ordinaryFisher h ρs / (2 * ordinaryEntropy h ρs) =
      ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal (1 + h ^ 2 * Z 0 h 2) := by
    rw [← hZs h hmem24 j0]
    exact quot_of_chart_STR02926 h (hC2 j0) ρs hj0 (hbranch h hmem24 j0 hne).1 _
      (hbranch h hmem24 j0 hne).2
  refine ⟨ρ, hρ, hpos, hq, ?_, ?_, ?_⟩
  · intro j ρ' hρ'
    rw [hq j, hZs h hmem24 j, ← hqs]
    exact hρsopt ρ' hρ'
  · intro i j hij
    exact s3c_chart_density_not_ae_STR02926 h (hC2 i) (hC2 j) (hdist h hmem24 hne i j hij)
      (ρ i) (ρ j) (hρ i) (hρ j)
  · intro ρ' hρ' hopt'
    obtain ⟨j, hj⟩ := hidentify h hne hlt3 ρ' hρ' hopt'
    refine ⟨j, ?_⟩
    have h1 := (ae_comp_angEquiv_iff (p := fun θ =>
      ρ'.density (angEquiv.symm θ) = (ρ j).density (angEquiv.symm θ))).2
      (hj.mono fun θ hθ => by rw [hθ, hρ j θ])
    have h2 : ∀ᵐ x ∂haar 1, ρ'.density x = (ρ j).density x := by simpa using h1
    exact h2


theorem str029_26_exactly_three_global_positive_entropy_optimizers :
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
              ∀ h : ℝ, 0 < |h| → |h| < δ →
                ∃ ρ : Fin 3 → AbsoluteDensity 1,
                  -- the three densities are the chart densities ρ(h, u_j) of the branches
                  (∀ (j : Fin 3) (θ : AngCircle), (ρ j).density (angEquiv.symm θ) =
                    rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ)) ∧
                  -- each has positive entropy and the common quotient `a0 * (1 + h² s_j)` (with `a0 = 4 * π ^ 2`, the angular-normalization constant)
                  (∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j)) ∧
                  (∀ j : Fin 3, ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j)) =
                    ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 * ENNReal.ofReal (1 + h ^ 2 * Z j h 2)) ∧
                  -- each is a global optimizer among all positive-entropy densities
                  (∀ (j : Fin 3) (ρ' : AbsoluteDensity 1), 0 < ordinaryEntropy h ρ' →
                    ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j)) ≤
                      ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) ∧
                  -- pairwise distinct (as elements of the almost-everywhere carrier)
                  (∀ i j : Fin 3, i ≠ j → ¬ (ρ i).density =ᵐ[haar 1] (ρ j).density) ∧
                  -- no other positive-entropy global optimizer
                  (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
                    (∀ ρ'' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ'' →
                      ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ') ≤
                        ordinaryFisher h ρ'' / (2 * ordinaryEntropy h ρ'')) →
                    ∃ j : Fin 3, ρ'.density =ᵐ[haar 1] (ρ j).density) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, δ₂₄, hδ₂₄, hδ₂₄η, hbranch, hdist, -⟩ :=
    str029_24_lift_reduced_branches_full_critical_densities
  obtain ⟨η₃, hη₃, hη₃η, hs5⟩ :=
    s5_radius_identification_STR02926 hUo hψC hψV hR hOo hOmem hEC hval hη hN0 hN1 hN2 hn0 hn1
      hn2 hKuniq hVo hV0 hU0 hψ0
  have hZs24 : ∀ h ∈ Set.Ioo (-δ₂₄) δ₂₄, ∀ j : Fin 3, Z j h 2 = Z 0 h 2 := by
    intro h hh j
    exact hZs h ⟨by linarith [hh.1], by linarith [hh.2]⟩ j
  obtain ⟨δ, hδ, hδ24, -, hopt⟩ :=
    str029_26_exactly_three_global_positive_entropy_optimizers_of_data hδ₂₄ hη₃
      (fun h hh j hne => (hbranch h hh j).2.2 hne) hZs24 hdist hs5
  exact ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, δ, hδ, hδ24.trans hδ₂₄η, hopt⟩

end DGPS.Frontier.STR029
