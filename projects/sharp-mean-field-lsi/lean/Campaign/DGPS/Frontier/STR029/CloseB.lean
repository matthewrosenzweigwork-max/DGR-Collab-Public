import DGPS.Frontier.STR029.T26
import DGPS.Frontier.STR029.T28
import DGPS.Frontier.STR029.T29
import DGPS.Frontier.STR029.T31
import DGPS.Frontier.STR029.T32

/-!
# STR029.CLOSE-B: canonical ordinary rate and branch expansions

## R5 notes

The canonical rate is `DGPS.ordinaryLSRate (ordinaryReference h)`, identified
with the optimizing absolute-density quotient through STR029.32 and with the
angular branch rate times `DGPS.Circle.AngularNormalization.a0` through STR029.26.
No new infimum replaces the canonical rate. Every regularity, entropy and rate
claim uses the same graph and branch witnesses from STR029.31; the same-data
helpers of STR029.26/.27/.28/.29 preserve these witnesses.

FD-006: the author permits one common smaller interval. We intersect finitely
many radii before quantifying over spatial order. STR029.31 already retains
the earlier critical-branch conclusions on its own smaller interval. No
spatial-order-dependent interval or additional hypothesis is introduced.
The logarithmic remainder includes the exact scalar normalizer of STR029.31.
The four-root conclusion is obtained by applying STR029.32's same-data classifier
to this very triple's positive entropy, global minimality and exhaustive
classification from STR029.26. No separately chosen CloseA witnesses are used;
pairwise distinctness and positive entropy separate all four measures.
Rotation of the supplied graph is obtained on the overlap with the equivariant
STR029.21 graph, by uniqueness of the same range equation. A common neighborhood
contains all three parameter curves. The displayed density shifts are negative:
rho_j(t) = rho_0(t - 2*pi*j/3), the pushforward convention for positive rotations
x -> x+j/3. Reflection identifies branch zero as even.
RD-012 places the unchanged public declaration name in this frontier module.
This closing statement is worker-authored and awaits external R5 review.
-/

open scoped ContDiff ENNReal
open Topology MeasureTheory
open DGPS DGPS.Circle.AngularNormalization
open DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

/-- The canonical rate equals the quotient of any actual global optimizer. -/
theorem canonical_eq_quot_STR029CLOSEB (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
      str025_quot h ρ ≤ str025_quot h σ) :
    ordinaryLSRate (ordinaryReference h) = str025_quot h ρ := by
  exact (ordinaryLSRate_eq_abs_inf_STR02932 h).trans
    (quot_eq_inf_STR02932 h ρ hpos hmin).symm

/-- Rotation of the actual normalized density for an equivariant graph. -/
theorem rho_rotation_STR029CLOSEB {U : Set Par_STR02916}
    {ψ : Par_STR02916 → E_STR02969}
    (hrot : ∀ p ∈ U, ∀ t : ℝ,
      ((ψ (rotPar_STR02916 (2 * Real.pi / 3) p) : E_STR02969) :
        PeriodicC2_STR02969).val t =
      ((ψ p : E_STR02969) : PeriodicC2_STR02969).val (t - 2 * Real.pi / 3))
    (h : ℝ) (z : Fin 3 → ℝ) (hp : ptPar_STR02923 h z ∈ U) (t : ℝ) :
    rhoT_STR02901 h (chartU_STR02924 ψ h (rot_STR02923 z)) t =
      rhoT_STR02901 h (chartU_STR02924 ψ h z) (t - 2 * Real.pi / 3) := by
  have he : chartU_STR02924 ψ h (rot_STR02923 z) =
      pb_STR02916 1 (-(2 * Real.pi / 3)) (chartU_STR02924 ψ h z) := by
    funext s
    simp only [pb_STR02916, one_mul, ← sub_eq_add_neg]
    change h * rot_STR02923 z 0 * Real.cos s + h * rot_STR02923 z 1 * Real.sin s +
      ((ψ (ptPar_STR02923 h (rot_STR02923 z)) : E_STR02969) : PeriodicC2_STR02969).val s =
      h * z 0 * Real.cos (s - 2 * Real.pi / 3) +
        h * z 1 * Real.sin (s - 2 * Real.pi / 3) +
        ((ψ (ptPar_STR02923 h z) : E_STR02969) : PeriodicC2_STR02969).val
          (s - 2 * Real.pi / 3)
    rw [ptPar_rot_STR02923, hrot _ hp]
    change h * (z 0 * Real.cos (2 * Real.pi / 3) - z 1 * Real.sin (2 * Real.pi / 3)) *
      Real.cos s + h * (z 0 * Real.sin (2 * Real.pi / 3) + z 1 * Real.cos (2 * Real.pi / 3)) *
      Real.sin s + _ = _
    rw [Real.cos_sub, Real.sin_sub]
    ring
  rw [he]
  simpa [pb_STR02916, sub_eq_add_neg] using congrFun
    (rho_pb_STR02921 (symOK_rot_STR02921 1) h (chartU_isC2_STR02924 ψ h z).1) t

/-- A local graph comparison transfers rotation to the supplied three branches. -/
theorem rotations_of_data_STR029CLOSEB
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {η : ℝ} {Z : Fin 3 → ℝ → Fin 3 → ℝ}
    (hUo : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U)
    (hVo : IsOpen V) (hV0 : (0 : E_STR02969) ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hη : 0 < η) (hZC : ∀ j, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η))
    (hZrot : ∀ h ∈ Set.Ioo (-η) η,
      Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∀ h ∈ Set.Ioo (-δ) δ, ∀ t : ℝ,
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 1 h)) t =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 2 * Real.pi / 3) ∧
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 2 h)) t =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 4 * Real.pi / 3) := by
  obtain ⟨U1, V1, ψ1, hU1o, h0U1, _, _, hcd1, hψ01, hψV1, hiff1,
    _, _, _, _, _, hpsiRot, _, _, _, _, _, _, _, _⟩ :=
    str029_21_equivariance_unique_range_graph
  let W := U ∩ (U1 ∩ ψ1 ⁻¹' V)
  have hWo : IsOpen W := hUo.inter (hcd1.continuousOn.isOpen_inter_preimage hU1o hVo)
  have hW0 : (0 : Par_STR02916) ∈ W := ⟨hU0, h0U1, by simpa [hψ01] using hV0⟩
  have hagree : ∀ p ∈ W, ψ p = ψ1 p := by
    intro p hp
    exact ((hR p hp.1 _ hp.2.2).mp ((hiff1 p hp.2.1 _ (hψV1 p hp.2.1)).mpr rfl)).symm
  obtain ⟨ε, hε, hmem⟩ := eventually_param_mem_STR02967 hWo hW0 hη hZC
  let δ := min ε η
  have hδε : δ ≤ ε := min_le_left _ _
  have hδη : δ ≤ η := min_le_right _ _
  refine ⟨δ, lt_min hε hη, hδη, fun h hh => ?_⟩
  have hhε : h ∈ Set.Ioo (-ε) ε := Set.Ioo_subset_Ioo (neg_le_neg hδε) hδε hh
  have hhη : h ∈ Set.Ioo (-η) η := Set.Ioo_subset_Ioo (neg_le_neg hδη) hδη hh
  have hψeq : ∀ j : Fin 3, chartU_STR02924 ψ h (Z j h) = chartU_STR02924 ψ1 h (Z j h) := by
    intro j
    unfold chartU_STR02924
    rw [hagree _ (hmem j h hhε)]
  have hr : ∀ j : Fin 3, ∀ t : ℝ,
      rhoT_STR02901 h (chartU_STR02924 ψ1 h (rot_STR02923 (Z j h))) t =
        rhoT_STR02901 h (chartU_STR02924 ψ1 h (Z j h)) (t - 2 * Real.pi / 3) := by
    intro j t
    apply rho_rotation_STR029CLOSEB (fun p hp s => by simpa using hpsiRot 1 p hp s)
    exact (hmem j h hhε).2.1
  have hr1 : ∀ s : ℝ, rhoT_STR02901 h (chartU_STR02924 ψ1 h (Z 1 h)) s =
      rhoT_STR02901 h (chartU_STR02924 ψ1 h (Z 0 h)) (s - 2 * Real.pi / 3) := by
    intro s
    rw [(hZrot h hhη).1]
    exact hr 0 s
  intro t
  simp only [hψeq]
  refine ⟨hr1 t, ?_⟩
  rw [(hZrot h hhη).2, hr 1 t, hr1]
  congr 1
  ring

end DGPS.Frontier.STR029

open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The canonical physical ordinary LSI rate, the actual optimizing densities,
and their entropy and fixed-spatial-order logarithmic expansions. -/
theorem threefold_ordinaryRate_expansion :
    ∃ (ψ : Par_STR02916 → E_STR02969) (Z : Fin 3 → ℝ → Fin 3 → ℝ)
      (δ C : ℝ), 0 < δ ∧ 0 ≤ C ∧
      (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
        (∀ t : ℝ, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
        ContDiff ℝ ∞ (rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)))) ∧
      (∀ h ∈ Set.Ioo (-δ) δ, ∀ t : ℝ,
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 1 h)) t =
          rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 2 * Real.pi / 3) ∧
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 2 h)) t =
          rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 4 * Real.pi / 3)) ∧
      (∀ h ∈ Set.Ioo (-δ) δ, ∀ t : ℝ,
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (-t) =
          rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) t) ∧
      (∀ h : ℝ, 0 < h → h < δ →
        ordinaryLSRate (ordinaryReference h) ≠ ⊤ ∧
        |(ordinaryLSRate (ordinaryReference h)).toReal -
          DGPS.Circle.AngularNormalization.a0 * (1 - 16 * h ^ 2 / 15)| ≤ C * h ^ 4 ∧
        ∃ ρ : Fin 3 → AbsoluteDensity 1,
          (∀ (j : Fin 3) (θ : AngCircle), (ρ j).density (angEquiv.symm θ) =
            rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ)) ∧
          (∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j)) ∧
          (∀ j : Fin 3, str025_quot h (ρ j) = ordinaryLSRate (ordinaryReference h)) ∧
          (∀ j : Fin 3,
            |(ordinaryEntropy h (ρ j)).toReal - h ^ 2| ≤ C * h ^ 4) ∧
          (∀ (j : Fin 3) (σ : AbsoluteDensity 1), 0 < ordinaryEntropy h σ →
            str025_quot h (ρ j) ≤ str025_quot h σ) ∧
          (∀ i j : Fin 3, i ≠ j → ¬ (ρ i).density =ᵐ[haar 1] (ρ j).density) ∧
          (∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
            (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
              str025_quot h σ ≤ str025_quot h τ) →
            ∃ j : Fin 3, σ.density =ᵐ[haar 1] (ρ j).density) ∧
          (∀ j : Fin 3, (densityMeasure (ρ j) : Measure (Torus 1)) ≠ threefoldReference h) ∧
          (∀ ν : Measure (Torus 1), ZeroDeficit_STR02901 h
            (ordinaryLSRate (ordinaryReference h)).toReal ν ↔
              ν = threefoldReference h ∨ ∃ j : Fin 3,
                ν = (densityMeasure (ρ j) : Measure (Torus 1)))) ∧
      (∀ k : ℕ, ∀ d : ℝ, 0 ≤ d → d < δ →
        ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ h : ℝ, |h| ≤ d →
          cmN_STR02966 k (logRemainder_STR02931 ψ (Z 0) h) ≤ Ck * |h| ^ 3) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo,
    hOmem, hEC, hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1,
    hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs, hKuniq,
    δ31, hδ31, hδ31η, hA, hB, hC, hD, hreg, hlog⟩ :=
    str029_31_required_logarithmic_density_expansion
  obtain ⟨δidentify, hδidentify, _, hidentify⟩ :=
    s5_radius_identification_STR02926 hUo hψC hψV hR hOo hOmem hEC hval
      hη hN0 hN1 hN2 hn0 hn1 hn2 hKuniq hVo hV0 hU0 hψ0
  have hsubη : Set.Ioo (-δ31) δ31 ⊆ Set.Ioo (-η) η :=
    Set.Ioo_subset_Ioo (neg_le_neg hδ31η) hδ31η
  obtain ⟨δ26, hδ26, hδ26δ31, _, hopt⟩ :=
    str029_26_exactly_three_global_positive_entropy_optimizers_of_data
      hδ31 hδidentify (fun h hh j hne => (hA h hh j).2.2 hne)
      (fun h hh j => hZs h (hsubη hh) j) hB hidentify
  obtain ⟨δ28, hδ28, _, C28, hC28, hexp⟩ :=
    str029_28_even_rate_entropy_expansions_of_data hUo hU0 hVo hV0 hψC
      hψ0 hψV hR hOo hOmem hEC hval hzero hη hn0 hsym hZC hZN hZrot hZs hKuniq
  obtain ⟨δ27, hδ27, _, hsymmetry⟩ :=
    str029_27_reflection_sign_symmetry_branches_of_data hUo hU0 hVo hV0 hR
      hOo hOmem hEC hval hzero hη hn0 hsym hZC hZN hKuniq
  obtain ⟨δrot, hδrot, _, hrotations⟩ :=
    rotations_of_data_STR029CLOSEB hUo hU0 hVo hV0 hR hη hZC hZrot
  let δ := min δ26 (min δ28 (min δ27 δrot))
  have hδ : 0 < δ := lt_min hδ26 (lt_min hδ28 (lt_min hδ27 hδrot))
  have hd26 : δ ≤ δ26 := min_le_left _ _
  have hd31 : δ ≤ δ31 := hd26.trans hδ26δ31
  have hd28 : δ ≤ δ28 := (min_le_right _ _).trans (min_le_left _ _)
  have hd27 : δ ≤ δ27 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdrot : δ ≤ δrot := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hs31 : Set.Ioo (-δ) δ ⊆ Set.Ioo (-δ31) δ31 :=
    Set.Ioo_subset_Ioo (neg_le_neg hd31) hd31
  have hs28 : Set.Ioo (-δ) δ ⊆ Set.Ioo (-δ28) δ28 :=
    Set.Ioo_subset_Ioo (neg_le_neg hd28) hd28
  have hs27 : Set.Ioo (-δ) δ ⊆ Set.Ioo (-δ27) δ27 :=
    Set.Ioo_subset_Ioo (neg_le_neg hd27) hd27
  have hsmooth : ∀ h ∈ Set.Ioo (-δ31) δ31, ∀ j : Fin 3,
      ContDiff ℝ ∞ (rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) := by
    apply branches_contDiff_STR02929
    intro j k
    obtain ⟨Uα, _, _, hk⟩ := hreg j
    obtain ⟨W, _, hv, _, _⟩ := hk k
    exact ⟨W, hv⟩
  have ha0 : 0 ≤ DGPS.Circle.AngularNormalization.a0 := by
    unfold DGPS.Circle.AngularNormalization.a0
    positivity
  let C := max C28 (DGPS.Circle.AngularNormalization.a0 * C28)
  have hC0 : 0 ≤ C := hC28.trans (le_max_left _ _)
  refine ⟨ψ, Z, δ, C, hδ, hC0, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh j
    exact ⟨(hA h (hs31 hh) j).1, hsmooth h (hs31 hh) j⟩
  · intro h hh t
    exact hrotations h (Set.Ioo_subset_Ioo (neg_le_neg hdrot) hdrot hh) t
  · intro h hh t
    exact (hsymmetry h (hs27 hh)).1.2.2.2 t
  · intro h hh hd
    have hmem : h ∈ Set.Ioo (-δ) δ := ⟨by linarith, hd⟩
    have habs : |h| < δ26 := by rw [abs_of_pos hh]; exact hd.trans_le hd26
    obtain ⟨ρ, hρ, hpos, hquot, hmin, hdist, hall⟩ :=
      hopt h (by rwa [abs_of_pos hh]) habs
    have hcanonical : ∀ j : Fin 3,
        ordinaryLSRate (ordinaryReference h) = str025_quot h (ρ j) :=
      fun j => canonical_eq_quot_STR029CLOSEB h (ρ j) (hpos j) (hmin j)
    have hqnonneg : 0 ≤ 1 + h ^ 2 * Z 0 h 2 := by
      have hchart := (hA h (hs31 hmem) 0).2.2 (ne_of_gt hh)
      rw [← hchart.2]
      exact div_nonneg (fisherChart_nonneg_STR02962 h
        (chartU_isC2_STR02924 ψ h (Z 0 h)).2.1.continuous)
        (mul_nonneg (by norm_num) hchart.1.le)
    have hrate : (ordinaryLSRate (ordinaryReference h)).toReal =
        DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * Z 0 h 2) := by
      rw [hcanonical 0]
      change (ordinaryFisher h (ρ 0) / (2 * ordinaryEntropy h (ρ 0))).toReal = _
      rw [hquot 0, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0,
        ENNReal.toReal_ofReal hqnonneg]
    refine ⟨?_, ?_, ρ, hρ, hpos, fun j => (hcanonical j).symm, ?_, hmin, hdist, hall, ?_,
      str029_32_zero_deficit_roots_of_data h ρ hpos hmin hall⟩
    · rw [hcanonical 0]
      exact quot_ne_top_STR02932 h (ρ 0) (hpos 0)
    · rw [hrate]
      calc
        |DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * Z 0 h 2) -
            DGPS.Circle.AngularNormalization.a0 * (1 - 16 * h ^ 2 / 15)| =
            DGPS.Circle.AngularNormalization.a0 *
              |(1 + h ^ 2 * Z 0 h 2) - (1 - 16 * h ^ 2 / 15)| := by
                rw [← mul_sub, abs_mul, abs_of_nonneg ha0]
        _ ≤ DGPS.Circle.AngularNormalization.a0 * (C28 * h ^ 4) :=
          mul_le_mul_of_nonneg_left (hexp h (hs28 hmem) 0).1 ha0
        _ = (DGPS.Circle.AngularNormalization.a0 * C28) * h ^ 4 := by ring
        _ ≤ C * h ^ 4 := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    · intro j
      have hH := (s3b_chart_invariants_STR02926 h (chartU_isC2_STR02924 ψ h (Z j h))
        (ρ j) (Filter.Eventually.of_forall (hρ j))).1
      rw [hH, ENNReal.toReal_ofReal (le_of_lt ((hA h (hs31 hmem) j).2.2 (ne_of_gt hh)).1)]
      exact (hexp h (hs28 hmem) j).2.trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · intro j heq
      have hzero : ordinaryEntropy h (ρ j) = 0 := by
        unfold ordinaryEntropy
        rw [heq]
        exact relativeEntropy_self _
      exact (hpos j).ne' hzero
  · intro k d hd hdδ
    exact hlog k d hd (hdδ.trans_le hd31)

end DGPS.Examples.ThreeSpeciesCircle
