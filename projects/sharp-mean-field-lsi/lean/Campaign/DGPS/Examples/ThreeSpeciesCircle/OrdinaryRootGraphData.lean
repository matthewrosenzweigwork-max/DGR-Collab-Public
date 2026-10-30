import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundStateRoots

/-!
# Actual ordinary roots with the same retained range graph and rate parameter

This package is constructed once from the existing T31 and T26 producers. It retains
only proved ordinary-branch, graph, chart, and canonical-rate data. It contains no
Poincare gap, Hessian positivity, Schur identity, or interacting optimizer conclusion.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Same-witness ordinary data for subsequent full-form coercivity arguments. -/
structure OrdinaryRootGraphData where
  radius : ℝ
  radius_pos : 0 < radius
  U : Set Par_STR02916
  V : Set E_STR02969
  ψ : Par_STR02916 → E_STR02969
  openU : IsOpen U
  zero_memU : (0 : Par_STR02916) ∈ U
  openV : IsOpen V
  zero_memV : (0 : E_STR02969) ∈ V
  smoothψ : ContDiffOn ℝ ∞ ψ U
  zeroψ : ψ 0 = 0
  memψ : ∀ p ∈ U, ψ p ∈ V
  range_eq : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p
  O : Set (ℝ × (Fin 3 → ℝ))
  reduced : ℝ × (Fin 3 → ℝ) → ℝ
  openO : IsOpen O
  zero_memO : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O
  smooth_reduced : ContDiffOn ℝ ∞ reduced O
  reduced_value : ∀ h z, (h, z) ∈ O → h ≠ 0 →
    reduced (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4
  reduced_zero : ∀ z : Fin 3 → ℝ, reduced ((0 : ℝ), z) =
    Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)
  Z : Fin 3 → ℝ → Fin 3 → ℝ
  smoothZ : ∀ j, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-radius) radius)
  Z_zero : Z 0 0 = ![2, 0, -16 / 15]
  Z_rotation : ∀ h ∈ Set.Ioo (-radius) radius,
    Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)
  Z_rate_same : ∀ h ∈ Set.Ioo (-radius) radius, ∀ j : Fin 3, Z j h 2 = Z 0 h 2
  Z_critical : ∀ j, ∀ h ∈ Set.Ioo (-radius) radius, Kfun_STR02923 reduced (h, Z j h) = 0
  branch_memU : ∀ j, ∀ h ∈ Set.Ioo (-radius) radius, ptPar_STR02923 h (Z j h) ∈ U
  branch_memO : ∀ j, ∀ h ∈ Set.Ioo (-radius) radius, (h, Z j h) ∈ O
  chart_critical : ∀ h ∈ Set.Ioo (-radius) radius, ∀ j : Fin 3, ∀ t,
    gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0
  density_rotations : ∀ h ∈ Set.Ioo (-radius) radius, ∀ t : ℝ,
    rhoT_STR02901 h (chartU_STR02924 ψ h (Z 1 h)) t =
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 2 * Real.pi / 3) ∧
    rhoT_STR02901 h (chartU_STR02924 ψ h (Z 2 h)) t =
      rhoT_STR02901 h (chartU_STR02924 ψ h (Z 0 h)) (t - 4 * Real.pi / 3)
  log_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ radius →
    cmN_STR02966 0 (logRemainder_STR02931 ψ (Z 0) h) ≤ C * |h| ^ 3
  log_bound_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, |h| ≤ radius →
    cmN_STR02966 1 (logRemainder_STR02931 ψ (Z 0) h) ≤ C * |h| ^ 3
  roots : ∀ h : ℝ, 0 < h → h < radius →
    ∃ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (σ j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ)) ∧
      (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
      (∀ j, str025_quot h (σ j) = ordinaryLSRate (ordinaryReference h)) ∧
      (∀ j (τ : AbsoluteDensity 1), 0 < ordinaryEntropy h τ →
        str025_quot h (σ j) ≤ str025_quot h τ) ∧
      (∀ i j : Fin 3, i ≠ j → ¬ (σ i).density =ᵐ[haar 1] (σ j).density) ∧
      (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
        (∀ η : AbsoluteDensity 1, 0 < ordinaryEntropy h η → str025_quot h τ ≤ str025_quot h η) →
        ∃ j : Fin 3, τ.density =ᵐ[haar 1] (σ j).density) ∧
      ordinaryLSRate (ordinaryReference h) ≠ ⊤ ∧
      ∀ j : Fin 3, (ordinaryLSRate (ordinaryReference h)).toReal =
        DGPS.Circle.AngularNormalization.a0 * (1 + h ^ 2 * Z j h 2)

/-- The full retained package is supplied by the actual ordinary construction. -/
theorem exists_ordinaryRootGraphData : Nonempty OrdinaryRootGraphData := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo,
    hOmem, hEC, hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1,
    hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs, hKuniq,
    δ31, hδ31, hδ31η, hA, hB, hC, hD, hreg, hlog⟩ :=
    str029_31_required_logarithmic_density_expansion
  obtain ⟨δidentify, hδidentify, _, hidentify⟩ :=
    s5_radius_identification_STR02926 hUo hψC hψV hR hOo hOmem hEC hval
      hη hN0 hN1 hN2 hn0 hn1 hn2 hKuniq hVo hV0 hU0 hψ0
  have hs31 : Set.Ioo (-δ31) δ31 ⊆ Set.Ioo (-η) η :=
    Set.Ioo_subset_Ioo (neg_le_neg hδ31η) hδ31η
  obtain ⟨δ26, hδ26, hδ26δ31, _, hopt⟩ :=
    str029_26_exactly_three_global_positive_entropy_optimizers_of_data
      hδ31 hδidentify (fun h hh j hne => (hA h hh j).2.2 hne)
      (fun h hh j => hZs h (hs31 hh) j) hB hidentify
  obtain ⟨δrot, hδrot, _, hrotations⟩ :=
    rotations_of_data_STR029CLOSEB hUo hU0 hVo hV0 hR hη hZC hZrot
  obtain ⟨δU, hδU, hmemU⟩ := eventually_param_mem_STR02967 hUo hU0 hη hZC
  have hevO : ∀ j : Fin 3, ∀ᶠ h in 𝓝 (0 : ℝ), (h, Z j h) ∈ O := by
    intro j
    have hz : ContinuousAt (Z j) 0 :=
      (hZC j).continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hη)
    exact (continuousAt_id.prodMk hz).eventually_mem (hOo.mem_nhds (hOmem (Z j 0)))
  obtain ⟨δO, hδO, hmemO⟩ := Metric.eventually_nhds_iff.1 (Filter.eventually_all.2 hevO)
  obtain ⟨C0, hC0, hlog0⟩ := hlog 0 (δ31 / 2) (by linarith) (by linarith)
  obtain ⟨C1, hC1, hlog1⟩ := hlog 1 (δ31 / 2) (by linarith) (by linarith)
  let δ := min δ26 (min δrot (min δU (min δO (δ31 / 2))))
  have hδ : 0 < δ := lt_min hδ26 (lt_min hδrot (lt_min hδU (lt_min hδO (by linarith))))
  have hd26 : δ ≤ δ26 := min_le_left _ _
  have hdrot : δ ≤ δrot := (min_le_right _ _).trans (min_le_left _ _)
  have hdU : δ ≤ δU := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdO : δ ≤ δO := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hdhalf : δ ≤ δ31 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hd31 : δ ≤ δ31 := hdhalf.trans (by linarith)
  have hdη : δ ≤ η := hd31.trans hδ31η
  have hsη : Set.Ioo (-δ) δ ⊆ Set.Ioo (-η) η := Set.Ioo_subset_Ioo (neg_le_neg hdη) hdη
  have hsδ31 : Set.Ioo (-δ) δ ⊆ Set.Ioo (-δ31) δ31 :=
    Set.Ioo_subset_Ioo (neg_le_neg hd31) hd31
  have hz0 : (0 : ℝ) ∈ Set.Ioo (-η) η := by constructor <;> linarith
  have hbase := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
  change Kfun_STR02923 E ((0 : ℝ), (![2, 0, -16 / 15] : Fin 3 → ℝ)) = 0 at hbase
  have hZ00 : Z 0 0 = ![2, 0, -16 / 15] :=
    ((hKuniq 0 0 hz0 _ (mem_of_mem_nhds hn0)).mp hbase).symm
  refine ⟨{
    radius := δ
    radius_pos := hδ
    U := U
    V := V
    ψ := ψ
    openU := hUo
    zero_memU := hU0
    openV := hVo
    zero_memV := hV0
    smoothψ := hψC
    zeroψ := hψ0
    memψ := hψV
    range_eq := hR
    O := O
    reduced := E
    openO := hOo
    zero_memO := hOmem
    smooth_reduced := hEC
    reduced_value := hval
    reduced_zero := hzero
    Z := Z
    smoothZ := fun j => (hZC j).mono hsη
    Z_zero := hZ00
    Z_rotation := fun h hh => hZrot h (hsη hh)
    Z_rate_same := fun h hh j => hZs h (hsη hh) j
    Z_critical := fun j h hh => (hKuniq j h (hsη hh) _ (hZN j h (hsη hh))).mpr rfl
    branch_memU := fun j h hh => hmemU j h (Set.Ioo_subset_Ioo (neg_le_neg hdU) hdU hh)
    branch_memO := by
      intro j h hh
      apply hmemO _ j
      rw [Real.dist_eq, sub_zero]
      exact lt_of_lt_of_le (abs_lt.mpr hh) hdO
    chart_critical := fun h hh j => (hA h (hsδ31 hh) j).2.1
    density_rotations := fun h hh => hrotations h (Set.Ioo_subset_Ioo (neg_le_neg hdrot) hdrot hh)
    log_bound := ⟨C0, hC0, fun h hh => hlog0 h (hh.trans hdhalf)⟩
    log_bound_one := ⟨C1, hC1, fun h hh => hlog1 h (hh.trans hdhalf)⟩
    roots := ?_
  }⟩
  intro h hh hδh
  obtain ⟨σ, hσ, hpos, hquot, hmin, hdist, hall⟩ :=
    hopt h (by rw [abs_of_pos hh]; exact hh) (by rw [abs_of_pos hh]; exact hδh.trans_le hd26)
  have hcanonical : ∀ j, ordinaryLSRate (ordinaryReference h) = str025_quot h (σ j) :=
    fun j => canonical_eq_quot_STR029CLOSEB h (σ j) (hpos j) (hmin j)
  refine ⟨σ, hσ, hpos, fun j => (hcanonical j).symm, hmin, hdist, hall, ?_, ?_⟩
  · rw [hcanonical 0]
    exact quot_ne_top_STR02932 h (σ 0) (hpos 0)
  · intro j
    have hmem : h ∈ Set.Ioo (-δ31) δ31 :=
      hsδ31 ⟨by linarith, hδh⟩
    have hchart := (hA h hmem j).2.2 hh.ne'
    have ha : 0 ≤ 1 + h ^ 2 * Z j h 2 := by
      rw [← hchart.2]
      exact div_nonneg (fisherChart_nonneg_STR02962 h
        (chartU_isC2_STR02924 ψ h (Z j h)).2.1.continuous)
        (mul_nonneg (by norm_num) hchart.1.le)
    have ha0 : 0 ≤ DGPS.Circle.AngularNormalization.a0 := by
      unfold DGPS.Circle.AngularNormalization.a0
      positivity
    rw [hcanonical j]
    change (ordinaryFisher h (σ j) / (2 * ordinaryEntropy h (σ j))).toReal = _
    rw [hquot j, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal ha]

end DGPS.Examples.ThreeSpeciesCircle
