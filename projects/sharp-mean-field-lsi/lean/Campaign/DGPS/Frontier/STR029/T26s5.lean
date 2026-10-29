import DGPS.Frontier.STR029.T26s4
import DGPS.Frontier.STR029.T25

/-!
# STR029.26-s5: uniform identification of optimizers with the local branches

STR029.25 places every optimizer in one of three bounded neighborhoods. A compact
tube simultaneously controls the reduced domain and the overlap of the two range
graphs. STR029.26-s4 then identifies the scaled chart point with a unique branch.

## R5 notes

This worker-authored bridge preserves the saved STR029.26 split statement. It is
not a frozen specification and remains subject to the external statement review.
The auxiliary neighborhoods are intersected with unit balls about their limiting
points; their three closed balls form the compact set used for the uniform radius.
Graph agreement uses membership in both parameter domains and in the second value
neighborhood, through Wset_STR02923 and psi_agree_STR02923.
-/

open scoped ContDiff
open Filter Topology
open DGPS.Analysis.PeriodicHolder
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

theorem s5_radius_identification_STR02926
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hgr : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hO : IsOpen O) (hO0 : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (hE : ContDiffOn ℝ ∞ E O)
    (hEf : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    {η : ℝ} (hη : 0 < η)
    {N : Fin 3 → Set (Fin 3 → ℝ)} {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    (hN0 : IsOpen (N 0)) (hN1 : IsOpen (N 1)) (hN2 : IsOpen (N 2))
    (hn0 : N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ))
    (hn1 : N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ))
    (hn2 : N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ))
    (hKuniq : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
      Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h)
    (hV : IsOpen V) (h0V : (0 : E_STR02969) ∈ V) (h0U : (0 : Par_STR02916) ∈ U)
    (hψ0 : ψ 0 = 0) :
    ∃ η₃ : ℝ, 0 < η₃ ∧ η₃ ≤ η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η₃ → ∀ ρ : AbsoluteDensity 1,
      0 < ordinaryEntropy h ρ →
      (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
        ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
          ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) →
      ∃ j : Fin 3, ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) (angSec θ) := by
  let p0 : Fin 3 → ℝ := ![2, 0, -16 / 15]
  let p1 : Fin 3 → ℝ := ![-1, Real.sqrt 3, -16 / 15]
  let p2 : Fin 3 → ℝ := ![-1, -Real.sqrt 3, -16 / 15]
  let vec : (ℝ × ℝ × ℝ) → (Fin 3 → ℝ) := fun p => ![p.1, p.2.1, p.2.2]
  have hvec : Continuous vec := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [vec] <;> fun_prop
  let M0 := vec ⁻¹' (N 0 ∩ Metric.ball p0 1)
  let M1 := vec ⁻¹' (N 1 ∩ Metric.ball p1 1)
  let M2 := vec ⁻¹' (N 2 ∩ Metric.ball p2 1)
  have hM0 : IsOpen M0 := (hN0.inter Metric.isOpen_ball).preimage hvec
  have hM1 : IsOpen M1 := (hN1.inter Metric.isOpen_ball).preimage hvec
  have hM2 : IsOpen M2 := (hN2.inter Metric.isOpen_ball).preimage hvec
  have hp0 : ((2 : ℝ), 0, -16 / 15) ∈ M0 :=
    ⟨mem_of_mem_nhds hn0, Metric.mem_ball_self (by norm_num)⟩
  have hp1 : ((-1 : ℝ), Real.sqrt 3, -16 / 15) ∈ M1 :=
    ⟨mem_of_mem_nhds hn1, Metric.mem_ball_self (by norm_num)⟩
  have hp2 : ((-1 : ℝ), -Real.sqrt 3, -16 / 15) ∈ M2 :=
    ⟨mem_of_mem_nhds hn2, Metric.mem_ball_self (by norm_num)⟩
  obtain ⟨U', V', ψ', hU', h0U', hV', h0V', hψ', hψ0', hψV', hgr', δ, hδ, hentry⟩ :=
    str029_25_uniform_neighborhood_entry_global_optimizers
      M0 M1 M2 hM0 hM1 hM2 hp0 hp1 hp2
  clear hψ' hψ0' hψV'
  let W := Wset_STR02923 U U' (V ∩ V') ψ
  have hW : IsOpen W :=
    (hψ.continuousOn.isOpen_inter_preimage hU (hV.inter hV')).inter hU'
  have h0W : (0 : Par_STR02916) ∈ W :=
    ⟨⟨h0U, by show ψ 0 ∈ V ∩ V'; rw [hψ0]; exact ⟨h0V, h0V'⟩⟩, h0U'⟩
  let K := Metric.closedBall p0 1 ∪ Metric.closedBall p1 1 ∪ Metric.closedBall p2 1
  have hK : IsCompact K :=
    ((isCompact_closedBall p0 1).union (isCompact_closedBall p1 1)).union (isCompact_closedBall p2 1)
  have hQ : IsOpen (Qset_STR02923 O W) := isOpen_Qset_STR02923 hO hW
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ Qset_STR02923 O W := by
    rintro ⟨h, z⟩ ⟨hh0, _⟩
    have hh0' : h = 0 := Set.mem_singleton_iff.1 hh0
    subst h
    refine ⟨hO0 z, ?_⟩
    change ptPar_STR02923 0 z ∈ W
    rw [ptPar_zero_STR02923]
    exact h0W
  obtain ⟨A, B, hA, _, h0A, hKB, hAB⟩ :=
    generalized_tube_lemma isCompact_singleton hK hQ hsub
  obtain ⟨ε, hε, hεA⟩ := Metric.isOpen_iff.1 hA 0 (h0A (Set.mem_singleton 0))
  refine ⟨min η (min δ ε), lt_min hη (lt_min hδ hε), min_le_left _ _, ?_⟩
  intro h hh hhsmall ρ hpos hopt
  have hhη : |h| < η := lt_of_lt_of_le hhsmall (min_le_left _ _)
  have hhδ : |h| < δ := lt_of_lt_of_le hhsmall ((min_le_right _ _).trans (min_le_left _ _))
  have hhε : |h| < ε := lt_of_lt_of_le hhsmall ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, b, w, hae, hC2, hInE, wE, hwE, hpU', hwEψ', _, hmem⟩ :=
    hentry h hh hhδ ρ hpos hopt
  let z : Fin 3 → ℝ := ![a / h, b / h, rateSTR02963 h ρ / h ^ 2]
  have hzentry : (z ∈ N 0 ∧ z ∈ Metric.ball p0 1) ∨
      (z ∈ N 1 ∧ z ∈ Metric.ball p1 1) ∨ (z ∈ N 2 ∧ z ∈ Metric.ball p2 1) := by
    rcases hmem with (hmem | hmem) | hmem
    · exact Or.inl hmem
    · exact Or.inr (Or.inl hmem)
    · exact Or.inr (Or.inr hmem)
  have hzK : z ∈ K := by
    rcases hzentry with hz | hz | hz
    · exact Or.inl (Or.inl (Metric.ball_subset_closedBall hz.2))
    · exact Or.inl (Or.inr (Metric.ball_subset_closedBall hz.2))
    · exact Or.inr (Metric.ball_subset_closedBall hz.2)
  have hzQ : (h, z) ∈ Qset_STR02923 O W := hAB ⟨hεA (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hhε), hKB hzK⟩
  have ha : h * z 0 = a := by dsimp [z]; field_simp [hh]
  have hb : h * z 1 = b := by dsimp [z]; field_simp [hh]
  have hr : h ^ 2 * z 2 = rateSTR02963 h ρ := by dsimp [z]; field_simp [hh]
  have hp : ptPar_STR02923 h z = (a, b, h, rateSTR02963 h ρ) := by
    unfold ptPar_STR02923
    rw [ha, hb, hr]
  have hpW : (a, b, h, rateSTR02963 h ρ) ∈ W := by
    rw [← hp]
    exact hzQ.2
  have hψeq := psi_agree_STR02923 hψV hgr hgr' hpW.1.1 hpW.1.2.2 hpU'
  have hwEψ : wE = ψ (a, b, h, rateSTR02963 h ρ) := hwEψ'.trans hψeq.symm
  have hzero : Kfun_STR02923 E (h, z) = 0 :=
    s4_kfun_zero_STR02926 hU hψ hψV hgr hO hE hEf h hh z hzQ.1
      (by rw [hp]; exact hpW.1.1) ρ hpos hopt a b w hae hC2 hInE wE hwE hwEψ rfl
  have hchart : chartU_STR02924 ψ h z = uT_STR02901 a b w := by
    unfold chartU_STR02924
    rw [ha, hb, hr, ← hwEψ, hwE]
  have hzN : ∃ j : Fin 3, z ∈ N j := by
    rcases hzentry with hz | hz | hz
    · exact ⟨0, hz.1⟩
    · exact ⟨1, hz.1⟩
    · exact ⟨2, hz.1⟩
  obtain ⟨j, hzj⟩ := hzN
  have hzZ : z = Z j h := (hKuniq j h (abs_lt.1 hhη) z hzj).1 hzero
  refine ⟨j, ?_⟩
  rw [← hzZ, hchart]
  exact hae

end DGPS.Frontier.STR029
