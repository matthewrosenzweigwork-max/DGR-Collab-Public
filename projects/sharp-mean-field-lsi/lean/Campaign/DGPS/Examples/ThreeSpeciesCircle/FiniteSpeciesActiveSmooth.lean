import DGPS.Examples.ThreeSpeciesCircle.InteractingFixedFieldSmooth
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesAddition
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesActiveLocalization

/-! Every original active law of a full-family minimizer has a uniformly positive
smooth root representative. The reference is retained among all four nearby
ordinary roots, and the fixed-field minimum is derived by the addition argument. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem activeDeviation_change_rep (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ordinaryRootH1Deviation σ ρ σ.sqrt = ordinaryRootH1Deviation σ ρ u := by
  unfold ordinaryRootH1Deviation
  have he : (fun x => ρ.sqrt x - σ.sqrt x) =ᵐ[haar 1] fun x => ρ.sqrt x - u x :=
    hurep.mono fun x hx => by
      change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - u x
      rw [hx]
  rw [eLpNorm_congr_ae he]

/-- The positive lower bound precedes the coupling, drift, full original count,
all original positive weights, minimizer and active index. -/
theorem elementaryModel_speciesRate_active_positive_representative (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          0 < speciesGap (modelData h ε) F →
          speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
          ∀ s : Fin F.count, ∃ v : Torus 1 → ℝ, Continuous v ∧
            (F.density s).sqrt =ᵐ[haar 1] v ∧ ∀ x, m ≤ v x := by
  classical
  obtain ⟨δ, hδ, hδr, hlocal⟩ := elementaryModel_speciesRate_active_root_localization D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εL, hK, hεL, hεLmax, hloc⟩ := hlocal h hh hhd
  choose us hus hups hreps using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (ordinaryReferenceAbsolute h) σ
  let u : Fin 4 → Torus 1 → ℝ := Fin.cases (str025_w h) us
  have hu : ∀ i : Fin 4, Continuous (u i) :=
    Fin.cases (str025_continuous_w h) hus
  have hup : ∀ i : Fin 4, ∀ x, 0 < u i x :=
    Fin.cases (str025_w_pos h) hups
  have hrep : ∀ i : Fin 4, (R i).sqrt =ᵐ[haar 1] u i :=
    Fin.cases (Eventually.of_forall fun _ => rfl) hreps
  choose ηs ms hηs hms hpositive using fun i =>
    ordinaryRoot_near_positive_representative (R i) (u i) (hu i) (hup i) (hrep i)
  let η := min (ηs 0) (min (ηs 1) (min (ηs 2) (ηs 3)))
  let m := min (ms 0) (min (ms 1) (min (ms 2) (ms 3)))
  have hη : 0 < η := lt_min (hηs 0) (lt_min (hηs 1) (lt_min (hηs 2) (hηs 3)))
  have hm : 0 < m := lt_min (hms 0) (lt_min (hms 1) (lt_min (hms 2) (hms 3)))
  have hηroot : ∀ i : Fin 4, η ≤ ηs i := by
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmroot : ∀ i : Fin 4, m ≤ ms i := by
    intro i
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨min εL (η / K), m, lt_min hεL (div_pos hη hK),
    (min_le_left _ _).trans hεLmax, hm, fun ε hε he b F hG hmin s => ?_⟩
  obtain ⟨i, hnear, _⟩ := hloc ε hε (he.trans_le (min_le_left _ _)) b F hG hmin s
  have heK : K * ε < η := by
    have ht := (lt_div_iff₀ hK).mp (he.trans_le (min_le_right _ _))
    nlinarith
  change ordinaryRootH1Deviation (R i) (F.density s) (R i).sqrt ≤ K * ε at hnear
  rw [activeDeviation_change_rep (R i) (F.density s) (u i) (hrep i)] at hnear
  obtain ⟨v, hv, hae, hvmin⟩ := hpositive i (F.density s)
    (hnear.trans (heK.le.trans (hηroot i)))
  exact ⟨v, hv, hae, fun x => (hmroot i).trans (hvmin x)⟩

/-- Every active species of an actual full-family minimizer has a positive
smooth representative. No smoothness, weak equation or individual scalar
minimality premise is imposed on the original family densities. -/
theorem elementaryModel_speciesRate_active_smooth (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          0 < speciesGap (modelData h ε) F →
          speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
          ∀ s : Fin F.count, ∃ v : Torus 1 → ℝ, Continuous v ∧
            (F.density s).sqrt =ᵐ[haar 1] v ∧ (∀ x, m ≤ v x) ∧
            IsSmoothPeriodic v ∧ IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  obtain ⟨δ, hδ, hδr, hpositive⟩ := elementaryModel_speciesRate_active_positive_representative D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨ε0, m, hε0, hεmax, hm, hp⟩ := hpositive h hh hhd
  refine ⟨ε0, m, hε0, hεmax, hm, fun ε hε he b F hG hmin s => ?_⟩
  obtain ⟨v, hv, hae, hvmin⟩ := hp ε hε he b F hG hmin s
  let r := (speciesRate (modelData h ε) b).toReal
  have hglobal := elementaryModel_speciesRate_active_global_minimum hh hε
    (he.trans_le hεmax) b F hG hmin s
  have hvalue := elementaryModel_speciesRate_common_value hh hε
    (he.trans_le hεmax) b F hG hmin s
  obtain ⟨S, _, _, _, hvsm, _, hlogsm⟩ := elementaryFixedField_globalMin_smooth
    h ε r (barycenter F) (F.density s) hglobal hvalue v hv hae (fun x => hm.trans_le (hvmin x))
  exact ⟨v, hv, hae, hvmin, hvsm, hlogsm⟩

end DGPS.Examples.ThreeSpeciesCircle
