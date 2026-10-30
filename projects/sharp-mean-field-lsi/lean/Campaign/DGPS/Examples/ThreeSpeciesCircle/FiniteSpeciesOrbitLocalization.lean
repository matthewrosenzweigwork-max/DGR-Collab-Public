import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesActiveLocalization

/-! Actual orbit masses cannot approach a missing ordinary branch. The weight
lower bound is DERIVED from the genuine linear trial margin, coupling-uniform
positive gap and actual finite-moment correction transfer; it is not a premise. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem quadratic_coordinate_lower {α β : ℝ} (hα : 0 ≤ α)
    (hαu : α ≤ 5 / 4) (hβ : 7 ≤ β) (p : Fin 3 → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hm : threefoldMass p ≤ 1) (i : Fin 3) :
    -(β + 2 * α) * p i ≤ threefoldQuadratic α β p := by
  classical
  let q : Fin 3 → ℝ := fun j => if j = i then 0 else p j
  have hq : 0 ≤ threefoldQuadratic α β q :=
    (by positivity : (0 : ℝ) ≤ threefoldMass q ^ 2 / 2) |>.trans
      (threefoldQuadratic_binary_lower hβ hαu q ⟨i, by simp [q]⟩)
  have he : threefoldQuadratic α β p - threefoldQuadratic α β q =
      (β - α) * p i ^ 2 - (β + 2 * α) * p i * (threefoldMass p - p i) := by
    simp only [threefoldQuadratic, threefoldResultant_normSq, threefoldMass]
    fin_cases i <;> norm_num [q, Fin.sum_univ_three] <;> ring
  have hpos : 0 ≤ (β - α) * p i ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hK : 0 ≤ (β + 2 * α) * p i := mul_nonneg (by linarith) (hp i)
  have hcross := mul_le_mul_of_nonneg_left
    (show threefoldMass p - p i ≤ 1 by linarith [hp i]) hK
  nlinarith only [hq, he, hpos, hcross]

/-- Uniform grouped mass for ANY literal same-chart root assignment satisfying
its genuine original-H1 localization bound. The common constant K precedes all
couplings, families and assignments; this preserves the consumer's actual witness. -/
theorem elementaryModel_speciesRate_orbit_mass_lower_of_localization (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
        ∀ K : ℝ, 0 < K → ∃ η ε0 : ℝ, 0 < η ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
              0 < speciesGap (modelData h ε) F →
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
              ∀ label : Fin F.count → Fin 4,
                (∀ s, ordinaryRootH1Deviation
                  (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)) (F.density s)
                  (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)).sqrt ≤ K * ε) →
                ∀ j : Fin 3, η ≤ assignedOrbitWeights F label j := by
  obtain ⟨δT, hδT, hδTr, hTrial⟩ := elementaryModel_speciesRate_linear_trial_margin D
  obtain ⟨δG, hδG, _, hGap⟩ := elementaryModel_speciesRate_minimizer_uniform_gap D
  obtain ⟨δS, hδS, _, hSigns⟩ := ordinaryRoot_correction_coefficient_signs D
  let δ := min δT (min δG δS)
  refine ⟨δ, lt_min hδT (lt_min hδG hδS), (min_le_left _ _).trans hδTr,
    fun h hh hhd σ hσ K hK => ?_⟩
  have hhT : h < δT := hhd.trans_le (min_le_left _ _)
  have hhG : h < δG := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhS : h < δS := hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hhr : h < D.radius := hhT.trans_le hδTr
  obtain ⟨c, εT, hc, hεT, hεTmax, hmargin⟩ := hTrial h hh hhT
  obtain ⟨ηG, εG, hηG, hεG, _, hgap⟩ := hGap h hh hhG
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let α := ordinaryRootCorrectionAlpha h a σ
  let β := ordinaryRootCorrectionBeta h a σ
  obtain ⟨hα, hαu, hβ⟩ := hSigns h hh hhS σ hσ
  change 0 < α at hα
  change α < 5 / 4 at hαu
  change 7 < β at hβ
  have hcoef : 0 < β + 2 * α := by linarith
  obtain ⟨M, hM, hobs⟩ := elementaryCorrection_coordinates_bound h
  obtain ⟨L, hL, hLip⟩ := elementaryCorrection_moment_lipschitz h a
  let B := 2 * M * L * K
  have hB : 0 < B := by dsimp only [B]; positivity
  let η := (c * ηG) / (β + 2 * α)
  let ε0 := min εT (min εG ((c * ηG) / (B + 1)))
  have hε0 : 0 < ε0 := lt_min hεT
    (lt_min hεG (div_pos (mul_pos hc hηG) (by positivity)))
  refine ⟨η, ε0, div_pos (mul_pos hc hηG) hcoef, hε0,
    (min_le_left _ _).trans hεTmax, fun ε hε hεsmall b F hF hmin label hlabel => ?_⟩
  have heT : ε < εT := hεsmall.trans_le (min_le_left _ _)
  have heG : ε < εG := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heB : ε < (c * ηG) / (B + 1) := hεsmall.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have heMax : ε < epsMax h := heT.trans_le hεTmax
  classical
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ
  let S := assignedRootFamily F R label
  have hdist (s : Fin F.count) : rootDistanceSq (F.density s) (R (label s)) ≤ (K * ε) ^ 2 := by
    have hd := rootDistanceSq_le_originalH1 (R (label s)) (F.density s)
    have hs := hlabel s
    change ordinaryRootH1Deviation (R (label s)) (F.density s) (R (label s)).sqrt ≤ K * ε at hs
    have hx : 0 ≤ ordinaryRootH1Deviation (R (label s)) (F.density s) (R (label s)).sqrt :=
      add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    exact hd.trans ((sq_le_sq₀ hx (mul_pos hK hε).le).2 hs)
  have hbudget : rootDistanceBudget F R label ≤ (K * ε) ^ 2 := by
    unfold rootDistanceBudget
    calc _ ≤ ∑ s, F.weight s * (K * ε) ^ 2 :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hdist s) (F.weight_nonneg s)
      _ = _ := by rw [← Finset.sum_mul, F.weight_sum, one_mul]
  have hsqrt : Real.sqrt (rootDistanceBudget F R label) ≤ K * ε := by
    have he := Real.sqrt_le_sqrt hbudget
    simpa only [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos hK hε)] using he
  have hmom (i : Fin 6 ⊕ (Fin 3 × Fin 3)) :
      |(∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
        (∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure (barycenter S) : Measure (Torus 1)))| ≤
          2 * M * K * ε := by
    have hd := family_moment_error_le_root_budget F R label
      (continuous_elementaryCorrectionObservable h i) hM.le (hobs i)
    calc _ ≤ 2 * M * Real.sqrt (rootDistanceBudget F R label) := hd
      _ ≤ 2 * M * (K * ε) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = _ := by ring
  have herr : |elementaryC h a (barycenter F) - elementaryC h a (barycenter S)| ≤ B * ε := by
    have he := (hLip (barycenter F) (barycenter S) (2 * M * K * ε) (by positivity) hmom).1
    convert he using 1 <;> dsimp only [B] <;> ring
  have hr := (hmargin ε hε heT b).2
  change (speciesRate (modelData h ε) b).toReal ≤ a - c * ε at hr
  have hGF : ηG ≤ (speciesGap (modelData h ε) F : ℝ) := hgap ε hε heG b F hF hmin
  obtain ⟨hD0, hJ, _, _, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε heMax b F
  have hz := elementaryModel_speciesRate_cost_eq_zero h ε b F hF hmin
  have hGr : 0 < (speciesGap (modelData h ε) F : ℝ) := hF
  have hrG := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2 * (speciesGap (modelData h ε) F : ℝ))
  have hηG' := mul_le_mul_of_nonneg_left hGF (by positivity : 0 ≤ 2 * c * ε)
  have hJ' := mul_nonneg (sq_nonneg ε) hJ
  have hCε : ε * elementaryC h a (barycenter F) ≤ -2 * c * ε * ηG := by
    change (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) = _ at hdef
    nlinarith only [hdef, hz, hD0, hJ', hrG, hηG']
  have hC : elementaryC h a (barycenter F) ≤ -2 * c * ηG := by
    apply (mul_le_mul_iff_right₀ hε).1
    convert hCε using 1 <;> ring
  have hεB : B * ε ≤ c * ηG := by
    have he := (lt_div_iff₀ (by positivity : 0 < B + 1)).1 heB
    nlinarith only [he, hε]
  have hassigned : elementaryC h a (barycenter S) ≤ -(c * ηG) := by
    have he := (abs_le.mp herr).1
    linarith only [he, hC, hεB]
  have hpoly := elementaryC_assigned_ordinary_roots D hh ⟨by linarith, hhr⟩ σ hσ a F label
  change elementaryC h a (barycenter S) =
    threefoldQuadratic α β (assignedOrbitWeights F label) at hpoly
  have hmass : threefoldMass (assignedOrbitWeights F label) ≤ 1 := by
    rw [assignedOrbitWeights_mass]
    unfold nonreferenceRootWeight
    calc
      _ ≤ ∑ s, F.weight s := by
        apply Finset.sum_le_sum
        intro s _
        split_ifs
        · exact F.weight_nonneg s
        · exact le_rfl
      _ = 1 := F.weight_sum
  intro j
  have hlo := quadratic_coordinate_lower hα.le hαu.le hβ.le (assignedOrbitWeights F label)
    (assignedOrbitWeights_nonneg F label) hmass j
  rw [← hpoly] at hlo
  apply (div_le_iff₀ hcoef).2
  change c * ηG ≤ assignedOrbitWeights F label j * (β + 2 * α)
  nlinarith only [hlo, hassigned]


/-- Every actual full-family minimizer assigns a uniformly positive TOTAL mass
to each of the three SAME ordinary branches, after genuine active localization.
No lower bound on individual weights or original species count is assumed. -/
theorem elementaryModel_speciesRate_orbit_mass_lower (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K η ε0 : ℝ, 0 < K ∧ 0 < η ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
              0 < speciesGap (modelData h ε) F →
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
                ∃ label : Fin F.count → Fin 4,
                  (∀ s, ordinaryRootH1Deviation
                    (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)) (F.density s)
                    (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label s)).sqrt ≤ K * ε ∧
                    (ordinaryFisher h (F.density s)).toReal -
                      2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                        (ordinaryEntropy h (F.density s)).toReal ≤ K * ε ^ 2) ∧
                  ∀ j : Fin 3, η ≤ assignedOrbitWeights F label j := by
  obtain ⟨δA, hδA, hδAr, hActive⟩ := elementaryModel_speciesRate_active_root_localization D
  obtain ⟨δU, hδU, _, hUniform⟩ := elementaryModel_speciesRate_orbit_mass_lower_of_localization D
  let δ := min δA δU
  refine ⟨δ, lt_min hδA hδU, (min_le_left _ _).trans hδAr, fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εA, hK, hεA, hεAmax, hlocal⟩ :=
    hActive h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨η, εU, hη, hεU, _, hmass⟩ :=
    hUniform h hh (hhd.trans_le (min_le_right _ _)) σ hσ K hK
  refine ⟨σ, hσ, K, η, min εA εU, hK, hη, lt_min hεA hεU,
    (min_le_left _ _).trans hεAmax, fun ε hε hεsmall b F hF hmin => ?_⟩
  have heA : ε < εA := hεsmall.trans_le (min_le_left _ _)
  have heU : ε < εU := hεsmall.trans_le (min_le_right _ _)
  classical
  choose label hlabel using hlocal ε hε heA b F hF hmin
  exact ⟨label, hlabel, hmass ε hε heU b F hF hmin label (fun s => (hlabel s).1)⟩

end DGPS.Examples.ThreeSpeciesCircle
