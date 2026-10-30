import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesMinimizerLocalization
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootEntropyDistance
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitMomentError

/-! Actual unweighted localization of each active species of a full-family minimizer.
A genuine half-weight split retains the full original weight in every correction;
full-rate cost nonnegativity includes zero-gap competitors. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem relative_fisher_self_zero (P : BoundedPositiveReference 1) :
    ordinaryRelativeFisher P.measure P = 0 := by
  have he : relativeSqrt P.measure P =ᵐ[haar 1] fun _ => (1 : ℝ) := by
    filter_upwards [P.haar_ac_measure.ae_le P.measure.rnDeriv_self] with x hx
    simp only [relativeSqrt, hx, ENNReal.toReal_one, Real.sqrt_one]
  have hG := (isWeakGradient_const (d := 1) (1 : ℝ)).congr_ae he.symm
    (Filter.EventuallyEq.refl _ _)
  rw [ordinaryRelativeFisher_eq (Measure.AbsolutelyContinuous.refl _) hG]
  simp

private theorem reference_deficit_zero (h : ℝ) :
    (ordinaryFisher h (ordinaryReferenceAbsolute h)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal *
        (ordinaryEntropy h (ordinaryReferenceAbsolute h)).toReal = 0 := by
  letI : IsProbabilityMeasure (threefoldReference h) := by
    rw [← ordinaryReference_measure h]
    infer_instance
  have hI : ordinaryFisher h (ordinaryReferenceAbsolute h) = 0 := by
    unfold ordinaryFisher
    rw [ordinaryReferenceAbsolute_measure]
    exact relative_fisher_self_zero (ordinaryReference h)
  have hH : ordinaryEntropy h (ordinaryReferenceAbsolute h) = 0 := by
    unfold ordinaryEntropy
    rw [ordinaryReferenceAbsolute_measure]
    exact relativeEntropy_self _
  rw [hI, hH]
  simp

private theorem same_roots_deficit_zero (D : OrdinaryRootGraphData) {h : ℝ}
    (hh : 0 < h) (hhr : h < D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) :
    ∀ j, (ordinaryFisher h (σ j)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (σ j)).toReal = 0 := by
  obtain ⟨τ, hτ, hτpos, hτq, _, _, _, _, _⟩ := D.roots h hh hhr
  intro j
  have hμ : (densityMeasure (σ j) : Measure (Torus 1)) = densityMeasure (τ j) := by
    apply (densityMeasure_eq_iff_STR02901 _ _).2
    refine Filter.Eventually.of_forall fun x => ?_
    have he := (hσ j (angEquiv x)).trans (hτ j (angEquiv x)).symm
    simpa only [angEquiv.symm_apply_apply] using he
  have hI : ordinaryFisher h (σ j) = ordinaryFisher h (τ j) := by unfold ordinaryFisher; rw [hμ]
  have hH : ordinaryEntropy h (σ j) = ordinaryEntropy h (τ j) := by unfold ordinaryEntropy; rw [hμ]
  rw [hI, hH]
  have he := congrArg ENNReal.toReal (hτq j)
  change (ordinaryFisher h (τ j) / (2 * ordinaryEntropy h (τ j))).toReal = _ at he
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at he
  have hp : 0 < (ordinaryEntropy h (τ j)).toReal :=
    ENNReal.toReal_pos (hτpos j).ne' (str025_entropy_ne_top h (τ j))
  have hm := (div_eq_iff (by positivity : (2 : ℝ) * (ordinaryEntropy h (τ j)).toReal ≠ 0)).1 he
  nlinarith only [hm]

private theorem four_roots_entropy_plane (D : OrdinaryRootGraphData) (h : ℝ)
    (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (i : Fin 4) (ρ : AbsoluteDensity 1),
      (ordinaryEntropy h (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)).toReal -
        (ordinaryEntropy h ρ).toReal ≤
          K * Real.sqrt (rootDistanceSq ρ (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)) := by
  letI : IsProbabilityMeasure (threefoldReference h) := by
    rw [← ordinaryReference_measure h]
    infer_instance
  have hi : ∀ i : Fin 4, ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1,
      (ordinaryEntropy h (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)).toReal ≤
        (ordinaryEntropy h ρ).toReal +
          K * Real.sqrt (rootDistanceSq ρ (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · refine ⟨1, one_pos, fun ρ => ?_⟩
      have hH : ordinaryEntropy h (ordinaryReferenceAbsolute h) = 0 := by
        unfold ordinaryEntropy
        rw [ordinaryReferenceAbsolute_measure]
        exact relativeEntropy_self _
      change (ordinaryEntropy h (ordinaryReferenceAbsolute h)).toReal ≤ _
      rw [hH, ENNReal.toReal_zero]
      positivity
    · obtain ⟨hc, hp⟩ := ordinaryRoot_density_continuous_positive D h σ hσ j
      exact ordinaryEntropy_positive_root_distance h (σ j) hc hp
  choose K hK hbound using hi
  let L := 1 + ∑ i, K i
  have hL : 0 < L := by
    exact add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => (hK i).le)
  refine ⟨L, hL, fun i ρ => ?_⟩
  have hs : K i ≤ L := by
    have he := Finset.single_le_sum (fun j _ => (hK j).le) (Finset.mem_univ i)
    dsimp [L]
    linarith
  have hb := hbound i ρ
  have hm := mul_le_mul_of_nonneg_right hs
    (Real.sqrt_nonneg (rootDistanceSq ρ
      (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)))
  linarith only [hb, hm]

private theorem split_gap_upper {h : ℝ} (hh : 0 < h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 < ε → ε < epsMax h →
      ∀ (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
        (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
        (speciesGap (modelData h ε) (finiteSpeciesSplit F s τ t ht ht1) : ℝ) -
          (speciesGap (modelData h ε) F : ℝ) ≤
          t * F.weight s * ((ordinaryEntropy h τ).toReal - (ordinaryEntropy h (F.density s)).toReal) +
            ε * K * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) := by
  obtain ⟨K0, hK0, h0⟩ := finiteSpeciesSplit_correction_error h 0
  obtain ⟨K1, hK1, h1⟩ := finiteSpeciesSplit_correction_error h 1
  refine ⟨K0 + K1, add_pos hK0 hK1, fun ε hε hεmax F s τ t ht ht1 => ?_⟩
  let S := finiteSpeciesSplit F s τ t ht ht1
  let A := (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ)
  have hA : 0 ≤ A := mul_nonneg (mul_pos ht (F.weight_pos s)).le (Real.sqrt_nonneg _)
  have hQ : |elementaryQ h (densityMeasure (barycenter S)) -
      elementaryQ h (densityMeasure (barycenter F))| ≤ (K0 + K1) * A := by
    have he : elementaryQ h (densityMeasure (barycenter S)) -
        elementaryQ h (densityMeasure (barycenter F)) =
          (elementaryC h 0 (barycenter S) - elementaryC h 0 (barycenter F)) -
            (elementaryC h 1 (barycenter S) - elementaryC h 1 (barycenter F)) := by
      unfold elementaryC
      ring
    rw [he]
    have hb0 := (h0 F s τ t ht ht1).1
    have hb1 := (h1 F s τ t ht ht1).1
    calc _ ≤ |elementaryC h 0 (barycenter S) - elementaryC h 0 (barycenter F)| +
        |elementaryC h 1 (barycenter S) - elementaryC h 1 (barycenter F)| := abs_sub _ _
      _ ≤ _ := by dsimp only [S, A] at *; nlinarith only [hb0, hb1]
  have hQup := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hQ) (half_pos hε).le
  have hE := finiteSpeciesSplit_weighted_statistic F s τ ht ht1
    (fun ρ => (ordinaryEntropy h ρ).toReal)
  have hGF := elementaryModel_speciesGap_expansion hh hε hεmax F
  have hGS := elementaryModel_speciesGap_expansion hh hε hεmax S
  have hpos := mul_nonneg (mul_nonneg hε.le (add_pos hK0 hK1).le) hA
  dsimp only [A, S] at *
  nlinarith only [hE, hGF, hGS, hQup, hpos]

private theorem active_distance_from_split {h ε c Ke KL : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h) (hε1 : ε ≤ 1)
    (hc : 0 < c) (hKe : 0 ≤ Ke) (hKL : 0 ≤ KL)
    (KC KG : ℝ) (hKC : 0 < KC) (hKG : 0 < KG)
    (hC : ∀ (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
      (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
      |elementaryC h (ordinaryLSRate (ordinaryReference h)).toReal
          (barycenter (finiteSpeciesSplit F s τ t ht ht1)) -
        elementaryC h (ordinaryLSRate (ordinaryReference h)).toReal (barycenter F)| ≤
        KC * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ) ∧
      |elementaryJ h (barycenter (finiteSpeciesSplit F s τ t ht ht1)) -
        elementaryJ h (barycenter F)| ≤
        KC * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ))
    (hGap : ∀ (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
      (t : ℝ) (ht : 0 < t) (ht1 : t < 1),
      (speciesGap (modelData h ε) (finiteSpeciesSplit F s τ t ht ht1) : ℝ) -
        (speciesGap (modelData h ε) F : ℝ) ≤
        t * F.weight s * ((ordinaryEntropy h τ).toReal - (ordinaryEntropy h (F.density s)).toReal) +
          ε * KG * (t * F.weight s) * Real.sqrt (rootDistanceSq (F.density s) τ))
    (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hF : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (hbelow : (speciesRate (modelData h ε) b).toReal ≤ (ordinaryLSRate (ordinaryReference h)).toReal)
    (hlinear : (ordinaryLSRate (ordinaryReference h)).toReal -
      (speciesRate (modelData h ε) b).toReal ≤ KL * ε)
    (s : Fin F.count) (τ : AbsoluteDensity 1) (x : ℝ) (hx : 0 ≤ x)
    (hroot : (ordinaryFisher h τ).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h τ).toReal = 0)
    (hcoerc : c * x ^ 2 ≤ (ordinaryFisher h (F.density s)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (F.density s)).toReal)
    (hdist : Real.sqrt (rootDistanceSq (F.density s) τ) ≤ x)
    (hentropy : (ordinaryEntropy h τ).toReal - (ordinaryEntropy h (F.density s)).toReal ≤ Ke * x) :
    x ≤ ((2 * KC + 2 * KL * (Ke + KG)) / c) * ε ∧
      (ordinaryFisher h (F.density s)).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (F.density s)).toReal ≤
          ε * (2 * KC + 2 * KL * (Ke + KG)) * x := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let r := (speciesRate (modelData h ε) b).toReal
  let S := finiteSpeciesSplit F s τ (1 / 2) (by norm_num) (by norm_num)
  let w := (1 / 2 : ℝ) * F.weight s
  have hw : 0 < w := mul_pos (by norm_num) (F.weight_pos s)
  let d := (ordinaryFisher h (F.density s)).toReal - 2 * a * (ordinaryEntropy h (F.density s)).toReal
  let D0 := ∑ i, F.weight i * ((ordinaryFisher h (F.density i)).toReal -
    2 * a * (ordinaryEntropy h (F.density i)).toReal)
  have hDsplit := finiteSpeciesSplit_weighted_statistic F s τ
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (fun ρ => (ordinaryFisher h ρ).toReal - 2 * a * (ordinaryEntropy h ρ).toReal)
  change (∑ i, S.weight i * ((ordinaryFisher h (S.density i)).toReal -
    2 * a * (ordinaryEntropy h (S.density i)).toReal)) = D0 + w * (_ - d) at hDsplit
  change (ordinaryFisher h τ).toReal - 2 * a * (ordinaryEntropy h τ).toReal = 0 at hroot
  rw [hroot] at hDsplit
  obtain ⟨_, _, _, _, hDF⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b F
  obtain ⟨_, _, _, _, hDS⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b S
  change (speciesDissipation (modelData h ε) b F).toReal -
    2 * a * (speciesGap (modelData h ε) F : ℝ) =
      D0 + ε * elementaryC h a (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) at hDF
  change (speciesDissipation (modelData h ε) b S).toReal -
    2 * a * (speciesGap (modelData h ε) S : ℝ) =
      (∑ i, S.weight i * ((ordinaryFisher h (S.density i)).toReal -
        2 * a * (ordinaryEntropy h (S.density i)).toReal)) +
          ε * elementaryC h a (barycenter S) + ε ^ 2 * elementaryJ h (barycenter S) at hDS
  rw [hDsplit] at hDS
  have hCostF := elementaryModel_speciesRate_cost_eq_zero h ε b F hF hmin
  have hCostS := elementaryModel_speciesRate_cost_nonneg h ε b S
  have hbase : w * d ≤
      ε * (elementaryC h a (barycenter S) - elementaryC h a (barycenter F)) +
        ε ^ 2 * (elementaryJ h (barycenter S) - elementaryJ h (barycenter F)) +
          2 * (a - r) * ((speciesGap (modelData h ε) S : ℝ) - (speciesGap (modelData h ε) F : ℝ)) := by
    change (speciesDissipation (modelData h ε) b F).toReal -
      2 * r * (speciesGap (modelData h ε) F : ℝ) = 0 at hCostF
    change 0 ≤ (speciesDissipation (modelData h ε) b S).toReal -
      2 * r * (speciesGap (modelData h ε) S : ℝ) at hCostS
    nlinarith only [hDF, hDS, hCostF, hCostS]
  obtain ⟨hCS, hJS⟩ := hC F s τ (1 / 2) (by norm_num) (by norm_num)
  have hmDist := mul_le_mul_of_nonneg_left hdist (mul_pos hKC hw).le
  have hCup : elementaryC h a (barycenter S) - elementaryC h a (barycenter F) ≤ KC * w * x :=
    (le_abs_self _ |>.trans hCS).trans hmDist
  have hJup : elementaryJ h (barycenter S) - elementaryJ h (barycenter F) ≤ KC * w * x :=
    (le_abs_self _ |>.trans hJS).trans hmDist
  have hGup : (speciesGap (modelData h ε) S : ℝ) - (speciesGap (modelData h ε) F : ℝ) ≤
      w * (Ke + KG) * x := by
    have hg := hGap F s τ (1 / 2) (by norm_num) (by norm_num)
    have he := mul_le_mul_of_nonneg_left hentropy hw.le
    have hd := mul_le_mul_of_nonneg_left hdist (mul_nonneg (mul_pos hε hKG).le hw.le)
    have hc' := mul_le_mul_of_nonneg_right hε1 (mul_nonneg (mul_pos hKG hw).le hx)
    change _ ≤ w * _ + ε * KG * w * Real.sqrt _ at hg
    nlinarith only [hg, he, hd, hc']
  have hratio : 0 ≤ a - r := sub_nonneg.mpr hbelow
  have hCε := mul_le_mul_of_nonneg_left hCup hε.le
  have hJε := mul_le_mul_of_nonneg_left hJup (sq_nonneg ε)
  have hJsmall := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hε1 hε.le) (mul_nonneg (mul_pos hKC hw).le hx)
  have hGε := mul_le_mul_of_nonneg_left hGup
    (show 0 ≤ (2 : ℝ) * (a - r) from mul_nonneg (by norm_num) hratio)
  have hGsmall := mul_le_mul_of_nonneg_right hlinear
    (show 0 ≤ 2 * (w * (Ke + KG) * x) by positivity)
  have hdup : w * d ≤ w * (ε * (2 * KC + 2 * KL * (Ke + KG)) * x) := by
    nlinarith only [hbase, hCε, hJε, hJsmall, hGε, hGsmall]
  have hd : d ≤ ε * (2 * KC + 2 * KL * (Ke + KG)) * x :=
    (mul_le_mul_iff_right₀ hw).1 hdup
  refine ⟨?_, hd⟩
  by_cases hx0 : x = 0
  · rw [hx0]
    positivity
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hc' : (c * x) * x ≤ (ε * (2 * KC + 2 * KL * (Ke + KG))) * x := by
    change c * x ^ 2 ≤ d at hcoerc
    nlinarith only [hcoerc, hd]
  have he := (mul_le_mul_iff_left₀ hxp).1 hc'
  calc
    x ≤ (ε * (2 * KC + 2 * KL * (Ke + KG))) / c :=
      (le_div_iff₀ hc).2 (by nlinarith only [he])
    _ = _ := by ring

/-- EVERY active species of EVERY actual full-family minimizer is uniformly
O(epsilon) close in the original Haar square-root H1 distance to the SAME four
actual ordinary roots. Constants precede all counts, positive weights and minimizers. -/
theorem elementaryModel_speciesRate_active_root_localization (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
              0 < speciesGap (modelData h ε) F →
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
              ∀ s : Fin F.count, ∃ i : Fin 4,
                ordinaryRootH1Deviation (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)
                  (F.density s) (Fin.cases (motive := fun _ => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i).sqrt ≤ K * ε ∧
                (ordinaryFisher h (F.density s)).toReal -
                  2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                    (ordinaryEntropy h (F.density s)).toReal ≤ K * ε ^ 2 := by
  obtain ⟨δG, hδG, hδGr, hGlobal⟩ := ordinaryDeficit_global_same_graph D
  obtain ⟨δT, hδT, hδTr, hTrial⟩ := elementaryModel_equalThird_trial D
  let δ := min δG δT
  refine ⟨δ, lt_min hδG hδT, (min_le_left _ _).trans hδGr, fun h hh hhd => ?_⟩
  have hhG : h < δG := hhd.trans_le (min_le_left _ _)
  have hhT : h < δT := hhd.trans_le (min_le_right _ _)
  have hhr : h < D.radius := hhG.trans_le hδGr
  obtain ⟨σ, hσ, c, hc, hglobal⟩ := hGlobal h hh hhG
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (ordinaryReferenceAbsolute h) σ
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨Ke, hKe, hEntropy⟩ := four_roots_entropy_plane D h σ hσ
  obtain ⟨KC, hKC, hCorrection⟩ := finiteSpeciesSplit_correction_error h a
  obtain ⟨KG, hKG, hGap⟩ := split_gap_upper hh
  obtain ⟨KL, εL, hKL, hεL, hεLmax, hLinear⟩ := elementaryModel_quotient_lower_ordinary_linear hh
  obtain ⟨FT, _, εT, hεT, hεTmax, hTrialBound⟩ := hTrial h hh hhT
  let ε0 := min εT (min εL 1)
  let A := 2 * KC + 2 * KL * (Ke + KG)
  let L := A / c
  let K := L + A * L + 1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hL : 0 < L := div_pos hA hc
  have hK : 0 < K := by dsimp only [K]; positivity
  have hLK : L ≤ K := by dsimp only [K]; nlinarith only [mul_pos hA hL]
  have hAK : A * L ≤ K := by dsimp only [K]; linarith only [hL]
  have hε0 : 0 < ε0 := lt_min hεT (lt_min hεL one_pos)
  have hmax : ε0 ≤ epsMax h := (min_le_right _ _).trans ((min_le_left _ _).trans hεLmax)
  refine ⟨σ, hσ, K, ε0, hK, hε0, hmax, fun ε hε hεsmall b F hF hmin s => ?_⟩
  have heT : ε < εT := hεsmall.trans_le (min_le_left _ _)
  have heL : ε < εL := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ε ≤ 1 := (hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hemax : ε < epsMax h := heL.trans_le hεLmax
  obtain ⟨hFTpos, hFTlt⟩ := hTrialBound ε hε heT b
  have hrlt : speciesRate (modelData h ε) b < ordinaryLSRate (ordinaryReference h) :=
    (speciesRate_le (modelData h ε) b FT hFTpos).trans_lt hFTlt
  have hrfin : speciesRate (modelData h ε) b ≠ ⊤ := (hrlt.trans_le le_top).ne
  obtain ⟨_, _, _, _, _, _, _, hOrdFin, _⟩ := D.roots h hh hhr
  have hbelow : (speciesRate (modelData h ε) b).toReal ≤ a :=
    ((ENNReal.toReal_lt_toReal hrfin hOrdFin).2 hrlt).le
  have hLin := hLinear ε hε heL b F hF
  rw [hmin] at hLin
  have hlinear : a - (speciesRate (modelData h ε) b).toReal ≤ KL * ε := by
    change a - KL * ε ≤ _ at hLin
    linarith
  obtain ⟨i, hi⟩ := ordinaryFourRootH1Distance_attained h σ (F.density s)
  let τ := R i
  let x := ordinaryRootH1Deviation τ (F.density s) τ.sqrt
  have hx : 0 ≤ x := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hcoerc : c * x ^ 2 ≤ (ordinaryFisher h (F.density s)).toReal -
      2 * a * (ordinaryEntropy h (F.density s)).toReal := by
    have he := hglobal (F.density s)
    rw [← hi] at he
    exact he
  have hdist : Real.sqrt (rootDistanceSq (F.density s) τ) ≤ x := by
    have he := Real.sqrt_le_sqrt (rootDistanceSq_le_originalH1 τ (F.density s))
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx] at he
    exact he
  have hentropy : (ordinaryEntropy h τ).toReal - (ordinaryEntropy h (F.density s)).toReal ≤ Ke * x :=
    (hEntropy i (F.density s)).trans (mul_le_mul_of_nonneg_left hdist hKe.le)
  have hroot : (ordinaryFisher h τ).toReal - 2 * a * (ordinaryEntropy h τ).toReal = 0 := by
    have hroots : ∀ j : Fin 4, (ordinaryFisher h (R j)).toReal -
        2 * a * (ordinaryEntropy h (R j)).toReal = 0 := by
      intro j
      refine Fin.cases (reference_deficit_zero h)
        (same_roots_deficit_zero D hh hhr σ hσ) j
    exact hroots i
  obtain ⟨hdistance, hdeficit⟩ :=
    active_distance_from_split hh hε hemax he1 hc hKe.le hKL.le KC KG hKC hKG
      hCorrection (hGap ε hε hemax) b F hF hmin hbelow hlinear s τ x hx hroot hcoerc hdist hentropy
  change x ≤ L * ε at hdistance
  change (ordinaryFisher h (F.density s)).toReal - 2 * a * (ordinaryEntropy h (F.density s)).toReal ≤
    ε * A * x at hdeficit
  refine ⟨i, hdistance.trans (mul_le_mul_of_nonneg_right hLK hε.le), ?_⟩
  calc
    (ordinaryFisher h (F.density s)).toReal - 2 * a * (ordinaryEntropy h (F.density s)).toReal ≤
        ε * A * x := hdeficit
    _ ≤ ε * A * (L * ε) := mul_le_mul_of_nonneg_left hdistance (mul_pos hε hA).le
    _ = (A * L) * ε ^ 2 := by ring
    _ ≤ K * ε ^ 2 := mul_le_mul_of_nonneg_right hAK (sq_nonneg ε)

/-- A genuine equal-third root competitor gives a fixed negative LINEAR coupling
margin for the FULL actual species rate. Constants precede coupling and drift. -/
theorem elementaryModel_speciesRate_linear_trial_margin (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ c ε0 : ℝ, 0 < c ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          speciesRate (modelData h ε) b ≠ ⊤ ∧
          (speciesRate (modelData h ε) b).toReal ≤
            (ordinaryLSRate (ordinaryReference h)).toReal - c * ε := by
  obtain ⟨δ, hδ, hδr, hsign⟩ := ordinaryRoot_correction_coefficient_signs D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  have hhr : h < D.radius := hhd.trans_le hδr
  obtain ⟨σ, hσ, hpos, _, _, _, _, _, _⟩ := D.roots h hh hhr
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let α := ordinaryRootCorrectionAlpha h a σ
  have hα : 0 < α := (hsign h hh hhd σ hσ).1
  let F := SpeciesFamily.uniform (3 : ℕ+) σ
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  have hE : 0 < E := by
    change 0 < ∑ s : Fin 3, (1 / 3 : ℝ) * (ordinaryEntropy h (σ s)).toReal
    have hH0 : 0 < (ordinaryEntropy h (σ 0)).toReal :=
      ENNReal.toReal_pos (hpos 0).ne' (str025_entropy_ne_top h (σ 0))
    have hs := Finset.single_le_sum
      (f := fun s : Fin 3 => (1 / 3 : ℝ) * (ordinaryEntropy h (σ s)).toReal)
      (fun s _ => mul_nonneg (by norm_num) ENNReal.toReal_nonneg) (Finset.mem_univ 0)
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 3) hH0).trans_le hs
  have hD0 : (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * a * (ordinaryEntropy h (F.density s)).toReal)) = 0 := by
    change (∑ s : Fin 3, (1 / 3 : ℝ) * ((ordinaryFisher h (σ s)).toReal -
      2 * a * (ordinaryEntropy h (σ s)).toReal)) = 0
    have hr := same_roots_deficit_zero D hh hhr σ hσ
    have hz (s : Fin 3) : (ordinaryFisher h (σ s)).toReal -
        2 * a * (ordinaryEntropy h (σ s)).toReal = 0 := by
      exact hr s
    simp_rw [hz]
    simp only [mul_zero, Finset.sum_const_zero]
  have hC : elementaryC h a (barycenter F) = -α := by
    have he := elementaryC_assigned_ordinary_roots D hh ⟨by linarith, hhr⟩ σ hσ a F
      (fun j : Fin 3 => j.succ)
    change elementaryC h a (barycenter F) = threefoldQuadratic
      (ordinaryRootCorrectionAlpha h a σ) (ordinaryRootCorrectionBeta h a σ)
        (assignedOrbitWeights F (fun j : Fin 3 => j.succ)) at he
    have hp : assignedOrbitWeights F (fun j : Fin 3 => j.succ) = fun _ => (1 / 3 : ℝ) := by
      funext j
      change (∑ x : Fin 3, if x.succ = j.succ then (1 / 3 : ℝ) else 0) = 1 / 3
      fin_cases j <;> norm_num [Fin.sum_univ_three]
    rw [hp, threefoldQuadratic_equal_thirds] at he
    exact he
  let J := elementaryJ h (barycenter F)
  have hJ : 0 ≤ J := elementaryJ_nonneg h (barycenter F)
  obtain ⟨εg, hεg, hεgmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let c := α / (6 * E)
  let ε0 := min εg (α / (2 * (J + 1)))
  have hc : 0 < c := div_pos hα (by positivity)
  refine ⟨c, ε0, hc, lt_min hεg (div_pos hα (by positivity)),
    (min_le_left _ _).trans hεgmax, fun ε hε hεsmall b => ?_⟩
  have heG : ε < εg := hεsmall.trans_le (min_le_left _ _)
  have heMax : ε < epsMax h := heG.trans_le hεgmax
  have hGp : 0 < speciesGap (modelData h ε) F := by
    change 0 < (speciesGap (modelData h ε) F : ℝ)
    have hg := (hgap ε hε heG F).1
    change (1 / 2 : ℝ) * E ≤ _ at hg
    linarith
  have hGr : 0 < (speciesGap (modelData h ε) F : ℝ) := hGp
  have hGu : 2 * (speciesGap (modelData h ε) F : ℝ) ≤ 3 * E := by
    have hg := (hgap ε hε heG F).2
    change _ ≤ (3 / 2 : ℝ) * E at hg
    linarith
  have hεJ : ε * J ≤ α / 2 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 2 * (J + 1))).1
      (hεsmall.trans_le (min_le_right _ _))
    nlinarith only [he, hε]
  obtain ⟨_, _, hDfin, _, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε heMax b F
  rw [hD0, hC] at hdef
  have hmargin : (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) ≤ -2 * c * ε *
        (speciesGap (modelData h ε) F : ℝ) := by
    have hεJ' := mul_le_mul_of_nonneg_left hεJ hε.le
    have hG' := mul_le_mul_of_nonneg_left hGu (mul_pos hc hε).le
    have hcE : c * (6 * E) = α := (div_mul_cancel₀ α (by positivity : (6 : ℝ) * E ≠ 0))
    have hscaled : α * ε / 2 = 3 * c * ε * E := by rw [← hcE]; ring
    nlinarith only [hdef, hεJ', hG', hscaled]
  have hQfin : speciesQuotient (modelData h ε) b F ≠ ⊤ := by
    unfold speciesQuotient
    exact ENNReal.div_ne_top hDfin (by positivity)
  have hrle := ENNReal.toReal_mono hQfin (speciesRate_le (modelData h ε) b F hGp)
  have hreal : (speciesQuotient (modelData h ε) b F).toReal ≤ a - c * ε := by
    unfold speciesQuotient
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * (speciesGap (modelData h ε) F : ℝ))).2
    nlinarith only [hmargin]
  exact ⟨ne_top_of_le_ne_top hQfin (speciesRate_le (modelData h ε) b F hGp), hrle.trans hreal⟩

/-- The true linear trial margin and quadratic-gap barrier give a positive gap
constant chosen BEFORE coupling and EVERY actual full-family minimizer. -/
theorem elementaryModel_speciesRate_minimizer_uniform_gap (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ η ε0 : ℝ, 0 < η ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
            0 < speciesGap (modelData h ε) F →
            speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
              η ≤ (speciesGap (modelData h ε) F : ℝ) := by
  obtain ⟨δB, hδB, hδBr, hBarrier⟩ := elementaryModel_family_deficit_quadratic_gap D
  obtain ⟨δT, hδT, hδTr, hTrial⟩ := elementaryModel_speciesRate_linear_trial_margin D
  let δ := min δB δT
  refine ⟨δ, lt_min hδB hδT, (min_le_left _ _).trans hδBr, fun h hh hhd => ?_⟩
  obtain ⟨B, εB, hB, hεB, hεBmax, hBound⟩ := hBarrier h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨c, εT, hc, hεT, hεTmax, hMargin⟩ := hTrial h hh (hhd.trans_le (min_le_right _ _))
  let η := c / (2 * B)
  let ε0 := min εB εT
  refine ⟨η, ε0, div_pos hc (by positivity), lt_min hεB hεT,
    (min_le_left _ _).trans hεBmax, fun ε hε hεsmall b F hF hmin => ?_⟩
  have heB : ε < εB := hεsmall.trans_le (min_le_left _ _)
  have heT : ε < εT := hεsmall.trans_le (min_le_right _ _)
  have hG : 0 < (speciesGap (modelData h ε) F : ℝ) := hF
  have hQ := elementaryModel_speciesRate_cost_eq_zero h ε b F hF hmin
  have hBnd := hBound ε hε heB b F
  have hr := (hMargin ε hε heT b).2
  have hm := mul_le_mul_of_nonneg_right hr (show 0 ≤ 2 * (speciesGap (modelData h ε) F : ℝ) by positivity)
  have he : (2 * ε * (speciesGap (modelData h ε) F : ℝ)) * c ≤
      (2 * ε * (speciesGap (modelData h ε) F : ℝ)) *
        (2 * B * (speciesGap (modelData h ε) F : ℝ)) := by
    nlinarith only [hQ, hBnd, hm]
  have hcG := (mul_le_mul_iff_right₀ (show 0 < 2 * ε * (speciesGap (modelData h ε) F : ℝ) by positivity)).1 he
  exact (div_le_iff₀ (show 0 < 2 * B by positivity)).2 (by nlinarith only [hcG])

end DGPS.Examples.ThreeSpeciesCircle
