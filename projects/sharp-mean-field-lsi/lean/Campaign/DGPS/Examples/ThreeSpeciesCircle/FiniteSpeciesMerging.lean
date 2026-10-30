import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesWeightVariation
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensitySegmentJensen
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesReferenceExclusion

/-! Genuine family merging at fixed original positive weights. Replacing two
species by the same weighted density mixture preserves the barycenter; the
strict one-body comparison is supplied downstream by actual H1 segment calculus. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Replace the two indicated original laws by one actual mixture law, retaining
the original positive weights. Equal replacement labels may subsequently merge. -/
def finiteSpeciesMerge (F : SpeciesFamily 1) (i j : Fin F.count) (τ : AbsoluteDensity 1) :
    SpeciesFamily 1 := by
  classical
  exact { count := F.count
          weight := F.weight
          weight_pos := F.weight_pos
          weight_sum := F.weight_sum
          density := fun k => if k = i then τ else if k = j then τ else F.density k }

theorem finiteSpeciesMerge_statistic (F : SpeciesFamily 1) (i j : Fin F.count)
    (hij : i ≠ j) (τ : AbsoluteDensity 1) (L : AbsoluteDensity 1 → ℝ) :
    (∑ k, (finiteSpeciesMerge F i j τ).weight k * L ((finiteSpeciesMerge F i j τ).density k)) =
      (∑ k, F.weight k * L (F.density k)) +
        (F.weight i + F.weight j) * L τ - F.weight i * L (F.density i) -
          F.weight j * L (F.density j) := by
  classical
  have he (k : Fin F.count) : F.weight k *
      L (if k = i then τ else if k = j then τ else F.density k) =
        F.weight k * L (F.density k) +
          (if k = i then F.weight i * (L τ - L (F.density i)) else 0) +
          (if k = j then F.weight j * (L τ - L (F.density j)) else 0) := by
    by_cases hki : k = i
    · subst k
      simp only [ite_true, if_neg hij]
      ring
    · by_cases hkj : k = j
      · subst k
        simp only [if_neg hki, ite_true]
        ring
      · simp only [if_neg hki, if_neg hkj, add_zero]
  change (∑ k : Fin F.count, F.weight k *
    L (if k = i then τ else if k = j then τ else F.density k)) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The actual density segment has precisely the original convex-mixture moments. -/
theorem h1DensitySegment_moment (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (g : Torus 1 → ℝ) (hg : Continuous g) :
    (∫ x, g x ∂(densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht) : Measure (Torus 1))) =
      (1 - t) * (∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))) +
        t * (∫ x, g x ∂(densityMeasure σ : Measure (Torus 1))) := by
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
    Structural.budget_integral_densityMeasure]
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hiρ : Integrable (fun x => ρ.density x * g x) (haar 1) :=
    ρ.integrable_density.mul_bdd hg.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  have hiσ : Integrable (fun x => σ.density x * g x) (haar 1) :=
    σ.integrable_density.mul_bdd hg.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  have he : (fun x => (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x * g x) =ᵐ[haar 1]
      fun x => (1 - t) * (ρ.density x * g x) + t * (σ.density x * g x) := by
    filter_upwards [h1DensitySegment_density_ae ρ σ u v hu hv hup hvp hρ hσ t ht] with x hx
    rw [hx]
    ring
  rw [integral_congr_ae he, integral_add (hiρ.const_mul _) (hiσ.const_mul _),
    integral_const_mul, integral_const_mul]

/-- Exact pair-weight balance preserves EVERY actual continuous barycenter moment. -/
theorem finiteSpeciesMerge_moments (F : SpeciesFamily 1) (i j : Fin F.count)
    (hij : i ≠ j) (τ : AbsoluteDensity 1)
    (hτ : ∀ (g : Torus 1 → ℝ), Continuous g →
      (F.weight i + F.weight j) * (∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) =
        F.weight i * (∫ x, g x ∂(densityMeasure (F.density i) : Measure (Torus 1))) +
          F.weight j * (∫ x, g x ∂(densityMeasure (F.density j) : Measure (Torus 1))))
    (g : Torus 1 → ℝ) (hg : Continuous g) :
    (∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesMerge F i j τ)) : Measure (Torus 1))) =
      ∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
  rw [Structural.budget_integral_barycenter _ hg, Structural.budget_integral_barycenter _ hg,
    finiteSpeciesMerge_statistic F i j hij τ
      (fun ρ : AbsoluteDensity 1 => ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)))]
  rw [hτ g hg]
  ring

/-- Both changing-law corrections are preserved, with no frozen-force premise. -/
theorem finiteSpeciesMerge_corrections (h r : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count)
    (hij : i ≠ j) (τ : AbsoluteDensity 1)
    (hτ : ∀ (g : Torus 1 → ℝ), Continuous g →
      (F.weight i + F.weight j) * (∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) =
        F.weight i * (∫ x, g x ∂(densityMeasure (F.density i) : Measure (Torus 1))) +
          F.weight j * (∫ x, g x ∂(densityMeasure (F.density j) : Measure (Torus 1)))) :
    elementaryC h r (barycenter (finiteSpeciesMerge F i j τ)) = elementaryC h r (barycenter F) ∧
      elementaryJ h (barycenter (finiteSpeciesMerge F i j τ)) = elementaryJ h (barycenter F) := by
  obtain ⟨K, _, hLip⟩ := elementaryCorrection_moment_lipschitz h r
  have he := hLip (barycenter (finiteSpeciesMerge F i j τ)) (barycenter F) 0 le_rfl
    (fun k => by
      rw [finiteSpeciesMerge_moments F i j hij τ hτ _ (continuous_elementaryCorrectionObservable h k)]
      simp)
  constructor
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.1))
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.2))

private theorem family_cost_expansion {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1) (r : ℝ) :
    (speciesDissipation (modelData h ε) b F).toReal -
      2 * r * (speciesGap (modelData h ε) F : ℝ) =
        (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
          2 * r * (ordinaryEntropy h (F.density s)).toReal)) +
          ε * elementaryC h r (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) := by
  have hsum : (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * r * (ordinaryEntropy h (F.density s)).toReal)) =
      (∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal) -
        2 * r * (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [(elementaryModel_speciesDissipation_expansion h ε b F).2,
    elementaryModel_speciesGap_expansion hh hε hεmax F, hsum]
  unfold elementaryC
  ring


private theorem no_strict_merge {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (i j : Fin F.count) (hij : i ≠ j) (τ : AbsoluteDensity 1)
    (hτ : ∀ (g : Torus 1 → ℝ), Continuous g →
      (F.weight i + F.weight j) * (∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) =
        F.weight i * (∫ x, g x ∂(densityMeasure (F.density i) : Measure (Torus 1))) +
          F.weight j * (∫ x, g x ∂(densityMeasure (F.density j) : Measure (Torus 1))))
    (hstrict : let r := (speciesRate (modelData h ε) b).toReal
      (F.weight i + F.weight j) * ((ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal) <
        F.weight i * ((ordinaryFisher h (F.density i)).toReal - 2 * r * (ordinaryEntropy h (F.density i)).toReal) +
          F.weight j * ((ordinaryFisher h (F.density j)).toReal - 2 * r * (ordinaryEntropy h (F.density j)).toReal)) : False := by
  let r := (speciesRate (modelData h ε) b).toReal
  let L := fun ρ : AbsoluteDensity 1 =>
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal
  let S := finiteSpeciesMerge F i j τ
  have hs := finiteSpeciesMerge_statistic F i j hij τ L
  have hc := finiteSpeciesMerge_corrections h r F i j hij τ hτ
  have hf := family_cost_expansion hh hε hεmax b F r
  have hn := family_cost_expansion hh hε hεmax b S r
  rw [hc.1, hc.2] at hn
  have hz := elementaryModel_speciesRate_cost_eq_zero h ε b F hG hmin
  have hp := elementaryModel_speciesRate_cost_nonneg h ε b S
  change (speciesDissipation (modelData h ε) b F).toReal -
    2 * r * (speciesGap (modelData h ε) F : ℝ) = 0 at hz
  change 0 ≤ (speciesDissipation (modelData h ε) b S).toReal -
    2 * r * (speciesGap (modelData h ε) S : ℝ) at hp
  change (∑ k, S.weight k * L (S.density k)) =
    (∑ k, F.weight k * L (F.density k)) +
      (F.weight i + F.weight j) * L τ - F.weight i * L (F.density i) - F.weight j * L (F.density j) at hs
  change (F.weight i + F.weight j) * L τ < F.weight i * L (F.density i) + F.weight j * L (F.density j) at hstrict
  nlinarith only [hs, hc.1, hc.2, hf, hn, hz, hp, hstrict]

private theorem continuous_le_of_ae {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (he : f ≤ᵐ[haar 1] g) : ∀ x, f x ≤ g x := by
  have hm : (fun x => max (f x) (g x)) =ᵐ[haar 1] g :=
    he.mono fun x hx => max_eq_right hx
  have hp := MeasureTheory.Measure.eq_of_ae_eq hm (hf.max hg) hg
  intro x
  exact (le_max_left (f x) (g x)).trans_eq (congrFun hp x)

/-- Original weak H1 nearness gives actual positive continuous representatives
in one common pointwise density tube; stored null-set values are never used. -/
theorem ordinaryRoot_near_density_tube (ω : AbsoluteDensity 1) (w : Torus 1 → ℝ)
    (hw : Continuous w) (hwp : ∀ x, 0 < w x) (hω : ω.sqrt =ᵐ[haar 1] w)
    {q : ℝ} (hq : 0 < q) (hqu : q ≤ 1 / 4) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation ω ρ ω.sqrt ≤ η →
        ∃ v : Torus 1 → ℝ, Continuous v ∧ (∀ x, 0 < v x) ∧ ρ.sqrt =ᵐ[haar 1] v ∧
          (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ v x ^ 2) ∧
          (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) := by
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hw.continuousOn
  let m := w x0
  have hm : 0 < m := hwp x0
  refine ⟨m * q, mul_pos hm hq, fun ρ hnear => ?_⟩
  have hn : ordinaryRootH1Deviation ω ρ w ≤ m * q := by
    have he : ordinaryRootH1Deviation ω ρ ω.sqrt = ordinaryRootH1Deviation ω ρ w := by
      unfold ordinaryRootH1Deviation
      rw [eLpNorm_congr_ae (hω.mono fun x hx => by
        change ρ.sqrt x - ω.sqrt x = ρ.sqrt x - w x
        rw [hx])]
    rw [← he]
    exact hnear
  have hclose := ordinaryRoot_relative_ae_near ω ρ w hw hwp hω hm
    (fun x => hx0 (Set.mem_univ x)) hq.le hn
  obtain ⟨v, hv, hvae, _, _⟩ := exists_continuous_rep_one (isWeakGradient_weakGradient ρ.sqrt_mem)
  have hloAE : (fun x => (1 - q) * w x) ≤ᵐ[haar 1] v := by
    filter_upwards [hclose, hvae] with x hx he
    rw [he]
    exact (le_div_iff₀ (hwp x)).1 (by linarith only [(abs_le.mp hx).1])
  have hhiAE : v ≤ᵐ[haar 1] (fun x => (1 + q) * w x) := by
    filter_upwards [hclose, hvae] with x hx he
    rw [he]
    exact (div_le_iff₀ (hwp x)).1 (by linarith only [(abs_le.mp hx).2])
  have hlo := continuous_le_of_ae (hw.const_mul (1 - q)) hv hloAE
  have hhi := continuous_le_of_ae hv (hw.const_mul (1 + q)) hhiAE
  have hvp : ∀ x, 0 < v x := fun x =>
    (mul_pos (by linarith : 0 < 1 - q) (hwp x)).trans_le (hlo x)
  refine ⟨v, hv, hvp, hvae.symm, fun x => ?_, fun x => ?_⟩
  · calc _ = ((1 - q) * w x) ^ 2 := by ring
      _ ≤ v x ^ 2 := pow_le_pow_left₀ (mul_nonneg (by linarith) (hwp x).le) (hlo x) 2
  · calc _ ≤ ((1 + q) * w x) ^ 2 := pow_le_pow_left₀ (hvp x).le (hhi x) 2
      _ = _ := by ring

/-- Same-branch active species have identical ACTUAL laws. This preserves
arbitrary duplicate labels and makes no false cardinality assertion about them. -/
theorem elementaryModel_speciesRate_same_branch_law (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
              0 < speciesGap (modelData h ε) F →
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
              ∃ label : Fin F.count → Fin 3,
                (∀ s, ordinaryRootH1Deviation (σ (label s)) (F.density s) (σ (label s)).sqrt ≤ K * ε) ∧
                ∀ s t, label s = label t → densityMeasure (F.density s) = densityMeasure (F.density t) := by
  obtain ⟨δR, hδR, hδRr, hNonref⟩ := elementaryModel_speciesRate_active_nonreference_localization D
  obtain ⟨δJ, hδJ, _, hJensenFactory⟩ := ordinaryGraph_densitySegment_common_strictJensen D
  obtain ⟨δT, hδT, _, hTrial⟩ := elementaryModel_speciesRate_linear_trial_margin D
  let δ := min δR (min δJ δT)
  refine ⟨δ, lt_min hδR (lt_min hδJ hδT), (min_le_left _ _).trans hδRr,
    fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εR, hK, hεR, hεRmax, hlocal⟩ :=
    hNonref h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨w, q, hw, hwp, hrep, hq, hqu, hJensen⟩ :=
    hJensenFactory h hh (hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))) σ hσ
  obtain ⟨c, εT, hc, hεT, _, hmargin⟩ :=
    hTrial h hh (hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  classical
  choose η hη hTube using fun j : Fin 3 => ordinaryRoot_near_density_tube (σ j) (w j) (hw j) (hwp j) (hrep j) hq hqu
  let η0 := min (η 0) (min (η 1) (η 2))
  have hη0 : 0 < η0 := lt_min (hη 0) (lt_min (hη 1) (hη 2))
  have hηle (j : Fin 3) : η0 ≤ η j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let ε0 := min εR (min εT (η0 / (K + 1)))
  have hε0 : 0 < ε0 := lt_min hεR (lt_min hεT (div_pos hη0 (by positivity)))
  refine ⟨σ, hσ, K, ε0, hK, hε0, (min_le_left _ _).trans hεRmax,
    fun ε hε hεsmall b F hF hmin => ?_⟩
  have heR : ε < εR := hεsmall.trans_le (min_le_left _ _)
  have heT : ε < εT := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heN : ε < η0 / (K + 1) := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hKε : K * ε ≤ η0 := by
    have he := (lt_div_iff₀ (by positivity : 0 < K + 1)).1 heN
    nlinarith only [he, hε]
  have heMax : ε < epsMax h := heR.trans_le hεRmax
  choose label hlabel using hlocal ε hε heR b F hF hmin
  have hpos (s : Fin F.count) := hTube (label s) (F.density s)
    ((hlabel s).1.trans (hKε.trans (hηle (label s))))
  choose v hv hvp hvrep hvlo hvhi using hpos
  refine ⟨label, fun s => (hlabel s).1, fun s t hst => ?_⟩
  by_contra hne
  have hstne : s ≠ t := by
    intro he
    apply hne
    rw [he]
  let r := (speciesRate (modelData h ε) b).toReal
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hra : r ≤ (ordinaryLSRate (ordinaryReference h)).toReal := by
    have he := (hmargin ε hε heT b).2
    change r ≤ (ordinaryLSRate (ordinaryReference h)).toReal - c * ε at he
    nlinarith only [he, mul_pos hc hε]
  let W := F.weight s + F.weight t
  have hW : 0 < W := add_pos (F.weight_pos s) (F.weight_pos t)
  let θ := F.weight t / W
  have hθ : 0 < θ := div_pos (F.weight_pos t) hW
  have hθ1 : θ < 1 := (div_lt_one hW).2 (by dsimp only [W]; linarith [F.weight_pos s])
  let τ := h1DensitySegment (F.density s) (F.density t) (v s) (v t)
    (hv s) (hv t) (hvp s) (hvp t) (hvrep s) (hvrep t) θ ⟨hθ.le, hθ1.le⟩
  have hτ : ∀ (g : Torus 1 → ℝ), Continuous g →
      (F.weight s + F.weight t) * (∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) =
        F.weight s * (∫ x, g x ∂(densityMeasure (F.density s) : Measure (Torus 1))) +
          F.weight t * (∫ x, g x ∂(densityMeasure (F.density t) : Measure (Torus 1))) := by
    intro g hg
    rw [show (∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) = _ from
      h1DensitySegment_moment (F.density s) (F.density t) (v s) (v t)
        (hv s) (hv t) (hvp s) (hvp t) (hvrep s) (hvrep t) θ ⟨hθ.le, hθ1.le⟩ g hg]
    have hsum : F.weight s + F.weight t ≠ 0 := hW.ne'
    dsimp only [θ, W]
    field_simp [hsum]
    <;> ring
  have hj := hJensen r hr hra (label s) (F.density s) (F.density t) (v s) (v t)
    (hv s) (hv t) (hvp s) (hvp t) (hvrep s) (hvrep t) hne
    (hvlo s) (hvhi s) (by simpa only [hst] using hvlo t)
    (by simpa only [hst] using hvhi t) θ hθ hθ1
  have hstrict := mul_lt_mul_of_pos_left hj hW
  have hθW : W * θ = F.weight t := by
    dsimp only [θ]
    field_simp [hW.ne']
    <;> ring
  have hθW' : W * (1 - θ) = F.weight s := by
    have hsum : F.weight s + F.weight t ≠ 0 := hW.ne'
    dsimp only [θ, W]
    field_simp [hsum]
    <;> ring
  have hstrict' : W * ((ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal) <
      F.weight s * ((ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal) +
        F.weight t * ((ordinaryFisher h (F.density t)).toReal - 2 * r * (ordinaryEntropy h (F.density t)).toReal) := by
    change W * ((ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal) < _ at hstrict
    rw [mul_add, ← mul_assoc, hθW', ← mul_assoc, hθW] at hstrict
    exact hstrict
  exact no_strict_merge hh hε heMax b F hF hmin s t hstne τ hτ hstrict'

/-- The original count is at most three WHEN its actual laws are distinct.
Arbitrary repeated labels remain allowed in the original theorem domain. -/
theorem elementaryModel_speciesRate_distinct_count_le_three (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
            0 < speciesGap (modelData h ε) F →
            speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
            Function.Injective (fun s : Fin F.count => densityMeasure (F.density s)) →
              (F.count : ℕ) ≤ 3 := by
  obtain ⟨δ, hδ, hδr, hmerge⟩ := elementaryModel_speciesRate_same_branch_law D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, _, K, ε0, _, hε0, hε0max, hfamily⟩ := hmerge h hh hhd
  refine ⟨ε0, hε0, hε0max, fun ε hε hεsmall b F hF hmin hinj => ?_⟩
  obtain ⟨label, _, he⟩ := hfamily ε hε hεsmall b F hF hmin
  have hlabel : Function.Injective label := fun s t hst => hinj (he s t hst)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective label hlabel

end DGPS.Examples.ThreeSpeciesCircle
