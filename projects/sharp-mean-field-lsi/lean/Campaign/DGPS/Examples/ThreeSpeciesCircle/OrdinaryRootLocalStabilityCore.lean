import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundState
import DGPS.Frontier.STR029.T43
import DGPS.Equilibrium.GaussianRate
import DGPS.Structural.SmallRateCircle

/-!
Local ordinary-deficit stability on the original absolute H1 domain. Nearness is measured
by the Haar H1 distance of the original root to its positive continuous representative.
Stored roots are only required to be nonnegative almost everywhere.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual original-root H1 deviation; the second root has the same stored weak gradient. -/
noncomputable def ordinaryRootH1Deviation (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ) : ℝ :=
  (eLpNorm (fun x => ρ.sqrt x - u x) 2 (haar 1)).toReal +
    (eLpNorm (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x -
      weakGradient σ.sqrt σ.sqrt_mem x) 2 (haar 1)).toReal

/-- Genuine one-dimensional H1 control gives the required a.e. bound on the SAME relative root. -/
theorem ordinaryRoot_relative_ae_near (σ ρ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) {m δ : ℝ} (hm : 0 < m)
    (hmu : ∀ x, m ≤ u x) (hδ : 0 ≤ δ)
    (hnear : ordinaryRootH1Deviation σ ρ u ≤ m * δ) :
    ∀ᵐ x ∂haar 1, |ρ.sqrt x / u x - 1| ≤ δ := by
  have hσ := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hurep (EventuallyEq.refl _ _)
  have hd : IsWeakGradient (fun x => ρ.sqrt x - u x)
      (fun x => weakGradient ρ.sqrt ρ.sqrt_mem x - weakGradient σ.sqrt σ.sqrt_mem x) := by
    have hh := (isWeakGradient_weakGradient ρ.sqrt_mem).add (hσ.smul (-1))
    exact hh.congr_ae (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
  obtain ⟨v, _, hvae, _, hvbound⟩ := exists_continuous_rep_one hd
  filter_upwards [hvae] with x hx
  have hb : |ρ.sqrt x - u x| ≤ m * δ := by
    rw [← hx]
    exact (hvbound x).trans hnear
  have he : ρ.sqrt x / u x - 1 = (ρ.sqrt x - u x) / u x := by
    field_simp [(hupos x).ne']
  rw [he, abs_div, abs_of_pos (hupos x)]
  apply (div_le_iff₀ (hupos x)).2
  calc
    _ ≤ m * δ := hb
    _ = δ * m := mul_comm _ _
    _ ≤ δ * u x := mul_le_mul_of_nonneg_left (hmu x) hδ

/-- T43's actual entropy Taylor estimate, extended to the full a.e. H1 representative class. -/
theorem ordinaryRoot_entropy_near_one (μ : ProbabilityMeasure (Torus 1))
    (f : WeakH1Test μ) (hnn : 0 ≤ᵐ[(μ : Measure (Torus 1))] f.fn)
    (hmass : ∫ x, f.fn x ^ 2 ∂(μ : Measure (Torus 1)) = 1) {δ : ℝ}
    (hnear : ∀ᵐ x ∂(μ : Measure (Torus 1)), |f.fn x - 1| ≤ δ) (hδ : δ ≤ 1 / 4) :
    (homogeneousEntropy (μ : Measure (Torus 1)) (fun x => f.fn x ^ 2)).toReal ≤
      (2 + 4 * δ) * weightedVariance μ f.fn := by
  obtain ⟨g, hgm, hgae⟩ := f.isWeak.memLp.aestronglyMeasurable
  have hg0 : 0 ≤ᵐ[(μ : Measure (Torus 1))] g := by
    filter_upwards [hnn, hgae] with x hx he
    rwa [← he]
  have hgn : ∫ x, g x ^ 2 ∂(μ : Measure (Torus 1)) = 1 := by
    calc
      _ = ∫ x, f.fn x ^ 2 ∂(μ : Measure (Torus 1)) := by
        apply integral_congr_ae
        filter_upwards [hgae] with x hx
        rw [hx]
      _ = 1 := hmass
  have hgc : ∀ᵐ x ∂(μ : Measure (Torus 1)), |g x - 1| ≤ δ := by
    filter_upwards [hnear, hgae] with x hx he
    rwa [← he]
  have hT := str029_43_entropy_expansion_relative_variance
    (μ : Measure (Torus 1)) g hgm.measurable hg0 hgn hgc hδ
  have hH : homogeneousEntropy (μ : Measure (Torus 1)) (fun x => g x ^ 2) =
      homogeneousEntropy (μ : Measure (Torus 1)) (fun x => f.fn x ^ 2) := by
    apply homogeneousEntropy_congr_ae
    filter_upwards [hgae] with x hx
    rw [hx]
  have hv : variance g (μ : Measure (Torus 1)) = weightedVariance μ f.fn := by
    rw [variance_eq_integral hgm.measurable.aemeasurable]
    have hm : (∫ x, g x ∂(μ : Measure (Torus 1))) = ∫ x, f.fn x ∂(μ : Measure (Torus 1)) :=
      integral_congr_ae hgae.symm
    rw [hm]
    apply integral_congr_ae
    filter_upwards [hgae] with x hx
    rw [hx]
  rw [hH, hv] at hT
  have hh := (abs_le.mp hT).2
  linarith

/-- Normalized nonnegative roots satisfy the genuine squared-distance/variance estimate. -/
theorem ordinaryRoot_sq_distance_le_variance (μ : ProbabilityMeasure (Torus 1))
    (f : WeakH1Test μ) (hnn : 0 ≤ᵐ[(μ : Measure (Torus 1))] f.fn)
    (hmass : ∫ x, f.fn x ^ 2 ∂(μ : Measure (Torus 1)) = 1) :
    (∫ x, (f.fn x - 1) ^ 2 ∂(μ : Measure (Torus 1))) ≤ 2 * weightedVariance μ f.fn := by
  let m := ∫ x, f.fn x ∂(μ : Measure (Torus 1))
  have hm0 : 0 ≤ m := integral_nonneg_of_ae hnn
  have hv : weightedVariance μ f.fn = 1 - m ^ 2 := by
    have hv := variance_eq_sub f.isWeak.memLp
    rw [variance_eq_integral f.isWeak.memLp.aestronglyMeasurable.aemeasurable] at hv
    change weightedVariance μ f.fn = _ at hv
    simpa only [Pi.pow_apply, hmass] using hv
  have hm1 : m ≤ 1 := by nlinarith [weightedVariance_nonneg μ f.fn]
  have hi := f.isWeak.memLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hd : (∫ x, (f.fn x - 1) ^ 2 ∂(μ : Measure (Torus 1))) = 2 - 2 * m := by
    have he : (fun x => (f.fn x - 1) ^ 2) = fun x => f.fn x ^ 2 - 2 * f.fn x + 1 := by
      funext x
      ring
    have hi1 := integral_add (f.isWeak.memLp.integrable_sq.sub (hi.const_mul 2))
      (integrable_const (1 : ℝ))
    have hi2 := integral_sub f.isWeak.memLp.integrable_sq (hi.const_mul 2)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at hi1 hi2
    rw [he, hi1, hi2, integral_const_mul, hmass]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    dsimp only [m]
    ring
  rw [hd, hv]
  nlinarith [mul_nonneg hm0 (sub_nonneg.mpr hm1)]

private theorem ordinaryRoot_dirichlet_real (μ : ProbabilityMeasure (Torus 1))
    (f : WeakH1Test μ) : dirichletEnergy μ f =
      ENNReal.ofReal (∫ x, (f.grad x 0) ^ 2 ∂(μ : Measure (Torus 1))) := by
  have hi := f.isWeak.memLp_grad.norm.integrable_sq
  have hn : ∀ z : Tangent 1, ‖z‖ ^ 2 = (z 0) ^ 2 := by
    intro z
    simp [EuclideanSpace.norm_sq_eq]
  unfold dirichletEnergy
  rw [ofReal_integral_eq_lintegral_ofReal (by simpa only [hn] using hi)
    (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hn]

/-- The real Poincare consequence, with its actual native full weighted H1 test. -/
theorem ordinaryRoot_poincare_real (μ : ProbabilityMeasure (Torus 1))
    {p : ℝ} (hp : 0 ≤ p) (hPC : ENNReal.ofReal p ≤ poincareRate μ) (f : WeakH1Test μ) :
    p * weightedVariance μ f.fn ≤ ∫ x, (f.grad x 0) ^ 2 ∂(μ : Measure (Torus 1)) := by
  have hE : 0 ≤ ∫ x, (f.grad x 0) ^ 2 ∂(μ : Measure (Torus 1)) :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases hv : 0 < weightedVariance μ f.fn
  · have hh := (le_poincareRate_iff_forall μ (ENNReal.ofReal p)).1 hPC f hv
    rw [ordinaryRoot_dirichlet_real, ← ENNReal.ofReal_mul hp] at hh
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hp (weightedVariance_nonneg μ f.fn)),
      ENNReal.toReal_ofReal hE] using hr
  · have hz : weightedVariance μ f.fn = 0 :=
      le_antisymm (le_of_not_gt hv) (weightedVariance_nonneg μ f.fn)
    simpa only [hz, mul_zero] using hE

/-- The positive continuous representative supplies a bounded positive reference with
exactly the actual root probability, even if its stored root differs on a null set. -/
theorem ordinaryRoot_boundedReference (σ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : Continuous u) (hupos : ∀ x, 0 < u x) (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ∃ P : BoundedPositiveReference 1,
      P.measure = (densityMeasure σ : Measure (Torus 1)) ∧ P.density = fun x => u x ^ 2 := by
  have huc := hu.pow 2
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty huc.continuousOn
  obtain ⟨x1, _, hx1⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty huc.continuousOn
  have hm : ∫ x, u x ^ 2 ∂haar 1 = 1 := by
    calc
      _ = ∫ x, σ.sqrt x ^ 2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hurep] with x hx
        rw [hx]
      _ = 1 := σ.mass_one
  let P : BoundedPositiveReference 1 :=
    { density := fun x => u x ^ 2
      measurable_density := huc.measurable
      lower := u x0 ^ 2
      upper := u x1 ^ 2
      lower_pos := sq_pos_of_pos (hupos x0)
      lower_le := Eventually.of_forall fun x => hx0 (Set.mem_univ x)
      le_upper := Eventually.of_forall fun x => hx1 (Set.mem_univ x)
      mass_one := hm }
  refine ⟨P, ?_, rfl⟩
  apply withDensity_congr_ae
  filter_upwards [hurep] with x hx
  change ENNReal.ofReal (u x ^ 2) = ENNReal.ofReal (σ.sqrt x ^ 2)
  rw [hx]

/-- All actual relative-root test data, including the exact probability and entropy
identification, are derived on the original absolute H1 domain. -/
theorem ordinaryRoot_relativeTest_data (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : Continuous u) (hupos : ∀ x, 0 < u x) (hurep : σ.sqrt =ᵐ[haar 1] u) :
    let w := fun x => ρ.sqrt x / u x
    let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
    ∃ f : WeakH1Test (densityMeasure σ), f.fn = w ∧ f.grad = weakGradient w hw ∧
      (∫ x, f.fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) = 1 ∧
      (0 ≤ᵐ[(densityMeasure σ : Measure (Torus 1))] f.fn) ∧
      relativeEntropy (densityMeasure ρ : Measure (Torus 1))
        (densityMeasure σ : Measure (Torus 1)) =
          homogeneousEntropy (densityMeasure σ : Measure (Torus 1)) (fun x => f.fn x ^ 2) := by
  let w := fun x => ρ.sqrt x / u x
  let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
  let G := weakGradient w hw
  have hW := isWeakGradient_weakGradient hw
  obtain ⟨P, hP, hPd⟩ := ordinaryRoot_boundedReference σ u hu hupos hurep
  let f : WeakH1Test (densityMeasure σ) :=
    { fn := w
      grad := G
      isWeak :=
        { memLp := by simpa only [hP] using P.memLp_measure_iff.mpr hW.memLp
          memLp_grad := by simpa only [hP] using P.memLp_measure_iff.mpr hW.memLp_grad
          integrable := hW.memLp.integrable (by norm_num)
          integrable_grad := hW.memLp_grad.integrable (by norm_num)
          ibp := hW.ibp } }
  have hμac : (densityMeasure σ : Measure (Torus 1)) ≪ haar 1 :=
    withDensity_absolutelyContinuous _ _
  have hnn : 0 ≤ᵐ[(densityMeasure σ : Measure (Torus 1))] w :=
    hμac.ae_le (ρ.sqrt_nonneg.mono fun x hx => div_nonneg hx (hupos x).le)
  have hmass : ∫ x, w x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) = 1 := by
    rw [Structural.budget_integral_densityMeasure]
    calc
      _ = ∫ x, ρ.sqrt x ^ 2 ∂haar 1 := by
        apply integral_congr_ae
        filter_upwards [hurep] with x hx
        dsimp only [w, AbsoluteDensity.density]
        rw [hx]
        field_simp [(hupos x).ne']
      _ = 1 := ρ.mass_one
  have hμ : (densityMeasure σ : Measure (Torus 1)) =
      (haar 1).withDensity (fun x => ENNReal.ofReal (u x ^ 2)) := by
    rw [← hP, BoundedPositiveReference.measure, hPd]
  have hwm : AEMeasurable (fun x => w x ^ 2) (haar 1) :=
    hW.memLp.aestronglyMeasurable.aemeasurable.pow_const 2
  have hν : (densityMeasure σ : Measure (Torus 1)).withDensity
      (fun x => ENNReal.ofReal (w x ^ 2)) = (densityMeasure ρ : Measure (Torus 1)) := by
    have hqm : AEMeasurable (fun x => ENNReal.ofReal (u x ^ 2)) (haar 1) :=
      (hu.measurable.pow_const 2).aemeasurable.ennreal_ofReal
    have hmul := withDensity_mul₀ (μ := haar 1)
      (f := fun x => ENNReal.ofReal (u x ^ 2))
      (g := fun x => ENNReal.ofReal (w x ^ 2)) hqm hwm.ennreal_ofReal
    rw [hμ, ← hmul, densityMeasure_coe]
    apply withDensity_congr_ae
    exact Eventually.of_forall fun x => by
      change ENNReal.ofReal (u x ^ 2) * ENNReal.ofReal (w x ^ 2) =
        ENNReal.ofReal (ρ.sqrt x ^ 2)
      rw [← ENNReal.ofReal_mul (sq_nonneg (u x))]
      congr 1
      dsimp only [w, AbsoluteDensity.density]
      field_simp [(hupos x).ne']
  have hH := relativeEntropy_withDensity (P := (densityMeasure σ : Measure (Torus 1)))
    (v := fun x => w x ^ 2) (Eventually.of_forall fun _ => sq_nonneg _)
    (f.isWeak.memLp.aestronglyMeasurable.aemeasurable.pow_const 2)
  rw [hν] at hH
  exact ⟨f, rfl, rfl, hmass, hnn, hH⟩

/-- Local ordinary deficit controls the actual relative-root energy. Constants depend
only on the fixed equality root and its genuine Poincare improvement, before the competitor. -/
theorem ordinaryRoot_local_deficit_stability (h : ℝ) (σ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h σ)
    (hmin : ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ → str025_quot h σ ≤ str025_quot h τ)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) (p : ℝ)
    (hap : (ordinaryLSRate (ordinaryReference h)).toReal < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure σ)) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation σ ρ u ≤ η →
      let w := fun x => ρ.sqrt x / u x
      let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
      c * ((∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1) ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hp : 0 < p := lt_of_le_of_lt ha hap
  let δ := min (1 / 4) ((p - a) / (4 * (a + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (sub_pos.mpr hap) (by positivity))
  have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
  have hδp : 4 * (a + 1) * δ ≤ p - a := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (a + 1))).mp
      (show δ ≤ (p - a) / (4 * (a + 1)) from min_le_right _ _)
    nlinarith
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  let m := u x0
  have hm : 0 < m := hupos x0
  let cE := 2 * (p - a) / p
  let c := 2 * (p - a) / (p + 2)
  have hc : 0 < c := div_pos (by linarith) (by linarith)
  refine ⟨m * δ, c, mul_pos hm hδ, hc, fun ρ hnear => ?_⟩
  let w := fun x => ρ.sqrt x / u x
  let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep
  obtain ⟨f, hfn, hfg, hmass, hnn, hH⟩ := ordinaryRoot_relativeTest_data σ ρ u hu hupos hurep
  have hclose : ∀ᵐ x ∂(densityMeasure σ : Measure (Torus 1)), |f.fn x - 1| ≤ δ := by
    rw [hfn]
    apply (withDensity_absolutelyContinuous (haar 1) _).ae_le
    exact ordinaryRoot_relative_ae_near σ ρ u hu hupos hurep hm
      (fun x => hx0 (Set.mem_univ x)) hδ.le hnear
  have hEnt := ordinaryRoot_entropy_near_one (densityMeasure σ) f hnn hmass hclose hδ4
  have hP := ordinaryRoot_poincare_real (densityMeasure σ) hp.le hPC f
  let E := ∫ x, (f.grad x 0) ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let V := weightedVariance (densityMeasure σ) f.fn
  have hV : 0 ≤ V := weightedVariance_nonneg _ _
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨hHfin, hGSI⟩ := ordinaryEquality_groundStateIdentity h σ hpos hmin u hu hupos hurep ρ
  have hEnergy : E = ∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1 := by
    dsimp only [E]
    rw [hfg, Structural.budget_integral_densityMeasure]
  let L := ∫ x, (f.fn x - 1) ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  have hDistance : L = ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1 := by
    dsimp only [L]
    rw [hfn, Structural.budget_integral_densityMeasure]
  change c * ((∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) +
    ∫ x, σ.density x * (w x - 1) ^ 2 ∂haar 1) ≤ _
  rw [hGSI, ← hEnergy, ← hDistance, hH]
  change c * (E + L) ≤ 4 * E - 2 * a * _
  have hcoef : 2 * a * (2 + 4 * δ) ≤ 2 * (p + a) := by nlinarith
  have hEV : p * V ≤ E := hP
  have hHV : (homogeneousEntropy (densityMeasure σ : Measure (Torus 1))
      (fun x => f.fn x ^ 2)).toReal ≤ (2 + 4 * δ) * V := hEnt
  have h1 := mul_le_mul_of_nonneg_left hHV (show 0 ≤ 2 * a from mul_nonneg (by norm_num) ha)
  have h2 := mul_le_mul_of_nonneg_right hcoef hV
  have hcE : cE * E = 4 * E - (2 * (p + a) / p) * E := by
    dsimp only [cE]
    field_simp [hp.ne']
    ring
  have h3 := mul_le_mul_of_nonneg_left hEV
    (div_nonneg (by linarith : 0 ≤ 2 * (p + a)) hp.le)
  have hcancel : (2 * (p + a) / p) * (p * V) = 2 * (p + a) * V := by
    field_simp [hp.ne']
  rw [hcancel] at h3
  have hDef : cE * E ≤ 4 * E - 2 * a *
      (homogeneousEntropy (densityMeasure σ : Measure (Torus 1))
        (fun x => f.fn x ^ 2)).toReal := by
    rw [hcE]
    linarith
  have hL0 := ordinaryRoot_sq_distance_le_variance (densityMeasure σ) f hnn hmass
  have hL : L ≤ 2 * E / p := by
    apply (le_div_iff₀ hp).2
    change L ≤ 2 * V at hL0
    nlinarith [mul_le_mul_of_nonneg_left hL0 hp.le]
  have hnorm := mul_le_mul_of_nonneg_left (add_le_add (le_refl E) hL) hc.le
  have heq : c * (E + 2 * E / p) = cE * E := by
    dsimp only [c, cE]
    field_simp [hp.ne', show p + 2 ≠ 0 by linarith]
  rw [heq] at hnorm
  exact hnorm.trans hDef

end DGPS.Examples.ThreeSpeciesCircle
