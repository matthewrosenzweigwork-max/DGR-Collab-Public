import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootNormComparison
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferencePoincareGap

/-! Local deficit stability at the actual reference law, on the full original absolute
H1 domain. The reference root and all constants are fixed before the competitor. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual reference law in the original absolute square-root H1 carrier. -/
noncomputable def ordinaryReferenceAbsolute (h : ℝ) : AbsoluteDensity 1 where
  sqrt := str025_w h
  sqrt_mem := by
    have hw := RelativeFisher.mul_rpow_isWeakGradient (ordinaryReference_lip h)
      (r := (1 / 2 : ℝ)) (by norm_num) (isWeakGradient_const (d := 1) 1)
    rw [mem_H1Haar]
    have he : (fun x : Torus 1 => (1 : ℝ) * (ordinaryReference h).density x ^ (1 / 2 : ℝ)) =
        str025_w h := by
      funext x
      simp only [one_mul, str025_w, Real.sqrt_eq_rpow]
      rfl
    rw [← he]
    exact ⟨_, hw⟩
  sqrt_nonneg := Eventually.of_forall fun x => (str025_w_pos h x).le
  mass_one := str025_integral_w_sq h

/-- Exact law identification; the stored root is the positive continuous square root. -/
theorem ordinaryReferenceAbsolute_measure (h : ℝ) :
    (densityMeasure (ordinaryReferenceAbsolute h) : Measure (Torus 1)) = threefoldReference h := by
  rw [densityMeasure_coe]
  change (haar 1).withDensity (fun x => ENNReal.ofReal (str025_w h x ^ 2)) = _
  simp_rw [str025_w_sq]
  rfl

private theorem reference_dirichlet_real (μ : ProbabilityMeasure (Torus 1))
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

/-- The reference ground-state identity follows from the existing actual relative Fisher
formula. No optimizer or positive-entropy premise is required at the reference itself. -/
theorem ordinaryReference_groundStateIdentity (h : ℝ) (ρ : AbsoluteDensity 1) :
    let σ := ordinaryReferenceAbsolute h
    let u := str025_w h
    let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u (str025_continuous_w h)
      (str025_w_pos h) (EventuallyEq.refl _ _)
    (ordinaryFisher h ρ).toReal =
      4 * ∫ x, σ.density x * (weakGradient (fun y => ρ.sqrt y / u y) hw x 0) ^ 2 ∂haar 1 := by
  let σ := ordinaryReferenceAbsolute h
  let u := str025_w h
  let hw := ordinaryEquality_relativeRoot_memH1 σ ρ u (str025_continuous_w h)
    (str025_w_pos h) (EventuallyEq.refl _ _)
  have hW := isWeakGradient_weakGradient hw
  have he : str025_u h ρ = fun x => ρ.sqrt x / u x := funext (str025_u_eq h ρ)
  have hG := hW.ae_eq ((str025_isWeak h ρ).congr_ae
    (Eventually.of_forall fun x => congrFun he x) (EventuallyEq.refl _ _))
  have hμac : threefoldReference h ≪ haar 1 := (ordinaryReference h).measure_ac_haar
  have hi : (ordinaryFisher h ρ).toReal =
      4 * ∫ x, (str025_grad h ρ x 0) ^ 2 ∂threefoldReference h := by
    rw [str025_fisher_eq, reference_dirichlet_real, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    rfl
  rw [hi]
  congr 1
  calc
    _ = ∫ x, (weakGradient (fun y => ρ.sqrt y / u y) hw x 0) ^ 2 ∂threefoldReference h := by
      apply integral_congr_ae
      filter_upwards [hμac.ae_le hG] with x hx
      rw [hx]
    _ = ∫ x, σ.density x * (weakGradient (fun y => ρ.sqrt y / u y) hw x 0) ^ 2 ∂haar 1 := by
      rw [← ordinaryReferenceAbsolute_measure h, Structural.budget_integral_densityMeasure]

/-- Reference local coercivity in the relative-root H1 norm, with all analytic data
provided by the actual reference law. -/
theorem ordinaryReference_local_deficit_stability (h : ℝ) (p : ℝ)
    (hap : (ordinaryLSRate (ordinaryReference h)).toReal < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (str025_prob h)) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
      let w := fun x => ρ.sqrt x / str025_w h x
      let hw := ordinaryEquality_relativeRoot_memH1 (ordinaryReferenceAbsolute h) ρ
        (str025_w h) (str025_continuous_w h) (str025_w_pos h) (EventuallyEq.refl _ _)
      c * ((∫ x, (ordinaryReferenceAbsolute h).density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) +
        ∫ x, (ordinaryReferenceAbsolute h).density x * (w x - 1) ^ 2 ∂haar 1) ≤
          (ordinaryFisher h ρ).toReal - 2 * (ordinaryLSRate (ordinaryReference h)).toReal *
            (ordinaryEntropy h ρ).toReal := by
  let σ := ordinaryReferenceAbsolute h
  let u := str025_w h
  have hu := str025_continuous_w h
  have hupos := str025_w_pos h
  have hurep : σ.sqrt =ᵐ[haar 1] u := EventuallyEq.refl _ _
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
  have hprob : densityMeasure σ = str025_prob h := by
    apply Subtype.ext
    exact ordinaryReferenceAbsolute_measure h
  have hPC' : ENNReal.ofReal p ≤ poincareRate (densityMeasure σ) := by rwa [hprob]
  have hP := ordinaryRoot_poincare_real (densityMeasure σ) hp.le hPC' f
  let E := ∫ x, (f.grad x 0) ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
  let V := weightedVariance (densityMeasure σ) f.fn
  have hV : 0 ≤ V := weightedVariance_nonneg _ _
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hI := ordinaryReference_groundStateIdentity h ρ
  have hH0 : ordinaryEntropy h ρ = relativeEntropy (densityMeasure ρ : Measure (Torus 1))
      (densityMeasure σ : Measure (Torus 1)) := by
    rw [ordinaryReferenceAbsolute_measure]
    rfl
  have hGSI : (ordinaryFisher h ρ).toReal - 2 * a * (ordinaryEntropy h ρ).toReal =
      4 * (∫ x, σ.density x * (weakGradient w hw x 0) ^ 2 ∂haar 1) -
        2 * a * (relativeEntropy (densityMeasure ρ : Measure (Torus 1))
          (densityMeasure σ : Measure (Torus 1))).toReal := by
    rw [hI, hH0]
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

/-- Original Haar H1 local stability at the actual reference, with its real strict
Poincare improvement; the norm comparison is already proved, not assumed. -/
theorem ordinaryReference_localHaar_of_poincare (h : ℝ) (p : ℝ)
    (hap : (ordinaryLSRate (ordinaryReference h)).toReal < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (str025_prob h)) :
    ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
      c * ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ^ 2 ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  let σ := ordinaryReferenceAbsolute h
  let u := str025_w h
  have hu := str025_continuous_w h
  have hupos := str025_w_pos h
  have hurep : σ.sqrt =ᵐ[haar 1] u := EventuallyEq.refl _ _
  obtain ⟨C, hC, hcompare⟩ := ordinaryRoot_originalH1_comparison σ u hu hupos hurep
  obtain ⟨η, c, hη, hc, hlocal⟩ := ordinaryReference_local_deficit_stability h p hap hPC
  refine ⟨η, c / C, hη, div_pos hc hC, fun ρ hnear => ?_⟩
  have hl := hlocal ρ hnear
  have hm := mul_le_mul_of_nonneg_left (hcompare ρ) (div_nonneg hc.le hC.le)
  have heq : (c / C) * (C *
      ((∫ x, σ.density x *
        (weakGradient (fun y => ρ.sqrt y / u y)
          (ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep) x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (ρ.sqrt x / u x - 1) ^ 2 ∂haar 1)) =
      c * ((∫ x, σ.density x *
        (weakGradient (fun y => ρ.sqrt y / u y)
          (ordinaryEquality_relativeRoot_memH1 σ ρ u hu hupos hurep) x 0) ^ 2 ∂haar 1) +
        ∫ x, σ.density x * (ρ.sqrt x / u x - 1) ^ 2 ∂haar 1) := by
    field_simp [hC.ne']
  rw [heq] at hm
  exact hm.trans hl

/-- Actual reference local stability, with no supplied analytic premise. Constants may
depend on fixed h and are chosen before every full original absolute-H1 competitor. -/
theorem threefold_reference_localHaar_stability :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ η c : ℝ, 0 < η ∧ 0 < c ∧ ∀ ρ : AbsoluteDensity 1,
        ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
        c * ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ^ 2 ≤
          (ordinaryFisher h ρ).toReal -
            2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  obtain ⟨δ, hδ, hgap⟩ := threefold_reference_rate_and_strictPoincareGap
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨hfin, _, hstrict⟩ := hgap h hh hhd
  obtain ⟨q, haq, hqP⟩ := exists_between hstrict
  have hqfin : q ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hqP le_top)
  have hap : (ordinaryLSRate (ordinaryReference h)).toReal < q.toReal :=
    (ENNReal.toReal_lt_toReal hfin hqfin).2 haq
  apply ordinaryReference_localHaar_of_poincare h q.toReal hap
  rw [ENNReal.ofReal_toReal hqfin]
  exact hqP.le

end DGPS.Examples.ThreeSpeciesCircle
