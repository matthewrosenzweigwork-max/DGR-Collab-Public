import FullLabeledLSI.Defs.F03_RelFisher
import FullLabeledLSI.Infra.ProdH1
import SharpSymmetricLSI.Paper.Defective8
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.EntFinite

/-!
# `relFisher` agrees with `fisherInfo` for a reference density bounded above and below

`√(ρa/ρb) = √ρa · (√ρb)⁻¹` has weak gradient `(√ρb)⁻¹ ∇√ρa - √ρa ∇√ρb/ρb`
(`isWeakGrad_mul_L2`, with `(√ρb)⁻¹ = G(ρb)` for a `C¹` cutoff `G` of `t ↦ t^{-1/2}`).
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

theorem memLp_comp_weakGrad {f : Torus d → ℝ} (h : MemH1 (haar d) f) (k : Fin d) :
    MemLp (fun y => weakGrad f y k) 2 (haar d) :=
  h.2.2.of_le ((isWeakGrad_weakGrad h.1).aestronglyMeasurable_grad k)
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)

/-- The `C¹` cutoff `1/√t` for `t ≥ a`. -/
def invSqrtCut (a t : ℝ) : ℝ := (sqrtCut a t)⁻¹

theorem sqrtCut_ge {a : ℝ} (ha : 0 < a) (t : ℝ) : Real.sqrt (a / 2) ≤ sqrtCut a t :=
  Real.sqrt_le_sqrt (sqrtCut_inner_ge ha t)

theorem contDiff_invSqrtCut {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (invSqrtCut a) :=
  (contDiff_sqrtCut ha).inv fun t =>
    (lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) (sqrtCut_ge ha t)).ne'

theorem hasDerivAt_invSqrtCut {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (invSqrtCut a) (-(deriv (sqrtCut a) t) / sqrtCut a t ^ 2) t := by
  have hd : HasDerivAt (sqrtCut a) (deriv (sqrtCut a) t) t :=
    (((contDiff_sqrtCut ha).differentiable one_ne_zero) t).hasDerivAt
  exact hd.inv (lt_of_lt_of_le (Real.sqrt_pos.2 (by positivity)) (sqrtCut_ge ha t)).ne'

theorem exists_bound_deriv_invSqrtCut {a : ℝ} (ha : 0 < a) :
    ∃ L : ℝ, ∀ t, |deriv (invSqrtCut a) t| ≤ L := by
  obtain ⟨L, hL⟩ := exists_bound_deriv_sqrtCut ha
  refine ⟨L / (a / 2), fun t => ?_⟩
  rw [(hasDerivAt_invSqrtCut ha t).deriv, abs_div, abs_neg]
  have hs : a / 2 ≤ sqrtCut a t ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrtCut_ge ha t) 2
    rwa [Real.sq_sqrt (by positivity)] at this
  rw [abs_of_nonneg (sq_nonneg (sqrtCut a t))]
  exact div_le_div₀ ((abs_nonneg _).trans (hL t)) (hL t) (by positivity) hs


theorem isWeakGrad_inv_sqrt {ρb : Torus d → ℝ} {c : ℝ} (hc : 0 < c) (hρc : ∀ x, c ≤ ρb x)
    (hb1 : ∫ x, ρb x ∂haar d = 1) (hb' : MemH1 (haar d) (fun x => Real.sqrt (ρb x))) :
    IsWeakGrad (fun y => (Real.sqrt (ρb y))⁻¹)
      (fun y k => -(weakGrad (fun x => Real.sqrt (ρb x)) y k / ρb y)) := by
  set v : Torus d → ℝ := fun x => Real.sqrt (ρb x) with hv
  set gb := weakGrad v with hgb
  have hρ0 : ∀ x, 0 ≤ ρb x := fun x => (hc.trans_le (hρc x)).le
  have hvw : IsWeakGrad v gb := isWeakGrad_weakGrad hb'.1
  have hρwg : IsWeakGrad ρb (fun y k => 2 * v y * gb y k) := by
    have := isWeakGrad_sq hvw hb'.2.1 (memLp_comp_weakGrad hb')
    convert this using 2
    simp only [hv]
    rw [Real.sq_sqrt (hρ0 _)]
  have hρi : Integrable ρb (haar d) := integrable_of_integral_eq_one' hb1
  have hgi : ∀ k, Integrable (fun y => 2 * v y * gb y k) (haar d) := fun k => by
    have := (hb'.2.1.integrable_mul (memLp_comp_weakGrad hb' k)).const_mul 2
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)
  have ha : 0 < c / 2 := by positivity
  obtain ⟨L, hL⟩ := exists_bound_deriv_invSqrtCut ha
  have h := isWeakGrad_comp hρwg hρi hgi (contDiff_invSqrtCut ha) hL
  convert h using 1
  · funext y
    simp only [invSqrtCut]
    rw [sqrtCut_eq ha (by linarith [hρc y])]
  · funext y k
    have hy : c / 2 < ρb y := by linarith [hρc y]
    have hp : 0 < ρb y := hc.trans_le (hρc y)
    rw [(hasDerivAt_invSqrtCut ha (ρb y)).deriv, deriv_sqrtCut_of_gt ha hy,
      sqrtCut_eq ha hy.le]
    have hs : 0 < Real.sqrt (ρb y) := Real.sqrt_pos.2 hp
    have hs2 : Real.sqrt (ρb y) ^ 2 = ρb y := Real.sq_sqrt hp.le
    simp only [hv]
    field_simp
    rw [hs2]


/-- `√ρa · (√ρb)⁻¹ ∈ H¹`-type, with the quotient-rule gradient. -/
theorem isWeakGrad_sqrt_quot {ρa ρb : Torus d → ℝ} {c : ℝ} (hc : 0 < c) (hρc : ∀ x, c ≤ ρb x)
    (hb1 : ∫ x, ρb x ∂haar d = 1) (ha : MemH1 (haar d) (fun x => Real.sqrt (ρa x)))
    (hb' : MemH1 (haar d) (fun x => Real.sqrt (ρb x))) :
    IsWeakGrad (fun y => Real.sqrt (ρa y) * (Real.sqrt (ρb y))⁻¹)
      (fun y k => (Real.sqrt (ρb y))⁻¹ * weakGrad (fun x => Real.sqrt (ρa x)) y k +
        Real.sqrt (ρa y) * (-(weakGrad (fun x => Real.sqrt (ρb x)) y k / ρb y))) := by
  have hw := isWeakGrad_inv_sqrt hc hρc hb1 hb'
  have hρpos : ∀ x, 0 < ρb x := fun x => hc.trans_le (hρc x)
  have hw2 : MemLp (fun y => (Real.sqrt (ρb y))⁻¹) 2 (haar d) := by
    refine MemLp.of_bound hw.aestronglyMeasurable_fun (Real.sqrt c)⁻¹
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (hρpos y)))]
    exact inv_anti₀ (Real.sqrt_pos.2 hc) (Real.sqrt_le_sqrt (hρc y))
  have hgw2 : ∀ k, MemLp (fun y => -(weakGrad (fun x => Real.sqrt (ρb x)) y k / ρb y)) 2
      (haar d) := fun k => by
    refine (memLp_comp_weakGrad hb' k).of_le_mul (c := c⁻¹) (hw.aestronglyMeasurable_grad k) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos (hρpos y)]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hc (hρc y)) (abs_nonneg _)
  exact isWeakGrad_mul_L2 (isWeakGrad_weakGrad ha.1) hw ha.2.1 hw2 (memLp_comp_weakGrad ha) hgw2


theorem relFisher_eq_fisherInfo_aux {ρa ρb : Torus d → ℝ} (ha0 : ∀ x, 0 ≤ ρa x)
    (ha1 : ∫ x, ρa x ∂haar d = 1) (hb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ ρb x ∧ ρb x ≤ C)
    (hb1 : ∫ x, ρb x ∂haar d = 1) (ha : MemH1 (haar d) fun x => Real.sqrt (ρa x))
    (hb' : MemH1 (haar d) fun x => Real.sqrt (ρb x)) :
    relFisher ρa ρb = fisherInfo (densMeasure ρa) (densMeasure ρb) := by
  obtain ⟨c, C, hc, hbd⟩ := hb
  have hρc : ∀ x, c ≤ ρb x := fun x => (hbd x).1
  have hρpos : ∀ x, 0 < ρb x := fun x => hc.trans_le (hρc x)
  set u : Torus d → ℝ := fun x => Real.sqrt (ρa x) with hu
  set v : Torus d → ℝ := fun x => Real.sqrt (ρb x) with hv
  set ga := weakGrad u with hga
  set gb := weakGrad v with hgb
  have hq := isWeakGrad_sqrt_quot hc hρc hb1 ha hb'
  set q : Torus d → ℝ := fun y => u y * (v y)⁻¹ with hqdef
  set gq : Torus d → Fin d → ℝ := fun y k => (v y)⁻¹ * ga y k + u y * (-(gb y k / ρb y)) with hgq
  -- measures
  have hρam : AEMeasurable ρa (haar d) :=
    (integrable_of_integral_eq_one' ha1).aestronglyMeasurable.aemeasurable
  have hρbm : AEMeasurable ρb (haar d) :=
    (integrable_of_integral_eq_one' hb1).aestronglyMeasurable.aemeasurable
  have hQp : IsProbabilityMeasure (densMeasure ρb) :=
    isProbabilityMeasure_densMeasure' (fun x => (hρpos x).le) hb1
  have hQvol : densMeasure ρb ≪ haar d := withDensity_absolutelyContinuous _ _
  have hvolQ : haar d ≪ densMeasure ρb := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable hρbm)
    (Filter.Eventually.of_forall fun x => by simpa using hρpos x)
  have hrat : densMeasure ρa = (densMeasure ρb).withDensity
      (fun x => ENNReal.ofReal (ρa x / ρb x)) := by
    have hb : AEMeasurable (fun x => ENNReal.ofReal (ρb x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hρbm
    have hr : AEMeasurable (fun x => ENNReal.ofReal (ρa x / ρb x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hρam.div hρbm)
    unfold densMeasure
    rw [← withDensity_mul₀ hb hr]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (hρpos x).le]
    congr 1
    have := (hρpos x).ne'
    field_simp
  have hac : densMeasure ρa ≪ densMeasure ρb := by
    rw [hrat]; exact withDensity_absolutelyContinuous _ _
  have hrn : (densMeasure ρa).rnDeriv (densMeasure ρb) =ᵐ[densMeasure ρb]
      fun x => ENNReal.ofReal (ρa x / ρb x) := by
    rw [hrat]
    exact Measure.rnDeriv_withDensity₀ _ ((ENNReal.measurable_ofReal.comp_aemeasurable
      (hρam.div hρbm)).mono_ac hQvol)
  have hrnq : (fun x => Real.sqrt ((densMeasure ρa).rnDeriv (densMeasure ρb) x).toReal)
      =ᵐ[densMeasure ρb] q := by
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (div_nonneg (ha0 x) (hρpos x).le),
      Real.sqrt_div (ha0 x), div_eq_mul_inv]
  -- the relFisher integral
  have hrel : relFisher ρa ρb = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * ga x k -
      u x * score ρb x k) ^ 2) ∂haar d := by
    unfold relFisher
    rw [if_pos ⟨hac, ha, hb'⟩]
  -- pointwise identity `4 ρb |∇q|² = (2∇√ρa - √ρa score)²`
  have hpt : ∀ x, 4 * (ρb x * sqNorm (gq x)) = ∑ k, (2 * ga x k - u x * score ρb x k) ^ 2 := by
    intro x
    have hvpos : 0 < v x := Real.sqrt_pos.2 (hρpos x)
    have hρv : ρb x = v x ^ 2 := (Real.sq_sqrt (hρpos x).le).symm
    have hsc : ∀ k, score ρb x k = 2 * gb x k / v x := fun k => by
      simp only [score, if_pos (hρpos x), hv, hgb]
    unfold sqNorm
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsc k]
    simp only [hgq]
    rw [hρv]
    field_simp
    ring
  -- the Dirichlet integral of `q`
  have hwg := weakGrad_ae_eq hq
  have hmS : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (gq x))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (hq.aestronglyMeasurable_sqNorm.aemeasurable)
  have hdir : dirichlet (densMeasure ρb) q =
      ∫⁻ x, ENNReal.ofReal (ρb x) * ENNReal.ofReal (sqNorm (gq x)) ∂haar d := by
    unfold dirichlet densMeasure
    have hmW : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (weakGrad q x))) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((isWeakGrad_weakGrad ⟨_, hq⟩).aestronglyMeasurable_sqNorm.aemeasurable)
    have hmρ : AEMeasurable (fun x => ENNReal.ofReal (ρb x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hρbm
    rw [lintegral_withDensity_eq_lintegral_mul₀ hmρ hmW]
    refine lintegral_congr_ae ?_
    filter_upwards [hwg] with x hx
    simp only [Pi.mul_apply, hx]
  have h4 : 4 * dirichlet (densMeasure ρb) q = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * ga x k -
      u x * score ρb x k) ^ 2) ∂haar d := by
    rw [hdir, ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_congr fun x => ?_
    rw [← hpt x, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (hρpos x).le]
    simp [mul_assoc]
  -- transfer of `L²` from Haar measure to `Q`
  have hQle : densMeasure ρb ≤ ENNReal.ofReal C • haar d := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [densMeasure, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hbd x).2
  have hMemQ : ∀ {f : Torus d → ℝ}, MemLp f 2 (haar d) → MemLp f 2 (densMeasure ρb) :=
    fun h => (h.smul_measure ENNReal.ofReal_ne_top).mono_measure hQle
  by_cases hM : MemH1 (densMeasure ρb)
      (fun x => Real.sqrt ((densMeasure ρa).rnDeriv (densMeasure ρb) x).toReal)
  · rw [hrel]
    unfold fisherInfo
    rw [if_pos ⟨hac, hM⟩]
    obtain ⟨-, hd⟩ := memH1_congr_ae hQvol hvolQ hM hrnq
    rw [← hd, h4]
  · rw [hrel]
    unfold fisherInfo
    rw [if_neg (fun h => hM h.2)]
    by_contra hI
    apply hM
    have hqL2 : MemLp q 2 (haar d) := by
      refine ha.2.1.of_le_mul (c := (Real.sqrt c)⁻¹) hq.aestronglyMeasurable_fun
        (Filter.Eventually.of_forall fun y => ?_)
      simp only [hqdef, hu, hv]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2
        (Real.sqrt_pos.2 (hρpos y))), mul_comm]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ (Real.sqrt_pos.2 hc)
        (Real.sqrt_le_sqrt (hρc y))) (abs_nonneg _)
    have hgL2 : MemLp (fun x => Real.sqrt (sqNorm (weakGrad q x))) 2 (haar d) := by
      have hmeas : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad q x))) (haar d) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable
          (isWeakGrad_weakGrad ⟨_, hq⟩).aestronglyMeasurable_sqNorm
      rw [memLp_two_iff_integrable_sq hmeas]
      refine ⟨hmeas.pow 2, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      have hle : ∀ᵐ x ∂haar d, ENNReal.ofReal (Real.sqrt (sqNorm (weakGrad q x)) ^ 2) ≤
          ENNReal.ofReal (4 * c)⁻¹ * ENNReal.ofReal (∑ k, (2 * ga x k - u x * score ρb x k) ^ 2) := by
        filter_upwards [hwg] with x hx
        rw [Real.sq_sqrt (sqNorm_nonneg _), hx, ← ENNReal.ofReal_mul (by positivity), ← hpt x]
        refine ENNReal.ofReal_le_ofReal ?_
        have hs0 := sqNorm_nonneg (gq x)
        have e : (4 * c)⁻¹ * (4 * (ρb x * sqNorm (gq x))) = ρb x * sqNorm (gq x) / c := by
          field_simp
        rw [e, le_div_iff₀ hc]
        nlinarith [mul_le_mul_of_nonneg_right (hρc x) hs0]
      refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hI)
    have hMq : MemH1 (densMeasure ρb) q := ⟨⟨gq, hq⟩, hMemQ hqL2, hMemQ hgL2⟩
    exact (memH1_congr_ae hQvol hvolQ hMq hrnq.symm).1

end SharpLSI.FL
