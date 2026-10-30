import DGPS.Examples.EngineeredRankOneEX045
import DGPS.Examples.EngineeredRankOneRates
import DGPS.Examples.EngineeredRankOneGap

/-!
# Actual engineered scalar-rate bounds

The relative square root of every actual absolute density supplies the normalized
nonnegative angular Sobolev test required by EX045. Thus its entropy completion
and the exact fixed-coupling dissipation apply to the full canonical scalar domain.
No entropy estimate or sharp one-site LSI is assumed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples

open DGPS.Circle.AngularNormalization DGPS.Models DGPS.PositiveRankOne
open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredRankOneEX045
open DGPS.Examples.EngineeredHardy

/-- Factual normalized angular root data for every original absolute density.
The Fisher identity retains the physical factor `4*a0`. -/
theorem engineered_absolute_relative_root_data (h : ℝ) (hh : 2 ≤ h) (ρ : AbsoluteDensity 1) :
    ∃ f g : AngCircle → ℝ, IsAngularWeakDeriv f g ∧ (∀ θ, 0 ≤ f θ) ∧
      (∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h) = 1 ∧
      densityRef h f = (densityMeasure ρ : Measure (Torus 1)) ∧
      (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1))
        (engineeredModel h hh).ref).toReal =
          4 * a0 * ∫ x, g (angEquiv x) ^ 2 ∂engineeredReference h := by
  have ha0 : 0 < (a0 : ℝ) := DGPS.a0_pos
  let M := engineeredModel h hh
  let P := M.ref
  let ν : Measure (Torus 1) := densityMeasure ρ
  let u := relativeSqrt ν P
  have hac : ν ≪ P.measure :=
    (withDensity_absolutelyContinuous _ _).trans P.haar_ac_measure
  have hIfin : ordinaryRelativeFisher ν P ≠ ⊤ := by
    rw [M.fisher_eq ρ]
    exact ENNReal.ofReal_ne_top
  have hu : u ∈ WeightedH1 P := by
    by_contra hn
    exact hIfin (ordinaryRelativeFisher_of_not_mem hn)
  let f : AngCircle → ℝ := u ∘ angEquiv.symm
  have huf : (f ∘ angEquiv : Torus 1 → ℝ) = u := by
    funext x
    simp only [f, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have hf : AngularH1 f := by
    apply (angularH1_comp_iff f).2
    rw [huf]
    exact (mem_weightedH1_iff P).1 hu
  obtain ⟨g, hg⟩ := hf
  have hgphys : IsWeakGradient u (physGrad g) := by
    simpa only [huf] using (isWeakGradient_comp_iff f g).1 hg
  have hsq (x : Torus 1) : u x ^ 2 = (ν.rnDeriv P.measure x).toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  have href : P.measure = engineeredReference h := engineeredModel_ref_measure h hh
  have hnorm : ∫ x, u x ^ 2 ∂P.measure = 1 := by
    simp_rw [hsq]
    rw [Measure.integral_toReal_rnDeriv hac]
    simp [ν]
  have hfnorm : ∫ x, f (angEquiv x) ^ 2 ∂engineeredReference h = 1 := by
    rw [← href]
    simpa only [f, Function.comp_apply, MeasurableEquiv.symm_apply_apply] using hnorm
  have hmeasure : densityRef h f = ν := by
    unfold densityRef
    rw [← href]
    have he : (fun x => ENNReal.ofReal (f (angEquiv x) ^ 2)) =
        fun x => ENNReal.ofReal (u x ^ 2) := by
      funext x
      simp only [f, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rw [he]
    calc P.measure.withDensity (fun x => ENNReal.ofReal (u x ^ 2)) =
        P.measure.withDensity (ν.rnDeriv P.measure) := by
          refine withDensity_congr_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top ν P.measure] with x hx
          rw [hsq, ENNReal.ofReal_toReal hx.ne]
      _ = ν := Measure.withDensity_rnDeriv_eq ν P.measure hac
  have hgp : MemLp (physGrad g) 2 P.measure :=
    ((isWeightedWeakGradient_iff P).2 hgphys).memLp_grad
  have hgj : MemLp (g ∘ angEquiv) 2 P.measure := (memLp_physGrad_iff P.measure g).1 hgp
  let J := ∫ x, g (angEquiv x) ^ 2 ∂P.measure
  have hJ : 0 ≤ J := integral_nonneg fun _ => sq_nonneg _
  have hIE : ordinaryRelativeFisher ν P = ENNReal.ofReal (4 * a0 * J) := by
    rw [ordinaryRelativeFisher_eq hac hgphys]
    simp_rw [enorm_physGrad_sq]
    have hgj' : MemLp (fun x => g (angEquiv x)) 2 P.measure := hgj
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_hardy hgj']
    change 4 * (ENNReal.ofReal a0 * ENNReal.ofReal J) = _
    rw [← ENNReal.ofReal_mul a0_pos.le]
    have h4 : (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h4, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  refine ⟨f, g, hg, fun θ => Real.sqrt_nonneg _, hfnorm, hmeasure, ?_⟩
  rw [hIE, ENNReal.toReal_ofReal (by positivity)]
  dsimp only [J]
  rw [href]

/-- EX045's actual all-density consequence, with no proof-stage root assumption. -/
theorem engineered_absolute_entropy_completion :
    ∃ C h0 : ℝ, 0 < C ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      ∀ ρ : AbsoluteDensity 1,
        relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (engineeredReference h) ≤
          ENNReal.ofReal (C *
            ((ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1))
              (engineeredModel h hh).ref).toReal / (4 * a0 * h) +
              (∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1))) ^ 2)) := by
  obtain ⟨C, h0, hC, hh0, hbound⟩ := engineered_central_entropy_completion
  refine ⟨C, h0, hC, hh0, fun h hh h0h ρ => ?_⟩
  obtain ⟨f, g, hg, hf0, hnorm, hmeasure, hI⟩ := engineered_absolute_relative_root_data h hh ρ
  let T := (∫ x, g (angEquiv x) ^ 2 ∂engineeredReference h) / h +
    (∫ x, Eang h (angEquiv x) ∂densityRef h f) ^ 2
  have hb := (hbound h h0h f g hg hf0 hnorm T rfl).2
  rw [hmeasure] at hb
  refine hb.trans_eq ?_
  congr 1
  dsimp [T]
  rw [hmeasure, hI]
  field_simp [a0_pos.ne', show h ≠ 0 by linarith]

private theorem field_le_lamH {h : ℝ} (hh : 0 < h) : h ≤ lamH h := by
  have hs : 0 < Real.sinh h := Real.sinh_pos_iff.2 hh
  have hc : Real.sinh h ≤ Real.cosh h := by
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos (-h)]
  unfold lamH
  exact le_mul_of_one_le_right hh.le ((le_div_iff₀ hs).2 (by simpa using hc))

/-- A uniform actual scalar linear lower bound at coupling exactly one, on all
canonical absolute densities. -/
theorem engineered_scalar_linear_lower_bound :
    ∃ c h0 : ℝ, 0 < c ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      ∀ b : AbsoluteDrift (engineeredModel h hh).data,
        ENNReal.ofReal (c * a0 * h) ≤ scalarRate (engineeredModel h hh).data b := by
  obtain ⟨C, h0, hC, hh0, hEnt⟩ := engineered_absolute_entropy_completion
  refine ⟨(C + 1)⁻¹, h0, by positivity, hh0, fun h hh h0h b => ?_⟩
  have hp : 0 < h := by linarith
  have ha0 : 0 < (a0 : ℝ) := DGPS.a0_pos
  unfold scalarRate
  refine le_iInf fun ⟨ρ, hpos⟩ => ?_
  obtain ⟨_, _, _, _, hGap, hIfin, hDfin, hD⟩ := engineered_exact_scalar_gap_and_dissipation h hh b ρ
  rw [speciesGap_single] at hGap
  rw [speciesDissipation_single] at hDfin hD
  let I := (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1))
    (engineeredModel h hh).ref).toReal
  let m := ∫ x, Eang h (angEquiv x) ∂(densityMeasure ρ : Measure (Torus 1))
  let T := I / (4 * a0 * h) + m ^ 2
  have hI : 0 ≤ I := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hE : 0 ≤ ∫ x, dEang h (angEquiv x) ^ 2 ∂(densityMeasure ρ : Measure (Torus 1)) :=
    integral_nonneg fun _ => sq_nonneg _
  have hH := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hEnt h hh h0h ρ)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le hT)] at hH
  have hG : (scalarGap (engineeredModel h hh).data ρ : ℝ) ≤ (C + 1) * T := by
    rw [hGap]
    have hmT : m ^ 2 ≤ T := by
      dsimp [T]
      exact le_add_of_nonneg_left (by positivity)
    change _ ≤ C * T at hH
    nlinarith
  have hDlow : 2 * a0 * h * T ≤ (scalarDissipation (engineeredModel h hh).data b ρ).toReal := by
    have hl := field_le_lamH hp
    have hm := mul_le_mul_of_nonneg_right hl (sq_nonneg m)
    have hprod := mul_nonneg (sq_nonneg m) hE
    have hDb := hD
    change (scalarDissipation (engineeredModel h hh).data b ρ).toReal / a0 =
      I / a0 + 2 * lamH h * m ^ 2 + m ^ 2 * _ at hDb
    have hbase : 2 * h * T = I / (2 * a0) + 2 * h * m ^ 2 := by
      dsimp [T]
      field_simp [hp.ne', a0_pos.ne']
      ring
    have hhalf : I / (2 * a0) ≤ I / a0 := by
      apply div_le_div_of_nonneg_left hI a0_pos
      nlinarith [a0_pos]
    have hb : 2 * h * T ≤ (scalarDissipation (engineeredModel h hh).data b ρ).toReal / a0 := by
      rw [hbase]
      nlinarith
    have hb' := (le_div_iff₀ ha0).1 hb
    convert hb' using 1 <;> ring
  have hreal : ((C + 1)⁻¹ * a0 * h) *
      (2 * (scalarGap (engineeredModel h hh).data ρ : ℝ)) ≤
        (scalarDissipation (engineeredModel h hh).data b ρ).toReal := by
    have hg := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 * a0 * h / (C + 1) by positivity)
    have he : (2 * a0 * h / (C + 1)) * ((C + 1) * T) = 2 * a0 * h * T := by
      field_simp [show C + 1 ≠ 0 by linarith]
    rw [he] at hg
    convert hg.trans hDlow using 1 <;> ring
  have hden : 2 * (scalarGap (engineeredModel h hh).data ρ : ℝ≥0∞) =
      ENNReal.ofReal (2 * (scalarGap (engineeredModel h hh).data ρ : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  have hGpos : 0 < (scalarGap (engineeredModel h hh).data ρ : ℝ) := by
    exact_mod_cast hpos
  have h2pos : 0 < 2 * (scalarGap (engineeredModel h hh).data ρ : ℝ) :=
    mul_pos (by norm_num) hGpos
  unfold scalarQuotient
  rw [hden, ← ENNReal.ofReal_toReal hDfin, ← ENNReal.ofReal_div_of_pos h2pos]
  apply ENNReal.ofReal_le_ofReal
  exact (le_div_iff₀ h2pos).2 hreal

end DGPS.Examples
