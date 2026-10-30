import DGPS.Frontier.EX049.Close
import DGPS.Examples.EngineeredHardy
import DGPS.Examples.EngineeredRankOneOppositeTilt
import DGPS.Examples.EngineeredRankOneRates
import DGPS.FiniteN.Tools.Rothaus
import DGPS.FiniteN.Tools.EntropyChainRule
import DGPS.Structural.FrozenGibbsIdentities

/-!
# EX050: sharp engineered one-site LSI by defect removal

The EX049 input is the reconstructed replacement proved in `Frontier/EX049/Close`,
not a recovered historical granular proof. Centering and Rothaus remove its mass
term using the actual EX039 Hardy estimate. All constants are chosen before the
field and test, and the final ordinary rate uses the full original weighted H1
class. Physical and angular energies differ by exactly `a0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples

open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredGroundState
open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredHardy
open DGPS.Frontier.EX049 DGPS.Models

private theorem angular_sub_const {v g : AngCircle → ℝ}
    (hv : IsAngularWeakDeriv v g) (c : ℝ) :
    IsAngularWeakDeriv (fun θ => v θ - c) g := by
  apply (isWeakGradient_comp_iff _ _).2
  change IsWeakGradient (fun x => v (angEquiv x) - c) (physGrad g)
  exact ((isWeakGradient_comp_iff v g).1 hv).sub_const c

private theorem angular_entropy_eq (h : ℝ) (hh : 0 < h) {v : AngCircle → ℝ}
    (hv : AngularH1 v) :
    homogeneousEntropy (circleReference h) (fun θ => v θ ^ 2) =
      ENNReal.ofReal (entEX04910 (circleReference h) (fun θ => v θ ^ 2)) := by
  letI := isProbabilityMeasure_circleReference_EX04925 h hh
  obtain ⟨hi, hl⟩ := integrable_entropy_terms_EX049CLOSE h hh hv
  exact homogeneousEntropy_eq_formula (Eventually.of_forall fun θ => sq_nonneg _) hi hl

private theorem angular_hardy_variance (h : ℝ) (hh : 2 ≤ h)
    {v g : AngCircle → ℝ} (hv : IsAngularWeakDeriv v g) :
    ProbabilityTheory.variance v (circleReference h) ≤
      (4 * Real.pi / h) * ∫ θ, g θ ^ 2 ∂circleReference h := by
  have hp : 0 < h := by linarith
  letI := isProbabilityMeasure_circleReference_EX04925 h hp
  let ν : ProbabilityMeasure AngCircle := ⟨circleReference h, inferInstance⟩
  have hw : IsAngMeasureWeakDeriv ν v g :=
    ⟨(memLp_circleReference_iff_EX04925 h hp v).2 hv.memLp,
      (memLp_circleReference_iff_EX04925 h hp g).2 hv.memLp_deriv,
      hv.memLp.integrable (by norm_num), hv.memLp_deriv.integrable (by norm_num), hv.ibp⟩
  have hvar := weak_hardy_hardy (hardyData_qAng hp) ν rfl hw
  change (∫ θ, (v θ - ∫ y, v y ∂circleReference h) ^ 2 ∂circleReference h) ≤
    4 * (Real.pi / h) * ∫ θ, g θ ^ 2 ∂circleReference h at hvar
  have hvm : MemLp v 2 (circleReference h) := hw.memLp
  rw [ProbabilityTheory.variance_eq_integral hvm.aemeasurable]
  convert hvar using 1 <;> ring

/-- The reconstructed sharp defect, absorbed by the actual Hardy Poincare estimate,
for every angular H1 test and every genuine weak derivative. -/
theorem engineered_sharp_angular_entropy_bound :
    ∃ K h0 : ℝ, 0 < K ∧ 2 ≤ h0 ∧ ∀ h : ℝ, h0 ≤ h →
      ∀ v g : AngCircle → ℝ, IsAngularWeakDeriv v g →
        homogeneousEntropy (circleReference h) (fun θ => v θ ^ 2) ≤
          ENNReal.ofReal ((2 + K / Real.sqrt h) * ∫ θ, g θ ^ 2 ∂circleReference h) := by
  obtain ⟨C, h0, hC, _, hdef⟩ :=
    engineered_three_zone_sharp_defective_lsi_source_blocker_sqrt_inv_EX049CLOSE
  let K := C + 4 * Real.pi * (C + 2)
  refine ⟨K, max 2 h0, by dsimp [K]; positivity, le_max_left _ _, fun h hh v g hv => ?_⟩
  have h2 : 2 ≤ h := (le_max_left _ _).trans hh
  have hp : 0 < h := by linarith
  have hh0 : h0 ≤ h := (le_max_right _ _).trans hh
  letI := isProbabilityMeasure_circleReference_EX04925 h hp
  have hmem : MemLp v 2 (circleReference h) :=
    (memLp_circleReference_iff_EX04925 h hp v).2 hv.memLp
  let m := ∫ θ, v θ ∂circleReference h
  let w : AngCircle → ℝ := fun θ => v θ - m
  let E := ∫ θ, g θ ^ 2 ∂circleReference h
  let V := ProbabilityTheory.variance v (circleReference h)
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hV : 0 ≤ V := ProbabilityTheory.variance_nonneg _ _
  have hw : IsAngularWeakDeriv w g := angular_sub_const hv m
  have hmass : (∫ θ, w θ ^ 2 ∂circleReference h) = V :=
    (ProbabilityTheory.variance_eq_integral hmem.aemeasurable).symm
  have hd := hdef h hh0 w ⟨g, hw⟩ g hw
  rw [hmass] at hd
  have heq := angular_entropy_eq h hp (show AngularH1 w from ⟨g, hw⟩)
  have hdf : homogeneousEntropy (circleReference h) (fun θ => w θ ^ 2) ≤
      ENNReal.ofReal ((2 + C / Real.sqrt h) * E + C * Real.sqrt h * V) := by
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    simpa only [div_eq_mul_inv] using hd
  have hr := FiniteN.Tools.Rothaus.rothaus_centering_variance hmem
  change homogeneousEntropy (circleReference h) (fun θ => v θ ^ 2) ≤
    homogeneousEntropy (circleReference h) (fun θ => w θ ^ 2) + ENNReal.ofReal (2 * V) at hr
  have hraw : homogeneousEntropy (circleReference h) (fun θ => v θ ^ 2) ≤
      ENNReal.ofReal ((2 + C / Real.sqrt h) * E + (C * Real.sqrt h + 2) * V) := by
    calc
      _ ≤ homogeneousEntropy (circleReference h) (fun θ => w θ ^ 2) + ENNReal.ofReal (2 * V) := hr
      _ ≤ ENNReal.ofReal ((2 + C / Real.sqrt h) * E + C * Real.sqrt h * V) +
          ENNReal.ofReal (2 * V) := add_le_add hdf le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hvp : V ≤ (4 * Real.pi / h) * E := angular_hardy_variance h h2 hv
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hp
  have hs1 : 1 ≤ Real.sqrt h := by
    exact (Real.le_sqrt (by norm_num) hp.le).2 (by linarith)
  have hcoef : (2 + C / Real.sqrt h) + (C * Real.sqrt h + 2) * (4 * Real.pi / h) ≤
      2 + K / Real.sqrt h := by
    calc
      _ ≤ (2 + C / Real.sqrt h) + ((C + 2) * Real.sqrt h) * (4 * Real.pi / h) := by
        gcongr
        nlinarith
      _ = _ := by
        dsimp [K]
        field_simp [hp.ne', hs.ne']
        linear_combination (4 * Real.pi * (C + 2)) * (Real.sq_sqrt hp.le)
  refine hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ ((2 + C / Real.sqrt h) + (C * Real.sqrt h + 2) * (4 * Real.pi / h)) * E := by
      have ht := mul_le_mul_of_nonneg_left hvp (show 0 ≤ C * Real.sqrt h + 2 by positivity)
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

private theorem reference_map_angle (h : ℝ) (hh : 2 ≤ h) :
    (engineeredModel h hh).ref.measure.map angEquiv = circleReference h := by
  rw [engineeredModel_ref_measure]
  exact angMap_engineered_hardy (engineeredReference_isProbability h (by linarith))

/-- The sharp tight entropy estimate on the actual full weighted H1 domain, with
physical energy normalization. No regularity or positivity of the test is added. -/
theorem engineered_sharp_one_site_entropy_bound :
    ∃ K h0 : ℝ, 0 < K ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      ∀ (f : Torus 1 → ℝ) (hf : f ∈ WeightedH1 (engineeredModel h hh).ref),
        homogeneousEntropy (engineeredModel h hh).ref.measure (fun x => f x ^ 2) ≤
          ENNReal.ofReal ((2 + K / Real.sqrt h) / a0) *
            ∫⁻ x, ‖weightedGradient (engineeredModel h hh).ref f hf x‖ₑ ^ 2
              ∂(engineeredModel h hh).ref.measure ∧
          homogeneousEntropy (engineeredModel h hh).ref.measure (fun x => f x ^ 2) ≠ ⊤ := by
  obtain ⟨K, h0, hK, hh0, hbound⟩ := engineered_sharp_angular_entropy_bound
  refine ⟨K, h0, hK, hh0, fun h hh h0h f hf => ?_⟩
  have ha0 : 0 < (a0 : ℝ) := DGPS.a0_pos
  let P := (engineeredModel h hh).ref
  let v : AngCircle → ℝ := f ∘ angEquiv.symm
  have hfg : MemH1 (v ∘ angEquiv) := by
    simpa only [v, Function.comp_def, MeasurableEquiv.symm_apply_apply] using
      (mem_weightedH1_iff P).1 hf
  obtain ⟨g, hg⟩ := (angularH1_comp_iff v).2 hfg
  have hgphys : IsWeakGradient f (physGrad g) := by
    simpa only [v, Function.comp_def, MeasurableEquiv.symm_apply_apply] using
      (isWeakGradient_comp_iff v g).1 hg
  have hmap := reference_map_angle h hh
  have hEnt : homogeneousEntropy P.measure (fun x => f x ^ 2) =
      homogeneousEntropy (circleReference h) (fun θ => v θ ^ 2) := by
    rw [← hmap, FiniteN.Tools.homogeneousEntropy_map_measurableEquiv]
    simp only [P, v, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
  have hEp : (∫⁻ x, ‖weightedGradient P f hf x‖ₑ ^ 2 ∂P.measure) =
      ENNReal.ofReal a0 * ENNReal.ofReal (∫ θ, g θ ^ 2 ∂circleReference h) := by
    have hae : weightedGradient P f hf =ᵐ[P.measure] physGrad g :=
      P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hf hgphys)
    calc
      _ = ∫⁻ x, ‖physGrad g x‖ₑ ^ 2 ∂P.measure :=
        lintegral_congr_ae (hae.mono fun x hx => by rw [hx])
      _ = _ := by
        rw [lintegral_physGrad, hmap, lintegral_enorm_sq_hardy
          ((memLp_circleReference_iff_EX04925 h (by linarith) g).2 hg.memLp_deriv)]
        rfl
  constructor
  · rw [hEnt, hEp]
    refine (hbound h h0h v g hg).trans_eq ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ a0_pos.ne',
      ← ENNReal.ofReal_mul (by positivity)]
  · rw [hEnt, angular_entropy_eq h (by linarith) ⟨g, hg⟩]
    exact ENNReal.ofReal_ne_top

/-- The actual ordinary rate has the sharp one-site lower bound, on its full
weighted weak H1 infimum class. -/
theorem engineered_sharp_one_site_lower_bound :
    ∃ K h0 : ℝ, 0 < K ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      1 - K / Real.sqrt h ≤ (ordinaryLSRate (engineeredModel h hh).ref).toReal / a0 := by
  obtain ⟨K, h0, hK, hh0, hEnt⟩ := engineered_sharp_one_site_entropy_bound
  refine ⟨K, h0, hK, hh0, fun h hh h0h => ?_⟩
  let P := (engineeredModel h hh).ref
  let A := 2 + K / Real.sqrt h
  have ha0 : 0 < (a0 : ℝ) := DGPS.a0_pos
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : 0 ≤ 2 * a0 / A := by positivity
  have hrate : ENNReal.ofReal (2 * a0 / A) ≤ ordinaryLSRate P := by
    unfold ordinaryLSRate
    refine le_iInf fun ⟨f, hf, hpos⟩ => ?_
    obtain ⟨hfEnt, hfin⟩ := hEnt h hh h0h f hf
    rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin)]
    calc
      _ ≤ ENNReal.ofReal (2 * a0 / A) *
          (ENNReal.ofReal (A / a0) * ∫⁻ x, ‖weightedGradient P f hf x‖ₑ ^ 2 ∂P.measure) :=
        mul_le_mul' le_rfl hfEnt
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha]
        have he : (2 * a0 / A) * (A / a0) = 2 := by field_simp [hA.ne', a0_pos.ne']
        rw [he, ENNReal.ofReal_ofNat]
  have hfin : ordinaryLSRate P ≠ ⊤ := (Structural.ordinaryLSRate_lt_top (by decide) P).ne
  have hr : 2 * a0 / A ≤ (ordinaryLSRate P).toReal := by
    simpa only [ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono hfin hrate
  have hr' : 2 / A ≤ (ordinaryLSRate P).toReal / a0 := by
    rw [le_div_iff₀ a0_pos]
    convert hr using 1 <;> ring
  have ht : 0 ≤ K / Real.sqrt h := by positivity
  refine le_trans ?_ hr'
  rw [le_div_iff₀ hA]
  dsimp [A]
  nlinarith [sq_nonneg (K / Real.sqrt h)]

/-- EX050 quantitative bounds on the actual normalized ordinary one-site rate.
All constants are uniform in the field and all original Sobolev competitors. -/
theorem engineered_sharp_one_site_rate_bounds :
    ∃ C h0 : ℝ, 0 < C ∧ 2 ≤ h0 ∧ ∀ (h : ℝ) (hh : 2 ≤ h), h0 ≤ h →
      1 - C / Real.sqrt h ≤ (ordinaryLSRate (engineeredModel h hh).ref).toReal / a0 ∧
      (ordinaryLSRate (engineeredModel h hh).ref).toReal / a0 ≤ 1 + C * Real.log h / h := by
  obtain ⟨K, hL, hK, hhL, hlow⟩ := engineered_sharp_one_site_lower_bound
  obtain ⟨B, hU, hB, hhU, hup⟩ := engineered_opposite_tilt_one_site_upper_bound
  refine ⟨max K B, max hL hU, hK.trans_le (le_max_left _ _), hhL.trans (le_max_left _ _),
    fun h hh h0h => ?_⟩
  have hLh : hL ≤ h := (le_max_left _ _).trans h0h
  have hUh : hU ≤ h := (le_max_right _ _).trans h0h
  have hp : 0 < h := by linarith
  have ha0 : 0 < (a0 : ℝ) := DGPS.a0_pos
  have hlog : 0 ≤ Real.log h := Real.log_nonneg (by linarith)
  constructor
  · have ht : K / Real.sqrt h ≤ max K B / Real.sqrt h :=
      div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg h)
    exact (sub_le_sub_left ht 1).trans (hlow h hh hLh)
  · obtain ⟨_, _, _, _, _, hupper⟩ := hup h hh hUh
    have hright : 0 ≤ a0 * (1 + B * Real.log h / h) := by positivity
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
    rw [ENNReal.toReal_ofReal hright] at hr
    have hr' : (ordinaryLSRate (engineeredModel h hh).ref).toReal / a0 ≤
        1 + B * Real.log h / h := (div_le_iff₀ a0_pos).2 (by nlinarith [hr])
    refine hr'.trans (add_le_add le_rfl ?_)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right K B) hlog) hp.le

/-- EX050: the actual normalized one-site rate tends to one through the fixed
engineered family. The field subtype retains every h at least two. -/
theorem engineered_sharp_one_site_limit_from_defect_removal :
    Tendsto (fun h : Set.Ici (2 : ℝ) =>
      (ordinaryLSRate (engineeredModel h.1 h.2).ref).toReal / a0) atTop (𝓝 1) := by
  obtain ⟨C, h0, hC, hh0, hbound⟩ := engineered_sharp_one_site_rate_bounds
  have hval : Tendsto (fun h : Set.Ici (2 : ℝ) => (h : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    refine eventually_atTop.2 ⟨⟨max 2 b, by
      change (2 : ℝ) ≤ max 2 b
      exact le_max_left _ _⟩, fun h hh => ?_⟩
    change max (2 : ℝ) b ≤ (h : ℝ) at hh
    exact (le_max_right _ _).trans hh
  have hlog : Tendsto (fun h : ℝ => Real.log h / h) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlow : Tendsto (fun h : Set.Ici (2 : ℝ) => 1 - C / Real.sqrt (h : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := C)).div_atTop (Real.tendsto_sqrt_atTop.comp hval))
  have hupp : Tendsto (fun h : Set.Ici (2 : ℝ) => 1 + C * Real.log (h : ℝ) / (h : ℝ))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, mul_div_assoc, mul_zero, add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).add ((hlog.comp hval).const_mul C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · exact (hval.eventually (eventually_ge_atTop h0)).mono fun h hh => (hbound h.1 h.2 hh).1
  · exact (hval.eventually (eventually_ge_atTop h0)).mono fun h hh => (hbound h.1 h.2 hh).2

end DGPS.Examples
