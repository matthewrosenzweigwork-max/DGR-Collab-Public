import LeanResearch.PeriodicAttractiveLogGas.ConditionalEntropyDisintegration
import LeanResearch.PeriodicAttractiveLogGas.CrossingConcentration
import LeanResearch.PeriodicAttractiveLogGas.TwoCellEntropy

/-! The weighted entropy step in manuscript lines 2980--2984. The proof
uses the actual normalized density tilt, and includes the zero-mass branch.
Its exponential moment is an explicit input, discharged by the source
crossing concentration theorem in the later physical-law assembly. -/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.WeightedSquareEntropy

open ConditionalEntropyDisintegration RelativeEntropyVariational

variable {α : Type*} [MeasurableSpace α] {P : Measure α}

/-- A nonnegative observable with a positive exponential moment is integrable;
the bounded density times that observable is also genuinely integrable. -/
theorem weighted_integrable [IsProbabilityMeasure P] {F H : α → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ F x ∧ F x ≤ B)
    (hH : Measurable H) (hH0 : ∀ᵐ x ∂P, 0 ≤ H x) {s : ℝ} (hs : 0 < s)
    (he : Integrable (fun x => Real.exp (s * H x)) P) :
    Integrable H P ∧ Integrable (fun x => F x * H x) P := by
  have hsi := integrable_of_lower_bound_exp (hH.const_mul s)
    (hH0.mono fun x hx => mul_nonneg hs.le hx) he
  have hHi : Integrable H P := by
    convert hsi.div_const s using 1
    ext x
    field_simp
  exact ⟨hHi, integrable_bounded_density_mul hF hH hb hHi⟩

/-- Source variational argument before dividing by the positive scale. All
logarithmic and weighted integrability is derived. The density may vanish. -/
theorem weighted_entropy [IsProbabilityMeasure P] {F H : α → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ᵐ x ∂P, 0 ≤ F x ∧ F x ≤ B)
    (hH : Measurable H) (hH0 : ∀ᵐ x ∂P, 0 ≤ H x) {s K : ℝ} (hs : 0 < s)
    (he : Integrable (fun x => Real.exp (s * H x)) P)
    (hK : (∫ x, Real.exp (s * H x) ∂P) ≤ K) :
    ((s * ∫ x, F x * H x ∂P : ℝ) : EReal) ≤
      entropy P F + ((Real.log K * ∫ x, F x ∂P : ℝ) : EReal) := by
  obtain ⟨hFi, hFlog⟩ := bounded_density_integrable hF hb
  have hF0 := hb.mono fun _ hx => hx.1
  have hS0 : 0 ≤ ∫ x, F x ∂P := integral_nonneg_of_ae hF0
  have hFHi := (weighted_integrable hF hb hH hH0 hs he).2
  by_cases hS : ∫ x, F x ∂P = 0
  · obtain ⟨hz, hent⟩ := zero_mass_entropy hF hb hS
    have hi : ∫ x, F x * H x ∂P = 0 := by
      calc
        _ = ∫ _ : α, (0 : ℝ) ∂P := integral_congr_ae (hz.mono fun x hx => by simp [hx])
        _ = 0 := by simp
    simp [hi, hent, hS]
  have hSp : 0 < ∫ x, F x ∂P := lt_of_le_of_ne hS0 (Ne.symm hS)
  let Q := normalizedTilt P F
  let _ : IsProbabilityMeasure Q := normalizedTilt_probability hF0 hFi hSp
  have hq : Measurable (fun x => F x / ∫ y, F y ∂P) := hF.div_const _
  have hq0 : ∀ᵐ x ∂P, 0 ≤ F x / ∫ y, F y ∂P :=
    hF0.mono fun x hx => div_nonneg hx hS0
  have hqb : ∀ᵐ x ∂P, 0 ≤ F x / ∫ y, F y ∂P ∧
      F x / ∫ y, F y ∂P ≤ B / ∫ y, F y ∂P := by
    filter_upwards [hb] with x hx
    exact ⟨div_nonneg hx.1 hS0, div_le_div_of_nonneg_right hx.2 hS0⟩
  have hv := bounded_tilt_relativeEntropy (P := P) (Q := Q) rfl hq hqb
    (hH.const_mul s) (hH0.mono fun x hx => mul_nonneg hs.le hx) he
  have hiQ : (∫ x, s * H x ∂Q) =
      s / (∫ x, F x ∂P) * ∫ x, F x * H x ∂P := by
    rw [DensityMoments.integral_density (μ := P) (ν := Q) rfl hq hq0]
    calc
      _ = ∫ x, (s / (∫ y, F y ∂P)) * (F x * H x) ∂P :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = _ := integral_const_mul _ _
  have hh := hv.2.2
  rw [hiQ, normalizedTilt_log_integral hF hb] at hh
  have hscaled := mul_le_mul_of_nonneg_left hh hS0
  have hsimp : s * (∫ x, F x * H x ∂P) ≤
      (∫ x, F x * Real.log (F x) ∂P) -
        (∫ x, F x ∂P) * Real.log (∫ x, F x ∂P) +
          Real.log (∫ x, Real.exp (s * H x) ∂P) * (∫ x, F x ∂P) := by
    field_simp at hscaled
    nlinarith only [hscaled]
  have hlog := Real.log_le_log (integral_exp_pos he) hK
  have hlogscaled := mul_le_mul_of_nonneg_right hlog hS0
  rw [entropy_eq_integral hF0 hFlog, ← EReal.coe_add]
  exact_mod_cast hsimp.trans (by linarith only [hlogscaled])

/-- The precise real square-entropy inequality, including zero square mass.
Only the stated positive exponential moment is assumed. -/
theorem weighted_square [IsProbabilityMeasure P] {G F : α → ℝ}
    (hG : Measurable G) {M : ℝ} (hb : ∀ᵐ x ∂P, |G x| ≤ M)
    (hF : Measurable F) {s K : ℝ} (hs : 0 < s)
    (he : Integrable (fun x => Real.exp (s * F x ^ 2)) P)
    (hK : (∫ x, Real.exp (s * F x ^ 2) ∂P) ≤ K) :
    Integrable (fun x => G x ^ 2 * F x ^ 2) P ∧
      (∫ x, G x ^ 2 * F x ^ 2 ∂P) ≤
        s⁻¹ * (Rothaus.squareEntropy P G + Real.log K * ∫ x, G x ^ 2 ∂P) := by
  have hGb : ∀ᵐ x ∂P, 0 ≤ G x ^ 2 ∧ G x ^ 2 ≤ M ^ 2 := by
    filter_upwards [hb] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have hh := mul_self_le_mul_self (abs_nonneg (G x)) hx
    nlinarith only [hh, sq_abs (G x)]
  have hFi : ∀ᵐ x ∂P, 0 ≤ F x ^ 2 := Eventually.of_forall fun x => sq_nonneg _
  have hi := (weighted_integrable (hG.pow_const 2) hGb (hF.pow_const 2) hFi hs he).2
  have hh := weighted_entropy (hG.pow_const 2) hGb (hF.pow_const 2) hFi hs he hK
  rw [entropy_eq_integral (hGb.mono fun _ hx => hx.1)
    (bounded_density_integrable (hG.pow_const 2) hGb).2, ← EReal.coe_add] at hh
  have hr : s * (∫ x, G x ^ 2 * F x ^ 2 ∂P) ≤
      Rothaus.squareEntropy P G + Real.log K * ∫ x, G x ^ 2 ∂P := by
    exact_mod_cast hh
  refine ⟨hi, ?_⟩
  calc
    _ = s⁻¹ * (s * ∫ x, G x ^ 2 * F x ^ 2 ∂P) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr hs.le)

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions ConditionalLawEstimates
  BoundaryCovarianceSplitting MovingPoleNumerators MovingPoleCharts GreenPointWeights
  GreenGradientOscillation ResidualFarExponential ResidualNearExponential ReferenceResidual
  CrossingConcentration

section Source

variable {n J : ℕ} {β β₀ t C₂ : ℝ} (hN : 2 ≤ n + 1)
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
  (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
  (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
  (hadm : AdjacentAdmissible (mesh_pos hmesh) t η i a r)

include hN hβ hβ₀ hsub hC hk hmeshY ht htC hcap hscale hsmall hadm

/-- The actual source weighted square inequality, with concentration and
all integrability discharged for the original law and original observable. -/
theorem crossing_weighted_entropy {G : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := BoundaryCovarianceSplitting.crossingProbability hJ i a r β
    Integrable (fun X => G X ^ 2 * (q X - p) ^ 2) P ∧
      (∫ X, G X ^ 2 * (q X - p) ^ 2 ∂P) ≤
        (16 * quadraticConstant J β₀ t C₂ / (n + 1 : ℕ)) *
          (Rothaus.squareEntropy P G + Real.log (squareConstant J β₀ t C₂) * ∫ X, G X ^ 2 ∂P) := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let q := BoundaryCovarianceSplitting.crossingProbability hJ i a r β
  let s : ℝ := (n + 1 : ℕ) / (16 * quadraticConstant J β₀ t C₂)
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hs : 0 < s := div_pos (by positivity) (mul_pos (by norm_num) (quadraticConstant_pos _ _ _ _))
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set (Configuration (n + 1)))).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  have hb : ∀ᵐ X ∂P, |G X| ≤ M := Eventually.of_forall fun X => by
    simpa only [Real.norm_eq_abs] using hM X (mem_univ X)
  have hc := crossing_square_exponential hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall η i a r hadm
  have heq : (fun X => Real.exp (s * (q X - p) ^ 2)) =
      fun X => Real.exp ((n + 1 : ℕ) * (q X - p) ^ 2 / (16 * quadraticConstant J β₀ t C₂)) := by
    funext X
    congr 1
    dsimp [s]
    ring
  have he : Integrable (fun X => Real.exp (s * (q X - p) ^ 2)) P := by
    rw [heq]
    exact hc.1
  have hK : (∫ X, Real.exp (s * (q X - p) ^ 2) ∂P) ≤ squareConstant J β₀ t C₂ := by
    rw [heq]
    exact hc.2
  have hw := weighted_square hG.continuous.measurable hb
    ((CrossingComponentMeans.measurable_crossing hJ η i a r β).sub_const p) hs he hK
  have hinv : s⁻¹ = 16 * quadraticConstant J β₀ t C₂ / (n + 1 : ℕ) := by
    simp only [s, inv_div]
  simpa only [hinv] using hw

/-- Substituting the actual two-cell entropy comparison gives the source
weighted fluctuation bound in physical energy and square mass only. -/
theorem crossing_weighted_energy {G : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith L G) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := BoundaryCovarianceSplitting.crossingProbability hJ i a r β
    (∫ X, G X ^ 2 * (q X - p) ^ 2 ∂P) ≤
      (16 * quadraticConstant J β₀ t C₂ / (n + 1 : ℕ)) *
        (ConditionalLogSobolev.coefficient J β₀ C₂ *
          (∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂P) +
          (Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂)) * ∫ X, G X ^ 2 ∂P) := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let P := twoCellGibbsMeasure hJ η i a b β
  have hab : a ≠ b := Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    hab hβ (hβ₀.trans_lt hsub)
  have hi := TwoCellEntropy.twoCell_integrable hJ (mesh_three_le hmesh) hN η i hab
    hβ (hβ₀.trans_lt hsub) hG.lift.lipschitzOnWith hG.lift.lipschitzOnWith
  have hE := TwoCellEntropy.twoCell_entropy_le hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall η i a b (edgeAdjacent_nextCell J hJ a r) hadm hG
  rw [entropy_eq_integral (Eventually.of_forall fun X => sq_nonneg (G X)) hi.2.1] at hE
  have hEr : Rothaus.squareEntropy P G ≤ ConditionalLogSobolev.coefficient J β₀ C₂ *
      (∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂P) +
        Real.log (2 / lowerBound β₀) * ∫ X, G X ^ 2 ∂P := by
    exact_mod_cast hE
  have hw := (crossing_weighted_entropy hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall η i a r hadm hG).2
  refine hw.trans ?_
  apply mul_le_mul_of_nonneg_left _ (div_nonneg
    (mul_nonneg (by norm_num) (quadraticConstant_pos _ _ _ _).le) (by positivity))
  nlinarith only [hEr]

end Source

end PeriodicAttractiveLogGas.WeightedSquareEntropy
