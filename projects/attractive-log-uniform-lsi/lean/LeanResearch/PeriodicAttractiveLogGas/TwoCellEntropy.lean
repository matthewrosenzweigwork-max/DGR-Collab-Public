import LeanResearch.PeriodicAttractiveLogGas.ConditionalLogSobolev
import LeanResearch.PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

/-! The actual two-cell entropy comparison in source lines 2986--2999.
The binary entropy and the mixture chain rule are proved here; the final
comparison applies the existing LSI to the original two component laws.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.TwoCellEntropy

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions ConditionalLawEstimates
  BoundaryCovarianceSplitting MovingPoleNumerators MovingPoleCharts GreenPointWeights
  SourceConditionalEntropyEnergy ConditionalEntropyTightening SourceEntropyTests

/-- The finite binary entropy expression with the source zero convention. -/
def binaryEntropy (p a b : ℝ) : ℝ :=
  p * a * Real.log a + (1 - p) * b * Real.log b -
    (p * a + (1 - p) * b) * Real.log (p * a + (1 - p) * b)

private theorem weighted_log_le {w a S d : ℝ} (ha : 0 ≤ a) (hd : 0 < d)
    (hdw : d ≤ w) (hpart : w * a ≤ S) :
    w * a * Real.log a ≤ w * a * (Real.log S + Real.log (1 / d)) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  have hw : 0 < w := hd.trans_le hdw
  have hS : 0 < S := (mul_pos hw ha).trans_le hpart
  have haS : a ≤ S / d := (le_div_iff₀ hd).mpr (by
    calc
      a * d ≤ a * w := mul_le_mul_of_nonneg_left hdw ha.le
      _ = w * a := mul_comm _ _
      _ ≤ S := hpart)
  have hh := Real.log_le_log ha haS
  rw [Real.log_div hS.ne' hd.ne', Real.log_div one_ne_zero hd.ne', Real.log_one] at *
  have hh' : Real.log a ≤ Real.log S + (0 - Real.log d) := by linarith only [hh]
  exact mul_le_mul_of_nonneg_left hh' (mul_nonneg hw.le ha.le)

/-- The exact finite probability estimate used by the source, including
zero total mass and either zero component mass. No normalization by mass
is performed, so those cases do not need an extra positive-mass premise. -/
theorem binaryEntropy_le {p a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : 0 < d) (hda : d ≤ p) (hdb : d ≤ 1 - p) :
    binaryEntropy p a b ≤ Real.log (1 / d) * (p * a + (1 - p) * b) := by
  have hp : 0 ≤ p := hd.le.trans hda
  have hq : 0 ≤ 1 - p := hd.le.trans hdb
  have hleft := weighted_log_le ha hd hda
    (le_add_of_nonneg_right (mul_nonneg hq hb))
  have hright := weighted_log_le hb hd hdb
    (le_add_of_nonneg_left (mul_nonneg hp ha))
  unfold binaryEntropy
  nlinarith only [hleft, hright]

section Mixture

variable {Ω : Type*} [MeasurableSpace Ω] {P Pa Pb : Measure Ω}
  {c : ℝ≥0∞} {G : Ω → ℝ}

theorem integrable_mixture (hc : c ≤ 1) (hmix : P = c • Pa + (1 - c) • Pb)
    {f : Ω → ℝ} (ha : Integrable f Pa) (hb : Integrable f Pb) : Integrable f P := by
  rw [hmix]
  exact (ha.smul_measure (ne_top_of_le_ne_top (by simp) hc)).add_measure
    (hb.smul_measure (by finiteness))

/-- Literal finite integral algebra for the genuine mixture. -/
theorem squareEntropy_mixture (hc : c ≤ 1) (hmix : P = c • Pa + (1 - c) • Pb)
    (ha : Integrable (fun x => G x ^ 2) Pa) (hb : Integrable (fun x => G x ^ 2) Pb)
    (halog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) Pa)
    (hblog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) Pb) :
    Rothaus.squareEntropy P G = c.toReal * Rothaus.squareEntropy Pa G +
      (1 - c.toReal) * Rothaus.squareEntropy Pb G +
      binaryEntropy c.toReal (∫ x, G x ^ 2 ∂Pa) (∫ x, G x ^ 2 ∂Pb) := by
  unfold Rothaus.squareEntropy
  rw [integral_two_label_mixture hc hmix halog hblog, integral_two_label_mixture hc hmix ha hb]
  unfold binaryEntropy
  ring

/-- The true extended entropy chain rule for the same two component laws.
Finiteness of all three entropies is established from the displayed genuine
log-integrability hypotheses before any EReal algebra is used. -/
theorem entropy_mixture [IsFiniteMeasure P] [IsFiniteMeasure Pa] [IsFiniteMeasure Pb]
    (hc : c ≤ 1) (hmix : P = c • Pa + (1 - c) • Pb)
    (ha : Integrable (fun x => G x ^ 2) Pa) (hb : Integrable (fun x => G x ^ 2) Pb)
    (halog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) Pa)
    (hblog : Integrable (fun x => G x ^ 2 * Real.log (G x ^ 2)) Pb) :
    entropy P (fun x => G x ^ 2) =
      (c.toReal : EReal) * entropy Pa (fun x => G x ^ 2) +
      ((1 - c.toReal : ℝ) : EReal) * entropy Pb (fun x => G x ^ 2) +
      (binaryEntropy c.toReal (∫ x, G x ^ 2 ∂Pa) (∫ x, G x ^ 2 ∂Pb) : EReal) := by
  have hn (μ : Measure Ω) : 0 ≤ᵐ[μ] fun x => G x ^ 2 :=
    Eventually.of_forall fun x => sq_nonneg _
  have hPlog := integrable_mixture hc hmix halog hblog
  rw [entropy_eq_integral (hn P) hPlog, entropy_eq_integral (hn Pa) halog,
    entropy_eq_integral (hn Pb) hblog, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add, ← EReal.coe_add]
  exact congrArg (fun x : ℝ => (x : EReal)) (squareEntropy_mixture hc hmix ha hb halog hblog)

end Mixture

/-- The literal probability on the two component labels. -/
def binaryLaw (c : ℝ≥0∞) : Measure Bool :=
  c • Measure.dirac true + (1 - c) • Measure.dirac false

theorem binaryLaw_probability {c : ℝ≥0∞} (hc : c ≤ 1) :
    IsProbabilityMeasure (binaryLaw c) := by
  constructor
  simp only [binaryLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le hc

/-- The displayed binary expression is the actual entropy of the finite
two-atom probability, including vanishing values of either observable. -/
theorem binaryEntropy_eq_entropy {c : ℝ≥0∞} (hc : c ≤ 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    entropy (binaryLaw c) (fun x : Bool => cond x a b) =
      (binaryEntropy c.toReal a b : EReal) := by
  let : IsProbabilityMeasure (binaryLaw c) := binaryLaw_probability hc
  have hi (f : Bool → ℝ) : Integrable f (binaryLaw c) :=
    integrable_mixture hc rfl (integrable_dirac (by simp)) (integrable_dirac (by simp))
  have hn : 0 ≤ᵐ[binaryLaw c] (fun x : Bool => cond x a b) :=
    Eventually.of_forall fun x => by cases x <;> simp [ha, hb]
  have hm : (∫ x : Bool, cond x a b ∂binaryLaw c) = c.toReal * a + (1 - c.toReal) * b := by
    simpa only [integral_dirac, Bool.cond_true, Bool.cond_false] using
      integral_two_label_mixture hc (show binaryLaw c = _ from rfl)
        (integrable_dirac (a := true) (f := fun x : Bool => cond x a b) (by simp))
        (integrable_dirac (a := false) (f := fun x : Bool => cond x a b) (by simp))
  have hl : (∫ x : Bool, cond x a b * Real.log (cond x a b) ∂binaryLaw c) =
      c.toReal * (a * Real.log a) + (1 - c.toReal) * (b * Real.log b) := by
    simpa only [integral_dirac, Bool.cond_true, Bool.cond_false] using
      integral_two_label_mixture hc (show binaryLaw c = _ from rfl)
        (integrable_dirac (a := true) (f := fun x : Bool => cond x a b * Real.log (cond x a b)) (by
          simp
          exact ENNReal.mul_lt_top (by simp) (by simp)))
        (integrable_dirac (a := false) (f := fun x : Bool => cond x a b * Real.log (cond x a b)) (by
          simp
          exact ENNReal.mul_lt_top (by simp) (by simp)))
  rw [entropy_eq_integral hn (hi _), hm, hl]
  congr 1
  unfold binaryEntropy
  ring

theorem binary_entropy_le {c : ℝ≥0∞} (hc : c ≤ 1) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (hda : d ≤ c.toReal) (hdb : d ≤ 1 - c.toReal) :
    entropy (binaryLaw c) (fun x : Bool => cond x a b) ≤
      ((Real.log (1 / d) * (c.toReal * a + (1 - c.toReal) * b) : ℝ) : EReal) := by
  rw [binaryEntropy_eq_entropy hc ha hb]
  exact EReal.coe_le_coe_iff.mpr (binaryEntropy_le ha hb hd hda hdb)

/-- All square, entropy-density and physical-energy integrals in the actual
two-cell calculation are finite, from the original two local test classes. -/
theorem twoCell_integrable {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    (η : LabelVector J N) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) {G : Configuration N → ℝ} {Ca Cb : ℝ≥0}
    (hGa : LipschitzOnWith Ca (fun Z => G (sources Z))
      (closedChart J (Function.update η i a) (fun _ => Patch.cell)))
    (hGb : LipschitzOnWith Cb (fun Z => G (sources Z))
      (closedChart J (Function.update η i b) (fun _ => Patch.cell))) :
    Integrable (fun X => G X ^ 2) (twoCellGibbsMeasure hJ η i a b β) ∧
      Integrable (fun X => G X ^ 2 * Real.log (G X ^ 2)) (twoCellGibbsMeasure hJ η i a b β) ∧
      Integrable (BoundaryEdgeSummation.totalEnergyDensity G) (twoCellGibbsMeasure hJ η i a b β) := by
  have ha := source_square_integrable hJ hJ3 hN (Function.update η i a) hβ hsub hGa
  have hb := source_square_integrable hJ hJ3 hN (Function.update η i b) hβ hsub hGb
  have hc := twoCellMixingWeight_le_one hJ hN η i a b hβ hsub
  have hm := twoCellGibbsMeasure_eq_mixture hJ hN η i hab hβ hsub
  exact ⟨integrable_mixture hc hm ha.1 hb.1, integrable_mixture hc hm ha.2 hb.2,
    integrable_mixture hc hm
      (source_full_energy_integrable hJ hJ3 hN (Function.update η i a) hβ hsub hGa)
      (source_full_energy_integrable hJ hJ3 hN (Function.update η i b) hβ hsub hGb)⟩

/-- Source entropy chain with the original two-cell event and its actual
Gibbs mixing weight. There is no positivity assumption on any square mass. -/
theorem twoCell_entropy_chain {J N : ℕ} (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    (η : LabelVector J N) (i : Fin N) {a b : MeshIndex J} (hab : a ≠ b)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) {G : Configuration N → ℝ} {Ca Cb : ℝ≥0}
    (hGa : LipschitzOnWith Ca (fun Z => G (sources Z))
      (closedChart J (Function.update η i a) (fun _ => Patch.cell)))
    (hGb : LipschitzOnWith Cb (fun Z => G (sources Z))
      (closedChart J (Function.update η i b) (fun _ => Patch.cell))) :
    let c := twoCellMixingWeight hJ η i a b β
    let Pa := labelGibbsMeasure hJ (Function.update η i a) β
    let Pb := labelGibbsMeasure hJ (Function.update η i b) β
    entropy (twoCellGibbsMeasure hJ η i a b β) (fun X => G X ^ 2) =
      (c.toReal : EReal) * entropy Pa (fun X => G X ^ 2) +
      ((1 - c.toReal : ℝ) : EReal) * entropy Pb (fun X => G X ^ 2) +
      entropy (binaryLaw c) (fun k : Bool => cond k (∫ X, G X ^ 2 ∂Pa) (∫ X, G X ^ 2 ∂Pb)) := by
  let : IsProbabilityMeasure (twoCellGibbsMeasure hJ η i a b β) :=
    isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i hab hβ hsub
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i a) hβ hsub
  let := isProbabilityMeasure_labelGibbsMeasure hJ hN (Function.update η i b) hβ hsub
  have ha := source_square_integrable hJ hJ3 hN (Function.update η i a) hβ hsub hGa
  have hb := source_square_integrable hJ hJ3 hN (Function.update η i b) hβ hsub hGb
  have hc := twoCellMixingWeight_le_one hJ hN η i a b hβ hsub
  dsimp only
  rw [binaryEntropy_eq_entropy hc (integral_nonneg fun _ => sq_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)]
  exact entropy_mixture hc (twoCellGibbsMeasure_eq_mixture hJ hN η i hab hβ hsub) ha.1 hb.1 ha.2 hb.2

/-- Both mixing weights have their source lower bound for every original
particle number. The adjacency predicate includes the opposite orientation. -/
theorem edge_mixing_range {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
    {β β₀ t : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
    (he : EdgeAdjacent J hJ a b) (hadm : TwoEndpointAdmissible t η i a b) :
    let p := (twoCellMixingWeight hJ η i a b β).toReal
    lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 := by
  cases N with
  | zero => omega
  | succ n =>
    exact LabelRatioTransport.edgeAdjacent_mixing_range hN hβ hβ₀ hsub ht htC hmesh η i a b he hadm

open GreenGradientOscillation ResidualFarExponential ResidualNearExponential ReferenceResidual

section Source

variable {J N : ℕ} (hJ : 0 < J) (hN : 2 ≤ N)
  {β β₀ t C₂ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
  (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
  (η : LabelVector J N) (i : Fin N) (a b : MeshIndex J)
  (he : EdgeAdjacent J hJ a b) (hadm : TwoEndpointAdmissible t η i a b)

include hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall he hadm

/-- Source lines 2986--2999 for the actual two-cell Gibbs law. The component
LSIs are the already-proved source theorem, not hypotheses on this mixture. -/
theorem twoCell_entropy_le_local {G : Configuration N → ℝ} {Ca Cb : ℝ≥0}
    (hGa : LipschitzOnWith Ca (fun Z => G (sources Z))
      (closedChart J (Function.update η i a) (fun _ => Patch.cell)))
    (hGb : LipschitzOnWith Cb (fun Z => G (sources Z))
      (closedChart J (Function.update η i b) (fun _ => Patch.cell))) :
    entropy (twoCellGibbsMeasure hJ η i a b β) (fun X => G X ^ 2) ≤
      ((ConditionalLogSobolev.coefficient J β₀ C₂ *
          (∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂twoCellGibbsMeasure hJ η i a b β) +
        Real.log (2 / lowerBound β₀) * (∫ X, G X ^ 2 ∂twoCellGibbsMeasure hJ η i a b β) : ℝ) : EReal) := by
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  have hab : a ≠ b := he.ne (by omega)
  have hbsub := hβ₀.trans_lt hsub
  let P := twoCellGibbsMeasure hJ η i a b β
  let Pa := labelGibbsMeasure hJ (Function.update η i a) β
  let Pb := labelGibbsMeasure hJ (Function.update η i b) β
  let c := twoCellMixingWeight hJ η i a b β
  let p : ℝ := c.toReal
  let K : ℝ := ConditionalLogSobolev.coefficient J β₀ C₂
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i hab hβ hbsub
  let : IsProbabilityMeasure Pa := isProbabilityMeasure_labelGibbsMeasure hJ hN _ hβ hbsub
  let : IsProbabilityMeasure Pb := isProbabilityMeasure_labelGibbsMeasure hJ hN _ hβ hbsub
  have ha := source_square_integrable hJ hJ3 hN (Function.update η i a) hβ hbsub hGa
  have hb := source_square_integrable hJ hJ3 hN (Function.update η i b) hβ hbsub hGb
  have hEa : Integrable (BoundaryEdgeSummation.totalEnergyDensity G) Pa :=
    source_full_energy_integrable hJ hJ3 hN (Function.update η i a) hβ hbsub hGa
  have hEb : Integrable (BoundaryEdgeSummation.totalEnergyDensity G) Pb :=
    source_full_energy_integrable hJ hJ3 hN (Function.update η i b) hβ hbsub hGb
  have hc : c ≤ 1 := twoCellMixingWeight_le_one hJ hN η i a b hβ hbsub
  have hm : P = c • Pa + (1 - c) • Pb := twoCellGibbsMeasure_eq_mixture hJ hN η i hab hβ hbsub
  have hr : lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 :=
    edge_mixing_range hJ hN hβ hβ₀ hsub ht htC hmesh η i a b he hadm
  have hd : 0 < lowerBound β₀ / 2 := div_pos (lowerBound_pos β₀) (by norm_num)
  have hp : 0 ≤ p := hd.le.trans hr.1
  have hq : 0 ≤ 1 - p := by linarith only [hd, hr.2]
  have hLa := ConditionalLogSobolev.conditional_lsi hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall (Function.update η i a) hadm.1 hGa
  have hLb := ConditionalLogSobolev.conditional_lsi hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall (Function.update η i b) hadm.2 hGb
  rw [local_entropy_eq hJ hJ3 hN (Function.update η i a) hβ hbsub hGa] at hLa
  rw [local_entropy_eq hJ hJ3 hN (Function.update η i b) hβ hbsub hGb] at hLb
  have hLa' : Rothaus.squareEntropy Pa G ≤ K * ∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂Pa := by
    exact_mod_cast hLa
  have hLb' : Rothaus.squareEntropy Pb G ≤ K * ∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂Pb := by
    exact_mod_cast hLb
  have hbin : binaryEntropy p (∫ X, G X ^ 2 ∂Pa) (∫ X, G X ^ 2 ∂Pb) ≤
      Real.log (1 / (lowerBound β₀ / 2)) *
        (p * (∫ X, G X ^ 2 ∂Pa) + (1 - p) * (∫ X, G X ^ 2 ∂Pb)) :=
    binaryEntropy_le (integral_nonneg fun X => sq_nonneg (G X))
      (integral_nonneg fun X => sq_nonneg (G X)) hd hr.1 (by linarith only [hr.2])
  have hlog : Real.log (1 / (lowerBound β₀ / 2)) = Real.log (2 / lowerBound β₀) := by
    congr 1
    field_simp [(lowerBound_pos β₀).ne']
  rw [hlog] at hbin
  have hchain := squareEntropy_mixture hc hm ha.1 hb.1 ha.2 hb.2
  have hmass := integral_two_label_mixture hc hm ha.1 hb.1
  have henergy := integral_two_label_mixture hc hm hEa hEb
  have hn : 0 ≤ᵐ[P] (fun X => G X ^ 2) := Eventually.of_forall fun _ => sq_nonneg _
  rw [entropy_eq_integral hn (integrable_mixture hc hm ha.2 hb.2)]
  apply EReal.coe_le_coe_iff.mpr
  change Rothaus.squareEntropy P G ≤ K * (∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂P) +
    Real.log (2 / lowerBound β₀) * (∫ X, G X ^ 2 ∂P)
  rw [hchain]
  calc
    _ ≤ p * (K * ∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂Pa) +
        (1 - p) * (K * ∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂Pb) +
        Real.log (2 / lowerBound β₀) *
          (p * (∫ X, G X ^ 2 ∂Pa) + (1 - p) * (∫ X, G X ^ 2 ∂Pb)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hLa' hp)
        (mul_le_mul_of_nonneg_left hLb' hq)) hbin
    _ = _ := by rw [hmass, henergy]; ring

/-- The manuscript's global physical Lipschitz class is contained in both
component classes, with no loss in any final coefficient. -/
theorem twoCell_entropy_le {G : Configuration N → ℝ} {C : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith C G) :
    entropy (twoCellGibbsMeasure hJ η i a b β) (fun X => G X ^ 2) ≤
      ((ConditionalLogSobolev.coefficient J β₀ C₂ *
          (∫ X, BoundaryEdgeSummation.totalEnergyDensity G X ∂twoCellGibbsMeasure hJ η i a b β) +
        Real.log (2 / lowerBound β₀) * (∫ X, G X ^ 2 ∂twoCellGibbsMeasure hJ η i a b β) : ℝ) : EReal) := by
  apply twoCell_entropy_le_local hJ hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall η i a b he hadm
  · exact hG.lift.lipschitzOnWith
  · exact hG.lift.lipschitzOnWith

end Source

end PeriodicAttractiveLogGas.TwoCellEntropy
