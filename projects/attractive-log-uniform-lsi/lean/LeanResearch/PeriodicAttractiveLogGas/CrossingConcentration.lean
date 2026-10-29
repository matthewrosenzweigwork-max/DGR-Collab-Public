import LeanResearch.PeriodicAttractiveLogGas.CrossingComponentMeans
import LeanResearch.PeriodicAttractiveLogGas.ConditionalHerbst
import LeanResearch.PeriodicAttractiveLogGas.GaussianSquareMoment

/-! Source lines 2874–2933: concentration of the original crossing
probability under the actual two-cell Gibbs law. Component logarithmic
Sobolev inequalities are used separately; no mixture LSI is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace PeriodicAttractiveLogGas.CrossingConcentration

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions OneCoordinateConditionals
open BoundaryCovarianceSplitting ConditionalSourceDerivatives ConditionalLawEstimates
open ConditionalVarianceAssembly CollectiveGradientBounds CrossingComponentMeans
open MovingPoleNumerators MovingPoleCharts DeletedConditionalPoincare GreenPointWeights

variable {n J : ℕ}

/-- Each actual component closed product is contained in the actual
closed adjacent product, including edges crossing a torus seam. -/
theorem component_closed_subset (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2) (c : MeshIndex J)
    (hc : c = a ∨ c = nextCell J hJ a r) :
    (Set.pi univ fun k => closure (meshCell J hJ (Function.update η i c k))) ⊆
      closedPatchProduct hJ (Function.update η i a) (OneCoordinateConditionals.adjacentShapes i r) := by
  intro X hX k _
  by_cases hki : k = i
  · subst k
    simp only [OneCoordinateConditionals.adjacentShapes, Function.update_self]
    have hx := hX i (mem_univ i)
    simp only [Function.update_self] at hx
    change X i ∈ closure (edgeCellUnion J hJ a r)
    rcases hc with hc | hc
    · rw [hc] at hx
      exact closure_mono (show meshCell J hJ a ⊆ edgeCellUnion J hJ a r from
        subset_union_left) hx
    · rw [hc] at hx
      exact closure_mono (show meshCell J hJ (nextCell J hJ a r) ⊆ edgeCellUnion J hJ a r from
        subset_union_right) hx
  · have hx := hX k (mem_univ k)
    simpa only [closedPatchProduct, OneCoordinateConditionals.adjacentShapes, Function.update_of_ne hki, OneCoordinateConditionals.patchDomain,
      LocalPointEstimates.shape, TorusPatchDensity.domain] using hx

/-- The original crossing observable is an admissible physical Lipschitz
test on both original component rectangles. -/
theorem component_crossing_lipschitz {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (c : MeshIndex J) (hc : c = a ∨ c = nextCell J (mesh_pos hmesh) a r) :
    ∃ L : ℝ≥0, LipschitzOnWith L
      (fun Z => crossingProbability (mesh_pos hmesh) i a r β (sources Z))
      (closedChart J (Function.update η i c) (fun _ => Patch.cell)) := by
  obtain ⟨L, hL⟩ := twoCell_crossing_lipschitz hβ hβ₀ hδ hmesh η i a r hadm
  refine ⟨L, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro Z hZ W hW
  have hz : sources Z ∈ Set.pi univ (fun k => closure (meshCell J (mesh_pos hmesh)
      (Function.update η i c k))) := by
    intro k _
    exact source_mem_closure_patch (mesh_pos hmesh) _ (fun _ => Patch.cell) hZ k
  have hw : sources W ∈ Set.pi univ (fun k => closure (meshCell J (mesh_pos hmesh)
      (Function.update η i c k))) := by
    intro k _
    exact source_mem_closure_patch (mesh_pos hmesh) _ (fun _ => Patch.cell) hW k
  have he := hL _ (component_closed_subset _ η i a r c hc hz)
    _ (component_closed_subset _ η i a r c hc hw)
  have hJ3 : 3 ≤ J := by omega
  simpa only [Real.dist_eq,
    SourceConditionalEntropyEnergy.closedChart_distance hJ3 (Function.update η i c) hZ hW] using he

/-- A component with a strictly positive finite weight inherits every
almost-everywhere property of its genuine mixture. -/
theorem component_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    {μ ν ρ : Measure Ω} {p q : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤)
    (hmix : μ = p • ν + q • ρ) : ν ≪ μ := by
  have hle : p • ν ≤ μ := by
    rw [hmix]
    intro s
    rw [Measure.add_apply]
    exact le_add_of_nonneg_right bot_le
  have hh := smul_le_smul_left p⁻¹ hle
  have hd : ν ≤ p⁻¹ • μ := by
    simpa only [smul_smul, ENNReal.inv_mul_cancel hp hpt, one_smul] using hh
  exact Measure.absolutelyContinuous_of_le_smul hd

/-- Both original component measures are absolutely continuous with respect
to the actual two-cell law; positivity follows from the source mixing range. -/
theorem component_law_absolutelyContinuous {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (c : MeshIndex J) (hc : c = a ∨ c = nextCell J (mesh_pos hmesh) a r) :
    labelGibbsMeasure (mesh_pos hmesh) (Function.update η i c) β ≪
      twoCellGibbsMeasure (mesh_pos hmesh) η i a (nextCell J (mesh_pos hmesh) a r) β := by
  let hJ := mesh_pos hmesh
  let b := nextCell J hJ a r
  let p := (twoCellMixingWeight hJ η i a b β).toReal
  have hle := twoCellMixingWeight_le_one hJ hN η i a b hβ (hβ₀.trans_lt hsub)
  have htop : twoCellMixingWeight hJ η i a b β ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
  have hpp : ENNReal.ofReal p = twoCellMixingWeight hJ η i a b β := ENNReal.ofReal_toReal htop
  have hpc : ENNReal.ofReal (1 - p) = 1 - twoCellMixingWeight hJ η i a b β := by
    rw [ENNReal.ofReal_sub 1 ENNReal.toReal_nonneg, ENNReal.ofReal_one, hpp]
  have hmix : twoCellGibbsMeasure hJ η i a b β =
      ENNReal.ofReal p • labelGibbsMeasure hJ (Function.update η i a) β +
      ENNReal.ofReal (1 - p) • labelGibbsMeasure hJ (Function.update η i b) β := by
    rw [hpp, hpc]
    exact twoCellGibbsMeasure_eq_mixture hJ hN η i
      (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hr := LabelRatioTransport.adjacent_mixing_range hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
  change lowerBound β₀ / 2 ≤ p ∧ p ≤ 1 - lowerBound β₀ / 2 at hr
  have hp : 0 < p := by linarith [lowerBound_pos β₀, hr.1]
  have hp' : 0 < 1 - p := by linarith [lowerBound_pos β₀, hr.2]
  rcases hc with rfl | rfl
  · exact component_absolutelyContinuous (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hmix
  · exact component_absolutelyContinuous (ENNReal.ofReal_pos.mpr hp').ne' ENNReal.ofReal_ne_top
      (hmix.trans (add_comm _ _))

/-- The actual full physical energy is bounded on each original component
by the source value CΛ² J²/(16N). No regularity of a zero extension is used. -/
theorem component_crossing_energy {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (c : MeshIndex J) (hc : c = a ∨ c = nextCell J (mesh_pos hmesh) a r) :
    ∀ᵐ X ∂labelGibbsMeasure (mesh_pos hmesh) (Function.update η i c) β,
      BoundaryEdgeSummation.totalEnergyDensity (crossingProbability (mesh_pos hmesh) i a r β) X ≤
        crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant * J ^ 2 /
          (16 * (n + 1 : ℕ)) := by
  have hsource := twoCell_log_crossing_gradient_bounds hN hβ hβ₀ hsub hδ₀.le hδ hmesh η i a r hadm
  have hac := component_law_absolutelyContinuous hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm c hc
  filter_upwards [hac.ae_le hsource] with X hX
  have hn : 0 ≤ crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant * J ^ 2 /
      (4 * (n + 1 : ℕ)) := by
    exact div_nonneg (mul_nonneg (crossingConstantSquared_nonneg β₀ hδ₀.le _) (sq_nonneg _))
      (by positivity)
  have hh := hX.2.trans (mul_le_mul_of_nonneg_left (CrossingLogistic.bernoulli_factor_le _) hn)
  change (∑ k, ‖coordinateOrdinaryGradient (crossingProbability (mesh_pos hmesh) i a r β) k X‖ ^ 2) ≤ _
  convert hh using 1
  ring

/-- Literal source constants, independent of N, actual beta, and edge. -/
def linearConstant (β₀ t : ℝ) : ℝ :=
  finePoincareConstant β₀ * crossingConstantSquared β₀ t GreenCovarianceBounds.hessianConstant /
    (8 * lowerBound β₀)

def quadraticConstant (J : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  max 1 ((J : ℝ) ^ 2 * ConditionalLogSobolev.coefficient J β₀ C₂ *
    crossingConstantSquared β₀ t GreenCovarianceBounds.hessianConstant / 64)

def squareConstant (J : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  2 * Real.exp (linearConstant β₀ t ^ 2 / (8 * quadraticConstant J β₀ t C₂))

theorem quadraticConstant_pos (J : ℕ) (β₀ t C₂ : ℝ) :
    0 < quadraticConstant J β₀ t C₂ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem linearConstant_nonneg (β₀ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ linearConstant β₀ t :=
  div_nonneg (mul_nonneg (finePoincareConstant_nonneg β₀)
    (crossingConstantSquared_nonneg β₀ ht _))
    (mul_nonneg (by norm_num) (lowerBound_pos β₀).le)

open GreenGradientOscillation ResidualFarExponential ResidualNearExponential ReferenceResidual

section Source

variable {β β₀ t C₂ : ℝ} (hN : 2 ≤ n + 1)
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

/-- Both component exponential estimates are consequences of the actual
source conditional LSI and the actual original-q physical energy bound. -/
theorem component_centered_exponential (c : MeshIndex J)
    (hc : c = a ∨ c = nextCell J (mesh_pos hmesh) a r) (lam : ℝ) :
    let Pc := labelGibbsMeasure (mesh_pos hmesh) (Function.update η i c) β
    let q := crossingProbability (mesh_pos hmesh) i a r β
    Integrable (fun X => Real.exp (lam * (q X - ∫ Y, q Y ∂Pc))) Pc ∧
      (∫ X, Real.exp (lam * (q X - ∫ Y, q Y ∂Pc)) ∂Pc) ≤
        Real.exp (quadraticConstant J β₀ t C₂ * lam ^ 2 / (n + 1 : ℕ)) := by
  obtain ⟨L, hL⟩ := component_crossing_lipschitz hβ hβ₀ htC hmesh η i a r hadm c hc
  have hη : OccupationCap t (Function.update η i c) := by
    rcases hc with rfl | rfl
    · exact hadm.1
    · exact hadm.2
  let B := crossingConstantSquared β₀ t GreenCovarianceBounds.hessianConstant * J ^ 2 /
    (16 * (n + 1 : ℕ))
  have hB : 0 ≤ B := div_nonneg
    (mul_nonneg (crossingConstantSquared_nonneg β₀ ht.le _) (sq_nonneg _)) (by positivity)
  have hg := component_crossing_energy hN hβ hβ₀ hsub ht htC hmesh η i a r hadm c hc
  have he := ConditionalHerbst.conditional_centered_exp_le_of_energy_le (mesh_pos hmesh) hN
    hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall
    (Function.update η i c) hη hL hB hg lam
  refine ⟨(ConditionalHerbst.source_exp_integrable (mesh_pos hmesh) (mesh_three_le hmesh)
    hN (Function.update η i c) hβ (hβ₀.trans_lt hsub) hL lam).2.2, he.trans ?_⟩
  apply Real.exp_le_exp.mpr
  calc
    (ConditionalLogSobolev.coefficient J β₀ C₂ * B / 4) * lam ^ 2 =
        ((J : ℝ) ^ 2 * ConditionalLogSobolev.coefficient J β₀ C₂ *
          crossingConstantSquared β₀ t GreenCovarianceBounds.hessianConstant / 64) *
          lam ^ 2 / (n + 1 : ℕ) := by dsimp [B]; ring
    _ ≤ quadraticConstant J β₀ t C₂ * lam ^ 2 / (n + 1 : ℕ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg lam)

/-- The source linear exponential estimate under the actual two-cell law,
with genuine integrability and all component hypotheses discharged. -/
theorem crossing_linear_exponential (lam : ℝ) :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := crossingProbability hJ i a r β
    Integrable (fun X => Real.exp (lam * (q X - p))) P ∧
      (∫ X, Real.exp (lam * (q X - p)) ∂P) ≤
        Real.exp ((|lam| * linearConstant β₀ t + quadraticConstant J β₀ t C₂ * lam ^ 2) /
          (n + 1 : ℕ)) := by
  exact crossing_exponential_transfer hN hβ hβ₀ hsub ht htC hmesh η i a r hadm
    lam (quadraticConstant J β₀ t C₂) (fun c hc => component_centered_exponential hN hβ hβ₀
      hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall η i a r hadm c hc lam)

/-- The source Gaussian/Tonelli square-exponential conclusion, including
finiteness, for the original law and original crossing probability. -/
theorem crossing_square_exponential :
    let hJ := mesh_pos hmesh
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
    let q := crossingProbability hJ i a r β
    Integrable (fun X => Real.exp ((n + 1 : ℕ) * (q X - p) ^ 2 /
      (16 * quadraticConstant J β₀ t C₂))) P ∧
      (∫ X, Real.exp ((n + 1 : ℕ) * (q X - p) ^ 2 /
        (16 * quadraticConstant J β₀ t C₂)) ∂P) ≤ squareConstant J β₀ t C₂ := by
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β
  let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) β).toReal
  let q := crossingProbability hJ i a r β
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
    (Ne.symm (nextCell_ne J hJ (mesh_two_le hmesh) a r)) hβ (hβ₀.trans_lt hsub)
  have hq : Measurable q := measurable_crossing hJ η i a r β
  have hb : ∀ᵐ X ∂P, |q X - p| ≤ 1 + |p| := Eventually.of_forall fun X => by
    calc
      |q X - p| ≤ |q X| + |p| := abs_sub _ _
      _ ≤ 1 + |p| := add_le_add (by
        rw [abs_of_nonneg (crossing_bounds hJ i a r β X).1]
        exact (crossing_bounds hJ i a r β X).2) le_rfl
  exact GaussianSquareMoment.square_exponential_of_linear (hq.sub_const p) hb
    (by exact_mod_cast (show 1 ≤ n + 1 by omega)) (quadraticConstant_pos J β₀ t C₂)
    (fun lam => (crossing_linear_exponential hN hβ hβ₀ hsub hC hk hmesh hmeshY ht htC
      hcap hscale hsmall η i a r hadm lam).2)

end Source

/-- At zero coupling the original crossing probability is identically one
half, since the conditional law is the equal cell mixture. -/
theorem crossingProbability_zero (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2) (X : Configuration (n + 1)) :
    crossingProbability hJ i a r 0 X = 1 / 2 := by
  unfold crossingProbability
  rw [conditionalKernel_zero]
  have hh := congrArg (fun μ : Measure Torus => μ univ)
    (LabelRatioTransport.edgeCellMeasure_restrict_first hJ hJ2 a r)
  simp only [Measure.restrict_apply_univ, Measure.smul_apply, smul_eq_mul,
    meshCellMeasure_univ, mul_one] at hh
  change ((edgeCellMeasure J hJ a r) (meshCell J hJ a)).toReal = 1 / 2
  rw [hh]
  norm_num

/-- Both original zero-coupling exponential integrals are exactly one.
In particular beta0=0 is retained by the source bounds above. -/
theorem zero_coupling_exponentials (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (lam c₂ : ℝ) :
    let P := twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) 0
    let p := (twoCellMixingWeight hJ η i a (nextCell J hJ a r) 0).toReal
    let q := crossingProbability hJ i a r 0
    (∫ X, Real.exp (lam * (q X - p)) ∂P) = 1 ∧
      (∫ X, Real.exp ((n + 1 : ℕ) * (q X - p) ^ 2 / (16 * c₂)) ∂P) = 1 := by
  let : IsProbabilityMeasure (twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) 0) :=
    isProbabilityMeasure_twoCellGibbsMeasure hJ hN η i
      (Ne.symm (nextCell_ne J hJ hJ2 a r)) (by norm_num) (by norm_num)
  simp only [crossingProbability_zero hJ hJ2, LabelRatioTransport.mixing_weight_zero,
    sub_self, mul_zero, Real.exp_zero, zero_pow (by omega : 2 ≠ 0), zero_div,
    integral_const, probReal_univ, one_smul, and_self]

end PeriodicAttractiveLogGas.CrossingConcentration
