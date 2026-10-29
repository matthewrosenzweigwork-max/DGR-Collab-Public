import LeanResearch.PeriodicAttractiveLogGas.WeightedSquareEntropy
import LeanResearch.PeriodicAttractiveLogGas.EntropyBoundarySummation
import LeanResearch.PeriodicAttractiveLogGas.BoundaryComparison
import LeanResearch.PeriodicAttractiveLogGas.EntropyEdgeSplitting

/-! Actual entropy boundary comparison, source eq:entropy-single-edge and
eq:entropy-boundary-constants. Physical gradient energy is unscaled. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.EntropyBoundaryComparison

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions
open ConditionalLawEstimates ConditionalVarianceAssembly BoundaryEdgeSummation
open DiscreteOccupationIdentities EntropyBoundarySummation CrossingConcentration
open MovingPoleNumerators MovingPoleCharts GreenPointWeights GreenGradientOscillation
open ResidualFarExponential ResidualNearExponential ReferenceResidual

/-- The physical single-edge density has the literal source integral.
All integrability gates follow from the given global physical Lipschitz test. -/
theorem integral_edgeDensity {N J : ℕ} {μ : Measure (Configuration N)}
    [IsFiniteMeasure μ] {G : Configuration N → ℝ} {C : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith C G) (i : Fin N) (A B K L : ℝ) :
    (∫ X, entropyEdgeDensity J A B K L G i X ∂μ) =
      (A / (J : ℝ) ^ 2) * (∫ X, coordinateEnergy G i X ∂μ) +
        (B / N) * (K * (∫ X, totalEnergyDensity G X ∂μ) +
          L * ∫ X, G X ^ 2 ∂μ) := by
  have hi : Integrable (fun X => coordinateEnergy G i X) μ :=
    integrable_coordinate_energy hG μ i
  have hk : Integrable (fun X => K * totalEnergyDensity G X) μ :=
    (integrable_totalEnergyDensity hG).const_mul K
  have hl : Integrable (fun X => L * G X ^ 2) μ := (integrable_square hG).const_mul L
  have hsum : Integrable (fun X => K * totalEnergyDensity G X + L * G X ^ 2) μ :=
    hk.add hl
  unfold entropyEdgeDensity
  rw [integral_add (hi.const_mul _) (hsum.const_mul _),
    integral_const_mul, integral_const_mul, integral_add hk hl,
    integral_const_mul, integral_const_mul]

/-- The normalized quadratic edge quantity is invariant under reversal
of the actual outer graph edge. This uses the genuine conductance identity
and the strictly positive original component masses. -/
theorem mixing_square_symm {N J : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    (F : LabelState J N t → ℝ) (η ζ : LabelState J N t) (i : Fin N)
    (he : CoordinateStep hJ i η ζ) :
    let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
    let p' := (twoCellMixingWeight hJ ζ.val i (ζ.val i) (η.val i) β).toReal
    p' * (1 - p') * (F ζ - F η) ^ 2 = p * (1 - p) * (F η - F ζ) ^ 2 := by
  dsimp only
  have hw : 0 < labelWeight hJ β η + labelWeight hJ β ζ :=
    add_pos (labelWeight_pos hJ hN hβ hsub η) (labelWeight_pos hJ hN hβ hsub ζ)
  apply mul_left_cancel₀ hw.ne'
  have ha := labelTerm_eq_mass_mixing hJ hN hβ hsub F η ζ i he
  have hb := labelTerm_eq_mass_mixing hJ hN hβ hsub F ζ η i he.symm
  dsimp only at ha hb
  rw [labelTerm_symm hJ β F ζ η] at hb
  rw [ha] at hb
  nlinarith only [hb]


section SourceBoundary

variable {J : ℕ} {β β₀ t C₂ : ℝ}
  (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
  (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
  (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
  (ht : 0 < t) (htC : t ≤ occupationBound β₀)
  (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1)
  (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
  (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)

include hβ hβ₀ hsub hC hk hmeshY ht htC hcap hscale hsmall

/-- Source eq:entropy-single-edge for the actual positive orientation.
The original conditional split and weighted square estimate are proved inputs,
rather than assumptions about the observable or its conditional law. -/
theorem positive_label_edge_bound {n : ℕ} (hN : 2 ≤ n + 1)
    {G : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith C G)
    (η ζ : LabelState J (n + 1) t) (i : Fin (n + 1)) (r : Fin 2)
    (he : CoordinateStep (mesh_pos hmesh) i η ζ)
    (hr : ζ.val i = nextCell J (mesh_pos hmesh) (η.val i) r) :
    let hJ := mesh_pos hmesh
    let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
    p * (1 - p) * (labelSquareNorm hJ β G η - labelSquareNorm hJ β G ζ) ^ 2 ≤
      ∫ X, entropyEdgeDensity J (2 * finePoincareConstant β₀ / lowerBound β₀ ^ 2)
        (64 * quadraticConstant J β₀ t C₂ / lowerBound β₀ ^ 3)
        (ConditionalLogSobolev.coefficient J β₀ C₂)
        (Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂)) G i X
        ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β := by
  classical
  let hJ := mesh_pos hmesh
  have hu : Function.update η.val i (η.val i) = η.val := by funext k; simp
  have hadm : AdjacentAdmissible hJ t η.val i (η.val i) r := by
    constructor
    · change OccupationCap t (Function.update η.val i (η.val i))
      rw [hu]
      exact η.property
    · change OccupationCap t (Function.update η.val i (nextCell J hJ (η.val i) r))
      rw [← hr, he.2]
      exact ζ.property
  have hs := EntropyEdgeSplitting.single_edge_entropy_split hN hβ hβ₀ hsub ht htC hmesh
    η.val i (η.val i) r hadm hG
  have hw := WeightedSquareEntropy.crossing_weighted_energy hN hβ hβ₀ hsub hC hk hmesh hmeshY
    ht htC hcap hscale hsmall η.val i (η.val i) r hadm hG
  dsimp only at hs hw ⊢
  have hc := lowerBound_pos β₀
  have hb := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 4 / lowerBound β₀ ^ 3)
  have hh := hs.trans (add_le_add_right hb _)
  rw [← hr, hu, he.2] at hh
  let : IsProbabilityMeasure (twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) :=
    isProbabilityMeasure_twoCellGibbsMeasure hJ hN η.val i (he.1.ne (mesh_two_le hmesh))
      hβ (hβ₀.trans_lt hsub)
  rw [integral_edgeDensity hG]
  simp only [labelSquareNorm, coordinateEnergy]
  (convert hh using 1; ring)

/-- All orientations of the actual outer label graph, including periodic
seams, satisfy the same analytic estimate with the original two-cell law. -/
theorem label_edge_bound {n : ℕ} (hN : 2 ≤ n + 1)
    {G : Configuration (n + 1) → ℝ} {C : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith C G)
    (η ζ : LabelState J (n + 1) t) (i : Fin (n + 1))
    (he : CoordinateStep (mesh_pos hmesh) i η ζ) :
    let hJ := mesh_pos hmesh
    let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
    p * (1 - p) * (labelSquareNorm hJ β G η - labelSquareNorm hJ β G ζ) ^ 2 ≤
      ∫ X, entropyEdgeDensity J (2 * finePoincareConstant β₀ / lowerBound β₀ ^ 2)
        (64 * quadraticConstant J β₀ t C₂ / lowerBound β₀ ^ 3)
        (ConditionalLogSobolev.coefficient J β₀ C₂)
        (Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂)) G i X
        ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β := by
  obtain ⟨r, hr | hr⟩ := he.1
  · exact positive_label_edge_bound hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall
      hN hG η ζ i r he hr
  · have hh := positive_label_edge_bound hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall
      hN hG ζ η i r he.symm hr
    dsimp only at hh ⊢
    rw [mixing_square_symm (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub)
      (labelSquareNorm (mesh_pos hmesh) β G) η ζ i he,
      BoundaryComparison.twoCellGibbsMeasure_coordinateStep_symm (mesh_pos hmesh) β η ζ i he] at hh
    exact hh

/-- The actual source entropy boundary comparison for arbitrary particle
number in the stated regime. The single-edge premise is fully discharged. -/
theorem entropy_boundary_comparison {N : ℕ} (hN : 2 ≤ N)
    {G : Configuration N → ℝ} {C : ℝ≥0}
    (hG : ConfigurationEuclideanLipschitzWith C G) :
    labelEnergy (t := t) (mesh_pos hmesh) β (labelSquareNorm (mesh_pos hmesh) β G) ≤
      (energyCoefficient J β₀ t C₂ / (J : ℝ) ^ 2) *
        (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
      massCoefficient J β₀ t C₂ * ∫ X, G X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  cases N with
  | zero => omega
  | succ n =>
    exact source_entropy_boundary_of_single_edge hN hβ hβ₀ hsub hmesh hG
      (label_edge_bound hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall hN hG)

end SourceBoundary

section AmbientContinuity

variable {N J : ℕ} {t β : ℝ}

/-- Restriction of the original Gibbs L2 class to a fixed actual label event. -/
def labelRestriction (hJ : 0 < J) (β : ℝ) (η : LabelVector J N) :
    Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) →L[ℝ]
      Lp ℝ 2 ((gibbsMeasure greenRealRepresentative N β).restrict (labelFiber hJ η)) :=
  LpToLpRestrictCLM (Configuration N) ℝ ℝ
    (gibbsMeasure greenRealRepresentative N β) 2 (labelFiber hJ η)

/-- The literal component square integral is the fixed inverse mass times
the squared norm of the actual restricted L2 class. -/
theorem label_square_integral_eq (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N)
    (u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β)) :
    (∫ X, u X ^ 2 ∂labelGibbsMeasure hJ η β) =
      ((labelProbability hJ η β)⁻¹).toReal * ‖labelRestriction hJ β η u‖ ^ 2 := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let R := labelRestriction hJ β η u
  have hr : R =ᵐ[μ.restrict (labelFiber hJ η)] u :=
    LpToLpRestrictCLM_coeFn ℝ (labelFiber hJ η) u
  have hn : (∫ X, ‖R X‖ ^ 2 ∂μ.restrict (labelFiber hJ η)) = ‖R‖ ^ 2 := by
    simpa only [L2.inner_def, real_inner_self_eq_norm_sq] using real_inner_self_eq_norm_sq R
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub, ProbabilityTheory.cond, integral_smul_measure]
  congr 1
  calc
    (∫ X, u X ^ 2 ∂μ.restrict (labelFiber hJ η)) =
        ∫ X, R X ^ 2 ∂μ.restrict (labelFiber hJ η) :=
      integral_congr_ae (hr.mono fun X hX => congrArg (fun z : ℝ => z ^ 2) hX.symm)
    _ = ‖R‖ ^ 2 := by simpa only [Real.norm_eq_abs, sq_abs] using hn

/-- Component square norms are continuous on the original ambient L2 space.
This holds for every fixed label, without any regularity or symmetry gate. -/
theorem continuous_labelSquareNorm (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelState J N t) :
    Continuous (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) =>
      labelSquareNorm hJ β u η) := by
  have he : (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) =>
      labelSquareNorm hJ β u η) =
      fun u => Real.sqrt (((labelProbability hJ η.val β)⁻¹).toReal *
        ‖labelRestriction hJ β η.val u‖ ^ 2) := by
    funext u
    unfold labelSquareNorm
    rw [label_square_integral_eq hJ hN hβ hsub]
  rw [he]
  exact (continuous_const.mul ((labelRestriction hJ β η.val).continuous.norm.pow 2)).sqrt

/-- The entire finite outer boundary energy is continuous in the original
L2 norm; no smaller support graph is used in this limit. -/
theorem continuous_labelSquareEnergy (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) :
    Continuous (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) =>
      labelEnergy (t := t) hJ β (labelSquareNorm hJ β u)) := by
  classical
  unfold labelEnergy labelTerm
  apply continuous_finsetSum
  intro η _
  apply continuous_finsetSum
  intro ζ _
  by_cases he : labelRank η < labelRank ζ
  · simp only [ite_eq_left he]
    exact continuous_const.mul
      (((continuous_labelSquareNorm hJ hN hβ hsub ζ).sub
        (continuous_labelSquareNorm hJ hN hβ hsub η)).pow 2)
  · simp only [ite_eq_right he]
    exact continuous_const

/-- Smooth representatives and their original Gibbs L2 classes have
identical component square norms, by absolute continuity of the fixed law. -/
theorem labelSquareNorm_toLp (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (f : C(Configuration N, ℝ)) :
    labelSquareNorm (t := t) hJ β
      (ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ f) =
        labelSquareNorm hJ β f := by
  funext η
  unfold labelSquareNorm
  congr 1
  apply integral_congr_ae
  have hae : ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ f
      =ᵐ[labelGibbsMeasure hJ η.val β] f :=
    (BoundaryComparison.labelGibbsMeasure_absolutelyContinuous hJ hN hβ hsub η.val).ae_le
      (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
        (gibbsMeasure greenRealRepresentative N β) f)
  exact hae.mono (fun X hX => congrArg (fun z : ℝ => z ^ 2) hX)

end AmbientContinuity


/-- The entropy boundary comparison on the actual full ambient closed form
domain. The approximation is constructed by the existing smooth graph closure;
no approximation, regularity, symmetry or desired inequality is assumed. -/
theorem green_ambient_entropy_boundary_comparison {N J : ℕ} {β β₀ t C₂ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (f : GreenAmbientFormDomain N β) :
    labelEnergy (t := t) (mesh_pos hmesh) β (labelSquareNorm (mesh_pos hmesh) β (ambientValue f)) ≤
      (energyCoefficient J β₀ t C₂ / (J : ℝ) ^ 2) * ambientEnergy f +
        massCoefficient J β₀ t C₂ *
          ∫ X, ambientValue f X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let hJ := mesh_pos hmesh
  let A := energyCoefficient J β₀ t C₂ / (J : ℝ) ^ 2
  let B := massCoefficient J β₀ t C₂
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ (hβ₀.trans_lt hsub)
  obtain ⟨s, hs⟩ := exists_smooth_formNorm_approx f
  have hp : Tendsto (fun k => (ContinuousMap.toLp 2 μ ℝ (s k).value,
      ContinuousMap.toLp 2 μ ℝ (s k).gradient)) atTop (𝓝 f.1) :=
    tendsto_iff_graphFormNorm_sub_tendsto_zero.mpr hs
  have hv : Tendsto (fun k => ContinuousMap.toLp 2 μ ℝ (s k).value)
      atTop (𝓝 (ambientValue f)) := (continuous_fst.tendsto f.1).comp hp
  have hg : Tendsto (fun k => ContinuousMap.toLp 2 μ ℝ (s k).gradient)
      atTop (𝓝 (ambientGradient f)) := (continuous_snd.tendsto f.1).comp hp
  have hleft : Tendsto (fun k => labelEnergy (t := t) hJ β
      (labelSquareNorm hJ β (ContinuousMap.toLp 2 μ ℝ (s k).value)))
      atTop (𝓝 (labelEnergy (t := t) hJ β (labelSquareNorm hJ β (ambientValue f)))) :=
    ((continuous_labelSquareEnergy (t := t) hJ hN hβ (hβ₀.trans_lt hsub)).tendsto
      (ambientValue f)).comp hv
  have hright : Tendsto (fun k => A * ambientEnergy ((s k).toAmbient μ) +
      B * ‖ContinuousMap.toLp 2 μ ℝ (s k).value‖ ^ 2)
      atTop (𝓝 (A * ambientEnergy f + B * ‖ambientValue f‖ ^ 2)) := by
    change Tendsto (fun k => A * ‖ContinuousMap.toLp 2 μ ℝ (s k).gradient‖ ^ 2 +
      B * ‖ContinuousMap.toLp 2 μ ℝ (s k).value‖ ^ 2)
      atTop (𝓝 (A * ‖ambientGradient f‖ ^ 2 + B * ‖ambientValue f‖ ^ 2))
    exact ((hg.norm.pow 2).const_mul A).add ((hv.norm.pow 2).const_mul B)
  have hbound (k : ℕ) : labelEnergy (t := t) hJ β
      (labelSquareNorm hJ β (ContinuousMap.toLp 2 μ ℝ (s k).value)) ≤
      A * ambientEnergy ((s k).toAmbient μ) +
        B * ‖ContinuousMap.toLp 2 μ ℝ (s k).value‖ ^ 2 := by
    rw [labelSquareNorm_toLp hJ hN hβ (hβ₀.trans_lt hsub),
      (s k).ambientEnergy_eq_coordinate_integral,
      CenteredL2.norm_sq_eq_integral_sq_representative μ _
        (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (s k).value)]
    exact entropy_boundary_comparison hβ hβ₀ hsub hC hk hmesh hmeshY ht htC hcap hscale hsmall
      hN (s k).configurationEuclideanLipschitz
  have hb := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)
  simpa only [CenteredL2.norm_sq_eq_integral_sq] using hb

end PeriodicAttractiveLogGas.EntropyBoundaryComparison
