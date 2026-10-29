import LeanResearch.PeriodicAttractiveLogGas.CrossingConcentration

/-! Source lines 2993–3025: exact entropy edge-density summation over the
full permitted outer label graph. The analytic single-edge inequality is an
explicit intermediate premise; graph transport and counting are proved. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.EntropyBoundarySummation

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions DiscreteOccupationIdentities
open BoundaryEdgeSummation ConditionalLawEstimates ConditionalVarianceAssembly CrossingConcentration

variable {J N : ℕ} {t : ℝ}

/-- The actual label square norm; its law is the original specified-label
Gibbs probability, with no replacement of the outer graph. -/
def labelSquareNorm (hJ : 0 < J) (β : ℝ) (G : Configuration N → ℝ)
    (η : LabelState J N t) : ℝ :=
  Real.sqrt (∫ X, G X ^ 2 ∂labelGibbsMeasure hJ η.val β)

/-- The source single-edge density in its physical, unscaled energy convention. -/
def entropyEdgeDensity (J : ℕ) (A B K L : ℝ) (G : Configuration N → ℝ)
    (i : Fin N) (X : Configuration N) : ℝ :=
  (A / (J : ℝ) ^ 2) * coordinateEnergy G i X +
    (B / N) * (K * totalEnergyDensity G X + L * G X ^ 2)

theorem integrable_square {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G) :
    Integrable (fun X => G X ^ 2) μ := by
  have hm : MemLp G 2 μ := ContinuousMap.memLp (μ := μ) (p := 2) ℝ ⟨G, hG.continuous⟩
  exact hm.integrable_sq

theorem entropyEdgeDensity_nonneg {A B K L : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (G : Configuration N → ℝ) (i : Fin N) (X : Configuration N) :
    0 ≤ entropyEdgeDensity J A B K L G i X :=
  add_nonneg (mul_nonneg (div_nonneg hA (sq_nonneg _)) (sq_nonneg _))
    (mul_nonneg (div_nonneg hB (Nat.cast_nonneg _))
      (add_nonneg (mul_nonneg hK (totalEnergyDensity_nonneg G X)) (mul_nonneg hL (sq_nonneg _))))

theorem integrable_entropyEdgeDensity {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (A B K L : ℝ) (i : Fin N) : Integrable (entropyEdgeDensity J A B K L G i) μ := by
  exact ((integrable_coordinate_energy hG μ i).const_mul (A / (J : ℝ) ^ 2)).add
    (((integrable_totalEnergyDensity hG).const_mul K).add
      ((integrable_square hG).const_mul L) |>.const_mul (B / N))

/-- Exact finite summation: coordinate energy occurs once; the N identical
total-energy and mass terms cancel their source factor N inverse. -/
theorem sum_entropyEdgeDensity (hN : 0 < N) (A B K L : ℝ)
    (G : Configuration N → ℝ) (X : Configuration N) :
    (∑ i, entropyEdgeDensity J A B K L G i X) =
      (A / (J : ℝ) ^ 2 + B * K) * totalEnergyDensity G X + B * L * G X ^ 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (N : ℝ) * (B / N) = B := by field_simp [hn]
  simp only [entropyEdgeDensity, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (A / (J : ℝ) ^ 2) * totalEnergyDensity G X +
    (B / N) * (K * ((N : ℝ) * totalEnergyDensity G X) + L * ((N : ℝ) * G X ^ 2)) = _
  calc
    _ = (A / (J : ℝ) ^ 2) * totalEnergyDensity G X +
        ((N : ℝ) * (B / N)) * (K * totalEnergyDensity G X + L * G X ^ 2) := by ring
    _ = _ := by rw [hc]; ring

theorem sum_integral_entropyEdgeDensity {μ : Measure (Configuration N)} [IsFiniteMeasure μ]
    (hN : 0 < N) {C : ℝ≥0} {G : Configuration N → ℝ}
    (hG : ConfigurationEuclideanLipschitzWith C G) (A B K L : ℝ) :
    (∑ i, ∫ X, entropyEdgeDensity J A B K L G i X ∂μ) =
      (A / (J : ℝ) ^ 2 + B * K) * (∫ X, totalEnergyDensity G X ∂μ) +
        B * L * ∫ X, G X ^ 2 ∂μ := by
  rw [← integral_finsetSum Finset.univ (fun i _ => integrable_entropyEdgeDensity hG A B K L i)]
  simp_rw [sum_entropyEdgeDensity hN]
  rw [integral_add ((integrable_totalEnergyDensity hG).const_mul _)
    ((integrable_square hG).const_mul _), integral_const_mul, integral_const_mul]

/-- Conditional entropy boundary summation on every permitted outer edge.
The single-edge analytic estimate remains explicit; all actual conductance,
transport, four-incidence and integrability inputs are discharged. -/
theorem entropy_boundary_of_single_edge (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    {β A B K L : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) (hL : 0 ≤ L)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep hJ i η ζ →
      let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
      p * (1 - p) * (labelSquareNorm hJ β G η - labelSquareNorm hJ β G ζ) ^ 2 ≤
        ∫ X, entropyEdgeDensity J A B K L G i X
          ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) :
    labelEnergy (t := t) hJ β (labelSquareNorm hJ β G) ≤
      4 * (A / (J : ℝ) ^ 2 + B * K) *
        (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
      4 * B * L * ∫ X, G X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let : IsProbabilityMeasure μ := isProbabilityMeasure_greenGibbs N hN hβ hsub
  have hlocal (η ζ : LabelState J N t) (i : Fin N) (he : CoordinateStep hJ i η ζ) :
      labelTerm hJ β (labelSquareNorm hJ β G) η ζ ≤
        (labelWeight hJ β η + labelWeight hJ β ζ) *
          (∫ X, entropyEdgeDensity J A B K L G i X
            ∂twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β) := by
    rw [labelTerm_eq_mass_mixing hJ hN hβ hsub _ η ζ i he]
    have hh := mul_le_mul_of_nonneg_left (hedge η ζ i he)
      (add_nonneg (labelWeight_pos hJ hN hβ hsub η).le (labelWeight_pos hJ hN hβ hsub ζ).le)
    (convert hh using 1; ring)
  have hg := labelEnergy_le_of_twoCell_edge_bound hJ hJ3 hN hβ hsub
    (labelSquareNorm hJ β G) (entropyEdgeDensity J A B K L G)
    (fun i => integrable_entropyEdgeDensity (μ := μ) hG A B K L i)
    (entropyEdgeDensity_nonneg hA hB hK hL G) hlocal
  rw [sum_integral_entropyEdgeDensity (μ := μ) (by omega) hG] at hg
  (convert hg using 1; ring)

/-- Every label square norm is a true finite squared norm of the original
test under the original specified-label probability law. -/
theorem label_square_integrable (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (η : LabelState J N t) : Integrable (fun X => G X ^ 2) (labelGibbsMeasure hJ η.val β) := by
  let : IsProbabilityMeasure (labelGibbsMeasure hJ η.val β) :=
    isProbabilityMeasure_labelGibbsMeasure hJ hN η.val hβ hsub
  exact integrable_square hG

/-- The exact two source coefficients, independent of particle number and
actual beta. They retain the unscaled physical energy convention. -/
def energyCoefficient (J : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  8 * finePoincareConstant β₀ / lowerBound β₀ ^ 2 +
    256 * quadraticConstant J β₀ t C₂ * (J : ℝ) ^ 2 *
      ConditionalLogSobolev.coefficient J β₀ C₂ / lowerBound β₀ ^ 3

def massCoefficient (J : ℕ) (β₀ t C₂ : ℝ) : ℝ :=
  256 * quadraticConstant J β₀ t C₂ / lowerBound β₀ ^ 3 *
    (Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂))

theorem source_logFactor_nonneg {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) (J : ℕ) (t C₂ : ℝ) :
    0 ≤ Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂) := by
  have hc := lowerBound_pos β₀
  have hc1 := (ConditionalEntropyTightening.source_density_parameter_bounds hβ₀).1
  have hleft : 0 ≤ Real.log (2 / lowerBound β₀) :=
    Real.log_nonneg ((le_div_iff₀ hc).mpr (by linarith))
  have hq := quadraticConstant_pos J β₀ t C₂
  have he : 1 ≤ Real.exp (linearConstant β₀ t ^ 2 / (8 * quadraticConstant J β₀ t C₂)) :=
    Real.one_le_exp_iff.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hs : 1 ≤ squareConstant J β₀ t C₂ := by
    unfold squareConstant
    linarith
  exact add_nonneg hleft (Real.log_nonneg hs)

/-- This is the source single-edge logarithm written as the sum used in
the final coefficient; both arguments are strictly positive. -/
theorem source_logProduct_eq (J : ℕ) (β₀ t C₂ : ℝ) :
    Real.log (2 * squareConstant J β₀ t C₂ / lowerBound β₀) =
      Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂) := by
  have hs : 0 < squareConstant J β₀ t C₂ := by unfold squareConstant; positivity
  rw [show 2 * squareConstant J β₀ t C₂ / lowerBound β₀ =
    (2 / lowerBound β₀) * squareConstant J β₀ t C₂ by ring]
  exact Real.log_mul (div_ne_zero (by norm_num) (lowerBound_pos β₀).ne') hs.ne'

theorem source_coefficients_nonneg (hJ : 0 < J) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (t C₂ : ℝ) : 0 ≤ energyCoefficient J β₀ t C₂ ∧ 0 ≤ massCoefficient J β₀ t C₂ := by
  have hA := finePoincareConstant_nonneg β₀
  have hc := lowerBound_pos β₀
  have hq := quadraticConstant_pos J β₀ t C₂
  have hK := ConditionalLogSobolev.coefficient_nonneg hJ hβ₀ C₂
  have hL := source_logFactor_nonneg hβ₀ J t C₂
  constructor
  · unfold energyCoefficient
    positivity
  · exact mul_nonneg (by positivity) hL

/-- Exact source coefficients from the explicit genuine one-edge input.
This is an intermediate implication, not a proof of the analytic one-edge
estimate or a completed entropy boundary proposition. All outer edges are
retained and no smaller support graph is substituted. -/
theorem source_entropy_boundary_of_single_edge {β β₀ C₂ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    {C : ℝ≥0} {G : Configuration N → ℝ} (hG : ConfigurationEuclideanLipschitzWith C G)
    (hedge : ∀ η ζ : LabelState J N t, ∀ i, CoordinateStep (mesh_pos hmesh) i η ζ →
      let p := (twoCellMixingWeight (mesh_pos hmesh) η.val i (η.val i) (ζ.val i) β).toReal
      p * (1 - p) * (labelSquareNorm (mesh_pos hmesh) β G η -
        labelSquareNorm (mesh_pos hmesh) β G ζ) ^ 2 ≤
        ∫ X, entropyEdgeDensity J (2 * finePoincareConstant β₀ / lowerBound β₀ ^ 2)
          (64 * quadraticConstant J β₀ t C₂ / lowerBound β₀ ^ 3)
          (ConditionalLogSobolev.coefficient J β₀ C₂)
          (Real.log (2 / lowerBound β₀) + Real.log (squareConstant J β₀ t C₂)) G i X
          ∂twoCellGibbsMeasure (mesh_pos hmesh) η.val i (η.val i) (ζ.val i) β) :
    labelEnergy (t := t) (mesh_pos hmesh) β (labelSquareNorm (mesh_pos hmesh) β G) ≤
      (energyCoefficient J β₀ t C₂ / (J : ℝ) ^ 2) *
        (∫ X, totalEnergyDensity G X ∂gibbsMeasure greenRealRepresentative N β) +
      massCoefficient J β₀ t C₂ * ∫ X, G X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
  have hβ₀0 := hβ.trans hβ₀
  have hA := finePoincareConstant_nonneg β₀
  have hc := lowerBound_pos β₀
  have hq := quadraticConstant_pos J β₀ t C₂
  have hK := ConditionalLogSobolev.coefficient_nonneg (mesh_pos hmesh) hβ₀0 C₂
  have hL := source_logFactor_nonneg hβ₀0 J t C₂
  have hh := entropy_boundary_of_single_edge (mesh_pos hmesh) (mesh_three_le hmesh) hN
    hβ (hβ₀.trans_lt hsub) (by positivity : 0 ≤ 2 * finePoincareConstant β₀ / lowerBound β₀ ^ 2)
    (by positivity : 0 ≤ 64 * quadraticConstant J β₀ t C₂ / lowerBound β₀ ^ 3)
    hK hL hG hedge
  have hj : (J : ℝ) ≠ 0 := by exact_mod_cast (mesh_pos hmesh).ne'
  convert hh using 1
  unfold energyCoefficient massCoefficient
  field_simp [hj, hc.ne']
  ring

end PeriodicAttractiveLogGas.EntropyBoundarySummation
