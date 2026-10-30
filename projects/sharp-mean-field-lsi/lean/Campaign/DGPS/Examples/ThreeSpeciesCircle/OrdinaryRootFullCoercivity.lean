import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormAlgebra
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootTangentPositive
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootTangentBounds
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensityBounds
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootParameterBounds

/-! The actual Schur lift on the original periodic weak-H1 domain. The constants
are chosen before h, the branch, and the test. The quantitative gap is of order h². -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual ordinary-root form is uniformly coercive, with its necessary h²
factor, on every original Haar-mean-zero weak-H1 test. All finite-dimensional and
complement estimates come from the retained ordinary construction. -/
theorem ordinaryRoot_fullWeak_coercivity (D : OrdinaryRootGraphData) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ D.radius ∧
      ∀ h : ℝ, 0 < h → h < δ → ∀ j : Fin 3,
        ∀ f g : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 f g →
          normInt_STR02933 f = 0 →
        c * h ^ 2 * normInt_STR02933 (fun t => g t ^ 2 + f t ^ 2) ≤
          ordinaryRootHessianQuadratic
            (rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)))
            (1 + h ^ 2 * D.Z j h 2) f g := by
  obtain ⟨δp, hδp, hδpr, hp⟩ := ordinaryRoot_amplitude_tangent_positive D
  obtain ⟨K, δK, hK, hδK, hδKr, hKb⟩ := ordinaryRoot_amplitude_tangent_bound D
  obtain ⟨C, _, hrem⟩ := D.log_bound
  obtain ⟨δσ, hδσ, hδσr, hσb⟩ := ordinaryRoot_threefold_density_near_one
    D.ψ D.Z D.radius D.radius_pos C hrem D.density_rotations
  obtain ⟨δa, hδa, hδar, hab⟩ := ordinaryRoot_angular_parameter_bounds D
  let δ := min δp (min δK (min δσ (min δa 1)))
  let c := (48 * (K ^ 2 + 1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ : 0 < δ :=
    lt_min hδp (lt_min hδK (lt_min hδσ (lt_min hδa (by norm_num))))
  have hδr : δ ≤ D.radius := (min_le_left _ _).trans hδpr
  refine ⟨c, δ, hc, hδ, hδr, fun h hh hhd j f g hf hmean => ?_⟩
  have hsmall := lt_min_iff.mp hhd
  have hhp : h < δp := hsmall.1
  have hhK : h < δK := (lt_min_iff.mp hsmall.2).1
  have hhσ : h < δσ := (lt_min_iff.mp (lt_min_iff.mp hsmall.2).2).1
  have hha : h < δa :=
    (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hsmall.2).2).2).1
  have hh1 : h < 1 :=
    (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hsmall.2).2).2).2
  have hhr : h ∈ Ioo (-D.radius) D.radius := by
    constructor <;> linarith [D.radius_pos, hhd.trans_le hδr]
  let γ := h ^ 2 * D.Z j h 2
  let x : ℝ × ℝ := (h * D.Z j h 0, h * D.Z j h 1)
  let u := Lamp_STR02956 D.ψ (h, γ) x
  let v : ℝ × ℝ := (cosCoeff_STR02933 f 1, sinCoeff_STR02933 f 1)
  let T := fderiv ℝ (Lamp_STR02956 D.ψ (h, γ)) x v
  let w := fun t => f t - T.val t
  let k := fun t => g t - deriv T.val t
  let σ := rhoT_STR02901 h u.val
  have hU : iota_STR02956 (h, γ) x ∈ D.U := D.branch_memU j h hhr
  have hcrit : ∀ t, gradG_STR02950 h γ u.val t = 0 := D.chart_critical h hhr j
  obtain ⟨hw, hw0, hwc, hws, hsum, hgrad⟩ :=
    ordinaryRangeGraph_fullWeak_decomposition D.openU D.smoothψ (h, γ) x hU f g hf hmean
  have hTw : IsPeriodicWeakDerivative_STR02933 T.val (deriv T.val) :=
    ordinaryRoot_periodicWeak_of_c1 T.val T.isC2.1
      (contDiff_one_iff_deriv.mpr ⟨T.isC2.2.1, T.isC2.2.2.1.continuous⟩)
  have hsplit := ordinaryRangeGraph_fullWeak_quadratic_split D.openU D.smoothψ
    D.memψ D.range_eq h γ x hU hcrit f g hf hmean
  have hTlow : (h ^ 2 / 24) * (v.1 ^ 2 + v.2 ^ 2) ≤
      ordinaryRootHessianQuadratic σ (1 + γ) T.val (deriv T.val) := hp h hh hhp j v
  have hTup : normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) ≤
      K ^ 2 * (v.1 ^ 2 + v.2 ^ 2) :=
    hKb h (by rw [abs_of_pos hh]; exact hhK) j v
  have hσ : Continuous σ := continuous_rho_STR02950 h u.isC2.2.1.continuous
  have hσbounds : ∀ t, (3 / 4 : ℝ) ≤ σ t ∧ σ t ≤ (5 / 4 : ℝ) :=
    hσb h (by rw [abs_of_pos hh]; exact hhσ) j
  have ha : 0 ≤ 1 + γ ∧ 1 + γ ≤ (3 / 2 : ℝ) :=
    hab h (by rw [abs_of_pos hh]; exact hha) j
  have hWlow := ordinaryRootHessian_complement_lower σ hσ.measurable
    (fun t => (hσbounds t).1) (fun t => (hσbounds t).2)
    (1 + γ) ha.1 ha.2 w k hw hw0 hwc hws
  let A := v.1 ^ 2 + v.2 ^ 2
  let W := normInt_STR02933 (fun t => k t ^ 2 + w t ^ 2)
  let H := normInt_STR02933 (fun t => g t ^ 2 + f t ^ 2)
  have hA : 0 ≤ A := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hW : 0 ≤ W := by
    dsimp [W, normInt_STR02933]
    exact mul_nonneg (by positivity) (integral_nonneg fun t =>
      add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hnorm : H ≤ 2 * (K ^ 2 + 1) * (A + W) := by
    have he := ordinaryRootH1_add_bound T.val (deriv T.val) w k hTw hw
    have hsumf : ∀ t, T.val t + w t = f t := fun t => (hsum t).symm
    have hsumg : ∀ t, deriv T.val t + k t = g t := fun t => (hgrad t).symm
    simp_rw [hsumf, hsumg] at he
    change H ≤ 2 * normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) + 2 * W at he
    change normInt_STR02933 (fun t => deriv T.val t ^ 2 + T.val t ^ 2) ≤ K ^ 2 * A at hTup
    nlinarith [mul_nonneg (sq_nonneg K) hW]
  have hWsmall : (h ^ 2 / 24) * W ≤ ordinaryRootHessianQuadratic σ (1 + γ) w k := by
    have hcoef : h ^ 2 / 24 ≤ (9 / 40 : ℝ) := by
      nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1.le)]
    exact (mul_le_mul_of_nonneg_right hcoef hW).trans hWlow
  have htotal : (h ^ 2 / 24) * (A + W) ≤ ordinaryRootHessianQuadratic σ (1 + γ) f g := by
    change ordinaryRootHessianQuadratic σ (1 + γ) f g =
      ordinaryRootHessianQuadratic σ (1 + γ) T.val (deriv T.val) +
        ordinaryRootHessianQuadratic σ (1 + γ) w k at hsplit
    rw [hsplit]
    change (h ^ 2 / 24) * (A + W) ≤ _
    change (h ^ 2 / 24) * A ≤ _ at hTlow
    linarith
  have hcancel : c * (2 * (K ^ 2 + 1)) = (1 / 24 : ℝ) := by
    dsimp [c]
    field_simp [show K ^ 2 + 1 ≠ 0 by positivity]
    <;> ring
  change c * h ^ 2 * H ≤ ordinaryRootHessianQuadratic σ (1 + γ) f g
  calc
    _ ≤ c * h ^ 2 * (2 * (K ^ 2 + 1) * (A + W)) :=
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg hc.le (sq_nonneg h))
    _ = (c * (2 * (K ^ 2 + 1))) * h ^ 2 * (A + W) := by ring
    _ = (h ^ 2 / 24) * (A + W) := by rw [hcancel]; ring
    _ ≤ _ := htotal

end DGPS.Examples.ThreeSpeciesCircle
