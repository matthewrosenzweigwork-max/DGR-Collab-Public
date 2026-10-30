import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootSchurPairing
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphDecomposition

/-! Exact quadratic splitting and the full weak-H1 norm estimate. All products are
integrable on the original period; the actual range equation supplies the mixed zero. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem weighted_square_add (σ u v : ℝ → ℝ) (hσ : Continuous σ)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (2 * π))))
    (hv : MemLp v 2 (volume.restrict (Ioc 0 (2 * π)))) :
    normInt_STR02933 (fun t => σ t * (u t + v t) ^ 2) =
      normInt_STR02933 (fun t => σ t * u t ^ 2) +
      normInt_STR02933 (fun t => σ t * v t ^ 2) +
      2 * normInt_STR02933 (fun t => σ t * u t * v t) := by
  have hiu : Integrable (fun t => σ t * u t ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [pow_two] using integrable_cmul_STR02935 hσ hu hu
  have hiv : Integrable (fun t => σ t * v t ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [pow_two] using integrable_cmul_STR02935 hσ hv hv
  have hix : Integrable (fun t => σ t * u t * v t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [mul_assoc] using integrable_cmul_STR02935 hσ hu hv
  have he : (fun t => σ t * (u t + v t) ^ 2) = fun t =>
      1 * (σ t * u t ^ 2) + 1 * (σ t * v t ^ 2) + 2 * (σ t * u t * v t) := by
    funext t; ring
  rw [he, normInt_lin3_STR02935 hiu hiv hix]
  ring

/-- Exact quadratic polarization on the full weak-H1 domain. -/
theorem ordinaryRootHessian_add (σ : ℝ → ℝ) (hσ : Continuous σ) (a : ℝ)
    (f g w k : ℝ → ℝ)
    (hf : IsPeriodicWeakDerivative_STR02933 f g)
    (hw : IsPeriodicWeakDerivative_STR02933 w k) :
    ordinaryRootHessianQuadratic σ a (fun t => f t + w t) (fun t => g t + k t) =
      ordinaryRootHessianQuadratic σ a f g + ordinaryRootHessianQuadratic σ a w k +
      2 * (normInt_STR02933 (fun t => σ t * g t * k t) -
        a * (normInt_STR02933 (fun t => σ t * f t * w t) -
          normInt_STR02933 (fun t => σ t * f t) *
            normInt_STR02933 (fun t => σ t * w t))) := by
  have hmean : normInt_STR02933 (fun t => σ t * (f t + w t)) =
      normInt_STR02933 (fun t => σ t * f t) +
        normInt_STR02933 (fun t => σ t * w t) := by
    have he : (fun t => σ t * (f t + w t)) =
        fun t => σ t * f t + σ t * w t := by funext t; ring
    rw [he, normInt_add_STR02934
      (integrable_cmul_left_STR02935 hσ hf.1.2)
      (integrable_cmul_left_STR02935 hσ hw.1.2)]
  unfold ordinaryRootHessianQuadratic
  rw [weighted_square_add σ g k hσ hf.2.1.2 hw.2.1.2,
    weighted_square_add σ f w hσ hf.1.2 hw.1.2, hmean]
  ring

/-- The original unweighted H1 norm is controlled by the two genuine summands. -/
theorem ordinaryRootH1_add_bound (f g w k : ℝ → ℝ)
    (hf : IsPeriodicWeakDerivative_STR02933 f g)
    (hw : IsPeriodicWeakDerivative_STR02933 w k) :
    normInt_STR02933 (fun t => (g t + k t) ^ 2 + (f t + w t) ^ 2) ≤
      2 * normInt_STR02933 (fun t => g t ^ 2 + f t ^ 2) +
      2 * normInt_STR02933 (fun t => k t ^ 2 + w t ^ 2) := by
  have hsum : Integrable (fun t => (g t + k t) ^ 2 + (f t + w t) ^ 2)
      (volume.restrict (Ioc 0 (2 * π))) :=
    ((hf.2.1.2.add hw.2.1.2).integrable_sq).add
      ((hf.1.2.add hw.1.2).integrable_sq)
  have hT := hf.2.1.2.integrable_sq.add hf.1.2.integrable_sq
  have hW := hw.2.1.2.integrable_sq.add hw.1.2.integrable_sq
  calc
    _ ≤ normInt_STR02933 (fun t =>
        2 * (g t ^ 2 + f t ^ 2) + 2 * (k t ^ 2 + w t ^ 2)) :=
      normInt_mono_STR02935 hsum ((hT.const_mul 2).add (hW.const_mul 2))
        (fun t => by nlinarith [sq_nonneg (g t - k t), sq_nonneg (f t - w t)])
    _ = _ := by
      rw [normInt_add_STR02934 (f := fun t => 2 * (g t ^ 2 + f t ^ 2))
        (g := fun t => 2 * (k t ^ 2 + w t ^ 2)) (hT.const_mul 2) (hW.const_mul 2),
        normInt_mul_const_STR02933, normInt_mul_const_STR02933]

/-- On the actual critical range graph, the full weak-H1 quadratic form splits
exactly into its tangent and complement parts. No mixed-zero premise is used. -/
theorem ordinaryRangeGraph_fullWeak_quadratic_split
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (h γ : ℝ) (x : ℝ × ℝ) (hx : iota_STR02956 (h, γ) x ∈ U)
    (hcrit : ∀ t, gradG_STR02950 h γ (Lamp_STR02956 ψ (h, γ) x).val t = 0)
    (f g : ℝ → ℝ) (hf : IsPeriodicWeakDerivative_STR02933 f g)
    (hmean : normInt_STR02933 f = 0) :
    let v : ℝ × ℝ := (cosCoeff_STR02933 f 1, sinCoeff_STR02933 f 1)
    let u := Lamp_STR02956 ψ (h, γ) x
    let T := fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v
    ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val) (1 + γ) f g =
      ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val) (1 + γ) T.val (deriv T.val) +
      ordinaryRootHessianQuadratic (rhoT_STR02901 h u.val) (1 + γ)
        (fun t => f t - T.val t) (fun t => g t - deriv T.val t) := by
  let v : ℝ × ℝ := (cosCoeff_STR02933 f 1, sinCoeff_STR02933 f 1)
  let u := Lamp_STR02956 ψ (h, γ) x
  let T := fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v
  let w := fun t => f t - T.val t
  let k := fun t => g t - deriv T.val t
  obtain ⟨hw, hw0, hwc, hws, _, _⟩ :=
    ordinaryRangeGraph_fullWeak_decomposition hU hψC (h, γ) x hx f g hf hmean
  have hTw : IsPeriodicWeakDerivative_STR02933 T.val (deriv T.val) :=
    ordinaryRoot_periodicWeak_of_c1 T.val T.isC2.1
      (contDiff_one_iff_deriv.mpr ⟨T.isC2.2.1, T.isC2.2.2.1.continuous⟩)
  have hmix := ordinaryRangeGraph_fullWeak_complement_zero
    hU hψC hψV hR h γ x v hx hcrit w k hw hw0 hwc hws
  have he := ordinaryRootHessian_add (rhoT_STR02901 h u.val)
    (continuous_rho_STR02950 h u.isC2.2.1.continuous) (1 + γ)
    T.val (deriv T.val) w k hTw hw
  have hfun : (fun t => T.val t + w t) = f := by funext t; dsimp [w]; ring
  have hgrad : (fun t => deriv T.val t + k t) = g := by funext t; dsimp [k]; ring
  rw [hfun, hgrad] at he
  change normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * deriv T.val t * k t) -
    (1 + γ) * (normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t * w t) -
      normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t) *
        normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * w t)) = 0 at hmix
  rw [hmix] at he
  simpa only [mul_zero, add_zero] using he

end DGPS.Examples.ThreeSpeciesCircle
