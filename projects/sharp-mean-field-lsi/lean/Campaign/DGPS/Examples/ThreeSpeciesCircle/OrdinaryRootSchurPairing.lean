import DGPS.Examples.ThreeSpeciesCircle.OrdinaryHessianSchur
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootLinearizedForm
import DGPS.Examples.ThreeSpeciesCircle.OrdinarySecondVariation

/-! Actual differentiated range equations on the retained graph. The Holder-valued
linearized gradient is projected to zero, then paired with every original weak-H1
complement test. No mixed-form orthogonality or strict Poincare inequality is an input. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Differentiating the actual projected range equation gives the projected derivative
of the actual gradient, on the SAME graph and with h and gamma fixed. -/
theorem ordinaryRangeGraph_projected_gradient_derivative_zero
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (h γ : ℝ) (x v : ℝ × ℝ) (hx : iota_STR02956 (h, γ) x ∈ U) :
    PCLM_STR02955
      (fderiv ℝ (fun y => Gfun_STR02955 h γ (Lamp_STR02956 ψ (h, γ) y)) x v) = 0 := by
  let L := Lamp_STR02956 ψ (h, γ)
  let G : PeriodicC2_STR02969 → PeriodicHolder_STR02968 := Gfun_STR02955 h γ
  let K := fun y => G (L y)
  have hGs : ContDiff ℝ ∞ G := by
    change ContDiff ℝ ∞ (Gmap_STR02955 ∘ fun u : PeriodicC2_STR02969 => (h, γ, u))
    exact Gmap_smooth_STR02955.comp (by fun_prop)
  have hopen := isOpen_iota_preimage_STR02956 hU (h, γ)
  have hL : DifferentiableAt ℝ L x :=
    ((Lamp_contDiffOn_STR02956 hψC (h, γ)).contDiffAt
      (hopen.mem_nhds hx)).differentiableAt (by simp)
  have hK : DifferentiableAt ℝ K x :=
    ((hGs.differentiable (by simp)) (L x)).comp x hL
  have hzero : (fun y => PCLM_STR02955 (K y)) =ᶠ[𝓝 x]
      fun _ => (0 : PeriodicHolder_STR02968) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    apply ext_STR02954
    funext t
    change projP_STR02953 (Gfun_STR02955 h γ (L y)).val t = 0
    have he : (Gfun_STR02955 h γ (L y)).val = gradG_STR02950 h γ (L y).val :=
      Gfun_val_STR02955 h γ (L y)
    rw [he]
    change projP_STR02953 (gradG_STR02950 h γ
      (uT_STR02901 y.1 y.2 ((ψ (y.1, y.2, h, γ) : E_STR02969) : PeriodicC2_STR02969).val)) t = 0
    exact projP_gradG_zero_STR02924 hψV hR y.1 y.2 h γ hy t
  have hd := PCLM_STR02955.hasFDerivAt.comp x hK.hasFDerivAt
  have he := congrArg (fun A => A v) hd.fderiv
  change fderiv ℝ (fun y => PCLM_STR02955 (K y)) x v = _ at he
  rw [hzero.fderiv_eq, (hasFDerivAt_const (0 : PeriodicHolder_STR02968) x).fderiv] at he
  simpa only [ContinuousLinearMap.comp_apply, zero_apply] using he.symm

/-- At an actual critical graph chart, the actual linearized operator has zero projection.
The conclusion is supplied by the actual range equation, not postulated. -/
theorem ordinaryRangeGraph_projected_linearized_zero
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (h γ : ℝ) (x v : ℝ × ℝ) (hx : iota_STR02956 (h, γ) x ∈ U)
    (hcrit : ∀ t, gradG_STR02950 h γ (Lamp_STR02956 ψ (h, γ) x).val t = 0) :
    ∀ t, projP_STR02953
      (ordinaryRootLinearizedGradient h γ (Lamp_STR02956 ψ (h, γ) x)
        (fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v)) t = 0 := by
  let L := Lamp_STR02956 ψ (h, γ)
  let u := L x
  let T := fderiv ℝ L x v
  let G : PeriodicC2_STR02969 → PeriodicHolder_STR02968 := Gfun_STR02955 h γ
  have hGs : ContDiff ℝ ∞ G := by
    change ContDiff ℝ ∞ (Gmap_STR02955 ∘ fun u : PeriodicC2_STR02969 => (h, γ, u))
    exact Gmap_smooth_STR02955.comp (by fun_prop)
  have hopen := isOpen_iota_preimage_STR02956 hU (h, γ)
  have hL : DifferentiableAt ℝ L x :=
    ((Lamp_contDiffOn_STR02956 hψC (h, γ)).contDiffAt
      (hopen.mem_nhds hx)).differentiableAt (by simp)
  have hD := ordinaryRangeGraph_projected_gradient_derivative_zero hU hψC hψV hR h γ x v hx
  have hchain := ((hGs.differentiable (by simp)) (L x)).hasFDerivAt.comp x hL.hasFDerivAt
  change PCLM_STR02955 (fderiv ℝ (G ∘ L) x v) = 0 at hD
  rw [hchain.fderiv, ContinuousLinearMap.comp_apply] at hD
  change PCLM_STR02955 (fderiv ℝ G u T) = 0 at hD
  have hline : HasDerivAt (fun s : ℝ => u + s • T) T 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const T).const_add u
  have hgline := ((hGs.differentiable (by simp)) u).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℝ) hline (by simp)
  have hgrad := hgline.unique (OrdinarySecondVariation.gradient_line_deriv h γ u T hcrit)
  have hmean : meanCLM_STR02954 (e0_STR02955 T * rho_STR02954 (h, e0_STR02955 u)) =
      normInt_STR02933 (fun s => rhoT_STR02901 h u.val s * T.val s) := by
    rw [meanCLM_apply_STR02954]
    rw [← normInt_eq_meanT_STR02962]
    congr 1
    funext s
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954]
    simp only [e0_val_STR02955]
    ring
  have hval : (fderiv ℝ G u T).val = ordinaryRootLinearizedGradient h γ u T := by
    rw [hgrad]
    funext s
    simp only [val_mul_STR02954, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
      val_one_STR02954, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, rho_val_STR02954,
      e0_val_STR02955, e1_val_STR02955, e2_val_STR02955]
    change rhoT_STR02901 h u.val s *
      (-2 * deriv (deriv T.val) s + 6 * h * (Real.sin (3 * s) * deriv T.val s) -
        2 * (deriv u.val s * deriv T.val s) - 2 * (1 + γ) * T.val s +
          2 * (1 + γ) * meanCLM_STR02954
            (e0_STR02955 T * rho_STR02954 (h, e0_STR02955 u)) * 1) = _
    rw [hmean]
    unfold ordinaryRootLinearizedGradient
    ring
  intro t
  have hp := congrArg (fun f : PeriodicHolder_STR02968 => f.val t) hD
  change projP_STR02953 (fderiv ℝ G u T).val t = 0 at hp
  rw [hval] at hp
  exact hp

/-- Full weak-H1 orthogonality on the actual graph at a critical root. -/
theorem ordinaryRangeGraph_fullWeak_complement_zero
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (h γ : ℝ) (x v : ℝ × ℝ) (hx : iota_STR02956 (h, γ) x ∈ U)
    (hcrit : ∀ t, gradG_STR02950 h γ (Lamp_STR02956 ψ (h, γ) x).val t = 0)
    (w g : ℝ → ℝ) (hw : IsPeriodicWeakDerivative_STR02933 w g)
    (h0 : normInt_STR02933 w = 0)
    (hc : normInt_STR02933 (fun t => w t * Real.cos t) = 0)
    (hs : normInt_STR02933 (fun t => w t * Real.sin t) = 0) :
    let u := Lamp_STR02956 ψ (h, γ) x
    let T := fderiv ℝ (Lamp_STR02956 ψ (h, γ)) x v
    normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * deriv T.val t * g t) -
      (1 + γ) * (normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t * w t) -
        normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * T.val t) *
          normInt_STR02933 (fun t => rhoT_STR02901 h u.val t * w t)) = 0 := by
  exact ordinaryRoot_linearized_complement_zero h γ _ _ w g hw h0 hc hs
    (ordinaryRangeGraph_projected_linearized_zero hU hψC hψV hR h γ x v hx hcrit)

end DGPS.Examples.ThreeSpeciesCircle
