import DGPS.Examples.ThreeSpeciesCircle.InteractingExternalChart
import DGPS.Examples.ThreeSpeciesCircle.InteractingExternalRotation

/-! Actual third-turn covariance on the SAME periodic chart and common-field
parameter carriers. The retained T21 pullback identities give the ordinary
part. No invariant implicit-function domain or optimizer classification is an
input; graph identification still requires true neighborhood entry/uniqueness. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Translation of the actual C2-Holder chart, with its original full norm. -/
def interactingC2Translate (δ : ℝ) (u : PeriodicC2_STR02969) : PeriodicC2_STR02969 :=
  PeriodicC2_STR02969.mk (pb_STR02916 1 (-δ) u.val)
    (isC2Alpha_pb_STR02916 (Or.inl rfl) (-δ) u.isC2)

theorem interactingC2Translate_norm (δ : ℝ) (u : PeriodicC2_STR02969) :
    ‖interactingC2Translate δ u‖ = ‖u‖ :=
  c2Norm_pb_STR02916 (Or.inl rfl) (-δ) u.isC2

/-- The full chart transform is an isometry, hence continuous in the actual
capture topology; this does not assert invariance of any chosen neighborhood. -/
theorem interactingC2Translate_isometry (δ : ℝ) : Isometry (interactingC2Translate δ) := by
  apply Isometry.of_dist_eq
  intro u v
  have he : interactingC2Translate δ u - interactingC2Translate δ v =
      interactingC2Translate δ (u - v) := by
    apply Subtype.ext
    funext t
    rfl
  rw [dist_eq_norm, dist_eq_norm, he, interactingC2Translate_norm]

private theorem third_symmetry (j : Fin 3) :
    SymOK_STR02921 1 (-(2 * Real.pi * ((j : ℕ) / 3))) 1 := by
  simpa only [Int.cast_natCast, mul_div_assoc] using symOK_rot_STR02921 ((j : ℕ) : ℤ)

/-- Exact covariance of the actual normalized density on the retained carrier. -/
theorem interactingC2Translate_rho (h : ℝ) (j : Fin 3) (u : PeriodicC2_STR02969) :
    rho_STR02954 (h, e0_STR02955 (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u)) =
      interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) (rho_STR02954 (h, e0_STR02955 u)) := by
  apply ext_STR02954
  funext t
  have he := congrFun (rho_pb_STR02921 (third_symmetry j) h u.isC2.1) t
  change (rho_STR02954 (h, e0_STR02955 (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u))).val t = (rho_STR02954 (h, e0_STR02955 u)).val (t - 2 * Real.pi * ((j : ℕ) / 3))
  simp only [rho_val_STR02954, e0_val_STR02955]
  change rhoT_STR02901 h (pb_STR02916 1 (-(2 * Real.pi * ((j : ℕ) / 3))) u.val) t =
    rhoT_STR02901 h u.val (t - 2 * Real.pi * ((j : ℕ) / 3))
  simpa only [pb_STR02916, one_mul, sub_eq_add_neg] using he

/-- Exact covariance of the ordinary chart gradient, imported through the
verified T21 ordinary symmetry identity, including its normalization terms. -/
theorem interactingC2Translate_Gfun (h γ : ℝ) (j : Fin 3) (u : PeriodicC2_STR02969) :
    Gfun_STR02955 h γ (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) =
      interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) (Gfun_STR02955 h γ u) := by
  apply ext_STR02954
  funext t
  have he := congrFun (gradG_pb_STR02921 (third_symmetry j) h γ u.isC2.1
    u.isC2.2.1 u.isC2.2.2.1) t
  change (Gfun_STR02955 h γ (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u)).val t = (Gfun_STR02955 h γ u).val (t - 2 * Real.pi * ((j : ℕ) / 3))
  simp only [Gfun_val_STR02955]
  change gradG_STR02950 h γ (pb_STR02916 1 (-(2 * Real.pi * ((j : ℕ) / 3))) u.val) t =
    gradG_STR02950 h γ u.val (t - 2 * Real.pi * ((j : ℕ) / 3))
  simpa only [pb_STR02916, one_mul, sub_eq_add_neg] using he

private theorem JC2_turn (h γ : ℝ) (j : Fin 3) (u : PeriodicC2_STR02969) :
    JC2_STR02956 h γ (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) = JC2_STR02956 h γ u := by
  rw [JC2_eq_STR02956, JC2_eq_STR02956]
  change Jchart_STR02950 h γ (pb_STR02916 1 (-(2 * Real.pi * ((j : ℕ) / 3))) u.val) = Jchart_STR02950 h γ u.val
  simpa only [one_mul] using Jchart_pb_STR02921 (third_symmetry j) h γ u.isC2.1 u.isC2.2.1

/-- The actual common-field mean transports with both density and field. -/
theorem externalChartMean_interactingThirdTurn (h : ℝ) (j : Fin 3)
    (u : PeriodicC2_STR02969) (V : PeriodicHolder_STR02968) :
    externalChartMean h (interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u)
      (interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) V) = externalChartMean h u V := by
  let δ := 2 * Real.pi * ((j : ℕ) / 3)
  have hρ := interactingC2Translate_rho h j u
  unfold externalChartMean
  rw [hρ, meanCLM_apply_STR02954, meanCLM_apply_STR02954]
  change meanT_STR02901 ((interactingHolderTranslate δ (rho_STR02954 (h, e0_STR02955 u))) *
      interactingHolderTranslate δ V).val = meanT_STR02901 (rho_STR02954 (h, e0_STR02955 u) * V).val
  have he : ((interactingHolderTranslate δ (rho_STR02954 (h, e0_STR02955 u))) *
      interactingHolderTranslate δ V).val =
      pb_STR02916 1 (-δ) (fun t => rhoT_STR02901 h u.val t * V.val t) := by
    funext t
    rw [val_mul_STR02954]
    change (rho_STR02954 (h, e0_STR02955 u)).val (t - δ) * V.val (t - δ) = _
    rw [rho_val_STR02954, e0_val_STR02955]
    change rhoT_STR02901 h u.val (t - δ) * V.val (t - δ) =
      rhoT_STR02901 h u.val (1 * t + -δ) * V.val (1 * t + -δ)
    simp only [one_mul, sub_eq_add_neg]
  rw [he]
  have hr : (rho_STR02954 (h, e0_STR02955 u) * V).val =
      (fun t => rhoT_STR02901 h u.val t * V.val t) := by
    funext t
    rw [val_mul_STR02954, Pi.mul_apply, rho_val_STR02954, e0_val_STR02955]
  rw [hr]
  have hp : Function.Periodic (fun t => rhoT_STR02901 h u.val t * V.val t) (2 * Real.pi) :=
    (periodic_rho_STR02950 h u.isC2.1).mul V.isPerHolder.1
  exact meanT_pb_STR02916 (Or.inl rfl) (-δ) hp

/-- Covariance of the full external common-field gradient. The field and chart
are transformed, while the physical rate coordinate is unchanged. -/
theorem externalChartGradient_interactingThirdTurn (h γ : ℝ) (j : Fin 3)
    (u : PeriodicC2_STR02969) (V : PeriodicHolder_STR02968) :
    externalChartGradient h
        (interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) V, γ,
          interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) =
      interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) (externalChartGradient h (V, γ, u)) := by
  unfold externalChartGradient
  rw [interactingC2Translate_Gfun, externalChartMean_interactingThirdTurn, interactingC2Translate_rho]
  apply ext_STR02954
  funext t
  rfl

/-- Exact augmented external value covariance with the SAME common scalar c.
No symmetry of a selected complement graph or its parameter domain is assumed. -/
theorem externalChartDeficit_interactingThirdTurn (h γ c : ℝ) (j : Fin 3)
    (u : PeriodicC2_STR02969) (V : PeriodicHolder_STR02968) :
    externalChartDeficit h
        ((interactingHolderTranslate (2 * Real.pi * ((j : ℕ) / 3)) V, c), γ,
          interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) u) =
      externalChartDeficit h ((V, c), γ, u) := by
  unfold externalChartDeficit
  rw [JC2_turn, externalChartMean_interactingThirdTurn]

end DGPS.Examples.ThreeSpeciesCircle
