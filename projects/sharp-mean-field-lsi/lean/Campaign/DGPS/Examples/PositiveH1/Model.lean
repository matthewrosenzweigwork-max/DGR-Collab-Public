import Mathlib
import DGPS.Examples.PositiveH1.Fourier
import DGPS.Model.Data

/-!
# Positive `H¹` interaction data (H1004)

`V = 0`, `W(x,y) = κ (R(x-y) - A)` with `κ = 1/100` on `𝕋¹` (`positiveH1`), and the cutoffs
`W_M(x,y) = κ (R_M(x-y) - R_M(0))` (`positiveH1Cutoff M`).

Reading choices: `H¹(𝕋²)` membership of `W` is the campaign's `IsWeakGradient` on `Torus 2`, with the
two-variable function `pairFun W p = W (p 0) (p 1)` and difference coordinates
`diffPt p = p 0 - p 1` (Haar preserving, `measurePreserving_diffPt`). The weak gradient is
`(κ R'(x-y), -κ R'(x-y))` (`gradPair`), and it is proved for every weak derivative `R'` of `R`
(not just the one built in H1003). The diagonal identity `W(x,x) = 0` comes from the continuous
formula, independently of any weak-gradient representative.
-/

open MeasureTheory Filter Topology
open DGPS DGPS.Examples.PositiveH1.Fourier
namespace DGPS.Examples.PositiveH1.Model

noncomputable def diffPt (p : Torus 2) : Torus 1 := fun _ => p 0 - p 1

noncomputable def pairFun (F : Torus 1 → Torus 1 → ℝ) (p : Torus 2) : ℝ :=
  F (fun _ => p 0) (fun _ => p 1)

noncomputable def diffLin : (Fin 2 → ℝ) →L[ℝ] (Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun _ : Fin 1 =>
    ((ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.proj 1)

theorem diffLin_apply (v : Fin 2 → ℝ) (i : Fin 1) : diffLin v i = v 0 - v 1 := by
  simp [diffLin]

theorem diffPt_lift (v : Fin 2 → ℝ) : diffPt (torusLift v) = torusLift (diffLin v) := by
  funext i
  simp [diffPt, torusLift, SharpLSI.liftT, diffLin_apply]

theorem diffLin_single_zero : diffLin (Pi.single 0 1) = Pi.single 0 1 := by
  funext i
  rw [diffLin_apply, Subsingleton.elim i 0]; simp

theorem diffLin_single_one : diffLin (Pi.single 1 1) = -(Pi.single 0 1) := by
  funext i
  rw [diffLin_apply, Subsingleton.elim i 0]; simp

theorem measurePreserving_diffPt : MeasurePreserving diffPt (haar 2) (haar 1) := by
  set μ : Measure (AddCircle (1:ℝ)) := AddCircle.haarAddCircle with hμ
  have h2 : haar 2 = Measure.pi fun _ : Fin 2 => μ := haar_eq_pi_haarAddCircle 2
  have h1 : haar 1 = Measure.pi fun _ : Fin 1 => μ := haar_eq_pi_haarAddCircle 1
  have A := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have B := measurePreserving_prod_sub_swap μ μ
  have C : MeasurePreserving (fun z : AddCircle (1:ℝ) × AddCircle (1:ℝ) => z.2) (μ.prod μ) μ :=
    measurePreserving_snd
  have D := (measurePreserving_funUnique μ (Fin 1)).symm (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ)))
  have E := D.comp (C.comp (B.comp A))
  rw [h2, h1]
  have hf : diffPt = (MeasurableEquiv.funUnique (Fin 1) (AddCircle (1:ℝ))).symm ∘
      (fun z : AddCircle (1:ℝ) × AddCircle (1:ℝ) => z.2) ∘
      (fun z : AddCircle (1:ℝ) × AddCircle (1:ℝ) => (z.2, z.1 - z.2)) ∘
      (MeasurableEquiv.piFinTwo fun _ : Fin 2 => AddCircle (1:ℝ)) := by
    funext p i
    simp [diffPt, MeasurableEquiv.piFinTwo]
  rw [hf]; exact E

theorem torus2_exists_lift (x : Torus 2) : ∃ v : Fin 2 → ℝ, x = torusLift v :=
  ⟨SharpLSI.secT x, (SharpLSI.liftT_secT x).symm⟩

/-- Smoothness and partial derivatives of `κ (f(x-y) - c)` on `𝕋²`. -/
theorem diffKernel_aux (κ c : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    IsSmoothPeriodic (fun p : Torus 2 => κ * (f (diffPt p) - c)) ∧
    (∀ x, coordPartial 0 (fun p : Torus 2 => κ * (f (diffPt p) - c)) x
        = κ * coordPartial 0 f (diffPt x)) ∧
    (∀ x, coordPartial 1 (fun p : Torus 2 => κ * (f (diffPt p) - c)) x
        = -(κ * coordPartial 0 f (diffPt x))) := by
  have hG : ((fun p : Torus 2 => κ * (f (diffPt p) - c)) ∘ torusLift)
      = fun v => κ * ((f ∘ torusLift) (diffLin v) - c) := by
    funext v; simp [diffPt_lift]
  refine ⟨?_, ?_, ?_⟩
  · unfold IsSmoothPeriodic
    rw [hG]
    exact contDiff_const.mul ((hf.comp diffLin.contDiff).sub contDiff_const)
  · intro x
    obtain ⟨v, rfl⟩ := torus2_exists_lift x
    have h := (hf.differentiable (by simp) (diffLin v)).hasFDerivAt.comp v diffLin.hasFDerivAt
    have H := (h.sub_const c).const_mul κ
    have e1 := congrFun (coordPartial_comp_torusLift (d := 2) 0
      (fun p : Torus 2 => κ * (f (diffPt p) - c))) v
    have e2 := congrFun (coordPartial_comp_torusLift (d := 1) 0 f) (diffLin v)
    replace e1 : coordPartial 0 (fun p : Torus 2 => κ * (f (diffPt p) - c)) (torusLift v) = _ := e1
    replace e2 : coordPartial 0 f (torusLift (diffLin v)) = _ := e2
    have H' : HasFDerivAt (fun v => κ * ((f ∘ torusLift) (diffLin v) - c)) _ v := H
    rw [e1, hG, H'.fderiv]
    simp [diffLin_single_zero, diffPt_lift, e2]
  · intro x
    obtain ⟨v, rfl⟩ := torus2_exists_lift x
    have h := (hf.differentiable (by simp) (diffLin v)).hasFDerivAt.comp v diffLin.hasFDerivAt
    have H := (h.sub_const c).const_mul κ
    have e1 := congrFun (coordPartial_comp_torusLift (d := 2) 1
      (fun p : Torus 2 => κ * (f (diffPt p) - c))) v
    have e2 := congrFun (coordPartial_comp_torusLift (d := 1) 0 f) (diffLin v)
    replace e1 : coordPartial 1 (fun p : Torus 2 => κ * (f (diffPt p) - c)) (torusLift v) = _ := e1
    replace e2 : coordPartial 0 f (torusLift (diffLin v)) = _ := e2
    have H' : HasFDerivAt (fun v => κ * ((f ∘ torusLift) (diffLin v) - c)) _ v := H
    rw [e1, hG, H'.fderiv]
    simp [diffLin_single_one, diffPt_lift, e2]

noncomputable def kappa : ℝ := 1 / 100

theorem kappa_pos : 0 < kappa := by unfold kappa; norm_num

theorem continuous_diffPt : Continuous diffPt :=
  continuous_pi fun _ => (continuous_apply 0).sub (continuous_apply 1)

theorem continuous_single2 (i : Fin 2) :
    Continuous (fun t : ℝ => (EuclideanSpace.single i t : Tangent 2)) :=
  (Isometry.of_dist_eq fun a b => PiLp.dist_single_same 2 (fun _ : Fin 2 => ℝ) i a b).continuous

/-- The vector `(r, -r)` of `ℝ²`. -/
noncomputable def gradPair (r : ℝ) : Tangent 2 :=
  EuclideanSpace.single 0 r - EuclideanSpace.single 1 r

theorem gradPair_zero (r : ℝ) : gradPair r 0 = r := by simp [gradPair]

theorem gradPair_one (r : ℝ) : gradPair r 1 = -r := by simp [gradPair]

theorem continuous_gradPair : Continuous gradPair :=
  (continuous_single2 0).sub (continuous_single2 1)

theorem memLp_gradPair {r : Torus 2 → ℝ} (hr : MemLp r 2 (haar 2)) :
    MemLp (fun p => gradPair (r p)) 2 (haar 2) := by
  refine (hr.const_mul 2).mono
    (continuous_gradPair.comp_aestronglyMeasurable hr.aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  calc ‖gradPair (r p)‖ ≤ ‖(EuclideanSpace.single 0 (r p) : Tangent 2)‖ +
        ‖(EuclideanSpace.single 1 (r p) : Tangent 2)‖ := norm_sub_le _ _
    _ = ‖(2 : ℝ) * r p‖ := by
      simp only [PiLp.norm_single, Real.norm_eq_abs, abs_mul]
      norm_num; ring

theorem weakGradient_pair_dR :
    IsWeakGradient (fun p : Torus 2 => kappa * (R (diffPt p) - A))
      (fun p => gradPair (kappa * dR (diffPt p))) := by
  have hmp := measurePreserving_diffPt
  have hcont : Continuous (fun p : Torus 2 => kappa * (R (diffPt p) - A)) :=
    continuous_const.mul ((continuous_R.comp continuous_diffPt).sub continuous_const)
  have hdR : MemLp (fun p : Torus 2 => dR (diffPt p)) 2 (haar 2) :=
    memLp_dR.comp_measurePreserving hmp
  refine ⟨memLp_two_of_continuous hcont, memLp_gradPair (hdR.const_mul kappa), ?_⟩
  intro φ hφ j
  obtain ⟨C1, hC1⟩ := exists_abs_le_of_continuous (hφ.continuous_coordPartial j)
  obtain ⟨C2, hC2⟩ := exists_abs_le_of_continuous hφ.continuous_torus
  have hint : ∀ {f : Torus 2 → ℝ}, Continuous f → Integrable f (haar 2) := fun hf =>
    (memLp_two_of_continuous hf).integrable one_le_two
  have hsm : ∀ M, IsSmoothPeriodic (fun p : Torus 2 => kappa * (RM M (diffPt p) - A)) :=
    fun M => (diffKernel_aux kappa A (isSmoothPeriodic_RM M)).1
  have hA : Tendsto (fun M => ENNReal.ofReal (kappa * tailA M)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_tailA.const_mul kappa)
  have key : ∀ (s : ℝ), (∀ M x, coordPartial j (fun p : Torus 2 => kappa * (RM M (diffPt p) - A)) x
        = s * (kappa * dRM M (diffPt x))) →
      (∀ p, gradPair (kappa * dR (diffPt p)) j = s * (kappa * dR (diffPt p))) →
      ∫ x, kappa * (R (diffPt x) - A) * coordPartial j φ x ∂haar 2
        = -∫ x, gradPair (kappa * dR (diffPt x)) j * φ x ∂haar 2 := by
    intro s hs hg
    have hBt : Tendsto (fun M => ENNReal.ofReal (|s| * kappa * B M)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_B.const_mul (|s| * kappa))
    have T1 := tendsto_integral_mul_of_lintegral (l := atTop)
      (F := fun M p => kappa * (RM M (diffPt p) - A))
      (f := fun p => kappa * (R (diffPt p) - A))
      (ψ := coordPartial j φ) (C := C1)
      (fun M => hint (continuous_const.mul
        ((((continuous_RM M).comp continuous_diffPt)).sub continuous_const)))
      (hint hcont) (hφ.continuous_coordPartial j) hC1
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hA (fun _ => bot_le) (fun M => by
        calc ∫⁻ y, ‖kappa * (RM M (diffPt y) - A) - kappa * (R (diffPt y) - A)‖ₑ ∂haar 2
            ≤ ∫⁻ _y, ENNReal.ofReal (kappa * tailA M) ∂haar 2 := by
              refine lintegral_mono fun y => ?_
              rw [← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_pos kappa_pos]
              refine mul_le_mul_of_nonneg_left ?_ kappa_pos.le
              rw [show RM M (diffPt y) - A - (R (diffPt y) - A) = -(R (diffPt y) - RM M (diffPt y))
                by ring, abs_neg]
              exact abs_R_sub_RM_le M _
          _ = ENNReal.ofReal (kappa * tailA M) := by simp))
    have hL2 : ∀ M : ℕ, 1 ≤ M → ∫⁻ y, ‖s * (kappa * dRM M (diffPt y)) - s * (kappa * dR (diffPt y))‖ₑ ∂haar 2
        ≤ ENNReal.ofReal (|s| * kappa * B M) := by
      intro M hM
      have hae : AEMeasurable (fun b : Torus 1 => ‖s * (kappa * dRM M b) - s * (kappa * dR b)‖ₑ)
          (haar 1) := by
        have hc : Continuous (fun b : Torus 1 => s * (kappa * dRM M b)) :=
          continuous_const.mul (continuous_const.mul (continuous_dRM M))
        have := (hc.aestronglyMeasurable (μ := haar 1)).sub
          ((memLp_dR.aestronglyMeasurable.const_mul kappa).const_mul s)
        exact this.enorm
      have hmap := lintegral_map' (μ := haar 2) (g := diffPt)
        (f := fun b : Torus 1 => ‖s * (kappa * dRM M b) - s * (kappa * dR b)‖ₑ)
        (by rw [hmp.map_eq]; exact hae) hmp.aemeasurable
      rw [hmp.map_eq] at hmap
      refine le_of_eq_of_le hmap.symm ?_
      calc ∫⁻ b, ‖s * (kappa * dRM M b) - s * (kappa * dR b)‖ₑ ∂haar 1
          = ∫⁻ b, ENNReal.ofReal (|s| * kappa) * ‖dRM M b - dR b‖ₑ ∂haar 1 := by
            refine lintegral_congr fun b => ?_
            rw [show s * (kappa * dRM M b) - s * (kappa * dR b) = (s * kappa) * (dRM M b - dR b)
              by ring, enorm_mul, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
              abs_of_pos kappa_pos]
        _ = ENNReal.ofReal (|s| * kappa) * ∫⁻ b, ‖dRM M b - dR b‖ₑ ∂haar 1 :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (|s| * kappa) * ENNReal.ofReal (B M) := by
            gcongr; exact lintegral_dRM_sub_le hM
        _ = ENNReal.ofReal (|s| * kappa * B M) := by
            exact (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg s) kappa_pos.le)).symm
    have T2 := tendsto_integral_mul_of_lintegral (l := atTop)
      (F := fun M p => s * (kappa * dRM M (diffPt p)))
      (f := fun p => s * (kappa * dR (diffPt p)))
      (ψ := φ) (C := C2)
      (fun M => hint (continuous_const.mul (continuous_const.mul
        ((continuous_dRM M).comp continuous_diffPt))))
      (((hdR.const_mul kappa).const_mul s).integrable one_le_two) hφ.continuous_torus hC2
      (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBt
        (Eventually.of_forall fun _ => bot_le)
        (Filter.eventually_atTop.2 ⟨1, fun M hM => hL2 M hM⟩))
    have e : ∀ M, ∫ x, kappa * (RM M (diffPt x) - A) * coordPartial j φ x ∂haar 2
        = -∫ x, s * (kappa * dRM M (diffPt x)) * φ x ∂haar 2 := by
      intro M
      rw [integral_mul_coordPartial_of_smooth (hsm M) hφ j]
      simp_rw [hs]
    have T2' := T2.neg
    simp_rw [← e] at T2'
    have := tendsto_nhds_unique T1 T2'
    simp_rw [hg]
    simpa using this
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hj with rfl | rfl
  · refine key 1 (fun M x => ?_) (fun p => ?_)
    · rw [(diffKernel_aux kappa A (isSmoothPeriodic_RM M)).2.1 x, coordPartial_RM]; ring
    · simp [gradPair_zero]
  · refine key (-1) (fun M x => ?_) (fun p => ?_)
    · rw [(diffKernel_aux kappa A (isSmoothPeriodic_RM M)).2.2 x, coordPartial_RM]; ring
    · simp [gradPair_one]

theorem RM_neg (M : ℕ) (x : Torus 1) : RM M (-x) = RM M x := by
  unfold RM
  exact Finset.sum_congr rfl fun n _ => by rw [cosMode_neg]

/-- The positive `H¹` interaction data: `V = 0`, `W(x,y) = κ (R(x-y) - A)` with `κ = 1/100`. -/
noncomputable def positiveH1 : DGPS.InteractionData 1 where
  V := fun _ => 0
  W := fun x y => kappa * (R (x - y) - A)
  V_continuous := continuous_const
  W_continuous := continuous_const.mul
    ((continuous_R.comp (continuous_fst.sub continuous_snd)).sub continuous_const)
  W_symm := fun x y => by rw [show y - x = -(x - y) from (neg_sub x y).symm, R_neg]
  W_diag := fun x => by simp [R_zero]

/-- The cutoff data `W_M(x,y) = κ (R_M(x-y) - R_M(0))`. -/
noncomputable def positiveH1Cutoff (M : ℕ) : DGPS.InteractionData 1 where
  V := fun _ => 0
  W := fun x y => kappa * (RM M (x - y) - RM M 0)
  V_continuous := continuous_const
  W_continuous := continuous_const.mul
    (((continuous_RM M).comp (continuous_fst.sub continuous_snd)).sub continuous_const)
  W_symm := fun x y => by rw [show y - x = -(x - y) from (neg_sub x y).symm, RM_neg]
  W_diag := fun x => by simp

theorem pairFun_positiveH1 :
    pairFun positiveH1.W = fun p : Torus 2 => kappa * (R (diffPt p) - A) := rfl

theorem pairFun_cutoff (M : ℕ) :
    pairFun (positiveH1Cutoff M).W = fun p : Torus 2 => kappa * (RM M (diffPt p) - RM M 0) := rfl

theorem weakGradient_pair_of_weakDerivative {R' : Torus 1 → ℝ}
    (h : IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (R' x) : Tangent 1))) :
    IsWeakGradient (pairFun positiveH1.W) (fun p => gradPair (kappa * R' (diffPt p))) := by
  have hae := h.ae_eq weak_gradient_R
  have hR : R' =ᵐ[haar 1] dR := by
    filter_upwards [hae] with x hx
    simpa using congrArg (fun v : Tangent 1 => v 0) hx
  have hR2 : (fun p : Torus 2 => R' (diffPt p)) =ᵐ[haar 2] fun p => dR (diffPt p) :=
    measurePreserving_diffPt.quasiMeasurePreserving.ae_eq_comp hR
  rw [pairFun_positiveH1]
  refine weakGradient_pair_dR.congr_ae (Filter.EventuallyEq.refl _ _) ?_
  filter_upwards [hR2] with p hp
  simp only [hp]

theorem positive_h1_interaction_data :
    positiveH1.V = (fun _ => 0) ∧ kappa = 1 / 100 ∧
    (∀ x y, positiveH1.W x y = kappa * (R (x - y) - A)) ∧
    Continuous (fun p : Torus 1 × Torus 1 => positiveH1.W p.1 p.2) ∧
    (∀ x y, positiveH1.W x y = positiveH1.W y x) ∧
    (∀ x, positiveH1.W x x = 0) ∧
    MemH1 (pairFun positiveH1.W) ∧
    (∃ R' : Torus 1 → ℝ,
      IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (R' x) : Tangent 1)) ∧
      IsWeakGradient (pairFun positiveH1.W) (fun p => gradPair (kappa * R' (diffPt p)))) ∧
    (∀ R' : Torus 1 → ℝ,
      IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (R' x) : Tangent 1)) →
      IsWeakGradient (pairFun positiveH1.W) (fun p => gradPair (kappa * R' (diffPt p)))) ∧
    (∀ M : ℕ, 2 ≤ M →
      (positiveH1Cutoff M).V = (fun _ => 0) ∧
      (∀ x y, (positiveH1Cutoff M).W x y = kappa * (RM M (x - y) - RM M 0)) ∧
      IsSmoothPeriodic (pairFun (positiveH1Cutoff M).W) ∧
      (∀ x y, (positiveH1Cutoff M).W x y = (positiveH1Cutoff M).W y x) ∧
      (∀ x, (positiveH1Cutoff M).W x x = 0) ∧
      (∀ x, coordPartial 0 (pairFun (positiveH1Cutoff M).W) x = kappa * dRM M (diffPt x)) ∧
      (∀ x, coordPartial 1 (pairFun (positiveH1Cutoff M).W) x = -(kappa * dRM M (diffPt x)))) := by
  have hex : ∃ R' : Torus 1 → ℝ,
      IsWeakGradient R (fun x => (EuclideanSpace.single (0 : Fin 1) (R' x) : Tangent 1)) :=
    ⟨dR, weak_gradient_R⟩
  refine ⟨rfl, rfl, fun _ _ => rfl, positiveH1.W_continuous, positiveH1.W_symm, positiveH1.W_diag,
    ⟨_, weakGradient_pair_dR.congr_ae (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)⟩,
    ?_, fun R' h => weakGradient_pair_of_weakDerivative h, fun M _ => ?_⟩
  · obtain ⟨R', h⟩ := hex
    exact ⟨R', h, weakGradient_pair_of_weakDerivative h⟩
  · have aux := diffKernel_aux kappa (RM M 0) (isSmoothPeriodic_RM M)
    refine ⟨rfl, fun _ _ => rfl, aux.1, (positiveH1Cutoff M).W_symm, (positiveH1Cutoff M).W_diag,
      fun x => ?_, fun x => ?_⟩
    · rw [pairFun_cutoff, aux.2.1 x, coordPartial_RM]
    · rw [pairFun_cutoff, aux.2.2 x, coordPartial_RM]

end DGPS.Examples.PositiveH1.Model
