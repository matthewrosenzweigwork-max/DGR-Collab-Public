import SharpSymmetricLSI.Paper.AdmFinite
import SharpSymmetricLSI.Paper.KLLsc

/-!
# Admissible densities exist for `d ≥ 1` (D7 sanity lemma)

`ρ = s²/Z` with `s(x) = (1 - ‖x₀‖/δ)⁺` a tent in the first coordinate: `√ρ` is Lipschitz, hence in
`H¹(m)`, and `ρ` lives on `{‖x₀‖ < δ}`, of Haar measure `≤ 2δ`, so (Gibbs' inequality)
`H(ρ|m) ≥ log(1/(2δ)) - log 2` is large; since `V`, `W` are bounded, `G(ρ) > 0` for small `δ`.
This file imports nothing above `D06`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The tent `(1 - ‖x₀‖/δ)⁺`. -/
def tent (hd : 1 ≤ d) (δ : ℝ) (x : Torus d) : ℝ := max 0 (1 - ‖x ⟨0, hd⟩‖ / δ)

theorem continuous_tent (hd : 1 ≤ d) (δ : ℝ) : Continuous (tent hd δ) := by
  unfold tent; fun_prop

theorem tent_nonneg (hd : 1 ≤ d) (δ : ℝ) (x : Torus d) : 0 ≤ tent hd δ x := le_max_left _ _

theorem tent_le_one (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (x : Torus d) : tent hd δ x ≤ 1 :=
  max_le zero_le_one (by have := norm_nonneg (x ⟨0, hd⟩); have : 0 ≤ ‖x ⟨0, hd⟩‖ / δ := by positivity
                         linarith)

theorem lipschitz_tent (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal δ⁻¹) (tent hd δ ∘ liftT) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Function.comp, tent, liftT, Real.dist_eq]
  have h1 : |‖((x ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ - ‖((y ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖| ≤ dist x y := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [← AddCircle.coe_sub]
    refine (QuotientAddGroup.norm_mk_le_norm).trans ?_
    rw [Real.norm_eq_abs, ← Real.dist_eq]
    exact dist_le_pi_dist x y _
  have h2 : |max 0 (1 - ‖((x ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ / δ) -
      max 0 (1 - ‖((y ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ / δ)| ≤
      |‖((x ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ - ‖((y ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖| / δ := by
    rw [max_comm 0, max_comm 0]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show 1 - ‖((x ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ / δ - (1 - ‖((y ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ / δ)
        = -((‖((x ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖ - ‖((y ⟨0, hd⟩ : ℝ) : UnitAddCircle)‖) / δ) by ring,
      abs_neg, abs_div, abs_of_pos hδ]
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hδ.le)]
  calc _ ≤ _ := h2
    _ ≤ dist x y / δ := by gcongr
    _ = δ⁻¹ * dist x y := by ring

/-- `|ρ(V) + W(ρ,ρ)/2| ≤ C` on probability measures. -/
theorem abs_energy_le (hyp : Hyp V W KV KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ →
      |potE V ρ + interE W ρ ρ / 2| ≤ C := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBV0 : 0 ≤ BV := (abs_nonneg _).trans (hBV 0)
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  refine ⟨BV + BW / 2, by positivity, fun ρ _ => ?_⟩
  have h1 : |potE V ρ| ≤ BV := by
    unfold potE
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |V x| ∂ρ ≤ ∫ _x, BV ∂ρ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun x => hBV x)
      _ = BV := by simp
  have h2 : |interE W ρ ρ| ≤ BW := by
    unfold interE
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |∫ x, W x y ∂ρ| ∂ρ ≤ ∫ _y, BW ∂ρ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y => ?_)
          refine (abs_integral_le_integral_abs).trans ?_
          calc ∫ x, |W x y| ∂ρ ≤ ∫ _x, BW ∂ρ :=
                integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
                  (integrable_const _) (Eventually.of_forall fun x => hBW (x, y))
            _ = BW := by simp
      _ = BW := by simp
  calc |potE V ρ + interE W ρ ρ / 2| ≤ |potE V ρ| + |interE W ρ ρ| / 2 := by
        refine (abs_add_le _ _).trans ?_; rw [abs_div, abs_two]
    _ ≤ BV + BW / 2 := by linarith

/-- **The D7 sanity lemma for `d ≥ 1`.** -/
theorem admissible_nonempty_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    ∃ ρ : Torus d → ℝ, (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar d = 1 ∧
      MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧ 0 < gap V W (densMeasure ρ) := by
  obtain ⟨C0, hC00, hC0⟩ := abs_energy_le hyp (V := V) (W := W)
  set i0 : Fin d := ⟨0, hd⟩
  set L : ℝ := 2 * C0 + 1 + Real.log 2
  have hL0 : 0 ≤ L := by have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity
  set δ : ℝ := Real.exp (-L) / 2
  have hδ : 0 < δ := by positivity
  set t := tent hd δ
  have htc := continuous_tent hd δ
  have ht0 := tent_nonneg hd δ
  have ht1 := tent_le_one hd hδ
  set Z := ∫ x, t x ^ 2 ∂haar d
  have hti : Integrable (fun x => t x ^ 2) (haar d) :=
    Integrable.of_bound (htc.pow 2).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [ht0 x, ht1 x])
  have hZ : 0 < Z := by
    have h0 : t 0 = 1 := by simp [t, tent]
    refine (htc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun x => sq_nonneg _) (x := 0) (by simp [h0])
  set ρ : Torus d → ℝ := fun x => t x ^ 2 / Z
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => div_nonneg (sq_nonneg _) hZ.le
  have hρ1 : ∫ x, ρ x ∂haar d = 1 := by
    simp only [ρ]; rw [integral_div]; exact div_self hZ.ne'
  refine ⟨ρ, hρ0, hρ1, ?_, ?_⟩
  · -- `√ρ = t/√Z` is Lipschitz
    set u : Torus d → ℝ := fun x => (Real.sqrt Z)⁻¹ * t x
    have hu : (fun x => Real.sqrt (ρ x)) = u := by
      funext x
      simp only [ρ, u]
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (ht0 x), div_eq_inv_mul]
    rw [hu]
    have huc : Continuous u := continuous_const.mul htc
    set K : ℝ := (Real.sqrt Z)⁻¹ * δ⁻¹
    have hK0 : 0 ≤ K := by positivity
    have huL : LipschitzWith (Real.toNNReal K) (u ∘ liftT) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have h := (lipschitz_tent hd hδ).dist_le_mul x y
      rw [Real.coe_toNNReal _ (inv_nonneg.mpr hδ.le)] at h
      rw [Real.coe_toNNReal _ hK0]
      simp only [Function.comp, u, Real.dist_eq] at h ⊢
      rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      calc (Real.sqrt Z)⁻¹ * |t (liftT x) - t (liftT y)| ≤ (Real.sqrt Z)⁻¹ * (δ⁻¹ * dist x y) :=
            mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = K * dist x y := by ring
    have hw := isWeakGrad_lipGrad huc huL
    refine ⟨⟨_, hw⟩, MemLp.of_bound huc.aestronglyMeasurable (Real.sqrt Z)⁻¹
      (Eventually.of_forall fun x => ?_), ?_⟩
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (ht0 x))]
      calc (Real.sqrt Z)⁻¹ * t x ≤ (Real.sqrt Z)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (ht1 x) (inv_nonneg.mpr (Real.sqrt_nonneg _))
        _ = _ := mul_one _
    · refine MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm)
        (Real.sqrt (Fintype.card (Fin d) * K ^ 2)) ?_
      filter_upwards [weakGrad_ae_eq hw] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx]
      refine Real.sqrt_le_sqrt ?_
      unfold sqNorm
      calc ∑ k, lipGrad u x k ^ 2 ≤ ∑ _k : Fin d, K ^ 2 := Finset.sum_le_sum fun k _ => by
            have := abs_lipGrad_le huL x k
            rw [Real.coe_toNNReal _ hK0] at this
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = _ := by simp
  · -- the entropy is large
    haveI hP : IsProbabilityMeasure (densMeasure ρ) := isProbabilityMeasure_densMeasure' hρ0 hρ1
    set A : Set (Torus d) := {x | ‖x i0‖ < δ}
    have hAo : IsOpen A := isOpen_lt (continuous_norm.comp (continuous_apply i0)) continuous_const
    have hAm : MeasurableSet A := hAo.measurableSet
    have hρA : ∀ x ∉ A, ρ x = 0 := fun x hx => by
      simp only [A, Set.mem_setOf_eq, not_lt] at hx
      have : t x = 0 := by
        simp only [t, tent]
        refine max_eq_left ?_
        have : 1 ≤ ‖x i0‖ / δ := (one_le_div hδ).mpr hx
        linarith
      simp [ρ, this]
    have hPAc : densMeasure ρ Aᶜ = 0 := by
      rw [densMeasure, withDensity_apply _ hAm.compl]
      refine (setLIntegral_congr_fun hAm.compl (fun x hx => by rw [hρA x hx, ENNReal.ofReal_zero])).trans ?_
      simp
    have hPA : (densMeasure ρ).real A = 1 := by
      have := prob_compl_eq_zero_iff hAm |>.mp hPAc
      rw [Measure.real_def, this]; simp
    have hmA : (haar d).real A ≤ 2 * δ := by
      have hsub : A ⊆ (fun x : Torus d => x i0) ⁻¹' Metric.closedBall 0 δ := fun x hx => by
        simp only [A, Set.mem_setOf_eq] at hx
        simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]; exact hx.le
      have h1 : (haar d) ((fun x : Torus d => x i0) ⁻¹' Metric.closedBall 0 δ) =
          volume (Metric.closedBall (0 : UnitAddCircle) δ) :=
        (measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) i0).measure_preimage
          measurableSet_closedBall.nullMeasurableSet
      have h2 := measure_mono (μ := haar d) hsub
      rw [h1, AddCircle.volume_closedBall] at h2
      rw [Measure.real_def]
      refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (h2.trans ?_))
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    set g : Torus d → ℝ := A.indicator fun _ => L
    have hgm : Measurable g := measurable_const.indicator hAm
    have hgB : ∀ x, |g x| ≤ L := fun x => by
      by_cases hx : x ∈ A <;> simp [g, hx, abs_of_nonneg hL0, hL0]
    have hdv := dvFun_le_klDiv (ρ := densMeasure ρ) (ν := haar d) hgm hgB
    have hg1 : ∫ x, g x ∂densMeasure ρ = L := by
      rw [integral_indicator_const _ hAm, hPA, one_smul]
    have hexp : ∫ x, Real.exp (g x) ∂haar d ≤ 2 := by
      have hle : ∀ x, Real.exp (g x) ≤ 1 + A.indicator (fun _ => Real.exp L) x := fun x => by
        by_cases hx : x ∈ A <;> simp [g, hx]
      calc ∫ x, Real.exp (g x) ∂haar d ≤ ∫ x, (1 + A.indicator (fun _ => Real.exp L) x) ∂haar d :=
            integral_mono (integrable_of_bdd' (Real.measurable_exp.comp hgm) (C := Real.exp L)
              fun x => by
                rw [abs_of_pos (Real.exp_pos _)]
                exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgB x)))
              ((integrable_const _).add ((integrable_const _).indicator hAm)) hle
        _ = 1 + (haar d).real A * Real.exp L := by
            rw [integral_add (integrable_const _) ((integrable_const _).indicator hAm),
              integral_indicator_const _ hAm]
            simp
        _ ≤ 1 + 2 * δ * Real.exp L := by gcongr
        _ = 2 := by
            simp only [δ]; rw [mul_div_cancel₀ _ two_ne_zero, ← Real.exp_add, neg_add_cancel,
              Real.exp_zero]; norm_num
    have hpos : 0 < ∫ x, Real.exp (g x) ∂haar d := integral_exp_pos (integrable_of_bdd'
      (Real.measurable_exp.comp hgm) (C := Real.exp L) fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgB x)))
    have hdvv : 2 * C0 + 1 ≤ dvFun (densMeasure ρ) (haar d) g := by
      unfold dvFun
      rw [hg1]
      have := Real.log_le_log hpos hexp
      simp only [L] at this ⊢
      linarith
    have hK : ((2 * C0 + 1 : ℝ) : EReal) ≤ ((klDiv (densMeasure ρ) (haar d) : ℝ≥0∞) : EReal) :=
      (EReal.coe_le_coe_iff.mpr hdvv).trans hdv
    -- compare with `F(m)`
    have hFρ : ((C0 + 1 : ℝ) : EReal) ≤ freeEnergy V W (densMeasure ρ) := by
      unfold freeEnergy
      have hr := hC0 (densMeasure ρ) hP
      have hr' : ((-C0 : ℝ) : EReal) ≤ ((potE V (densMeasure ρ) + interE W (densMeasure ρ)
          (densMeasure ρ) / 2 : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr (by have := neg_abs_le (potE V (densMeasure ρ) +
          interE W (densMeasure ρ) (densMeasure ρ) / 2); linarith)
      calc ((C0 + 1 : ℝ) : EReal) = ((2 * C0 + 1 : ℝ) : EReal) + ((-C0 : ℝ) : EReal) := by
            rw [← EReal.coe_add]; congr 1; ring
        _ ≤ _ := add_le_add hK hr'
    have hFm : Fstar V W ≤ ((C0 : ℝ) : EReal) := by
      refine (iInf_le _ (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d))).trans ?_
      simp only [freeEnergy, ProbabilityMeasure.coe_mk, klDiv_self, ENNReal.coe_zero,
        EReal.coe_ennreal_zero, zero_add]
      exact EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans (hC0 (haar d) inferInstance))
    unfold gap
    calc (0 : EReal) < ((C0 + 1 : ℝ) : EReal) - ((C0 : ℝ) : EReal) := by
          rw [← EReal.coe_sub]; exact EReal.coe_pos.mpr (by linarith)
      _ ≤ _ := EReal.sub_le_sub hFρ hFm

end SharpLSI
