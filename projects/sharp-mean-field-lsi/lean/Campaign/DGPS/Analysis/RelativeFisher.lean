import DGPS.Foundations.RelativeEntropy
import DGPS.Foundations.SobolevCalculus
import DGPS.Model.Drift
import SharpSymmetricLSI.Paper.SemiconvexLip2

/-!
# Ordinary relative Fisher information and the positive-reference identity (DEF022)

For a bounded positive reference probability `P = p m` we define the weighted Sobolev domain
`WeightedH1 P` and the ordinary relative Fisher information
`ordinaryRelativeFisher ν P = 4 ∫ |∇ √(dν/dP)|² dP` (`+∞` unless `ν ≪ P` and `√(dν/dP) ∈ H¹(P)`).
For a Lipschitz reference density bounded below we prove the domain equivalence
`relativeSqrt_mem_weightedH1_iff` (relative and absolute `H¹` domains coincide) and the identity
`positiveReference_absolute_identity`:
`I(ρ m | P) = ∫ |2 ∇u - u ∇ log p|² dm` for `ρ = u²`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff NNReal

namespace DGPS.RelativeFisher

variable {d : ℕ}

theorem lipschitzWith_comp_lift {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f) :
    LipschitzWith (Real.toNNReal (L * Real.sqrt d)) (f ∘ DGPS.torusLift) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have h1 := hf (DGPS.torusLift x) (DGPS.torusLift y)
  have h2 := DGPS.torusDist_liftT_le x y
  have h3 : Real.sqrt (∑ j, (x j - y j) ^ 2) ≤ Real.sqrt d * dist x y := by
    rw [← Real.sqrt_sq dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg _)]
    apply Real.sqrt_le_sqrt
    calc ∑ j, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, dist x y ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := dist_le_pi_dist x y j
          rw [Real.dist_eq] at this
          calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
            _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = d * dist x y ^ 2 := by simp
  have hL : (0:ℝ) ≤ L * Real.sqrt d ∨ L * Real.sqrt d < 0 := le_or_gt _ _
  rw [Real.dist_eq]
  simp only [Function.comp]
  have hd := DGPS.torusDist_metric (d := d)
  have hnn : 0 ≤ DGPS.torusDist (DGPS.torusLift x) (DGPS.torusLift y) := by
    unfold DGPS.torusDist SharpLSI.flatDist; exact Real.sqrt_nonneg _
  have key : |f (DGPS.torusLift x) - f (DGPS.torusLift y)| ≤ max L 0 * (Real.sqrt d * dist x y) := by
    calc _ ≤ L * DGPS.torusDist (DGPS.torusLift x) (DGPS.torusLift y) := h1
      _ ≤ max L 0 * DGPS.torusDist (DGPS.torusLift x) (DGPS.torusLift y) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ ≤ _ := mul_le_mul_of_nonneg_left (h2.trans h3) (le_max_right _ _)
  refine key.trans (le_of_eq ?_)
  rw [Real.coe_toNNReal']
  rw [show max (L * Real.sqrt d) 0 = max L 0 * Real.sqrt d by
    rcases le_total L 0 with h | h
    · rw [max_eq_right h, zero_mul, max_eq_right (mul_nonpos_of_nonpos_of_nonneg h (Real.sqrt_nonneg _))]
    · rw [max_eq_left h, max_eq_left (mul_nonneg h (Real.sqrt_nonneg _))]]
  ring


/-- The gradient vector of a Lipschitz function (Rademacher, via the legacy library). -/
noncomputable def lipGradVec (f : DGPS.Torus d → ℝ) : DGPS.Torus d → DGPS.Tangent d :=
  fun x => WithLp.toLp 2 fun j => SharpLSI.lipGrad f x j

theorem lipGradVec_apply (f : DGPS.Torus d → ℝ) (x : DGPS.Torus d) (j : Fin d) :
    lipGradVec f x j = SharpLSI.lipGrad f x j := rfl

theorem continuous_of_lip {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f) :
    Continuous f := by
  have hl := lipschitzWith_comp_lift hf
  -- continuity of f via the quotient map
  have hc : Continuous (f ∘ DGPS.torusLift) := hl.continuous
  exact DGPS.continuous_of_comp_torusLift hc

theorem abs_lipGradVec_le {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f)
    (x : DGPS.Torus d) (j : Fin d) :
    |lipGradVec f x j| ≤ (Real.toNNReal (L * Real.sqrt d) : ℝ) :=
  SharpLSI.abs_lipGrad_le (lipschitzWith_comp_lift hf) x j

theorem isWeakGrad_lipGradVec {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f) :
    SharpLSI.IsWeakGrad f (fun y k => lipGradVec f y k) :=
  SharpLSI.isWeakGrad_lipGrad (continuous_of_lip hf) (lipschitzWith_comp_lift hf)

theorem coordPartial_moll_lip {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f)
    (n : ℕ) (j : Fin d) (x : DGPS.Torus d) :
    DGPS.coordPartial j (SharpLSI.moll n f) x = SharpLSI.moll n (fun y => lipGradVec f y j) x := by
  unfold DGPS.coordPartial
  rw [SharpLSI.moll_comp_liftT n f] 
  exact SharpLSI.fderiv_mollL_of_isWeakGrad (isWeakGrad_lipGradVec hf) n _ j


theorem moll_nonneg_of_nonneg {h : DGPS.Torus d → ℝ} (hh : ∀ x, 0 ≤ h x) (n : ℕ) (y : DGPS.Torus d) :
    0 ≤ SharpLSI.moll n h y := by
  rw [DGPS.moll_apply_eq]
  exact integral_nonneg fun s => mul_nonneg (SharpLSI.phiSeq_nonneg n s) (hh _)

theorem moll_const (a : ℝ) (n : ℕ) (y : DGPS.Torus d) :
    SharpLSI.moll n (fun _ : DGPS.Torus d => a) y = a := by
  rw [DGPS.moll_apply_eq, integral_mul_const, DGPS.integral_phiSeq, one_mul]

theorem integrable_const_torus (a : ℝ) : Integrable (fun _ : DGPS.Torus d => a) (DGPS.haar d) :=
  integrable_const a

theorem moll_ge {h : DGPS.Torus d → ℝ} (hh : Integrable h (DGPS.haar d)) {a : ℝ}
    (hge : ∀ x, a ≤ h x) (n : ℕ) (y : DGPS.Torus d) : a ≤ SharpLSI.moll n h y := by
  have h1 := moll_nonneg_of_nonneg (h := fun z => h z - a) (fun x => sub_nonneg.mpr (hge x)) n y
  rw [SharpLSI.moll_sub n hh (integrable_const_torus a), moll_const] at h1
  linarith

theorem moll_le {h : DGPS.Torus d → ℝ} (hh : Integrable h (DGPS.haar d)) {b : ℝ}
    (hle : ∀ x, h x ≤ b) (n : ℕ) (y : DGPS.Torus d) : SharpLSI.moll n h y ≤ b := by
  have h1 := moll_nonneg_of_nonneg (h := fun z => b - h z) (fun x => sub_nonneg.mpr (hle x)) n y
  rw [SharpLSI.moll_sub n (integrable_const_torus b) hh, moll_const] at h1
  linarith


theorem isSmoothPeriodic_comp {F : DGPS.Torus d → ℝ} (hF : DGPS.IsSmoothPeriodic F) {φ : ℝ → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ (Ioi 0)) (hpos : ∀ x, 0 < F x) :
    DGPS.IsSmoothPeriodic (fun y => φ (F y)) :=
  hφ.comp_contDiff hF (fun _ => hpos _)

theorem coordPartial_comp {F : DGPS.Torus d → ℝ} (hF : DGPS.IsSmoothPeriodic F) {φ D : ℝ → ℝ}
    (hφD : ∀ t, 0 < t → HasDerivAt φ (D t) t) (hpos : ∀ x, 0 < F x) (j : Fin d)
    (x : DGPS.Torus d) :
    DGPS.coordPartial j (fun y => φ (F y)) x = D (F x) * DGPS.coordPartial j F x := by
  unfold DGPS.coordPartial
  have hFd : HasFDerivAt (F ∘ DGPS.torusLift)
      (fderiv ℝ (F ∘ DGPS.torusLift) (SharpLSI.secT x)) (SharpLSI.secT x) :=
    ((hF.differentiable (by simp)) _).hasFDerivAt
  have hh : HasDerivAt φ (D (F x)) ((F ∘ DGPS.torusLift) (SharpLSI.secT x)) := by
    have := hφD (F x) (hpos x)
    simpa [DGPS.torusLift, SharpLSI.liftT_secT] using this
  have := (hh.comp_hasFDerivAt (SharpLSI.secT x) hFd).fderiv
  have e : ((fun y => φ (F y)) ∘ DGPS.torusLift) = φ ∘ (F ∘ DGPS.torusLift) := rfl
  rw [e, this]
  simp


theorem norm_le_of_coord_le {v : DGPS.Tangent d} {C : ℝ} (hC : 0 ≤ C) (h : ∀ j, |v j| ≤ C) :
    ‖v‖ ≤ Real.sqrt d * C := by
  rw [EuclideanSpace.norm_eq]
  rw [show Real.sqrt d * C = Real.sqrt (d * C ^ 2) by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hC]]
  apply Real.sqrt_le_sqrt
  calc ∑ j, ‖v j‖ ^ 2 ≤ ∑ _j : Fin d, C ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h j) 2
    _ = d * C ^ 2 := by simp

theorem measurable_lipGradVec {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f) :
    Measurable (lipGradVec f) := by
  have : Measurable fun x => (fun j => lipGradVec f x j) :=
    measurable_pi_iff.mpr fun j => SharpLSI.measurable_lipGrad (continuous_of_lip hf) j
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp this


theorem enorm_real_le {a b M : ℝ} (hM : 0 ≤ M) (h : |a| ≤ M * |b|) :
    ‖a‖ₑ ≤ ENNReal.ofReal M * ‖b‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hM]
  exact ENNReal.ofReal_le_ofReal h

/-- Chain rule for a Lipschitz function bounded below by `c > 0` and a function `φ` that is smooth
on `(0, ∞)` with bounded, Lipschitz derivative on `[c, ∞)`: a `W^{1,∞}` gradient. -/
theorem lip_chain {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f) {c : ℝ}
    (hfc : ∀ x, c ≤ f x) (hc : 0 < c) {φ D : ℝ → ℝ} {M K : ℝ}
    (hφs : ContDiffOn ℝ ∞ φ (Ioi 0)) (hφD : ∀ t, 0 < t → HasDerivAt φ (D t) t)
    (hφL : ∀ a b, c ≤ a → c ≤ b → |φ a - φ b| ≤ M * |a - b|)
    (hDM : ∀ t, c ≤ t → |D t| ≤ M)
    (hDL : ∀ a b, c ≤ a → c ≤ b → |D a - D b| ≤ K * |a - b|) :
    DGPS.IsWeakGradientLp ∞ (fun x => φ (f x)) (fun x => D (f x) • lipGradVec f x) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hDM c le_rfl)
  have hcont := continuous_of_lip hf
  have hf2 : MemLp f 2 (DGPS.haar d) := DGPS.memLp_two_of_continuous hcont
  have hfi : Integrable f (DGPS.haar d) := hf2.integrable one_le_two
  set C : ℝ := (Real.toNNReal (L * Real.sqrt d) : ℝ) with hCdef
  have hC0 : 0 ≤ C := NNReal.coe_nonneg _
  have hgb := abs_lipGradVec_le hf
  have hgm : ∀ j, Measurable fun y => lipGradVec f y j := fun j =>
    SharpLSI.measurable_lipGrad hcont j
  have hgL2 : ∀ j, MemLp (fun y => lipGradVec f y j) 2 (DGPS.haar d) := fun j =>
    (memLp_top_of_bound (hgm j).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x j)).mono_exponent le_top
  -- continuity of `φ ∘ f` and `D ∘ f`
  have hφc : Continuous fun x => φ (f x) :=
    hφs.continuousOn.comp_continuous hcont (fun x => lt_of_lt_of_le hc (hfc x))
  have hDon : ContinuousOn D (Ici c) := by
    have : LipschitzOnWith (Real.toNNReal K) D (Ici c) := by
      refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
      rw [Real.dist_eq, Real.dist_eq]
      calc |D a - D b| ≤ K * |a - b| := hDL a b ha hb
        _ ≤ (Real.toNNReal K : ℝ) * |a - b| :=
          mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (abs_nonneg _)
    exact this.continuousOn
  have hDc : Continuous fun x => D (f x) := hDon.comp_continuous hcont hfc
  -- the gradient vector
  have hnorm : ∀ x, ‖D (f x) • lipGradVec f x‖ ≤ M * (Real.sqrt d * C) := fun x => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hDM _ (hfc x)) (norm_le_of_coord_le hC0 (hgb x)) (norm_nonneg _) hM
  have hGm : Measurable fun x => D (f x) • lipGradVec f x :=
    hDc.measurable.smul (measurable_lipGradVec hf)
  have hG2 : MemLp (fun x => D (f x) • lipGradVec f x) ∞ (DGPS.haar d) :=
    memLp_top_of_bound hGm.aestronglyMeasurable _ (Eventually.of_forall fun x => hnorm x)
  have hu2 : MemLp (fun x => φ (f x)) ∞ (DGPS.haar d) := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hφc.continuousOn
    exact memLp_top_of_bound hφc.aestronglyMeasurable B
      (Eventually.of_forall fun x => hB x (mem_univ x))
  -- smooth approximants
  have hFs : ∀ n, DGPS.IsSmoothPeriodic (SharpLSI.moll n f) := fun n =>
    DGPS.isSmoothPeriodic_moll n hfi
  have hFpos : ∀ n x, 0 < SharpLSI.moll n f x := fun n x =>
    lt_of_lt_of_le hc (moll_ge hfi hfc n x)
  have hFc : ∀ n x, c ≤ SharpLSI.moll n f x := fun n x => moll_ge hfi hfc n x
  have hUs : ∀ n, DGPS.IsSmoothPeriodic (fun y => φ (SharpLSI.moll n f y)) := fun n =>
    isSmoothPeriodic_comp (hFs n) hφs (hFpos n)
  have hgi : ∀ j, Integrable (fun y => lipGradVec f y j) (DGPS.haar d) := fun j =>
    (hgL2 j).integrable one_le_two
  have hT0 := DGPS.tendsto_lintegral_moll_sub hf2
  have hweak : DGPS.IsWeakGradient (fun x => φ (f x)) (fun x => D (f x) • lipGradVec f x) := by
    refine DGPS.IsWeakGradient.of_tendsto_L1 (U := fun n y => φ (SharpLSI.moll n f y))
      (G := fun n => DGPS.smoothGrad (fun y => φ (SharpLSI.moll n f y)))
      (hu2.mono_exponent le_top) (hG2.mono_exponent le_top) (fun n => (hUs n).isWeakGradient) ?_ ?_
    · have a2 := ENNReal.Tendsto.const_mul hT0 (Or.inr (ENNReal.ofReal_ne_top (r := M)))
      rw [mul_zero] at a2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds a2
        (fun _ => zero_le) (fun n => ?_)
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_mono fun y => enorm_real_le hM (hφL _ _ (hFc n y) (hfc y))
    · intro j
      have hT1 := DGPS.tendsto_lintegral_moll_sub (hgL2 j)
      have hK : 0 ≤ K := by
        have := hDL c (c + 1) le_rfl (by linarith)
        have h2 : |c - (c + 1)| = 1 := by rw [show c - (c + 1) = -1 by ring]; simp
        rw [h2, mul_one] at this
        exact (abs_nonneg _).trans this
      have hKC : 0 ≤ K * C := mul_nonneg hK hC0
      have hsum : Tendsto (fun n => ENNReal.ofReal M * ∫⁻ y, ‖SharpLSI.moll n (fun x => lipGradVec f x j) y - lipGradVec f y j‖ₑ ∂DGPS.haar d
          + ENNReal.ofReal (K * C) * ∫⁻ y, ‖SharpLSI.moll n f y - f y‖ₑ ∂DGPS.haar d) atTop (𝓝 0) := by
        have a1 := ENNReal.Tendsto.const_mul hT1 (Or.inr (ENNReal.ofReal_ne_top (r := M)))
        have a2 := ENNReal.Tendsto.const_mul hT0 (Or.inr (ENNReal.ofReal_ne_top (r := K * C)))
        simpa using a1.add a2
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun _ => zero_le) (fun n => ?_)
      have hmeas1 : Measurable fun y => ‖SharpLSI.moll n (fun x => lipGradVec f x j) y - lipGradVec f y j‖ₑ :=
        ((SharpLSI.measurable_moll n (hgi j)).sub (hgm j)).enorm
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left (hmeas1.const_mul _)]
      refine lintegral_mono fun y => ?_
      simp only [DGPS.smoothGrad_apply, PiLp.smul_apply, smul_eq_mul]
      rw [coordPartial_comp (hFs n) hφD (hFpos n), coordPartial_moll_lip hf]
      have hab := hDL _ _ (hFc n y) (hfc y)
      have hDb := hDM _ (hFc n y)
      have hgj : |lipGradVec f y j| ≤ C := hgb y j
      set m := SharpLSI.moll n (fun x => lipGradVec f x j) y
      set gy := lipGradVec f y j
      set Fy := SharpLSI.moll n f y
      have hreal : |D Fy * m - D (f y) * gy| ≤ M * |m - gy| + (K * C) * |Fy - f y| := by
        have e : D Fy * m - D (f y) * gy = D Fy * (m - gy) + (D Fy - D (f y)) * gy := by ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hDb (abs_nonneg _)
        · rw [abs_mul]
          calc |D Fy - D (f y)| * |gy| ≤ (K * |Fy - f y|) * C :=
                mul_le_mul hab hgj (abs_nonneg _) (mul_nonneg hK (abs_nonneg _))
            _ = K * C * |Fy - f y| := by ring
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      calc ENNReal.ofReal |D Fy * m - D (f y) * gy|
          ≤ ENNReal.ofReal (M * |m - gy| + (K * C) * |Fy - f y|) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal M * ENNReal.ofReal |m - gy| + ENNReal.ofReal (K * C) * ENNReal.ofReal |Fy - f y| := by
          rw [ENNReal.ofReal_add (mul_nonneg hM (abs_nonneg _)) (mul_nonneg hKC (abs_nonneg _)),
            ENNReal.ofReal_mul hM, ENNReal.ofReal_mul hKC]
  exact ⟨hu2, hG2, hweak.ibp⟩

theorem lip_of_deriv_bound {φ φ' : ℝ → ℝ} {c M : ℝ}
    (h : ∀ t, c ≤ t → HasDerivAt φ (φ' t) t) (hb : ∀ t, c ≤ t → |φ' t| ≤ M) :
    ∀ a b, c ≤ a → c ≤ b → |φ a - φ b| ≤ M * |a - b| := by
  intro a b ha hb'
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ) (f' := φ') (C := M)
    (s := Ici c) (x := b) (y := a) (fun x hx => (h x hx).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hb x hx) (convex_Ici c) hb' ha
  simpa [Real.norm_eq_abs] using this

theorem isWeakGradientLp_rpow {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f)
    {c : ℝ} (hfc : ∀ x, c ≤ f x) (hc : 0 < c) {r : ℝ} (hr : r ≤ 1) :
    DGPS.IsWeakGradientLp ∞ (fun x => f x ^ r)
      (fun x => (r * f x ^ (r - 1)) • lipGradVec f x) := by
  have hpos : ∀ t, c ≤ t → 0 < t := fun t ht => lt_of_lt_of_le hc ht
  have hD1 : ∀ t, 0 < t → HasDerivAt (fun t : ℝ => t ^ r) (r * t ^ (r - 1)) t := fun t ht =>
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hD2 : ∀ t, 0 < t → HasDerivAt (fun t : ℝ => r * t ^ (r - 1))
      (r * ((r - 1) * t ^ (r - 1 - 1))) t := fun t ht =>
    (Real.hasDerivAt_rpow_const (p := r - 1) (Or.inl ht.ne')).const_mul r
  have hb1 : ∀ t, c ≤ t → |r * t ^ (r - 1)| ≤ |r| * c ^ (r - 1) := by
    intro t ht
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hpos t ht) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht (by linarith)) (abs_nonneg _)
  have hb2 : ∀ t, c ≤ t → |r * ((r - 1) * t ^ (r - 1 - 1))| ≤ |r * (r - 1)| * c ^ (r - 1 - 1) := by
    intro t ht
    rw [← mul_assoc, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hpos t ht) _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc ht (by linarith)) (abs_nonneg _)
  exact lip_chain hf hfc hc (φ := fun t => t ^ r) (D := fun t => r * t ^ (r - 1))
    (M := |r| * c ^ (r - 1)) (K := |r * (r - 1)| * c ^ (r - 1 - 1))
    (fun t ht => (Real.contDiffAt_rpow_const_of_ne (ne_of_gt ht)).contDiffWithinAt) hD1
    (lip_of_deriv_bound (fun t ht => hD1 t (hpos t ht)) hb1) hb1
    (lip_of_deriv_bound (fun t ht => hD2 t (hpos t ht)) hb2)

theorem isWeakGradientLp_log {L : ℝ} {f : DGPS.Torus d → ℝ} (hf : DGPS.TorusLipschitzWith L f)
    {c : ℝ} (hfc : ∀ x, c ≤ f x) (hc : 0 < c) :
    DGPS.IsWeakGradientLp ∞ (fun x => Real.log (f x))
      (fun x => (f x)⁻¹ • lipGradVec f x) := by
  have hpos : ∀ t, c ≤ t → 0 < t := fun t ht => lt_of_lt_of_le hc ht
  have hD1 : ∀ t : ℝ, 0 < t → HasDerivAt Real.log t⁻¹ t := fun t ht => Real.hasDerivAt_log ht.ne'
  have hD2 : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => t⁻¹) (-(t ^ 2)⁻¹) t := fun t ht =>
    hasDerivAt_inv ht.ne'
  have hb1 : ∀ t, c ≤ t → |t⁻¹| ≤ c⁻¹ := by
    intro t ht
    rw [abs_of_pos (inv_pos.mpr (hpos t ht))]
    exact inv_anti₀ hc ht
  have hb2 : ∀ t, c ≤ t → |-(t ^ 2)⁻¹| ≤ (c ^ 2)⁻¹ := by
    intro t ht
    rw [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos (hpos t ht) 2))]
    exact inv_anti₀ (pow_pos hc 2) (pow_le_pow_left₀ hc.le ht 2)
  exact lip_chain hf hfc hc (φ := Real.log) (D := fun t => t⁻¹) (M := c⁻¹) (K := (c ^ 2)⁻¹)
    (Real.contDiffOn_log.mono fun t ht => ne_of_gt ht) hD1
    (lip_of_deriv_bound (fun t ht => hD1 t (hpos t ht)) hb1) hb1
    (lip_of_deriv_bound (fun t ht => hD2 t (hpos t ht)) hb2)

end DGPS.RelativeFisher

namespace DGPS

variable {d : ℕ}

/-- A bounded positive reference probability `P = w m` (INTERFACES/definitions.md §5): a measurable
density `w` with constants `0 < lower ≤ w ≤ upper < ∞` Haar-a.e. and mass one. No regularity of `w`
is required. -/
structure BoundedPositiveReference (d : ℕ) where
  density : Torus d → ℝ
  measurable_density : Measurable density
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_le : ∀ᵐ x ∂haar d, lower ≤ density x
  le_upper : ∀ᵐ x ∂haar d, density x ≤ upper
  mass_one : ∫ x, density x ∂haar d = 1

end DGPS

namespace DGPS.BoundedPositiveReference

variable {d : ℕ}

variable (P : BoundedPositiveReference d)

/-- The reference probability measure `P = w m`. -/
noncomputable def measure : Measure (Torus d) :=
  (haar d).withDensity fun x => ENNReal.ofReal (P.density x)

noncomputable instance : CoeOut (BoundedPositiveReference d) (Measure (Torus d)) := ⟨measure⟩

/-- The positive-Lipschitz-density hypothesis: the density is bounded below by a positive constant
everywhere and has a (direct, pointwise) Lipschitz representative, namely `P.density` itself. -/
def hasPositiveLipschitzDensity : Prop :=
  ∃ L c : ℝ, 0 < c ∧ (∀ x, c ≤ P.density x) ∧ TorusLipschitzWith L P.density

theorem ae_pos : ∀ᵐ x ∂haar d, 0 < P.density x := by
  filter_upwards [P.lower_le] with x hx using lt_of_lt_of_le P.lower_pos hx

theorem memLp_top_density : MemLp P.density ∞ (haar d) := by
  refine memLp_top_of_bound P.measurable_density.aestronglyMeasurable P.upper ?_
  filter_upwards [P.lower_le, P.le_upper] with x h1 h2
  rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le P.lower_pos h1)]
  exact h2

theorem integrable_density : Integrable P.density (haar d) :=
  P.memLp_top_density.integrable (by simp)

instance isProbabilityMeasure : IsProbabilityMeasure P.measure := by
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal P.integrable_density
      (by filter_upwards [P.ae_pos] with x hx using hx.le),
    P.mass_one, ENNReal.ofReal_one]

theorem measurable_ofReal_density : Measurable fun x => ENNReal.ofReal (P.density x) :=
  P.measurable_density.ennreal_ofReal

theorem measure_le_smul_haar : P.measure ≤ ENNReal.ofReal P.upper • haar d := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [measure, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae P.le_upper] with x hx
  exact ENNReal.ofReal_le_ofReal hx

theorem haar_le_smul_measure : haar d ≤ ENNReal.ofReal P.lower⁻¹ • P.measure := by
  refine Measure.le_iff.2 fun s hs => ?_
  rw [measure, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul _ P.measurable_ofReal_density, ← setLIntegral_one]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae P.lower_le] with x hx
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 P.lower_pos.le)]
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ P.lower_pos]
  linarith

theorem measure_ac_haar : P.measure ≪ haar d := withDensity_absolutelyContinuous _ _

theorem haar_ac_measure : haar d ≪ P.measure :=
  withDensity_absolutelyContinuous' P.measurable_ofReal_density.aemeasurable (by
    filter_upwards [P.ae_pos] with x hx
    exact (ENNReal.ofReal_pos.2 hx).ne')

theorem memLp_measure_iff {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {u : Torus d → E} :
    MemLp u p P.measure ↔ MemLp u p (haar d) :=
  ⟨fun h => h.of_measure_le_smul (by simp) P.haar_le_smul_measure,
    fun h => h.of_measure_le_smul (by simp) P.measure_le_smul_haar⟩

end DGPS.BoundedPositiveReference

namespace DGPS

variable {d : ℕ}

/-- `g` is a weighted weak gradient of `u` for the bounded positive reference `P`: `u ∈ L²(P)`,
`g ∈ L²(P; ℝ^d)` and `∫ u ∂ⱼφ dm = -∫ gⱼ φ dm` for every smooth periodic `φ` (the distributional
gradient). -/
structure IsWeightedWeakGradient (P : BoundedPositiveReference d) (u : Torus d → ℝ)
    (g : Torus d → Tangent d) : Prop where
  memLp : MemLp u 2 P.measure
  memLp_grad : MemLp g 2 P.measure
  ibp : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ j : Fin d,
    ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, g x j * φ x ∂haar d

/-- The full weighted weak `H¹(P)` domain of a bounded positive reference. -/
def WeightedH1 (P : BoundedPositiveReference d) : Set (Torus d → ℝ) :=
  {u | ∃ g, IsWeightedWeakGradient P u g}

/-- The weighted weak gradient of `u ∈ WeightedH1 P` (requires the membership proof). -/
noncomputable def weightedGradient (P : BoundedPositiveReference d) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) : Torus d → Tangent d :=
  hu.choose

theorem isWeightedWeakGradient_weightedGradient (P : BoundedPositiveReference d)
    {u : Torus d → ℝ} (hu : u ∈ WeightedH1 P) :
    IsWeightedWeakGradient P u (weightedGradient P u hu) :=
  hu.choose_spec

theorem isWeightedWeakGradient_iff (P : BoundedPositiveReference d) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} : IsWeightedWeakGradient P u g ↔ IsWeakGradient u g :=
  ⟨fun h => ⟨P.memLp_measure_iff.1 h.memLp, P.memLp_measure_iff.1 h.memLp_grad, h.ibp⟩,
    fun h => ⟨P.memLp_measure_iff.2 h.memLp, P.memLp_measure_iff.2 h.memLp_grad, h.ibp⟩⟩

/-- Weighted weak `H¹(P)` and Haar `H¹` coincide as sets for a bounded positive reference. -/
theorem mem_weightedH1_iff (P : BoundedPositiveReference d) {u : Torus d → ℝ} :
    u ∈ WeightedH1 P ↔ MemH1 u :=
  ⟨fun ⟨g, hg⟩ => ⟨g, (isWeightedWeakGradient_iff P).1 hg⟩,
    fun ⟨g, hg⟩ => ⟨g, (isWeightedWeakGradient_iff P).2 hg⟩⟩

theorem weightedGradient_ae_eq (P : BoundedPositiveReference d) {u : Torus d → ℝ}
    (hu : u ∈ WeightedH1 P) {g : Torus d → Tangent d} (hg : IsWeakGradient u g) :
    weightedGradient P u hu =ᵐ[haar d] g :=
  ((isWeightedWeakGradient_iff P).1 (isWeightedWeakGradient_weightedGradient P hu)).ae_eq hg

/-- The relative square root `√(dν/dP)`. -/
noncomputable def relativeSqrt (ν : Measure (Torus d)) (P : BoundedPositiveReference d) :
    Torus d → ℝ :=
  fun x => Real.sqrt (ν.rnDeriv P.measure x).toReal

open Classical in
/-- The ordinary relative Fisher information `4 ∫ |∇ √(dν/dP)|² dP` when `ν ≪ P` and the relative
square root lies in the weighted form domain, and `+∞` otherwise (DEF022). -/
noncomputable def ordinaryRelativeFisher (ν : Measure (Torus d)) (P : BoundedPositiveReference d) :
    ℝ≥0∞ :=
  if h : ν ≪ P.measure ∧ relativeSqrt ν P ∈ WeightedH1 P then
    4 * ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) h.2 x‖ₑ ^ 2 ∂P.measure
  else ⊤

theorem ordinaryRelativeFisher_of_not_absolutelyContinuous {ν : Measure (Torus d)}
    {P : BoundedPositiveReference d} (h : ¬ ν ≪ P.measure) : ordinaryRelativeFisher ν P = ⊤ := by
  simp [ordinaryRelativeFisher, h]

theorem ordinaryRelativeFisher_of_not_mem {ν : Measure (Torus d)} {P : BoundedPositiveReference d}
    (h : relativeSqrt ν P ∉ WeightedH1 P) : ordinaryRelativeFisher ν P = ⊤ := by
  simp [ordinaryRelativeFisher, h]

/-- Evaluation of `ordinaryRelativeFisher` through any weak gradient of the relative square root. -/
theorem ordinaryRelativeFisher_eq {ν : Measure (Torus d)} {P : BoundedPositiveReference d}
    (hν : ν ≪ P.measure) {g : Torus d → Tangent d} (hg : IsWeakGradient (relativeSqrt ν P) g) :
    ordinaryRelativeFisher ν P = 4 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure := by
  have hmem : relativeSqrt ν P ∈ WeightedH1 P := (mem_weightedH1_iff P).2 ⟨g, hg⟩
  rw [ordinaryRelativeFisher, dite_eq_left_of_eq_true (eq_true ⟨hν, hmem⟩)]
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hmem hg)] with x hx
  rw [hx]

end DGPS

namespace DGPS.RelativeFisher

variable {d : ℕ}

theorem isWeakGradient_of_top {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradientLp ∞ u g) : IsWeakGradient u g :=
  ⟨h.memLp.mono_exponent le_top, h.memLp_grad.mono_exponent le_top, h.ibp⟩

theorem mul_rpow_isWeakGradient {P : BoundedPositiveReference d} (hLip : P.hasPositiveLipschitzDensity)
    {r : ℝ} (hr : r ≤ 1) {u : Torus d → ℝ} {g : Torus d → Tangent d} (hu : IsWeakGradient u g) :
    IsWeakGradient (fun x => u x * P.density x ^ r)
      (fun x => P.density x ^ r • g x +
        u x • ((r * P.density x ^ (r - 1)) • lipGradVec P.density x)) := by
  obtain ⟨L, c, hc, hcP, hL⟩ := hLip
  exact hu.mul_W1infty (isWeakGradientLp_rpow hL hcP hc hr)

theorem isWeakGradient_log {P : BoundedPositiveReference d} (hLip : P.hasPositiveLipschitzDensity) :
    IsWeakGradient (fun x => Real.log (P.density x))
      (fun x => (P.density x)⁻¹ • lipGradVec P.density x) := by
  obtain ⟨L, c, hc, hcP, hL⟩ := hLip
  exact isWeakGradient_of_top (isWeakGradientLp_log hL hcP hc)

theorem density_pos {P : BoundedPositiveReference d} (hLip : P.hasPositiveLipschitzDensity)
    (x : Torus d) : 0 < P.density x := by
  obtain ⟨L, c, hc, hcP, hL⟩ := hLip
  exact lt_of_lt_of_le hc (hcP x)

/-- Multiplication/division by `√p` identifies the weighted and Haar `H¹` domains. -/
theorem memWeightedH1_iff_memH1_mul_sqrt {P : BoundedPositiveReference d}
    (hLip : P.hasPositiveLipschitzDensity) {s : Torus d → ℝ} :
    s ∈ WeightedH1 P ↔ MemH1 (fun x => P.density x ^ (1 / 2 : ℝ) * s x) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (mem_weightedH1_iff P).1 h
    have := mul_rpow_isWeakGradient hLip (r := 1 / 2) (by norm_num) hg
    exact ⟨_, this.congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      (Filter.EventuallyEq.refl _ _)⟩
  · rintro ⟨g, hg⟩
    have := mul_rpow_isWeakGradient hLip (r := -(1 / 2)) (by norm_num) hg
    have key : ∀ x, P.density x ^ (1 / 2 : ℝ) * s x * P.density x ^ (-(1 / 2) : ℝ) = s x := by
      intro x
      rw [mul_right_comm, ← Real.rpow_add (density_pos hLip x)]
      simp
    exact (mem_weightedH1_iff P).2 ⟨_, this.congr_ae (Filter.Eventually.of_forall key)
      (Filter.EventuallyEq.refl _ _)⟩

/-- The relative square root is, Haar-a.e., the absolute square root of `dν/dm` times `p^(-1/2)`. -/
theorem relativeSqrt_ae_eq (P : BoundedPositiveReference d) (ν : Measure (Torus d))
    [IsFiniteMeasure ν] :
    relativeSqrt ν P =ᵐ[haar d]
      fun x => Real.sqrt (ν.rnDeriv (haar d) x).toReal * P.density x ^ (-(1 / 2) : ℝ) := by
  have h := Measure.rnDeriv_withDensity_right ν (haar d)
    (f := fun x => ENNReal.ofReal (P.density x)) P.measurable_ofReal_density.aemeasurable
    (by filter_upwards [P.ae_pos] with x hx; exact (ENNReal.ofReal_pos.2 hx).ne')
    (by filter_upwards with x; exact ENNReal.ofReal_ne_top)
  filter_upwards [h, P.ae_pos] with x hx hp
  have hx' : ν.rnDeriv P.measure x = (ENNReal.ofReal (P.density x))⁻¹ * ν.rnDeriv (haar d) x := hx
  simp only [relativeSqrt, hx', ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp.le]
  rw [Real.sqrt_mul (inv_nonneg.2 hp.le), mul_comm, Real.sqrt_inv, Real.sqrt_eq_rpow (P.density x),
    Real.rpow_neg hp.le]

/-- The precise equivalence of relative and absolute square-root `H¹` domains under a positive
Lipschitz reference density: `√(dν/dP) ∈ H¹(P)` iff `√(dν/dm) ∈ H¹(m)`. -/
theorem relativeSqrt_mem_weightedH1_iff {P : BoundedPositiveReference d}
    (hLip : P.hasPositiveLipschitzDensity) (ν : Measure (Torus d)) [IsFiniteMeasure ν] :
    relativeSqrt ν P ∈ WeightedH1 P ↔
      (fun x => Real.sqrt (ν.rnDeriv (haar d) x).toReal) ∈ H1Haar d := by
  have hae := relativeSqrt_ae_eq P ν
  have key : ∀ x, P.density x ^ (1 / 2 : ℝ) *
      (Real.sqrt (ν.rnDeriv (haar d) x).toReal * P.density x ^ (-(1 / 2) : ℝ)) =
      Real.sqrt (ν.rnDeriv (haar d) x).toReal := by
    intro x
    rw [mul_left_comm, ← Real.rpow_add (density_pos hLip x)]
    simp
  have h1 : relativeSqrt ν P ∈ WeightedH1 P ↔
      (fun x => Real.sqrt (ν.rnDeriv (haar d) x).toReal *
        P.density x ^ (-(1 / 2) : ℝ)) ∈ WeightedH1 P := by
    rw [mem_weightedH1_iff, mem_weightedH1_iff]
    exact ⟨fun h => mem_H1Haar_congr_ae h hae, fun h => mem_H1Haar_congr_ae h hae.symm⟩
  rw [h1, memWeightedH1_iff_memH1_mul_sqrt hLip]
  simp only [key]
  rfl

end DGPS.RelativeFisher

namespace DGPS.RelativeFisher

variable {d : ℕ}

theorem enorm_aux {E : Type*} [NormedAddCommGroup E] (G V : E) (p : ℝ) (hp : 0 ≤ p)
    (h : 4 * p * ‖G‖ ^ 2 = ‖V‖ ^ 2) :
    4 * (ENNReal.ofReal p * ‖G‖ₑ ^ 2) = ‖V‖ₑ ^ 2 := by
  rw [← ofReal_norm G, ← ofReal_norm V, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hp,
    show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  linarith

theorem gradient_identity {p : ℝ} (hp : 0 < p) (u : ℝ) (g gp : Tangent d) :
    4 * p * ‖p ^ (-(1 / 2) : ℝ) • g + u • (((-(1 / 2)) * p ^ (-(1 / 2) - 1 : ℝ)) • gp)‖ ^ 2 =
      ‖(2 : ℝ) • g - u • (p⁻¹ • gp)‖ ^ 2 := by
  have e : p ^ (-(1 / 2) - 1 : ℝ) = p ^ (-(1 / 2) : ℝ) * p⁻¹ := by
    rw [Real.rpow_sub_one hp.ne']; ring
  have ha : 0 < p ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hp _
  have haa : p ^ (-(1 / 2) : ℝ) * p ^ (-(1 / 2) : ℝ) = p⁻¹ := by
    rw [← Real.rpow_add hp]; norm_num [Real.rpow_neg_one]
  have hGV : p ^ (-(1 / 2) : ℝ) • g + u • (((-(1 / 2)) * p ^ (-(1 / 2) - 1 : ℝ)) • gp) =
      ((1 / 2) * p ^ (-(1 / 2) : ℝ)) • ((2 : ℝ) • g - u • (p⁻¹ • gp)) := by
    rw [e]
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  rw [hGV, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity), mul_pow,
    show (p ^ (-(1 / 2) : ℝ)) ^ 2 = p⁻¹ by rw [sq]; exact haa]
  field_simp
  ring

end DGPS.RelativeFisher

namespace DGPS

variable {d : ℕ}

theorem BoundedPositiveReference.memH1_log (P : BoundedPositiveReference d)
    (hLip : P.hasPositiveLipschitzDensity) : MemH1 (fun x => Real.log (P.density x)) :=
  ⟨_, RelativeFisher.isWeakGradient_log hLip⟩

end DGPS

namespace DGPS

variable {d : ℕ}

/-- DEF022 positive-reference identity: for a positive Lipschitz reference density `p` and an
absolute-admissible `ρ = u²`, the ordinary relative Fisher information of `ρ m` against `P = p m` is
`∫ |2 ∇u - u ∇ log p|² dm`. -/
theorem positiveReference_absolute_identity (P : BoundedPositiveReference d)
    (hLip : P.hasPositiveLipschitzDensity) (ρ : AbsoluteDensity d) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus d)) P =
      ∫⁻ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x
        - ρ.sqrt x • weakGradient (fun x => Real.log (P.density x)) (P.memH1_log hLip) x‖ₑ ^ 2
        ∂haar d := by
  set ν : Measure (Torus d) := (densityMeasure ρ : Measure (Torus d)) with hν
  have hνac : ν ≪ P.measure :=
    (withDensity_absolutelyContinuous _ _).trans P.haar_ac_measure
  have habs : (fun x => Real.sqrt (ν.rnDeriv (haar d) x).toReal) =ᵐ[haar d] ρ.sqrt := by
    have h := Measure.rnDeriv_withDensity₀ (haar d)
      (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
      (by exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    filter_upwards [h, ρ.sqrt_nonneg] with x hx hx0
    rw [hν, densityMeasure_coe, hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq hx0]
  have hrel : relativeSqrt ν P =ᵐ[haar d]
      fun x => ρ.sqrt x * P.density x ^ (-(1 / 2) : ℝ) := by
    filter_upwards [RelativeFisher.relativeSqrt_ae_eq P ν, habs] with x h1 h2
    rw [h1, h2]
  have hG := RelativeFisher.mul_rpow_isWeakGradient hLip (r := (-(1 / 2) : ℝ)) (by norm_num)
    (isWeakGradient_weakGradient ρ.sqrt_mem)
  have hws := hG.congr_ae hrel.symm (Filter.EventuallyEq.refl _ _)
  rw [ordinaryRelativeFisher_eq hνac hws]
  have hlog := (isWeakGradient_weakGradient (P.memH1_log hLip)).ae_eq
    (RelativeFisher.isWeakGradient_log hLip)
  have hmeas : AEMeasurable (fun x => ‖(P.density x ^ (-(1 / 2) : ℝ)) •
      weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x •
        (((-(1 / 2) : ℝ) * P.density x ^ (-(1 / 2) - 1 : ℝ)) •
          RelativeFisher.lipGradVec P.density x)‖ₑ ^ 2) (haar d) := by
    have := hG.memLp_grad.aestronglyMeasurable.aemeasurable.enorm.pow_const 2
    exact this
  rw [show P.measure = (haar d).withDensity fun x => ENNReal.ofReal (P.density x) from rfl,
    lintegral_withDensity_eq_lintegral_mul₀ P.measurable_ofReal_density.aemeasurable hmeas,
    ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr_ae ?_
  filter_upwards [hlog, P.ae_pos] with x hx hp
  simp only [Pi.mul_apply]
  rw [hx]
  exact RelativeFisher.enorm_aux _ _ _ hp.le
    (RelativeFisher.gradient_identity hp _ _ _)

end DGPS
