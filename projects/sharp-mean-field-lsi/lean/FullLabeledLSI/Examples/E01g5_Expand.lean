import FullLabeledLSI.Examples.E01g1_Basic
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Paper.GroundState

/-!
# Lane D, Task C (E01g5): the dissipation of a density in expanded form

The key input is the integration by parts `2 ∫ f f' b = - ∫ f² b'` for `f ∈ H¹(𝕋)` and smooth `b`
(`ibp_sq_smooth`), proved by testing the weak gradient of `f` against the smooth periodic function
`(moll n f) · b` (`integral_mul_Dk_eq`) and passing to the limit using `L²` convergence of the
mollifications (`exists_subseq_moll_ae`, `L2Tendsto_moll`).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem lintegral_sq_ne_top_of_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
  have := h.integrable_sq.lintegral_lt_top
  simp_rw [ofReal_sq_eq_enorm_sq] at this
  exact this.ne

theorem tendsto_integral_sq_of_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {D : ℕ → α → ℝ} (hD : ∀ n, MemLp (D n) 2 μ)
    (h : Tendsto (fun n => ∫⁻ x, ‖D n x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (D n x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have e : ∀ n, ∫ x, (D n x) ^ 2 ∂μ = (∫⁻ x, ‖D n x‖ₑ ^ 2 ∂μ).toReal := fun n => by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      ((hD n).integrable_sq.aestronglyMeasurable)]
    simp_rw [ofReal_sq_eq_enorm_sq]
  simp_rw [e]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  exact this

/-- Pairing against a fixed `L²` function is continuous for `L²` convergence. -/
theorem tendsto_integral_mul_of_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A G : α → ℝ} {F : ℕ → α → ℝ} (hA : MemLp A 2 μ) (hG : MemLp G 2 μ)
    (hF : ∀ n, MemLp (F n) 2 μ)
    (h : Tendsto (fun n => ∫⁻ x, ‖F n x - G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, A x * F n x ∂μ) atTop (𝓝 (∫ x, A x * G x ∂μ)) := by
  have hD : ∀ n, MemLp (fun x => F n x - G x) 2 μ := fun n => (hF n).sub hG
  have hI := tendsto_integral_sq_of_lintegral (D := fun n x => F n x - G x) hD h
  set S := ∫ x, A x ^ 2 ∂μ with hS
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  set lam := ε / (S + 1) with hlam
  have hlam0 : 0 < lam := div_pos hε (by linarith)
  have hev := (Metric.tendsto_atTop.1 hI) (ε * lam) (mul_pos hε hlam0)
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  rw [Real.dist_eq, sub_zero] at hn'
  have hAF : Integrable (fun x => A x * F n x) μ := hA.integrable_mul (hF n)
  have hAG : Integrable (fun x => A x * G x) μ := hA.integrable_mul hG
  have hAD : Integrable (fun x => A x * (F n x - G x)) μ := hA.integrable_mul (hD n)
  have e1 : ∫ x, A x * F n x ∂μ - ∫ x, A x * G x ∂μ = ∫ x, A x * (F n x - G x) ∂μ := by
    rw [← integral_sub hAF hAG]; congr 1; funext x; ring
  rw [Real.dist_eq, e1]
  have hpt : ∀ x, |A x * (F n x - G x)| ≤ lam / 2 * A x ^ 2 + (1 / (2 * lam)) * (F n x - G x) ^ 2 := by
    intro x
    rw [abs_le]
    have key : 0 ≤ (lam * A x - (F n x - G x)) ^ 2 / (2 * lam) := by positivity
    have key2 : 0 ≤ (lam * A x + (F n x - G x)) ^ 2 / (2 * lam) := by positivity
    have e2 : lam / 2 * A x ^ 2 + (1 / (2 * lam)) * (F n x - G x) ^ 2 - A x * (F n x - G x)
        = (lam * A x - (F n x - G x)) ^ 2 / (2 * lam) := by field_simp; ring
    have e3 : lam / 2 * A x ^ 2 + (1 / (2 * lam)) * (F n x - G x) ^ 2 + A x * (F n x - G x)
        = (lam * A x + (F n x - G x)) ^ 2 / (2 * lam) := by field_simp; ring
    constructor <;> linarith
  have hint : Integrable (fun x => lam / 2 * A x ^ 2 + (1 / (2 * lam)) * (F n x - G x) ^ 2) μ :=
    (hA.integrable_sq.const_mul _).add ((hD n).integrable_sq.const_mul _)
  calc |∫ x, A x * (F n x - G x) ∂μ| ≤ ∫ x, |A x * (F n x - G x)| ∂μ := by
        simpa using abs_integral_le_integral_abs (f := fun x => A x * (F n x - G x)) (μ := μ)
    _ ≤ ∫ x, (lam / 2 * A x ^ 2 + (1 / (2 * lam)) * (F n x - G x) ^ 2) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = lam / 2 * S + (1 / (2 * lam)) * ∫ x, (F n x - G x) ^ 2 ∂μ := by
        rw [integral_add (hA.integrable_sq.const_mul _) ((hD n).integrable_sq.const_mul _),
          integral_const_mul, integral_const_mul]
    _ < ε := by
        have h1 : lam / 2 * S < ε / 2 := by
          have : lam * S < ε := by
            rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
          linarith
        have h2 : (1 / (2 * lam)) * ∫ x, (F n x - G x) ^ 2 ∂μ < ε / 2 := by
          have hI0 : ∫ x, (F n x - G x) ^ 2 ∂μ < ε * lam := by
            have := le_abs_self (∫ x, (F n x - G x) ^ 2 ∂μ); linarith
          rw [one_div, inv_mul_lt_iff₀ (by positivity)]; nlinarith
        linarith


theorem fderiv_secT_eq_dT {h : Torus 1 → ℝ} (hh : IsSmoothT h) (y : Torus 1) :
    fderiv ℝ (h ∘ liftT) (secT y) (Pi.single 0 1) = dT h y := by
  have hx' : secT y = fun _ : Fin 1 => secT y 0 := by funext i; fin_cases i; rfl
  rw [hx', fderiv_single_eq_deriv hh]
  have : y = lift1 (secT y 0) := by
    have := liftT_secT y
    rw [liftT_eq_lift1] at this
    exact this.symm
  conv_rhs => rw [this]
  rw [dT_lift1]

theorem memLp_two_of_smooth {h : Torus 1 → ℝ} (hh : IsSmoothT h) : MemLp h 2 (haar 1) := by
  have hc : Continuous h := continuous_of_smooth hh
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable M (Eventually.of_forall fun x => by
    simpa using hM x (Set.mem_univ _))

theorem memLp_two_mul_smooth {f b : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (hb : IsSmoothT b) :
    MemLp (fun x => f x * b x) 2 (haar 1) := by
  have hc : Continuous b := continuous_of_smooth hb
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hc.continuousOn
  have hbm : MemLp b ⊤ (haar 1) :=
    MemLp.of_bound hc.aestronglyMeasurable M (Eventually.of_forall fun x => by
      simpa using hM x (Set.mem_univ _))
  have := hbm.mul hf (r := 2)
  refine this.ae_eq (Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply]; ring

/-- Integration by parts for an `H¹` function against a smooth one:
`2 ∫ f f' b = - ∫ f² b'`. -/
theorem ibp_sq_smooth {f : Torus 1 → ℝ} (hH : MemH1 (haar 1) f) {b : Torus 1 → ℝ}
    (hb : IsSmoothT b) :
    2 * ∫ x, f x * weakGrad f x 0 * b x ∂haar 1 = -∫ x, f x ^ 2 * dT b x ∂haar 1 := by
  have hw : IsWeakGrad f (weakGrad f) := isWeakGrad_weakGrad hH.1
  have hf2 : MemLp f 2 (haar 1) := hH.2.1
  have hg2 : MemLp (fun x => weakGrad f x 0) 2 (haar 1) := memLp_weakGrad_zero hH
  have hfi : Integrable f volume := hf2.integrable one_le_two
  have hgi : ∀ k : Fin 1, Integrable (fun y => weakGrad f y k) volume := fun k => by
    have : k = 0 := Subsingleton.elim _ _
    subst this; exact hg2.integrable one_le_two
  obtain ⟨ns, hns, hae⟩ := exists_subseq_moll_ae hfi hgi
  have hae1 : ∀ᵐ y ∂(volume : Measure (Torus 1)), Tendsto (fun j => moll (ns j) f y) atTop (𝓝 (f y)) := by
    filter_upwards [hae] with y hy using hy.1
  have hae2 : ∀ᵐ y ∂(volume : Measure (Torus 1)),
      Tendsto (fun j => moll (ns j) (fun z => weakGrad f z 0) y) atTop (𝓝 (weakGrad f y 0)) := by
    filter_upwards [hae] with y hy using hy.2 0
  have hL1 := L2Tendsto_moll hfi (lintegral_sq_ne_top_of_memLp hf2) hae1
  have hL2 := L2Tendsto_moll (hgi 0) (lintegral_sq_ne_top_of_memLp hg2) hae2
  have hsm1 : ∀ n, IsSmoothT (moll n f) := fun n => moll_comp_liftT_contDiff n hfi
  have hsm2 : ∀ n, IsSmoothT (moll n (fun z => weakGrad f z 0)) := fun n =>
    moll_comp_liftT_contDiff n (hgi 0)
  have hm1 : ∀ n, MemLp (moll n f) 2 (haar 1) := fun n => memLp_two_of_smooth (hsm1 n)
  have hm2 : ∀ n, MemLp (moll n (fun z => weakGrad f z 0)) 2 (haar 1) := fun n =>
    memLp_two_of_smooth (hsm2 n)
  -- identity for each `n`
  have hid : ∀ n, ∫ x, (f x * b x) * moll n (fun z => weakGrad f z 0) x ∂haar 1 +
      ∫ x, (f x * dT b x) * moll n f x ∂haar 1 =
      - ∫ x, (weakGrad f x 0 * b x) * moll n f x ∂haar 1 := by
    intro n
    have hΘ : ContDiff ℝ ∞ (fun x => mollL n (f ∘ liftT) x * (b ∘ liftT) x) :=
      (contDiff_mollL n (locallyIntegrable_comp_liftT hfi)).mul hb
    have hper : IsPer (fun x => mollL n (f ∘ liftT) x * (b ∘ liftT) x) := fun m x => by
      simp only [mollL_comp_liftT_add, Function.comp_apply, liftT_add_intVec]
    have key := integral_mul_Dk_eq hw hfi hgi hΘ hper 0
    have hΘe : ∀ y, (fun x => mollL n (f ∘ liftT) x * (b ∘ liftT) x) (secT y) =
        moll n f y * b y := fun y => by
      simp only [moll, Function.comp_apply, liftT_secT]
    have hDe : ∀ y, Dk (fun x => mollL n (f ∘ liftT) x * (b ∘ liftT) x) 0 (secT y) =
        moll n (fun z => weakGrad f z 0) y * b y + moll n f y * dT b y := fun y => by
      have hd1 : Differentiable ℝ (mollL n (f ∘ liftT)) :=
        (contDiff_mollL n (locallyIntegrable_comp_liftT hfi)).differentiable (by simp)
      have hd2 : Differentiable ℝ (b ∘ liftT) := hb.differentiable (by simp)
      unfold Dk
      rw [fderiv_fun_mul (hd1 _) (hd2 _)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      rw [fderiv_mollL_of_isWeakGrad hw n (secT y) 0, fderiv_secT_eq_dT hb y]
      simp only [Function.comp_apply, liftT_secT, moll]
      rw [add_comm, mul_comm (b y)]
      rfl
    simp_rw [hΘe, hDe] at key
    have i1 : Integrable (fun x => (f x * b x) * moll n (fun z => weakGrad f z 0) x) (haar 1) :=
      (memLp_two_mul_smooth hf2 hb).integrable_mul (hm2 n)
    have i2 : Integrable (fun x => (f x * dT b x) * moll n f x) (haar 1) :=
      (memLp_two_mul_smooth hf2 (isSmoothT_dT hb)).integrable_mul (hm1 n)
    rw [← integral_add i1 i2]
    have e1 : ∀ x, f x * (moll n (fun z => weakGrad f z 0) x * b x + moll n f x * dT b x) =
        (f x * b x) * moll n (fun z => weakGrad f z 0) x + (f x * dT b x) * moll n f x :=
      fun x => by ring
    simp_rw [e1] at key
    rw [key]
    congr 1
    simp_rw [show ∀ x, weakGrad f x 0 * (moll n f x * b x) = (weakGrad f x 0 * b x) * moll n f x
      from fun x => by ring]
  -- limits
  have t1 := tendsto_integral_mul_of_L2 (memLp_two_mul_smooth hf2 hb) hg2
    (F := fun j => moll (ns j) (fun z => weakGrad f z 0)) (fun j => hm2 (ns j)) hL2
  have t2 := tendsto_integral_mul_of_L2 (memLp_two_mul_smooth hf2 (isSmoothT_dT hb)) hf2
    (F := fun j => moll (ns j) f) (fun j => hm1 (ns j)) hL1
  have t3 := tendsto_integral_mul_of_L2 (memLp_two_mul_smooth hg2 hb) hf2
    (F := fun j => moll (ns j) f) (fun j => hm1 (ns j)) hL1
  have hlim := tendsto_nhds_unique ((t1.add t2).congr fun j => hid (ns j)) t3.neg
  have c1 : ∫ x, (f x * b x) * weakGrad f x 0 ∂haar 1 = ∫ x, f x * weakGrad f x 0 * b x ∂haar 1 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have c2 : ∫ x, (f x * dT b x) * f x ∂haar 1 = ∫ x, f x ^ 2 * dT b x ∂haar 1 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have c3 : ∫ x, (weakGrad f x 0 * b x) * f x ∂haar 1 = ∫ x, f x * weakGrad f x 0 * b x ∂haar 1 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [c1, c2, c3] at hlim
  linarith

/-- (9.3) for a single density: `D(ρ) = I(ρ) + 2∫ρ (C''*ρ) + ∫ρ (C'*ρ)²`
(`IR ρ = 4 ∫ ((√ρ)')²`, `DR C ρ = ∫ (2(√ρ)' - √ρ (C'*ρ))²`). -/
theorem diss_expand {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    DR C ρ = IR ρ + 2 * ∫ x, ρ x * convT (dT (dT C)) ρ x ∂haar 1 +
      ∫ x, ρ x * (convT (dT C) ρ x) ^ 2 ∂haar 1 := by
  have := isProbabilityMeasure_densMeasure' h0 h1
  set f : Torus 1 → ℝ := fun x => Real.sqrt (ρ x) with hf
  have hbs : IsSmoothT (convT (dT C) ρ) := by
    rw [convT_eq_conv h0 h1]; exact isSmoothT_conv (isSmoothT_dT hC.smooth) _
  have hdb : dT (convT (dT C) ρ) = convT (dT (dT C)) ρ := by
    funext x
    have e1 : convT (dT C) ρ = fun x => ∫ y, dT C (x - y) ∂densMeasure ρ := convT_eq_conv h0 h1
    rw [e1, dT_conv (isSmoothT_dT hC.smooth), convT_eq_conv h0 h1]
  have hf2 : MemLp f 2 (haar 1) := hH.2.1
  have hg2 : MemLp (fun x => weakGrad f x 0) 2 (haar 1) := memLp_weakGrad_zero hH
  have hfs : ∀ x, f x ^ 2 = ρ x := fun x => Real.sq_sqrt (h0 x)
  have hfb : MemLp (fun x => f x * convT (dT C) ρ x) 2 (haar 1) := memLp_two_mul_smooth hf2 hbs
  have i1 : Integrable (fun x => weakGrad f x 0 ^ 2) (haar 1) := hg2.integrable_sq
  have i2 : Integrable (fun x => f x * weakGrad f x 0 * convT (dT C) ρ x) (haar 1) := by
    have := hfb.integrable_mul hg2
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  have i3 : Integrable (fun x => ρ x * convT (dT C) ρ x ^ 2) (haar 1) := by
    refine hfb.integrable_sq.congr (Eventually.of_forall fun x => ?_)
    show (f x * convT (dT C) ρ x) ^ 2 = ρ x * convT (dT C) ρ x ^ 2
    rw [mul_pow, hfs]
  have hexp : DR C ρ = 4 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 -
      4 * ∫ x, f x * weakGrad f x 0 * convT (dT C) ρ x ∂haar 1 +
      ∫ x, ρ x * convT (dT C) ρ x ^ 2 ∂haar 1 := by
    unfold DR
    have e : ∀ x, (2 * weakGrad f x 0 - f x * convT (dT C) ρ x) ^ 2 =
        4 * weakGrad f x 0 ^ 2 - 4 * (f x * weakGrad f x 0 * convT (dT C) ρ x) +
          ρ x * convT (dT C) ρ x ^ 2 := fun x => by
      rw [← hfs x]; ring
    show ∫ x, (2 * weakGrad f x 0 - f x * convT (dT C) ρ x) ^ 2 ∂haar 1 = _
    simp_rw [e]
    have j1 : Integrable (fun x => 4 * weakGrad f x 0 ^ 2 -
        4 * (f x * weakGrad f x 0 * convT (dT C) ρ x)) (haar 1) :=
      (i1.const_mul 4).sub (i2.const_mul 4)
    rw [integral_add j1 i3,
      integral_sub (i1.const_mul 4) (i2.const_mul 4), integral_const_mul, integral_const_mul]
  have hibp := ibp_sq_smooth hH hbs
  rw [hdb] at hibp
  have e2 : ∫ x, f x ^ 2 * convT (dT (dT C)) ρ x ∂haar 1 =
      ∫ x, ρ x * convT (dT (dT C)) ρ x ∂haar 1 := by
    congr 1; funext x; rw [hfs]
  rw [e2] at hibp
  rw [hexp]
  unfold IR
  linarith

end SharpLSI.FL.Ex.LaneD
