import FullLabeledLSI.Paper.Prop23Defs
import SharpSymmetricLSI.Paper.CenteredEntropy
import SharpSymmetricLSI.Paper.GroundT8

/-!
# Proposition 2.3, WP-B and WP-C: the exact ground-state identities

* `energy_ground_identity` (WP-B): `ℰ_N(f) = ∫ ∑ᵢₖ (∇Ψ + ½ Ψ ∇U_N)² dQ_N`;
* `entropy_ground_identity` (WP-C): for bounded `f`,
  `Ent_{P_N}(f²) = Ent_{Q_N}(Ψ²) + ∫ Ψ² U_N dQ_N + log K_N ∫ Ψ² dQ_N`.
-/

open MeasureTheory Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section WPB
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N)

include hyp hμ hN in
/-- **(energy-ground)**. -/
theorem energy_ground_identity {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) :
    energy V W N f = ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k,
      (weakGradC (psiG W (μ : Measure (Torus d)) N f) X i k + (1 / 2) *
        psiG W (μ : Measure (Torus d)) N f X *
          weakGradC (Ucentered W (μ : Measure (Torus d)) N) X i k) ^ 2)
      ∂QN (μ : Measure (Torus d)) N := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  have hpair := isWeakGrad_psi hyp hμ hN hf
  have h1 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hpair⟩) hpair
  have hU := isWeakGrad_gsU hyp hac hN (μ := μm)
  have h2 := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hU⟩) hU
  have hK := centeredPartition_pos hyp μm N
  have hp : ∀ X : Config N d, 0 ≤ Real.exp (-Ucentered W μm N X) / centeredPartition W μm N :=
    fun X => div_nonneg (Real.exp_pos _).le hK.le
  have key : ∀ᵐ X ∂QN μm N, ∑ i, ∑ k,
      (weakGradC (psiG W μm N f) X i k + (1 / 2) * psiG W μm N f X *
        weakGradC (Ucentered W μm N) X i k) ^ 2 =
      (Real.exp (-Ucentered W μm N X) / centeredPartition W μm N) * gradSqC f X := by
    filter_upwards [ae_pi_of_ae_volume hyp hμ (h1.and h2)] with X hX
    set s := Real.sqrt (Real.exp (-Ucentered W μm N X) / centeredPartition W μm N) with hs_def
    have hs : s = (Real.sqrt (centeredPartition W μm N))⁻¹ * gsE W μm N (flat X) :=
      sqrt_dens_eq (μ := μm) X
    have hs2 : s ^ 2 = Real.exp (-Ucentered W μm N X) / centeredPartition W μm N :=
      Real.sq_sqrt (hp X)
    unfold gradSqC
    rw [Finset.mul_sum, ← hs2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : weakGradC (psiG W μm N f) X i k = gsPsiG W μm N f (flat X) (i, k) := by
      unfold weakGradC; exact congrFun hX.1 (i, k)
    have e2 : weakGradC (Ucentered W μm N) X i k = gsG W μm N (flat X) (i, k) := by
      unfold weakGradC; exact congrFun hX.2 (i, k)
    have e3 : psiG W μm N f X = f X * s := rfl
    have e4 : gsPsiG W μm N f (flat X) (i, k) =
        s * weakGradC f X i k - 1 / 2 * f X * s * gsG W μm N (flat X) (i, k) := by
      unfold gsPsiG weakGradC
      rw [hs]
      show _ = _
      simp only [Function.comp_apply]
      have : unflat (flat X) = X := rfl
      rw [this]
      ring
    rw [e1, e2, e3, e4]
    ring
  unfold energy
  rw [lintegral_gibbs_eq hyp hμ (fun X => ENNReal.ofReal (gradSqC f X))]
  unfold QN
  refine lintegral_congr_ae ?_
  filter_upwards [key] with X hX
  rw [hX, ENNReal.ofReal_mul (hp X)]

end WPB

/-! ### Helpers for WP-C -/

/-- `∫ h dP_N = ∫ p_N h dQ_N` (Bochner). -/
theorem g2_integral_gibbs_eq (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {N : ℕ} (h : Config N d → ℝ) :
    ∫ X, h X ∂gibbs V W N = ∫ X, (Real.exp (-Ucentered W (μ : Measure (Torus d)) N X) /
      centeredPartition W (μ : Measure (Torus d)) N) * h X
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hK := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  rw [gibbs_eq_centered_aux hyp hμ N]
  have hm : Measurable fun X : Config N d => ENNReal.ofReal (Real.exp (-Ucentered W
      (μ : Measure (Torus d)) N X) / centeredPartition W (μ : Measure (Torus d)) N) :=
    ENNReal.measurable_ofReal.comp (((measurable_Ucentered hyp _ N).neg.exp).div_const _)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK.le)]

theorem g2_integrable_mul_log_of_bdd {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsFiniteMeasure P] {u : α → ℝ} (hm : AEStronglyMeasurable u P) {M : ℝ}
    (h0 : ∀ᵐ x ∂P, 0 ≤ u x) (hM : ∀ᵐ x ∂P, u x ≤ M) :
    Integrable (fun x => u x * Real.log (u x)) P := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn)
  refine Integrable.of_bound (C := C) (Real.continuous_mul_log.comp_aestronglyMeasurable hm) ?_
  filter_upwards [h0, hM] with x hx0 hxM
  exact hC (u x) ⟨hx0, hxM⟩

theorem g2_ent_toReal_formula {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (u : α → ℝ) (hu : ∀ x, 0 ≤ u x) (hint : Integrable u P)
    (hlog : Integrable (fun x => u x * Real.log (u x)) P) :
    (ent P u).toReal = ∫ x, u x * Real.log (u x) ∂P -
      (∫ x, u x ∂P) * Real.log (∫ x, u x ∂P) := by
  rw [ent_eq_formula P u hu hint hlog, ENNReal.toReal_ofReal]
  set c := ∫ x, u x ∂P with hc
  have hc0 : 0 ≤ c := integral_nonneg hu
  rcases hc0.eq_or_lt with h0 | h0
  · have hz : u =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hu hint).mp h0.symm
    have h1 : ∫ x, u x * Real.log (u x) ∂P = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [hz] with x hx; simp [hx]
    rw [← h0, h1]; simp
  · have hpt : ∀ x, 0 ≤ u x * Real.log (u x) - u x * Real.log c + c - u x := by
      intro x
      rcases (hu x).eq_or_lt with h | h
      · rw [← h]; simpa using hc0
      · have := Real.log_le_sub_one_of_pos (div_pos h0 h)
        rw [Real.log_div h0.ne' h.ne'] at this
        have h3 := mul_le_mul_of_nonneg_left this h.le
        have h4 : u x * (c / u x - 1) = c - u x := by field_simp
        nlinarith
    have i1 : Integrable (fun x => u x * Real.log c) P := hint.mul_const _
    have i2 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log c) P := hlog.sub i1
    have i3 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log c + c) P :=
      i2.add (integrable_const c)
    have hF := integral_nonneg (μ := P)
      (f := fun x => u x * Real.log (u x) - u x * Real.log c + c - u x) hpt
    rw [integral_sub i3 hint, integral_add i2 (integrable_const c), integral_sub hlog i1,
      integral_mul_const, integral_const, ← hc] at hF
    simp at hF
    linarith

section WPC
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {N : ℕ} (hN : 1 ≤ N)

omit hN in
include hyp hμ in
/-- **(entropy-ground)**; no `1 ≤ N` needed. -/
theorem entropy_ground_identity {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) {B : ℝ}
    (hB : ∀ᵐ X ∂gibbs V W N, |f X| ≤ B) :
    (ent (gibbs V W N) (fun X => f X ^ 2)).toReal =
      (ent (QN (μ : Measure (Torus d)) N)
        (fun X => psiG W (μ : Measure (Torus d)) N f X ^ 2)).toReal +
      ∫ X, psiG W (μ : Measure (Torus d)) N f X ^ 2 * Ucentered W (μ : Measure (Torus d)) N X
        ∂QN (μ : Measure (Torus d)) N +
      Real.log (centeredPartition W (μ : Measure (Torus d)) N) *
        ∫ X, psiG W (μ : Measure (Torus d)) N f X ^ 2 ∂QN (μ : Measure (Torus d)) N := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set μm := (μ : Measure (Torus d))
  have : IsProbabilityMeasure (Measure.pi fun _ : Fin N => μm) := inferInstance
  unfold QN
  set Q := Measure.pi fun _ : Fin N => μm with hQ
  set P := gibbs V W N with hP
  set K := centeredPartition W μm N with hKdef
  set U := Ucentered W μm N with hUdef
  have hK : 0 < K := centeredPartition_pos hyp μm N
  set p : Config N d → ℝ := fun X => Real.exp (-U X) / K with hpdef
  have hp0 : ∀ X, 0 < p X := fun X => div_pos (Real.exp_pos _) hK
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm N
  have hUm : Measurable U := measurable_Ucentered hyp μm N
  have hpm : Measurable p := ((hUm.neg.exp).div_const K)
  have hpb : ∀ X, p X ≤ Real.exp BU / K := fun X => by
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) hK.le
    have := hBU X; rw [abs_le] at this; linarith
  have hQP : Q ≪ P := by
    rw [hP, gibbs_eq_centered_aux hyp hμ N]
    exact withDensity_absolutelyContinuous' (hpm.ennreal_ofReal.aemeasurable)
      (Eventually.of_forall fun X => (ENNReal.ofReal_pos.2 (hp0 X)).ne')
  have hfm : AEStronglyMeasurable f P := (memLp_of_memH1C hyp hf).aestronglyMeasurable
  have hfmQ : AEStronglyMeasurable f Q := hfm.mono_ac hQP
  have hBQ : ∀ᵐ X ∂Q, |f X| ≤ B := hQP.ae_le hB
  set u : Config N d → ℝ := fun X => f X ^ 2 with hu
  set v : Config N d → ℝ := fun X => psiG W μm N f X ^ 2 with hv
  have hvu : ∀ X, v X = p X * u X := fun X => by
    simp only [hv, hu, psiG]
    rw [mul_pow, Real.sq_sqrt (hp0 X).le]; ring
  have hu0 : ∀ X, 0 ≤ u X := fun X => sq_nonneg _
  have hv0 : ∀ X, 0 ≤ v X := fun X => sq_nonneg _
  have huM_P : ∀ᵐ X ∂P, u X ≤ B ^ 2 := by
    filter_upwards [hB] with X hX
    exact sq_le_sq' (by linarith [abs_nonneg (f X), neg_abs_le (f X)] ) (le_trans (le_abs_self _) hX)
  have huM_Q : ∀ᵐ X ∂Q, u X ≤ B ^ 2 := hQP.ae_le huM_P
  have hum_P : AEStronglyMeasurable u P := hfm.pow 2
  have hum_Q : AEStronglyMeasurable u Q := hfmQ.pow 2
  have hvm_Q : AEStronglyMeasurable v Q :=
    (hpm.aestronglyMeasurable.mul hum_Q).congr (Eventually.of_forall fun X => (hvu X).symm)
  have hvM_Q : ∀ᵐ X ∂Q, v X ≤ Real.exp BU / K * B ^ 2 := by
    filter_upwards [huM_Q] with X hX
    rw [hvu]
    exact mul_le_mul (hpb X) hX (hu0 X) (div_nonneg (Real.exp_pos _).le hK.le)
  have hiu_P : Integrable u P :=
    Integrable.of_bound (C := B ^ 2) hum_P (by
      filter_upwards [huM_P] with X hX
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 X)]; exact hX)
  have hiv_Q : Integrable v Q :=
    Integrable.of_bound (C := Real.exp BU / K * B ^ 2) hvm_Q (by
      filter_upwards [hvM_Q] with X hX
      rw [Real.norm_eq_abs, abs_of_nonneg (hv0 X)]; exact hX)
  have hil_P : Integrable (fun X => u X * Real.log (u X)) P :=
    g2_integrable_mul_log_of_bdd hum_P (Eventually.of_forall hu0) huM_P
  have hil_Q : Integrable (fun X => v X * Real.log (v X)) Q :=
    g2_integrable_mul_log_of_bdd hvm_Q (Eventually.of_forall hv0) hvM_Q
  have hivU : Integrable (fun X => v X * U X) Q :=
    Integrable.of_bound (C := Real.exp BU / K * B ^ 2 * BU) (hvm_Q.mul hUm.aestronglyMeasurable) (by
      filter_upwards [hvM_Q] with X hX
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv0 X)]
      exact mul_le_mul hX (hBU X) (abs_nonneg _) ((hv0 X).trans hX))
  -- the mass
  have hm : ∫ X, u X ∂P = ∫ X, v X ∂Q := by
    rw [hP, g2_integral_gibbs_eq hyp hμ]
    exact integral_congr_ae (Eventually.of_forall fun X => (hvu X).symm)
  -- the pointwise identity
  have hpt : ∀ X, p X * (u X * Real.log (u X)) =
      v X * Real.log (v X) + v X * U X + Real.log K * v X := by
    intro X
    rcases (hu0 X).eq_or_lt with h | h
    · have : v X = 0 := by rw [hvu, ← h]; simp
      rw [← h, this]; simp
    · have hlp : Real.log (p X) = -U X - Real.log K := by
        simp only [hpdef]
        rw [Real.log_div (Real.exp_pos _).ne' hK.ne', Real.log_exp]
      have hlv : Real.log (v X) = Real.log (p X) + Real.log (u X) := by
        rw [hvu, Real.log_mul (hp0 X).ne' h.ne']
      rw [hlv, hlp, hvu]; ring
  have hent_int : ∫ X, u X * Real.log (u X) ∂P =
      ∫ X, v X * Real.log (v X) ∂Q + ∫ X, v X * U X ∂Q + Real.log K * ∫ X, v X ∂Q := by
    rw [hP, g2_integral_gibbs_eq hyp hμ]
    rw [integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_add (f := fun X => v X * Real.log (v X) + v X * U X)
      (g := fun X => Real.log K * v X) (hil_Q.add hivU) (hiv_Q.const_mul _),
      integral_add (f := fun X => v X * Real.log (v X)) (g := fun X => v X * U X) hil_Q hivU,
      integral_const_mul]
  rw [g2_ent_toReal_formula P u hu0 hiu_P hil_P, g2_ent_toReal_formula Q v hv0 hiv_Q hil_Q,
    hent_int, hm]
  ring

end WPC

end SharpLSI.FL
