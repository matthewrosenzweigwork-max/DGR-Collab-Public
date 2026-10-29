import SharpSymmetricLSI.Paper.LocalStructure1

/-!
# Section 4.2: minimality gives `A = I + T ≥ 0` (Phase 3, lane D; R14)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `(1+u) log(1+u) ≤ u + u²/2 + 4|u|³` for `|u| ≤ 1/2`. -/
theorem one_add_mul_log_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    (1 + u) * Real.log (1 + u) ≤ u + u ^ 2 / 2 + 4 * |u| ^ 3 := by
  have h1 : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := abs_log_sub_add_sum_range_le h1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, sub_neg_eq_add, abs_neg] at h
  have hden : |u| ^ (2 + 1) / (1 - |u|) ≤ 2 * |u| ^ 3 := by
    rw [div_le_iff₀ (by linarith), show (2 + 1 : ℕ) = 3 from rfl]
    have := abs_nonneg u
    nlinarith [mul_nonneg (pow_nonneg this 3) (by linarith : (0 : ℝ) ≤ 1 - 2 * |u|)]
  have hlog : Real.log (1 + u) ≤ u - u ^ 2 / 2 + 2 * |u| ^ 3 := by
    have := (abs_le.mp (h.trans hden)).2
    norm_num at this
    linarith
  have hpos : 0 < 1 + u := by have := neg_abs_le u; linarith
  have h3 : |u| ^ 3 = |u ^ 3| := by rw [abs_pow]
  calc (1 + u) * Real.log (1 + u) ≤ (1 + u) * (u - u ^ 2 / 2 + 2 * |u| ^ 3) :=
        mul_le_mul_of_nonneg_left hlog hpos.le
    _ = u + u ^ 2 / 2 - u ^ 3 / 2 + 2 * |u| ^ 3 * (1 + u) := by ring
    _ ≤ u + u ^ 2 / 2 + 4 * |u| ^ 3 := by
        have hu3 : -(u ^ 3) / 2 ≤ |u| ^ 3 / 2 := by
          rw [h3]; have := neg_abs_le (u ^ 3); linarith
        have hb : 2 * |u| ^ 3 * (1 + u) ≤ 2 * |u| ^ 3 * (3 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self u]) (by positivity)
        nlinarith [pow_nonneg (abs_nonneg u) 3]

section second
variable (hyp : Hyp V W KV KW)
include hyp

/-- **Second variation**, bounded centered directions:
`∫ h² dμ + ∫∫ W h h dμ dμ ≥ 0`. -/
theorem secondVar_nonneg_bdd {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {h : Torus d → ℝ} (hm : Measurable h) {M : ℝ} (hM : ∀ x, |h x| ≤ M)
    (h0 : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) :
    0 ≤ ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) +
      ∫ x, h x * (∫ y, W x y * h y ∂(μ : Measure (Torus d))) ∂(μ : Measure (Torus d)) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨hpm, hppos, hp1⟩ := elDensity_props hyp μm
  set p := elDens V W μm with hpdef
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  have hpC : ∀ x, p x ≤ C := fun x => ((hb μm inferInstance).1 x).2
  have hC0 : 0 < C := hc.trans_le (((hb μm inferInstance).1 0).1.trans (hpC 0))
  have hp2C : ∀ x, p x ≤ 2 * C := fun x => by linarith [hpC x]
  have hμp : μm = densMeasure p := minimizer_eq_elDensity hyp hμ
  have hpi := integrable_of_integral_eq_one' hp1
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μm x with hΦ
  have hΦb : ∀ x, |Φ x| ≤ BV + BW := fun x => abs_potential_le hBV (fun x y => hBW (x, y)) μm x
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add (measurable_convMeas hyp μm)
  set Z := ∫ y, exp (-Φ y) ∂haar d with hZ
  have hei : Integrable (fun x => exp (-Φ x)) (haar d) := integrable_of_bdd
    (measurable_exp.comp hΦm.neg) (C := exp (BV + BW)) fun x => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (by linarith [neg_le_abs (Φ x), hΦb x])
  have hZpos : 0 < Z := integral_exp_pos hei
  have hlogp : ∀ x, Real.log (p x) = -Φ x - Real.log Z := fun x => by
    have : p x = exp (-Φ x) / Z := by simp only [hpdef, elDens, hΦ, hZ, neg_add']
    rw [this, Real.log_div (exp_pos _).ne' hZpos.ne', Real.log_exp]
  have hw : ∀ x, convDens W p x = convMeas W μm x := fun x => by
    rw [hμp, convMeas_densMeasure (fun x => (hppos x).le) hp1]
  -- integrals against `μ` as integrals against `m`
  have hμint : ∀ F : Torus d → ℝ, ∫ x, F x ∂μm = ∫ x, p x * F x ∂haar d := fun F => by
    rw [hμp]; exact integral_densMeasure' (fun x => (hppos x).le) hp1 F
  -- bounded-integrability helper
  have bi : ∀ {F : Torus d → ℝ}, Measurable F → ∀ B, (∀ x, |F x| ≤ B) → Integrable F (haar d) :=
    fun {F} hF B hB => integrable_of_bdd hF hB
  have hpb : ∀ x, |p x| ≤ C := fun x => by rw [abs_of_pos (hppos x)]; exact hpC x
  set q : Torus d → ℝ := fun x => p x * h x with hq
  have hqm : Measurable q := hpm.mul hm
  have hqb : ∀ x, |q x| ≤ C * M := fun x => by
    rw [hq, abs_mul]; exact mul_le_mul (hpb x) (hM x) (abs_nonneg _) ((abs_nonneg _).trans (hpb x))
  have hqi : Integrable q (haar d) := bi hqm _ hqb
  have hq0 : ∫ x, q x ∂haar d = 0 := by rw [← h0, hμint]
  set S := ∫ x, h x ^ 2 ∂μm + ∫ x, h x * (∫ y, W x y * h y ∂μm) ∂μm with hSdef
  have hS : S = ∫ x, p x * h x ^ 2 ∂haar d + Aform W q q := by
    rw [hSdef, hμint, hμint]
    congr 1
    unfold Aform convDens
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hq]
    rw [hμint, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  -- the variation `p(1 + t h)`
  set t₀ : ℝ := 1 / (2 * M + 2) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have key : ∀ t, 0 < t → t ≤ t₀ →
      0 ≤ t ^ 2 / 2 * S + 4 * t ^ 3 * (C * M ^ 3) := by
    intro t ht0 ht1
    have hut : ∀ x, |t * h x| ≤ 1 / 2 := fun x => by
      rw [abs_mul, abs_of_pos ht0]
      calc t * |h x| ≤ t₀ * M := mul_le_mul ht1 (hM x) (abs_nonneg _) ht₀pos.le
        _ ≤ 1 / 2 := by rw [ht₀, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
    set g : Torus d → ℝ := fun x => p x + t * q x with hg
    have hgm : Measurable g := hpm.add (measurable_const.mul hqm)
    have hg' : ∀ x, g x = p x * (1 + t * h x) := fun x => by simp only [hg, hq]; ring
    have hg0 : ∀ x, 0 ≤ g x := fun x => by
      rw [hg']
      exact mul_nonneg (hppos x).le (by linarith [neg_abs_le (t * h x), hut x])
    have hg1 : ∫ x, g x ∂haar d = 1 := by
      rw [integral_add hpi (hqi.const_mul t), integral_const_mul, hq0, hp1]; ring
    have hgb : ∀ x, g x ≤ 2 * C := fun x => by
      rw [hg']
      have := hpC x; have := (hppos x).le
      have h1 : 1 + t * h x ≤ 2 := by linarith [le_abs_self (t * h x), hut x]
      nlinarith
    have hKi : ∀ {f : Torus d → ℝ}, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 2 * C) →
        Integrable (fun x => klFun (f x)) (haar d) := fun {f} hf h0 hC =>
      bi (measurable_klFun.comp hf) ((2 * C + 1) ^ 2) fun x => by
        rw [abs_of_nonneg (klFun_nonneg (h0 x))]; exact klFun_le_bound (h0 x) (hC x)
    have hle : freeEnergy V W μm ≤ freeEnergy V W (densMeasure g) := by
      haveI := isProbabilityMeasure_densMeasure' hg0 hg1
      unfold IsMinimizer at hμ
      rw [hμ]
      exact iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ) ⟨densMeasure g, inferInstance⟩
    rw [hμp, freeEnergy_densMeasure hyp hpm (fun x => (hppos x).le) hp1
      (hKi hpm (fun x => (hppos x).le) hp2C),
      freeEnergy_densMeasure hyp hgm hg0 hg1 (hKi hgm hg0 hgb), EReal.coe_le_coe_iff] at hle
    -- pointwise identity for the entropy densities
    set ℓ : Torus d → ℝ := fun x => (1 + t * h x) * Real.log (1 + t * h x) with hℓ
    have hpt : ∀ x, klFun (g x) - klFun (p x) =
        p x * ℓ x - t * q x * Φ x - t * q x * (Real.log Z + 1) := fun x => by
      have hp0 := (hppos x).ne'
      have h1 : 0 < 1 + t * h x := by linarith [neg_abs_le (t * h x), hut x]
      rw [hg', klFun_apply, klFun_apply, Real.log_mul hp0 h1.ne', hlogp]
      simp only [hℓ, hq]
      ring
    have hℓm : Measurable ℓ := (measurable_const.add (measurable_const.mul hm)).mul
      (Real.measurable_log.comp (measurable_const.add (measurable_const.mul hm)))
    have hℓb : ∀ x, |ℓ x| ≤ 2 := fun x => by
      have h1 : 1 / 2 ≤ 1 + t * h x := by linarith [neg_abs_le (t * h x), hut x]
      have h2 : 1 + t * h x ≤ 3 / 2 := by linarith [le_abs_self (t * h x), hut x]
      simp only [hℓ]
      rw [abs_mul, abs_of_pos (by linarith)]
      have hl1 : Real.log (1 + t * h x) ≤ 1 / 2 := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t * h x); linarith
      have hl2 : -(1 : ℝ) ≤ Real.log (1 + t * h x) := by
        have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) h1
        have h4 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
        linarith [Real.log_two_lt_d9]
      have : |Real.log (1 + t * h x)| ≤ 1 := abs_le.mpr ⟨hl2, by linarith⟩
      calc (1 + t * h x) * |Real.log (1 + t * h x)| ≤ 3 / 2 * 1 :=
            mul_le_mul h2 this (abs_nonneg _) (by norm_num)
        _ ≤ 2 := by norm_num
    have iℓ : Integrable (fun x => p x * ℓ x) (haar d) := bi (hpm.mul hℓm) (C * 2) fun x => by
      rw [abs_mul]; exact mul_le_mul (hpb x) (hℓb x) (abs_nonneg _) hC0.le
    have iqΦ : Integrable (fun x => t * q x * Φ x) (haar d) := bi ((measurable_const.mul hqm).mul hΦm)
      (|t| * (C * M) * (BV + BW)) fun x => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hqb x) (abs_nonneg _)) (hΦb x) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) (mul_nonneg hC0.le hM0))
    have hK : ∫ x, klFun (g x) ∂haar d - ∫ x, klFun (p x) ∂haar d =
        ∫ x, p x * ℓ x ∂haar d - ∫ x, t * q x * Φ x ∂haar d := by
      rw [← integral_sub (hKi hgm hg0 hgb) (hKi hpm (fun x => (hppos x).le) hp2C)]
      simp_rw [hpt]
      rw [integral_sub (f := fun x => p x * ℓ x - t * q x * Φ x)
          (g := fun x => t * q x * (Real.log Z + 1)) (iℓ.sub iqΦ) ((hqi.const_mul t).mul_const _),
        integral_sub (f := fun x => p x * ℓ x) (g := fun x => t * q x * Φ x) iℓ iqΦ,
        integral_mul_const, integral_const_mul, hq0]
      ring
    have hVi : ∀ {f : Torus d → ℝ}, Integrable f (haar d) → Integrable (fun x => f x * V x) (haar d) :=
      fun {f} hf => Integrable.mono' (hf.abs.mul_const BV) (hf.aestronglyMeasurable.mul
        hyp.continuous_V.aestronglyMeasurable) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left (hBV x) (abs_nonneg _))
    have hV : ∫ x, g x * V x ∂haar d - ∫ x, p x * V x ∂haar d = ∫ x, t * q x * V x ∂haar d := by
      rw [← integral_sub (f := fun x => g x * V x) (g := fun x => p x * V x)
        (hVi (hpi.add (hqi.const_mul t))) (hVi hpi)]
      congr 1; funext x; simp only [hg]; ring
    have hA : Aform W g g - Aform W p p = 2 * ∫ x, t * q x * convMeas W μm x ∂haar d +
        t ^ 2 * Aform W q q := by
      have hc : ∀ x, convDens W g x = 1 * convDens W p x + t * convDens W q x := fun x => by
        have := convDens_add hyp hpi hqi 1 t x
        simp only [one_mul] at this ⊢
        rw [← this]
      have i1 := integrable_mul_convDens hyp hpm hpi hpi
      have i2 := integrable_mul_convDens hyp hqm hqi hpi
      have i3 := integrable_mul_convDens hyp hpm hpi hqi
      have i4 := integrable_mul_convDens hyp hqm hqi hqi
      have hcomm := Aform_comm hyp hpm hqm hpi hqi
      unfold Aform at hcomm ⊢
      simp_rw [hc]
      have e : ∀ x, g x * (1 * convDens W p x + t * convDens W q x) =
          1 * (p x * convDens W p x) + t * (p x * convDens W q x) +
          t * (q x * convDens W p x) + t ^ 2 * (q x * convDens W q x) := fun x => by
        simp only [hg]; ring
      simp_rw [e]
      rw [integral_lin4 i1 i2 i3 i4, ← hcomm]
      have e2 : ∫ x, t * q x * convMeas W μm x ∂haar d = t * ∫ x, q x * convDens W p x ∂haar d := by
        rw [← integral_const_mul]; congr 1; funext x; rw [hw]; ring
      rw [e2]; ring
    -- assemble the first-order cancellation
    have hlin : -(∫ x, t * q x * Φ x ∂haar d) + ∫ x, t * q x * V x ∂haar d +
        ∫ x, t * q x * convMeas W μm x ∂haar d = 0 := by
      have iV := hVi (hqi.const_mul t)
      have iw : Integrable (fun x => t * q x * convMeas W μm x) (haar d) :=
        bi ((measurable_const.mul hqm).mul (measurable_convMeas hyp μm)) (|t| * (C * M) * BW)
          fun x => by
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul_of_nonneg_left (hqb x) (abs_nonneg _))
              (abs_integral_le_of_bdd fun z => hBW (x, z)) (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) (mul_nonneg hC0.le hM0))
      have e : ∫ x, t * q x * Φ x ∂haar d =
          ∫ x, t * q x * V x ∂haar d + ∫ x, t * q x * convMeas W μm x ∂haar d := by
        rw [← integral_add (f := fun x => t * q x * V x) (g := fun x => t * q x * convMeas W μm x)
          iV iw]
        congr 1; funext x; simp only [hΦ]; ring
      rw [e]; ring
    -- the Taylor bound
    have hTay : ∫ x, p x * ℓ x ∂haar d ≤ t ^ 2 / 2 * ∫ x, p x * h x ^ 2 ∂haar d +
        4 * t ^ 3 * (C * M ^ 3) := by
      have i2 : Integrable (fun x => p x * h x ^ 2) (haar d) := bi (hpm.mul (hm.pow_const 2))
        (C * M ^ 2) fun x => by
          rw [abs_mul, abs_pow]
          exact mul_le_mul (hpb x) (pow_le_pow_left₀ (abs_nonneg _) (hM x) 2) (by positivity)
            ((abs_nonneg _).trans (hpb x))
      have i3 : Integrable (fun x => p x * |h x| ^ 3) (haar d) := bi (hpm.mul (hm.abs.pow_const 3))
        (C * M ^ 3) fun x => by
          rw [abs_mul, abs_pow, abs_abs]
          exact mul_le_mul (hpb x) (pow_le_pow_left₀ (abs_nonneg _) (hM x) 3) (by positivity)
            ((abs_nonneg _).trans (hpb x))
      have hpt2 : ∀ x, p x * ℓ x ≤ t * q x + t ^ 2 / 2 * (p x * h x ^ 2) +
          4 * t ^ 3 * (p x * |h x| ^ 3) := fun x => by
        have := mul_le_mul_of_nonneg_left (one_add_mul_log_le (hut x)) (hppos x).le
        rw [abs_mul, abs_of_pos ht0] at this
        simp only [hℓ, hq]
        nlinarith [this]
      calc ∫ x, p x * ℓ x ∂haar d ≤ ∫ x, (t * q x + t ^ 2 / 2 * (p x * h x ^ 2) +
            4 * t ^ 3 * (p x * |h x| ^ 3)) ∂haar d :=
            integral_mono iℓ (((hqi.const_mul t).add (i2.const_mul _)).add (i3.const_mul _)) hpt2
        _ = t ^ 2 / 2 * ∫ x, p x * h x ^ 2 ∂haar d + 4 * t ^ 3 * ∫ x, p x * |h x| ^ 3 ∂haar d := by
            rw [integral_add (f := fun x => t * q x + t ^ 2 / 2 * (p x * h x ^ 2))
                (g := fun x => 4 * t ^ 3 * (p x * |h x| ^ 3))
                ((hqi.const_mul t).add (i2.const_mul _)) (i3.const_mul _),
              integral_add (f := fun x => t * q x) (g := fun x => t ^ 2 / 2 * (p x * h x ^ 2))
                (hqi.const_mul t) (i2.const_mul _), integral_const_mul, integral_const_mul,
              integral_const_mul, hq0]
            ring
        _ ≤ _ := by
            gcongr
            calc ∫ x, p x * |h x| ^ 3 ∂haar d ≤ ∫ _x, C * M ^ 3 ∂haar d :=
                  integral_mono i3 (integrable_const _) fun x => by
                    exact (le_abs_self _).trans (by
                      rw [abs_mul, abs_pow, abs_abs]
                      exact mul_le_mul (hpb x) (pow_le_pow_left₀ (abs_nonneg _) (hM x) 3)
                        (by positivity) ((abs_nonneg _).trans (hpb x)))
              _ = C * M ^ 3 := by simp
    rw [hS]
    nlinarith [hK, hV, hA, hlin, hTay]
  -- conclude
  have hX := nonneg_of_forall_small (X := t₀ * (S / 2)) (Y := t₀ ^ 2 * (4 * (C * M ^ 3)))
    fun s hs0 hs1 => by
      have := key (t₀ * s) (mul_pos ht₀pos hs0) (by nlinarith)
      have hts : 0 < t₀ * s := mul_pos ht₀pos hs0
      have e : (t₀ * s) ^ 2 / 2 * S + 4 * (t₀ * s) ^ 3 * (C * M ^ 3) =
          (t₀ * s) * (s * (t₀ * (S / 2)) + s ^ 2 * (t₀ ^ 2 * (4 * (C * M ^ 3)))) := by ring
      rw [e] at this
      exact (mul_nonneg_iff_of_pos_left hts).mp this
  nlinarith

/-- **`A = I + T ≥ 0`** on `L²_0(μ)` for a minimizer. -/
theorem secondVar_nonneg {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {h : Torus d → ℝ} (hh : MemL20 μ h) : 0 ≤ secondVar W μ h := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  -- the quadratic form for integrable directions
  set Q : (Torus d → ℝ) → ℝ := fun f => ∫ x, f x ^ 2 ∂μm + ∫ x, f x * (∫ y, W x y * f y ∂μm) ∂μm
    with hQ
  have hi := hh.1.integrable one_le_two
  have hsv : secondVar W μ h = Q h := by
    unfold secondVar Top
    have hab : Integrable (fun x => h x * ∫ y, W x y * h y ∂μm) μm :=
      Integrable.mono' (hi.abs.mul_const (BW * ∫ y, |h y| ∂μm))
        (hi.aestronglyMeasurable.mul (aW_aesm hyp μm hi.aestronglyMeasurable))
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (aW_bdd hyp μm (fun x y => hBW (x, y)) hi x) (abs_nonneg _))
    have e : ∀ x, h x * (h x + ((∫ y, W x y * h y ∂μm) - ∫ x', (∫ y, W x' y * h y ∂μm) ∂μm)) =
        h x ^ 2 + h x * (∫ y, W x y * h y ∂μm) - (∫ x', (∫ y, W x' y * h y ∂μm) ∂μm) * h x :=
      fun x => by ring
    show ∫ x, h x * (h x + ((∫ y, W x y * h y ∂μm) - ∫ x', (∫ y, W x' y * h y ∂μm) ∂μm)) ∂μm = Q h
    rw [integral_congr_ae (Eventually.of_forall e)]
    rw [integral_sub (f := fun x => h x ^ 2 + h x * (∫ y, W x y * h y ∂μm))
      (g := fun x => (∫ x', (∫ y, W x' y * h y ∂μm) ∂μm) * h x) (hh.1.integrable_sq.add hab)
      (hi.const_mul _), integral_add (f := fun x => h x ^ 2) hh.1.integrable_sq hab,
      integral_const_mul, hh.2, mul_zero, sub_zero]
  rw [hsv]
  -- a measurable representative
  set h' := hi.aestronglyMeasurable.mk h
  have hh' : h =ᵐ[μm] h' := hi.aestronglyMeasurable.ae_eq_mk
  have hm' : Measurable h' := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hi' : Integrable h' μm := hi.congr hh'
  have hL' : MemLp h' 2 μm := hh.1.ae_eq hh'
  have hQe : Q h = Q h' := by
    rw [hQ]
    have hin : ∀ x, ∫ y, W x y * h y ∂μm = ∫ y, W x y * h' y ∂μm := fun x =>
      integral_congr_ae (hh'.mono fun y hy => by simp only [hy])
    simp_rw [hin]
    congr 1
    · exact integral_congr_ae (hh'.mono fun x hx => by simp only [hx])
    · exact integral_congr_ae (hh'.mono fun x hx => by simp only [hx])
  rw [hQe]
  -- truncations
  set B := ∫ y, |h' y| ∂μm
  have hB0 : 0 ≤ B := integral_nonneg fun _ => abs_nonneg _
  set g : ℕ → Torus d → ℝ := fun n x => max (-(n : ℝ)) (min (h' x) n) with hg
  have hgm : ∀ n, Measurable (g n) := fun n => measurable_const.max (hm'.min measurable_const)
  have hgabs : ∀ n x, |g n x| ≤ |h' x| := fun n x => by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hg]
    rw [abs_le]
    constructor
    · exact le_max_of_le_right (le_min (neg_abs_le _) (by linarith [abs_nonneg (h' x)]))
    · exact max_le (by linarith [abs_nonneg (h' x)]) ((min_le_left _ _).trans (le_abs_self _))
  have hgn : ∀ n x, |g n x| ≤ n := fun n x => by
    simp only [hg]
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (min_le_right _ _)⟩
  have hglim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (h' x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (Nat.ceil |h' x|)] with n hn
    have hn' : |h' x| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [hg]
    rw [min_eq_left (le_abs_self _ |>.trans hn'), max_eq_right (by linarith [neg_abs_le (h' x)])]
  have hgi : ∀ n, Integrable (g n) μm := fun n => integrable_of_bdd (hgm n) (hgn n)
  set m : ℕ → ℝ := fun n => ∫ x, g n x ∂μm
  have hm0 : Tendsto m atTop (𝓝 0) := by
    rw [← hh.2]
    have := tendsto_integral_of_dominated_convergence (μ := μm) (fun x => |h' x|)
      (fun n => (hgm n).aestronglyMeasurable) hi'.abs
      (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgabs n x)
      (Eventually.of_forall hglim)
    rwa [integral_congr_ae hh'.symm] at this
  have hmB : ∀ n, |m n| ≤ B := fun n => (abs_integral_le_integral_abs).trans
    (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hi'.abs
      (Eventually.of_forall fun x => hgabs n x))
  set f : ℕ → Torus d → ℝ := fun n x => g n x - m n
  have hfm : ∀ n, Measurable (f n) := fun n => (hgm n).sub measurable_const
  have hfb : ∀ n x, |f n x| ≤ |h' x| + B := fun n x =>
    (abs_sub _ _).trans (add_le_add (hgabs n x) (hmB n))
  have hflim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (h' x)) := fun x => by
    have := (hglim x).sub hm0
    rwa [sub_zero] at this
  have hQf : ∀ n, 0 ≤ Q (f n) := fun n => by
    have h0 : ∫ x, f n x ∂μm = 0 := by
      simp only [f]; rw [integral_sub (hgi n) (integrable_const _)]; simp [m]
    exact secondVar_nonneg_bdd hyp hμ (hfm n) (M := n + B) (fun x =>
      (abs_sub _ _).trans (add_le_add (hgn n x) (hmB n))) h0
  -- passage to the limit
  have hdom : Integrable (fun x => |h' x| + B) μm := hi'.abs.add (integrable_const _)
  have t1 : Tendsto (fun n => ∫ x, f n x ^ 2 ∂μm) atTop (𝓝 (∫ x, h' x ^ 2 ∂μm)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * h' x ^ 2 + 2 * B ^ 2)
      (fun n => ((hfm n).pow_const 2).aestronglyMeasurable)
      ((hL'.integrable_sq.const_mul 2).add (integrable_const _))
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hflim x).pow 2)
    rw [Real.norm_eq_abs, abs_pow]
    have := hfb n x
    have h1 : |f n x| ^ 2 ≤ (|h' x| + B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [sq_abs (h' x), sq_nonneg (|h' x| - B)]
  have ta : ∀ x, Tendsto (fun n => ∫ y, W x y * f n y ∂μm) atTop (𝓝 (∫ y, W x y * h' y ∂μm)) :=
    fun x => tendsto_integral_of_dominated_convergence (fun y => BW * (|h' y| + B))
      (fun n => ((hyp.continuous_W.measurable.comp measurable_prodMk_left).mul
        (hfm n)).aestronglyMeasurable) (hdom.const_mul _)
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hBW (x, y)) (hfb n y) (abs_nonneg _) hBW0)
      (Eventually.of_forall fun y => (hflim y).const_mul _)
  have hab : ∀ n x, |∫ y, W x y * f n y ∂μm| ≤ BW * (B + B) := fun n x => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |W x y * f n y| ∂μm ≤ ∫ y, BW * (|h' y| + B) ∂μm :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hdom.const_mul _)
            (Eventually.of_forall fun y => by
              show |W x y * f n y| ≤ BW * (|h' y| + B)
              rw [abs_mul]; exact mul_le_mul (hBW (x, y)) (hfb n y) (abs_nonneg _) hBW0)
      _ = BW * (B + B) := by
          rw [integral_const_mul, integral_add hi'.abs (integrable_const _)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          rfl
  have t2 : Tendsto (fun n => ∫ x, f n x * (∫ y, W x y * f n y ∂μm) ∂μm) atTop
      (𝓝 (∫ x, h' x * (∫ y, W x y * h' y ∂μm) ∂μm)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (|h' x| + B) * (BW * (B + B)))
      (fun n => (hfm n).aestronglyMeasurable.mul (aW_aesm hyp μm (hfm n).aestronglyMeasurable))
      (hdom.mul_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hflim x).mul (ta x))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hfb n x) (hab n x) (abs_nonneg _) (by positivity)
  exact ge_of_tendsto' (t1.add t2) hQf

end second

end SharpLSI
