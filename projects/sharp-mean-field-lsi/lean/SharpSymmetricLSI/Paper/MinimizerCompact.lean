import SharpSymmetricLSI.Paper.ELEquation
import SharpSymmetricLSI.Paper.AscoliSeq
import SharpSymmetricLSI.Paper.UpperApprox
import SharpSymmetricLSI.Infra.Heat

/-!
# Lemma 4.1: compactness of the minimizer densities in `W^{1,∞}` (Phase 3, lane D; R13)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem convMeas_densMeasure {h : Torus d → ℝ} (h0 : ∀ x, 0 ≤ h x) (h1 : ∫ x, h x ∂haar d = 1)
    (x : Torus d) : convMeas W (densMeasure h) x = convDens W h x := by
  unfold convMeas convDens
  rw [integral_densMeasure' h0 h1]
  congr 1; funext y; ring

section grad
variable (hyp : Hyp V W KV KW)
include hyp

/-- The weak gradient of the Euler–Lagrange density: `∇p = -p (∇V + β)`. -/
theorem isWeakGrad_elDensity {h : Torus d → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    (h1 : ∫ x, h x ∂haar d = 1) :
    IsWeakGrad (elDens V W (densMeasure h))
      (fun x k => -elDens V W (densMeasure h) x * (lipGrad V x k + bForceL W h x k)) := by
  have hi := integrable_of_integral_eq_one' h1
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  set B := BV + BW
  have hB0 : 0 ≤ B := add_nonneg ((abs_nonneg _).trans (hBV 0)) ((abs_nonneg _).trans (hBW 0))
  set Φ : Torus d → ℝ := fun x => V x + convDens W h x with hΦ
  have hΦb : ∀ x, |Φ x| ≤ B := fun x => by
    have := abs_potential_le hBV (fun x y => hBW (x, y)) (densMeasure h) x
    rwa [convMeas_densMeasure h0 h1] at this
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add (measurable_convDens hyp hm)
  set g : Torus d → Fin d → ℝ := fun x k => lipGrad V x k + bForceL W h x k with hgdef
  have hΦw : IsWeakGrad Φ g :=
    (isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp)).add (isWeakGrad_convDens hyp hm hi)
  have hgm : ∀ k, Measurable fun x => g x k := fun k =>
    (measurable_lipGrad hyp.continuous_V k).add (measurable_bForceL' hyp hi k)
  have hgb : ∀ x k, |g x k| ≤ (Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ) +
      Cb * ∫ y, |h y| ∂haar d := fun x k => by
    refine (abs_add_le _ _).trans (add_le_add (abs_lipGrad_le (lipschitz_V hyp) x k) ?_)
    unfold bForceL
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |bGrad W x y k * h y| ∂haar d ≤ ∫ y, Cb * |h y| ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hi.abs.const_mul Cb) (Eventually.of_forall fun y => by
              show |bGrad W x y k * h y| ≤ Cb * |h y|
              rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _))
      _ = _ := integral_const_mul _ _
  have h2 := hΦw.cmul (-2)
  have h2i : Integrable (fun x => -2 * Φ x) volume :=
    integrable_of_bdd (measurable_const.mul hΦm) (C := 2 * B) fun x => by
      rw [abs_mul]; norm_num; linarith [hΦb x]
  have h2g : ∀ k, Integrable (fun x => -2 * g x k) volume := fun k =>
    integrable_of_bdd (measurable_const.mul (hgm k)) fun x => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hgb x k) (abs_nonneg _)
  have h2B : 0 ≤ 2 * B := by positivity
  obtain ⟨L, hL⟩ := deriv_expCut_bdd (2 * B) h2B
  have h3 := isWeakGrad_comp h2 h2i h2g ((contDiff_expCut (2 * B) h2B).of_le (by simp)) hL
  set Z := ∫ y, exp (-Φ y) ∂haar d with hZ
  have h4 := h3.cmul Z⁻¹
  have hb2 : ∀ x, |-2 * Φ x| ≤ 2 * B := fun x => by rw [abs_mul]; norm_num; linarith [hΦb x]
  have hel' : ∀ x, elDens V W (densMeasure h) x = Z⁻¹ * exp (-Φ x) := fun x => by
    simp only [elDens, convMeas_densMeasure h0 h1, hZ, hΦ, neg_add']
    ring
  have hel : ∀ x, elDens V W (densMeasure h) x = Z⁻¹ * expCut (2 * B) h2B (-2 * Φ x) := fun x => by
    rw [expCut_eq h2B (hb2 x), show -2 * Φ x / 2 = -Φ x by ring, hel']
  convert h4 using 1
  · funext x; exact hel x
  · funext x k
    rw [hel', deriv_expCut h2B (hb2 x), show -2 * Φ x / 2 = -Φ x by ring]
    simp only [hgdef]
    ring

end grad

theorem klFun_le_bound {t C : ℝ} (h0 : 0 ≤ t) (hC : t ≤ C) : klFun t ≤ (C + 1) ^ 2 := by
  have h1 : klFun t ≤ (t - 1) ^ 2 := by
    rw [klFun_apply]
    rcases h0.eq_or_lt with h | h
    · rw [← h]; simp
    · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) h0
      nlinarith
  nlinarith

section conv
variable (hyp : Hyp V W KV KW)
include hyp

/-- `E(h) = ∫ klFun h + ∫ hV + A(h,h)/2` is continuous under bounded pointwise convergence. -/
theorem tendsto_energy {hs : ℕ → Torus d → ℝ} {h : Torus d → ℝ} (hsm : ∀ n, Measurable (hs n))
    (hm : Measurable h) {C : ℝ} (hs0 : ∀ n x, 0 ≤ hs n x) (hsC : ∀ n x, hs n x ≤ C)
    (hlim : ∀ x, Tendsto (fun n => hs n x) atTop (𝓝 (h x))) :
    Tendsto (fun n => ∫ x, klFun (hs n x) ∂haar d + ∫ x, hs n x * V x ∂haar d +
      Aform W (hs n) (hs n) / 2) atTop
      (𝓝 (∫ x, klFun (h x) ∂haar d + ∫ x, h x * V x ∂haar d + Aform W h h / 2)) := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hC0 : 0 ≤ C := (hs0 0 0).trans (hsC 0 0)
  have h0 : ∀ x, 0 ≤ h x := fun x => ge_of_tendsto' (hlim x) fun n => hs0 n x
  have hC' : ∀ x, h x ≤ C := fun x => le_of_tendsto' (hlim x) fun n => hsC n x
  have hab : ∀ n x, |hs n x| ≤ C := fun n x => by rw [abs_of_nonneg (hs0 n x)]; exact hsC n x
  -- `klFun` term
  have t1 : Tendsto (fun n => ∫ x, klFun (hs n x) ∂haar d) atTop (𝓝 (∫ x, klFun (h x) ∂haar d)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (C + 1) ^ 2)
      (fun n => (measurable_klFun.comp (hsm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x =>
        (continuous_klFun.tendsto _).comp (hlim x))
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hs0 n x))]
    exact klFun_le_bound (hs0 n x) (hsC n x)
  have t2 : Tendsto (fun n => ∫ x, hs n x * V x ∂haar d) atTop (𝓝 (∫ x, h x * V x ∂haar d)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C * BV)
      (fun n => ((hsm n).mul hyp.continuous_V.measurable).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x =>
        (hlim x).mul_const _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hab n x) (hBV x) (abs_nonneg _) hC0
  have hcb : ∀ {k : Torus d → ℝ}, (∀ y, |k y| ≤ C) → ∀ x, |convDens W k x| ≤ BW * C := by
    intro k hk x
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |W x y * k y| ∂haar d ≤ ∫ _y, BW * C ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => by
              show |W x y * k y| ≤ BW * C
              rw [abs_mul]
              exact mul_le_mul (hBW (x, y)) (hk y) (abs_nonneg _)
                ((abs_nonneg _).trans (hBW (x, y))))
      _ = BW * C := by simp
  have tc : ∀ x, Tendsto (fun n => convDens W (hs n) x) atTop (𝓝 (convDens W h x)) := fun x => by
    refine tendsto_integral_of_dominated_convergence (fun _ => BW * C)
      (fun n => ((hyp.continuous_W.measurable.comp measurable_prodMk_left).mul
        (hsm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y =>
        (hlim y).const_mul _)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBW (x, y)) (hab n y) (abs_nonneg _) ((abs_nonneg _).trans (hBW (x, y)))
  have t3 : Tendsto (fun n => Aform W (hs n) (hs n)) atTop (𝓝 (Aform W h h)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C * (BW * C))
      (fun n => ((hsm n).mul (measurable_convDens hyp (hsm n))).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hlim x).mul (tc x))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hab n x) (hcb (hab n) x) (abs_nonneg _) hC0
  exact (t1.add t2).add (t3.div_const 2)

end conv

section w1
variable (hyp : Hyp V W KV KW)
include hyp

/-- The `W^{1,∞}` distance between two Euler–Lagrange densities. -/
theorem w1infDist_el_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ (h₁ h₂ : Torus d → ℝ), Measurable h₁ → Measurable h₂ →
    (∀ x, 0 ≤ h₁ x) → (∀ x, 0 ≤ h₂ x) → ∫ x, h₁ x ∂haar d = 1 → ∫ x, h₂ x ∂haar d = 1 →
    ∀ {C ε : ℝ}, 0 ≤ ε → (∀ x, elDens V W (densMeasure h₂) x ≤ C) →
    (∀ᵐ x ∂haar d, |elDens V W (densMeasure h₁) x - elDens V W (densMeasure h₂) x| ≤ ε) →
    w1infDist (elDens V W (densMeasure h₁)) (elDens V W (densMeasure h₂)) ≤
      ENNReal.ofReal ε + ENNReal.ofReal (K * (ε + C * ∫ x, |h₁ x - h₂ x| ∂haar d)) := by
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  set K1 : ℝ := (Real.toNNReal (KV * Fintype.card (Fin d) / 2) : ℝ)
  have hK1 : 0 ≤ K1 := NNReal.coe_nonneg _
  have hCb0 : 0 ≤ |Cb| := abs_nonneg _
  refine ⟨Real.sqrt d * (K1 + |Cb|), by positivity, ?_⟩
  intro h₁ h₂ hm₁ hm₂ h0₁ h0₂ h1₁ h1₂ C ε hε hC hdist
  have hi₁ := integrable_of_integral_eq_one' h1₁
  have hi₂ := integrable_of_integral_eq_one' h1₂
  set p₁ := elDens V W (densMeasure h₁)
  set p₂ := elDens V W (densMeasure h₂)
  have hw := (isWeakGrad_elDensity hyp hm₁ h0₁ h1₁).add ((isWeakGrad_elDensity hyp hm₂ h0₂ h1₂).cmul (-1))
  have hw' : IsWeakGrad (fun y => p₁ y - p₂ y) (fun y k =>
      -p₁ y * (lipGrad V y k + bForceL W h₁ y k) + -1 * (-p₂ y * (lipGrad V y k + bForceL W h₂ y k))) := by
    convert hw using 1; funext y; ring
  have hae := weakGrad_ae_eq hw'
  set D := ∫ x, |h₁ x - h₂ x| ∂haar d
  have hβ : ∀ y k, |bForceL W h₁ y k - bForceL W h₂ y k| ≤ |Cb| * D := fun y k => by
    unfold bForceL
    have i : ∀ {h : Torus d → ℝ}, Integrable h (haar d) →
        Integrable (fun z => bGrad W y z k * h z) (haar d) := fun {h} hi =>
      Integrable.mono' (hi.abs.const_mul Cb) ((measurable_bGrad hyp (W := W) k).of_uncurry_left
        |>.aestronglyMeasurable.mul hi.aestronglyMeasurable) (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_right (hCb y z k) (abs_nonneg _))
    rw [← integral_sub (i hi₁) (i hi₂)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |bGrad W y z k * h₁ z - bGrad W y z k * h₂ z| ∂haar d
        ≤ ∫ z, |Cb| * |h₁ z - h₂ z| ∂haar d := integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) ((hi₁.sub hi₂).abs.const_mul _)
          (Eventually.of_forall fun z => by
            show |bGrad W y z k * h₁ z - bGrad W y z k * h₂ z| ≤ |Cb| * |h₁ z - h₂ z|
            rw [← mul_sub, abs_mul]
            exact mul_le_mul_of_nonneg_right ((hCb y z k).trans (le_abs_self _)) (abs_nonneg _))
      _ = |Cb| * D := integral_const_mul _ _
  have hβ1 : ∀ y k, |lipGrad V y k + bForceL W h₁ y k| ≤ K1 + |Cb| := fun y k => by
    refine (abs_add_le _ _).trans (add_le_add (abs_lipGrad_le (lipschitz_V hyp) y k) ?_)
    unfold bForceL
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |bGrad W y z k * h₁ z| ∂haar d ≤ ∫ z, |Cb| * h₁ z ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (hi₁.const_mul _)
            (Eventually.of_forall fun z => by
              show |bGrad W y z k * h₁ z| ≤ |Cb| * h₁ z
              rw [abs_mul, abs_of_nonneg (h0₁ z)]
              exact mul_le_mul_of_nonneg_right ((hCb y z k).trans (le_abs_self _)) (h0₁ z))
      _ = |Cb| := by rw [integral_const_mul, h1₁, mul_one]
  obtain ⟨c0, -, -, -, hb⟩ := elDensity_bounds hyp
  have hp₂0 : ∀ y, 0 ≤ p₂ y := fun y => by
    haveI := isProbabilityMeasure_densMeasure' h0₂ h1₂
    obtain ⟨c, C', L, hc, hall⟩ := elDensity_bounds hyp
    exact hc.le.trans ((hall _ inferInstance).1 y).1
  have hD0 : 0 ≤ D := integral_nonneg fun _ => abs_nonneg _
  have hC0 : 0 ≤ C := (hp₂0 0).trans (hC 0)
  have hAS1 : AEStronglyMeasurable (fun x => p₁ x - p₂ x) volume := hw'.aestronglyMeasurable_fun
  have hAS2 : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (weakGrad (fun y => p₁ y - p₂ y) x)))
      volume := Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad ⟨_, hw'⟩).aestronglyMeasurable_sqNorm
  unfold w1infDist
  refine add_le_add ?_ ?_
  · rw [eLpNorm_exponent_top hAS1]
    exact eLpNormEssSup_le_of_ae_bound (hdist.mono fun x hx => by rwa [Real.norm_eq_abs])
  · rw [eLpNorm_exponent_top hAS2]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [hae, hdist] with y hy hdy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy]
    set M := ε * (K1 + |Cb|) + C * (|Cb| * D)
    have hk : ∀ k, |-p₁ y * (lipGrad V y k + bForceL W h₁ y k) +
        -1 * (-p₂ y * (lipGrad V y k + bForceL W h₂ y k))| ≤ M := fun k => by
      have e : -p₁ y * (lipGrad V y k + bForceL W h₁ y k) +
          -1 * (-p₂ y * (lipGrad V y k + bForceL W h₂ y k)) =
          -((p₁ y - p₂ y) * (lipGrad V y k + bForceL W h₁ y k)) -
            p₂ y * (bForceL W h₁ y k - bForceL W h₂ y k) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_neg, abs_mul]
        exact mul_le_mul hdy (hβ1 y k) (abs_nonneg _) hε
      · rw [abs_mul, abs_of_nonneg (hp₂0 y)]
        exact mul_le_mul (hC y) (hβ y k) (abs_nonneg _) hC0
    have hM0 : 0 ≤ M := by positivity
    have hsq : sqNorm (fun k => -p₁ y * (lipGrad V y k + bForceL W h₁ y k) +
        -1 * (-p₂ y * (lipGrad V y k + bForceL W h₂ y k))) ≤ d * M ^ 2 := by
      unfold sqNorm
      calc _ ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hk k) 2
        _ = d * M ^ 2 := by simp
    calc Real.sqrt _ ≤ Real.sqrt (d * M ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt d * M := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM0]
      _ ≤ Real.sqrt d * (K1 + |Cb|) * (ε + C * D) := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
          have : C * (|Cb| * D) ≤ (K1 + |Cb|) * (C * D) := by
            nlinarith [mul_nonneg hC0 hD0, mul_nonneg hK1 (mul_nonneg hC0 hD0)]
          nlinarith [mul_nonneg hε hK1]

end w1

section main
variable (hyp : Hyp V W KV KW)
include hyp

theorem elDensity_props (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Measurable (elDens V W μ) ∧ (∀ x, 0 < elDens V W μ x) ∧
      ∫ x, elDens V W μ x ∂haar d = 1 := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  obtain ⟨hbd, hL⟩ := hb μ inferInstance
  refine ⟨hL.continuous.measurable, fun x => hc.trans_le (hbd x).1, ?_⟩
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  set Φ : Torus d → ℝ := fun x => V x + convMeas W μ x with hΦ
  have hΦb : ∀ x, |Φ x| ≤ BV + BW := fun x => abs_potential_le hBV (fun x y => hBW (x, y)) μ x
  have hΦm : Measurable Φ := hyp.continuous_V.measurable.add
    ((hyp.continuous_W.measurable.stronglyMeasurable.integral_prod_right (ν := μ)
      (f := fun x y => W x y)).measurable)
  have hei : Integrable (fun y => exp (-Φ y)) (haar d) :=
    integrable_of_bdd (measurable_exp.comp hΦm.neg) (C := exp (BV + BW)) fun y => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (by linarith [neg_le_abs (Φ y), hΦb y])
  have hZ := integral_exp_pos hei
  have e : ∀ x, elDens V W μ x = exp (-Φ x) / ∫ y, exp (-Φ y) ∂haar d := fun x => by
    simp only [elDens, hΦ, neg_add']
  simp_rw [e]
  rw [integral_div, div_self hZ.ne']

/-- **Compactness**: minimizer densities have a `W^{1,∞}`-convergent subsequence whose limit is
again a minimizer density. -/
theorem minimizers_compact (μs : ℕ → ProbabilityMeasure (Torus d))
    (hmin : ∀ n, IsMinimizer V W (μs n)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ ∧
      Tendsto (fun n => w1infDist (elDens V W (μs (φ n))) (elDens V W μ)) atTop (𝓝 0) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  set p : ℕ → Torus d → ℝ := fun n => elDens V W (μs n) with hpdef
  have hpb : ∀ n x, c ≤ p n x ∧ p n x ≤ C := fun n => (hb _ inferInstance).1
  have hpL : ∀ n, LipschitzWith L (p n) := fun n => (hb _ inferInstance).2
  have hpp : ∀ n, Measurable (p n) ∧ (∀ x, 0 < p n x) ∧ ∫ x, p n x ∂haar d = 1 := fun n =>
    elDensity_props hyp _
  have hEL : ∀ n, (μs n : Measure (Torus d)) = densMeasure (p n) := fun n =>
    minimizer_eq_elDensity hyp (hmin n)
  obtain ⟨φ, hφ, v, hv, hunif⟩ := exists_subseq_unif p (C := C) (fun n x => by
    rw [abs_of_pos ((hpp n).2.1 x)]; exact (hpb n x).2) hpL
  have hlim : ∀ x, Tendsto (fun n => p (φ n) x) atTop (𝓝 (v x)) := fun x => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (ε / 2) (by positivity))
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; linarith [hN n hn x]⟩
  have hv0 : ∀ x, c ≤ v x := fun x => ge_of_tendsto' (hlim x) fun n => (hpb _ x).1
  have hvC : ∀ x, v x ≤ C := fun x => le_of_tendsto' (hlim x) fun n => (hpb _ x).2
  have hvp : ∀ x, 0 ≤ v x := fun x => hc.le.trans (hv0 x)
  have hvm : Measurable v := hv.measurable
  have hv1 : ∫ x, v x ∂haar d = 1 := by
    have t := tendsto_integral_of_dominated_convergence (μ := haar d) (fun _ => C)
      (fun n => (hpp (φ n)).1.aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos ((hpp _).2.1 x)]; exact (hpb _ x).2)
      (Eventually.of_forall hlim)
    simp_rw [fun n => (hpp (φ n)).2.2] at t
    exact tendsto_nhds_unique t tendsto_const_nhds
  haveI hvP := isProbabilityMeasure_densMeasure' hvp hv1
  set μ : ProbabilityMeasure (Torus d) := ⟨densMeasure v, hvP⟩ with hμdef
  -- the limit is a minimizer
  have hK : ∀ {h : Torus d → ℝ}, Measurable h → (∀ x, 0 ≤ h x) → (∀ x, h x ≤ C) →
      Integrable (fun x => klFun (h x)) (haar d) := fun {h} hm h0 hC =>
    integrable_of_bdd (measurable_klFun.comp hm) (C := (C + 1) ^ 2) fun x => by
      rw [abs_of_nonneg (klFun_nonneg (h0 x))]; exact klFun_le_bound (h0 x) (hC x)
  set E : (Torus d → ℝ) → ℝ := fun h => ∫ x, klFun (h x) ∂haar d + ∫ x, h x * V x ∂haar d +
    Aform W h h / 2 with hE
  have hFp : ∀ n, freeEnergy V W (μs n) = ((E (p n) : ℝ) : EReal) := fun n => by
    rw [hEL n]
    exact freeEnergy_densMeasure hyp (hpp n).1 (fun x => ((hpp n).2.1 x).le) (hpp n).2.2
      (hK (hpp n).1 (fun x => ((hpp n).2.1 x).le) fun x => (hpb n x).2)
  have hEc : ∀ n, E (p n) = E (p 0) := fun n => by
    have h1 := hFp n
    have h2 := hFp 0
    rw [show freeEnergy V W (μs n) = Fstar V W from hmin n] at h1
    rw [show freeEnergy V W (μs 0) = Fstar V W from hmin 0] at h2
    exact EReal.coe_injective (h1.symm.trans h2)
  have hEv : E v = E (p 0) := by
    have t := tendsto_energy hyp (hs := fun n => p (φ n)) (fun n => (hpp _).1) hvm
      (fun n x => ((hpp _).2.1 x).le) (fun n x => (hpb _ x).2) hlim
    simp_rw [show ∀ n, ∫ x, klFun (p (φ n) x) ∂haar d + ∫ x, p (φ n) x * V x ∂haar d +
      Aform W (p (φ n)) (p (φ n)) / 2 = E (p 0) from fun n => hEc (φ n)] at t
    exact tendsto_nhds_unique tendsto_const_nhds t |>.symm
  have hμmin : IsMinimizer V W μ := by
    unfold IsMinimizer
    rw [← hmin 0, hFp 0, ← hEv]
    exact freeEnergy_densMeasure hyp hvm hvp hv1 (hK hvm hvp hvC)
  refine ⟨φ, hφ, μ, hμmin, ?_⟩
  -- `W^{1,∞}` convergence
  have hELμ := minimizer_eq_elDensity hyp hμmin
  have hpμ := elDensity_props hyp (μ : Measure (Torus d))
  have hae : elDens V W μ =ᵐ[haar d] v := by
    have h : densMeasure (elDens V W μ) = densMeasure v := hELμ.symm
    unfold densMeasure at h
    rw [withDensity_eq_iff (f := fun x => ENNReal.ofReal (elDens V W μ x))
      (g := fun x => ENNReal.ofReal (v x)) (ENNReal.measurable_ofReal.comp hpμ.1).aemeasurable
      (ENNReal.measurable_ofReal.comp hvm).aemeasurable (by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one' hpμ.2.2)
          (Eventually.of_forall fun x => (hpμ.2.1 x).le)]; exact ENNReal.ofReal_ne_top)] at h
    filter_upwards [h] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hpμ.2.1 x).le (hvp x)).mp hx
  obtain ⟨K, hK0, hw⟩ := w1infDist_el_le hyp
  have hpn : ∀ n, elDens V W (μs n) = elDens V W (densMeasure (p n)) := fun n => by
    rw [← hEL n]
  have hμv : elDens V W μ = elDens V W (densMeasure v) := rfl
  have hCμ : ∀ x, elDens V W (densMeasure v) x ≤ C := fun x => ((hb _ hvP).1 x).2
  rw [ENNReal.tendsto_nhds_zero]
  intro a ha
  rcases eq_or_ne a ⊤ with rfl | hat
  · exact Eventually.of_forall fun _ => le_top
  set A := a.toReal
  have hA : 0 < A := ENNReal.toReal_pos ha.ne' hat
  set ε := A / (1 + K * (1 + C)) with hεdef
  have hC0 : 0 ≤ C := hc.le.trans (hpb 0 0).1 |>.trans (hpb 0 0).2
  have hden : 0 < 1 + K * (1 + C) := by positivity
  have hε : 0 < ε := div_pos hA hden
  filter_upwards [hunif ε hε] with n hn
  have hdist : ∀ᵐ x ∂haar d, |elDens V W (densMeasure (p (φ n))) x -
      elDens V W (densMeasure v) x| ≤ ε := by
    filter_upwards [hae] with x hx
    rw [← hpn, ← hμv, hx]; exact hn x
  have hint : ∫ x, |p (φ n) x - v x| ∂haar d ≤ ε := by
    calc ∫ x, |p (φ n) x - v x| ∂haar d ≤ ∫ _x, ε ∂haar d :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall hn)
      _ = ε := by simp
  have := hw (p (φ n)) v (hpp _).1 hvm (fun x => ((hpp _).2.1 x).le) hvp (hpp _).2.2 hv1 hε.le
    hCμ hdist
  rw [hpn, hμv]
  refine this.trans ?_
  rw [← ENNReal.ofReal_add hε.le (by positivity), ← ENNReal.ofReal_toReal hat]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ε + K * (ε + C * ∫ x, |p (φ n) x - v x| ∂haar d) ≤ ε + K * (ε + C * ε) := by
        gcongr
    _ = ε * (1 + K * (1 + C)) := by ring
    _ = A := by rw [hεdef]; field_simp

end main

end SharpLSI
