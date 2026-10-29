import DGPS.Particle.CenteredForceMoment

/-!
# Uniform force exponential moments and changed-measure error (LIP015)

For the LIP014 smoothing construction, the force `∇E_{N,R}` has the sub-Gaussian-type bound
`∫ exp(α |∇E_{N,R}|²) dQ_N ≤ 2 exp(1/16)` for `α = [8d(1 + M₁² + M₂²)]⁻¹`, uniformly in `N ≥ 1`
and `R`.  The proof conditions on `X_i` and applies Hoeffding (sub-Gaussian MGF) to each
coordinate, integrates a Gaussian to get `exp(s z²)`, then uses Jensen over coordinates and labels.

Changed-measure error: for `P_N ≪ Q_N` with `‖dP_N/dQ_N‖_{L^p} ≤ C` (`p > 1`), the integer exponent
`(m+1)/m ≤ p` is used with Hölder, Cauchy–Schwarz against the exponential moment, and the
factorial bound to interpolate with the exact second moment from LIP014, giving
`lim_R limsup_N ∫ |∇E_{N,R}|² dP_N = 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DGPS.Lipschitz.CenteredForceExponential

/-- The Gaussian integral `E exp(k g²) ≤ 2` for `0 ≤ k`, `2k ≤ 1/2`. -/
theorem lintegral_exp_sq_gaussian {k : ℝ} (hk2 : 2 * k ≤ 1 / 2) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (k * g ^ 2)) ∂(gaussianReal 0 1) ≤ ENNReal.ofReal 2 := by
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero _ hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (by fun_prop)]
  set b : ℝ := (1 - 2 * k) / 2 with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  have hfun : ∀ g : ℝ, (gaussianPDF 0 1 * fun g => ENNReal.ofReal (Real.exp (k * g ^ 2))) g =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-b * g ^ 2)) := by
    intro g
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    rw [hb]; ring
  simp_rw [hfun]
  have hint : Integrable (fun g : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-b * g ^ 2)) :=
    (integrable_exp_neg_mul_sq hbpos).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun g => by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_const_mul, integral_gaussian]
  have h1 : (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / b) =
      Real.sqrt (1 / (2 * b)) := by
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [h1]
  have h2 : (1 : ℝ) / 4 ≤ b := by rw [hb]; linarith
  have : 1 / (2 * b) ≤ 2 ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  calc Real.sqrt (1 / (2 * b)) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt this
    _ = 2 := Real.sqrt_sq (by norm_num)

/-- Gaussian trick: a variable with sub-Gaussian mgf has `E exp(s Z²) ≤ 2` when `s v ≤ 1/4`. -/
theorem lintegral_exp_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : Measurable Z) {v : ℝ}
    (hmgf : ∀ t : ℝ, ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Z ω)) ∂P ≤
      ENNReal.ofReal (Real.exp (v * t ^ 2 / 2)))
    {s : ℝ} (hs : 0 ≤ s) (hsv : s * v ≤ 1 / 4) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (s * Z ω ^ 2)) ∂P ≤ ENNReal.ofReal 2 := by
  have hpt : ∀ z : ℝ, ENNReal.ofReal (Real.exp (s * z ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (Real.exp ((Real.sqrt (2 * s) * z) * g)) ∂(gaussianReal 0 1) := by
    intro z
    have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (Real.sqrt (2 * s) * z)
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
      (ae_of_all _ fun g => (Real.exp_pos _).le)]
    unfold mgf at h
    rw [h]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
    ring_nf
  simp_rw [hpt]
  have hmeas : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp ((Real.sqrt (2 * s) * Z p.1) * p.2))) := by
    fun_prop
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (Real.exp ((Real.sqrt (2 * s) * Z ω) * g)) ∂P ∂(gaussianReal 0 1)
      ≤ ∫⁻ g, ENNReal.ofReal (Real.exp ((s * v) * g ^ 2)) ∂(gaussianReal 0 1) := by
        refine lintegral_mono fun g => ?_
        have h2 := hmgf (Real.sqrt (2 * s) * g)
        have e : ∀ ω, (Real.sqrt (2 * s) * Z ω) * g = (Real.sqrt (2 * s) * g) * Z ω := fun ω => by
          ring
        simp_rw [e]
        refine h2.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith
    _ ≤ ENNReal.ofReal 2 := lintegral_exp_sq_gaussian (by linarith)

/-- Hoeffding for a sum of `n` independent bounded centered variables. -/
theorem sum_lintegral_exp_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y, |f y| ≤ M) (hf0 : ∫ y, f y ∂μ = 0) (n : ℕ) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (t * ∑ k : Fin n, f (y k))) ∂(Measure.pi fun _ : Fin n => μ) ≤
      ENNReal.ofReal (Real.exp (((n : ℝ) * M ^ 2) * t ^ 2 / 2)) := by
  have hind := iIndepFun_pi (μ := fun _ : Fin n => μ) (X := fun _ : Fin n => f)
    (fun _ => hf.aemeasurable)
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin n)), HasSubgaussianMGF
      (fun y : Fin n → Ω => f (y k)) ((‖M - -M‖₊ / 2) ^ 2) (Measure.pi fun _ : Fin n => μ) := by
    intro k _
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (a := -M) (b := M)
      (hf.comp (measurable_pi_apply k)).aemeasurable
      (ae_of_all _ fun y => ⟨by have := hM (y k); rw [abs_le] at this; exact this.1,
        by have := hM (y k); rw [abs_le] at this; exact this.2⟩) ?_
    have h := integral_map (μ := Measure.pi fun _ : Fin n => μ)
      (measurable_pi_apply k).aemeasurable (f := f) hf.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin n => μ) k).map_eq] at h
    rw [← h]
    exact hf0
  have hS := HasSubgaussianMGF.sum_of_iIndepFun hind hsub
  have hint := hS.integrable_exp_mul t
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := hS.mgf_le t
  have e : ((∑ k : Fin n, (‖M - -M‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (n : ℝ) * M ^ 2 := by
    have : ‖M - -M‖ = 2 * M := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; ring
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, NNReal.coe_nsmul]
    push_cast
    rw [this, nsmul_eq_mul]
    ring
  rw [e] at h
  exact h

/-- Conditioning on the `i`-th coordinate of a product measure. -/
theorem lintegral_pi_succAbove {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} (i : Fin (n + 1)) {Φ : Ω → (Fin n → Ω) → ℝ≥0∞}
    (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ x : Fin (n + 1) → Ω, Φ (x i) (fun k => x (i.succAbove k)) ∂(Measure.pi fun _ => μ) =
      ∫⁻ a, ∫⁻ y, Φ a y ∂(Measure.pi fun _ : Fin n => μ) ∂μ := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have h := hmp.lintegral_comp hΦ
  rw [lintegral_prod _ hΦ.aemeasurable] at h
  exact h

/-- The conditional exponential moment of one force coordinate. -/
theorem cond_lintegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c : Ω → Ω → ℝ} (hcm : Measurable (Function.uncurry c)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x y, |c x y| ≤ M) (hc0 : ∀ᵐ a ∂μ, ∫ y, c a y ∂μ = 0)
    {h : Ω → ℝ} (hhm : Measurable h) {M2 : ℝ} (hM2 : ∀ x, |h x| ≤ M2)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin N) {s κ e0 : ℝ} (hs : 0 ≤ s)
    (hsn : s * (((N : ℝ) - 1) * M ^ 2) ≤ 1 / 4)
    (hκ : ∀ z w : ℝ, |w| ≤ M2 →
      κ * ((N : ℝ)⁻¹ * z + (2 * (N : ℝ))⁻¹ * w) ^ 2 ≤ s * z ^ 2 + e0) :
    ∫⁻ x : Fin N → Ω, ENNReal.ofReal (Real.exp (κ * ((N : ℝ)⁻¹ *
        ∑ j ∈ Finset.univ.erase i, c (x i) (x j) + (2 * (N : ℝ))⁻¹ * h (x i)) ^ 2))
        ∂(Measure.pi fun _ => μ) ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp e0) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hsum : ∀ x : Fin (n + 1) → Ω, ∑ j ∈ Finset.univ.erase i, c (x i) (x j) =
      ∑ k : Fin n, c (x i) (x (i.succAbove k)) := by
    intro x
    have h1 := Fin.sum_univ_succAbove (fun j => c (x i) (x j)) i
    have h2 := Finset.add_sum_erase Finset.univ (fun j => c (x i) (x j)) (Finset.mem_univ i)
    linarith
  set Φ : Ω → (Fin n → Ω) → ℝ≥0∞ := fun a y => ENNReal.ofReal (Real.exp (κ *
    (((n + 1 : ℕ) : ℝ)⁻¹ * ∑ k : Fin n, c a (y k) + (2 * ((n + 1 : ℕ) : ℝ))⁻¹ * h a) ^ 2)) with hΦ
  have hsm : Measurable fun p : Ω × (Fin n → Ω) => ∑ k : Fin n, c p.1 (p.2 k) :=
    Finset.measurable_sum _ fun k _ =>
      hcm.comp (measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd))
  have hΦm : Measurable (Function.uncurry Φ) := by
    have hhm' : Measurable fun p : Ω × (Fin n → Ω) => h p.1 := hhm.comp measurable_fst
    simp only [hΦ]
    fun_prop
  have e : (fun x : Fin (n + 1) → Ω => ENNReal.ofReal (Real.exp (κ * (((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ j ∈ Finset.univ.erase i, c (x i) (x j) + (2 * ((n + 1 : ℕ) : ℝ))⁻¹ * h (x i)) ^ 2))) =
      fun x => Φ (x i) (fun k => x (i.succAbove k)) := by
    funext x; rw [hsum x]
  rw [e, lintegral_pi_succAbove i hΦm]
  calc ∫⁻ a, ∫⁻ y, Φ a y ∂(Measure.pi fun _ : Fin n => μ) ∂μ
      ≤ ∫⁻ _a, ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp e0) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hc0] with a ha
        have hcb : Measurable (c a) := hcm.comp measurable_prodMk_left
        have hZ : Measurable fun y : Fin n → Ω => ∑ k : Fin n, c a (y k) :=
          Finset.measurable_sum _ fun k _ => hcb.comp (measurable_pi_apply k)
        calc ∫⁻ y, Φ a y ∂(Measure.pi fun _ : Fin n => μ)
            ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (s * (∑ k : Fin n, c a (y k)) ^ 2)) *
                ENNReal.ofReal (Real.exp e0) ∂(Measure.pi fun _ : Fin n => μ) := by
              refine lintegral_mono fun y => ?_
              simp only [hΦ]
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
              exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hκ _ _ (hM2 a)))
          _ = (∫⁻ y, ENNReal.ofReal (Real.exp (s * (∑ k : Fin n, c a (y k)) ^ 2))
                ∂(Measure.pi fun _ : Fin n => μ)) * ENNReal.ofReal (Real.exp e0) :=
              lintegral_mul_const _ (by fun_prop)
          _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp e0) := by
              refine mul_le_mul_left (lintegral_exp_sq_le (P := Measure.pi fun _ : Fin n => μ)
                (Z := fun y => ∑ k : Fin n, c a (y k)) hZ (v := (n : ℝ) * M ^ 2)
                (fun t => sum_lintegral_exp_le hcb hM0 (hM a) ha n t) hs ?_) _
              have : (((n + 1 : ℕ) : ℝ) - 1) = n := by push_cast; ring
              rw [this] at hsn
              exact hsn
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp e0) := by simp

/-- Jensen for the exponential over a finite index set. -/
theorem exp_sum_le {ι : Type*} [Fintype ι] [Nonempty ι] (r : ι → ℝ) :
    Real.exp (∑ i, r i) ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, Real.exp (Fintype.card ι * r i) := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ : ι => (Fintype.card ι : ℝ)⁻¹)
    (p := fun i => Fintype.card ι * r i) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hm.ne'])
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have e1 : ∑ i, (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * r i) = ∑ i, r i := by
    simp_rw [← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
  rw [e1, ← Finset.mul_sum] at h
  exact h

/-- The exponential moment of the squared force, in `lintegral` form (per `N ≥ 1`). -/
theorem exp_moment_core {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 0 < d) {B : Ω → Ω → EuclideanSpace ℝ (Fin d)} {g : Ω → EuclideanSpace ℝ (Fin d)}
    (hBm : Measurable (Function.uncurry B)) (hgm : Measurable g) {M1 M2 : ℝ}
    (hM10 : 0 ≤ M1) (hM1 : ∀ x y, ‖B x y‖ ≤ M1) (hM2 : ∀ x, ‖g x‖ ≤ M2)
    (hb0 : ∀ᵐ x ∂μ, ∫ y, B x y ∂μ = 0) {α : ℝ}
    (hα : α = (8 * (d : ℝ) * (1 + M1 ^ 2 + M2 ^ 2))⁻¹) {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ x : Fin N → Ω, ENNReal.ofReal (Real.exp (α *
      ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2)) ∂(Measure.pi fun _ => μ) ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (1 / 16)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set T : ℝ := 1 + M1 ^ 2 + M2 ^ 2 with hT
  have hT1 : 1 ≤ T := by nlinarith [sq_nonneg M1, sq_nonneg M2]
  have hα0 : 0 < α := by rw [hα]; positivity
  have hdα : (d : ℝ) * α = (8 * T)⁻¹ := by rw [hα]; field_simp
  -- coordinates
  set c : Fin d → Ω → Ω → ℝ := fun ℓ x y => B x y ℓ with hc
  set h : Fin d → Ω → ℝ := fun ℓ x => g x ℓ with hh
  have hcm : ∀ ℓ, Measurable (Function.uncurry (c ℓ)) := fun ℓ =>
    (EuclideanSpace.proj ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hBm
  have hhm : ∀ ℓ, Measurable (h ℓ) := fun ℓ =>
    (EuclideanSpace.proj ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hgm
  have hcb : ∀ ℓ x y, |c ℓ x y| ≤ M1 := fun ℓ x y =>
    ((Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le (B x y) ℓ)).trans (hM1 x y)
  have hhb : ∀ ℓ x, |h ℓ x| ≤ M2 := fun ℓ x =>
    ((Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le (g x) ℓ)).trans (hM2 x)
  have hc0 : ∀ ℓ, ∀ᵐ a ∂μ, ∫ y, c ℓ a y ∂μ = 0 := by
    intro ℓ
    filter_upwards [hb0] with a ha
    have hBa : Measurable fun y => B a y := hBm.comp (f := fun y : Ω => (a, y)) measurable_prodMk_left
    have hint : Integrable (fun y => B a y) μ :=
      Integrable.of_bound hBa.aestronglyMeasurable M1
        (ae_of_all _ fun y => by simpa using hM1 a y)
    have := (EuclideanSpace.proj ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm hint
    have h2 : ∫ y, c ℓ a y ∂μ = (∫ y, B a y ∂μ) ℓ := this
    rw [h2, ha]; rfl
  -- pointwise coordinate expansion
  set a : Fin d → Fin N → (Fin N → Ω) → ℝ := fun ℓ i x =>
    (N : ℝ)⁻¹ * ∑ j ∈ Finset.univ.erase i, c ℓ (x i) (x j) + (2 * (N : ℝ))⁻¹ * h ℓ (x i) with ha
  have hcoord : ∀ x i, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
      (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 = ∑ ℓ, a ℓ i x ^ 2 := by
    intro x i
    rw [EuclideanSpace.norm_sq_eq]
    simp [ha, hc, hh]
  have hpt : ∀ x : Fin N → Ω, Real.exp (α * ∑ i : Fin N, ‖(N : ℝ)⁻¹ •
      ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2) ≤
      ((N : ℝ) * d)⁻¹ * ∑ p : Fin N × Fin d,
        Real.exp (((N : ℝ) * d * α) * a p.2 p.1 x ^ 2) := by
    intro x
    have e : α * ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 = ∑ p : Fin N × Fin d, α * a p.2 p.1 x ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcoord, Finset.mul_sum]
    rw [e]
    have := exp_sum_le (fun p : Fin N × Fin d => α * a p.2 p.1 x ^ 2)
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1; ring
  -- the constants
  set s : ℝ := 2 * (d : ℝ) * α / N with hs
  set e0 : ℝ := (d : ℝ) * α * M2 ^ 2 / 2 with he0
  have hdα0 : 0 < (d : ℝ) * α := by positivity
  have hs0 : 0 ≤ s := by positivity
  have hM1T : M1 ^ 2 ≤ T := by rw [hT]; nlinarith [sq_nonneg M2]
  have hM2T : M2 ^ 2 ≤ T := by rw [hT]; nlinarith [sq_nonneg M1]
  have hTpos : 0 < T := by linarith
  have hsn : s * (((N : ℝ) - 1) * M1 ^ 2) ≤ 1 / 4 := by
    have e : s * (((N : ℝ) - 1) * M1 ^ 2) = (2 * ((d : ℝ) * α)) * M1 ^ 2 * (((N : ℝ) - 1) / N) := by
      rw [hs]; field_simp
    rw [e, hdα]
    have h1 : ((N : ℝ) - 1) / N ≤ 1 := by
      rw [div_le_one hNpos]; linarith
    have h2 : 0 ≤ ((N : ℝ) - 1) / N := div_nonneg (by linarith) hNpos.le
    have h3 : (2 * (8 * T)⁻¹) * M1 ^ 2 ≤ 1 / 4 := by
      rw [show (2 * (8 * T)⁻¹) * M1 ^ 2 = M1 ^ 2 / (4 * T) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    calc (2 * (8 * T)⁻¹) * M1 ^ 2 * (((N : ℝ) - 1) / N)
        ≤ (2 * (8 * T)⁻¹) * M1 ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / 4 := by rw [mul_one]; exact h3
  have he0le : e0 ≤ 1 / 16 := by
    rw [he0, hdα, show (8 * T)⁻¹ * M2 ^ 2 / 2 = M2 ^ 2 / (16 * T) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hκ : ∀ z w : ℝ, |w| ≤ M2 →
      ((N : ℝ) * d * α) * ((N : ℝ)⁻¹ * z + (2 * (N : ℝ))⁻¹ * w) ^ 2 ≤ s * z ^ 2 + e0 := by
    intro z w hw
    have hw2 : w ^ 2 ≤ M2 ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg w) hw 2
      rwa [sq_abs] at this
    have h1 : ((N : ℝ)⁻¹ * z + (2 * (N : ℝ))⁻¹ * w) ^ 2 ≤
        2 * ((N : ℝ)⁻¹ * z) ^ 2 + 2 * ((2 * (N : ℝ))⁻¹ * w) ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ)⁻¹ * z - (2 * (N : ℝ))⁻¹ * w)]
    have hκ0 : 0 ≤ (N : ℝ) * d * α := by positivity
    have h2 : ((N : ℝ) * d * α) * (2 * ((N : ℝ)⁻¹ * z) ^ 2 + 2 * ((2 * (N : ℝ))⁻¹ * w) ^ 2) =
        s * z ^ 2 + ((d : ℝ) * α * w ^ 2 / 2) * (N : ℝ)⁻¹ := by
      rw [hs]; field_simp
    have hNi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    have h3 : ((d : ℝ) * α * w ^ 2 / 2) * (N : ℝ)⁻¹ ≤ e0 := by
      calc ((d : ℝ) * α * w ^ 2 / 2) * (N : ℝ)⁻¹ ≤ ((d : ℝ) * α * w ^ 2 / 2) * 1 :=
            mul_le_mul_of_nonneg_left hNi (by positivity)
        _ ≤ e0 := by
          rw [mul_one, he0]
          have := mul_le_mul_of_nonneg_left hw2 hdα0.le
          linarith
    calc ((N : ℝ) * d * α) * ((N : ℝ)⁻¹ * z + (2 * (N : ℝ))⁻¹ * w) ^ 2
        ≤ ((N : ℝ) * d * α) * (2 * ((N : ℝ)⁻¹ * z) ^ 2 + 2 * ((2 * (N : ℝ))⁻¹ * w) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hκ0
      _ ≤ s * z ^ 2 + e0 := by rw [h2]; linarith
  have hlint : ∀ p : Fin N × Fin d, ∫⁻ x : Fin N → Ω,
      ENNReal.ofReal (Real.exp (((N : ℝ) * d * α) * a p.2 p.1 x ^ 2)) ∂(Measure.pi fun _ => μ) ≤
      ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (1 / 16)) := by
    intro p
    refine (cond_lintegral (hcm p.2) hM10 (hcb p.2) (hc0 p.2) (hhm p.2) (hhb p.2) hN p.1 hs0 hsn
      hκ).trans ?_
    gcongr
  have haM : ∀ p : Fin N × Fin d, Measurable fun x : Fin N → Ω =>
      ENNReal.ofReal (Real.exp (((N : ℝ) * d * α) * a p.2 p.1 x ^ 2)) := by
    intro p
    have : Measurable fun x : Fin N → Ω => a p.2 p.1 x := by
      simp only [ha]
      refine Measurable.add (Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _)
        (Measurable.const_mul ((hhm p.2).comp (measurable_pi_apply p.1)) _)
      exact (hcm p.2).comp (f := fun x : Fin N → Ω => (x p.1, x j))
        ((measurable_pi_apply p.1).prodMk (measurable_pi_apply j))
    fun_prop
  calc ∫⁻ x : Fin N → Ω, ENNReal.ofReal (Real.exp (α * ∑ i : Fin N, ‖(N : ℝ)⁻¹ •
        ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2))
        ∂(Measure.pi fun _ => μ)
      ≤ ∫⁻ x : Fin N → Ω, ENNReal.ofReal (((N : ℝ) * d)⁻¹) * ∑ p : Fin N × Fin d,
          ENNReal.ofReal (Real.exp (((N : ℝ) * d * α) * a p.2 p.1 x ^ 2))
          ∂(Measure.pi fun _ => μ) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => (Real.exp_pos _).le),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (((N : ℝ) * d)⁻¹) * ∑ p : Fin N × Fin d, ∫⁻ x : Fin N → Ω,
          ENNReal.ofReal (Real.exp (((N : ℝ) * d * α) * a p.2 p.1 x ^ 2))
          ∂(Measure.pi fun _ => μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ (fun p _ => haM p)]
    _ ≤ ENNReal.ofReal (((N : ℝ) * d)⁻¹) * ∑ p : Fin N × Fin d,
          (ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (1 / 16))) :=
        by gcongr with p _; exact hlint p
    _ = ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (1 / 16)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity),
          ENNReal.ofReal_one, one_mul]

/-- Cauchy–Schwarz: `∫ S^{m+1} ≤ (∫ S)^{1/2} (∫ S^{2m+1})^{1/2}`. -/
theorem lintegral_pow_cs {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {S : Ω → ℝ}
    (hSm : Measurable S) (hS0 : ∀ x, 0 ≤ S x) (m : ℕ) :
    ∫⁻ x, ENNReal.ofReal (S x ^ (m + 1)) ∂Q ≤
      (∫⁻ x, ENNReal.ofReal (S x) ∂Q) ^ (1 / 2 : ℝ) *
        (∫⁻ x, ENNReal.ofReal (S x ^ (2 * m + 1)) ∂Q) ^ (1 / 2 : ℝ) := by
  have hf : Measurable fun x => ENNReal.ofReal (Real.sqrt (S x)) := by fun_prop
  have hg : Measurable fun x => ENNReal.ofReal (S x ^ m * Real.sqrt (S x)) := by fun_prop
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq Q Real.HolderConjugate.two_two hf.aemeasurable
    hg.aemeasurable
  have e1 : ∀ x, ENNReal.ofReal (Real.sqrt (S x)) *
      ENNReal.ofReal (S x ^ m * Real.sqrt (S x)) = ENNReal.ofReal (S x ^ (m + 1)) := by
    intro x
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    have := Real.mul_self_sqrt (hS0 x)
    calc Real.sqrt (S x) * (S x ^ m * Real.sqrt (S x))
        = S x ^ m * (Real.sqrt (S x) * Real.sqrt (S x)) := by ring
      _ = S x ^ (m + 1) := by rw [this]; ring
  have e2 : ∀ x, ENNReal.ofReal (Real.sqrt (S x)) ^ (2 : ℝ) = ENNReal.ofReal (S x) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    congr 1
    rw [Real.rpow_two, Real.sq_sqrt (hS0 x)]
  have e3 : ∀ x, ENNReal.ofReal (S x ^ m * Real.sqrt (S x)) ^ (2 : ℝ) =
      ENNReal.ofReal (S x ^ (2 * m + 1)) := by
    intro x
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (pow_nonneg (hS0 x) _) (Real.sqrt_nonneg _))
      (by norm_num)]
    congr 1
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hS0 x)]
    ring
  simp only [Pi.mul_apply, e1, e2, e3] at h
  exact h

/-- Changed-measure estimate: Hölder with `p₀ = (m+1)/m`, Cauchy–Schwarz, and the factorial bound. -/
theorem changed_measure_bound {Ω : Type*} [MeasurableSpace Ω] {Q P : Measure Ω}
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P] (hPQ : P ≪ Q) {S : Ω → ℝ}
    (hSm : Measurable S) (hS0 : ∀ x, 0 ≤ S x) {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA0 : 0 ≤ A)
    (hρ : ∫⁻ x, (P.rnDeriv Q x) ^ (((m : ℝ) + 1) / m) ∂Q ≤ ENNReal.ofReal A)
    {α K : ℝ} (hα : 0 < α) (hK0 : 0 ≤ K)
    (hK : ∫⁻ x, ENNReal.ofReal (Real.exp (α * S x)) ∂Q ≤ ENNReal.ofReal K) :
    ∫ x, S x ∂P ≤ (A ^ ((m : ℝ) / ((m : ℝ) + 1)) *
      (((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1) * K) ^ (1 / (2 * ((m : ℝ) + 1)))) *
        (∫ x, S x ∂Q) ^ (1 / (2 * ((m : ℝ) + 1))) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hHC : (((m : ℝ) + 1) / m).HolderConjugate ((m : ℝ) + 1) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hmpos]; linarith
    · field_simp
  set c : ℝ := ((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1) * K with hc
  have hc0 : 0 ≤ c := by positivity
  set I := ∫⁻ x, ENNReal.ofReal (S x) ∂Q with hI
  have hIle : I ≤ ENNReal.ofReal α⁻¹ * ENNReal.ofReal K := by
    calc I ≤ ∫⁻ x, ENNReal.ofReal α⁻¹ * ENNReal.ofReal (Real.exp (α * S x)) ∂Q := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have := Real.add_one_le_exp (α * S x)
          calc S x = α⁻¹ * (α * S x) := by field_simp
            _ ≤ α⁻¹ * Real.exp (α * S x) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ENNReal.ofReal α⁻¹ * ∫⁻ x, ENNReal.ofReal (Real.exp (α * S x)) ∂Q :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal α⁻¹ * ENNReal.ofReal K := by gcongr
  have hItop : I ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hIle
  have hSint : Integrable S Q :=
    (lintegral_ofReal_ne_top_iff_integrable hSm.aestronglyMeasurable (ae_of_all _ hS0)).1 hItop
  set x0 : ℝ := ∫ x, S x ∂Q with hx0def
  have hx0 : 0 ≤ x0 := integral_nonneg hS0
  have hIeq : I = ENNReal.ofReal x0 :=
    (ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ hS0)).symm
  have hJ : ∫⁻ x, ENNReal.ofReal (S x ^ (2 * m + 1)) ∂Q ≤ ENNReal.ofReal c := by
    calc ∫⁻ x, ENNReal.ofReal (S x ^ (2 * m + 1)) ∂Q
        ≤ ∫⁻ x, ENNReal.ofReal (((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1)) *
            ENNReal.ofReal (Real.exp (α * S x)) ∂Q := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 := Real.pow_div_factorial_le_exp (α * S x) (mul_nonneg hα.le (hS0 x)) (2 * m + 1)
          rw [mul_pow, div_le_iff₀ (by positivity)] at h1
          rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hα _)]
          linarith
      _ = ENNReal.ofReal (((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1)) *
            ∫⁻ x, ENNReal.ofReal (Real.exp (α * S x)) ∂Q :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (((2 * m + 1).factorial : ℝ) / α ^ (2 * m + 1)) * ENNReal.ofReal K := by
          gcongr
      _ = ENNReal.ofReal c := by rw [← ENNReal.ofReal_mul (by positivity)]
  have h1 : ∫⁻ x, ENNReal.ofReal (S x) ∂P = ∫⁻ x, P.rnDeriv Q x * ENNReal.ofReal (S x) ∂Q :=
    (lintegral_rnDeriv_mul hPQ hSm.ennreal_ofReal.aemeasurable).symm
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq Q hHC (f := fun x => P.rnDeriv Q x)
    (g := fun x => ENNReal.ofReal (S x)) (Measure.measurable_rnDeriv P Q).aemeasurable
    hSm.ennreal_ofReal.aemeasurable
  have h3 : ∫⁻ x, ENNReal.ofReal (S x) ^ ((m : ℝ) + 1) ∂Q =
      ∫⁻ x, ENNReal.ofReal (S x ^ (m + 1)) ∂Q := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (hS0 x) (by positivity)]
    congr 1
    have : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
  have h4 := lintegral_pow_cs (Q := Q) hSm hS0 m
  set r : ℝ := 1 / (2 * ((m : ℝ) + 1)) with hr
  have hL : ∫⁻ x, ENNReal.ofReal (S x) ∂P ≤
      ENNReal.ofReal (A ^ ((m : ℝ) / ((m : ℝ) + 1)) * c ^ r * x0 ^ r) := by
    rw [h1]
    refine h2.trans ?_
    simp only [Pi.mul_apply] at h2
    have hX : (∫⁻ x, (P.rnDeriv Q x) ^ (((m : ℝ) + 1) / m) ∂Q) ^ (1 / (((m : ℝ) + 1) / m)) ≤
        ENNReal.ofReal (A ^ ((m : ℝ) / ((m : ℝ) + 1))) := by
      rw [one_div_div, ← ENNReal.ofReal_rpow_of_nonneg hA0 (by positivity)]
      exact ENNReal.rpow_le_rpow hρ (by positivity)
    have hY : (∫⁻ x, ENNReal.ofReal (S x) ^ ((m : ℝ) + 1) ∂Q) ^ (1 / ((m : ℝ) + 1)) ≤
        (ENNReal.ofReal x0 ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ)) ^
          (1 / ((m : ℝ) + 1)) := by
      refine ENNReal.rpow_le_rpow ?_ (by positivity)
      rw [h3]
      refine h4.trans ?_
      rw [← hIeq]
      gcongr
    refine (mul_le_mul' hX hY).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg hx0 (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0, ← Real.rpow_mul hc0]
    have : 1 / 2 * (1 / ((m : ℝ) + 1)) = r := by rw [hr]; field_simp
    rw [this]; ring
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hS0) hSm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL

/-- A real exponential with finite `lintegral` bound is integrable, with the same bound. -/
theorem integrable_exp_of_lintegral {X : Type*} [MeasurableSpace X] {Q : Measure X} {f : X → ℝ}
    (hf : Measurable f) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂Q ≤ ENNReal.ofReal K) :
    Integrable (fun x => Real.exp (f x)) Q ∧ ∫ x, Real.exp (f x) ∂Q ≤ K := by
  refine ⟨?_, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable hf.exp.aestronglyMeasurable
      (ae_of_all _ fun x => (Real.exp_pos _).le)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hK)
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => (Real.exp_pos _).le)
      hf.exp.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hK0 hK

/-- Measurability of the squared force `∑ᵢ |∇ᵢE|²`. -/
theorem measurable_force_sq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {B : Ω → Ω → EuclideanSpace ℝ (Fin d)} {g : Ω → EuclideanSpace ℝ (Fin d)}
    (hBm : Measurable (Function.uncurry B)) (hgm : Measurable g) (N : ℕ) :
    Measurable fun x : Fin N → Ω => ∑ i : Fin N,
      ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) + (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 := by
  have hi : ∀ i : Fin N, Measurable fun x : Fin N → Ω =>
      ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 := by
    intro i
    have h1 : Measurable fun x : Fin N → Ω =>
        (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) := by
      have he : ∀ j : Fin N, Measurable fun x : Fin N → Ω => B (x i) (x j) := fun j =>
        hBm.comp (f := fun x : Fin N → Ω => (x i, x j))
          ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact (Finset.measurable_sum _ fun j _ => he j).const_smul ((N : ℝ)⁻¹)
    have hproj : Measurable fun x : Fin N → Ω => x i := measurable_pi_apply i
    have h2 : Measurable fun x : Fin N → Ω => (2 * (N : ℝ))⁻¹ • g (x i) :=
      (hgm.comp hproj).const_smul ((2 * (N : ℝ))⁻¹)
    exact (h1.add h2).norm.pow_const 2
  exact Finset.measurable_sum _ fun i _ => hi i

/-- For `p > 1` there is an integer `m ≥ 1` with `(m+1)/m ≤ p`. -/
theorem exists_nat_exponent {p : ℝ≥0∞} (hp : 1 < p) :
    ∃ m : ℕ, 1 ≤ m ∧ ENNReal.ofReal (((m : ℝ) + 1) / m) ≤ p := by
  rcases eq_or_ne p ⊤ with rfl | hpt
  · exact ⟨1, le_rfl, le_top⟩
  · have hp1 : 1 < p.toReal := by
      simpa using ENNReal.toReal_strict_mono hpt hp
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / (p.toReal - 1))
    have hpos : 0 < p.toReal - 1 := by linarith
    have hm0 : (0 : ℝ) < m := lt_trans (one_div_pos.2 hpos) hm
    refine ⟨m, Nat.cast_pos.1 hm0, ?_⟩
    rw [← ENNReal.ofReal_toReal hpt]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hm0]
    rw [div_lt_iff₀ (by linarith)] at hm
    nlinarith

/-- `L^p` control of the density `p_N = dP/dQ` gives a bound on `∫ p_N^{(m+1)/m} dQ`. -/
theorem rnDeriv_lintegral_le {Ω : Type*} [MeasurableSpace Ω] {Q P : Measure Ω}
    [IsProbabilityMeasure Q] [IsFiniteMeasure P] {p : ℝ≥0∞} {m : ℕ} (hm : 1 ≤ m)
    (hp : ENNReal.ofReal (((m : ℝ) + 1) / m) ≤ p) {C : ℝ≥0}
    (hC : eLpNorm (fun x => (P.rnDeriv Q x).toReal) p Q ≤ C) :
    ∫⁻ x, (P.rnDeriv Q x) ^ (((m : ℝ) + 1) / m) ∂Q ≤
      ENNReal.ofReal ((C : ℝ) ^ (((m : ℝ) + 1) / m)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := ((m : ℝ) + 1) / m with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hmeas : AEStronglyMeasurable (fun x => (P.rnDeriv Q x).toReal) Q :=
    (Measure.measurable_rnDeriv P Q).ennreal_toReal.aestronglyMeasurable
  have h1 : eLpNorm (fun x => (P.rnDeriv Q x).toReal) (ENNReal.ofReal q) Q ≤ C :=
    (eLpNorm_le_eLpNorm_of_exponent_le hp).trans hC
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hq0.le] at h1
  have h2 : ∫⁻ x, ‖(P.rnDeriv Q x).toReal‖ₑ ^ q ∂Q = ∫⁻ x, (P.rnDeriv Q x) ^ q ∂Q := by
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top P Q] with x hx
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  rw [h2] at h1
  have h3 := ENNReal.rpow_le_rpow h1 hq0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one] at h3
  refine h3.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_nonneg C.coe_nonneg hq0.le]

open Filter Topology

/-- The abstract limsup estimate: exponential moments under `Q_N`, the changed-measure Hölder
estimate with `p_N = dP_N/dQ_N ∈ L^p`, and the `Q_N`-limit `L_R → 0` give
`lim_R limsup_N ∫ S_{R,N} dP_N = 0`. -/
theorem limsup_changed_measure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (S : ℕ → (N : ℕ) → (Fin N → Ω) → ℝ)
    (hSm : ∀ R N, Measurable (S R N)) (hS0 : ∀ R N x, 0 ≤ S R N x)
    {α K : ℝ} (hα : 0 < α) (hK0 : 0 ≤ K)
    (hK : ∀ R N, 1 ≤ N → ∫⁻ x, ENNReal.ofReal (Real.exp (α * S R N x))
      ∂(Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal K)
    {L : ℕ → ℝ} (hL : Tendsto L atTop (𝓝 0))
    (hlim : ∀ R, Tendsto (fun N : ℕ => ∫ x, S R N x ∂(Measure.pi fun _ : Fin N => μ)) atTop
      (𝓝 (L R)))
    (P : (N : ℕ) → Measure (Fin N → Ω)) (hP : ∀ N, 1 ≤ N → IsProbabilityMeasure (P N))
    (hPQ : ∀ N, 1 ≤ N → P N ≪ Measure.pi fun _ : Fin N => μ) {p : ℝ≥0∞} (hp : 1 < p) {Cp : ℝ≥0}
    (hCp : ∀ N, 1 ≤ N → eLpNorm (fun x => ((P N).rnDeriv (Measure.pi fun _ : Fin N => μ) x).toReal)
      p (Measure.pi fun _ : Fin N => μ) ≤ Cp) :
    Tendsto (fun R : ℕ => limsup (fun N : ℕ => ∫ x, S R N x ∂(P N)) atTop) atTop (𝓝 0) := by
  obtain ⟨mm, hmm1, hmp⟩ := exists_nat_exponent hp
  set r : ℝ := 1 / (2 * ((mm : ℝ) + 1)) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set Ccst : ℝ := ((Cp : ℝ) ^ (((mm : ℝ) + 1) / mm)) ^ ((mm : ℝ) / ((mm : ℝ) + 1)) *
    ((((2 * mm + 1).factorial : ℝ) / α ^ (2 * mm + 1) * K) ^ r) with hCc
  have hbound : ∀ R N, 1 ≤ N → ∫ x, S R N x ∂(P N) ≤
      Ccst * (∫ x, S R N x ∂(Measure.pi fun _ : Fin N => μ)) ^ r := by
    intro R N hN
    have := hP N hN
    exact changed_measure_bound (Q := Measure.pi fun _ : Fin N => μ) (P := P N) (hPQ N hN)
      (hSm R N) (hS0 R N) hmm1 (Real.rpow_nonneg Cp.coe_nonneg _)
      (rnDeriv_lintegral_le hmm1 hmp (hCp N hN)) hα hK0 (hK R N hN)
  have hnn : ∀ R N, 0 ≤ ∫ x, S R N x ∂(P N) := fun R N => integral_nonneg (hS0 R N)
  have hlimv : ∀ R, Tendsto (fun N : ℕ => Ccst * (∫ x, S R N x ∂(Measure.pi fun _ : Fin N => μ)) ^ r)
      atTop (𝓝 (Ccst * L R ^ r)) := fun R =>
    ((hlim R).rpow_const (Or.inr hr0.le)).const_mul Ccst
  have hup : ∀ R, limsup (fun N : ℕ => ∫ x, S R N x ∂(P N)) atTop ≤ Ccst * L R ^ r := by
    intro R
    rw [← (hlimv R).limsup_eq]
    refine limsup_le_limsup ?_ (isCoboundedUnder_le_of_le atTop (hnn R))
      (hlimv R).isBoundedUnder_le
    filter_upwards [eventually_ge_atTop 1] with N hN using hbound R N hN
  have hlow : ∀ R, 0 ≤ limsup (fun N : ℕ => ∫ x, S R N x ∂(P N)) atTop := fun R =>
    le_limsup_of_frequently_le (Eventually.of_forall (hnn R)).frequently
      ((hlimv R).isBoundedUnder_le.mono_le
        ((eventually_ge_atTop 1).mono fun N hN => hbound R N hN))
  have hfin : Tendsto (fun R => Ccst * L R ^ r) atTop (𝓝 0) := by
    have := (hL.rpow_const (Or.inr hr0.le)).const_mul Ccst
    rwa [Real.zero_rpow hr0.ne', mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfin hlow hup

end DGPS.Lipschitz.CenteredForceExponential

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS DGPS.Lipschitz.KernelApproximation DGPS.Lipschitz.CenteredForceMoment
  DGPS.Lipschitz.CenteredKernelMoments DGPS.Lipschitz.CenteredForceExponential

/-- The force package of `CenteredForceMoment.force_package`, together with the Haar-a.e.
(hence `μ`-a.e.) centering `∫ ∇₁F(x,y) dμ(y) = 0` of the kernel gradient. -/
theorem force_package_centered {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hμ : ∀ P : Torus d → Prop, (∀ᵐ x ∂haar d, P x) → ∀ᵐ x ∂μ, P x)
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {g : Torus d → Tangent d}
    (hsymm : ∀ x y, F x y = F y x)
    (hFc : Continuous (Function.uncurry F)) (hBm : Measurable (Function.uncurry B))
    {M : ℝ} (hM : ∀ x y, ‖B x y‖ ≤ M) (hgm : Measurable g) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hw : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (hδ : IsWeakGradient (fun x => F x x) g)
    (h0 : ∀ x, ∫ y, F x y ∂μ = 0) :
    ((∀ N : ℕ+, IsParticleHaarWeakGradient N
      (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j, F (x i) (x j))
      (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i))) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∫ x : Fin N → Torus d, ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ((N : ℝ) - 1) / N * ∫ p, ‖B p.1 p.2‖ ^ 2 ∂μ.prod μ +
        (4 * (N : ℝ))⁻¹ * ∫ a, ‖g a‖ ^ 2 ∂μ) ∧
    ∀ᵐ x ∂μ, ∫ y, B x y ∂μ = 0 := by
  refine ⟨force_package hμ hsymm hFc hBm hM hgm hMg hw hδ h0, ?_⟩
  obtain ⟨CF, hCF⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    hFc.continuousOn
  have hF : ∀ x y, |F x y| ≤ CF := fun x y => by
    simpa [Real.norm_eq_abs] using hCF (x, y) (Set.mem_univ _)
  exact hμ _ (centered_gradient_ae hFc.measurable hBm hF hM hw h0)

/-- **Uniform force exponential moments and changed-measure error (LIP015).**

Take the spectral data `(S, A)`, kernel `K`, diagonal gradient `gK`, and the smoothing parameters
`(t, m)` of LIP014, with `∇₁F_R = G1 - smoothG1` and `∇δ_R = gK - (smoothG1 + smoothG2)(x,x)`.
Then `∇₁F_R` and `∇δ_R` are bounded uniformly in `R` (by some `M1`, `M2`), and for *any* uniform
bounds `M1`, `M2` and `α = [8d(1 + M1² + M2²)]⁻¹`:

* there is `K` with `∫ exp(α |∇E_{N,R}|²) dQ_N ≤ K` (and integrable) for all `N ≥ 1` and all `R`,
  where `Q_N = S.mu^{⊗N}` and `|∇E_{N,R}|² = ∑ᵢ |∇ᵢE_{N,R}|²`;
* if `P_N ≪ Q_N` are probability measures with `‖dP_N/dQ_N‖_{L^p(Q_N)} ≤ Cp` for some `p > 1`
  (`p = ∞` allowed) and all `N ≥ 1`, then `lim_R limsup_N ∫ |∇E_{N,R}|² dP_N = 0`. -/
theorem uniform_force_exponential_moments_and_changed_measure_error {d : ℕ}
    {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (S : Spec d) (A : Aux S), S.w = WeightedGenerator.gibbsW Φ ∧
      ∀ D : KData d, (∀ y, ∫ x, D.K x y ∂S.mu = 0) → (∀ x y, D.K x y = D.K y x) →
      ∀ gK : Torus d → Tangent d, Measurable gK → (∃ M : ℝ, ∀ x, ‖gK x‖ ≤ M) →
        IsWeakGradient (fun x => D.K x x) gK →
        ∃ (t : ℕ → ℝ) (m : ℕ → ℕ), (∀ R, 0 < t R) ∧ Antitone t ∧
          Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
          (∀ R (N : ℕ+), IsParticleHaarWeakGradient N
            (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j,
              (D.K (x i) (x j) - smoothK S D (t R) (m R) (x i) (x j)))
            (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
              (2 * (N : ℝ))⁻¹ • (gK (x i) -
                (smoothG1 S A D (t R) (m R) (x i) (x i) +
                  smoothG2 S A D (t R) (m R) (x i) (x i))))) ∧
          (∃ M1 M2 : ℝ,
            (∀ R x y, ‖D.G1 x y - smoothG1 S A D (t R) (m R) x y‖ ≤ M1) ∧
            (∀ R x, ‖gK x - (smoothG1 S A D (t R) (m R) x x +
              smoothG2 S A D (t R) (m R) x x)‖ ≤ M2)) ∧
          ∀ M1 M2 : ℝ,
            (∀ R x y, ‖D.G1 x y - smoothG1 S A D (t R) (m R) x y‖ ≤ M1) →
            (∀ R x, ‖gK x - (smoothG1 S A D (t R) (m R) x x +
              smoothG2 S A D (t R) (m R) x x)‖ ≤ M2) →
            ∀ α : ℝ, α = (8 * (d : ℝ) * (1 + M1 ^ 2 + M2 ^ 2))⁻¹ →
            (∃ K : ℝ, ∀ R (N : ℕ), 1 ≤ N →
              Integrable (fun x : Fin N → Torus d => Real.exp (α * ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2))
                (Measure.pi fun _ => S.mu) ∧
              ∫ x : Fin N → Torus d, Real.exp (α * ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2)
                ∂(Measure.pi fun _ => S.mu) ≤ K) ∧
            ∀ (P : (N : ℕ) → Measure (Fin N → Torus d)),
              (∀ N, 1 ≤ N → IsProbabilityMeasure (P N)) →
              (∀ N, 1 ≤ N → P N ≪ Measure.pi fun _ : Fin N => S.mu) →
              ∀ p : ℝ≥0∞, 1 < p → ∀ Cp : ℝ≥0,
              (∀ N, 1 ≤ N → eLpNorm (fun x => ((P N).rnDeriv
                (Measure.pi fun _ : Fin N => S.mu) x).toReal) p
                (Measure.pi fun _ : Fin N => S.mu) ≤ Cp) →
              Tendsto (fun R => limsup (fun N : ℕ =>
                ∫ x : Fin N → Torus d, ∑ i : Fin N,
                  ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                      (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                    (2 * (N : ℝ))⁻¹ • (gK (x i) -
                      (smoothG1 S A D (t R) (m R) (x i) (x i) +
                        smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                  ∂(P N)) atTop) atTop (𝓝 0) := by
  obtain ⟨S, A, hw, hrest⟩ := product_form_parseval_and_smoothed_finite_rank_kernels hd hL hΦ hb
  refine ⟨S, A, hw, fun D hc hsym gK hgm ⟨Mgk, hMgk⟩ hδK => ?_⟩
  obtain ⟨-, t, m, C, ht, hanti, htend, hm, hC, hK, hG1, hG2, -, -, -, hconv⟩ := hrest D hc hsym
  have : IsProbabilityMeasure S.mu := ⟨by
    have h := S.real_univ
    rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h⟩
  have hdiag : Measurable fun x : Torus d => (x, x) := measurable_id.prodMk measurable_id
  have hG1m : ∀ R, Measurable (Function.uncurry (smoothG1 S A D (t R) (m R))) := fun R => by
    rw [smoothG1_eq]; exact G1fin_meas S A D (t R) (m R + 1)
  have hG2m : ∀ R, Measurable (Function.uncurry (smoothG2 S A D (t R) (m R))) := fun R => by
    rw [smoothG2_eq]; exact G2fin_meas S A D (t R) (m R + 1)
  have hBm : ∀ R, Measurable (Function.uncurry fun x y =>
      D.G1 x y - smoothG1 S A D (t R) (m R) x y) := fun R => D.G1m.sub (hG1m R)
  have hgm' : ∀ R, Measurable fun x => gK x - (smoothG1 S A D (t R) (m R) x x +
      smoothG2 S A D (t R) (m R) x x) := fun R =>
    hgm.sub (((hG1m R).comp hdiag).add ((hG2m R).comp hdiag))
  have hBb : ∀ R x y, ‖D.G1 x y - smoothG1 S A D (t R) (m R) x y‖ ≤ D.B + C := fun R x y =>
    (norm_sub_le _ _).trans (add_le_add (D.G1b x y) (hG1 R x y))
  have hgb : ∀ R x, ‖gK x - (smoothG1 S A D (t R) (m R) x x +
      smoothG2 S A D (t R) (m R) x x)‖ ≤ Mgk + (C + C) := fun R x =>
    (norm_sub_le _ _).trans (add_le_add (hMgk x)
      ((norm_add_le _ _).trans (add_le_add (hG1 R x x) (hG2 R x x))))
  have hsymmR : ∀ R x y, D.K x y - smoothK S D (t R) (m R) x y =
      D.K y x - smoothK S D (t R) (m R) y x := fun R x y => by
    rw [hsym x y, smoothK_symm S D hsym _ _ x y]
  have hFc : ∀ R, Continuous (Function.uncurry fun x y =>
      D.K x y - smoothK S D (t R) (m R) x y) := fun R =>
    D.Kc.sub (smoothK_continuous S D _ _)
  have hwR : ∀ R y, IsWeakGradient (fun x => D.K x y - smoothK S D (t R) (m R) x y)
      (fun x => D.G1 x y - smoothG1 S A D (t R) (m R) x y) := fun R y => by
    refine wg_sub (D.g1 y) ?_
    have := Kfin_wg1 S A D (t R) (m R + 1) y
    simpa only [smoothK_eq, smoothG1_eq] using this
  have hδR : ∀ R, IsWeakGradient (fun x => D.K x x - smoothK S D (t R) (m R) x x)
      (fun x => gK x - (smoothG1 S A D (t R) (m R) x x +
        smoothG2 S A D (t R) (m R) x x)) := fun R =>
    wg_sub hδK (smoothK_diag_wg S A D _ _)
  have h0R : ∀ R x, ∫ y, (D.K x y - smoothK S D (t R) (m R) x y) ∂S.mu = 0 := fun R x => by
    have h1 : Integrable (fun y => D.K x y) S.mu :=
      S.int_cont (D.Kc.comp (continuous_const.prodMk continuous_id))
    have h2 : Integrable (fun y => smoothK S D (t R) (m R) x y) S.mu :=
      S.int_cont ((smoothK_continuous S D (t R) (m R)).comp
        (continuous_const.prodMk continuous_id))
    rw [integral_sub h1 h2]
    have e1 : ∫ y, D.K x y ∂S.mu = 0 := by
      simp_rw [hsym x]; exact hc x
    have e2 : ∫ y, smoothK S D (t R) (m R) x y ∂S.mu = 0 := by
      simp_rw [smoothK_symm S D hsym _ _ x]
      exact smoothK_centered S D A.v0 hc _ _ x
    rw [e1, e2, sub_zero]
  have key := fun R => force_package_centered (fun P h => S.ae_mu h) (hsymmR R) (hFc R) (hBm R)
    (hBb R) (hgm' R) (hgb R) (hwR R) (hδR R) (h0R R)
  have hb0 : Tendsto (fun R => ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2
      ∂S.mu.prod S.mu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun R => integral_nonneg fun p => sq_nonneg _) (fun R => ?_)
    have ha : 0 ≤ ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu :=
      integral_nonneg fun p => sq_nonneg _
    have hc2 : 0 ≤ ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2
        ∂S.mu.prod S.mu := integral_nonneg fun p => sq_nonneg _
    show _ ≤ _ + _ + _
    linarith
  have hlim := fun R => tendsto_of_identity (key R).1.2
  refine ⟨t, m, ht, hanti, htend, hm, fun R => (key R).1.1, ⟨D.B + C, Mgk + (C + C), hBb, hgb⟩,
    fun M1 M2 hM1 hM2 α hα => ?_⟩
  obtain ⟨x0⟩ : Nonempty (Torus d) := inferInstance
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0 x0 x0)
  have hαpos : 0 < α := by
    rw [hα]
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hKc : (0 : ℝ) ≤ 2 * Real.exp (1 / 16) := by positivity
  have hexp := fun R (N : ℕ) (hN : 1 ≤ N) =>
    (exp_moment_core hd (hBm R) (hgm' R) hM10 (hM1 R) (hM2 R) (key R).2 hα hN).trans
      (le_of_eq (ENNReal.ofReal_mul (by norm_num)).symm)
  refine ⟨⟨2 * Real.exp (1 / 16), fun R N hN => ?_⟩, ?_⟩
  · exact integrable_exp_of_lintegral
      ((measurable_force_sq (hBm R) (hgm' R) N).const_mul α) hKc (hexp R N hN)
  · intro P hP hPQ p hp Cp hCp
    refine limsup_changed_measure _ (fun R N => measurable_force_sq (hBm R) (hgm' R) N)
      (fun R N x => Finset.sum_nonneg fun i _ => sq_nonneg _) hαpos hKc
      (fun R N hN => ?_) hb0 (fun R => hlim R) P hP hPQ hp hCp
    exact hexp R N hN

end DGPS.Lipschitz
