import FullLabeledLSI.Paper.Prop23ReplaceA

/-! # Prop 2.3 WP-D(b): replacement in the energy -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### D(b): replacement in the energy -/

section DB

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! #### Auxiliary lemmas -/

/-- Local `IsWeakGrad.sub`. -/
theorem isWeakGrad_sub_loc {ι : Type*} [Fintype ι] [DecidableEq ι] {f₁ f₂ : UnitAddTorus ι → ℝ}
    {g₁ g₂ : UnitAddTorus ι → ι → ℝ} (h₁ : IsWeakGrad f₁ g₁) (h₂ : IsWeakGrad f₂ g₂) :
    IsWeakGrad (fun y => f₁ y - f₂ y) (fun y k => g₁ y k - g₂ y k) := by
  have := h₁.add (h₂.cmul (-1))
  simpa [sub_eq_add_neg] using this

/-- `weakGradC (U₁ - U₂) = weakGradC U₁ - weakGradC U₂` `Q_N`-a.e. -/
theorem weakGradC_sub_ae {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ) {N : ℕ} {U₁ U₂ : Config N d → ℝ}
    (h₁ : HasWeakGrad (U₁ ∘ unflat)) (h₂ : HasWeakGrad (U₂ ∘ unflat)) :
    ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ i k,
      weakGradC (fun Y => U₁ Y - U₂ Y) X i k = weakGradC U₁ X i k - weakGradC U₂ X i k := by
  have hD : IsWeakGrad ((fun Y => U₁ Y - U₂ Y) ∘ unflat)
      (fun y k => weakGrad (U₁ ∘ unflat) y k - weakGrad (U₂ ∘ unflat) y k) :=
    isWeakGrad_sub_loc (isWeakGrad_weakGrad h₁) (isWeakGrad_weakGrad h₂)
  have h := weakGrad_ae_eq hD
  filter_upwards [ae_pi_of_ae_volume hyp hμ h] with X hX i k
  have := congrFun hX (i, k)
  exact this

theorem aesm_fun_QN {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ) {N : ℕ} {u : Config N d → ℝ} (hu : HasWeakGrad (u ∘ unflat)) :
    AEStronglyMeasurable u (QN (μ : Measure (Torus d)) N) :=
  aestronglyMeasurable_comp_flat hyp hμ (G := u ∘ unflat)
    (isWeakGrad_weakGrad hu).aestronglyMeasurable_fun

theorem aesm_grad_QN {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ) {N : ℕ} {u : Config N d → ℝ} (hu : HasWeakGrad (u ∘ unflat))
    (i : Fin N) (k : Fin d) :
    AEStronglyMeasurable (fun X => weakGradC u X i k) (QN (μ : Measure (Torus d)) N) :=
  aestronglyMeasurable_comp_flat hyp hμ (G := fun y => weakGrad (u ∘ unflat) y (i, k))
    ((isWeakGrad_weakGrad hu).aestronglyMeasurable_grad (i, k))

/-- Euclidean triangle inequality (squared form) over a finite index set. -/
theorem sum_sq_add_le_loc {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    ∑ i, (a i + b i) ^ 2 ≤ (Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)) ^ 2 := by
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have cs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have e : ∑ i, (a i + b i) ^ 2 = ∑ i, a i ^ 2 + 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    have : ∀ i, (a i + b i) ^ 2 = a i ^ 2 + 2 * (a i * b i) + b i ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  nlinarith [cs]

theorem dsum_sq_add_le_loc {m n : ℕ} (a b : Fin m → Fin n → ℝ) :
    ∑ i, ∑ k, (a i k + b i k) ^ 2 ≤
      (Real.sqrt (∑ i, ∑ k, a i k ^ 2) + Real.sqrt (∑ i, ∑ k, b i k ^ 2)) ^ 2 := by
  have := sum_sq_add_le_loc (ι := Fin m × Fin n) (fun p => a p.1 p.2) (fun p => b p.1 p.2)
  simpa [Fintype.sum_prod_type] using this

theorem aemeas_dsum_loc {α : Type*} [MeasurableSpace α] {ν : Measure α} {m n : ℕ}
    (a : α → Fin m → Fin n → ℝ) (ha : ∀ i k, AEStronglyMeasurable (fun x => a x i k) ν) :
    AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, a x i k ^ 2))) ν := by
  have h : AEStronglyMeasurable (fun x => ∑ i, ∑ k, a x i k ^ 2) ν :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun k _ => (ha i k).pow 2
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    (Real.continuous_sqrt.measurable.comp_aemeasurable h.aemeasurable)

/-- Minkowski in `ℓ²` (over the finite index `Fin m × Fin n`) inside a lintegral. -/
theorem lintegral_minkowski_dsum {α : Type*} [MeasurableSpace α] {ν : Measure α} {m n : ℕ}
    (a b : α → Fin m → Fin n → ℝ)
    (ha : ∀ i k, AEStronglyMeasurable (fun x => a x i k) ν)
    (hb : ∀ i k, AEStronglyMeasurable (fun x => b x i k) ν) :
    (∫⁻ x, ENNReal.ofReal (∑ i, ∑ k, (a x i k + b x i k) ^ 2) ∂ν) ^ (1 / 2 : ℝ) ≤
      (∫⁻ x, ENNReal.ofReal (∑ i, ∑ k, a x i k ^ 2) ∂ν) ^ (1 / 2 : ℝ) +
        (∫⁻ x, ENNReal.ofReal (∑ i, ∑ k, b x i k ^ 2) ∂ν) ^ (1 / 2 : ℝ) := by
  have hFm := aemeas_dsum_loc a ha
  have hGm := aemeas_dsum_loc b hb
  have hM := ENNReal.lintegral_Lp_add_le (μ := ν) hFm hGm (p := 2) (by norm_num)
  simp only [Pi.add_apply] at hM
  have hsq : ∀ (c : α → Fin m → Fin n → ℝ) (x : α),
      (ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, c x i k ^ 2))) ^ (2 : ℝ) =
        ENNReal.ofReal (∑ i, ∑ k, c x i k ^ 2) := by
    intro c x
    have hS : 0 ≤ ∑ i, ∑ k, c x i k ^ 2 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hS]
  have hpt : ∀ x, ENNReal.ofReal (∑ i, ∑ k, (a x i k + b x i k) ^ 2) ≤
      (ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, a x i k ^ 2)) +
        ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, b x i k ^ 2))) ^ (2 : ℝ) := by
    intro x
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (dsum_sq_add_le_loc _ _)
  calc (∫⁻ x, ENNReal.ofReal (∑ i, ∑ k, (a x i k + b x i k) ^ 2) ∂ν) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x, (ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, a x i k ^ 2)) +
        ENNReal.ofReal (Real.sqrt (∑ i, ∑ k, b x i k ^ 2))) ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ ≤ _ := by
        simp only [hsq] at hM
        exact hM

/-- Pointwise algebra: the `b`-term. -/
theorem sum_half_mul_sq_loc {m n : ℕ} (c : ℝ) (u v : Fin m → Fin n → ℝ) :
    ∑ i, ∑ k, (1 / 2 * c * (u i k - v i k)) ^ 2 =
      1 / 4 * c ^ 2 * ∑ i, ∑ k, (u i k - v i k) ^ 2 := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **D(a''')**: `U_{N,R}` has a weak gradient (the form needed by `shEn_rpow_half_le`), obtained
from `exists_c1_reps` (ForceApprox4:26) and `isWeakGrad_URN`. -/
theorem hasWeakGrad_URN
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    HasWeakGrad (URN A R N ∘ unflat) := by
  obtain ⟨eC, hc⟩ := exists_c1_reps hd hyp hr hμ he
  exact ⟨_, isWeakGrad_URN A (fun j => (hc j).1) (fun j => (hc j).2.1) R hN⟩

/-- Core of `shEn_rpow_half_le` (one direction), with the difference function `D` abstract. -/
theorem shEn_rpow_half_le_aux {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ) {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) {B : ℝ} (hB : ∀ᵐ X ∂gibbs V W N, |f X| ≤ B)
    {U₁ U₂ D : Config N d → ℝ} (h₁ : HasWeakGrad (U₁ ∘ unflat)) (h₂ : HasWeakGrad (U₂ ∘ unflat))
    (hDq : ∀ᵐ X ∂QN (μ : Measure (Torus d)) N, ∀ i k,
      weakGradC D X i k ^ 2 = (weakGradC U₁ X i k - weakGradC U₂ X i k) ^ 2) :
    (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₁) ^ (1 / 2 : ℝ) ≤
        (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₂) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (B / 2) *
            (∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂gibbs V W N) ^ (1 / 2 : ℝ) := by
  have := gibbs_isProbabilityMeasure hyp N
  have hK := centeredPartition_pos hyp (μ : Measure (Torus d)) N
  have hB0 : 0 ≤ B := by
    obtain ⟨X, hX⟩ := hB.exists
    exact (abs_nonneg _).trans hX
  have hΨ : HasWeakGrad (psiG W μ N f ∘ unflat) := ⟨_, isWeakGrad_psi hyp hμ hN hf⟩
  set Ψ := psiG W μ N f with hΨdef
  have mΨ : AEStronglyMeasurable Ψ (QN (μ : Measure (Torus d)) N) := aesm_fun_QN hyp hμ hΨ
  have hmain : (shEn (μ : Measure (Torus d)) Ψ U₁) =
      ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k,
        ((weakGradC Ψ X i k + 1 / 2 * Ψ X * weakGradC U₂ X i k) +
          (1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k))) ^ 2) ∂QN (μ : Measure (Torus d)) N := by
    unfold shEn
    refine lintegral_congr fun X => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    congr 1; ring
  have mink := lintegral_minkowski_dsum (ν := QN (μ : Measure (Torus d)) N)
    (fun X i k => weakGradC Ψ X i k + 1 / 2 * Ψ X * weakGradC U₂ X i k)
    (fun X i k => 1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k))
    (fun i k => (aesm_grad_QN hyp hμ hΨ i k).add
      ((mΨ.const_mul (1 / 2)).mul (aesm_grad_QN hyp hμ h₂ i k)))
    (fun i k => (mΨ.const_mul (1 / 2)).mul
      ((aesm_grad_QN hyp hμ h₁ i k).sub (aesm_grad_QN hyp hμ h₂ i k)))
  rw [hmain]
  refine mink.trans (add_le_add (le_of_eq rfl) ?_)
  -- the `b`-term
  have h1 : ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k,
        (1 / 2 * Ψ X * (weakGradC U₁ X i k - weakGradC U₂ X i k)) ^ 2) ∂QN (μ : Measure (Torus d)) N =
      ∫⁻ X, ENNReal.ofReal (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) *
        ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂QN (μ : Measure (Torus d)) N := by
    refine lintegral_congr_ae ?_
    filter_upwards [hDq] with X hX
    have hg : gradSqC D X = ∑ i, ∑ k, (weakGradC U₁ X i k - weakGradC U₂ X i k) ^ 2 := by
      unfold gradSqC
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hX i k
    have hΨ2 : Ψ X ^ 2 = f X ^ 2 * (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) := by
      simp only [hΨdef, psiG]
      rw [mul_pow, Real.sq_sqrt (div_nonneg (Real.exp_pos _).le hK.le)]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hK.le),
      sum_half_mul_sq_loc, hg, hΨ2]
    congr 1; ring
  have h3 : ∫⁻ X, ENNReal.ofReal (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) *
        ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂QN (μ : Measure (Torus d)) N =
      ∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂gibbs V W N :=
    (lintegral_gibbs_eq hyp hμ (fun X => ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X))).symm
  have h4 : ∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂gibbs V W N ≤
      ENNReal.ofReal ((B / 2) ^ 2) * ∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂gibbs V W N := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae (hB.mono fun X hX => ?_)
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hg0 : 0 ≤ gradSqC D X :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hf2 : f X ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hX 2
    have : 1 / 4 * f X ^ 2 ≤ (B / 2) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hg0
  rw [h1, h3]
  calc (∫⁻ X, ENNReal.ofReal (1 / 4 * f X ^ 2 * gradSqC D X) ∂gibbs V W N) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((B / 2) ^ 2) * ∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂gibbs V W N) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h4 (by norm_num)
    _ = ENNReal.ofReal (B / 2) * (∫⁻ X, ENNReal.ofReal (gradSqC D X) ∂gibbs V W N) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith)]

/-- **D(b1): Minkowski, `eq:energy-root-error`.**  For `f ∈ H¹(P_N)`, `|f| ≤ B` `P_N`-a.e., and two
functions `U₁ U₂` with weak gradients, with `Ψ = psiG W μ N f`:
`(∫|∇Ψ+½Ψ∇U₁|² dQ)^{1/2} ≤ (∫|∇Ψ+½Ψ∇U₂|² dQ)^{1/2} + (B/2)(∫|∇(U₁-U₂)|² dP_N)^{1/2}`, and
symmetrically.  (Both sides in `ℝ≥0∞`, so no finiteness is needed.)  `U₁ = Ucentered W μ N`,
`U₂ = URN A R N` is the application; for the former `HasWeakGrad` is `isWeakGrad_gsU`
(GroundT3:32), for the latter `hasWeakGrad_URN`.

Proof (about 80-110 lines):
1. `hΨ : IsWeakGrad (psiG … ∘ unflat) (gsPsiG …)` (`isWeakGrad_psi`, GroundT5:75) so
   `weakGradC Ψ` is `Q_N`-a.e.-measurable and `L²`; same for `U₁, U₂` via
   `aestronglyMeasurable_comp_flat` (GroundT6:46) and `IsWeakGrad.aestronglyMeasurable_grad`.
2. A.e. pointwise `weakGradC (U₁ - U₂) = weakGradC U₁ - weakGradC U₂` (`weakGrad_ae_unique` applied
   to the difference of weak gradients; needs a small `IsWeakGrad.sub`, cf. `isWeakGrad_finsetSum`
   in ForceApprox2), so `gradSqC (U₁-U₂) = ∑ (∂U₁ - ∂U₂)²` a.e.
3. Minkowski: `ENNReal.lintegral_Lp_add_le` (or `eLpNorm_add_le`) with exponent 2 for the vector
   fields `a = ∇Ψ + ½Ψ∇U₂`, `b = ½Ψ(∇U₁ - ∇U₂)` (use `∑ᵢₖ` as an `ℓ²`-norm; the cleanest way is
   `Finset.sum` over the product index `Fin N × Fin d` and Minkowski in `L²(Q × counting)`, or the
   triangle inequality in `EuclideanSpace`, or: Cauchy–Schwarz expansion `|a+b|² ≤ (|a|+|b|)²`).
4. `∫⁻ ofReal(Ψ² gradSqC(U₁-U₂)) dQ = ∫⁻ ofReal(f² gradSqC(…)) dP_N ≤ ofReal(B²) ∫⁻ ofReal(gradSqC …) dP_N`
   by `lintegral_gibbs_eq` (GroundT5:60) and `Ψ² = f² e^{-U_N}/K_N` (`Real.sq_sqrt`). -/
theorem shEn_rpow_half_le {μ : ProbabilityMeasure (Torus d)} (hyp : Hyp V W KV KW)
    (hμ : IsMinimizer V W μ) {N : ℕ} (hN : 1 ≤ N) {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) {B : ℝ} (hB : ∀ᵐ X ∂gibbs V W N, |f X| ≤ B)
    {U₁ U₂ : Config N d → ℝ} (h₁ : HasWeakGrad (U₁ ∘ unflat)) (h₂ : HasWeakGrad (U₂ ∘ unflat)) :
    (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₁) ^ (1 / 2 : ℝ) ≤
        (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₂) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (B / 2) *
            (∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => U₁ Y - U₂ Y) X) ∂gibbs V W N) ^ (1 / 2 : ℝ) ∧
      (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₂) ^ (1 / 2 : ℝ) ≤
        (shEn (μ : Measure (Torus d)) (psiG W μ N f) U₁) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (B / 2) *
            (∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => U₁ Y - U₂ Y) X) ∂gibbs V W N) ^ (1 / 2 : ℝ) := by
  have hsub := weakGradC_sub_ae hyp hμ h₁ h₂
  refine ⟨shEn_rpow_half_le_aux hyp hμ hN hf hB h₁ h₂ ?_,
    shEn_rpow_half_le_aux hyp hμ hN hf hB h₂ h₁ ?_⟩
  · filter_upwards [hsub] with X hX i k
    rw [hX i k]
  · filter_upwards [hsub] with X hX i k
    rw [hX i k]; ring

/-- **D(b2): the force approximation in the order of limits needed (R31 (7.12)).**
`lim_R limsup_N ∫ |∇(U_N - U_{N,R})|² dP_N = 0`, rephrased as: for every `ε` there is `R₁` such
that for `R ≥ R₁` the integral is `≤ ε` for all large `N`.

Proof (about 25 lines): `(force_approximation hd hyp hr hμ he A.approx).2` is
`Tendsto (fun R => limsup … ) atTop (𝓝 0)` for `KR R x y = ∑∑ a e e`, where `Ukernel (KR R) N` is
`URN A R N` by `URN_eq_Ukernel` (`funext`/`simp only`); extract `R₁` with `limsup < ofReal ε`
(`Tendsto.eventually_lt_const`/`eventually_atTop`), then `Filter.eventually_lt_of_limsup_lt`. -/
theorem force_error_eventually {μ : ProbabilityMeasure (Torus d)} (hd : 1 ≤ d)
    (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N in atTop,
      ∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => Ucentered W μ N Y - URN A R N Y) X) ∂gibbs V W N ≤
        ENNReal.ofReal ε := by
  intro ε hε
  have hlim := (force_approximation hd hyp hr hμ he A.approx).2
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hpos))
  refine ⟨R₁, fun R hR => ?_⟩
  have hev := Filter.eventually_lt_of_limsup_lt (hR₁ R hR)
  filter_upwards [hev] with N hN
  have hfun : (fun Y => Ucentered W μ N Y - URN A R N Y) = fun Y => Ucentered W μ N Y -
      Ukernel (fun x y => ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * e (i + 1) x * e (j + 1) y) N Y :=
    funext fun Y => by rw [URN_eq_Ukernel A R N Y]
  rw [hfun]
  exact hN.le

/-- Real-variable end of `energy_replace`. -/
theorem real_sq_diff_loc {r₁ r₂ s δ ε : ℝ} (h1 : 0 ≤ r₁) (h2 : 0 ≤ r₂) (hs : r₁ ≤ s) (hδ : 0 ≤ δ)
    (a : r₂ ≤ r₁ + δ) (b : r₁ ≤ r₂ + δ) (hε : δ * (2 * s + δ) ≤ ε) : |r₁ ^ 2 - r₂ ^ 2| ≤ ε := by
  have e : r₁ ^ 2 - r₂ ^ 2 = (r₁ - r₂) * (r₁ + r₂) := by ring
  rw [e, abs_mul, abs_of_nonneg (add_nonneg h1 h2)]
  have hab : |r₁ - r₂| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
  calc |r₁ - r₂| * (r₁ + r₂) ≤ δ * (2 * s + δ) :=
        mul_le_mul hab (by linarith) (add_nonneg h1 h2) hδ
    _ ≤ ε := hε

/-- Conversion of the `ℝ≥0∞` square-root inequality to reals. -/
theorem toReal_rpow_half_le_loc {x y : ℝ≥0∞} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : x ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) + ENNReal.ofReal δ) (hy : y ≠ ⊤) :
    Real.sqrt x.toReal ≤ Real.sqrt y.toReal + δ := by
  have hy' : y ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hy
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hy', ENNReal.ofReal_ne_top⟩) h
  rw [ENNReal.toReal_add hy' ENNReal.ofReal_ne_top, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hδ, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at this
  exact this

/-- **D(b3): the energy with `U_N` replaced by `U_{N,R}`** (plan D(b); the statement WP-F consumes).
For fixed `B, M`, every `ε > 0` admits `R₁` such that for `R ≥ R₁` and all large `N`, for all
`f ∈ H¹(P_N)` with `|f| ≤ B` (`P_N`-a.e.) and `shEn Ψ U_N ≤ M` (by WP-B this is `energy ≤ M`, and
in the application `M = B`, `energy ≤ B`):
`|shEn Ψ U_N - shEn Ψ U_{N,R}| ≤ ε` (toReal; both sides are finite by the proof).
Via the Schrödinger identity (E1) the second term equals
`∫|∇Ψ|² dQ + ∫ VNR Ψ² dQ`.

Proof (about 50 lines): `δ := (B/2)·(∫⁻ … dP_N)^{1/2}` is `≤ δ_ε` for `R ≥ R₁` and large `N`
(`force_error_eventually`, with `δ_ε` chosen so that `δ_ε (2√M + δ_ε) ≤ ε`).  From
`shEn_rpow_half_le` (both conjuncts; `h₁` from `isWeakGrad_gsU`, `h₂` from `hasWeakGrad_URN`):
`√x₂ ≤ √x₁ + δ ≤ √M + δ < ⊤`, `√x₁ ≤ √x₂ + δ`; so `|x₁ - x₂| = |√x₁ - √x₂| (√x₁ + √x₂) ≤ δ (2√M + δ)`
(convert with `ENNReal.toReal_rpow`, `Real.sqrt_eq_rpow`). -/
theorem energy_replace {μ : ProbabilityMeasure (Torus d)} (hd : 1 ≤ d)
    (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (B M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N in atTop, ∀ f : Config N d → ℝ,
      MemH1C (gibbs V W N) f → (∀ᵐ X ∂gibbs V W N, |f X| ≤ B) →
      shEn (μ : Measure (Torus d)) (psiG W μ N f) (Ucentered W μ N) ≤ ENNReal.ofReal M →
      |(shEn (μ : Measure (Torus d)) (psiG W μ N f) (Ucentered W μ N)).toReal -
          (shEn (μ : Measure (Torus d)) (psiG W μ N f) (URN A R N)).toReal| ≤ ε := by
  intro ε hε
  have hac := minimizer_ac hyp hμ
  set s : ℝ := Real.sqrt (max M 0) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set β : ℝ := max (B / 2) 0 with hβ
  have hβ0 : 0 ≤ β := le_max_right _ _
  set δ₀ : ℝ := min 1 (ε / (2 * s + 1)) with hδ₀
  have h2s : 0 < 2 * s + 1 := by linarith
  have hδ0 : 0 < δ₀ := lt_min one_pos (div_pos hε h2s)
  have hδε : δ₀ * (2 * s + δ₀) ≤ ε := by
    calc δ₀ * (2 * s + δ₀) ≤ δ₀ * (2 * s + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [min_le_left 1 (ε / (2 * s + 1))]) hδ0.le
      _ ≤ ε / (2 * s + 1) * (2 * s + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) h2s.le
      _ = ε := div_mul_cancel₀ _ h2s.ne'
  set η : ℝ := (δ₀ / (β + 1)) ^ 2 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨R₁, hR₁⟩ := force_error_eventually hd hyp hr hμ he A η hη0
  refine ⟨R₁, fun R hR => ?_⟩
  filter_upwards [hR₁ R hR, eventually_ge_atTop 1] with N hI hN f hf hB hM
  have h₁ : HasWeakGrad (Ucentered W (μ : Measure (Torus d)) N ∘ unflat) :=
    ⟨_, isWeakGrad_gsU hyp hac hN⟩
  have h₂ := hasWeakGrad_URN hd hyp hr hμ he A R hN
  obtain ⟨hA1, hA2⟩ := shEn_rpow_half_le hyp hμ hN hf hB h₁ h₂
  set x₁ := shEn (μ : Measure (Torus d)) (psiG W μ N f) (Ucentered W μ N) with hx₁
  set x₂ := shEn (μ : Measure (Torus d)) (psiG W μ N f) (URN A R N) with hx₂
  set I := ∫⁻ X, ENNReal.ofReal (gradSqC (fun Y => Ucentered W μ N Y - URN A R N Y) X)
    ∂gibbs V W N with hIdef
  have hδE : ENNReal.ofReal (B / 2) * I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal δ₀ := by
    have hI' : I ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (δ₀ / (β + 1)) := by
      calc I ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal η) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hI (by norm_num)
        _ = ENNReal.ofReal (δ₀ / (β + 1)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hη0.le (by norm_num), ← Real.sqrt_eq_rpow, hη,
              Real.sqrt_sq (by positivity)]
    calc ENNReal.ofReal (B / 2) * I ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal β * ENNReal.ofReal (δ₀ / (β + 1)) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hI'
      _ = ENNReal.ofReal (β * (δ₀ / (β + 1))) := (ENNReal.ofReal_mul hβ0).symm
      _ ≤ ENNReal.ofReal δ₀ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith
  have hx₁top : x₁ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hM
  have hA1' : x₁ ^ (1 / 2 : ℝ) ≤ x₂ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ := hA1.trans (add_le_add le_rfl hδE)
  have hA2' : x₂ ^ (1 / 2 : ℝ) ≤ x₁ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ := hA2.trans (add_le_add le_rfl hδE)
  have hx₂top : x₂ ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hA2'
    have : x₁ ^ (1 / 2 : ℝ) + ENNReal.ofReal δ₀ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) hx₁top, ENNReal.ofReal_ne_top⟩
    exact this (top_le_iff.1 hA2')
  have r1 := toReal_rpow_half_le_loc hδ0.le hA1' hx₂top
  have r2 := toReal_rpow_half_le_loc hδ0.le hA2' hx₁top
  have hx₁le : x₁.toReal ≤ max M 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM
    rwa [ENNReal.toReal_ofReal'] at this
  have hrs : Real.sqrt x₁.toReal ≤ s := Real.sqrt_le_sqrt hx₁le
  have key := real_sq_diff_loc (Real.sqrt_nonneg x₁.toReal) (Real.sqrt_nonneg x₂.toReal) hrs hδ0.le
    r2 r1 hδε
  rwa [Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg] at key

end DB

end SharpLSI.FL
