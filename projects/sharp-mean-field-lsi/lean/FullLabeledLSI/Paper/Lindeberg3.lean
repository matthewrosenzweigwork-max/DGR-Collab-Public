import FullLabeledLSI.Paper.Lindeberg2

/-!
# Lemma 7.1, part 4: the one-label Lindeberg step (Piece D)

For `Φ ∈ C_c^∞`, a low-influence label `i ∈ B`: replacing the torus coordinate of label `i` by its
Gaussian coordinate changes `IP … B` by at most
`C₁ (√Inf_i ^ 3 + (n^{-1/2}) ^ 3)`, with `C₁` independent of `N, c, δ, B, i`.
Inputs: `integral_pi_update` (resampling label `i`), `swap_affine` (second-order matching, third-order
remainder), and `HybridPolyMoment` (third moments of the coefficient polynomials).
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### Real-variable helpers -/

theorem cube_add_le (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) : (x + a) ^ 3 ≤ 4 * (x ^ 3 + a ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg hx ha) (sq_nonneg (x - a))]

theorem sum_cube_le {J : ℕ} (f : Fin J → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ r, f r) ^ 3 ≤ (J : ℝ) ^ 2 * ∑ r, f r ^ 3 := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ; simp
  · have h := pow_sum_le_card_mul_sum_pow (s := Finset.univ) (f := f) (fun r _ => hf r) 2
    simpa using h

/-- A lintegral bound for a nonnegative measurable function gives integrability and an integral bound. -/
theorem integrable_integral_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {P : Measure α}
    {f : α → ℝ} (hf : AEStronglyMeasurable f P) (hnn : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂P ≤ ENNReal.ofReal C) :
    Integrable f P ∧ ∫ x, f x ∂P ≤ C := by
  have hne : ∫⁻ x, ENNReal.ofReal (f x) ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hi : Integrable f P :=
    (lintegral_ofReal_ne_top_iff_integrable hf (Filter.Eventually.of_forall hnn)).1 hne
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn) hf]
  exact ENNReal.toReal_le_of_le_ofReal hC h

/-! ### Measurability of the label-wise objects -/

section meas

variable {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem measurable_lf (hG : GoodBasis μ e) {N J : ℕ} (B : Finset (Fin N)) (l : Fin N)
    (m : Fin (J + 1)) : Measurable (lf e B l m : Torus d × (Fin J → ℝ) → ℝ) := by
  unfold lf
  by_cases hl : l ∈ B
  · simp only [hl, ↓reduceIte]
    exact (hG.meas m).comp measurable_fst
  · simp only [hl, ↓reduceIte]
    by_cases hm : (m : ℕ) = 0
    · simp only [hm, ↓reduceDIte]; exact measurable_const
    · simp only [hm, ↓reduceDIte]
      exact (measurable_pi_apply _).comp measurable_snd

theorem measurable_polyF_lf (hG : GoodBasis μ e) {N J : ℕ} (B : Finset (Fin N))
    (c : (Fin N → Fin (J + 1)) → ℝ) :
    Measurable (fun ω : Fin N → Torus d × (Fin J → ℝ) => polyF (lf e B) c ω) := by
  unfold polyF
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  exact Finset.measurable_prod _ fun l _ => (measurable_lf hG B l (j l)).comp (measurable_pi_apply l)

theorem measurable_zP (hG : GoodBasis μ e) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (B : Finset (Fin N)) (m : Fin J) :
    Measurable (fun ω : Fin N → Torus d × (Fin J → ℝ) => zP e c δ B ω m) := by
  unfold zP
  refine measurable_const.mul (Finset.measurable_sum _ fun l _ => ?_)
  exact (measurable_lf hG B l m.succ).comp (measurable_pi_apply l)

theorem measurable_Fint (hG : GoodBasis μ e) {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : Continuous Φ) (B : Finset (Fin N)) :
    Measurable (Fint e c δ hJ Φ B : (Fin N → Torus d × (Fin J → ℝ)) → ℝ) := by
  unfold Fint
  refine hΦ.measurable.comp (Measurable.prodMk (measurable_polyF_lf hG B c) ?_)
  exact measurable_pi_iff.2 fun m => measurable_zP hG c δ B _

theorem Psi_continuous {N J JR : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J)
    {Φ : ℝ × (Fin JR → ℝ) → ℝ} (hΦ : Continuous Φ) (B : Finset (Fin N)) (i : Fin N)
    (ω : Fin N → Torus d × (Fin J → ℝ)) :
    Continuous (Psi e c δ hJ Φ B i ω) := by
  have : Psi e c δ hJ Φ B i ω = fun u => Φ ((bco e c B i 0 ω, fun r' : Fin JR =>
      Cz e c δ B i (Fin.castLE hJ r') ω) + Mlin hJ (fun r => bco e c B i r.succ ω)
      (Real.sqrt (lowCount c δ))⁻¹ u) := funext fun u => Psi_eq_affine c δ hJ Φ B i ω u
  rw [this]
  exact hΦ.comp (continuous_const.add (Mlin hJ _ _).continuous)

end meas

/-! ### Moments of the coefficient polynomials -/

section moments

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
  {J : ℕ}

/-- Third moment of the coefficient polynomial `b_{r+1}` of label `i`. -/
theorem bco_moment (hG : GoodBasis μ e) {Kh : ℝ} (hKh0 : 0 ≤ Kh) {L : ℝ}
    (hKh : ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c → ∫⁻ ω, ENNReal.ofReal (|polyB e c B ω| ^ 3) ∂hybMeasure μ N J ≤
        ENNReal.ofReal (Kh * Real.sqrt (∑ j, c j ^ 2) ^ 3))
    (hlam0 : lam 0 = 0) (hnn : ∀ k, 0 ≤ lam k) {N : ℕ} {c : (Fin N → Fin (J + 1)) → ℝ}
    (hc : SpectralCoeff lam L c) (B : Finset (Fin N)) (i : Fin N) (r : Fin J) :
    Integrable (fun ω => |bco e c B i r.succ ω| ^ 3) (pairMeasure μ N J) ∧
      ∫ ω, |bco e c B i r.succ ω| ^ 3 ∂pairMeasure μ N J ≤ Kh * Real.sqrt (infl c i) ^ 3 := by
  have hc' : SpectralCoeff lam L (cdrop c i r.succ) := spectralCoeff_cdrop hlam0 hnn hc i r.succ
  have h := hKh N B (cdrop c i r.succ) hc'
  rw [lintegral_hyb_eq] at h
  have hsq : Real.sqrt (∑ j, (cdrop c i r.succ j) ^ 2) ≤ Real.sqrt (infl c i) :=
    Real.sqrt_le_sqrt (sum_sq_cdrop_le_infl c i r.succ (Fin.succ_ne_zero r))
  have hC : Kh * Real.sqrt (∑ j, (cdrop c i r.succ j) ^ 2) ^ 3 ≤ Kh * Real.sqrt (infl c i) ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 3) hKh0
  have hmeas : Measurable fun ω : Fin N → Torus d × (Fin J → ℝ) => |bco e c B i r.succ ω| ^ 3 :=
    ((measurable_polyF_lf hG B _).abs).pow_const 3
  have h' : ∫⁻ ω, ENNReal.ofReal (|bco e c B i r.succ ω| ^ 3) ∂pairMeasure μ N J ≤
      ENNReal.ofReal (Kh * Real.sqrt (∑ j, (cdrop c i r.succ j) ^ 2) ^ 3) := h
  obtain ⟨hi, hI⟩ := integrable_integral_le_of_lintegral_le hmeas.aestronglyMeasurable
    (fun ω => by positivity) (by positivity) h'
  exact ⟨hi, hI.trans hC⟩

end moments

end SharpLSI.FL
