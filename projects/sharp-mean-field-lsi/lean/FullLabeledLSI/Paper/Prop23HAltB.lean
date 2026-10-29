import FullLabeledLSI.Paper.Prop23FAltB
import FullLabeledLSI.Paper.Prop23GAltB
import FullLabeledLSI.Paper.Prop23HAltA
import FullLabeledLSI.Statements.S23_Lemma_6_1
import FullLabeledLSI.Statements.S25_Prop_6_3
import SharpSymmetricLSI.Statements.R27_Lemma_6_1

/-!
# Proposition 2.3, WP-H (alt): the core theorem

`propBoundedCore_alt : PropBoundedCore V W (bRate μ lam C)`: combine `(reduce-J)` (WP-F), the `J`-cut
(WP-G) and Proposition 6.3 (S25) exactly as in the proof of Proposition 2.3 (Section 7.5):
fix `ε`, choose `R ≥ max (R₁, R₀)`, then `t` and the level `L`; Proposition 6.3 applied to
`F_{N,t,L}` gives `liminf 𝒥(F) ≥ 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Conversion of the real inequality to the `ℝ≥0∞` form used in `PropBoundedCore`. -/
theorem ha_conv {b E Ent : ℝ≥0∞} {ε : ℝ} (hb : b ≠ ⊤) (hE : E ≠ ⊤) (hEnt : Ent ≠ ⊤)
    (hε : 0 ≤ ε) (h : b.toReal / 2 * Ent.toReal ≤ E.toReal + ε) :
    b / 2 * Ent ≤ E + ENNReal.ofReal ε := by
  have h2 : b / 2 ≠ ⊤ := by
    rw [div_eq_mul_inv]
    exact ENNReal.mul_ne_top hb (ENNReal.inv_ne_top.2 two_ne_zero)
  have h1 : b / 2 * Ent ≠ ⊤ := ENNReal.mul_ne_top h2 hEnt
  rw [← ENNReal.ofReal_toReal h1, ← ENNReal.ofReal_toReal hE,
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_div]
  simpa using h

/-- **WP-H**: the `N`-indexed core theorem of Proposition 2.3. -/
theorem propBoundedCore_alt (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ)
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W (μ : Measure (Torus d)) e) C) :
    PropBoundedCore V W (bRate (μ : Measure (Torus d)) lam C) := by
  intro f hf hBex ε hε
  obtain ⟨B, hB⟩ := hBex
  -- the data of the assembly
  obtain ⟨eC, hφ, heC⟩ := exists_C1_rep hd hyp hr μ hμ e lam he
  obtain ⟨A⟩ := exists_finiteRankApprox hd hyp hr hμ he
  obtain ⟨CR, hCR⟩ := exists_CR hd hyp hr μ hμ e lam he A
  obtain ⟨Q, hQ⟩ := exists_secondChaos_Tmat hyp hμ he
  obtain ⟨hKN, hK0, -, -⟩ := gaussian_limit_law hd hyp hr hμ he hQ hC
  obtain ⟨hU, hκ, -, hbR⟩ := rank_errors hd hyp hr μ hμ e lam he C hC Q hQ A CR hCR
  have hbtop : bRate (μ : Measure (Torus d)) lam C ≠ ⊤ :=
    ((Jexpr_terms_finite hd hyp hr μ hμ e lam he).1 C).ne
  have hb0 : 0 ≤ (bRate (μ : Measure (Torus d)) lam C).toReal := ENNReal.toReal_nonneg
  have hbRr : Tendsto (fun R => (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) atTop
      (𝓝 (bRate (μ : Measure (Torus d)) lam C).toReal) :=
    (ENNReal.tendsto_toReal hbtop).comp hbR
  have hε3 : 0 < ε / 3 := by positivity
  -- (reduce-J) and Proposition 6.3
  obtain ⟨R₁, hR₁⟩ := reduce_J_alt hd hyp hr hμ he hφ heC A CR hK0 hKN hκ hU hb0 hbRr f hf B hB
    (ε / 3) hε3
  obtain ⟨R₀, hR₀⟩ := spectral_comparison hd hyp hr μ hμ e lam he A CR hCR
  set R : ℕ := max R₁ R₀ with hRdef
  have hRa : R ≥ R₁ := le_max_left _ _
  have hRb : R₀ ≤ R := le_max_right _ _
  -- bounds on the ground-state transforms
  obtain ⟨p, Cg, hp, hCg, hG⟩ := ground_transform_nosym hd hyp hr hμ
  set M1 : ℝ := 2 * (B : ℝ) + Cg * (B : ℝ) ^ 2 with hM1
  set M2 : ℝ := Cg * (B : ℝ) ^ (2 * p) with hM2
  have hM10 : 0 ≤ M1 := by
    rw [hM1]; exact add_nonneg (by positivity) (mul_nonneg hCg (sq_nonneg _))
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; exact mul_nonneg hCg (Real.rpow_nonneg B.coe_nonneg _)
  have hΨ : ∀ N : ℕ, 1 ≤ N →
      MemH1C (QN (μ : Measure (Torus d)) N) (psiG W (μ : Measure (Torus d)) N (f N)) ∧
      refEnergy (μ : Measure (Torus d)) (psiG W (μ : Measure (Torus d)) N (f N)) ≤
        ENNReal.ofReal M1 ∧
      ∫⁻ X, ENNReal.ofReal (|psiG W (μ : Measure (Torus d)) N (f N) X| ^ (2 * p))
        ∂QN (μ : Measure (Torus d)) N ≤ ENNReal.ofReal M2 := by
    intro N hN
    obtain ⟨h1, -, h3, h4⟩ := hG N hN (f N) (B : ℝ) (hf N) (hB N).1
    refine ⟨h1, ?_, h4⟩
    have hB' : energy V W N (f N) ≤ ENNReal.ofReal (B : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]; exact (hB N).2
    calc refEnergy (μ : Measure (Torus d)) (psiG W (μ : Measure (Torus d)) N (f N))
        ≤ 2 * energy V W N (f N) + ENNReal.ofReal (Cg * (B : ℝ) ^ 2) := h3
      _ ≤ 2 * ENNReal.ofReal (B : ℝ) + ENNReal.ofReal (Cg * (B : ℝ) ^ 2) := by gcongr
      _ = ENNReal.ofReal M1 := by
        rw [hM1, ENNReal.ofReal_add (by positivity) (mul_nonneg hCg (sq_nonneg _)),
          ENNReal.ofReal_mul (p := 2) (by norm_num)]
        simp
  -- the `J`-cut
  obtain ⟨t, ht, L₀, hcut⟩ := J_cut_alt hd hyp hr hμ he hφ heC A CR R hp hM10 hM20 (ε / 3) hε3
  set L : ℝ := L₀ with hL
  set F : (N : ℕ) → Config N d → ℝ := fun N =>
    if 1 ≤ N then Spectral.Fcut (μ : Measure (Torus d)) e lam t L (psiG W (μ : Measure (Torus d)) N (f N))
    else fun _ => 0 with hFdef
  have hFpos : ∀ N : ℕ, 1 ≤ N →
      F N = Spectral.Fcut (μ : Measure (Torus d)) e lam t L
        (psiG W (μ : Measure (Torus d)) N (f N)) := fun N hN => by simp [hFdef, hN]
  have hrange : ∀ N, InSpectralRange e lam L (F N) := by
    intro N
    by_cases hN : 1 ≤ N
    · rw [hFpos N hN]
      obtain ⟨h1, h2, h3⟩ := hΨ N hN
      exact (hcut L le_rfl N hN _ h1 h2 h3).1
    · have : F N = fun _ => 0 := by simp [hFdef, hN]
      rw [this]
      exact ⟨∅, fun _ => 0, by simp, by simp⟩
  have hbnd : ∃ B' : ℝ, ∀ N, eLpNorm (F N) 2
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal B' := by
    refine ⟨M2 ^ (1 / (2 * p)), fun N => ?_⟩
    by_cases hN : 1 ≤ N
    · rw [hFpos N hN]
      obtain ⟨h1, h2, h3⟩ := hΨ N hN
      exact (hcut L le_rfl N hN _ h1 h2 h3).2.1
    · have : F N = fun _ => 0 := by simp [hFdef, hN]
      rw [this]
      simp
  have hS25 := hR₀ R hRb L F hrange hbnd (ε / 3) hε3
  have hF1 := hR₁ R hRa
  have hfin : ∀ᶠ N in atTop, (bRate (μ : Measure (Torus d)) lam C).toReal / 2 *
      (ent (gibbs V W N) (fun X => f N X ^ 2)).toReal ≤ (energy V W N (f N)).toReal + ε := by
    filter_upwards [hS25, hF1, eventually_ge_atTop 1] with N h1 h2 hN
    obtain ⟨g1, g2, g3⟩ := hΨ N hN
    have h3 := (hcut L le_rfl N hN _ g1 g2 g3).2.2
    rw [← hFpos N hN] at h3
    linarith
  filter_upwards [hfin] with N hN
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  refine ha_conv hbtop ?_ (ent_sq_lt_top_aux hyp (hf N)).ne hε.le hN
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hB N).2

end SharpLSI.FL
