import FullLabeledLSI.Paper.Hybrid63AltK

/-!
# Proposition 6.3: the `(7.21)` terms are small, uniformly in the coefficients
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem errT15_small (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) (hG : GoodBasis (μ : Measure (Torus d)) e')
    (hae : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j)
    (J : ℕ) (hJ : ∀ i ∈ A.s R, i < J) (L B τ : ℝ) (hτ : 0 < τ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N in atTop, ∀ c : (Fin N → Fin (J + 1)) → ℝ, SpectralCoeff lam L c → ∑ j, c j ^ 2 ≤ B ^ 2 →
      0 < lowCount c δ ∧ errT1 (μ : Measure (Torus d)) A lam R e' c δ ≤ τ ∧
        errT5 (μ : Measure (Torus d)) A R e' c δ ≤ τ := by
  obtain ⟨hlam0, hnn, hmono, hpos⟩ := lam_facts hd hyp hr hμ he
  have hmom' : HybridPolyMoment (μ : Measure (Torus d)) e' lam J :=
    (hybridPolyMoment_of_min hd hyp hr μ hμ e lam he J).of_ae_eq hae
  obtain ⟨Mq1, Kq1, hM1, hK1, H1⟩ := est721 hG hmom' hlam0 L B (A.s R) hJ (vQ A lam R)
  obtain ⟨Mq2, Kq2, hM2, hK2, H2⟩ := est721 hG hmom' hlam0 L B (A.s R) hJ
    (fun i j => A.a R i j / 2)
  set Cs1 : ℝ := ∑ i ∈ A.s R, ∑ j ∈ A.s R, |vQ A lam R i j| with hCs1
  set Cs2 : ℝ := ∑ i ∈ A.s R, ∑ j ∈ A.s R, |A.a R i j / 2| with hCs2
  have hC1 : 0 ≤ Cs1 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hC2 : 0 ≤ Cs2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set bmax : ℝ := max (L / lam 1) 0 * B ^ 2 / δ with hbmax
  obtain ⟨t1, ht1, N01, hN01⟩ := choose_t Cs1 Mq1 Kq1 bmax τ hC1 hM1 hK1 hτ
  obtain ⟨t2, ht2, N02, hN02⟩ := choose_t Cs2 Mq2 Kq2 bmax τ hC2 hM2 hK2 hτ
  refine eventually_atTop.2 ⟨max (max N01 N02) (⌈bmax⌉₊ + 1), fun N hN c hc hB => ?_⟩
  have hN1 : N01 ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N02 ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN3 : ⌈bmax⌉₊ + 1 ≤ N := (le_max_right _ _).trans hN
  have hlow := lowCount_lower hlam0 hnn hmono hpos hc hB hδ
  have hNb : bmax < N := by
    have : (⌈bmax⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN3
    linarith [Nat.le_ceil bmax]
  have hn : 0 < lowCount c δ := by
    have : (0 : ℝ) < lowCount c δ := by linarith
    exact_mod_cast this
  have hcard : ((retained c δ).card : ℝ) ≤ bmax := by
    have hle : (retained c δ).card ≤ N := by simpa using Finset.card_le_univ (retained c δ)
    have : ((retained c δ).card : ℝ) = N - lowCount c δ := by
      unfold lowCount; rw [Nat.cast_sub hle]; ring
    linarith
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by
    have : 0 ≤ bmax := by
      rw [hbmax]
      have : (0 : ℝ) ≤ max (L / lam 1) 0 := le_max_right _ _
      positivity
    exact this) hNb
  have hx0 : 0 ≤ ((retained c δ).card : ℝ) / N := by positivity
  have hxb : ((retained c δ).card : ℝ) / N ≤ bmax / N :=
    div_le_div_of_nonneg_right hcard hNpos.le
  refine ⟨hn, ?_, ?_⟩
  · unfold errT1
    rw [errT_eq_integral hG A R c δ (vQ A lam R)
      (-((1 / 2) * ∑ m ∈ A.s R, A.a R m m * lam (m + 1))) (vR A lam R)
      (fun y => by rw [vR_eq_quad]; ring)]
    exact (H1 N c hc hB δ hn t1 ht1).trans (hN01 N hN1 _ hx0 hxb)
  · unfold errT5
    rw [errT_eq_integral hG A R c δ (fun i j => A.a R i j / 2) 0 (uR A R)
      (fun y => by rw [uR_eq_quadA]; ring)]
    exact (H2 N c hc hB δ hn t2 ht2).trans (hN02 N hN2 _ hx0 hxb)

end

end SharpLSI.FL

end
