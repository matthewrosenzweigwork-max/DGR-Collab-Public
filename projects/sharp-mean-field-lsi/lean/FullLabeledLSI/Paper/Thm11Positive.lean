import FullLabeledLSI.Paper.Thm11PositiveA

/-!
# Theorem 1.1 (FL), positive limiting entropy is impossible

`positive_contra_all`: along a violating sequence with `h_N → h > 0` and `ℰ_N → E`, the bounded
comparison (Proposition 2.3, in the form `hcomp` for the truncations `f_N ∧ M`) and the defective
inequality contradict `2ℰ(f_N) < r h_N`. The limit object of the symmetric proof (the law `F` of
the limit of `f_N`) is replaced by the dyadic pigeonhole `tail_pigeon`, which finds, for each `N`
and a fixed finite family of truncation levels, one level at which the tail entropy is small.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

set_option maxHeartbeats 1000000 in
/-- **The positive-entropy case is impossible.** -/
theorem positive_contra_all (hyp : Hyp V W KV KW) {r r₀ η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (hrη : (1 + η) * r < r₀) {B : NNReal}
    (hdef : ∀ N, 1 ≤ N → ∀ u : Config N d → ℝ, MemH1C (gibbs V W N) u →
      ent (gibbs V W N) (fun X => u X ^ 2) ≤ ENNReal.ofReal (2 / r₀) * energy V W N u +
        (B : ℝ≥0∞) * ∫⁻ X, ENNReal.ofReal (u X ^ 2) ∂gibbs V W N)
    {Ns : ℕ → ℕ} (hNs1 : ∀ k, 1 ≤ Ns k)
    {f : (k : ℕ) → Config (Ns k) d → ℝ} (hmem : ∀ k, MemH1C (gibbs V W (Ns k)) (f k))
    (hf0 : ∀ k X, 0 ≤ f k X)
    (hnorm : ∀ k, ∫ X, f k X ^ 2 ∂gibbs V W (Ns k) = 1)
    (hfin : ∀ k, ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≠ ⊤)
    (hviol : ∀ k, 2 * (energy V W (Ns k) (f k)).toReal <
      r * (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal)
    {h E : ℝ}
    (hh : Tendsto (fun k => (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal) atTop (𝓝 h))
    (hhpos : 0 < h) (hE : Tendsto (fun k => (energy V W (Ns k) (f k)).toReal) atTop (𝓝 E))
    (hcomp : ∀ M : ℝ, 1 ≤ M → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      r₀ / 2 * (ent (gibbs V W (Ns k)) (fun X => min (f k X) M ^ 2)).toReal ≤
        (energy V W (Ns k) (fun X => min (f k X) M)).toReal + ε) : False := by
  have hr₀ : 0 < r₀ := by nlinarith
  obtain ⟨C, hC0, hC⟩ := large_pointwise lemma_B1 hη
  set c0 := (1 + η) * (2 / r₀) with hc0
  have hB0 : (0 : ℝ) ≤ B := B.2
  -- a uniform bound for the entropies, hence for `∫ f² log⁺ f²`
  obtain ⟨H, hH⟩ : ∃ H : ℝ, ∀ k, (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal ≤ H := by
    obtain ⟨H, hH⟩ := hh.bddAbove_range
    exact ⟨H, fun k => hH ⟨k, rfl⟩⟩
  set A : ℝ := max H 0 + 1 with hA
  have hA1 : 1 ≤ A := by rw [hA]; linarith [le_max_right H 0]
  have hpl : ∀ k, Integrable (fun X => f k X ^ 2 * Real.posLog (f k X ^ 2)) (gibbs V W (Ns k)) ∧
      ∫ X, f k X ^ 2 * Real.posLog (f k X ^ 2) ∂gibbs V W (Ns k) ≤ A := by
    intro k
    obtain ⟨i, j⟩ := int_sq_posLog_le hyp (hmem k) (hf0 k) (hnorm k) (hfin k)
    exact ⟨i, j.trans (by linarith [hH k, le_max_left H 0])⟩
  have hexp3 : 1 / 3 ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    rw [one_div]
    exact inv_anti₀ (Real.exp_pos 1) this.le
  have claim : ∀ γ : ℝ, 0 < γ → h ≤ c0 * E + γ := by
    intro γ hγ
    set ε : ℝ := r₀ * γ / 8 with hε
    have hε0 : 0 < ε := by positivity
    set L : ℝ := 3 + 24 * A + 32 * (1 + η) * B * A / γ with hL
    have hL3 : 3 ≤ L := by
      have : 0 ≤ 32 * (1 + η) * B * A / γ := by positivity
      rw [hL]; linarith
    have hL24 : 24 * A ≤ L := by
      have : 0 ≤ 32 * (1 + η) * B * A / γ := by positivity
      rw [hL]; linarith
    have hLγ : 32 * (1 + η) * B * A ≤ L * γ := by
      have h1 : 32 * (1 + η) * B * A / γ ≤ L := by
        rw [hL]; linarith
      rwa [div_le_iff₀ hγ] at h1
    have hL0 : 0 < L := by linarith
    obtain ⟨K, hK⟩ := exists_nat_gt (64 * C * A / γ)
    have hKγ : 64 * C * A < K * γ := by rwa [div_lt_iff₀ hγ] at hK
    have hKpos : 0 < K := by
      have : (0 : ℝ) < K := lt_of_le_of_lt (by positivity) hK
      exact_mod_cast this
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
    -- the levels
    have hs3 : ∀ j : ℕ, 3 ≤ (2 : ℝ) ^ j * L := fun j =>
      le_trans hL3 (le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num)))
    have hM1 : ∀ j : ℕ, 1 ≤ 2 * Real.exp ((2 : ℝ) ^ j * L / 2) := fun j => by
      have : 1 ≤ Real.exp ((2 : ℝ) ^ j * L / 2) := Real.one_le_exp (by have := hs3 j; linarith)
      linarith
    have hev : ∀ᶠ k in atTop, ∀ j ∈ Finset.range K,
        r₀ / 2 * (ent (gibbs V W (Ns k))
          (fun X => min (f k X) (2 * Real.exp ((2 : ℝ) ^ j * L / 2)) ^ 2)).toReal ≤
        (energy V W (Ns k) (fun X => min (f k X) (2 * Real.exp ((2 : ℝ) ^ j * L / 2)))).toReal
          + ε := by
      rw [Filter.eventually_all_finset]
      intro j _
      exact hcomp _ (hM1 j) ε hε0
    have hbound : ∀ᶠ k in atTop, (ent (gibbs V W (Ns k)) (fun X => f k X ^ 2)).toReal ≤
        c0 * (energy V W (Ns k) (f k)).toReal + γ := by
      filter_upwards [hev] with k hk
      have : IsProbabilityMeasure (gibbs V W (Ns k)) := gibbs_isProbabilityMeasure hyp (Ns k)
      have hf2 : Integrable (fun X => f k X ^ 2) (gibbs V W (Ns k)) :=
        (memLp_of_memH1C hyp (hmem k)).integrable_sq
      obtain ⟨hsum, hpig⟩ := tail_pigeon (gibbs V W (Ns k)) hf2 (hpl k).1 (hpl k).2 hL0
      obtain ⟨j, hjK, hj⟩ := hpig K hKpos
      set s : ℝ := (2 : ℝ) ^ j * L with hs
      set ψ := ∫ X, tailFun s (f k X ^ 2) ∂gibbs V W (Ns k) with hψ
      have hψ0 : 0 ≤ ψ := integral_nonneg fun X => tailFun_nonneg (sq_nonneg _)
      -- `(s/2) ψ ≤ A`
      have hsA : s / 2 * ψ ≤ A := by
        have h1 := hsum (j + 1)
        rw [Finset.sum_range_succ] at h1
        have h2 : 0 ≤ ∑ i ∈ Finset.range j, (2 : ℝ) ^ i * L / 2 *
            ∫ X, tailFun ((2 : ℝ) ^ i * L) (f k X ^ 2) ∂gibbs V W (Ns k) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
            (integral_nonneg fun X => tailFun_nonneg (sq_nonneg _))
        linarith
      have hsL : L ≤ s := le_mul_of_one_le_left hL0.le (one_le_pow₀ (by norm_num))
      have hψL : L * ψ ≤ 2 * A := by
        have : L / 2 * ψ ≤ s / 2 * ψ := mul_le_mul_of_nonneg_right (by linarith) hψ0
        linarith
      have hψ1 : ψ ≤ 1 / 12 := by
        have : 24 * A * ψ ≤ 2 * A := le_trans (mul_le_mul_of_nonneg_right hL24 hψ0) hψL
        by_contra hcon
        push Not at hcon
        nlinarith
      have hψs : 4 / 3 * ψ ≤ Real.exp (-1) := by linarith
      have hone := positive_one hyp hη hC0 hC hr₀ (hdef (Ns k) (hNs1 k)) (hmem k) (hf0 k)
        (hnorm k) (hfin k) (hs3 j) (hk j (Finset.mem_range.2 hjK)) hψs
      -- bound the error terms
      have hterm1 : (1 + η) * B * (4 / 3 * ψ) ≤ γ / 4 := by
        have h1 : L * ((1 + η) * B * (4 / 3 * ψ)) ≤ 8 / 3 * ((1 + η) * B * A) := by
          have : L * ((1 + η) * B * (4 / 3 * ψ)) = 4 / 3 * ((1 + η) * B) * (L * ψ) := by ring
          rw [this]
          have h3 : 0 ≤ 4 / 3 * ((1 + η) * B) := by positivity
          calc 4 / 3 * ((1 + η) * B) * (L * ψ) ≤ 4 / 3 * ((1 + η) * B) * (2 * A) :=
                mul_le_mul_of_nonneg_left hψL h3
            _ = 8 / 3 * ((1 + η) * B * A) := by ring
        have h2 : L * ((1 + η) * B * (4 / 3 * ψ)) ≤ L * (γ / 4) := by
          calc L * ((1 + η) * B * (4 / 3 * ψ)) ≤ 8 / 3 * ((1 + η) * B * A) := h1
            _ ≤ L * (γ / 4) := by nlinarith
        exact le_of_mul_le_mul_left h2 hL0
      have hterm2 : C * (2 * s) * (4 / 3 * ψ) ≤ γ / 4 := by
        have e : C * (2 * s) * (4 / 3 * ψ) = 16 / 3 * C * (s / 2 * ψ) := by ring
        rw [e]
        calc 16 / 3 * C * (s / 2 * ψ) ≤ 16 / 3 * C * (A / K) :=
              mul_le_mul_of_nonneg_left hj (by positivity)
          _ = 16 / 3 * C * A / K := by ring
          _ ≤ γ / 4 := by
              rw [div_le_iff₀ hK0]
              nlinarith
      have hsplit : ((1 + η) * B + C * (2 * s)) * (4 / 3 * ψ) =
          (1 + η) * B * (4 / 3 * ψ) + C * (2 * s) * (4 / 3 * ψ) := by ring
      have hε2 : 2 / r₀ * ε = γ / 4 := by rw [hε]; field_simp; ring
      rw [hsplit, hε2] at hone
      rw [hc0]
      linarith
    have hlim : Tendsto (fun k => c0 * (energy V W (Ns k) (f k)).toReal + γ) atTop
        (𝓝 (c0 * E + γ)) := (hE.const_mul c0).add_const γ
    exact le_of_tendsto_of_tendsto hh hlim hbound
  have hhE : h ≤ c0 * E := le_of_forall_pos_le_add claim
  have h2E : 2 * E ≤ r * h :=
    le_of_tendsto_of_tendsto' (hE.const_mul 2) (hh.const_mul r) fun k => (hviol k).le
  have : c0 * E ≤ (1 + η) * r / r₀ * h := by
    rw [hc0]
    have : (1 + η) * (2 / r₀) * E = (1 + η) / r₀ * (2 * E) := by ring
    rw [this]
    have h1 : (1 + η) / r₀ * (2 * E) ≤ (1 + η) / r₀ * (r * h) :=
      mul_le_mul_of_nonneg_left h2E (by positivity)
    calc (1 + η) / r₀ * (2 * E) ≤ (1 + η) / r₀ * (r * h) := h1
      _ = (1 + η) * r / r₀ * h := by ring
  have hlt : (1 + η) * r / r₀ * h < h := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hr₀]
    nlinarith
  linarith

end SharpLSI.FL
