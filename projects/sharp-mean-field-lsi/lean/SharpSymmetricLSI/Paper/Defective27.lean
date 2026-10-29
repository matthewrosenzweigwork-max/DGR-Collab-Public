import SharpSymmetricLSI.Paper.Defective26

/-!
# R03 (Proposition 2.2), part 27: scalar lemmas for the absorption

* `absorb_sqrt`: `αH ≤ βI + K₁ + K₂√(H+1)` with `2rβ < α`, `β ≥ 1` gives `2rH ≤ I + K₃`;
* `exists_tau_eps`: the choice of `τ, ε` with `2r(1 + ε + bτ) < 2r₀(1 - aτ)`;
* `sum_Ico_le_of_mono`: the last `M` increments are at most `M h_{N-1}`;
* `exists_r0`: some `r < r₀` with `r₀ ≤ r_*`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

theorem absorb_sqrt {r α β K₁ K₂ H I : ℝ} (hr : 0 < r) (hβ : 1 ≤ β) (hαβ : 2 * r * β < α)
    (hK₂ : 0 ≤ K₂) (hH : 0 ≤ H)
    (h : α * H ≤ β * I + K₁ + K₂ * Real.sqrt (H + 1)) :
    2 * r * H ≤ I + max 0 (K₁ + (α - 2 * r * β) + K₂ ^ 2 / (4 * (α - 2 * r * β))) := by
  set δ := α - 2 * r * β with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set s := Real.sqrt (H + 1)
  have hs2 : s ^ 2 = H + 1 := Real.sq_sqrt (by linarith)
  -- `K₂ s ≤ δ s² + K₂²/(4δ)`
  have hamgm : K₂ * s ≤ δ * s ^ 2 + K₂ ^ 2 / (4 * δ) := by
    have h0 : 0 ≤ (2 * δ * s - K₂) ^ 2 := sq_nonneg _
    have e : δ * s ^ 2 + K₂ ^ 2 / (4 * δ) - K₂ * s = (2 * δ * s - K₂) ^ 2 / (4 * δ) := by
      first | (field_simp; done) | (field_simp; ring)
    have : 0 ≤ (2 * δ * s - K₂) ^ 2 / (4 * δ) := div_nonneg h0 (by positivity)
    linarith
  rw [hs2] at hamgm
  have h2 : 2 * r * β * H ≤ β * I + (K₁ + δ + K₂ ^ 2 / (4 * δ)) := by nlinarith
  have h3 : 2 * r * H ≤ I + (K₁ + δ + K₂ ^ 2 / (4 * δ)) / β := by
    have hβ0 : 0 < β := by linarith
    rw [← mul_le_mul_iff_of_pos_left hβ0]
    have : β * (I + (K₁ + δ + K₂ ^ 2 / (4 * δ)) / β) = β * I + (K₁ + δ + K₂ ^ 2 / (4 * δ)) := by
      field_simp
    rw [this]; linarith
  have h4 : (K₁ + δ + K₂ ^ 2 / (4 * δ)) / β ≤ max 0 (K₁ + δ + K₂ ^ 2 / (4 * δ)) := by
    rcases le_total (K₁ + δ + K₂ ^ 2 / (4 * δ)) 0 with hn | hn
    · exact (div_nonpos_of_nonpos_of_nonneg hn (by linarith)).trans (le_max_left _ _)
    · exact (div_le_self hn hβ).trans (le_max_right _ _)
  linarith

theorem exists_tau_eps {r r₀ a b : ℝ} (hr : 0 < r) (hrr : r < r₀) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ τ ε : ℝ, 0 < τ ∧ τ ≤ 1 / 4 ∧ 0 < ε ∧
      2 * r * (1 + ε + b * τ) < 2 * r₀ * (1 - a * τ) := by
  set D := 2 * r * b + 2 * r₀ * a + 1 with hD
  have hr₀ : 0 < r₀ := hr.trans hrr
  have hD0 : 0 < D := by rw [hD]; positivity
  set τ := min (1 / 4) ((r₀ - r) / D)
  have hτ0 : 0 < τ := lt_min (by norm_num) (div_pos (by linarith) hD0)
  have hτD : τ * D ≤ r₀ - r := by
    have := min_le_right (1 / 4 : ℝ) ((r₀ - r) / D)
    rwa [le_div_iff₀ hD0] at this
  refine ⟨τ, (r₀ - r) / (4 * r), hτ0, min_le_left _ _, div_pos (by linarith) (by positivity), ?_⟩
  have e : 2 * r * ((r₀ - r) / (4 * r)) = (r₀ - r) / 2 := by first | (field_simp; done) | (field_simp; ring)
  have hτ1 : 0 ≤ τ := hτ0.le
  nlinarith [mul_nonneg hτ1 (le_of_lt hD0)]

theorem sum_Ico_le_of_mono {h : ℕ → ℝ} {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (hmono : ∀ j, j + 1 < N → h j ≤ h (j + 1)) :
    ∑ j ∈ Finset.Ico ℓ N, h j ≤ (N - ℓ : ℕ) * h (N - 1) := by
  have aux : ∀ j k, j + k < N → h j ≤ h (j + k) := by
    intro j k
    induction k with
    | zero => intro _; simp
    | succ k ih => intro hk; exact (ih (by omega)).trans (hmono (j + k) (by omega))
  have hle : ∀ j, j < N → h j ≤ h (N - 1) := by
    intro j hj
    have := aux j (N - 1 - j) (by omega)
    rwa [show j + (N - 1 - j) = N - 1 by omega] at this
  calc ∑ j ∈ Finset.Ico ℓ N, h j ≤ ∑ _j ∈ Finset.Ico ℓ N, h (N - 1) :=
        Finset.sum_le_sum fun j hj => hle j (Finset.mem_Ico.mp hj).2
    _ = _ := by simp [Finset.sum_const, Nat.card_Ico]

theorem exists_r0 {R : ℝ≥0∞} {r : ℝ} (hr0 : 0 < r) (hr : ENNReal.ofReal r < R) :
    ∃ r₀ : ℝ, r < r₀ ∧ ENNReal.ofReal r₀ ≤ R := by
  by_cases hR : R = ⊤
  · exact ⟨r + 1, by linarith, hR ▸ le_top⟩
  · have hlt : r < R.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hr0.le hR).mp hr
    refine ⟨(r + R.toReal) / 2, by linarith, ?_⟩
    calc ENNReal.ofReal ((r + R.toReal) / 2) ≤ ENNReal.ofReal R.toReal :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = R := ENNReal.ofReal_toReal hR

end SharpLSI
