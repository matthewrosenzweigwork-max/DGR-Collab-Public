import SharpSymmetricLSI.Paper.PartitionUpper

/-!
# Lemma 2.4 (Phase 3, lane D; R5)

`N^{-1} log Z_N → -F_*`: the lower half from the Gibbs variational identity with product
states (`Paper/PartitionLower.lean`), the upper half by the method of types
(`Paper/PartitionUpper.lean`). Route departure from Sanov/Varadhan, recorded in
`Audit/statement_map.md`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Uniform continuity gives a cell resolution with oscillation `≤ ω`. -/
theorem exists_cells (hyp : Hyp V W KV KW) {ω : ℝ} (hω : 0 < ω) :
    ∃ K : ℕ, ∃ _ : NeZero K, (∀ x, |V x - V (cellPt K (cellIdx K x))| ≤ ω) ∧
      ∀ x y, |W x y - W (cellPt K (cellIdx K x)) (cellPt K (cellIdx K y))| ≤ ω := by
  obtain ⟨δV, hδV, hV⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hyp.continuous_V) ω hω
  obtain ⟨δW, hδW, hW⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hyp.continuous_W) ω hω
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδV hδW)
  refine ⟨n + 1, ⟨by omega⟩, fun x => ?_, fun x y => ?_⟩
  · have h1 := (dist_cellPt (K := n + 1) x).trans_lt (by push_cast; exact hn.trans_le (min_le_left _ _))
    have := hV h1
    rw [Real.dist_eq] at this
    exact this.le
  · have hx := (dist_cellPt (K := n + 1) x).trans_lt (by push_cast; exact hn.trans_le (min_le_right _ _))
    have hy := (dist_cellPt (K := n + 1) y).trans_lt (by push_cast; exact hn.trans_le (min_le_right _ _))
    have h1 : dist (x, y) (cellPt (n + 1) (cellIdx (n + 1) x), cellPt (n + 1) (cellIdx (n + 1) y)) <
        δW := by
      rw [Prod.dist_eq]; exact max_lt hx hy
    have := hW h1
    rw [Real.dist_eq] at this
    exact this.le

theorem Fstar_eq_coe (hyp : Hyp V W KV KW) : Fstar V W = ((Fstar V W).toReal : EReal) := by
  obtain ⟨c, C, hc, hC, -⟩ := Fstar_bounds hyp
  refine (EReal.coe_toReal ?_ ?_).symm
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top C) hC
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) hc

theorem tendsto_log_succ_div :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / N) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine h.congr fun N => ?_
  simp

/-- Lemma 2.4 in `ℝ`. -/
theorem tendsto_log_partition (hyp : Hyp V W KV KW) :
    Tendsto (fun N : ℕ => Real.log (partitionFn V W N) / N) atTop (𝓝 (-(Fstar V W).toReal)) := by
  set F := (Fstar V W).toReal with hFdef
  have hF : Fstar V W = F := Fstar_eq_coe hyp
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW' : ∀ x y, |W x y| ≤ BW := fun x y => hBW (x, y)
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower half
    set ε := -F - b with hε
    have hε0 : 0 < ε := by linarith
    have hlt : Fstar V W < ((F + ε / 2 : ℝ) : EReal) := by
      rw [hF, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨ρ, hρ⟩ := iInf_lt_iff.mp hlt
    have hk : klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ := by
      intro h; rw [freeEnergy_top _ h] at hρ; exact not_top_lt hρ
    rw [freeEnergy_eq _ hk, EReal.coe_lt_coe_iff] at hρ
    have hI := abs_interE_le hBW' hyp.continuous_W (ρ := (ρ : Measure (Torus d)))
      (η := (ρ : Measure (Torus d)))
    have ht : Tendsto (fun N : ℕ => BW / (2 * N)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (BW / 2))
      refine this.congr fun N => ?_
      ring
    filter_upwards [eventually_ge_atTop 1, ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))]
      with N hN hsmall
    have h1 := log_partition_ge hyp hN hk
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have h2 : -(BW / (2 * N)) ≤ interE W ρ ρ / (2 * N) := by
      rw [neg_div', div_le_div_iff_of_pos_right (by positivity)]
      linarith [(abs_le.mp hI).1]
    linarith
  · -- upper half
    set ε := b + F with hε
    have hε0 : 0 < ε := by linarith
    obtain ⟨K, hK, hV, hW⟩ := exists_cells hyp (by positivity : 0 < ε / 6)
    have ht : Tendsto (fun N : ℕ => (K : ℝ) ^ d * (Real.log ((N : ℝ) + 1) / N)) atTop (𝓝 0) := by
      simpa using tendsto_log_succ_div.const_mul ((K : ℝ) ^ d)
    filter_upwards [eventually_ge_atTop 1, ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))]
      with N hN hsmall
    have h1 := log_partition_le_cells hyp hN hV hW hF
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hN0]
    have : (K : ℝ) ^ d * (Real.log ((N : ℝ) + 1) / N) * N = (K : ℝ) ^ d * Real.log ((N : ℝ) + 1) := by
      field_simp
    nlinarith

/-- **Lemma 2.4** in the frozen `EReal` form. -/
theorem partition_limit_aux (hyp : Hyp V W KV KW) :
    Tendsto (fun N : ℕ => ((Real.log (partitionFn V W N) / N : ℝ) : EReal)) atTop
      (𝓝 (-Fstar V W)) := by
  rw [Fstar_eq_coe hyp, ← EReal.coe_neg]
  exact (continuous_coe_real_ereal.tendsto _).comp (tendsto_log_partition hyp)

end SharpLSI
