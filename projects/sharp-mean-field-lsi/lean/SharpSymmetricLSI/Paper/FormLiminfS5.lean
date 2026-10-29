import Mathlib

/-!
# (8.20) (lane s42): the abstract duality step

If `G = sup_c (2 A_c - B_c)` and, for every `c`, there are real sequences `x_k → A_c`,
`y_k → B_c` with `2 x_k - y_k ≤ E_k`, then `G ≤ liminf E` (`le_liminf_of_duality`). Pure
`ℝ≥0∞`/`EReal` bookkeeping; no real-valued `liminf` is taken.
-/

open Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- **The duality lower bound.** -/
theorem le_liminf_of_duality {ι : Type*} {G : ℝ≥0∞} {E : ℕ → ℝ≥0∞} (hE : ∀ k, E k ≠ ⊤)
    {A : ι → ℝ} {B : ι → ℝ≥0∞} (hB : ∀ c, B c ≠ ⊤)
    (hdual : (G : EReal) = ⨆ c, ((2 * A c : ℝ) : EReal) - (B c : EReal))
    (hseq : ∀ c, ∃ x y : ℕ → ℝ, Tendsto x atTop (𝓝 (A c)) ∧ Tendsto y atTop (𝓝 (B c).toReal) ∧
      ∀ k, 2 * x k - y k ≤ (E k).toReal) :
    G ≤ liminf E atTop := by
  rw [← EReal.coe_ennreal_le_coe_ennreal_iff, hdual]
  refine iSup_le fun c => ?_
  obtain ⟨x, y, hx, hy, hxy⟩ := hseq c
  set v := 2 * A c - (B c).toReal
  have hv : ((2 * A c : ℝ) : EReal) - (B c : EReal) = (v : EReal) := by
    rw [← EReal.coe_ennreal_toReal (hB c), ← EReal.coe_sub]
  rw [hv]
  -- every `w < v` gives `ofReal w ≤ liminf E`
  have hlim : Tendsto (fun k => 2 * x k - y k) atTop (𝓝 v) := (hx.const_mul 2).sub hy
  have hw : ∀ w < v, ENNReal.ofReal w ≤ liminf E atTop := fun w hwv => by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hlim.eventually (lt_mem_nhds hwv)] with k hk
    calc ENNReal.ofReal w ≤ ENNReal.ofReal (E k).toReal :=
          ENNReal.ofReal_le_ofReal (hk.le.trans (hxy k))
      _ = E k := ENNReal.ofReal_toReal (hE k)
  have hv' : ENNReal.ofReal v ≤ liminf E atTop := by
    refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto v).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio v))) ?_
    filter_upwards [self_mem_nhdsWithin] with w hwv
    exact hw w hwv
  calc (v : EReal) ≤ ((ENNReal.ofReal v : ℝ≥0∞) : EReal) := by
        rw [EReal.coe_ennreal_ofReal]; exact_mod_cast le_max_left v 0
    _ ≤ _ := EReal.coe_ennreal_le_coe_ennreal_iff.2 hv'

end SharpLSI
