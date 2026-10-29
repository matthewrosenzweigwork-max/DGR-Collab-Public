import SharpSymmetricLSI.Paper.GaussFormClause1

/-!
# R32 form clause (lane s42), step 2: lower semicontinuity of `ℰ_∞`

`ℰ_∞ = gaussForm` is the relaxation of the cylinder form, hence lower semicontinuous along
`L²(γ)` limits (`gaussForm_le_liminf_of_L2`): a diagonal choice of cylinders.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {lam' : ℕ → ℝ}

/-- One cylinder close to `f` in `L²` with form below `b > ℰ_∞(f)`. -/
theorem exists_cyl_near {f : (ℕ → ℝ) → ℝ} {b : ℝ≥0∞} (hb : gaussForm lam' γ f < b) {ε : ℝ≥0∞}
    (hε : 0 < ε) : ∃ c : Cyl, eLpNorm (fun z => c.eval z - f z) 2 γ < ε ∧ c.form lam' γ < b := by
  unfold gaussForm at hb
  obtain ⟨u, hb⟩ := iInf_lt_iff.mp hb
  obtain ⟨hu, hb⟩ := iInf_lt_iff.mp hb
  have h1 := frequently_lt_of_liminf_lt (by isBoundedDefault) hb
  have h2 := hu.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn1, hn2⟩ := (h1.and_eventually h2).exists
  exact ⟨u n, hn2, hn1⟩

/-- **`ℰ_∞` is lower semicontinuous along `L²` limits.** -/
theorem gaussForm_le_liminf_of_L2 {f : ℕ → (ℕ → ℝ) → ℝ} {g : (ℕ → ℝ) → ℝ}
    (hf : Tendsto (fun n => eLpNorm (fun z => f n z - g z) 2 γ) atTop (𝓝 0)) :
    gaussForm lam' γ g ≤ liminf (fun n => gaussForm lam' γ (f n)) atTop := by
  set L := liminf (fun n => gaussForm lam' γ (f n)) atTop
  rcases eq_top_or_lt_top L with hL | hL
  · rw [hL]; exact le_top
  -- indices `n_k ≥ k` with `ℰ_∞(f_{n_k}) < L + 1/(k+1)`
  have hfreq : ∀ k : ℕ, ∃ n, k ≤ n ∧ gaussForm lam' γ (f n) < L + ((k : ℝ≥0∞) + 1)⁻¹ := fun k => by
    have hlt : L < L + ((k : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.lt_add_right hL.ne (ENNReal.inv_ne_zero.2 (by simp))
    have := frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    obtain ⟨n, hn1, hn2⟩ := (this.and_eventually (eventually_ge_atTop k)).exists
    exact ⟨n, hn2, hn1⟩
  choose n hn1 hn2 using hfreq
  have hcyl : ∀ k, ∃ c : Cyl, eLpNorm (fun z => c.eval z - f (n k) z) 2 γ < ((k : ℝ≥0∞) + 1)⁻¹ ∧
      c.form lam' γ < L + ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
    exists_cyl_near (hn2 k) (ENNReal.inv_pos.2 (by simp))
  choose u hu1 hu2 using hcyl
  have hinv : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have hfn : Tendsto (fun k => eLpNorm (fun z => f (n k) z - g z) 2 γ) atTop (𝓝 0) :=
    hf.comp (tendsto_atTop_mono hn1 tendsto_id)
  have hconv : Tendsto (fun k => eLpNorm (fun z => (u k).eval z - g z) 2 γ) atTop (𝓝 0) := by
    have hsum : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹ + eLpNorm (fun z => f (n k) z - g z) 2 γ)
        atTop (𝓝 0) := by simpa using hinv.add hfn
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
      fun k => ?_
    have e : (fun z => (u k).eval z - g z) =
        (fun z => (u k).eval z - f (n k) z) + fun z => f (n k) z - g z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    refine (eLpNorm_add_le one_le_two).trans ?_
    exact add_le_add (hu1 k).le le_rfl
  refine (gaussForm_le_liminf u hconv).trans ?_
  have hb : Tendsto (fun k : ℕ => L + ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 L) := by
    simpa using tendsto_const_nhds.add hinv
  calc liminf (fun k => (u k).form lam' γ) atTop
      ≤ liminf (fun k : ℕ => L + ((k : ℝ≥0∞) + 1)⁻¹) atTop :=
        liminf_le_liminf (Eventually.of_forall fun k => (hu2 k).le)
    _ = L := hb.liminf_eq

end SharpLSI
