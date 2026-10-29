import SharpSymmetricLSI.Paper.GaussForm30

/-!
# R32 (H1): the easy half of the duality, lower semicontinuity of `ℰ_∞`

* `dual_le_gaussForm`: `2∫ f(-Lc) - ℰ(c) ≤ ℰ_∞(f)` for every cylinder `c` and `f ∈ L²(γ)`.
* `gaussForm_le_of_tendsto`: if `f_n → f` in `L²(γ)` and `ℰ_∞(f_n) ≤ a_n → a` then `ℰ_∞(f) ≤ a`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} {T : ℕ → ℕ → ℝ}

/-- **Easy half of the duality**: `2∫ f(-Lc) - ℰ(c) ≤ ℰ_∞(f)`. -/
theorem dual_le_gaussForm (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    ENNReal.ofReal (2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ - c.formR lam' γ) ≤
      gaussForm lam' γ f := by
  haveI := hγ.1
  unfold gaussForm
  refine le_iInf₂ fun u hu => ?_
  set G : (ℕ → ℝ) → ℝ := fun z => -(c.gen lam' Y z)
  have hG : MemLp G 2 γ := (memLp_gen hγ hY lam' c).neg
  set a : ℕ → ℝ := fun n => ∫ z, (u n).eval z * G z ∂γ
  have ha : Tendsto a atTop (𝓝 (∫ z, f z * G z ∂γ)) := by
    have hd : ∀ n, |a n - ∫ z, f z * G z ∂γ| ≤
        (eLpNorm (fun z => (u n).eval z - f z) 2 γ).toReal * (eLpNorm G 2 γ).toReal := fun n => by
      have hm : MemLp (fun z => (u n).eval z - f z) 2 γ := (u n).memLp_eval.sub hf
      have e : a n - ∫ z, f z * G z ∂γ = ∫ z, ((u n).eval z - f z) * G z ∂γ := by
        simp only [a]
        rw [← integral_sub (f := fun z => (u n).eval z * G z) (g := fun z => f z * G z)
          ((u n).memLp_eval.integrable_mul hG) (hf.integrable_mul hG)]
        congr 1; funext z; ring
      rw [e]
      exact abs_integral_mul_le_L2 hm hG
    have h0 : Tendsto (fun n => (eLpNorm (fun z => (u n).eval z - f z) 2 γ).toReal *
        (eLpNorm G 2 γ).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hu).mul_const (eLpNorm G 2 γ).toReal
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hd n) h0
  have hb : Tendsto (fun n => ENNReal.ofReal (2 * a n - c.formR lam' γ)) atTop
      (𝓝 (ENNReal.ofReal (2 * ∫ z, f z * G z ∂γ - c.formR lam' γ))) :=
    ENNReal.tendsto_ofReal ((ha.const_mul 2).sub_const _)
  rw [← hb.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [(u n).form_eq_ofReal hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  have := two_mul_le_formR hγ hPSD hC hY hlam (u n) c
  simp only [a, G]
  linarith

/-- **Lower semicontinuity of `ℰ_∞` along `L²` limits.** -/
theorem gaussForm_le_of_tendsto {lam' : ℕ → ℝ} {F : ℕ → (ℕ → ℝ) → ℝ} {f : (ℕ → ℝ) → ℝ}
    (hF : Tendsto (fun n => eLpNorm (fun z => F n z - f z) 2 γ) atTop (𝓝 0))
    {a : ℕ → ℝ≥0∞} {a0 : ℝ≥0∞} (ha : ∀ n, gaussForm lam' γ (F n) ≤ a n)
    (hlim : Tendsto a atTop (𝓝 a0)) (hfin : ∀ n, a n < ⊤) :
    gaussForm lam' γ f ≤ a0 := by
  have hchoose : ∀ n : ℕ, ∃ w : Cyl, eLpNorm (fun z => w.eval z - F n z) 2 γ < 1 / ((n : ℝ≥0∞) + 1)
      ∧ w.form lam' γ < a n + 1 / ((n : ℝ≥0∞) + 1) := by
    intro n
    have hδ : (0 : ℝ≥0∞) < 1 / ((n : ℝ≥0∞) + 1) := by simp
    obtain ⟨u, b, hu, hb, hblt⟩ :=
      exists_seq_form_tendsto ((ha n).trans_lt (hfin n)) hδ
    have h2 : b < a n + 1 / ((n : ℝ≥0∞) + 1) :=
      hblt.trans_le (by gcongr; exact ha n)
    obtain ⟨k, hk1, hk2⟩ := ((hu.eventually (gt_mem_nhds hδ)).and
      (hb.eventually (gt_mem_nhds h2))).exists
    exact ⟨u k, hk1, hk2⟩
  choose w hw1 hw2 using hchoose
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0∞) + 1)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1) |>.congr
      (fun n => by simp)
  have hconv : Tendsto (fun n => eLpNorm (fun z => (w n).eval z - f z) 2 γ) atTop (𝓝 0) := by
    have hle : ∀ n : ℕ, eLpNorm (fun z => (w n).eval z - f z) 2 γ ≤
        1 / ((n : ℝ≥0∞) + 1) + eLpNorm (fun z => F n z - f z) 2 γ := fun n => by
      have e : (fun z => (w n).eval z - f z) =
          (fun z => (w n).eval z - F n z) + fun z => F n z - f z := by funext z; simp
      rw [e]
      exact (eLpNorm_add_le (by norm_num)).trans (by gcongr; exact (hw1 n).le)
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ≥0∞) + 1) + eLpNorm (fun z => F n z - f z) 2 γ)
        atTop (𝓝 0) := by simpa using hinv.add hF
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hle
  refine (gaussForm_le_liminf w hconv).trans ?_
  have h1 : Tendsto (fun n : ℕ => a n + 1 / ((n : ℝ≥0∞) + 1)) atTop (𝓝 a0) := by
    simpa using hlim.add hinv
  rw [← h1.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n => (hw2 n).le)

end SharpLSI
