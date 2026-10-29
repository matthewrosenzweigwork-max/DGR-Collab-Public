import FullLabeledLSI.Paper.Sec8Min1

/-!
# Section 8.3 (linearization), part 9: continuity of the second variation along `H`-convergent
sequences

If `u_n`, `g` are bounded measurable with mean zero and `(I+T)u_n → (I+T)g` in `L²(μ)`, then, by
the coercivity `⟨x,(I+T)x⟩ ≥ σ‖x‖²`, `⟨u_n,(I+T)u_n⟩ → ⟨g,(I+T)g⟩` (`quad_conv`).
-/

open MeasureTheory InformationTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Bounded measurable functions. -/
def BM (f : Torus d → ℝ) : Prop := Measurable f ∧ ∃ B, ∀ x, |f x| ≤ B

theorem BM.add {f g : Torus d → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨hfm, Bf, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg⟩ := hg
  exact ⟨hfm.add hgm, Bf + Bg, fun x => (abs_add_le _ _).trans (add_le_add (hBf x) (hBg x))⟩

theorem BM.sub {f g : Torus d → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  obtain ⟨hfm, Bf, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg⟩ := hg
  exact ⟨hfm.sub hgm, Bf + Bg, fun x => (abs_sub _ _).trans (add_le_add (hBf x) (hBg x))⟩

theorem BM.mul {f g : Torus d → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨hfm, Bf, hBf⟩ := hf
  obtain ⟨hgm, Bg, hBg⟩ := hg
  refine ⟨hfm.mul hgm, Bf * Bg, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hBf x) (hBg x) (abs_nonneg _) ((abs_nonneg _).trans (hBf x))

theorem BM.integrable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : BM f) : Integrable f μ := by
  obtain ⟨hfm, B, hB⟩ := hf
  exact Integrable.of_bound hfm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem BM.memLp {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : BM f) : MemLp f 2 μ := by
  obtain ⟨hfm, B, hB⟩ := hf
  exact memLp_of_bdd hfm hB

theorem BM.sq {f : Torus d → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  obtain ⟨h1, B, hB⟩ := hf.mul hf
  refine ⟨?_, B, fun x => ?_⟩
  · have e : (fun x => f x ^ 2) = fun x => f x * f x := by funext x; ring
    rw [e]; exact h1
  · have := hB x
    simp only [] at this ⊢
    rwa [_root_.sq]

theorem BM.of_lip {f : Torus d → ℝ} (hf : ∃ L : ℝ≥0, LipschitzWith L f) : BM f := by
  obtain ⟨L, hL⟩ := hf
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hL.continuous
  exact ⟨hL.continuous.measurable, B, hB⟩

theorem BM.of_cont {f : Torus d → ℝ} (hf : Continuous f) : BM f := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hf
  exact ⟨hf.measurable, B, hB⟩

theorem BM.top (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {u : Torus d → ℝ} (hu : BM u) (hu0 : ∫ x, u x ∂μ = 0) : BM (Top W μ u) := by
  obtain ⟨hum, B, hB⟩ := hu
  obtain ⟨⟨L, hL⟩, hbd⟩ := top_lip_bdd hyp hum hB hu0
  exact ⟨hL.continuous.measurable, hbd⟩

theorem BM.H (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {u : Torus d → ℝ} (hu : BM u) (hu0 : ∫ x, u x ∂μ = 0) :
    BM (fun x => u x + Top W μ u x) := hu.add (hu.top hyp hu0)

theorem quad_conv (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ x : Torus d → ℝ, MemL20 μ x → σ * ∫ y, x y ^ 2 ∂μ ≤ secondVar W μ x)
    {g : Torus d → ℝ} (hg : BM g) (hg0 : ∫ x, g x ∂μ = 0)
    {u : ℕ → Torus d → ℝ} (hu : ∀ n, BM (u n)) (hu0 : ∀ n, ∫ x, u n x ∂μ = 0)
    (hδ : Tendsto (fun n => ∫ x, ((u n x + Top W μ (u n) x) - (g x + Top W μ g x)) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => secondVar W μ (u n)) atTop (𝓝 (secondVar W μ g)) := by
  set F : Torus d → ℝ := fun x => g x + Top W μ g x with hF
  have hFB : BM F := hg.H hyp hg0
  set δ : ℕ → ℝ := fun n => ∫ x, ((u n x + Top W μ (u n) x) - F x) ^ 2 ∂μ with hδdef
  have hδ0 : ∀ n, 0 ≤ δ n := fun n => integral_nonneg fun x => sq_nonneg _
  set A : ℝ := ∫ x, F x ^ 2 ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have key : ∀ n, |secondVar W μ (u n) - secondVar W μ g| ≤
      (Real.sqrt (δ n) / σ) * Real.sqrt (2 * A + 2 * δ n) +
        Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (δ n) := by
    intro n
    have hHB : BM (fun x => u n x + Top W μ (u n) x) := (hu n).H hyp (hu0 n)
    set Hn : Torus d → ℝ := fun x => u n x + Top W μ (u n) x with hHn
    set xn : Torus d → ℝ := fun x => u n x - g x with hxn
    have hxB : BM xn := (hu n).sub hg
    have hx0 : ∫ x, xn x ∂μ = 0 := by
      simp only [xn]
      rw [integral_sub (hu n).integrable hg.integrable, hu0 n, hg0, sub_zero]
    have hxL20 : MemL20 μ xn := ⟨hxB.memLp, hx0⟩
    have hTx : ∀ x, Top W μ xn x = Top W μ (u n) x - Top W μ g x := by
      intro x
      have := Top_lin hyp μ (hu n).integrable hg.integrable 1 (-1) x
      have e : xn = fun y => 1 * u n y + (-1) * g y := by funext y; simp only [xn]; ring
      rw [e, this]; ring
    have hxH : ∀ x, xn x + Top W μ xn x = Hn x - F x := by
      intro x; rw [hTx]; simp only [xn, Hn, F]; ring
    have hHFB : BM (fun x => Hn x - F x) := hHB.sub hFB
    have hsv : secondVar W μ xn = ∫ x, xn x * (Hn x - F x) ∂μ := by
      unfold secondVar
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hxH x])
    have hcs := cs2 (μ := μ) hxB.memLp hHFB.memLp
    set a : ℝ := ∫ x, xn x ^ 2 ∂μ with ha
    have ha0 : 0 ≤ a := integral_nonneg fun x => sq_nonneg _
    have hσa := hσ xn hxL20
    have hs : Real.sqrt a ≤ Real.sqrt (δ n) / σ := by
      rw [le_div_iff₀ hσ0]
      have h1 : σ * a ≤ Real.sqrt a * Real.sqrt (δ n) := by
        calc σ * a ≤ secondVar W μ xn := hσa
          _ = ∫ x, xn x * (Hn x - F x) ∂μ := hsv
          _ ≤ |∫ x, xn x * (Hn x - F x) ∂μ| := le_abs_self _
          _ ≤ _ := hcs
      have h2 : σ * a = σ * Real.sqrt a ^ 2 := by rw [Real.sq_sqrt ha0]
      by_cases hz : Real.sqrt a = 0
      · rw [hz]; simp
      · have hpos : 0 < Real.sqrt a := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
        by_contra hlt
        push Not at hlt
        nlinarith [mul_pos hpos (sub_pos.2 hlt)]
    have hHn2 : ∫ x, Hn x ^ 2 ∂μ ≤ 2 * A + 2 * δ n := by
      have hi1 : Integrable (fun x => F x ^ 2) μ := hFB.sq.integrable
      have hi2 : Integrable (fun x => (Hn x - F x) ^ 2) μ := hHFB.sq.integrable
      have : ∫ x, (2 * F x ^ 2 + 2 * (Hn x - F x) ^ 2) ∂μ = 2 * A + 2 * δ n := by
        rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
          integral_const_mul]
      rw [← this]
      exact integral_mono hHB.sq.integrable ((hi1.const_mul 2).add (hi2.const_mul 2))
        fun x => by nlinarith [sq_nonneg (Hn x - 2 * F x)]
    have hQ : secondVar W μ (u n) - secondVar W μ g =
        ∫ x, xn x * Hn x ∂μ + ∫ x, g x * (Hn x - F x) ∂μ := by
      unfold secondVar
      rw [← integral_add (hxB.mul hHB).integrable (hg.mul hHFB).integrable,
        ← integral_sub ((hu n).mul hHB).integrable (hg.mul hFB).integrable]
      congr 1; funext x; simp only [xn, Hn, F]; ring
    rw [hQ]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · calc |∫ x, xn x * Hn x ∂μ| ≤ Real.sqrt a * Real.sqrt (∫ x, Hn x ^ 2 ∂μ) :=
            cs2 hxB.memLp hHB.memLp
        _ ≤ (Real.sqrt (δ n) / σ) * Real.sqrt (2 * A + 2 * δ n) :=
            mul_le_mul hs (Real.sqrt_le_sqrt hHn2) (Real.sqrt_nonneg _)
              (div_nonneg (Real.sqrt_nonneg _) hσ0.le)
    · exact cs2 hg.memLp hHFB.memLp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun n => (Real.sqrt (δ n) / σ) * Real.sqrt (2 * A + 2 * δ n) +
        Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (δ n)) (fun n => norm_nonneg _)
    (fun n => by rw [Real.norm_eq_abs]; exact key n) ?_
  have hr : Tendsto (fun n => Real.sqrt (δ n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hδ
    simpa [Function.comp_def] using this
  have hs2 : Tendsto (fun n => Real.sqrt (2 * A + 2 * δ n)) atTop (𝓝 (Real.sqrt (2 * A + 2 * 0))) :=
    (Real.continuous_sqrt.tendsto _).comp (tendsto_const_nhds.add (hδ.const_mul 2))
  have := ((hr.div_const σ).mul hs2).add (hr.const_mul (Real.sqrt (∫ x, g x ^ 2 ∂μ)))
  simpa using this

end Sec8
end SharpLSI.FL
