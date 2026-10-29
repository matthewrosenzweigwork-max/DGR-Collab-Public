import SharpSymmetricLSI.Paper.GaussForm16
import SharpSymmetricLSI.Paper.GaussForm14

/-!
# R32 (8.8), part 1: the easy direction of the form duality

`sup_le_gaussForm`: for every `f ∈ L²(γ)`,
`sup_c (2∫ f(-L c) dγ - ℰ(c)) ≤ ℰ_∞(f)` (in `EReal`), from `2∫ u(-Lc) ≤ ℰ(u) + ℰ(c)` on cylinders
(`two_mul_le_formR`) and the definition of `ℰ_∞` as the relaxation of (8.1).
`sup_le_gaussForm_of_prop21` is the same for the paper's data, given Proposition 2.1, and
`form_duality_of_le_sup` reduces (8.8) to the hard inequality `ℰ_∞(f) ≤ sup`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

section generic
variable {γ : Measure (ℕ → ℝ)} {C T : ℕ → ℕ → ℝ}

/-- One cylinder: `2∫ f(-Lc) - ℰ(c) ≤ ℰ_∞(f)`. -/
theorem two_integral_sub_form_le (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) {lam' : ℕ → ℝ}
    (hlam : ∀ i, 0 ≤ lam' i) {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) (c : Cyl) :
    ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) - (c.form lam' γ : EReal) ≤
      (gaussForm lam' γ f : EReal) := by
  haveI := hγ.1
  set a : ℝ := 2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ - c.formR lam' γ with ha
  have hform : (c.form lam' γ : EReal) = ((c.formR lam' γ : ℝ) : EReal) := by
    rw [Cyl.form_eq_ofReal hlam, EReal.coe_ennreal_ofReal, max_eq_left]
    exact integral_nonneg fun z => Finset.sum_nonneg fun i _ => mul_nonneg (hlam _) (sq_nonneg _)
  -- `ofReal a ≤ ℰ_∞(f)`
  have hkey : ENNReal.ofReal a ≤ gaussForm lam' γ f := by
    refine le_iInf₂ fun u hu => ?_
    have hgen := memLp_gen (T := T) hγ hY lam' c
    have hneg : MemLp (fun z => -(c.gen lam' Y z)) 2 γ := hgen.neg
    -- `∫ uₙ(-Lc) → ∫ f(-Lc)`
    have hconv : Tendsto (fun n => ∫ z, (u n).eval z * (-(c.gen lam' Y z)) ∂γ) atTop
        (𝓝 (∫ z, f z * (-(c.gen lam' Y z)) ∂γ)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      have hb : ∀ n, dist (∫ z, (u n).eval z * (-(c.gen lam' Y z)) ∂γ)
          (∫ z, f z * (-(c.gen lam' Y z)) ∂γ) ≤
          (eLpNorm (fun z => (u n).eval z - f z) 2 γ).toReal * (eLpNorm (fun z => -(c.gen lam' Y z)) 2 γ).toReal := by
        intro n
        have hi1 : Integrable (fun z => (u n).eval z * (-(c.gen lam' Y z))) γ :=
          ((u n).memLp_eval).integrable_mul hneg
        have hi2 : Integrable (fun z => f z * (-(c.gen lam' Y z))) γ := hf.integrable_mul hneg
        rw [Real.dist_eq, ← integral_sub hi1 hi2]
        have e : (fun z => (u n).eval z * (-(c.gen lam' Y z)) - f z * (-(c.gen lam' Y z))) =
            fun z => ((u n).eval z - f z) * (-(c.gen lam' Y z)) := by funext z; ring
        rw [e]
        exact abs_integral_mul_le_L2 (((u n).memLp_eval).sub hf) hneg
      refine squeeze_zero (fun n => dist_nonneg) hb ?_
      have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hu
      simpa using h0.mul_const (eLpNorm (fun z => -(c.gen lam' Y z)) 2 γ).toReal
    have hlim : Tendsto (fun n => ENNReal.ofReal
        (2 * ∫ z, (u n).eval z * (-(c.gen lam' Y z)) ∂γ - c.formR lam' γ)) atTop
        (𝓝 (ENNReal.ofReal a)) :=
      ENNReal.tendsto_ofReal ((hconv.const_mul 2).sub_const _)
    rw [← hlim.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    rw [Cyl.form_eq_ofReal hlam]
    refine ENNReal.ofReal_le_ofReal ?_
    have := two_mul_le_formR hγ hPSD hC hY hlam (u n) c
    linarith
  rw [hform, ← EReal.coe_sub]
  rcases le_or_gt a 0 with h | h
  · exact (EReal.coe_le_coe_iff.mpr h).trans (EReal.coe_ennreal_nonneg _)
  · calc ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ - c.formR lam' γ : ℝ) : EReal)
        = ((ENNReal.ofReal a : ℝ≥0∞) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left h.le]
      _ ≤ (gaussForm lam' γ f : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hkey

/-- **The easy direction of (8.8)**: `sup_c (2∫ f(-Lc) - ℰ(c)) ≤ ℰ_∞(f)`. -/
theorem sup_le_gaussForm (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) {lam' : ℕ → ℝ}
    (hlam : ∀ i, 0 ≤ lam' i) {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen lam' Y z)) ∂γ : ℝ) : EReal) -
        (c.form lam' γ : EReal)) ≤ (gaussForm lam' γ f : EReal) :=
  iSup_le fun c => two_integral_sub_form_le hγ hPSD hC hY hlam hf c

end generic

section paper
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
  (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
  (h21 : Prop21Conclusion V W μ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C)
include hyp hμ he h21 hC

/-- The easy direction of (8.8) for the paper's data, given Proposition 2.1. -/
theorem sup_le_gaussForm_of_prop21 {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) :
    (⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift lam) γ : EReal)) ≤ (gaussForm (lamShift lam) γ f : EReal) :=
  sup_le_gaussForm hγ (blockMat_posSemidef_of_prop21 hyp hμ he h21 hC) hC hY
    (fun i => he.lam_nonneg' (i + 1)) hf

/-- **Statement-level reduction of (8.8)**: the duality follows from the hard inequality
`ℰ_∞(f) ≤ sup_c (2∫ f(-Lc) - ℰ(c))`. -/
theorem form_duality_of_le_sup {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat W μ e) γ i (Y i))
    {f : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ)
    (hge : (gaussForm (lamShift lam) γ f : EReal) ≤
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift lam) γ : EReal)) :
    (gaussForm (lamShift lam) γ f : EReal) =
      ⨆ c : Cyl, ((2 * ∫ z, f z * (-(c.gen (lamShift lam) Y z)) ∂γ : ℝ) : EReal) -
        (c.form (lamShift lam) γ : EReal) :=
  le_antisymm hge (sup_le_gaussForm_of_prop21 hyp hμ he h21 hC hγ hY hf)

end paper

end SharpLSI
