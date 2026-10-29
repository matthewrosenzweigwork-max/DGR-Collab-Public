import FullLabeledLSI.Paper.Lem25Ent
import Mathlib.Probability.Moments.Variance

/-!
# Lemma 2.5, part 2: signed truncation and variance of the truncated function

* `truncR A`, the signed truncation `(-A) ∨ (s ∧ A)`; it is `1`-Lipschitz.
* `trunc_var_lower`: if `∫ h = 0`, `∫ h² = 1` and `∫_{h² > A²} h² ≤ ε ≤ 1`, the truncation
  `g = truncR A ∘ h` has `Var(g) ≥ 1 - 2 √ε` (the manuscript's `inf_N Var(h_N^{(M)}) → 1`).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace SharpLSI.FL

/-- Signed truncation at level `A`. -/
noncomputable def truncR (A s : ℝ) : ℝ := max (-A) (min s A)

theorem truncR_lipschitz (A : ℝ) : LipschitzWith 1 (truncR A) := by
  unfold truncR
  exact (LipschitzWith.id.min_const A).const_max (-A)

theorem abs_truncR_le {A : ℝ} (hA : 0 ≤ A) (s : ℝ) : |truncR A s| ≤ A := by
  unfold truncR
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

theorem truncR_eq_of_abs_le {A : ℝ} {s : ℝ} (h : |s| ≤ A) : truncR A s = s := by
  unfold truncR
  rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_right h.1]

theorem sq_sub_truncR_le {A : ℝ} (hA : 0 ≤ A) (s : ℝ) : (s - truncR A s) ^ 2 ≤ s ^ 2 := by
  unfold truncR
  rcases le_total s (-A) with h | h
  · rw [min_eq_left (by linarith), max_eq_left h]
    nlinarith
  · rcases le_total s A with h2 | h2
    · rw [min_eq_left h2, max_eq_right h]; simp; positivity
    · rw [min_eq_right h2, max_eq_right (by linarith)]
      nlinarith

variable {α : Type*} [MeasurableSpace α]

theorem sq_integral_le_integral_sq (P : Measure α) [IsProbabilityMeasure P] {D : α → ℝ}
    (hD : MemLp D 2 P) : (∫ x, D x ∂P) ^ 2 ≤ ∫ x, D x ^ 2 ∂P := by
  have h := ProbabilityTheory.variance_nonneg D P
  rw [ProbabilityTheory.variance_eq_sub hD] at h
  simpa using h

theorem trunc_var_lower (P : Measure α) [IsProbabilityMeasure P] {h : α → ℝ} (hh : MemLp h 2 P)
    (h0 : ∫ x, h x ∂P = 0) (h1 : ∫ x, h x ^ 2 ∂P = 1) {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (htail : ∫⁻ x in {x | A ^ 2 < h x ^ 2}, ENNReal.ofReal (h x ^ 2) ∂P ≤ ENNReal.ofReal ε) :
    1 - 2 * Real.sqrt ε ≤
      (∫ x, truncR A (h x) ^ 2 ∂P) - (∫ x, truncR A (h x) ∂P) ^ 2 := by
  set g : α → ℝ := fun x => truncR A (h x) with hgdef
  set D : α → ℝ := fun x => h x - g x with hDdef
  have hhm : AEStronglyMeasurable h P := hh.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g P :=
    (truncR_lipschitz A).continuous.comp_aestronglyMeasurable hhm
  have hgb : ∀ x, ‖g x‖ ≤ A := fun x => by
    simpa [Real.norm_eq_abs, hgdef] using abs_truncR_le hA.le (h x)
  have hgL : MemLp g 2 P := MemLp.of_bound hgm A (Filter.Eventually.of_forall hgb)
  have hDL : MemLp D 2 P := hh.sub hgL
  have hh_int : Integrable h P := hh.integrable (by norm_num)
  have hg_int : Integrable g P := hgL.integrable (by norm_num)
  have hh2 : Integrable (fun x => h x ^ 2) P := hh.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) P := hgL.integrable_sq
  have hD2 : Integrable (fun x => D x ^ 2) P := hDL.integrable_sq
  -- `∫ D² ≤ ε`
  have hDsq : ∫ x, D x ^ 2 ∂P ≤ ε := by
    have hsupp : (fun x => ENNReal.ofReal (D x ^ 2)).support ⊆ {x | A ^ 2 < h x ^ 2} := by
      intro x hx
      by_contra hxn
      have hxn' : h x ^ 2 ≤ A ^ 2 := not_lt.1 hxn
      have : |h x| ≤ A := abs_le_of_sq_le_sq' hxn' hA.le |> fun h => abs_le.2 h
      have : D x = 0 := by simp [hDdef, hgdef, truncR_eq_of_abs_le this]
      exact hx (by simp [this])
    have step : ∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂P ≤ ENNReal.ofReal ε := by
      rw [← setLIntegral_eq_of_support_subset hsupp]
      refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) htail
      exact sq_sub_truncR_le hA.le (h x)
    rw [← ofReal_integral_eq_lintegral_ofReal hD2
      (Filter.Eventually.of_forall fun x => sq_nonneg _)] at step
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).1 step
  set θ := Real.sqrt ε with hθ
  have hθ0 : 0 < θ := Real.sqrt_pos.2 hε
  have hθ2 : θ ^ 2 = ε := Real.sq_sqrt hε.le
  have hθ1 : θ ≤ 1 := by
    rw [hθ]; exact Real.sqrt_le_one.2 hε1 |> fun h => by simpa using h
  -- `∫ g² ≥ (1 - θ)²`
  have hg2low : (1 - θ) ^ 2 ≤ ∫ x, g x ^ 2 ∂P := by
    have hpt : ∀ x, (1 - θ) * h x ^ 2 - (1 / θ - 1) * D x ^ 2 ≤ g x ^ 2 := by
      intro x
      have hid : g x ^ 2 - ((1 - θ) * h x ^ 2 - (1 / θ - 1) * D x ^ 2) =
          (θ * h x - D x) ^ 2 / θ := by
        have : g x = h x - D x := by simp [hDdef]
        rw [this]; field_simp; ring
      have : 0 ≤ (θ * h x - D x) ^ 2 / θ := by positivity
      linarith
    have k1 : Integrable (fun x => (1 - θ) * h x ^ 2) P := hh2.const_mul (1 - θ)
    have k2 : Integrable (fun x => (1 / θ - 1) * D x ^ 2) P := hD2.const_mul (1 / θ - 1)
    have := integral_mono (f := fun x => (1 - θ) * h x ^ 2 - (1 / θ - 1) * D x ^ 2)
      (g := fun x => g x ^ 2) (by exact k1.sub k2) hg2 hpt
    rw [integral_sub k1 k2, integral_const_mul, integral_const_mul, h1] at this
    have h3 : (1 / θ - 1) * ∫ x, D x ^ 2 ∂P ≤ (1 / θ - 1) * θ ^ 2 := by
      refine mul_le_mul_of_nonneg_left (hDsq.trans hθ2.ge) ?_
      rw [sub_nonneg, le_div_iff₀ hθ0]; linarith
    have h4 : (1 / θ - 1) * θ ^ 2 = θ - θ ^ 2 := by field_simp
    nlinarith
  -- `(∫ g)² ≤ ε`
  have hmean : (∫ x, g x ∂P) ^ 2 ≤ ε := by
    have : ∫ x, g x ∂P = -∫ x, D x ∂P := by
      have : ∫ x, D x ∂P = ∫ x, h x ∂P - ∫ x, g x ∂P := integral_sub hh_int hg_int
      rw [h0] at this; linarith
    rw [this, neg_sq]
    exact (sq_integral_le_integral_sq P hDL).trans hDsq
  show 1 - 2 * θ ≤ (∫ x, g x ^ 2 ∂P) - (∫ x, g x ∂P) ^ 2
  nlinarith

end SharpLSI.FL
