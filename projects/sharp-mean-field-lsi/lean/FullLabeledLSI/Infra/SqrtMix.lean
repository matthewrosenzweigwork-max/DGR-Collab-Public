import SharpSymmetricLSI.Paper.R36Meas1
import SharpSymmetricLSI.Paper.Defective15

/-!
# Weak gradient of `√f` for an unbounded nonnegative `f`

Variant of the argument inside `dissipation_eq_fisher` (R36Meas1) without a bound on `f`:
if `f ≥ 0` is integrable with an integrable weak gradient `w` and the candidate
`h = w/(2√f)` on `{f > 0}` (`0` elsewhere) lies in `L²`, then `h` is a weak gradient of `√f`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI.FL

open SharpLSI

theorem abs_sig_le_sqrt {δ r : ℝ} (hδ : 0 ≤ δ) : |sig δ r| ≤ Real.sqrt |r| + Real.sqrt δ := by
  unfold sig
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 : Real.sqrt (r ^ 2 + δ ^ 2) ≤ |r| + δ := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [abs_nonneg r, sq_abs r]
  refine (Real.sqrt_le_sqrt h1).trans ?_
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have := Real.sq_sqrt (abs_nonneg r)
  have := Real.sq_sqrt hδ
  nlinarith [Real.sqrt_nonneg |r|, Real.sqrt_nonneg δ, mul_nonneg (Real.sqrt_nonneg |r|) (Real.sqrt_nonneg δ)]


variable {d : ℕ}

/-- The candidate gradient `w/(2√f)` of `√f` (zero where `f = 0`). -/
noncomputable def sqrtGradCand (f : Torus d → ℝ) (w : Torus d → Fin d → ℝ) (x : Torus d)
    (j : Fin d) : ℝ :=
  if 0 < f x then w x j / (2 * Real.sqrt (f x)) else 0

theorem isWeakGrad_sqrt_L2 {f : Torus d → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable f (haar d)) {w : Torus d → Fin d → ℝ} (hw : IsWeakGrad f w)
    (hwi : ∀ k, Integrable (fun y => w y k) (haar d))
    (hh2 : ∀ j, MemLp (fun x => sqrtGradCand f w x j) 2 (haar d)) :
    IsWeakGrad (fun y => Real.sqrt (f y)) (sqrtGradCand f w) := by
  have hm : ∀ j, AEStronglyMeasurable (fun x => sqrtGradCand f w x j) (haar d) := fun j =>
    (hh2 j).aestronglyMeasurable
  have hhi : ∀ k, Integrable (fun y => sqrtGradCand f w y k) (haar d) := fun k =>
    (hh2 k).integrable one_le_two
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδn : ∀ n, 0 < δn n := fun n => by positivity
  have hδn1 : ∀ n, δn n ≤ 1 := fun n => by
    simp only [δn]; rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  -- `√f` is integrable
  have hsqm : Measurable fun y => Real.sqrt (f y) := Real.continuous_sqrt.measurable.comp hf
  have hsqi : Integrable (fun y => Real.sqrt (f y)) (haar d) := by
    refine Integrable.mono' (hfi.add (integrable_const 1)) hsqm.aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := Real.sqrt_le_sqrt (show f y ≤ (f y + 1) ^ 2 by nlinarith [h0 y])
    rw [Real.sqrt_sq (by linarith [h0 y])] at this
    exact this.trans (by simp only [Pi.add_apply]; linarith [h0 y])
  have hFG : ∀ n, IsWeakGrad (fun y => sig (δn n) (f y)) (fun y k => sigp (δn n) (f y) * w y k) :=
    fun n => by
      have := isWeakGrad_comp hw hfi hwi (contDiff_sig (hδn n)) (L := 1 / (2 * Real.sqrt (δn n)))
        fun t => by rw [deriv_sig (hδn n)]; exact abs_sigp_le (hδn n) t
      simpa only [deriv_sig (hδn n)] using this
  -- domination for `sig`
  have hsigb : ∀ n y, |sig (δn n) (f y)| ≤ Real.sqrt (f y) + 1 := fun n y => by
    refine (abs_sig_le_sqrt (hδn n).le).trans ?_
    rw [abs_of_nonneg (h0 y)]
    have : Real.sqrt (δn n) ≤ 1 := by
      rw [Real.sqrt_le_one]; exact hδn1 n
    linarith
  have hFi : ∀ n, Integrable (fun y => sig (δn n) (f y)) (haar d) := fun n =>
    Integrable.mono' (hsqi.add (integrable_const 1))
      ((contDiff_sig (hδn n)).continuous.measurable.comp hf).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hsigb n y)
  have hGi : ∀ n k, Integrable (fun y => sigp (δn n) (f y) * w y k) (haar d) := fun n k =>
    (hwi k).bdd_mul (c := 1 / (2 * Real.sqrt (δn n)))
      ((contDiff_sig (hδn n)).continuous_deriv le_rfl |> fun hc => by
        rw [deriv_sig (hδn n)] at hc; exact (hc.measurable.comp hf).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_sigp_le (hδn n) _)
  have hlimδ := tendsto_delta_seq
  have hFc : Tendsto (fun n => ∫⁻ y, ‖sig (δn n) (f y) - Real.sqrt (f y)‖ₑ ∂haar d) atTop (𝓝 0) := by
    have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
      (F := fun n y => sig (δn n) (f y)) (f := fun y => Real.sqrt (f y))
      (bound := fun y => Real.sqrt (f y) + 1)
      (fun n => (hFi n).aestronglyMeasurable) (hsqi.add (integrable_const 1)).hasFiniteIntegral
      (fun n => Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hsigb n y)
      (Eventually.of_forall fun y => (tendsto_sig (h0 y)).comp hlimδ)
    simpa only [ofReal_norm] using this
  have hGc : ∀ k, Tendsto (fun n => ∫⁻ y, ‖sigp (δn n) (f y) * w y k - sqrtGradCand f w y k‖ₑ ∂haar d)
      atTop (𝓝 0) := fun k => by
    have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
      (F := fun n y => sigp (δn n) (f y) * w y k) (f := fun y => sqrtGradCand f w y k)
      (bound := fun y => |sqrtGradCand f w y k|)
      (fun n => (hGi n k).aestronglyMeasurable) (hhi k).abs.hasFiniteIntegral
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        rcases (h0 y).lt_or_eq with hy | hy
        · simp only [sqrtGradCand, if_pos hy]
          rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (f y)), div_eq_mul_inv,
            mul_comm (|w y k|)]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := abs_sigp_le_of_pos (hδn n) hy
          rwa [one_div] at this
        · rw [← hy, sigp_zero, abs_zero, zero_mul]; exact abs_nonneg _)
      (Eventually.of_forall fun y => by
        rcases (h0 y).lt_or_eq with hy | hy
        · simp only [sqrtGradCand, if_pos hy]
          have := ((tendsto_sigp hy).comp hlimδ).mul_const (w y k)
          have e : w y k / (2 * Real.sqrt (f y)) = 1 / (2 * Real.sqrt (f y)) * w y k := by ring
          rw [e]; exact this
        · have hfy : ¬ (0 < f y) := by rw [← hy]; exact lt_irrefl 0
          simp only [sqrtGradCand, if_neg hfy]
          rw [← hy]; simp only [sigp_zero, zero_mul]; exact tendsto_const_nhds)
    simpa only [ofReal_norm] using this
  exact isWeakGrad_of_tendsto hFG hFi hGi hsqi hhi hFc hGc


/-- `isWeakGrad_sqrt_L2` for an a.e. measurable, a.e. nonnegative `f`. -/
theorem isWeakGrad_sqrt_L2' {f : Torus d → ℝ} (hf : AEMeasurable f (haar d))
    (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (hfi : Integrable f (haar d)) {w : Torus d → Fin d → ℝ}
    (hw : IsWeakGrad f w) (hwi : ∀ k, Integrable (fun y => w y k) (haar d))
    (hh2 : ∀ j, MemLp (fun x => sqrtGradCand f w x j) 2 (haar d)) :
    IsWeakGrad (fun y => Real.sqrt (f y)) (sqrtGradCand f w) := by
  set f' : Torus d → ℝ := fun x => max (hf.mk f x) 0 with hf'
  have hf'm : Measurable f' := hf.measurable_mk.max measurable_const
  have hee : f' =ᵐ[haar d] f := by
    filter_upwards [hf.ae_eq_mk, h0] with x hx hx0
    simp only [hf']
    rw [← hx]; exact max_eq_left hx0
  have hw' : IsWeakGrad f' w := hw.congr_ae hee.symm
  have hcand : ∀ j, (fun x => sqrtGradCand f' w x j) =ᵐ[haar d] fun x => sqrtGradCand f w x j :=
    fun j => by
      filter_upwards [hee] with x hx
      simp only [sqrtGradCand, hx]
  have hh2' : ∀ j, MemLp (fun x => sqrtGradCand f' w x j) 2 (haar d) := fun j =>
    (hh2 j).ae_eq (hcand j).symm
  have hmain := isWeakGrad_sqrt_L2 hf'm (fun x => le_max_right _ _) (hfi.congr hee.symm) hw' hwi hh2'
  have hsq : (fun y => Real.sqrt (f' y)) =ᵐ[haar d] fun y => Real.sqrt (f y) := by
    filter_upwards [hee] with x hx; rw [hx]
  exact (hmain.congr_ae hsq).congr_grad hcand

end SharpLSI.FL
