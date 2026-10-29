import SharpSymmetricLSI.Paper.Defective7
import SharpSymmetricLSI.Paper.GroundT2
import SharpSymmetricLSI.Paper.ProductDissipation

/-!
# R03 (Proposition 2.2), part 8: `√ρ` and the dissipation of densities bounded below

* `isWeakGrad_sqrt_of_ge`: if `∇ρ = g` and `ρ ≥ c > 0` then `∇√ρ = g / (2√ρ)` (chain rule with a
  smooth function equal to `√·` on `[c/2, ∞)`, built from `phiCutH`).
* `dissipation_eq_of_ge`: for such a probability density with `g ∈ L²`,
  `D(ρ) = ∫ ρ |g/ρ + ∇V + b_ρ|²` (`b_ρ = ∇(W * ρ)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- A smooth function equal to `√t` for `t ≥ a`. -/
noncomputable def sqrtCut (a t : ℝ) : ℝ := Real.sqrt (a / 2 * (phiCutH 1 (2 * t / a - 3) + 3))

theorem sqrtCut_inner_ge {a : ℝ} (ha : 0 < a) (t : ℝ) :
    a / 2 ≤ a / 2 * (phiCutH 1 (2 * t / a - 3) + 3) := by
  have := phiCutH_ge 1 (2 * t / a - 3)
  have h : (1 : ℝ) ≤ phiCutH 1 (2 * t / a - 3) + 3 := by linarith
  nlinarith

theorem sqrtCut_eq {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) : sqrtCut a t = Real.sqrt t := by
  unfold sqrtCut
  rw [phiCutH_eq (by rw [le_sub_iff_add_le, le_div_iff₀ ha]; linarith)]
  congr 1; field_simp; ring

theorem contDiff_sqrtCut {a : ℝ} (ha : 0 < a) : ContDiff ℝ 1 (sqrtCut a) := by
  have hi : ContDiff ℝ 1 (fun t : ℝ => a / 2 * (phiCutH 1 (2 * t / a - 3) + 3)) :=
    contDiff_const.mul (((contDiff_phiCutH 1).comp (by fun_prop)).add contDiff_const)
  exact hi.sqrt fun t => (lt_of_lt_of_le (by positivity) (sqrtCut_inner_ge ha t)).ne'

theorem hasDerivAt_sqrtCut {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (sqrtCut a) (deriv (phiCutH 1) (2 * t / a - 3) /
      (2 * Real.sqrt (a / 2 * (phiCutH 1 (2 * t / a - 3) + 3)))) t := by
  have hφ : HasDerivAt (phiCutH 1) (deriv (phiCutH 1) (2 * t / a - 3)) (2 * t / a - 3) :=
    ((contDiff_phiCutH 1).differentiable one_ne_zero _).hasDerivAt
  have hu : HasDerivAt (fun t : ℝ => 2 * t / a - 3) (2 / a) t := by
    have := ((hasDerivAt_id t).const_mul 2).div_const a |>.sub_const 3
    simpa using this
  have hin : HasDerivAt (fun t : ℝ => a / 2 * (phiCutH 1 (2 * t / a - 3) + 3))
      (a / 2 * (deriv (phiCutH 1) (2 * t / a - 3) * (2 / a))) t :=
    ((hφ.comp t hu).add_const 3).const_mul (a / 2)
  have hne : a / 2 * (phiCutH 1 (2 * t / a - 3) + 3) ≠ 0 :=
    (lt_of_lt_of_le (by positivity) (sqrtCut_inner_ge ha t)).ne'
  have e : sqrtCut a = fun t => Real.sqrt (a / 2 * (phiCutH 1 (2 * t / a - 3) + 3)) := rfl
  rw [e]
  convert hin.sqrt hne using 1
  field_simp

theorem exists_bound_deriv_sqrtCut {a : ℝ} (ha : 0 < a) : ∃ L, ∀ t, |deriv (sqrtCut a) t| ≤ L := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_phiCutH 1
  refine ⟨M / (2 * Real.sqrt (a / 2)), fun t => ?_⟩
  have h1 : Real.sqrt (a / 2) ≤ Real.sqrt (a / 2 * (phiCutH 1 (2 * t / a - 3) + 3)) :=
    Real.sqrt_le_sqrt (sqrtCut_inner_ge ha t)
  have h2 : 0 < Real.sqrt (a / 2) := Real.sqrt_pos.mpr (by positivity)
  have hden : (0 : ℝ) < 2 * Real.sqrt (a / 2 * (phiCutH 1 (2 * t / a - 3) + 3)) := by linarith
  rw [(hasDerivAt_sqrtCut ha t).deriv, abs_div, abs_of_pos hden]
  exact div_le_div₀ hM0 (hM _) (by positivity) (by linarith)

theorem deriv_sqrtCut_of_gt {a t : ℝ} (ha : 0 < a) (ht : a < t) :
    deriv (sqrtCut a) t = 1 / (2 * Real.sqrt t) := by
  have h : sqrtCut a =ᶠ[𝓝 t] Real.sqrt := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact sqrtCut_eq ha (le_of_lt hs)
  rw [h.deriv_eq, (Real.hasDerivAt_sqrt (by linarith : t ≠ 0)).deriv]

section sqrt
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`∇√ρ = ∇ρ / (2√ρ)`** for `ρ ≥ c > 0`. -/
theorem isWeakGrad_sqrt_of_ge {ρ : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad ρ g) (hρi : Integrable ρ volume) (hgi : ∀ k, Integrable (fun y => g y k) volume)
    {c : ℝ} (hc : 0 < c) (hρc : ∀ y, c ≤ ρ y) :
    IsWeakGrad (fun y => Real.sqrt (ρ y)) (fun y k => g y k / (2 * Real.sqrt (ρ y))) := by
  have ha : 0 < c / 2 := by positivity
  obtain ⟨L, hL⟩ := exists_bound_deriv_sqrtCut ha
  have hcomp := isWeakGrad_comp h hρi hgi (contDiff_sqrtCut ha) hL
  convert hcomp using 1
  · funext y; rw [sqrtCut_eq ha (by linarith [hρc y])]
  · funext y k
    rw [deriv_sqrtCut_of_gt ha (by linarith [hρc y])]
    ring

end sqrt

section diss
variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **`D(ρ) = ∫ ρ |∇ρ/ρ + ∇V + b_ρ|²`** for an `H¹`-type density bounded below. -/
theorem dissipation_eq_of_ge (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ}
    (hρm : Measurable ρ) (h : IsWeakGrad ρ g) (hgm : ∀ k, Measurable fun x => g x k)
    (hg2 : ∀ k, MemLp (fun x => g x k) 2 (haar d)) {c C : ℝ} (hc : 0 < c) (hρc : ∀ x, c ≤ ρ x)
    (hρC : ∀ x, ρ x ≤ C) (h1 : ∫ x, ρ x ∂haar d = 1) :
    dissipation V W ρ = ∫⁻ x, ENNReal.ofReal (ρ x * ∑ k, (g x k / ρ x + lipGrad V x k +
      bForceL W ρ x k) ^ 2) ∂haar d := by
  have hρ0 : ∀ x, 0 < ρ x := fun x => hc.trans_le (hρc x)
  have hρi : Integrable ρ (haar d) := Integrable.of_bound hρm.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_pos (hρ0 x)]; exact hρC x)
  have hgi : ∀ k, Integrable (fun x => g x k) (haar d) := fun k => (hg2 k).integrable one_le_two
  have hS := isWeakGrad_sqrt_of_ge h hρi hgi hc hρc
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCw := isWeakGrad_convDens hyp hρm hρi (W := W)
  have hVCw := hVw.add hCw
  -- `√ρ ∈ H¹`
  have hmem : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) := by
    refine ⟨⟨_, hS⟩, MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable
      hρm.aestronglyMeasurable) (Real.sqrt C) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt (hρC x)), ?_⟩
    have hL : MemLp (fun x => ∑ k, (1 / (2 * Real.sqrt c)) * ‖g x k‖) 2 (haar d) :=
      memLp_finsetSum _ fun k _ => ((hg2 k).norm).const_mul _
    refine hL.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hS⟩).aestronglyMeasurable_sqNorm) ?_
    filter_upwards [weakGrad_ae_eq hS] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Finset.sum_nonneg fun k _ => by positivity), hx]
    have hsc : Real.sqrt c ≤ Real.sqrt (ρ x) := Real.sqrt_le_sqrt (hρc x)
    have hsc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hpt : ∀ k, |g x k / (2 * Real.sqrt (ρ x))| ≤ (1 / (2 * Real.sqrt c)) * ‖g x k‖ := fun k => by
      have hd : (0 : ℝ) < 2 * Real.sqrt (ρ x) := by linarith
      rw [abs_div, abs_of_pos hd, Real.norm_eq_abs, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith)
    calc Real.sqrt (sqNorm fun k => g x k / (2 * Real.sqrt (ρ x)))
        ≤ ∑ k, |g x k / (2 * Real.sqrt (ρ x))| := by
          rw [Real.sqrt_le_left (Finset.sum_nonneg fun k _ => abs_nonneg _)]
          unfold sqNorm
          calc ∑ k, (g x k / (2 * Real.sqrt (ρ x))) ^ 2 = ∑ k, |g x k / (2 * Real.sqrt (ρ x))| ^ 2 := by
                simp_rw [sq_abs]
            _ ≤ (∑ k, |g x k / (2 * Real.sqrt (ρ x))|) ^ 2 :=
                Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
      _ ≤ ∑ k, (1 / (2 * Real.sqrt c)) * ‖g x k‖ := Finset.sum_le_sum fun k _ => hpt k
  unfold dissipation
  rw [if_pos ⟨hmem, ⟨_, hVCw⟩⟩]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hS, weakGrad_ae_eq hVCw] with x h1 h2
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, h2]
  have hs0 : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.mpr (hρ0 x)
  have hsq : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ0 x).le
  have key : ∀ (a gg t : ℝ), 0 < t →
      (2 * (gg / (2 * t)) + t * a) ^ 2 = t ^ 2 * (gg / t ^ 2 + a) ^ 2 := by
    intro a gg t ht
    first
    | (field_simp; done)
    | (field_simp; ring)
  rw [key _ _ _ hs0, hsq]
  ring

end diss

end SharpLSI
