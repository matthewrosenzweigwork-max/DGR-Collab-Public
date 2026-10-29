import SharpSymmetricLSI.Paper.AppAFisher3

/-!
# The square root of the heat flow of a density with `√ρ ∈ H¹`

For `√ρ ∈ H¹` with weak gradient `g`, `t > 0` and `H = e^{tΔ}ρ`:
`√H ∈ H¹`, with weak gradient `A = e^{tΔ}(2√ρ g) / (2√H)` (`isWeakGrad_sqrt_heatT`), and
pointwise `|A|² ≤ e^{tΔ}|g|²` (`sqNorm_sqrtHeatGrad_le`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appA_isWeakGrad_congr_grad {u : UnitAddTorus ι → ℝ} {g g' : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (hgg : g =ᵐ[volume] g') : IsWeakGrad u g' where
  locInt := h.locInt
  locInt_grad k := (h.locInt_grad k).congr (by
    filter_upwards [ae_liftT_of_ae hgg] with x hx
    rw [hx])
  ibp φ hφ hφc k := by
    rw [h.ibp φ hφ hφc k]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_liftT_of_ae hgg] with x hx
    rw [hx]

end General

variable {d : ℕ}

/-- The gradient `A = e^{tΔ}(2√ρ g) / (2√(e^{tΔ}ρ))` of `√(e^{tΔ}ρ)`. -/
noncomputable def sqrtHeatGrad (t : ℝ) (ρ : Torus d → ℝ) (y : Torus d) (k : Fin d) : ℝ :=
  heatT t (fun z => 2 * Real.sqrt (ρ z) * weakGrad (fun w => Real.sqrt (ρ w)) z k) y /
    (2 * Real.sqrt (heatT t ρ y))

/-- Common hypotheses: a probability density with `√ρ ∈ H¹`. -/
structure H1Dens (ρ : Torus d → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  one : ∫ x, ρ x ∂haar d = 1
  h1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))

namespace H1Dens

variable {ρ : Torus d → ℝ} (h : H1Dens ρ)
include h

theorem integrable : Integrable ρ (haar d) :=
  Integrable.of_integral_ne_zero (by rw [h.one]; exact one_ne_zero)

theorem isWeakGrad : IsWeakGrad (fun x => Real.sqrt (ρ x)) (weakGrad fun x => Real.sqrt (ρ x)) :=
  appA_isWeakGrad_weakGrad h.h1.1

theorem memLp_grad (k : Fin d) :
    MemLp (fun y => weakGrad (fun x => Real.sqrt (ρ x)) y k) 2 volume := by
  refine h.h1.2.2.mono (appA_aestronglyMeasurable_grad h.isWeakGrad k)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.abs_le_sqrt ?_
  unfold sqNorm
  exact Finset.single_le_sum (f := fun j => weakGrad (fun x => Real.sqrt (ρ x)) y j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ k)

theorem integrable_flux (k : Fin d) :
    Integrable fun y => 2 * Real.sqrt (ρ y) * weakGrad (fun x => Real.sqrt (ρ x)) y k :=
  ((h.h1.2.1.integrable_mul (h.memLp_grad k)).const_mul 2).congr
    (Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)

theorem integrable_sqNorm :
    Integrable fun y => sqNorm (weakGrad (fun x => Real.sqrt (ρ x)) y) := by
  unfold sqNorm; exact integrable_finsetSum _ fun k _ => (h.memLp_grad k).integrable_sq

theorem isWeakGrad_rho :
    IsWeakGrad ρ (fun y k => 2 * Real.sqrt (ρ y) * weakGrad (fun x => Real.sqrt (ρ x)) y k) := by
  have := isWeakGrad_sq h.isWeakGrad h.h1.2.1 h.memLp_grad
  have hρs : (fun y => Real.sqrt (ρ y) ^ 2) = ρ := funext fun y => Real.sq_sqrt (h.nonneg y)
  rwa [hρs] at this

theorem heatT_pos {t : ℝ} (ht : 0 < t) (z : Torus d) : 0 < heatT t ρ z := by
  obtain ⟨c, hc, hlow⟩ := heatT_lower (ι := Fin d) ht
  have := hlow ρ h.integrable (Eventually.of_forall h.nonneg) z
  rw [show ∫ y, ρ y = 1 from h.one, mul_one] at this
  exact lt_of_lt_of_le hc this

/-- `|A|² ≤ e^{tΔ}|g|²` everywhere. -/
theorem sqNorm_sqrtHeatGrad_le {t : ℝ} (ht : 0 < t) (z : Torus d) :
    sqNorm (fun k => sqrtHeatGrad t ρ z k) ≤
      heatT t (fun y => sqNorm (weakGrad (fun x => Real.sqrt (ρ x)) y)) z := by
  have hρs : (fun y => Real.sqrt (ρ y) ^ 2) = ρ := funext fun y => Real.sq_sqrt (h.nonneg y)
  have hHp := h.heatT_pos ht z
  have hA : 0 < heatT t (fun y => Real.sqrt (ρ y) ^ 2) z := by rw [hρs]; exact hHp
  have hpt : sqNorm (fun k => heatT t (fun y => 2 * Real.sqrt (ρ y) *
      weakGrad (fun x => Real.sqrt (ρ x)) y k) z) ≤
      4 * heatT t ρ z * heatT t (fun y => sqNorm (weakGrad (fun x => Real.sqrt (ρ x)) y)) z := by
    unfold sqNorm
    rw [heatT_sum ht _ fun k _ => (h.memLp_grad k).integrable_sq, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := heatT_sq_le ht h.h1.2.1 (h.memLp_grad k) z hA
    rwa [hρs] at this
  have e : sqNorm (fun k => sqrtHeatGrad t ρ z k) =
      sqNorm (fun k => heatT t (fun y => 2 * Real.sqrt (ρ y) *
        weakGrad (fun x => Real.sqrt (ρ x)) y k) z) / (4 * heatT t ρ z) := by
    unfold sqNorm sqrtHeatGrad
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_pow, mul_pow, Real.sq_sqrt hHp.le]; ring
  rw [e, div_le_iff₀ (by positivity)]
  linarith

/-- **`√(e^{tΔ}ρ) ∈ H¹` with weak gradient `A`.** -/
theorem isWeakGrad_sqrt_heatT {t : ℝ} (ht : 0 < t) :
    IsWeakGrad (fun x => Real.sqrt (heatT t ρ x)) (fun y k => sqrtHeatGrad t ρ y k) := by
  set H := heatT t ρ with hHdef
  have hHs : IsSmoothT H := isSmoothT_heatT ht h.integrable
  set sH : Torus d → ℝ := fun x => Real.sqrt (H x) with hsHdef
  have hsHs : ContDiff ℝ ∞ (sH ∘ liftT) := hHs.sqrt fun x => (h.heatT_pos ht _).ne'
  have hsHw := isWeakGrad_of_contDiff (hsHs.of_le (by simp))
  refine appA_isWeakGrad_congr_grad hsHw ?_
  have hclass := weakGrad_ae_eq_of_contDiff (hHs.of_le (by simp) : ContDiff ℝ 1 (H ∘ liftT))
  have hHae := appA_weakGrad_ae_eq (isWeakGrad_heatT ht h.isWeakGrad_rho h.integrable
    h.integrable_flux)
  filter_upwards [hclass, hHae] with y h1 h2
  funext k
  have hd := ((hHs.differentiable (by simp)) (secT y)).hasFDerivAt.sqrt
    (h.heatT_pos ht (liftT (secT y))).ne'
  rw [show (sH ∘ liftT) = fun x => Real.sqrt ((H ∘ liftT) x) from rfl, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Function.comp, liftT_secT]
  have h3 := congrFun (h1.symm.trans h2) k
  rw [h3, sqrtHeatGrad]
  field_simp
  rfl

theorem memH1_sqrt_heatT {t : ℝ} (ht : 0 < t) :
    MemH1 (haar d) (fun x => Real.sqrt (heatT t ρ x)) := by
  have hw := h.isWeakGrad_sqrt_heatT ht
  have hHc : Continuous (heatT t ρ) := continuous_of_comp_liftT (isSmoothT_heatT ht h.integrable).continuous
  have hsHc : Continuous fun x => Real.sqrt (heatT t ρ x) := hHc.sqrt
  have hb : Integrable (heatT t fun y => sqNorm (weakGrad (fun x => Real.sqrt (ρ x)) y)) :=
    integrable_heatT ht h.integrable_sqNorm
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hsHc.continuousOn
    exact MemLp.of_bound hsHc.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (mem_univ x))
  · have hae := appA_weakGrad_ae_eq hw
    have hsq : Integrable fun y => sqNorm (weakGrad (fun x => Real.sqrt (heatT t ρ x)) y) := by
      refine hb.mono' ?_ ?_
      · unfold sqNorm
        exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (appA_aestronglyMeasurable_grad (appA_isWeakGrad_weakGrad ⟨_, hw⟩) k).pow 2
      · filter_upwards [hae] with y hy
        rw [Real.norm_eq_abs, abs_of_nonneg (by unfold sqNorm; positivity), hy]
        exact h.sqNorm_sqrtHeatGrad_le ht y
    have hm : AEStronglyMeasurable
        (fun x => Real.sqrt (sqNorm (weakGrad (fun x => Real.sqrt (heatT t ρ x)) x))) volume :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hsq.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    refine hsq.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.sq_sqrt (by unfold sqNorm; positivity)]

end H1Dens

end SharpLSI
