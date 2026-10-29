import FullLabeledLSI.Paper.Sec8NoInt3
import FullLabeledLSI.Paper.Sec8Agree
import FullLabeledLSI.Paper.Sec3Dilute
import FullLabeledLSI.Paper.Sec3Equi
import FullLabeledLSI.Paper.Sec3DiluteA

/-!
# Section 8.5: the mean-field quantities for `W = 0`

For `W = 0` the dissipation of a density `ρ` is the relative Fisher information `I(ρ|μ)`, the
gap is `H(ρ|μ)`, and the multi-species gap and dissipation are the `θ`-averages of the single
species ones.  Consequently `r_ms = r_* = r_LS(μ)`.
-/

open MeasureTheory InformationTheory Filter Topology SharpLSI
open scoped ENNReal

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {KV KW : ℝ}

theorem convDens_zero' (ρ : Torus d → ℝ) : convDens (fun _ _ => (0 : ℝ)) ρ = fun _ => 0 := by
  funext x; simp [convDens]

theorem speciesDiss_zero' (V : Torus d → ℝ) (ρa ρb : Torus d → ℝ) :
    speciesDiss V (fun _ _ => (0 : ℝ)) ρa ρb = dissipation V (fun _ _ => (0 : ℝ)) ρa := by
  unfold speciesDiss dissipation
  rw [convDens_zero', convDens_zero']

theorem msDiss_zero' (V : Torus d → ℝ) (F : Family d) :
    msDiss V (fun _ _ => (0 : ℝ)) F =
      ∑ a, ENNReal.ofReal (F.θ a) * dissipation V (fun _ _ => (0 : ℝ)) (F.ρ a) := by
  unfold msDiss
  simp_rw [speciesDiss_zero']

theorem potE_bar (hV : Continuous V) {F : Family d} (hF : F.Admissible) :
    potE V (densMeasure F.bar) = ∑ a, F.θ a * potE V (densMeasure (F.ρ a)) := by
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hV
  have hint : ∀ a, Integrable (fun x => F.ρ a x * V x) (haar d) := fun a =>
    (rho_integrable F hF a).mul_bdd (c := BV) hV.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBV x)
  unfold potE
  rw [integral_densMeasure' (bar_nonneg F hF) (bar_integral F hF)]
  have e : (fun x => F.bar x * V x) = fun x => ∑ a, F.θ a * (F.ρ a x * V x) := by
    funext x; simp only [Family.bar, Finset.sum_mul, mul_assoc]
  rw [e, integral_finsetSum _ fun a _ => (hint a).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, integral_densMeasure' (hF.2.2 a).1 (hF.2.2 a).2.1]

section Mu

variable (hyp : Hyp V (fun _ _ => (0 : ℝ)) KV KW) {μ : ProbabilityMeasure (Torus d)}
  (hμ : IsMinimizer V (fun _ _ => (0 : ℝ)) μ)
include hyp hμ

/-- The force term of the equilibrium density vanishes against the score. -/
theorem w0_force_ae :
    MemH1 (haar d) (fun x => Real.sqrt (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) x)) ∧
    HasWeakGrad (fun x => V x + convDens (fun _ _ => (0 : ℝ))
      (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))) x) ∧
    ∀ᵐ x ∂haar d, ∀ k, 2 * weakGrad (fun y => Real.sqrt
        (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) y)) x k +
      Real.sqrt (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) x) *
        weakGrad (fun y => V y + convDens (fun _ _ => (0 : ℝ))
          (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))) y) x k = 0 := by
  set q := elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) with hq
  have h0 := dissipation_elDens_eq_zero hyp hμ
  rw [← hq] at h0
  by_cases hc : MemH1 (haar d) (fun x => Real.sqrt (q x)) ∧
      HasWeakGrad (fun x => V x + convDens (fun _ _ => (0 : ℝ)) q x)
  · refine ⟨hc.1, hc.2, ?_⟩
    unfold dissipation at h0
    rw [if_pos hc] at h0
    have hm : AEMeasurable (fun x => ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (q y)) x k +
        Real.sqrt (q x) * weakGrad (fun y => V y + convDens (fun _ _ => (0 : ℝ)) q y) x k) ^ 2))
        (haar d) := by
      refine ENNReal.measurable_ofReal.comp_aemeasurable (Finset.aemeasurable_fun_sum _ fun k _ => ?_)
      have h1 := (isWeakGrad_weakGrad hc.1.1).aestronglyMeasurable_grad k
      have h2 := (isWeakGrad_weakGrad hc.2).aestronglyMeasurable_grad k
      have h3 := hc.1.2.1.aestronglyMeasurable
      exact (((h1.aemeasurable.const_mul 2).add (h3.aemeasurable.mul h2.aemeasurable))).pow_const 2
    have := (lintegral_eq_zero_iff' hm).1 h0
    filter_upwards [this] with x hx k
    have hx' : ∑ k, (2 * weakGrad (fun y => Real.sqrt (q y)) x k +
        Real.sqrt (q x) * weakGrad (fun y => V y + convDens (fun _ _ => (0 : ℝ)) q y) x k) ^ 2 = 0 := by
      refine le_antisymm (by simpa using hx) (Finset.sum_nonneg fun k _ => sq_nonneg _)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)).1 hx' k (Finset.mem_univ k)
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  · unfold dissipation at h0
    rw [if_neg hc] at h0
    exact absurd h0 (by simp)

theorem w0_diss_eq_relFisher {ρ : Torus d → ℝ}
    (hρH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    dissipation V (fun _ _ => (0 : ℝ)) ρ =
      relFisher ρ (elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))) := by
  set q := elDens V (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) with hq
  obtain ⟨hqH, hqW, hae⟩ := w0_force_ae hyp hμ
  rw [← hq] at hqH hqW hae
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))
  rw [← hq] at hqm hqpos hq1
  have hfun : (fun x => V x + convDens (fun _ _ => (0 : ℝ)) ρ x) =
      (fun x => V x + convDens (fun _ _ => (0 : ℝ)) q x) := by
    funext x; simp [convDens_zero']
  have hac : densMeasure ρ ≪ densMeasure q :=
    (withDensity_absolutelyContinuous _ _).trans (haar_ac_densMeasure hqpos hq1)
  unfold dissipation relFisher
  rw [if_pos ⟨hρH, by rw [hfun]; exact hqW⟩, if_pos ⟨hac, hρH, hqH⟩, hfun]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
  have hk := hx k
  have hsc : score q x k = 2 * weakGrad (fun y => Real.sqrt (q y)) x k / Real.sqrt (q x) := by
    simp only [score, if_pos (hqpos x)]
  have hΦ : weakGrad (fun y => V y + convDens (fun _ _ => (0 : ℝ)) q y) x k =
      -(2 * weakGrad (fun y => Real.sqrt (q y)) x k / Real.sqrt (q x)) := by
    field_simp
    linarith
  rw [hsc, hΦ]
  ring

theorem w0_species_bound {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hρH : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    2 * (rLS (μ : Measure (Torus d)) * klDiv (densMeasure ρ) (μ : Measure (Torus d))) ≤
      dissipation V (fun _ _ => (0 : ℝ)) ρ := by
  rw [w0_diss_eq_relFisher hyp hμ hρH]
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := fun _ _ => (0 : ℝ)) (μ : Measure (Torus d))
  obtain ⟨-, hqH1⟩ := memH1_sqrt_of_lipschitz hc hb hL
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V (fun _ _ => (0 : ℝ)) μ) :=
    minimizer_eq_elDensity hyp hμ
  have hρm : AEMeasurable ρ (haar d) := by
    have h1 := hρH.2.1.aestronglyMeasurable.aemeasurable.pow_const 2
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Real.sq_sqrt (hρ0 x)]
  have key := rLS_mul_klDiv_le hρm hρ0 hc hb hρ1 hq1 hqm hρH hqH1
  rw [← hμq] at key
  exact key


theorem w0_gap_eq (ρ : ProbabilityMeasure (Torus d)) :
    gap V (fun _ _ => (0 : ℝ)) (ρ : Measure (Torus d)) =
      ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) := by
  have h := gap_eq_aux hyp hμ ρ
  have hJ : Jfun (fun _ _ => (0 : ℝ)) (μ : Measure (Torus d)) (ρ : Measure (Torus d)) = 0 := by
    simp [Jfun, interE, centeredKernel, convMeas]
  rw [h, hJ]; simp

theorem w0_msGap {F : Family d} (hF : F.Admissible) :
    msGap V (fun _ _ => (0 : ℝ)) F = ((∑ a, ENNReal.ofReal (F.θ a) *
      klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) := by
  have hρp : ∀ a, IsProbabilityMeasure (densMeasure (F.ρ a)) := fun a =>
    isProbabilityMeasure_densMeasure' (hF.2.2 a).1 (hF.2.2 a).2.1
  have hKm : ∀ a, klDiv (densMeasure (F.ρ a)) (haar d) ≠ ⊤ := fun a =>
    klDiv_densMeasure_ne_top_of_memH1 (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2
  set c : ℝ := (Fstar V (fun _ _ => (0 : ℝ))).toReal with hc
  have hFs : Fstar V (fun _ _ => (0 : ℝ)) = (c : EReal) := Fstar_eq_coe hyp
  have hga : ∀ a, gap V (fun _ _ => (0 : ℝ)) (densMeasure (F.ρ a)) =
      (((klDiv (densMeasure (F.ρ a)) (haar d)).toReal + potE V (densMeasure (F.ρ a)) - c : ℝ) :
        EReal) := fun a => by
    have hE : energyMF V (fun _ _ => (0 : ℝ)) (densMeasure (F.ρ a)) =
        potE V (densMeasure (F.ρ a)) := by simp [energyMF, interE]
    rw [gap_eq_coe hyp (hKm a), hE]
  have hgb : ∀ a, gap V (fun _ _ => (0 : ℝ)) (densMeasure (F.ρ a)) =
      ((klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) := fun a =>
    w0_gap_eq hyp hμ ⟨densMeasure (F.ρ a), hρp a⟩
  have hKμ : ∀ a, klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) ≠ ⊤ ∧
      (klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d))).toReal =
        (klDiv (densMeasure (F.ρ a)) (haar d)).toReal + potE V (densMeasure (F.ρ a)) - c :=
    fun a => by
      have h := (hgb a).symm.trans (hga a)
      have hne : klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) ≠ ⊤ := fun ht => by
        rw [ht, EReal.coe_ennreal_top] at h
        exact EReal.coe_ne_top _ h.symm
      refine ⟨hne, ?_⟩
      have := congrArg EReal.toReal h
      rw [EReal.toReal_coe_ennreal, EReal.toReal_coe] at this
      exact this
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  have hSt : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKm a)
  have hTt : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) :
      ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKμ a).1
  have hSr : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) : ℝ≥0∞).toReal =
      ∑ a, F.θ a * (klDiv (densMeasure (F.ρ a)) (haar d)).toReal := by
    rw [ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKm a)]
    exact Finset.sum_congr rfl fun a _ => by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 a)]
  have hTr : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d)) :
      ℝ≥0∞).toReal = ∑ a, F.θ a * (klDiv (densMeasure (F.ρ a)) (μ : Measure (Torus d))).toReal := by
    rw [ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKμ a).1]
    exact Finset.sum_congr rfl fun a _ => by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 a)]
  have hpb := potE_bar hyp.continuous_V hF
  have hmsGap : msGap V (fun _ _ => (0 : ℝ)) F =
      (((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) : ℝ≥0∞).toReal +
        potE V (densMeasure F.bar) - c : ℝ) : EReal) := by
    unfold msGap
    rw [hFs, ← EReal.coe_ennreal_toReal hSt]
    simp [EReal.coe_add, EReal.coe_sub, interE]
  rw [hmsGap, ← EReal.coe_ennreal_toReal hTt, EReal.coe_eq_coe_iff, hTr, hSr, hpb]
  simp_rw [(hKμ _).2]
  have : ∑ a, F.θ a * c = c := by rw [← Finset.sum_mul, hF.2.1, one_mul]
  have e : ∑ a, F.θ a * ((klDiv (densMeasure (F.ρ a)) (haar d)).toReal +
      potE V (densMeasure (F.ρ a)) - c) = ∑ a, F.θ a * (klDiv (densMeasure (F.ρ a)) (haar d)).toReal
      + ∑ a, F.θ a * potE V (densMeasure (F.ρ a)) - ∑ a, F.θ a * c := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [e, this]

end Mu

end Sec8
end SharpLSI.FL
