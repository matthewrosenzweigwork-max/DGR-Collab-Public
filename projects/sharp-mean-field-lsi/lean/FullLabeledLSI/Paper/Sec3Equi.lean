import FullLabeledLSI.Paper.Sec3Pos2

/-!
# Proposition 3.3 (≥): congruence lemmas and the equilibrium dissipation

`dissipation`, `relFisher` only depend on the density up to a.e. equality; `D(μ) = 0` and
`G(μ) = 0` for the minimizer.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem memH1_sqrt_congr {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ')
    (hρ : MemH1 (haar d) fun x => Real.sqrt (ρ x)) : MemH1 (haar d) fun x => Real.sqrt (ρ' x) := by
  have hae : (fun x => Real.sqrt (ρ x)) =ᵐ[haar d] fun x => Real.sqrt (ρ' x) := by
    filter_upwards [h] with x hx; rw [hx]
  exact (memH1_congr_ae (Measure.AbsolutelyContinuous.refl _) (Measure.AbsolutelyContinuous.refl _)
    hρ hae).1

theorem dissipation_congr_ae {ρ ρ' : Torus d → ℝ} (h : ρ =ᵐ[haar d] ρ') :
    dissipation V W ρ = dissipation V W ρ' := by
  have hc : convDens W ρ = convDens W ρ' := convDens_congr_ae h
  have hae : (fun x => Real.sqrt (ρ x)) =ᵐ[haar d] fun x => Real.sqrt (ρ' x) := by
    filter_upwards [h] with x hx; rw [hx]
  unfold dissipation
  rw [hc]
  by_cases hcond : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) ∧
      HasWeakGrad (fun x => V x + convDens W ρ' x)
  · have hcond' : MemH1 (haar d) (fun x => Real.sqrt (ρ' x)) ∧
        HasWeakGrad (fun x => V x + convDens W ρ' x) := ⟨memH1_sqrt_congr h hcond.1, hcond.2⟩
    rw [if_pos hcond, if_pos hcond']
    obtain ⟨-, hw⟩ := weakGrad_congr_ae hcond.1.1 hae
    refine lintegral_congr_ae ?_
    filter_upwards [hw, h] with x hx hx2
    rw [hx, hx2]
  · have hcond' : ¬ (MemH1 (haar d) (fun x => Real.sqrt (ρ' x)) ∧
        HasWeakGrad (fun x => V x + convDens W ρ' x)) := fun h' =>
      hcond ⟨memH1_sqrt_congr (h.symm) h'.1, h'.2⟩
    rw [if_neg hcond, if_neg hcond']

theorem relFisher_congr_ae {ρa ρb ρb' : Torus d → ℝ} (h : ρb =ᵐ[haar d] ρb') :
    relFisher ρa ρb = relFisher ρa ρb' := by
  have hdm : densMeasure ρb = densMeasure ρb' :=
    withDensity_congr_ae (by filter_upwards [h] with x hx; rw [hx])
  have hae : (fun x => Real.sqrt (ρb x)) =ᵐ[haar d] fun x => Real.sqrt (ρb' x) := by
    filter_upwards [h] with x hx; rw [hx]
  unfold relFisher
  rw [hdm]
  by_cases hcond : densMeasure ρa ≪ densMeasure ρb' ∧ MemH1 (haar d) (fun x => Real.sqrt (ρa x)) ∧
      MemH1 (haar d) (fun x => Real.sqrt (ρb x))
  · have hcond' : densMeasure ρa ≪ densMeasure ρb' ∧ MemH1 (haar d) (fun x => Real.sqrt (ρa x)) ∧
        MemH1 (haar d) (fun x => Real.sqrt (ρb' x)) :=
      ⟨hcond.1, hcond.2.1, memH1_sqrt_congr h hcond.2.2⟩
    rw [if_pos hcond, if_pos hcond']
    obtain ⟨-, hw⟩ := weakGrad_congr_ae hcond.2.2.1 hae
    refine lintegral_congr_ae ?_
    filter_upwards [hw, h] with x hx hx2
    simp only [score, hx, hx2]
  · have hcond' : ¬ (densMeasure ρa ≪ densMeasure ρb' ∧ MemH1 (haar d) (fun x => Real.sqrt (ρa x)) ∧
        MemH1 (haar d) (fun x => Real.sqrt (ρb' x))) := fun h' =>
      hcond ⟨h'.1, h'.2.1, memH1_sqrt_congr (h.symm) h'.2.2⟩
    rw [if_neg hcond, if_neg hcond']


theorem aux_score (q s P : ℝ) (hs : 0 < s) (hq : s ^ 2 = q) :
    2 * (-(q * P) / (2 * s)) + s * P = 0 := by
  subst hq; field_simp; ring

section Equil

variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
include hyp hμ

theorem dissipation_elDens_eq_zero :
    dissipation V W (elDens V W (μ : Measure (Torus d))) = 0 := by
  set q := elDens V W (μ : Measure (Torus d)) with hqdef
  obtain ⟨c, C, L, hc, hb, hL⟩ := elDens_data hyp hμ
  obtain ⟨hS, hq1⟩ := memH1_sqrt_of_lipschitz hc hb hL
  obtain ⟨hqm, hqpos, hqint⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hqi : Integrable q (haar d) := integrable_of_integral_eq_one' hqint
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hforce : IsWeakGrad (fun x => V x + convDens W q x) (fun x k => lipGrad V x k + bForceL W q x k) :=
    hVw.add (isWeakGrad_convDens' hyp hqi (W := W))
  unfold dissipation
  rw [if_pos ⟨hq1, ⟨_, hforce⟩⟩]
  have h1 := weakGrad_ae_eq hS
  have h2 := weakGrad_ae_eq hforce
  have h3 := lipGrad_elDens_ae hyp hμ
  have h4 := lipGrad_Phi_ae hyp hμ
  refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
  filter_upwards [h1, h2, h3, h4] with x e1 e2 e3 e4
  have hs : 0 < Real.sqrt (q x) := Real.sqrt_pos.2 (hqpos x)
  have hs2 : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (hqpos x).le
  have hk : ∀ k, 2 * weakGrad (fun y => Real.sqrt (q y)) x k +
      Real.sqrt (q x) * weakGrad (fun y => V y + convDens W q y) x k = 0 := fun k => by
    rw [e1, e2]
    simp only
    rw [e3 k, e4 k]
    exact aux_score _ _ _ hs hs2
  simp [hk]

theorem gap_minimizer_eq_zero : gap V W (μ : Measure (Torus d)) = 0 := by
  have hFs : Fstar V W = ((Fstar V W).toReal : EReal) := Fstar_eq_coe hyp
  unfold gap
  rw [show freeEnergy V W (μ : Measure (Torus d)) = Fstar V W from hμ]
  rw [hFs]
  exact EReal.sub_self (EReal.coe_ne_top _) (EReal.coe_ne_bot _)


theorem rLS_le_quotient (F : Family d) (hAd : F.Admissible)
    (hbar : densMeasure F.bar = (μ : Measure (Torus d))) (hpos : 0 < msGap V W F) :
    rLS (μ : Measure (Torus d)) ≤ msDiss V W F / (2 * (msGap V W F).toENNReal) := by
  set q := elDens V W (μ : Measure (Torus d)) with hqdef
  obtain ⟨cq, Cq, L, hcq, hbq, hLq⟩ := elDens_data hyp hμ
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hμq : (μ : Measure (Torus d)) = densMeasure q := minimizer_eq_elDensity hyp hμ
  obtain ⟨-, hqH1⟩ := memH1_sqrt_of_lipschitz hcq hbq hLq
  have hbq' : densMeasure F.bar = densMeasure q := hbar.trans hμq
  -- `ρ̄ = q` a.e.
  have hbarq : F.bar =ᵐ[haar d] q := by
    have hm1 : AEMeasurable (fun x => ENNReal.ofReal (F.bar x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (bar_aemeasurable F hAd)
    have hm2 : AEMeasurable (fun x => ENNReal.ofReal (q x)) (haar d) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hqm.aemeasurable
    have hfin : ∫⁻ x, ENNReal.ofReal (F.bar x) ∂haar d ≠ ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (bar_integrable hAd)
        (Filter.Eventually.of_forall (bar_nonneg F hAd))]
      exact ENNReal.ofReal_ne_top
    have := (withDensity_eq_iff hm1 hm2 hfin).1 hbq'
    filter_upwards [this] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (bar_nonneg F hAd x) (hqpos x).le).1 hx
  -- decompositions
  obtain ⟨hmsG, -⟩ := msGap_decomp F hyp hAd
  have hDdec := msDiss_decomp F hyp hAd
  have hg : gap V W (densMeasure F.bar) = 0 := by
    rw [hbar]; exact gap_minimizer_eq_zero hyp hμ
  have hD0 : dissipation V W F.bar = 0 := by
    rw [dissipation_congr_ae hbarq]; exact dissipation_elDens_eq_zero hyp hμ
  set S : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) *
    klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) with hS
  have hG : (msGap V W F).toENNReal = S := by
    rw [hmsG, hg, zero_add, EReal.toENNReal_coe]
  have hI : msDiss V W F = ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) q := by
    rw [hDdec, hD0, zero_add]
    exact Finset.sum_congr rfl fun a _ => by rw [relFisher_congr_ae hbarq]
  have hSq : S = ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure q) := by
    rw [hS, hbq']
  rw [hG, hI]
  have hSpos : 0 < S := by rw [← hG]; exact EReal.toENNReal_pos_iff.2 hpos
  have hSt : S ≠ ⊤ := by
    rw [← hG]
    exact EReal.toENNReal_ne_top_iff.2 (msGap_bounds_of_admissible hyp hAd).1.ne
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hSpos.ne')) (Or.inl (ENNReal.mul_ne_top (by norm_num) hSt))]
  rw [hSq]
  calc rLS (μ : Measure (Torus d)) * (2 * ∑ a, ENNReal.ofReal (F.θ a) *
        klDiv (densMeasure (F.ρ a)) (densMeasure q))
      = ∑ a, ENNReal.ofReal (F.θ a) * (2 * (rLS (densMeasure q) *
          klDiv (densMeasure (F.ρ a)) (densMeasure q))) := by
        rw [congrArg rLS hμq, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ ≤ ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) q := by
        refine Finset.sum_le_sum fun a _ => ?_
        gcongr
        exact rLS_mul_klDiv_le (rho_aemeasurable F hAd a) (fun x => (hAd.2.2 a).1 x) hcq hbq
          (hAd.2.2 a).2.1 hq1 hqm (hAd.2.2 a).2.2 hqH1

end Equil

end SharpLSI.FL
