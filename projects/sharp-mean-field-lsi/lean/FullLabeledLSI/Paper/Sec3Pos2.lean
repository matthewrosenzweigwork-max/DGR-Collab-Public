import FullLabeledLSI.Paper.Sec3Pos
import FullLabeledLSI.Paper.Sec3PosAlg
import SharpSymmetricLSI.Statements.R06_Upper_Bound

/-!
# Proposition 3.4: the quotient bound for one admissible family
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem gap_densMeasure_nonneg (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    0 ≤ gap V W (densMeasure F.bar) := by
  haveI : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' (bar_nonneg F hF) (bar_integral F hF)
  have hle : Fstar V W ≤ freeEnergy V W (densMeasure F.bar) :=
    iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ) ⟨densMeasure F.bar, this⟩
  unfold gap
  have hFs : Fstar V W = ((Fstar V W).toReal : EReal) := Fstar_eq_coe hyp
  exact (EReal.sub_nonneg (Or.inr (by rw [hFs]; exact EReal.coe_ne_top _))
    (Or.inr (by rw [hFs]; exact EReal.coe_ne_bot _))).2 hle


theorem rStar_ne_top (hd : 1 ≤ d) (hyp : Hyp V W KV KW) : rStar V W ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := admissible_nonempty hd hyp
  obtain ⟨h1, h2⟩ := gap_lt_top_of_admissible hyp hρ
  have hg0 : 0 < (gap V W (densMeasure ρ)).toENNReal := EReal.toENNReal_pos_iff.2 hρ.2.2.2
  have hgt : (gap V W (densMeasure ρ)).toENNReal ≠ ⊤ :=
    EReal.toENNReal_ne_top_iff.2 h1.ne
  refine ne_top_of_le_ne_top ?_ (iInf₂_le ρ hρ)
  exact ENNReal.div_ne_top h2.ne (by simpa using hg0.ne')

theorem rLS_mu_ne_zero (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) : rLS (μ : Measure (Torus d)) ≠ 0 := by
  obtain ⟨cq, Cq, L, hcq, hbq, hLq⟩ := elDens_data hyp hμ
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hμq : (μ : Measure (Torus d)) = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    minimizer_eq_elDensity hyp hμ
  have h := rLS_lower hcq hbq hq1 hqm
  rw [← congrArg rLS hμq] at h
  intro h0
  rw [h0] at h
  have h2 : 0 < cq / Cq := div_pos hcq ((hcq.trans_le (hbq 0).1).trans_le (hbq 0).2)
  exact absurd (ENNReal.ofReal_pos.2 h2) (not_lt.2 h)

theorem msRatio_lower (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ ρ : ProbabilityMeasure (Torus d), klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
      (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) ≤
        gap V W ρ)
    {B : ℝ} (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2)
    (F : Family d) (hF : MsAdmissible V W F) :
    ((rStar V W)⁻¹ + 2 * (rLS (μ : Measure (Torus d)))⁻¹ *
        (1 + ENNReal.ofReal (B ^ 2 / c) * (rStar V W)⁻¹))⁻¹ ≤
      msDiss V W F / (2 * (msGap V W F).toENNReal) := by
  obtain ⟨hAd, hpos⟩ := hF
  set q := elDens V W (μ : Measure (Torus d)) with hqdef
  obtain ⟨cq, Cq, L, hcq, hbq, hLq⟩ := elDens_data hyp hμ
  obtain ⟨hqm, hqpos, hq1⟩ := elDensity_props hyp (W := W) (μ : Measure (Torus d))
  have hμq : (μ : Measure (Torus d)) = densMeasure q := minimizer_eq_elDensity hyp hμ
  obtain ⟨-, hqH1⟩ := memH1_sqrt_of_lipschitz hcq hbq hLq
  set r := rStar V W with hrdef
  set a := rLS (μ : Measure (Torus d)) with hadef
  have ha_eq : a = rLS (densMeasure q) := congrArg rLS hμq
  have hr0 : r ≠ 0 := hr.ne'
  have hrt : r ≠ ⊤ := rStar_ne_top hd hyp
  have ha0 : a ≠ 0 := by
    have := rLS_lower hcq hbq hq1 hqm
    rw [← ha_eq] at this
    intro h
    rw [h] at this
    have h2 : 0 < cq / Cq := div_pos hcq ((hcq.trans_le (hbq 0).1).trans_le (hbq 0).2)
    exact absurd (ENNReal.ofReal_pos.2 h2) (not_lt.2 this)
  have hg0 : 0 ≤ gap V W (densMeasure F.bar) := gap_densMeasure_nonneg hyp F hAd
  set g := gap V W (densMeasure F.bar) with hg
  set S : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) *
    klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) with hS
  obtain ⟨hmsG, -⟩ := msGap_decomp F hyp hAd
  have hG : (msGap V W F).toENNReal = g.toENNReal + S := by
    rw [hmsG, EReal.toENNReal_add hg0 (EReal.coe_ennreal_nonneg S), EReal.toENNReal_coe]
  have hDdec := msDiss_decomp F hyp hAd
  set D := msDiss V W F with hD
  have hDt : D ≠ ⊤ := (msDiss_lt_top_of_admissible hyp hAd).ne
  have hDbar : dissipation V W F.bar ≤ D := by rw [hDdec]; exact le_self_add
  have hGpos : 0 < g.toENNReal + S := by rw [← hG]; exact EReal.toENNReal_pos_iff.2 hpos
  rw [hG]
  -- (A) `2 r G(ρ̄) ≤ D(ρ̄)`
  have hA : 2 * r * g.toENNReal ≤ dissipation V W F.bar := by
    by_cases hgz : g.toENNReal = 0
    · rw [hgz]; simp
    have hgpos : 0 < g := EReal.toENNReal_pos_iff.1 (pos_iff_ne_zero.2 hgz)
    have hadm : Admissible V W F.bar :=
      ⟨bar_nonneg F hAd, bar_integral F hAd, memH1_sqrtBar F hAd, hgpos⟩
    have h1 := iInf₂_le (f := fun ρ (_ : ρ ∈ {ρ | Admissible V W ρ}) =>
      dissipation V W ρ / (2 * (gap V W (densMeasure ρ)).toENNReal)) F.bar hadm
    have hgt : g.toENNReal ≠ ⊤ := EReal.toENNReal_ne_top_iff.2
      (gap_lt_top_of_admissible hyp hadm).1.ne
    have h2 : r * (2 * g.toENNReal) ≤ dissipation V W F.bar := by
      refine (ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hgz)) (Or.inl ?_)).1 h1
      exact ENNReal.mul_ne_top (by norm_num) hgt
    calc 2 * r * g.toENNReal = r * (2 * g.toENNReal) := by ring
      _ ≤ _ := h2
  -- (B) coercivity: `c H(ρ̄|μ) ≤ G(ρ̄)`
  set H : ℝ≥0∞ := klDiv (densMeasure F.bar) (densMeasure q) with hH
  haveI hPbar : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' (bar_nonneg F hAd) (bar_integral F hAd)
  have hcB : ENNReal.ofReal c * H ≤ g.toENNReal := by
    have hk : klDiv (densMeasure F.bar) (haar d) ≠ ⊤ :=
      klDiv_densMeasure_ne_top_of_memH1 (bar_nonneg F hAd) (bar_integral F hAd)
        (memH1_sqrtBar F hAd)
    have h := hcoer ⟨densMeasure F.bar, hPbar⟩ hk
    have e : klDiv (densMeasure F.bar) (μ : Measure (Torus d)) = H :=
      congrArg (klDiv (densMeasure F.bar)) hμq
    have h' := EReal.toENNReal_le_toENNReal h
    change (↑c * ((klDiv ((⟨densMeasure F.bar, hPbar⟩ : ProbabilityMeasure (Torus d)) :
      Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal)).toENNReal ≤
      g.toENNReal at h'
    rw [EReal.toENNReal_mul (EReal.coe_nonneg.2 hc.le), EReal.real_coe_toENNReal, EReal.toENNReal_coe] at h'
    simpa [e] using h'
  -- (C) Pinsker: `(∫|ρ̄ - q|)² ≤ 2 H`
  set M : ℝ := ∫ x, |F.bar x - q x| ∂haar d with hM
  have hqi : Integrable q (haar d) := integrable_of_integral_eq_one' hq1
  have hMe : ENNReal.ofReal M = ∫⁻ x, ‖F.bar x - q x‖ₑ ∂haar d := by
    rw [hM]
    have := ofReal_integral_norm_eq_lintegral_enorm ((bar_integrable hAd).sub hqi)
    simpa [Real.norm_eq_abs] using this
  have hP : ENNReal.ofReal M ^ 2 ≤ 2 * H := by
    rw [hMe]
    exact l1_sq_le_two_klDiv (bar_aemeasurable F hAd) hqm (bar_nonneg F hAd) hqpos
      (bar_integral F hAd) hq1
  -- (D) species LSI and the Fisher bound
  have hθ0 : ∀ a', 0 ≤ F.θ a' := fun a' => (hAd.1 a').le
  have hS1 : S ≤ ∑ a', ENNReal.ofReal (F.θ a') *
      klDiv (densMeasure (F.ρ a')) (densMeasure q) :=
    entropy_compensation F hAd hqm.aemeasurable hqpos hq1
  have hSa : 2 * (a * ∑ a', ENNReal.ofReal (F.θ a') *
      klDiv (densMeasure (F.ρ a')) (densMeasure q)) ≤
      ∑ a', ENNReal.ofReal (F.θ a') * relFisher (F.ρ a') q := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun a' _ => ?_
    have h := rLS_mul_klDiv_le (rho_aemeasurable F hAd a') (fun x => (hAd.2.2 a').1 x) hcq hbq
      (hAd.2.2 a').2.1 hq1 hqm (hAd.2.2 a').2.2 hqH1
    calc 2 * (a * (ENNReal.ofReal (F.θ a') *
          klDiv (densMeasure (F.ρ a')) (densMeasure q)))
        = ENNReal.ofReal (F.θ a') * (2 * (a * klDiv (densMeasure (F.ρ a')) (densMeasure q))) := by
          ring
      _ ≤ ENNReal.ofReal (F.θ a') * relFisher (F.ρ a') q := by
          rw [ha_eq]; gcongr
  set E : ℝ := 2 * (B ^ 2 * M ^ 2) with hE
  have hFis : ∑ a', ENNReal.ofReal (F.θ a') * relFisher (F.ρ a') q ≤ 2 * D + ENNReal.ofReal E := by
    calc ∑ a', ENNReal.ofReal (F.θ a') * relFisher (F.ρ a') q
        ≤ ∑ a', ENNReal.ofReal (F.θ a') *
            (2 * speciesDiss V W (F.ρ a') F.bar + ENNReal.ofReal E) :=
          Finset.sum_le_sum fun a' _ => by
            gcongr
            exact relFisher_le hyp hμ hB F hAd a'
      _ = 2 * D + ENNReal.ofReal E := by
          have h1 : ∑ a', ENNReal.ofReal (F.θ a') = 1 := by
            rw [← ENNReal.ofReal_sum_of_nonneg fun a' _ => hθ0 a', hAd.2.1]; simp
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [h1, one_mul]
          congr 1
          rw [hD, msDiss, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a' _ => by ring
  have hE2 : ENNReal.ofReal E = 2 * ENNReal.ofReal (B ^ 2 * M ^ 2) := by
    rw [hE, ENNReal.ofReal_mul (by norm_num)]; simp
  have hSD : a * S ≤ D + ENNReal.ofReal (B ^ 2 * M ^ 2) := by
    have h1 : 2 * (a * S) ≤ 2 * (D + ENNReal.ofReal (B ^ 2 * M ^ 2)) := by
      calc 2 * (a * S) ≤ 2 * (a * ∑ a', ENNReal.ofReal (F.θ a') *
            klDiv (densMeasure (F.ρ a')) (densMeasure q)) := by gcongr
        _ ≤ 2 * D + ENNReal.ofReal E := hSa.trans hFis
        _ = 2 * (D + ENNReal.ofReal (B ^ 2 * M ^ 2)) := by rw [hE2]; ring
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by simp)).1 h1
  -- (E) `ofReal (B² M²) ≤ ofReal (B²/c) r⁻¹ D`
  set Bq : ℝ≥0∞ := ENNReal.ofReal (B ^ 2) with hBq
  have hXe : ENNReal.ofReal (B ^ 2 * M ^ 2) = Bq * ENNReal.ofReal M ^ 2 := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (integral_nonneg fun _ => abs_nonneg _)]
  have hcr : ENNReal.ofReal c * r * ENNReal.ofReal (B ^ 2 * M ^ 2) ≤ Bq * D := by
    rw [hXe]
    calc ENNReal.ofReal c * r * (Bq * ENNReal.ofReal M ^ 2)
        ≤ ENNReal.ofReal c * r * (Bq * (2 * H)) := by gcongr
      _ = Bq * (r * (2 * (ENNReal.ofReal c * H))) := by ring
      _ ≤ Bq * (r * (2 * g.toENNReal)) := by gcongr
      _ = Bq * (2 * r * g.toENNReal) := by ring
      _ ≤ Bq * D := by gcongr; exact hA.trans hDbar
  have hcrne0 : ENNReal.ofReal c * r ≠ 0 := mul_ne_zero (by simpa using hc) hr0
  have hcrnet : ENNReal.ofReal c * r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hrt
  have hX : ENNReal.ofReal (B ^ 2 * M ^ 2) ≤ ENNReal.ofReal (B ^ 2 / c) * r⁻¹ * D := by
    have h1 := (ENNReal.mul_le_iff_le_inv hcrne0 hcrnet).1 hcr
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.mul_inv (Or.inr hrt) (Or.inr hr0)]
    rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv]
    ring
  -- (F) conclusion
  have hYt : 1 + ENNReal.ofReal (B ^ 2 / c) * r⁻¹ ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 hr0)⟩
  refine final_quotient_ineq hr0 hrt ha0 hDt hYt hGpos (hA.trans hDbar) ?_
  calc a * S ≤ D + ENNReal.ofReal (B ^ 2 * M ^ 2) := hSD
    _ ≤ D + ENNReal.ofReal (B ^ 2 / c) * r⁻¹ * D := by gcongr
    _ = D * (1 + ENNReal.ofReal (B ^ 2 / c) * r⁻¹) := by ring


theorem rMs_lower_bound_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ ρ : ProbabilityMeasure (Torus d), klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ →
      (c : EReal) * ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ℝ≥0∞) : EReal) ≤
        gap V W ρ)
    {B : ℝ} (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2) :
    0 < rMs V W ∧
      ((rStar V W)⁻¹ + 2 * (rLS (μ : Measure (Torus d)))⁻¹ *
          (1 + ENNReal.ofReal (B ^ 2 / c) * (rStar V W)⁻¹))⁻¹ ≤ rMs V W := by
  have hbound : ((rStar V W)⁻¹ + 2 * (rLS (μ : Measure (Torus d)))⁻¹ *
      (1 + ENNReal.ofReal (B ^ 2 / c) * (rStar V W)⁻¹))⁻¹ ≤ rMs V W := by
    unfold rMs
    exact le_iInf₂ fun F hF => msRatio_lower hd hyp hr hμ hc hcoer hB F hF
  refine ⟨lt_of_lt_of_le (ENNReal.inv_pos.2 ?_) hbound, hbound⟩
  refine ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 hr.ne', ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.2 (rLS_mu_ne_zero hyp hμ)))
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 hr.ne')⟩)⟩

end SharpLSI.FL
