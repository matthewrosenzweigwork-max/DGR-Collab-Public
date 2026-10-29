import FullLabeledLSI.Paper.AdmissibleFinite

/-!
# Proposition 3.1, entropy part (3.1)

`∑ₐ θₐ H(ρₐ|m) = H(ρ̄|m) + ∑ₐ θₐ H(ρₐ|ρ̄)` in `ℝ≥0∞`, from the pointwise identity
`∑ₐ θₐ klFun ρₐ = klFun ρ̄ + ∑ₐ θₐ ρ̄ klFun(ρₐ/ρ̄)`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

theorem klFun_ratio_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    b * klFun (a / b) = a * (Real.log a - Real.log b) - a + b := by
  unfold klFun
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hb.ne']
    field_simp
    ring

theorem klFun_decomp {q : ℕ} (θ ρ : Fin q → ℝ) (hθ : ∀ a, 0 < θ a) (hθ1 : ∑ a, θ a = 1)
    (hρ : ∀ a, 0 ≤ ρ a) :
    ∑ a, θ a * klFun (ρ a) = klFun (∑ a, θ a * ρ a) +
      ∑ a, θ a * ((∑ b, θ b * ρ b) * klFun (ρ a / ∑ b, θ b * ρ b)) := by
  set bar := ∑ b, θ b * ρ b with hbar
  have hbar0 : 0 ≤ bar := Finset.sum_nonneg fun a _ => mul_nonneg (hθ a).le (hρ a)
  rcases hbar0.eq_or_lt with h0 | hpos
  · have hz : ∀ a, ρ a = 0 := fun a => by
      have h1 : θ a * ρ a ≤ bar := Finset.single_le_sum (f := fun b => θ b * ρ b)
        (fun b _ => mul_nonneg (hθ b).le (hρ b)) (Finset.mem_univ a)
      have : θ a * ρ a = 0 := le_antisymm (h0 ▸ h1) (mul_nonneg (hθ a).le (hρ a))
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hθ a).ne'
      · exact h
    rw [← h0]
    simp only [hz, klFun, Real.log_zero, mul_zero, zero_div, zero_add, zero_sub, sub_zero]
    simp [hθ1, ← Finset.mul_sum]
  · have e : ∀ a, θ a * (bar * klFun (ρ a / bar)) =
        θ a * (ρ a * (Real.log (ρ a) - Real.log bar) - ρ a + bar) := fun a => by
      rw [klFun_ratio_mul (hρ a) hpos]
    simp_rw [e]
    have e2 : ∀ a, θ a * (ρ a * (Real.log (ρ a) - Real.log bar) - ρ a + bar) =
        θ a * ρ a * Real.log (ρ a) - Real.log bar * (θ a * ρ a) - θ a * ρ a + bar * θ a :=
      fun a => by ring
    have e3 : ∀ a, θ a * klFun (ρ a) = θ a * ρ a * Real.log (ρ a) + θ a - θ a * ρ a :=
      fun a => by unfold klFun; ring
    simp_rw [e2, e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hbar, hθ1]
    rw [Finset.sum_add_distrib, hθ1]
    unfold klFun
    ring


section Family

variable (F : Family d)

theorem rho_integrable (hF : F.Admissible) (a : Fin F.q) : Integrable (F.ρ a) (haar d) :=
  integrable_of_integral_eq_one' (hF.2.2 a).2.1

theorem bar_nonneg (hF : F.Admissible) (x : Torus d) : 0 ≤ F.bar x :=
  Finset.sum_nonneg fun a _ => mul_nonneg (hF.1 a).le ((hF.2.2 a).1 x)

theorem bar_integral (hF : F.Admissible) : ∫ x, F.bar x ∂haar d = 1 := by
  have : F.bar = fun x => ∑ a, F.θ a * F.ρ a x := rfl
  rw [this, integral_finsetSum _ fun a _ => (rho_integrable F hF a).const_mul _]
  simp_rw [integral_const_mul, (hF.2.2 _).2.1, mul_one]
  exact hF.2.1

theorem theta_rho_le_bar (hF : F.Admissible) (a : Fin F.q) (x : Torus d) :
    F.θ a * F.ρ a x ≤ F.bar x :=
  Finset.single_le_sum (f := fun b => F.θ b * F.ρ b x)
    (fun b _ => mul_nonneg (hF.1 b).le ((hF.2.2 b).1 x)) (Finset.mem_univ a)

theorem rho_eq_zero_of_bar_eq_zero (hF : F.Admissible) (a : Fin F.q) (x : Torus d)
    (h : F.bar x = 0) : F.ρ a x = 0 := by
  have h1 := theta_rho_le_bar F hF a x
  rw [h] at h1
  have h2 : 0 ≤ F.ρ a x := (hF.2.2 a).1 x
  have h3 : F.θ a * F.ρ a x = 0 := le_antisymm h1 (mul_nonneg (hF.1 a).le h2)
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd h (hF.1 a).ne'
  · exact h


theorem bar_aemeasurable (hF : F.Admissible) : AEMeasurable F.bar (haar d) :=
  (bar_integrable hF).aestronglyMeasurable.aemeasurable

theorem rho_aemeasurable (hF : F.Admissible) (a : Fin F.q) : AEMeasurable (F.ρ a) (haar d) :=
  (rho_integrable F hF a).aestronglyMeasurable.aemeasurable

theorem densMeasure_eq_ratio (hF : F.Admissible) (a : Fin F.q) :
    densMeasure (F.ρ a) = (densMeasure F.bar).withDensity
      (fun x => ENNReal.ofReal (F.ρ a x / F.bar x)) := by
  have hb : AEMeasurable (fun x => ENNReal.ofReal (F.bar x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (bar_aemeasurable F hF)
  have hr : AEMeasurable (fun x => ENNReal.ofReal (F.ρ a x / F.bar x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((rho_aemeasurable F hF a).div (bar_aemeasurable F hF))
  unfold densMeasure
  rw [← withDensity_mul₀ hb hr]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  by_cases h : F.bar x = 0
  · rw [rho_eq_zero_of_bar_eq_zero F hF a x h, h]; simp
  · rw [← ENNReal.ofReal_mul (bar_nonneg F hF x)]
    congr 1
    field_simp

theorem klDiv_species (hF : F.Admissible) (a : Fin F.q) :
    klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) =
      ∫⁻ x, ENNReal.ofReal (F.bar x * klFun (F.ρ a x / F.bar x)) ∂haar d := by
  have hb : AEMeasurable (fun x => ENNReal.ofReal (F.bar x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (bar_aemeasurable F hF)
  have hr : AEMeasurable (fun x => ENNReal.ofReal (F.ρ a x / F.bar x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((rho_aemeasurable F hF a).div (bar_aemeasurable F hF))
  have hac : densMeasure (F.ρ a) ≪ densMeasure F.bar := by
    rw [densMeasure_eq_ratio F hF a]; exact withDensity_absolutelyContinuous _ _
  have : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' (bar_nonneg F hF) (bar_integral F hF)
  have : IsProbabilityMeasure (densMeasure (F.ρ a)) :=
    isProbabilityMeasure_densMeasure' (hF.2.2 a).1 (hF.2.2 a).2.1
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  have hrn : (densMeasure (F.ρ a)).rnDeriv (densMeasure F.bar) =ᵐ[densMeasure F.bar]
      fun x => ENNReal.ofReal (F.ρ a x / F.bar x) := by
    rw [densMeasure_eq_ratio F hF a]
    have hrm : AEMeasurable (fun x => ENNReal.ofReal (F.ρ a x / F.bar x)) (densMeasure F.bar) :=
      hr.mono_ac (withDensity_absolutelyContinuous _ _)
    exact Measure.rnDeriv_withDensity₀ _ hrm
  have h1 : ∫⁻ x, ENNReal.ofReal (klFun ((densMeasure (F.ρ a)).rnDeriv (densMeasure F.bar) x).toReal)
      ∂(densMeasure F.bar) =
      ∫⁻ x, ENNReal.ofReal (klFun (F.ρ a x / F.bar x)) ∂(densMeasure F.bar) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal (div_nonneg ((hF.2.2 a).1 x) (bar_nonneg F hF x))]
  rw [h1]
  have hg : AEMeasurable (fun x => ENNReal.ofReal (klFun (F.ρ a x / F.bar x))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_klFun.comp_aemeasurable ((rho_aemeasurable F hF a).div (bar_aemeasurable F hF)))
  unfold densMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hb hg]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (bar_nonneg F hF x)]


theorem entropy_identity (hF : F.Admissible) :
    ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) =
      klDiv (densMeasure F.bar) (haar d) +
        ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) := by
  have hρ0 := fun a => (hF.2.2 a).1
  have hρ1 := fun a => (hF.2.2 a).2.1
  simp_rw [klDiv_densMeasure' (hρ0 _) (hρ1 _), klDiv_species F hF,
    klDiv_densMeasure' (bar_nonneg F hF) (bar_integral F hF)]
  have hm1 : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (klFun (F.ρ a x))) (haar d) := fun a =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_klFun.comp_aemeasurable (rho_aemeasurable F hF a))
  have hm2 : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (F.bar x * klFun (F.ρ a x / F.bar x)))
      (haar d) := fun a =>
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((bar_aemeasurable F hF).mul
        (measurable_klFun.comp_aemeasurable ((rho_aemeasurable F hF a).div (bar_aemeasurable F hF))))
  have hm3 : AEMeasurable (fun x => ENNReal.ofReal (klFun (F.bar x))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (measurable_klFun.comp_aemeasurable (bar_aemeasurable F hF))
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_finsetSum' _ fun a _ => (hm1 a).const_mul _,
    ← lintegral_finsetSum' _ fun a _ => (hm2 a).const_mul _,
    ← lintegral_add_left' hm3]
  refine lintegral_congr fun x => ?_
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  have hk : ∀ a, 0 ≤ klFun (F.ρ a x) := fun a => klFun_nonneg (hρ0 a x)
  have hk2 : ∀ a, 0 ≤ F.bar x * klFun (F.ρ a x / F.bar x) := fun a =>
    mul_nonneg (bar_nonneg F hF x) (klFun_nonneg (div_nonneg (hρ0 a x) (bar_nonneg F hF x)))
  have hd := klFun_decomp F.θ (fun a => F.ρ a x) hF.1 hF.2.1 (fun a => hρ0 a x)
  have hbar : F.bar x = ∑ a, F.θ a * F.ρ a x := rfl
  rw [← hbar] at hd
  have e1 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (klFun (F.ρ a x)) =
      ENNReal.ofReal (∑ a, F.θ a * klFun (F.ρ a x)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a) (hk a)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  have e2 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (F.bar x * klFun (F.ρ a x / F.bar x)) =
      ENNReal.ofReal (∑ a, F.θ a * (F.bar x * klFun (F.ρ a x / F.bar x))) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a) (hk2 a)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  show _ = ENNReal.ofReal (klFun (F.bar x)) + _
  rw [e1, e2, ← ENNReal.ofReal_add (klFun_nonneg (bar_nonneg F hF x))
    (Finset.sum_nonneg fun a _ => mul_nonneg (hθ0 a) (hk2 a)), hd]


/-- Proposition 3.1, parts (3.1) and `0 ≤ G_θ`. -/
theorem msGap_decomp {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (hF : F.Admissible) :
    msGap V W F = gap V W (densMeasure F.bar) +
      ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) : ℝ≥0∞) :
        EReal) ∧ 0 ≤ msGap V W F := by
  set S : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) with hS
  set K : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar)
    with hK
  set H : ℝ≥0∞ := klDiv (densMeasure F.bar) (haar d) with hH
  have hSt : S ≠ ⊤ := by
    refine ENNReal.sum_ne_top.2 fun a _ => ?_
    obtain ⟨h0, h1, hH1⟩ := hF.2.2 a
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (klDiv_densMeasure_ne_top_of_memH1 h0 h1 hH1)
  have hid : S = H + K := entropy_identity F hF
  have hHt : H ≠ ⊤ := fun h => hSt (by rw [hid, h]; simp)
  have hKt : K ≠ ⊤ := fun h => hSt (by rw [hid, h]; simp)
  set R : ℝ := potE V (densMeasure F.bar) + interE W (densMeasure F.bar) (densMeasure F.bar) / 2
    with hR
  set c : ℝ := (Fstar V W).toReal with hc
  have hFs : Fstar V W = (c : EReal) := Fstar_eq_coe hyp
  have hgap : gap V W (densMeasure F.bar) = ((H.toReal + R - c : ℝ) : EReal) := by
    unfold gap freeEnergy
    rw [hFs, ← hH, ← hR, ← EReal.coe_ennreal_toReal hHt]
    simp [EReal.coe_add, EReal.coe_sub]
  have hmsGap : msGap V W F = ((S.toReal + R - c : ℝ) : EReal) := by
    unfold msGap
    rw [hFs, ← hS, ← hR, ← EReal.coe_ennreal_toReal hSt]
    simp [EReal.coe_add, EReal.coe_sub]
  have hKcoe : (K : EReal) = ((K.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hKt).symm
  have hSr : S.toReal = H.toReal + K.toReal := by
    rw [hid, ENNReal.toReal_add hHt hKt]
  refine ⟨?_, ?_⟩
  · rw [hgap, hKcoe, hmsGap, ← EReal.coe_add, EReal.coe_eq_coe_iff, hSr]; ring
  · rw [hmsGap, EReal.coe_nonneg]
    -- `c ≤ H + R` since `F_* ≤ F(ρ̄)`
    have hle : Fstar V W ≤ freeEnergy V W (densMeasure F.bar) := by
      haveI : IsProbabilityMeasure (densMeasure F.bar) :=
        isProbabilityMeasure_densMeasure' (bar_nonneg F hF) (bar_integral F hF)
      exact iInf_le (fun ρ : ProbabilityMeasure (Torus d) => freeEnergy V W ρ)
        ⟨densMeasure F.bar, this⟩
    have h2 : (c : EReal) ≤ ((H.toReal + R : ℝ) : EReal) := by
      rw [← hFs]
      refine hle.trans (le_of_eq ?_)
      unfold freeEnergy
      rw [← hH, ← hR, ← EReal.coe_ennreal_toReal hHt]
      simp [EReal.coe_add]
    rw [EReal.coe_le_coe_iff] at h2
    rw [hSr]
    nlinarith [ENNReal.toReal_nonneg (a := K)]

end Family

end SharpLSI.FL
