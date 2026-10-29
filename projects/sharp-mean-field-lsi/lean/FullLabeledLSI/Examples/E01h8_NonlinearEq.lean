import FullLabeledLSI.Examples.E01h6_PoissonFacts
import FullLabeledLSI.Examples.E01h5_Concavity
import FullLabeledLSI.Examples.E01g9_Attain
import FullLabeledLSI.Examples.E01h6_Unique
import FullLabeledLSI.Examples.E01b_LaneA

/-!
# Lane D, Task D: Proposition 9.10 (assembly)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem le_rMs_of_deficit {C : Torus 1 → ℝ} {KV KW : ℝ} (hyp : Hyp zeroV (attrW C) KV KW) {ℓ : ℝ}
    (h : ∀ F : Family 1, F.Admissible → 0 ≤ deficit (attrW C) ℓ F) :
    ENNReal.ofReal ℓ ≤ rMs zeroV (attrW C) := by
  unfold rMs
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨hFa, hpos⟩ := hF
  obtain ⟨hlt, hbot, hDlt⟩ := msGap_msDiss_lt_top (le_refl 1) hyp hFa
  have hd := h F hFa
  unfold deficit at hd
  set g : ℝ := (msGap zeroV (attrW C) F).toReal with hg
  have hgE : msGap zeroV (attrW C) F = (g : EReal) := (EReal.coe_toReal hlt.ne hbot.ne').symm
  have hgpos : 0 < g := by
    rw [hgE] at hpos; exact_mod_cast hpos
  set D : ℝ := (msDiss zeroV (attrW C) F).toReal with hD
  have hDE : msDiss zeroV (attrW C) F = ENNReal.ofReal D := (ENNReal.ofReal_toReal hDlt.ne).symm
  rw [hDE, hgE, EReal.real_coe_toENNReal,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem nonlinear_equality_core
    (hzero : ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW poissonKernel) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1)
    (htrial : ∃ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) ∧ 0 < GR poissonKernel ρ ∧
      DR poissonKernel ρ < aCos * (2 * GR poissonKernel ρ)) :
    0 < rMs zeroV (attrW poissonKernel) ∧ rMs zeroV (attrW poissonKernel) = rStar zeroV (attrW poissonKernel) ∧
      rStar zeroV (attrW poissonKernel) < ENNReal.ofReal aCos ∧
      LamGValue (attrW poissonKernel) (ENNReal.ofReal aCos) ∧
      (∃ ρ : Torus 1 → ℝ, IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
        ¬ (ρ =ᵐ[haar 1] fun _ => 1) ∧ 0 < gap zeroV (attrW poissonKernel) (densMeasure ρ) ∧
        dissipation zeroV (attrW poissonKernel) ρ =
          2 * rStar zeroV (attrW poissonKernel) *
            (gap zeroV (attrW poissonKernel) (densMeasure ρ)).toENNReal) ∧
      Tendsto (fun N => rAll zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) ∧
      Tendsto (fun N => rSym zeroV (attrW poissonKernel) N) atTop (𝓝 (rStar zeroV (attrW poissonKernel))) := by
  have hC : GoodKernel poissonKernel := poisson_good
  have hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (poissonKernel x : ℂ) ∂haar 1).re :=
    fun n hn => (chat_poisson_nonneg_le n hn).1
  have hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 →
      (∫ x, fourier (-n) (x 0) * (poissonKernel x : ℂ) ∂haar 1).re ≤ 1 - δ :=
    ⟨21 / 25, by norm_num, fun n hn => by have := (chat_poisson_nonneg_le n hn).2; show chat poissonKernel n ≤ _; linarith⟩
  have hsup' : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat poissonKernel n ≤ 1 - δ := hsup
  have huniq : HaarUniqueMinimizer (attrW poissonKernel) :=
    haarUnique_of_bound hC abs_poisson_le (by norm_num)
  have hmin0 := huniq.1
  have hatt := scalar_quotient_attainment hC hCpos hsup huniq hzero
  have hrfin := rStar_ne_top hC hmin0
  set r0 : ℝ := (rStar zeroV (attrW poissonKernel)).toReal with hr0def
  have hrr : rStar zeroV (attrW poissonKernel) = ENNReal.ofReal r0 := (ENNReal.ofReal_toReal hrfin).symm
  have hr0 : 0 ≤ r0 := ENNReal.toReal_nonneg
  have haC : 0 < aCos := by unfold aCos; positivity
  -- strict inequality from the trial density
  have hlt : rStar zeroV (attrW poissonKernel) < ENNReal.ofReal aCos := by
    obtain ⟨ρ, h0, h1, hH, hG, hD⟩ := htrial
    have hadm : Admissible zeroV (attrW poissonKernel) ρ := (admissible_iff hC hmin0).2 ⟨h0, h1, hH, hG⟩
    have hle : rStar zeroV (attrW poissonKernel) ≤ dissipation zeroV (attrW poissonKernel) ρ /
        (2 * (gap zeroV (attrW poissonKernel) (densMeasure ρ)).toENNReal) := iInf₂_le _ hadm
    rw [quot_real hC hmin0 hadm] at hle
    refine lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff haC).2 ?_)
    rw [div_lt_iff₀ (by positivity)]
    linarith
  have hr0lt : r0 < aCos := by
    rw [hrr] at hlt; exact (ENNReal.ofReal_lt_ofReal_iff haC).1 hlt
  -- r_ms = r_*
  obtain ⟨KV, KW, hyp⟩ := Ex.hyp_attr_proved hC
  have hcomp := fun (F : Family 1) (hF : F.Admissible) =>
    Ex.interaction_compensation_proved hC hmin0 hCpos hr0 hrr (γ := 19 / 250) (by norm_num)
      (fun ρ α₁ β₁ hρ hα hβ hm => analytic_concavity ρ α₁ β₁ hρ hα hβ hm hr0 hr0lt.le) F hF
  have hdef : ∀ F : Family 1, F.Admissible → 0 ≤ deficit (attrW poissonKernel) r0 F :=
    fun F hF => le_trans (hcomp F hF).2 (hcomp F hF).1
  have hge : ENNReal.ofReal r0 ≤ rMs zeroV (attrW poissonKernel) := le_rMs_of_deficit hyp hdef
  have hle : rMs zeroV (attrW poissonKernel) ≤ rStar zeroV (attrW poissonKernel) :=
    (upper_comparison (le_refl 1) hyp).2
  have hrms : rMs zeroV (attrW poissonKernel) = rStar zeroV (attrW poissonKernel) :=
    le_antisymm hle (hrr ▸ hge)
  -- λ_G
  have hLamG : LamGValue (attrW poissonKernel) (ENNReal.ofReal aCos) := by
    have h := lamGValue_of_formula hC hmin0 ⟨KV, KW, hyp⟩ hsup'
    have hinf : (⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat poissonKernel ((n : ℤ) + 1)))) =
        ENNReal.ofReal aCos := by
      apply le_antisymm
      · refine (iInf_le _ 0).trans (le_of_eq ?_)
        have : chat poissonKernel 1 = 0 := chat_poisson_odd 1 (by decide)
        simp [this]
      · refine le_iInf fun n => ENNReal.ofReal_le_ofReal ?_
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have : chat poissonKernel 1 = 0 := chat_poisson_odd 1 (by decide)
          simp [this]
        · have hc := (chat_poisson_nonneg_le ((n : ℤ) + 1) (by omega)).2
          have h2 : (4 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
            have : (2 : ℝ) ≤ (n : ℝ) + 1 := by
              have : (1 : ℝ) ≤ n := by exact_mod_cast hn
              linarith
            nlinarith
          have h3 : 21 / 25 ≤ 1 - chat poissonKernel ((n : ℤ) + 1) := by linarith
          have h4 : 1 ≤ ((n : ℝ) + 1) ^ 2 * (1 - chat poissonKernel ((n : ℤ) + 1)) := by nlinarith
          calc aCos = aCos * 1 := (mul_one _).symm
            _ ≤ aCos * (((n : ℝ) + 1) ^ 2 * (1 - chat poissonKernel ((n : ℤ) + 1))) :=
                mul_le_mul_of_nonneg_left h4 haC.le
            _ = _ := by ring
    rw [hinf] at h
    exact h
  refine ⟨?_, hrms, hlt, hLamG, ?_, ?_, ?_⟩
  · rw [hrms]; exact hatt.1
  · obtain ⟨e0, lam0, Cm0, he0, hCm0⟩ := exists_ref_data hC hmin0 ⟨KV, KW, hyp⟩ hsup'
    obtain ⟨-, hv⟩ := hLamG
    have := hv e0 lam0 Cm0 he0 hCm0
    exact hatt.2 e0 lam0 Cm0 he0 hCm0 (this ▸ hlt)
  · rw [← hrms]; exact full_labeled_lsi_limit (le_refl 1) hyp
  · exact sharp_symmetric_lsi_limit (le_refl 1) hyp

end SharpLSI.FL.Ex.LaneD
