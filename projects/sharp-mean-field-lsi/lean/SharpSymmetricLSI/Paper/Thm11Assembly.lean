import SharpSymmetricLSI.Paper.R7Main
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Statements.R06_Upper_Bound

/-!
# Theorem 1.1 (lane s42; R01): assembly from Propositions 2.1–2.3, Lemma B.1 and Section 2.2

* `equilibrium_of_rStar_pos_aux`: the equilibrium assertions, from Proposition 2.1 (R02).
* `finiteN_of`: (1.10) from the lower-bound core of Section 2.3 (Paper/R7Main), with the
  conclusions of Proposition 2.2 (R03) and Proposition 2.3 (R04) as hypotheses.
* `limit_of_finiteN`: (1.9) from (1.10) and the upper bound `limsup r_N^sym ≤ r_*` (R06).

This file does not import Statements R01, R03, R07 or R08.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- (1.10) at size `N` gives `r ≤ r_N^sym`. -/
theorem le_rSym_of_lsi (hyp : Hyp V W KV KW) {r : ℝ} (hr0 : 0 < r) {N : ℕ}
    (h : ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f → IsSymmetric f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal (2 / r) * energy V W N f) :
    ENNReal.ofReal r ≤ rSym V W N := by
  unfold rSym
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hmem, hsym, hent⟩ := hf
  have hE := energy_lt_top hyp hmem
  have h1 := h f hmem hsym
  have hEt : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE.ne) h1
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hEt)]
  calc ENNReal.ofReal r * ent (gibbs V W N) (fun X => f X ^ 2)
      ≤ ENNReal.ofReal r * (ENNReal.ofReal (2 / r) * energy V W N f) := by gcongr
    _ = 2 * energy V W N f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le, mul_div_cancel₀ (2 : ℝ) hr0.ne',
          ENNReal.ofReal_ofNat]

/-- **(1.9) from (1.10)**. -/
theorem limit_of_finiteN (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hfin : FiniteNConclusion' V W) :
    Tendsto (fun N => rSym V W N) atTop (𝓝 (rStar V W)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ (upper_bound hd hyp)
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨r, -, hcr, hrS⟩ := ENNReal.lt_iff_exists_real_btwn.mp hc
  have hr0 : 0 < r := by
    rcases le_or_gt r 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h] at hcr; exact absurd hcr (not_lt.mpr zero_le)
    · exact h
  obtain ⟨Nr, hNr⟩ := hfin r hr0 hrS
  refine lt_of_lt_of_le hcr (le_liminf_of_le (by isBoundedDefault) ?_)
  filter_upwards [eventually_ge_atTop Nr] with N hN
  exact le_rSym_of_lsi hyp hr0 (hNr N hN)

/-- **(1.10)** from Propositions 2.2 and 2.3 (as hypotheses), Proposition 2.1 and Lemma B.1. -/
theorem finiteN_of (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (h22 : 0 < rStar V W → DefectiveConclusion' V W)
    (h23 : 0 < rStar V W → CompactnessConclusion V W) : FiniteNConclusion' V W := by
  intro r hr0 hr
  have hpos : 0 < rStar V W := lt_of_le_of_lt zero_le hr
  obtain ⟨μ, hμ⟩ := (prop_equilibrium hd hyp hpos).1.exists
  obtain ⟨⟨e, lam, he⟩, h2⟩ := h23 hpos μ hμ
  obtain ⟨⟨C, hC⟩, h3⟩ := h2 e lam he
  obtain ⟨⟨γ, hγ⟩, h4⟩ := h3 C hC
  haveI := hγ.1
  exact lower_bound_core hyp hpos (h22 hpos) lemma_B1 (h4 γ hγ) r hr0 hr

/-- **The equilibrium assertions of Theorem 1.1.** -/
theorem equilibrium_of_rStar_pos_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) :
    (∃! μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ) ∧
    ∀ μ : ProbabilityMeasure (Torus d), IsMinimizer V W μ →
      (∃ p, HasPosLipDensity μ p) ∧
      ∀ h : Torus d → ℝ, MemL20 μ h → ¬ (h =ᵐ[(μ : Measure (Torus d))] 0) →
        0 < secondVar W μ h := by
  obtain ⟨huniq, hall⟩ := prop_equilibrium hd hyp hr
  refine ⟨huniq, fun μ hμ => ?_⟩
  obtain ⟨p, hp, -, σ, hσ, c, -, -, hcoer, -⟩ := hall μ hμ
  refine ⟨⟨p, hp⟩, fun h hh hne => ?_⟩
  have hi : Integrable (fun x => h x ^ 2) (μ : Measure (Torus d)) := hh.1.integrable_sq
  have hpos : 0 < ∫ x, h x ^ 2 ∂(μ : Measure (Torus d)) := by
    refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) fun h0 => hne ?_
    have := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (h x)) hi).mp h0.symm
    filter_upwards [this] with x hx
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  exact lt_of_lt_of_le (mul_pos hσ hpos) (hcoer h hh)

end SharpLSI
