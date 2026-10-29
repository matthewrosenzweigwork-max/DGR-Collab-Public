import FullLabeledLSI.Statements.S07_Prop_3_1
import FullLabeledLSI.Statements.S09_Prop_3_3
import FullLabeledLSI.Defs.F07_Sanity
import SharpSymmetricLSI.Statements.R01_Theorem_1_1

/-!
# Section 8.1: agreement of the limiting constants (Corollary 8.1)

Proofs of the statements of `S12_Cor_8_1`.  Theorem 1.1 of the full-labeled paper (`r_N^all → r_ms`)
and the smooth-family description of `r_ms` (`rMs_eq_smooth_inf`) are *hypotheses* of the
agreement statements; they are supplied by `S01_Theorem_1_1` and `S02_Prop_2_1` at the statement
level.

* `Sec8.Crit` is the real-valued criterion (8.2) (it is `AgreementCriterion` of `S12`);
* `Sec8.crit_iff` identifies it with `2 r_* G_θ ≤ D_θ` in `ℝ≥0∞` for admissible families;
* `Sec8.rMs_eq_rStar_iff` reduces `r_ms = r_*` to the criterion.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The criterion (8.2) in real form (this is `AgreementCriterion` of `S12`). -/
def Crit (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (F : Family d) : Prop :=
  -((dissipation V W F.bar).toReal - 2 * (rStar V W).toReal * (gap V W (densMeasure F.bar)).toReal)
    ≤ ∑ a, F.θ a * ((relFisher (F.ρ a) F.bar).toReal -
      2 * (rStar V W).toReal * (klDiv (densMeasure (F.ρ a)) (densMeasure F.bar)).toReal)

theorem rStar_lt_top (hd : 1 ≤ d) (hyp : Hyp V W KV KW) : rStar V W < ⊤ := by
  obtain ⟨ρ, hρ⟩ := SharpLSI.admissible_nonempty hd hyp
  obtain ⟨_, hD⟩ := SharpLSI.gap_lt_top_of_admissible hyp hρ
  refine lt_of_le_of_lt (iInf₂_le ρ hρ) ?_
  refine ENNReal.div_lt_top hD.ne ?_
  have : 0 < (gap V W (densMeasure ρ)).toENNReal := EReal.toENNReal_pos_iff.2 hρ.2.2.2
  simpa using this.ne'

/-- The finiteness assertions of `criterion_terms_finite`. -/
theorem terms_finite (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    rStar V W < ⊤ ∧ dissipation V W F.bar < ⊤ ∧ gap V W (densMeasure F.bar) < ⊤ ∧
      ⊥ < gap V W (densMeasure F.bar) ∧
      ∀ a, relFisher (F.ρ a) F.bar < ⊤ ∧ klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) < ⊤ := by
  obtain ⟨hG, hD, -⟩ := species_decomposition hyp F hF
  obtain ⟨hGt, hGb, hDt⟩ := msGap_msDiss_lt_top hd hyp hF
  set K : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) *
    klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) with hK
  set g : EReal := gap V W (densMeasure F.bar) with hg
  have hgb : ⊥ < g := by
    refine bot_lt_iff_ne_bot.2 fun h => ?_
    rw [hG, h, EReal.bot_add] at hGb
    exact lt_irrefl _ hGb
  have hKt : K ≠ ⊤ := by
    intro h
    rw [hG, h, EReal.coe_ennreal_top, EReal.add_top_of_ne_bot hgb.ne'] at hGt
    exact lt_irrefl _ hGt
  have hgt : g < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => ?_
    rw [hG, h, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot _)] at hGt
    exact lt_irrefl _ hGt
  have hDt' := hDt
  rw [hD] at hDt'
  refine ⟨rStar_lt_top hd hyp, lt_of_le_of_lt le_self_add hDt', hgt, hgb, fun a => ?_⟩
  have hθ : ENNReal.ofReal (F.θ a) ≠ 0 := by
    simpa using (hF.1 a)
  constructor
  · have h2 : ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar < ⊤ :=
      lt_of_le_of_lt le_add_self hDt'
    have h3 := (ENNReal.sum_lt_top.1 h2) a (Finset.mem_univ a)
    rcases ENNReal.mul_lt_top_iff.1 h3 with h | h | h
    · exact h.2
    · exact absurd h hθ
    · rw [h]; exact ENNReal.zero_lt_top
  · have h3 := (ENNReal.sum_ne_top.1 hKt) a (Finset.mem_univ a)
    rw [lt_top_iff_ne_top]
    intro h
    rw [h] at h3
    simp [hθ] at h3

/-- For an admissible family, the real criterion (8.2) is `2 r_* G_θ ≤ D_θ`. -/
theorem crit_iff (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible) :
    Crit V W F ↔ 2 * rStar V W * (msGap V W F).toENNReal ≤ msDiss V W F := by
  obtain ⟨hG, hD, h0⟩ := species_decomposition hyp F hF
  obtain ⟨hrs, hDb, hgt, hgb, hab⟩ := terms_finite hd hyp F hF
  obtain ⟨hGt, hGb, hDt⟩ := msGap_msDiss_lt_top hd hyp hF
  set rr : ℝ := (rStar V W).toReal with hrr
  have hrr0 : 0 ≤ rr := ENNReal.toReal_nonneg
  have hrs' : rStar V W = ENNReal.ofReal rr := (ENNReal.ofReal_toReal hrs.ne).symm
  set gr : ℝ := (gap V W (densMeasure F.bar)).toReal with hgr
  set Dr : ℝ := (dissipation V W F.bar).toReal with hDr
  set Ir : Fin F.q → ℝ := fun a => (relFisher (F.ρ a) F.bar).toReal with hIr
  set Hr : Fin F.q → ℝ := fun a => (klDiv (densMeasure (F.ρ a)) (densMeasure F.bar)).toReal
    with hHr
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  -- the gap
  have hKe : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) :
      ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun a _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hab a).2.ne
  have hKr : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) :
      ℝ≥0∞).toReal = ∑ a, F.θ a * Hr a := by
    rw [ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hab a).2.ne]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 a)]
  have hmsG : msGap V W F = ((gr + ∑ a, F.θ a * Hr a : ℝ) : EReal) := by
    rw [hG, EReal.coe_add, ← hKr, EReal.coe_ennreal_toReal hKe, hgr, EReal.coe_toReal hgt.ne hgb.ne']
  -- the dissipation
  have hIe : ∀ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar ≠ ⊤ := fun a =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hab a).1.ne
  have hmsD : (msDiss V W F).toReal = Dr + ∑ a, F.θ a * Ir a := by
    rw [hD, ENNReal.toReal_add hDb.ne (ENNReal.sum_ne_top.2 fun a _ => hIe a),
      ENNReal.toReal_sum fun a _ => hIe a]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 a)]
  have hmsDe : msDiss V W F = ENNReal.ofReal (Dr + ∑ a, F.θ a * Ir a) := by
    rw [← hmsD, ENNReal.ofReal_toReal hDt.ne]
  have hnn : 0 ≤ Dr + ∑ a, F.θ a * Ir a := by rw [← hmsD]; exact ENNReal.toReal_nonneg
  rw [hmsG, hmsDe, EReal.real_coe_toENNReal, hrs', Crit, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff hnn]
  have e1 : ∑ a, F.θ a * (Ir a - 2 * rr * Hr a) =
      ∑ a, F.θ a * Ir a - 2 * rr * ∑ a, F.θ a * Hr a := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  simp only [hIr, hHr] at e1 hnn ⊢
  rw [e1]
  constructor <;> intro h <;> nlinarith [h]

/-- `r_ms ≤ r_*`, from the family with a single group. -/
theorem rMs_le_rStar : rMs V W ≤ rStar V W := by
  unfold rMs rStar
  refine le_iInf₂ fun ρ hρ => ?_
  refine (iInf₂_le (Family.single ρ) ((msAdmissible_single_iff V W ρ).2 hρ)).trans ?_
  rw [msDiss_single, msGap_single]

/-- For an admissible family with nonpositive gap the criterion `2 r_* G_θ ≤ D_θ` is trivial. -/
theorem le_of_not_pos (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (F : Family d) (hF : F.Admissible)
    (hg : ¬ 0 < msGap V W F) : 2 * rStar V W * (msGap V W F).toENNReal ≤ msDiss V W F := by
  rw [EReal.toENNReal_of_nonpos (not_lt.1 hg)]
  simp

/-- `r_* ≤ r_ms` iff the criterion `2 r_* G_θ ≤ D_θ` holds for every admissible family. -/
theorem rStar_le_rMs_iff (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rStar V W ≤ rMs V W ↔
      ∀ F : Family d, F.Admissible → 2 * rStar V W * (msGap V W F).toENNReal ≤ msDiss V W F := by
  constructor
  · intro h F hF
    by_cases hg : 0 < msGap V W F
    · have hMs : MsAdmissible V W F := ⟨hF, hg⟩
      have h1 : rStar V W ≤ msDiss V W F / (2 * (msGap V W F).toENNReal) :=
        h.trans (iInf₂_le F hMs)
      have hpos : 0 < (msGap V W F).toENNReal := EReal.toENNReal_pos_iff.2 hg
      have hfin : (msGap V W F).toENNReal ≠ ⊤ :=
        EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top hd hyp hF).1.ne
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
        (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))] at h1
      calc 2 * rStar V W * (msGap V W F).toENNReal = rStar V W * (2 * (msGap V W F).toENNReal) := by
            ring
        _ ≤ _ := h1
    · exact le_of_not_pos hd hyp F hF hg
  · intro h
    unfold rMs
    refine le_iInf₂ fun F hF => ?_
    have hpos : 0 < (msGap V W F).toENNReal := EReal.toENNReal_pos_iff.2 hF.2
    have hfin : (msGap V W F).toENNReal ≠ ⊤ :=
      EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top hd hyp hF.1).1.ne
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))]
    calc rStar V W * (2 * (msGap V W F).toENNReal) = 2 * rStar V W * (msGap V W F).toENNReal := by
          ring
      _ ≤ _ := h F hF.1

/-- Given Theorem 1.1 of the full-labeled paper, the two limits agree iff `r_ms = r_*`. -/
theorem agree_iff_rMs_eq_rStar (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hlim : Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W))) :
    (∃ L : ℝ≥0∞, Tendsto (fun N => rAll V W N) atTop (𝓝 L) ∧
        Tendsto (fun N => rSym V W N) atTop (𝓝 L)) ↔ rMs V W = rStar V W := by
  have hsym : Tendsto (fun N => rSym V W N) atTop (𝓝 (rStar V W)) :=
    SharpLSI.sharp_symmetric_lsi_limit hd hyp
  constructor
  · rintro ⟨L, h1, h2⟩
    exact (tendsto_nhds_unique hlim h1).trans (tendsto_nhds_unique h2 hsym)
  · intro h
    exact ⟨rStar V W, h ▸ hlim, hsym⟩

/-- `r_ms = r_*` iff the criterion (8.2) holds for every admissible family. -/
theorem rMs_eq_rStar_iff (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rMs V W = rStar V W ↔ ∀ F : Family d, F.Admissible → Crit V W F := by
  have h1 : rMs V W = rStar V W ↔ rStar V W ≤ rMs V W :=
    ⟨fun h => h.symm.le, fun h => le_antisymm rMs_le_rStar h⟩
  rw [h1, rStar_le_rMs_iff hd hyp]
  exact forall_congr' fun F => forall_congr' fun hF => (crit_iff hd hyp F hF).symm

/-- Corollary 8.1, (8.1) iff (8.2). -/
theorem agreement_iff (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hlim : Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W))) :
    (∃ L : ℝ≥0∞, Tendsto (fun N => rAll V W N) atTop (𝓝 L) ∧
        Tendsto (fun N => rSym V W N) atTop (𝓝 L)) ↔
      ∀ F : Family d, F.Admissible → Crit V W F :=
  (agree_iff_rMs_eq_rStar hd hyp hlim).trans (rMs_eq_rStar_iff hd hyp)

/-- Corollary 8.1: smooth strictly positive families suffice (given the smooth-infimum
description of `r_ms`, Proposition 2.1 of the full-labeled paper). -/
theorem agreement_smooth_suffices (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hsm : rMs V W = ⨅ F ∈ {F : Family d | MsAdmissible V W F ∧
        ∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x},
      msDiss V W F / (2 * (msGap V W F).toENNReal)) :
    (∀ F : Family d, F.Admissible → Crit V W F) ↔
      ∀ F : Family d, F.Admissible → (∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x) →
        Crit V W F := by
  constructor
  · intro h F hF _
    exact h F hF
  · intro h
    rw [← rMs_eq_rStar_iff hd hyp]
    refine le_antisymm rMs_le_rStar ?_
    rw [hsm]
    refine le_iInf₂ fun F hF => ?_
    have hc := h F hF.1.1 hF.2
    have h2 := (crit_iff hd hyp F hF.1.1).1 hc
    have hpos : 0 < (msGap V W F).toENNReal := EReal.toENNReal_pos_iff.2 hF.1.2
    have hfin : (msGap V W F).toENNReal ≠ ⊤ :=
      EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top hd hyp hF.1.1).1.ne
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))]
    calc rStar V W * (2 * (msGap V W F).toENNReal) = 2 * rStar V W * (msGap V W F).toENNReal := by
          ring
      _ ≤ _ := h2

/-- Corollary 8.1, (8.3). -/
theorem agreement_necessary (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (hlim : Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)))
    (hagree : ∃ L : ℝ≥0∞, Tendsto (fun N => rAll V W N) atTop (𝓝 L) ∧
        Tendsto (fun N => rSym V W N) atTop (𝓝 L)) :
    rStar V W ≤ rLS (μ : Measure (Torus d)) := by
  rw [← (agree_iff_rMs_eq_rStar hd hyp hlim).1 hagree]
  have h := equilibrium_families hd hyp hr μ hμ
  refine le_of_le_of_eq (le_iInf₂ fun F hF => ?_) h
  exact iInf₂_le F hF.1

end Sec8
end SharpLSI.FL
