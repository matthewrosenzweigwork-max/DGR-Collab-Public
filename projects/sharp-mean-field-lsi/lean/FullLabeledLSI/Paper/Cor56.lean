import FullLabeledLSI.Statements.S02_Prop_2_1
import FullLabeledLSI.Statements.S03_Prop_2_2
import FullLabeledLSI.Statements.S08_Prop_3_2
import SharpSymmetricLSI.Paper.R37Particle

/-!
# Corollary 5.6 (`cor:defective-optimal`): optimal uniform defective rate

* `ac_of_fisherInfoC_lt_top`: finite relative Fisher information forces `ν ≪ P_N`.
* `uniform_defective_of_lt_rMs`: from `prop_defective_all` (Proposition 2.2) to the `ν`-form of the
  defective inequality, with `f = √(dν/dP_N)` (homogeneity is not needed: `∫ f² = 1`).
* `defective_optimal_aux`: the supremum formula (5.28). The proof of the manuscript: rates above
  `r_ms` are excluded by `le_rMs_of_uniform_defective` (Proposition 3.2), rates below `r_ms` are
  admissible by Proposition 2.2 if `r_* > 0`, and `r_* = 0` gives `r_ms = 0` by (2.1).
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem ac_of_fisherInfoC_lt_top {N : ℕ} {ν P : Measure (Config N d)}
    (h : fisherInfoC ν P < ⊤) : ν ≪ P := by
  unfold fisherInfoC fisherInfo at h
  by_cases hac : ν.map flat ≪ P.map flat ∧
      MemH1 (P.map flat) (fun x => Real.sqrt ((ν.map flat).rnDeriv (P.map flat) x).toReal)
  · have h1 := hac.1.map (measurable_unflat (N := N) (d := d))
    have e : ∀ μ : Measure (Config N d), (μ.map flat).map unflat = μ := by
      intro μ
      rw [Measure.map_map measurable_unflat measurable_flat]
      have : (unflat ∘ flat : Config N d → Config N d) = id := by
        funext X; rfl
      rw [this, Measure.map_id]
    rwa [e, e] at h1
  · rw [if_neg hac] at h
    exact absurd h (lt_irrefl _)

/-- The `ν`-form of the defective inequality at a rate strictly below `r_ms`. -/
theorem uniform_defective_of_lt_rMs {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W) {r : ℝ} (hr0 : 0 < r)
    (hlt : ENNReal.ofReal r < rMs V W) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      fisherInfoC ν (gibbs V W N) < ⊤ →
        ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
          fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C := by
  obtain ⟨Br, hBr⟩ := prop_defective_all hd hyp hr r hr0 hlt
  refine ⟨2 * r * Br, fun N hN ν hν hfin => ?_⟩
  have hP : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac : ν ≪ gibbs V W N := ac_of_fisherInfoC_lt_top hfin
  have hF := fisherInfoC_eq hyp hac
  have hm : MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N)) := by
    by_contra hm
    rw [if_neg hm] at hF
    rw [hF] at hfin
    exact lt_irrefl _ hfin
  rw [if_pos hm] at hF
  have hKL := klDiv_eq_ent hac (ν := ν) (P := gibbs V W N)
  -- `∫⁻ f² = 1`
  have hint : ∫⁻ X, ENNReal.ofReal (sqrtDens ν (gibbs V W N) X ^ 2) ∂gibbs V W N = 1 := by
    have e : ∀ X, sqrtDens ν (gibbs V W N) X ^ 2 = (ν.rnDeriv (gibbs V W N) X).toReal := by
      intro X; simp [sqrtDens, Real.sq_sqrt ENNReal.toReal_nonneg]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal Measure.integrable_toReal_rnDeriv
      (Filter.Eventually.of_forall fun X => ENNReal.toReal_nonneg),
      Measure.integral_toReal_rnDeriv hac]
    simp
  have hdef := hBr N hN (sqrtDens ν (gibbs V W N)) hm
  rw [hint, mul_one, ← hKL] at hdef
  -- multiply by `2r`
  have h2r : (0 : ℝ) < 2 * r := by positivity
  calc ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N)
      ≤ ENNReal.ofReal (2 * r) * (ENNReal.ofReal (2 / r) *
          energy V W N (sqrtDens ν (gibbs V W N)) + (Br : ℝ≥0∞)) := by gcongr
    _ = fisherInfoC ν (gibbs V W N) + ENNReal.ofReal (2 * r * Br) := by
        rw [mul_add, ← mul_assoc, ← ENNReal.ofReal_mul h2r.le, hF]
        have e1 : 2 * r * (2 / r) = 4 := by field_simp; norm_num
        have e2 : ENNReal.ofReal (2 * r * Br) = ENNReal.ofReal (2 * r) * (Br : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul h2r.le, ENNReal.ofReal_coe_nnreal]
        rw [e1, e2]
        simp

/-- Corollary 5.6, (5.28), with the set of uniform defective rates written out. -/
theorem defective_optimal_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rMs V W = ⨆ r ∈ {r : ℝ | 0 ≤ r ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
          fisherInfoC ν (gibbs V W N) < ⊤ →
            ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
              fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C}, ENNReal.ofReal r := by
  apply le_antisymm
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ rStar V W) with h0 | hpos
    · have : rMs V W = 0 := le_antisymm ((upper_comparison hd hyp).2.trans h0.symm.le) zero_le
      rw [this]; exact zero_le
    · refine le_of_forall_lt fun c hc => ?_
      obtain ⟨r, hr0, hcr, hrlt⟩ := ENNReal.lt_iff_exists_real_btwn.1 hc
      have hr0' : 0 < r := ENNReal.ofReal_pos.1 (lt_of_le_of_lt zero_le hcr)
      obtain ⟨C, hC⟩ := uniform_defective_of_lt_rMs hd hyp hpos hr0' hrlt
      refine lt_of_lt_of_le hcr ?_
      exact le_iSup₂_of_le (f := fun (r : ℝ) (_ : r ∈ {r : ℝ | 0 ≤ r ∧ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
          fisherInfoC ν (gibbs V W N) < ⊤ →
            ENNReal.ofReal (2 * r) * klDiv ν (gibbs V W N) ≤
              fisherInfoC ν (gibbs V W N) + ENNReal.ofReal C}) => ENNReal.ofReal r) r
        ⟨hr0, C, hC⟩ le_rfl
  · refine iSup₂_le fun r hr => ?_
    obtain ⟨hr0, C, hC⟩ := hr
    refine le_rMs_of_uniform_defective hd hyp r hr0 C fun N hN ν hν => ?_
    by_cases hfin : fisherInfoC ν (gibbs V W N) < ⊤
    · exact hC N hN ν hν hfin
    · rw [not_lt, top_le_iff] at hfin
      rw [hfin]; simp

end SharpLSI.FL
