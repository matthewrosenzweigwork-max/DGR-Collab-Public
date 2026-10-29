import SharpSymmetricLSI.Paper.TorusLSI
import SharpSymmetricLSI.Paper.DensMeasure
import SharpSymmetricLSI.Defs.D07_rStar

/-!
# Non-vacuity in every dimension: the free gas

With `V = W = 0`, the hypotheses (1.2) hold with `K_V = K_W = 0`; the gap is `H(ρ|m)` and the
dissipation is `4∫|∇√ρ|²`, so the logarithmic Sobolev inequality of the flat torus
(`lsi_torus_H1`, by tensorization of the circle inequality) gives `r_* ≥ a = 4π² > 0` for every
`d ≥ 1`.
-/

open MeasureTheory Filter Topology Real InformationTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- **(1.2) for the free gas.** -/
theorem hyp_zero (d : ℕ) : Hyp (d := d) (fun _ => 0) (fun _ _ => 0) 0 0 where
  KV_nonneg := le_rfl
  KW_nonneg := le_rfl
  continuous_V := continuous_const
  continuous_W := continuous_const
  semiconvex_V := fun φ _ _ _ ξ => by simp
  semiconvex_W := fun φ _ _ _ ξ => by simp
  symm := fun _ _ => rfl
  diag := fun _ => rfl

theorem Fstar_zero : Fstar (d := d) (fun _ => 0) (fun _ _ => 0) = 0 := by
  unfold Fstar freeEnergy potE interE
  refine le_antisymm ?_ ?_
  · refine (iInf_le _ (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d))).trans ?_
    simp [klDiv_self]
  · refine le_iInf fun ρ => ?_
    simp only [integral_zero, zero_div, add_zero, EReal.coe_zero]
    exact EReal.coe_ennreal_nonneg _

theorem gap_zero (ρ : Measure (Torus d)) :
    gap (d := d) (fun _ => 0) (fun _ _ => 0) ρ = ((klDiv ρ (haar d) : ℝ≥0∞) : EReal) := by
  unfold gap
  rw [Fstar_zero]
  simp [freeEnergy, potE, interE]

/-- **`r_* ≥ 4π²` for the free gas**, in every dimension. -/
theorem rStar_ge_free : ENNReal.ofReal aCos ≤ rStar (d := d) (fun _ => 0) (fun _ _ => 0) := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  refine le_iInf₂ fun ρ hρ => ?_
  obtain ⟨h0, h1, hH1, hgap⟩ := hρ
  set h : Torus d → ℝ := fun x => Real.sqrt (ρ x)
  have hsq : (fun x => h x ^ 2) = ρ := funext fun x => Real.sq_sqrt (h0 x)
  -- the gap is the entropy of `ρ`
  have hKL : klDiv (densMeasure ρ) (haar d) = ent (haar d) (fun x => h x ^ 2) := by
    rw [hsq, klDiv_densMeasure' h0 h1, ent, if_pos (integrable_of_integral_eq_one' h1), h1]
    simp
  have hG : (gap (fun _ => 0) (fun _ _ => 0) (densMeasure ρ)).toENNReal =
      ent (haar d) (fun x => h x ^ 2) := by
    rw [gap_zero, EReal.toENNReal_coe, hKL]
  -- the dissipation is `4 ∫|∇h|²`
  have hconv : (fun x => (fun _ : Torus d => (0 : ℝ)) x + convDens (fun _ _ => (0 : ℝ)) ρ x) =
      fun _ => (0 : ℝ) := by
    funext x; simp [convDens]
  have hwg : HasWeakGrad (fun x => (fun _ : Torus d => (0 : ℝ)) x + convDens (fun _ _ => (0 : ℝ)) ρ x) := by
    rw [hconv]; exact ⟨0, isWeakGrad_const 0⟩
  have hD : dissipation (fun _ => 0) (fun _ _ => 0) ρ = 4 * dirichlet (haar d) h := by
    unfold dissipation
    rw [if_pos ⟨hH1, hwg⟩, hconv, dirichlet, ← lintegral_const_mul' _ _ (by norm_num)]
    · refine lintegral_congr_ae ?_
      filter_upwards [weakGrad_ae_eq (isWeakGrad_const (ι := Fin d) (0 : ℝ))] with x hx
      rw [hx]
      simp only [Pi.zero_apply, mul_zero, add_zero, sqNorm]
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
  -- the logarithmic Sobolev inequality of the torus
  have hLSI : ent (haar d) (fun x => h x ^ 2) ≤ ENNReal.ofReal (2 / aCos) * dirichlet (haar d) h :=
    lsi_torus_H1 (ι := Fin d) hH1
  have hE0 : ent (haar d) (fun x => h x ^ 2) ≠ 0 := by
    rw [← hKL]; intro hz
    rw [gap_zero, hz] at hgap; simp at hgap
  have hEtop : ent (haar d) (fun x => h x ^ 2) ≠ ⊤ := by
    have := (gap_lt_top_of_admissible (hyp_zero d) ⟨h0, h1, hH1, hgap⟩).1
    rw [gap_zero, hKL] at this
    exact fun ht => by rw [ht] at this; simp at this
  rw [hD, hG, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero two_ne_zero hE0))
    (Or.inl (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hEtop))]
  calc ENNReal.ofReal aCos * (2 * ent (haar d) (fun x => h x ^ 2))
      ≤ ENNReal.ofReal aCos * (2 * (ENNReal.ofReal (2 / aCos) * dirichlet (haar d) h)) := by
        gcongr
    _ = ENNReal.ofReal (aCos * 2 * (2 / aCos)) * dirichlet (haar d) h := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_ofNat]
        ring
    _ = 4 * dirichlet (haar d) h := by
        congr 1
        rw [show aCos * 2 * (2 / aCos) = 4 by field_simp; ring]
        norm_num

/-- **`r_* > 0` for the free gas in every dimension `d ≥ 1`** (non-vacuity of the positive-rate
branch of Theorem 1.1 beyond `d = 1`). -/
theorem rStar_pos_free (hd : 1 ≤ d) : 0 < rStar (d := d) (fun _ => 0) (fun _ _ => 0) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by unfold aCos; positivity)) rStar_ge_free

end SharpLSI

namespace SharpLSI

/-- The bound `r_* ≥ 4π²` for the free gas, with the constant written out. -/
theorem rStar_ge_free' {d : ℕ} :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ rStar (d := d) (fun _ => 0) (fun _ _ => 0) :=
  rStar_ge_free

end SharpLSI
