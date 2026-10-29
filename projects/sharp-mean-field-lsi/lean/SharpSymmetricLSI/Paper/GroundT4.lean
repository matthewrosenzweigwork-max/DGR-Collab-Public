import SharpSymmetricLSI.Paper.GroundT3

/-!
# R30 groundwork: the measure `ν = g² P_N / ‖g‖²` and the force bound under `f² P_N`

Variant of `sqMeasure_props` for `‖g‖² > 0` (no positive entropy needed):
`ν` is a symmetric probability, `ν ≪ P_N` and `KL(ν‖P_N) = ‖g‖⁻² Ent_{P_N}(g²)`. With the force
bound of Lemma 5.3 ((5.14)) this gives `∫ g²|∇U_N|² dP_N ≤ C (Ent(g²) + ‖g‖²)`.
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sqMeasure_props' (hyp : Hyp V W KV KW) {N : ℕ} {g : Config N d → ℝ} (hgm : Measurable g)
    (hi : Integrable (fun X => g X ^ 2) (gibbs V W N)) (hc : 0 < ∫ Y, g Y ^ 2 ∂gibbs V W N) :
    IsProbabilityMeasure (sqMeasure (gibbs V W N) g) ∧ sqMeasure (gibbs V W N) g ≪ gibbs V W N ∧
      klDiv (sqMeasure (gibbs V W N) g) (gibbs V W N) =
        ENNReal.ofReal (∫ Y, g Y ^ 2 ∂gibbs V W N)⁻¹ * ent (gibbs V W N) (fun X => g X ^ 2) ∧
      (IsSymmetric g → IsSymmetricMeasure (sqMeasure (gibbs V W N) g)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N with hP
  set c := ∫ Y, g Y ^ 2 ∂P with hc_def
  have hρm : Measurable fun X => ENNReal.ofReal (g X ^ 2 / c) :=
    ENNReal.measurable_ofReal.comp ((hgm.pow_const 2).div_const c)
  have hprob : IsProbabilityMeasure (sqMeasure P g) := by
    refine ⟨?_⟩
    rw [sqMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hi.div_const c)
        (ae_of_all _ fun X => div_nonneg (sq_nonneg _) hc.le), integral_div, div_self hc.ne',
      ENNReal.ofReal_one]
  have hac : sqMeasure P g ≪ P := withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity P hρm
  have hsd : sqrtDens (sqMeasure P g) P =ᵐ[P] fun X => (Real.sqrt c)⁻¹ * |g X| := by
    filter_upwards [hrn] with X hX
    simp only [sqrtDens]
    rw [show sqMeasure P g = P.withDensity fun X => ENNReal.ofReal (g X ^ 2 / c) from rfl, hX,
      ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) hc.le), Real.sqrt_div (sq_nonneg _),
      Real.sqrt_sq_eq_abs, div_eq_inv_mul]
  have hsq : ((Real.sqrt c)⁻¹) ^ 2 = c⁻¹ := by rw [inv_pow, Real.sq_sqrt hc.le]
  refine ⟨hprob, hac, ?_, ?_⟩
  · rw [klDiv_eq_ent hac, ← ent_const_mul P hi (inv_nonneg.mpr hc.le)]
    refine ent_congr_ae ?_
    filter_upwards [hsd] with X hX
    rw [hX, mul_pow, hsq, sq_abs]
  · intro hs σ
    change (sqMeasure P g).map (permEquiv σ) = sqMeasure P g
    rw [show sqMeasure P g = P.withDensity fun X => ENNReal.ofReal (g X ^ 2 / c) from rfl,
      map_withDensity_equiv _ _ hρm, hP, gibbs_map_perm hyp]
    congr 1
    funext X
    simp only [Function.comp_apply, permEquiv_symm_apply, hs σ.symm X]

theorem gradSqC_nonneg {N : ℕ} (u : Config N d → ℝ) (X : Config N d) : 0 ≤ gradSqC u X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The force bound under `f² P_N`** (from (5.14)). -/
theorem lintegral_sq_gradU_le (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} {N : ℕ} {CF : ℝ}
    (hForce : ∀ ν : Measure (Config N d), IsProbabilityMeasure ν → IsSymmetricMeasure ν →
      klDiv ν (gibbs V W N) ≠ ⊤ →
      ∫⁻ X, ENNReal.ofReal (gradSqC (Ucentered W μ N) X) ∂ν ≤
        ENNReal.ofReal CF * (klDiv ν (gibbs V W N) + 1))
    {f : Config N d → ℝ} (hf : MemH1C (gibbs V W N) f) (hs : IsSymmetric f)
    (hent : ent (gibbs V W N) (fun X => f X ^ 2) ≠ ⊤) :
    ∫⁻ X, ENNReal.ofReal (f X ^ 2 * gradSqC (Ucentered W μ N) X) ∂gibbs V W N ≤
      ENNReal.ofReal CF * (ent (gibbs V W N) (fun X => f X ^ 2) +
        ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  set G := gradSqC (Ucentered W μ N)
  have hfL := memLp_of_memH1C hyp hf
  obtain ⟨g, hgm, hgf, hgs⟩ := exists_measurable_rep hyp hfL.aestronglyMeasurable
  have hgs' := hgs hs
  have hsq : (fun X => g X ^ 2) =ᵐ[P] fun X => f X ^ 2 := by
    filter_upwards [hgf] with X hX; rw [hX]
  have e1 : ∫⁻ X, ENNReal.ofReal (f X ^ 2 * G X) ∂P = ∫⁻ X, ENNReal.ofReal (g X ^ 2 * G X) ∂P :=
    lintegral_congr_ae (by filter_upwards [hgf] with X hX; rw [hX])
  have e2 : ent P (fun X => f X ^ 2) = ent P (fun X => g X ^ 2) := ent_congr_ae hsq.symm
  have e3 : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂P = ∫⁻ X, ENNReal.ofReal (g X ^ 2) ∂P :=
    lintegral_congr_ae (by filter_upwards [hgf] with X hX; rw [hX])
  rw [e1, e2, e3]
  rw [e2] at hent
  have hi : Integrable (fun X => g X ^ 2) P := (hfL.integrable_sq).congr hsq.symm
  set c := ∫ Y, g Y ^ 2 ∂P
  have hc0 : 0 ≤ c := integral_nonneg fun _ => sq_nonneg _
  have hcl : ∫⁻ X, ENNReal.ofReal (g X ^ 2) ∂P = ENNReal.ofReal c :=
    (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)).symm
  rcases hc0.eq_or_lt with h0 | hpos
  · have hz : (fun X => g X ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).1 h0.symm
    have : ∫⁻ X, ENNReal.ofReal (g X ^ 2 * G X) ∂P = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) (by
        filter_upwards [hz] with X hX
        simp only [Pi.zero_apply] at hX; rw [hX, zero_mul, ENNReal.ofReal_zero])]
      simp
    rw [this]; exact bot_le
  obtain ⟨hprob, hac, hkl, hsym⟩ := sqMeasure_props' hyp hgm hi hpos
  have hklt : klDiv (sqMeasure P g) P ≠ ⊤ := by
    rw [hkl]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hent
  have hF := hForce _ hprob (hsym hgs') hklt
  have hρm : Measurable fun X => ENNReal.ofReal (g X ^ 2 / c) :=
    ENNReal.measurable_ofReal.comp ((hgm.pow_const 2).div_const c)
  have hν : ∫⁻ X, ENNReal.ofReal (G X) ∂sqMeasure P g =
      ∫⁻ X, ENNReal.ofReal (g X ^ 2 / c) * ENNReal.ofReal (G X) ∂P :=
    lintegral_withDensity_eq_lintegral_mul_non_measurable P hρm
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
  have hL : ∫⁻ X, ENNReal.ofReal (g X ^ 2 * G X) ∂P =
      ENNReal.ofReal c * ∫⁻ X, ENNReal.ofReal (G X) ∂sqMeasure P g := by
    rw [hν, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun X => ?_
    rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) hc0), ← ENNReal.ofReal_mul hc0]
    congr 1
    field_simp
  rw [hL, hcl]
  calc ENNReal.ofReal c * ∫⁻ X, ENNReal.ofReal (G X) ∂sqMeasure P g
      ≤ ENNReal.ofReal c * (ENNReal.ofReal CF * (klDiv (sqMeasure P g) P + 1)) :=
        mul_le_mul_right hF _
    _ = ENNReal.ofReal CF * (ent P (fun X => g X ^ 2) + ENNReal.ofReal c) := by
        rw [hkl, mul_left_comm, mul_add, mul_one, ← mul_assoc, ← ENNReal.ofReal_mul hc0,
          mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

end SharpLSI
