import FullLabeledLSI.Paper.Sec3Entropy
import FullLabeledLSI.Paper.Sec3Alg
import FullLabeledLSI.Defs.F03_RelFisher
import FullLabeledLSI.Infra.SqrtMix
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.UpperApprox

/-!
# Proposition 3.1, dissipation part (3.2)

`√ρ̄ ∈ H¹(m)` with `∇√ρ̄ = ∑ₐ θₐ √ρₐ ∇√ρₐ / √ρ̄` on `{ρ̄ > 0}` and `0` elsewhere, and
`∑ₐ θₐ D_a = D(ρ̄) + ∑ₐ θₐ I(ρₐ|ρ̄)`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} (F : Family d)

/-- The chosen weak gradient of `√ρₐ`. -/
def sg (a : Fin F.q) : Torus d → Fin d → ℝ := weakGrad (fun y => Real.sqrt (F.ρ a y))

theorem sg_isWeakGrad (hF : F.Admissible) (a : Fin F.q) :
    IsWeakGrad (fun y => Real.sqrt (F.ρ a y)) (sg F a) :=
  isWeakGrad_weakGrad (hF.2.2 a).2.2.1

theorem sg_memLp (hF : F.Admissible) (a : Fin F.q) (k : Fin d) :
    MemLp (fun y => sg F a y k) 2 (haar d) := by
  have h := (hF.2.2 a).2.2.2.2
  refine h.of_le ((sg_isWeakGrad F hF a).aestronglyMeasurable_grad k) ?_
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact abs_le_sqrt_sqNorm _ k

theorem s_memLp (hF : F.Admissible) (a : Fin F.q) :
    MemLp (fun y => Real.sqrt (F.ρ a y)) 2 (haar d) :=
  (hF.2.2 a).2.2.2.1

/-- The weak gradient `∑ₐ θₐ 2 √ρₐ ∇√ρₐ` of `ρ̄`. -/
def wbar (x : Torus d) (k : Fin d) : ℝ :=
  ∑ a, F.θ a * (2 * Real.sqrt (F.ρ a x) * sg F a x k)

theorem isWeakGrad_bar (hF : F.Admissible) : IsWeakGrad F.bar (wbar F) := by
  have h1 : ∀ a, IsWeakGrad (fun y => F.θ a * F.ρ a y)
      (fun y k => F.θ a * (2 * Real.sqrt (F.ρ a y) * sg F a y k)) := fun a => by
    have := (isWeakGrad_sq (sg_isWeakGrad F hF a) (s_memLp F hF a) (sg_memLp F hF a)).cmul (F.θ a)
    convert this using 2
    rw [Real.sq_sqrt ((hF.2.2 a).1 _)]
  exact isWeakGrad_finsetSum Finset.univ (fun a _ => h1 a)


theorem cand_abs_le (hF : F.Admissible) (x : Torus d) (j : Fin d) :
    |sqrtGradCand F.bar (wbar F) x j| ≤ ∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖ := by
  have hrhs : 0 ≤ ∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖ :=
    Finset.sum_nonneg fun a _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  unfold sqrtGradCand
  split_ifs with hx
  · set r := Real.sqrt (F.bar x) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hx
    have hsle : ∀ a, Real.sqrt (F.θ a) * Real.sqrt (F.ρ a x) ≤ r := fun a => by
      rw [← Real.sqrt_mul (hF.1 a).le]
      exact Real.sqrt_le_sqrt (theta_rho_le_bar F hF a x)
    have hterm : ∀ a, F.θ a * Real.sqrt (F.ρ a x) / r ≤ Real.sqrt (F.θ a) := fun a => by
      rw [div_le_iff₀ hr0]
      have h1 : F.θ a = Real.sqrt (F.θ a) * Real.sqrt (F.θ a) :=
        (Real.mul_self_sqrt (hF.1 a).le).symm
      calc F.θ a * Real.sqrt (F.ρ a x)
          = Real.sqrt (F.θ a) * (Real.sqrt (F.θ a) * Real.sqrt (F.ρ a x)) := by
            rw [← mul_assoc, ← h1]
        _ ≤ Real.sqrt (F.θ a) * r :=
            mul_le_mul_of_nonneg_left (hsle a) (Real.sqrt_nonneg _)
    unfold wbar
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * r), div_le_iff₀ (by positivity)]
    calc |∑ a, F.θ a * (2 * Real.sqrt (F.ρ a x) * sg F a x j)|
        ≤ ∑ a, |F.θ a * (2 * Real.sqrt (F.ρ a x) * sg F a x j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a, (F.θ a * Real.sqrt (F.ρ a x) / r) * ‖sg F a x j‖ * (2 * r) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos (hF.1 a), abs_of_nonneg (Real.sqrt_nonneg _),
            abs_two, Real.norm_eq_abs]
          field_simp
      _ ≤ ∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖ * (2 * r) :=
          Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hterm a) (norm_nonneg _))
              (by positivity)
      _ = (∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖) * (2 * r) := by rw [Finset.sum_mul]
  · rw [abs_zero]; exact hrhs

theorem cand_memLp (hF : F.Admissible) (j : Fin d) :
    MemLp (fun x => sqrtGradCand F.bar (wbar F) x j) 2 (haar d) := by
  have hB : MemLp (fun x => ∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖) 2 (haar d) :=
    memLp_finsetSum _ fun a _ => ((sg_memLp F hF a j).norm).const_mul _
  have hbm : AEMeasurable F.bar (haar d) := bar_aemeasurable F hF
  have hwm : AEStronglyMeasurable (fun x => wbar F x j) (haar d) :=
    (isWeakGrad_bar F hF).aestronglyMeasurable_grad j
  have hmeas : AEMeasurable (fun x => sqrtGradCand F.bar (wbar F) x j) (haar d) := by
    have e : (fun x => sqrtGradCand F.bar (wbar F) x j) = {x | 0 < F.bar x}.indicator
        (fun x => wbar F x j / (2 * Real.sqrt (F.bar x))) := by
      funext x; simp [sqrtGradCand, Set.indicator]
    rw [e]
    refine AEMeasurable.indicator₀ ?_ (nullMeasurableSet_lt aemeasurable_const hbm)
    exact hwm.aemeasurable.div (aemeasurable_const.mul
      (Real.continuous_sqrt.measurable.comp_aemeasurable hbm))
  refine hB.of_le hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
    (Finset.sum_nonneg fun a _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
  exact cand_abs_le F hF x j


theorem sum_sq_le_sq_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ∑ k, v k ^ 2 ≤ (∑ k, |v k|) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  calc v i ^ 2 = |v i| * |v i| := by rw [← sq_abs, sq]
    _ ≤ ∑ j, |v i| * |v j| := Finset.single_le_sum (f := fun j => |v i| * |v j|)
        (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)

theorem sqrt_sqNorm_le_sum_abs {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    Real.sqrt (sqNorm v) ≤ ∑ k, |v k| :=
  Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, sum_sq_le_sq_sum_abs v⟩

theorem wbar_integrable (hF : F.Admissible) (k : Fin d) : Integrable (fun y => wbar F y k) (haar d) := by
  unfold wbar
  refine integrable_finsetSum _ fun a _ => ?_
  have h := (s_memLp F hF a).integrable_mul (sg_memLp F hF a k)
  have : Integrable (fun y => 2 * (Real.sqrt (F.ρ a y) * sg F a y k)) (haar d) := h.const_mul 2
  exact (this.const_mul (F.θ a)).congr (Filter.Eventually.of_forall fun y => by
    simp only; ring)

theorem isWeakGrad_sqrtBar (hF : F.Admissible) :
    IsWeakGrad (fun y => Real.sqrt (F.bar y)) (sqrtGradCand F.bar (wbar F)) :=
  isWeakGrad_sqrt_L2' (bar_aemeasurable F hF)
    (Filter.Eventually.of_forall (bar_nonneg F hF)) (bar_integrable hF) (isWeakGrad_bar F hF)
    (wbar_integrable F hF) (cand_memLp F hF)

theorem memH1_sqrtBar (hF : F.Admissible) : MemH1 (haar d) (fun x => Real.sqrt (F.bar x)) := by
  have hw := isWeakGrad_sqrtBar F hF
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · have hm : AEStronglyMeasurable (fun x => Real.sqrt (F.bar x)) (haar d) :=
      hw.aestronglyMeasurable_fun
    rw [memLp_two_iff_integrable_sq hm]
    refine (bar_integrable hF).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Real.sq_sqrt (bar_nonneg F hF x)]
  · have hB : MemLp (fun x => ∑ j, ∑ a, Real.sqrt (F.θ a) * ‖sg F a x j‖) 2 (haar d) :=
      memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun a _ =>
        ((sg_memLp F hF a j).norm).const_mul _
    refine hB.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm) ?_
    filter_upwards [weakGrad_ae_eq hw] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hx,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun a _ =>
        mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact (sqrt_sqNorm_le_sum_abs _).trans
      (Finset.sum_le_sum fun j _ => cand_abs_le F hF x j)


section Diss

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem hasWeakGrad_force (hyp : Hyp V W KV KW) (hF : F.Admissible) :
    HasWeakGrad (fun x => V x + convDens W F.bar x) := by
  have hVw := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  exact ⟨_, hVw.add (isWeakGrad_convDens' hyp (bar_integrable hF) (W := W))⟩

theorem speciesDiss_eq (hyp : Hyp V W KV KW) (hF : F.Admissible) (a : Fin F.q) :
    speciesDiss V W (F.ρ a) F.bar = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * sg F a x k +
      Real.sqrt (F.ρ a x) * weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2) ∂haar d := by
  unfold speciesDiss
  rw [if_pos ⟨(hF.2.2 a).2.2, hasWeakGrad_force F hyp hF⟩]
  rfl

theorem dissipation_bar_eq (hyp : Hyp V W KV KW) (hF : F.Admissible) :
    dissipation V W F.bar = ∫⁻ x, ENNReal.ofReal (∑ k,
      (2 * weakGrad (fun y => Real.sqrt (F.bar y)) x k + Real.sqrt (F.bar x) *
        weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2) ∂haar d := by
  unfold dissipation
  rw [if_pos ⟨memH1_sqrtBar F hF, hasWeakGrad_force F hyp hF⟩]

theorem relFisher_eq (hF : F.Admissible) (a : Fin F.q) :
    relFisher (F.ρ a) F.bar = ∫⁻ x, ENNReal.ofReal (∑ k, (2 * sg F a x k -
      Real.sqrt (F.ρ a x) * score F.bar x k) ^ 2) ∂haar d := by
  have hac : densMeasure (F.ρ a) ≪ densMeasure F.bar := by
    rw [densMeasure_eq_ratio F hF a]; exact withDensity_absolutelyContinuous _ _
  unfold relFisher
  rw [if_pos ⟨hac, (hF.2.2 a).2.2, memH1_sqrtBar F hF⟩]
  rfl


theorem diss_pointwise (hyp : Hyp V W KV KW) (hF : F.Admissible) :
    ∀ᵐ x ∂haar d,
      ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (∑ k, (2 * sg F a x k +
        Real.sqrt (F.ρ a x) * weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2) =
      ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (F.bar y)) x k +
        Real.sqrt (F.bar x) * weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2) +
      ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (∑ k, (2 * sg F a x k -
        Real.sqrt (F.ρ a x) * score F.bar x k) ^ 2) := by
  have hwb := isWeakGrad_sqrtBar F hF
  have hz : ∀ a, ∀ᵐ x ∂haar d, Real.sqrt (F.ρ a x) = 0 → ∀ k, sg F a x k = 0 := fun a =>
    ae_grad_eq_zero_of_eq_zero (sg_isWeakGrad F hF a) ((s_memLp F hF a).integrable one_le_two)
      (fun k => (sg_memLp F hF a k).integrable one_le_two)
  filter_upwards [weakGrad_ae_eq hwb, ae_all_iff.2 hz] with x hx hzx
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  set f : Fin d → ℝ := fun k => weakGrad (fun y => V y + convDens W F.bar y) x k with hf
  set Gt : Fin d → ℝ := fun k => weakGrad (fun y => Real.sqrt (F.bar y)) x k with hGt
  have hGtc : ∀ k, Gt k = sqrtGradCand F.bar (wbar F) x k := fun k => congrFun hx k
  -- the ENNReal bookkeeping
  have e1 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (∑ k, (2 * sg F a x k +
      Real.sqrt (F.ρ a x) * f k) ^ 2) =
      ENNReal.ofReal (∑ a, F.θ a * ∑ k, (2 * sg F a x k + Real.sqrt (F.ρ a x) * f k) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a)
      (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  have e2 : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (∑ k, (2 * sg F a x k -
      Real.sqrt (F.ρ a x) * score F.bar x k) ^ 2) =
      ENNReal.ofReal (∑ a, F.θ a * ∑ k, (2 * sg F a x k -
        Real.sqrt (F.ρ a x) * score F.bar x k) ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a)
      (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun a _ => (ENNReal.ofReal_mul (hθ0 a)).symm
  show ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (∑ k, (2 * sg F a x k +
      Real.sqrt (F.ρ a x) * f k) ^ 2) = ENNReal.ofReal (∑ k, (2 * Gt k +
      Real.sqrt (F.bar x) * f k) ^ 2) + _
  rw [e1, e2, ← ENNReal.ofReal_add (Finset.sum_nonneg fun k _ => sq_nonneg _)
    (Finset.sum_nonneg fun a _ => mul_nonneg (hθ0 a) (Finset.sum_nonneg fun k _ => sq_nonneg _))]
  congr 1
  by_cases hpos : 0 < F.bar x
  · set r := Real.sqrt (F.bar x) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hpos
    have hscore : ∀ k, score F.bar x k = 2 * Gt k / r := fun k => by
      simp only [score, if_pos hpos, hGt, hr]
    have hs2 : ∑ a, F.θ a * Real.sqrt (F.ρ a x) ^ 2 = r ^ 2 := by
      rw [hr, Real.sq_sqrt (bar_nonneg F hF x)]
      exact Finset.sum_congr rfl fun a _ => by rw [Real.sq_sqrt ((hF.2.2 a).1 x)]
    have hsg : ∀ k, ∑ a, F.θ a * (Real.sqrt (F.ρ a x) * sg F a x k) = r * Gt k := fun k => by
      rw [hGtc k]
      simp only [sqrtGradCand, if_pos hpos, wbar]
      rw [← hr]
      field_simp
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by ring
    simp_rw [hscore]
    exact diss_algebra F.θ (fun a => Real.sqrt (F.ρ a x)) (fun a k => sg F a x k) f Gt hr0 hs2 hsg
  · have hb0 : F.bar x = 0 := le_antisymm (not_lt.1 hpos) (bar_nonneg F hF x)
    have hρ0 : ∀ a, F.ρ a x = 0 := fun a => rho_eq_zero_of_bar_eq_zero F hF a x hb0
    have hsg0 : ∀ a k, sg F a x k = 0 := fun a k => hzx a (by rw [hρ0 a, Real.sqrt_zero]) k
    have hG0 : ∀ k, Gt k = 0 := fun k => by rw [hGtc k]; simp [sqrtGradCand, hpos]
    have hsc : ∀ k, score F.bar x k = 0 := fun k => by simp [score, hpos]
    simp [hb0, hρ0, hsg0, hG0, hsc]


theorem aemeasurable_ofReal_sq_sum {A : Fin d → Torus d → ℝ}
    (h : ∀ k, AEMeasurable (A k) (haar d)) :
    AEMeasurable (fun x => ENNReal.ofReal (∑ k, (A k x) ^ 2)) (haar d) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    (Finset.aemeasurable_fun_sum _ fun k _ => (h k).pow_const 2)

theorem aemeasurable_score (hF : F.Admissible) (k : Fin d) :
    AEMeasurable (fun x => score F.bar x k) (haar d) := by
  have hwb := isWeakGrad_sqrtBar F hF
  have hG := (isWeakGrad_weakGrad ⟨_, hwb⟩).aestronglyMeasurable_grad k
  have hbm := bar_aemeasurable F hF
  have e : (fun x => score F.bar x k) = {x | 0 < F.bar x}.indicator
      (fun x => 2 * weakGrad (fun y => Real.sqrt (F.bar y)) x k / Real.sqrt (F.bar x)) := by
    funext x; simp [score, Set.indicator]
  rw [e]
  refine AEMeasurable.indicator₀ ?_ (nullMeasurableSet_lt aemeasurable_const hbm)
  exact (hG.aemeasurable.const_mul 2).div (Real.continuous_sqrt.measurable.comp_aemeasurable hbm)

theorem msDiss_decomp (hyp : Hyp V W KV KW) (hF : F.Admissible) :
    msDiss V W F = dissipation V W F.bar +
      ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar := by
  have hwb := isWeakGrad_sqrtBar F hF
  have hforce := isWeakGrad_weakGrad (hasWeakGrad_force F hyp hF)
  have hfk : ∀ k, AEMeasurable (fun x => weakGrad (fun y => V y + convDens W F.bar y) x k)
      (haar d) := fun k => (hforce.aestronglyMeasurable_grad k).aemeasurable
  have hsa : ∀ a, AEMeasurable (fun x => Real.sqrt (F.ρ a x)) (haar d) := fun a =>
    (sg_isWeakGrad F hF a).aestronglyMeasurable_fun.aemeasurable
  have hga : ∀ a k, AEMeasurable (fun x => sg F a x k) (haar d) := fun a k =>
    ((sg_isWeakGrad F hF a).aestronglyMeasurable_grad k).aemeasurable
  have hmS : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (∑ k, (2 * sg F a x k +
      Real.sqrt (F.ρ a x) * weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2)) (haar d) :=
    fun a => aemeasurable_ofReal_sq_sum fun k =>
      ((hga a k).const_mul 2).add ((hsa a).mul (hfk k))
  have hmR : ∀ a, AEMeasurable (fun x => ENNReal.ofReal (∑ k, (2 * sg F a x k -
      Real.sqrt (F.ρ a x) * score F.bar x k) ^ 2)) (haar d) :=
    fun a => aemeasurable_ofReal_sq_sum fun k =>
      ((hga a k).const_mul 2).sub ((hsa a).mul (aemeasurable_score F hF k))
  have hmB : AEMeasurable (fun x => ENNReal.ofReal (∑ k,
      (2 * weakGrad (fun y => Real.sqrt (F.bar y)) x k + Real.sqrt (F.bar x) *
        weakGrad (fun y => V y + convDens W F.bar y) x k) ^ 2)) (haar d) :=
    aemeasurable_ofReal_sq_sum fun k =>
      (((isWeakGrad_weakGrad ⟨_, hwb⟩).aestronglyMeasurable_grad k).aemeasurable.const_mul 2).add
        ((Real.continuous_sqrt.measurable.comp_aemeasurable (bar_aemeasurable F hF)).mul (hfk k))
  unfold msDiss
  simp_rw [speciesDiss_eq F hyp hF, relFisher_eq F hF]
  rw [dissipation_bar_eq F hyp hF]
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_finsetSum' _ fun a _ => (hmS a).const_mul _,
    ← lintegral_finsetSum' _ fun a _ => (hmR a).const_mul _, ← lintegral_add_left' hmB]
  exact lintegral_congr_ae (diss_pointwise F hyp hF)

end Diss

end SharpLSI.FL
