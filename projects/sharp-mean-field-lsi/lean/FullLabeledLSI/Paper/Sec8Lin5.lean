import FullLabeledLSI.Paper.Sec8Lin4
import FullLabeledLSI.Paper.AdmissibleFinite
import SharpSymmetricLSI.Statements.R02_Prop_2_1

/-!
# Section 8.3 (linearization), part 5: the perturbation family

* `hb θ h = ∑ θₐ hₐ` and `fam p θ h t`, the family `ρₐ = p (1 + t hₐ)` (the same terms as
  `hBar` and `linFamily` of S14);
* `p = elDens` for a positive Lipschitz density of the equilibrium;
* uniform bounds, Lipschitz constants and the weak gradient of `hb`;
* the Dirichlet integral of a function with a bounded measurable weak gradient.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

/-- `h̄ = ∑ₐ θₐ hₐ`. -/
noncomputable def hb {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ a, θ a * h a x

/-- The family `ρₐ = p (1 + t hₐ)`. -/
noncomputable def fam (p : Torus d → ℝ) {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ)
    (t : ℝ) : Family d :=
  ⟨q, θ, fun a x => p x * (1 + t * h a x)⟩

theorem fam_bar (p : Torus d → ℝ) {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (t : ℝ)
    (hθ1 : ∑ a, θ a = 1) : (fam p θ h t).bar = fun x => p x * (1 + t * hb θ h x) := by
  funext x
  have : ∑ a : Fin q, θ a * (p x * (1 + t * h a x)) =
      p x * ((∑ a : Fin q, θ a) + t * ∑ a : Fin q, θ a * h a x) := by
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hθ1] at this
  have e : (fam p θ h t).bar x = ∑ a : Fin q, θ a * (p x * (1 + t * h a x)) := rfl
  rw [e, this]
  rfl

theorem p_eq_elDens {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {p : Torus d → ℝ} (hp : HasPosLipDensity μ p) :
    p = elDens V W (μ : Measure (Torus d)) := by
  obtain ⟨hp0, ⟨L, hL⟩, hμp⟩ := hp
  obtain ⟨hpm, hE0, hE1⟩ := elDensity_props hyp (μ : Measure (Torus d))
  obtain ⟨c, C, LE, hc, hb⟩ := elDensity_bounds hyp (V := V) (W := W)
  obtain ⟨-, hLE⟩ := hb (μ : Measure (Torus d)) inferInstance
  have hμE := minimizer_eq_elDensity hyp hμ
  have hEq : densMeasure p = densMeasure (elDens V W (μ : Measure (Torus d))) :=
    hμp.symm.trans hμE
  have hfin : ∫⁻ x, ENNReal.ofReal (p x) ∂haar d ≠ ⊤ := by
    have : densMeasure p Set.univ = 1 := by
      rw [← hμp]; simp
    have h2 : densMeasure p Set.univ = ∫⁻ x, ENNReal.ofReal (p x) ∂haar d := by
      unfold densMeasure; rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← h2, this]; exact ENNReal.one_ne_top
  have hae : (fun x => ENNReal.ofReal (p x)) =ᵐ[haar d]
      fun x => ENNReal.ofReal (elDens V W (μ : Measure (Torus d)) x) :=
    (withDensity_eq_iff (ENNReal.measurable_ofReal.comp hL.continuous.measurable).aemeasurable
      (ENNReal.measurable_ofReal.comp hpm).aemeasurable hfin).1 hEq
  have hae' : p =ᵐ[haar d] elDens V W (μ : Measure (Torus d)) := by
    filter_upwards [hae] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hp0 x).le (hE0 x).le).1 hx
  exact (Continuous.ae_eq_iff_eq (haar d) hL.continuous hLE.continuous).1 hae'

theorem lin_bounds {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) (hθ : ∀ a, 0 < θ a)
    (hθ1 : ∑ a, θ a = 1) (hbd : ∀ a, ∃ B, ∀ x, |h a x| ≤ B) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ a x, |h a x| ≤ B) ∧ ∀ x, |hb θ h x| ≤ B := by
  choose Ba hBa using hbd
  refine ⟨∑ a, |Ba a|, Finset.sum_nonneg fun a _ => abs_nonneg _, fun a x => ?_, fun x => ?_⟩
  · exact (hBa a x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |Ba a|) (fun j _ => abs_nonneg _) (Finset.mem_univ a)))
  · have hB : ∀ a, |h a x| ≤ ∑ a, |Ba a| := fun a => (hBa a x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun a => |Ba a|) (fun j _ => abs_nonneg _) (Finset.mem_univ a)))
    unfold hb
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |θ a * h a x| = ∑ a, θ a * |h a x| :=
          Finset.sum_congr rfl fun a _ => by rw [abs_mul, abs_of_pos (hθ a)]
      _ ≤ ∑ a, θ a * ∑ a, |Ba a| := Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hB a) (hθ a).le
      _ = ∑ a, |Ba a| := by rw [← Finset.sum_mul, hθ1, one_mul]

theorem lip_hb {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ)
    (hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a)) :
    ∃ L : ℝ≥0, LipschitzWith L (hb θ h) :=
  lip_sum Finset.univ (fun a x => θ a * h a x) fun a => lip_smul (θ a) (hLip a)

theorem hb_integral {q : ℕ} (θ : Fin q → ℝ) (h : Fin q → Torus d → ℝ) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hLip : ∀ a, ∃ L : ℝ≥0, LipschitzWith L (h a))
    (hbd : ∀ a, ∃ B, ∀ x, |h a x| ≤ B) (hmean : ∀ a, ∫ x, h a x ∂μ = 0) :
    ∫ x, hb θ h x ∂μ = 0 := by
  have hint : ∀ a, Integrable (fun x => θ a * h a x) μ := fun a => by
    obtain ⟨B, hB⟩ := hbd a
    obtain ⟨L, hL⟩ := hLip a
    exact (Integrable.of_bound hL.continuous.measurable.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)).const_mul _
  unfold hb
  rw [integral_finsetSum _ fun a _ => hint a]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_const_mul, hmean a, mul_zero]

/-- The Dirichlet integral of a function with a bounded measurable weak gradient. -/
theorem dirichlet_toReal_of_wg {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    {f : Torus d → ℝ} {gg : Torus d → Fin d → ℝ} (hw : IsWeakGrad f gg) {K : ℝ}
    (hb : ∀ x k, |gg x k| ≤ K) (hm : ∀ k, Measurable fun x => gg x k) :
    (dirichlet μ f).toReal = ∫ x, ∑ k, gg x k ^ 2 ∂μ := by
  have hae : weakGrad f =ᵐ[μ] gg := hac.ae_le (weakGrad_ae_eq hw)
  have hnn : ∀ x, 0 ≤ ∑ k, gg x k ^ 2 := fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hint : Integrable (fun x => ∑ k, gg x k ^ 2) μ :=
    Integrable.of_bound (Finset.measurable_sum _ fun k _ => (hm k).pow_const 2).aestronglyMeasurable
      (d * K ^ 2) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
        calc ∑ k, gg x k ^ 2 ≤ ∑ _k : Fin d, K ^ 2 := Finset.sum_le_sum fun k _ => by
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x k) 2
          _ = d * K ^ 2 := by simp)
  unfold dirichlet
  rw [lintegral_congr_ae (hae.mono fun x hx => by rw [hx]; rfl : ∀ᵐ x ∂μ, ENNReal.ofReal (sqNorm (weakGrad f x)) =
      ENNReal.ofReal (∑ k, gg x k ^ 2)),← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall hnn), ENNReal.toReal_ofReal (integral_nonneg hnn)]

end Sec8
end SharpLSI.FL
