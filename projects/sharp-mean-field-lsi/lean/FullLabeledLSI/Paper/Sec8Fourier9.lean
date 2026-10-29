import FullLabeledLSI.Paper.Sec8Fourier8
import FullLabeledLSI.Paper.Sec8Cosine

/-!
# Section 8.5 (Corollary 8.4), part 9: the free species and the Fisher identity in dimension `d`

* `D2 ρ = ∑_k ∫ (∂_k √ρ)²`;
* `lsi_species`: `a H(ρ|m) ≤ 2 D2 ρ` and `H(ρ|m) < ∞` for `√ρ ∈ H¹`;
* `dissipation_zero_D2`: the free dissipation is `4 D2`;
* `fisher_identity_d`: `∑ θ_a 4 D2(ρ_a) = 4 D2(ρ̄) + ∑ θ_a I(ρ_a|ρ̄)`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

/-- `D2 ρ = ∑_k ∫ (∂_k √ρ)² dm`. -/
noncomputable def D2 (ρ : Torus d → ℝ) : ℝ :=
  ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d

theorem memLp_grad_comp {u : Torus d → ℝ} (hH1 : MemH1 (haar d) u) (k : Fin d) :
    MemLp (fun x => weakGrad u x k) 2 (haar d) :=
  hH1.2.2.of_le ((isWeakGrad_weakGrad hH1.1).aestronglyMeasurable_grad k)
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)

theorem D2_nonneg (ρ : Torus d → ℝ) : 0 ≤ D2 ρ :=
  Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _

theorem dirichlet_sqrt_eq {ρ : Torus d → ℝ} (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    dirichlet (haar d) (fun x => Real.sqrt (ρ x)) = ENNReal.ofReal (D2 ρ) := by
  have hg2 := memLp_grad_comp hH1
  unfold dirichlet sqNorm D2
  rw [← integral_finsetSum _ fun k _ => (hg2 k).integrable_sq,
    ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun k _ => (hg2 k).integrable_sq)
      (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)]

/-- The logarithmic Sobolev inequality for a density `ρ` with `√ρ ∈ H¹`. -/
theorem lsi_species {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar d) ≠ ⊤ ∧
      aCos * (klDiv (densMeasure ρ) (haar d)).toReal ≤ 2 * D2 ρ := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  set h : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hh
  have hsq : (fun x => h x ^ 2) = ρ := funext fun x => Real.sq_sqrt (hρ0 x)
  have hKL : klDiv (densMeasure ρ) (haar d) = ent (haar d) (fun x => h x ^ 2) := by
    rw [hsq, klDiv_densMeasure' hρ0 hρ1, ent, if_pos (integrable_of_integral_eq_one' hρ1), hρ1]
    simp
  have hLSI : ent (haar d) (fun x => h x ^ 2) ≤ ENNReal.ofReal (2 / aCos) * dirichlet (haar d) h :=
    lsi_torus_H1 (ι := Fin d) hH1
  rw [← hKL, dirichlet_sqrt_eq hH1, ← ENNReal.ofReal_mul (by positivity)] at hLSI
  have hne : klDiv (densMeasure ρ) (haar d) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLSI
  refine ⟨hne, ?_⟩
  have hKr : (klDiv (densMeasure ρ) (haar d)).toReal ≤ 2 / aCos * D2 ρ :=
    ENNReal.toReal_le_of_le_ofReal (by have := D2_nonneg ρ; positivity) hLSI
  have := mul_le_mul_of_nonneg_left hKr ha0.le
  rwa [show aCos * (2 / aCos * D2 ρ) = 2 * D2 ρ by field_simp] at this

theorem dissipation_zero_D2 {ρ : Torus d → ℝ} (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    dissipation (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) ρ = ENNReal.ofReal (4 * D2 ρ) := by
  have hw := hasWeakGrad_zero ρ
  unfold dissipation
  rw [if_pos ⟨hH1, hw⟩]
  have hae : weakGrad (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) =ᵐ[haar d] 0 := by
    rw [convDens_zero]; exact weakGrad_ae_eq (isWeakGrad_const 0)
  have hg2 := memLp_grad_comp hH1
  have hint : Integrable (fun x => ∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k) ^ 2) (haar d) :=
    integrable_finsetSum _ fun k _ => ((hg2 k).const_mul 2).integrable_sq
  have e1 : ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k +
        Real.sqrt (ρ x) * weakGrad (fun y => (fun _ => (0 : ℝ)) y +
          convDens (fun _ _ => (0 : ℝ)) ρ y) x k) ^ 2) ∂haar d =
      ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k) ^ 2) ∂haar d := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have hx0 : ∀ k, weakGrad (fun y => (fun _ => (0 : ℝ)) y +
        convDens (fun _ _ => (0 : ℝ)) ρ y) x k = 0 := fun k => by
      have := congrFun hx k; simpa using this
    simp only [hx0, mul_zero, add_zero]
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _)]
  congr 1
  rw [integral_finsetSum _ fun k _ => ((hg2 k).const_mul 2).integrable_sq]
  unfold D2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem fisher_identity_d (F : Family d) (hF : F.Admissible) :
    ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (4 * D2 (F.ρ a)) =
      ENNReal.ofReal (4 * D2 F.bar) +
        ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar := by
  obtain ⟨-, hD, -⟩ := species_decomposition (hyp_zero (d := d)) F hF
  unfold msDiss at hD
  simp_rw [speciesDiss_zero] at hD
  rw [dissipation_zero_D2 (memH1_sqrtBar F hF)] at hD
  rw [← hD]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dissipation_zero_D2 (hF.2.2 a).2.2]

end Sec8
end SharpLSI.FL
