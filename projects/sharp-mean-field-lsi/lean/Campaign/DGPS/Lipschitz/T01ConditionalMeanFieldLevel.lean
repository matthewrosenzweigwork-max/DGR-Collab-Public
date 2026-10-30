import DGPS.Lipschitz.T01ConditionalScoreIdentification
import DGPS.Lipschitz.T01ConditionalIntegrability
import FullLabeledLSI.Paper.Sec5LND

/-!
# The actual multispecies conditional mean-field inequality

The pointwise current-family rate theorem, genuine conditional score identification, and
conditional disintegration give the fixed-revealed-set inequality used in defective absorption.
All input score data are factual density/weak-gradient/force statements; no defective inequality
or legacy semiconvexity hypothesis is assumed.
-/

open MeasureTheory InformationTheory ProbabilityTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

/-- The fixed-set integration step shared by scalar and species pointwise generators. -/
theorem actual_meanfield_S_of_pointwise {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ} (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card)
    (hpoint : ∀ᵐ X ∂ν,
      ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
          (μ : Measure (Torus d))).toReal + SharpLSI.Jfun A.W (μ : Measure (Torus d))
          (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ x,
        ENNReal.ofReal (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
        ENNReal.ofReal (conditionalMeanFieldScoreSquare D v Q GQ S i (SharpLSI.FL.restrictS S X) x)) :
    2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
      (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X))
        (μ : Measure (Torus d))).toReal ∂ν +
      ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, ∑ k,
        (ν[fun Y => s i k Y - SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) bΔ N Y i k |
          SharpLSI.FL.revSigma S i] X +
          SharpLSI.FL.BS (fun x y k => D.G1 x y k) ν S X (X i) k) ^ 2 ∂ν := by
  classical
  let L : (S → Torus d) → ℝ := fun a => 2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
    (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i a)) (μ : Measure (Torus d))).toReal +
    SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S a)))
  let H := conditionalMeanFieldScoreSquare D v Q GQ S
  have hL := conditional_rate_left_integrable A μ hscore.dens ν hscore.eq hH S hS r
  have hHm : ∀ i ∈ Sᶜ, Measurable (Function.uncurry (H i)) := fun i _ =>
    measurable_conditionalMeanFieldScoreSquare D hvm hscore.dens hscore.gradM S i
  have hH0 : ∀ i ∈ Sᶜ, ∀ a x, 0 ≤ H i a x := fun i _ a x => sq_nonneg _
  have hHi : ∀ i ∈ Sᶜ, Integrable (fun X => H i (SharpLSI.FL.restrictS S X) (X i)) ν := by
    intro i hi
    exact (actual_meanfield_score_square_integrable hscore S hS i).congr
      (conditionalMeanFieldScoreSquare_eq_score A hA μ D hvc hscore S i
        (Finset.mem_compl.mp hi)).symm
  have hcore := integrate_conditional_density_bound hscore.dens ν hscore.eq S L hL H hHm hH0 hHi hpoint
  have hKL : ∀ i ∈ Sᶜ, Integrable (fun X =>
      (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
        (μ : Measure (Torus d))).toReal) ν := by
    intro i hi
    apply (conditional_information_integrable ν (μ : Measure (Torus d)) hH S i
      (Finset.mem_compl.mp hi)).1.congr
    filter_upwards [SharpLSI.FL.condLawS_ae_eq_X hscore.dens (Finset.mem_compl.mp hi) hscore.eq]
      with X hX
    rw [hX]
  have hJ : Integrable (fun X => SharpLSI.Jfun A.W (μ : Measure (Torus d))
      (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X)))) ν := by
    apply (conditional_Jfun_integrable A μ ν S hS).congr
    filter_upwards [SharpLSI.FL.barCond_ae_eq_densMeasure hscore.dens hscore.eq (S := S)] with X hX
    rw [hX]
  have hLeq : (∫ X, L (SharpLSI.FL.restrictS S X) ∂ν) =
      2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
        (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X))
          (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν) := by
    dsimp only [L]
    rw [integral_const_mul, integral_add ((integrable_finsetSum _ hKL).const_mul _) hJ,
      integral_const_mul, integral_finsetSum _ hKL]
    congr 1
    apply congrArg₂ (· + ·)
    · congr 1
      refine Finset.sum_congr rfl fun i hi => integral_congr_ae ?_
      filter_upwards [SharpLSI.FL.condLawS_ae_eq_X hscore.dens (Finset.mem_compl.mp hi) hscore.eq]
        with X hX
      rw [hX]
    · apply integral_congr_ae
      filter_upwards [SharpLSI.FL.barCond_ae_eq_densMeasure hscore.dens hscore.eq (S := S)] with X hX
      rw [hX]
  rw [hLeq] at hcore
  refine hcore.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun i hi => integral_congr_ae ?_
  exact conditionalMeanFieldScoreSquare_eq_score A hA μ D hvc hscore S i (Finset.mem_compl.mp hi)

/-- The actual current multispecies rate controls one arbitrary revealed set. -/
theorem actual_species_meanfield_S {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    (S : Finset (Fin N)) (hS : 1 ≤ Sᶜ.card) :
    2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
      (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X))
        (μ : Measure (Torus d))).toReal ∂ν +
      ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, ∑ k,
        (ν[fun Y => s i k Y - SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) bΔ N Y i k |
          SharpLSI.FL.revSigma S i] X +
          SharpLSI.FL.BS (fun x y k => D.G1 x y k) ν S X (X i) k) ^ 2 ∂ν := by
  apply actual_meanfield_S_of_pointwise A hA μ D hvm hvc hscore hH S hS
  exact ae_conditional_species_explicit_score A b μ hμ D hD hv hr hrr hscore.dens
    hscore.gradW hscore.gradM hscore.gradL2 ν hscore.eq S (Finset.card_pos.mp hS)



/-- Finite reveal averaging of either actual pointwise rate generator. -/
theorem actual_level_meanfield_of_pointwise {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ}
    (hpoint : ∀ (S : Finset (Fin N)), 1 ≤ Sᶜ.card → ∀ᵐ X ∂ν,
      ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
          (μ : Measure (Torus d))).toReal + SharpLSI.Jfun A.W (μ : Measure (Torus d))
          (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ x,
        ENNReal.ofReal (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
        ENNReal.ofReal (conditionalMeanFieldScoreSquare D v Q GQ S i (SharpLSI.FL.restrictS S X) x))
    {j : ℕ} (hj : j < N) :
    2 * r * ((SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal +
      SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j) ≤
      SharpLSI.FL.mfDiss (fun x y k => D.G1 x y k) bΔ ν s j := by
  classical
  rw [hRev_toReal_eq_of_finite_entropy ν (μ : Measure (Torus d)) hH hj,
    condMeanS_eq_avg1R_Jfun_of_current_data A μ ν hj]
  unfold SharpLSI.FL.mfDiss SharpLSI.FL.avg1R
  have hkey : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X,
        (klDiv (SharpLSI.FL.condLawS ν S i (SharpLSI.FL.restrictS S X))
          (μ : Measure (Torus d))).toReal ∂ν +
        ∫ X, SharpLSI.Jfun A.W (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ, ∫ X, ∑ k,
        (ν[fun Y => s i k Y - SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) bΔ N Y i k |
          SharpLSI.FL.revSigma S i] X +
          SharpLSI.FL.BS (fun x y k => D.G1 x y k) ν S X (X i) k) ^ 2 ∂ν := by
    intro S hS
    have hcard : 1 ≤ Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
      omega
    exact actual_meanfield_S_of_pointwise A hA μ D hvm hvc hscore hH S hcard (hpoint S hcard)
  have hcn : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, (Sᶜ.card : ℝ) ≠ 0 := by
    intro S hS
    have hpos : 0 < Sᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin, (Finset.mem_powersetCard.mp hS).2]
      omega
    exact_mod_cast hpos.ne'
  have hconst : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∀ x : ℝ,
      (Sᶜ.card : ℝ)⁻¹ * ∑ _i ∈ Sᶜ, x = x := by
    intro S hS x
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp [hcn S hS]
  beta_reduce
  rw [Finset.sum_congr rfl fun S hS => hconst S hS (∫ X, SharpLSI.Jfun A.W
      (μ : Measure (Torus d)) (SharpLSI.FL.barCond ν S X) ∂ν),
    ← mul_add, ← Finset.sum_add_distrib]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hkey)
    (inv_nonneg.mpr (Nat.cast_nonneg _)))
  rw [← Finset.mul_sum]
  ring

theorem actual_species_level_meanfield {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    {j : ℕ} (hj : j < N) :
    2 * r * ((SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal +
      SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j) ≤
      SharpLSI.FL.mfDiss (fun x y k => D.G1 x y k) bΔ ν s j := by
  apply actual_level_meanfield_of_pointwise A hA μ D hvm hvc hscore hH (j := j) (hj := hj)
  intro S hS
  exact ae_conditional_species_explicit_score A b μ hμ D hD hv hr hrr hscore.dens
    hscore.gradW hscore.gradM hscore.gradL2 ν hscore.eq S (Finset.card_pos.mp hS)

/-- The common per-level bound for either proved pointwise rate generator. -/
theorem actual_level_bound_of_pointwise {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ}
    (hpoint : ∀ (S : Finset (Fin N)), 1 ≤ Sᶜ.card → ∀ᵐ X ∂ν,
      ENNReal.ofReal (2 * r * ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        (klDiv (SharpLSI.densMeasure (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X)))
          (μ : Measure (Torus d))).toReal + SharpLSI.Jfun A.W (μ : Measure (Torus d))
          (SharpLSI.densMeasure (SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X))))) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) * ∑ i ∈ Sᶜ, ∫⁻ x,
        ENNReal.ofReal (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
        ENNReal.ofReal (conditionalMeanFieldScoreSquare D v Q GQ S i (SharpLSI.FL.restrictS S X) x))
    {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : j < N) :
    2 * r * ((SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal +
      SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j) ≤
      (1 + ε) * ((N : ℝ)⁻¹ * SharpLSI.FL.fisherS ν s) +
        (1 + 1 / ε) * SharpLSI.FL.forceDelta (fun x y k => D.G1 x y k) bΔ ν j := by
  exact (actual_level_meanfield_of_pointwise A hA μ D hvm hvc hscore hH hpoint hj).trans
    (SharpLSI.FL.level_young hscore hε hj)

theorem actual_species_level_bound {d N : ℕ} (A : InteractionData d) (hA : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (D : KData d) (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d} (hvm : Measurable v)
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    (hvc : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) ≠ ⊤)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    {ε : ℝ} (hε : 0 < ε) {j : ℕ} (hj : j < N) :
    2 * r * ((SharpLSI.FL.hRev ν (μ : Measure (Torus d)) j).toReal +
      SharpLSI.FL.condMeanS ν 2 (SharpLSI.FL.Bk A.W (μ : Measure (Torus d))) j) ≤
      (1 + ε) * ((N : ℝ)⁻¹ * SharpLSI.FL.fisherS ν s) +
        (1 + 1 / ε) * SharpLSI.FL.forceDelta (fun x y k => D.G1 x y k) bΔ ν j := by
  exact (actual_species_level_meanfield A hA b μ hμ D hD hvm hv hvc hscore hH hr hrr hj).trans
    (SharpLSI.FL.level_young hscore hε hj)

end DGPS.Lipschitz
