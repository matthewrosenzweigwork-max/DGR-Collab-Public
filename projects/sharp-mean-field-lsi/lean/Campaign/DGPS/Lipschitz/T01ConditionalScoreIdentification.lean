import DGPS.Lipschitz.T01ConditionalFactory
import DGPS.Lipschitz.T01LastIncrementReference
import DGPS.Lipschitz.T01ConditionalLevel

/-!
# The actual conditional mean-field score in reveal coordinates

The explicit centered-kernel convolution is measurable in the revealed values and current
coordinate. Disintegration identifies it with the bounded force representative `BS`; the
actual conditional density score then identifies the full integrand with the conditional
expectation expression used in the reveal-level argument.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

noncomputable def conditionalMeanFieldScoreSquare {d N : ℕ} (D : KData d)
    (v : Torus d → Tangent d) (Q : SharpLSI.Config N d → ℝ)
    (GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ)
    (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d) : ℝ :=
  ‖(SharpLSI.FL.condDensS Q S i a x)⁻¹ • WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i a x) +
    (v x + ∫ y, SharpLSI.FL.barDensS Q S a y • D.G1 x y ∂haar d)‖ ^ 2

private theorem measurable_conditional_gradient_vector {d N : ℕ}
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hGm : ∀ p, Measurable (fun y => GQ y p)) (S : Finset (Fin N)) (i : Fin N) :
    Measurable (fun p : (S → Torus d) × Torus d =>
      WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i p.1 p.2)) := by
  have hgcoord (k : Fin d) : Measurable (fun p : (S → Torus d) × Torus d =>
      SharpLSI.FL.gradCondS Q GQ S i p.1 p.2 k) :=
    SharpLSI.FL.measurable_gradCondS (S := S) (i := i) hQ hGm k
  have hgf : Measurable (fun p : (S → Torus d) × Torus d =>
      fun k => SharpLSI.FL.gradCondS Q GQ S i p.1 p.2 k) := measurable_pi_iff.mpr hgcoord
  exact (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp hgf

private theorem measurable_scalar_kernel_integral {α : Type*} [MeasurableSpace α] {d : ℕ}
    (ρ : α → Torus d → ℝ) (K : Torus d → Torus d → Tangent d)
    (hρ : Measurable (Function.uncurry ρ)) (hK : Measurable (Function.uncurry K)) :
    Measurable (fun p : α × Torus d => ∫ y, ρ p.1 y • K p.2 y ∂haar d) := by
  have hp1 : Measurable (fun p : (α × Torus d) × Torus d => (p.1.1, p.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hp2 : Measurable (fun p : (α × Torus d) × Torus d => (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm1 : Measurable (fun p : (α × Torus d) × Torus d => ρ p.1.1 p.2) := hρ.comp hp1
  have hm2 : Measurable (fun p : (α × Torus d) × Torus d => K p.1.2 p.2) := hK.comp hp2
  have hmF : Measurable (fun p : (α × Torus d) × Torus d =>
      ρ p.1.1 p.2 • K p.1.2 p.2) := hm1.smul hm2
  exact (hmF.stronglyMeasurable.integral_prod_right' (ν := haar d)).measurable

private theorem measurable_conditional_convolution {d N : ℕ} (D : KData d)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    (S : Finset (Fin N)) :
    Measurable (fun p : (S → Torus d) × Torus d =>
      ∫ y, SharpLSI.FL.barDensS Q S p.1 y • D.G1 p.2 y ∂haar d) := by
  exact measurable_scalar_kernel_integral (SharpLSI.FL.barDensS Q S) D.G1
    (SharpLSI.FL.measurable_barDensS hQ S) D.G1m

private theorem measurable_score_norm_sq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {r : Ω → ℝ} {g w : Ω → Tangent d} (hr : Measurable r)
    (hg : Measurable g) (hw : Measurable w) :
    Measurable (fun x => ‖r x • g x + w x‖ ^ 2) :=
  ((hr.smul hg).add hw).norm.pow_const 2

/-- Joint measurability of the actual conditional score integral. -/
theorem measurable_conditionalMeanFieldScoreSquare {d N : ℕ} (D : KData d)
    {v : Torus d → Tangent d} (hvm : Measurable v)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hGm : ∀ p, Measurable (fun y => GQ y p)) (S : Finset (Fin N)) (i : Fin N) :
    Measurable (Function.uncurry (conditionalMeanFieldScoreSquare D v Q GQ S i)) := by
  change Measurable (fun p : (S → Torus d) × Torus d =>
    ‖(SharpLSI.FL.condDensS Q S i p.1 p.2)⁻¹ •
        WithLp.toLp 2 (SharpLSI.FL.gradCondS Q GQ S i p.1 p.2) +
      (v p.2 + ∫ y, SharpLSI.FL.barDensS Q S p.1 y • D.G1 p.2 y ∂haar d)‖ ^ 2)
  have hρ : Measurable (fun p : (S → Torus d) × Torus d => SharpLSI.FL.condDensS Q S i p.1 p.2) :=
    SharpLSI.FL.measurable_condDensS hQ S i
  exact measurable_score_norm_sq hρ.inv (measurable_conditional_gradient_vector hQ hGm S i)
    ((hvm.comp measurable_snd).add (measurable_conditional_convolution D hQ S))

/-- The actual barycenter convolution is the force of the conditional barycenter law. -/
theorem conditional_centered_convolution_eq_BS {d N : ℕ} (D : KData d)
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N)) (hS : Sᶜ.Nonempty)
    (i : Fin N) :
    ∀ᵐ X ∂ν, ∀ k,
      (∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y • D.G1 (X i) y ∂haar d) k =
        SharpLSI.FL.BS (fun x y k => D.G1 x y k) ν S X (X i) k := by
  filter_upwards [SharpLSI.FL.barCond_ae_eq_densMeasure hQ hν (S := S)] with X hX
  intro k
  obtain ⟨h0, h1⟩ := SharpLSI.FL.barDensS_props hQ hS (SharpLSI.FL.restrictS S X)
  have hi := integrable_smul_slice D.G1m (SharpLSI.integrable_of_integral_eq_one' h1)
    (Eventually.of_forall fun y => D.G1b (X i) y)
  have he := (EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).integral_comp_comm hi
  have hc : (∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y • D.G1 (X i) y ∂haar d) k =
      ∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y * D.G1 (X i) y k ∂haar d := by
    simpa using he.symm
  rw [hc]
  unfold SharpLSI.FL.BS
  rw [hX, SharpLSI.integral_densMeasure' h0 h1]

/-- The explicit current mean-field score equals the inherited conditional-expectation score.
The only score premise is the factual joint-density identity stored in `ScoreData`. -/
theorem conditionalMeanFieldScoreSquare_eq_score {d N : ℕ}
    (A : InteractionData d) (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d))
    (D : KData d) {v : Torus d → Tangent d}
    (hv : ∀ x k, v x k = SharpLSI.lipGrad (SharpLSI.PhiMF A.V A.W μ) x k)
    {ν : Measure (SharpLSI.Config N d)} [IsProbabilityMeasure ν]
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ}
    {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    {s : Fin N → Fin d → SharpLSI.Config N d → ℝ}
    {bΔ : Torus d → Fin d → ℝ} {B : ℝ}
    (hscore : SharpLSI.FL.ScoreData A.V A.W (μ : Measure (Torus d)) ν Q c C GQ s
      (fun x y k => D.G1 x y k) bΔ B)
    (S : Finset (Fin N)) (i : Fin N) (hi : i ∉ S) :
    (fun X => conditionalMeanFieldScoreSquare D v Q GQ S i (SharpLSI.FL.restrictS S X) (X i)) =ᵐ[ν]
      fun X => ∑ k, (ν[fun Y => s i k Y -
        SharpLSI.FL.Gpart (fun x y k => D.G1 x y k) bΔ N Y i k | SharpLSI.FL.revSigma S i] X +
        SharpLSI.FL.BS (fun x y k => D.G1 x y k) ν S X (X i) k) ^ 2 := by
  have hcond := ae_all_iff.mpr fun k => actual_condScore_ae_eq A hA μ hscore hi k
  filter_upwards [hcond, conditional_centered_convolution_eq_BS D hscore.dens ν hscore.eq S
    ⟨i, Finset.mem_compl.mpr hi⟩ i] with X hX hB
  simp only [conditionalMeanFieldScoreSquare, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) (X i))⁻¹ *
      SharpLSI.FL.gradCondS Q GQ S i (SharpLSI.FL.restrictS S X) (X i) k +
      ((v (X i)).ofLp k +
        (∫ y, SharpLSI.FL.barDensS Q S (SharpLSI.FL.restrictS S X) y • D.G1 (X i) y ∂haar d).ofLp k) = _
  rw [hv (X i) k, hB k]
  have he := hX k
  rw [div_eq_mul_inv] at he
  nlinarith [he]

end DGPS.Lipschitz
