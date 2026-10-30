import DGPS.Lipschitz.KernelApproximation
import DGPS.Analysis.RelativeFisher
import SharpSymmetricLSI.Paper.LemmaA2_28

/-!
# The legacy pair gradient of campaign kernel data

The explicit bounded slice gradients in `KData` agree almost everywhere with the chosen
legacy weak gradient on the two-particle torus. This identifies the actual Sobolev error in
the old finite-rank approximation interface, including for residual kernels.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation

/-- Identification of both coordinate blocks of the legacy pair weak gradient. -/
theorem legacy_pair_weakGrad_ae {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hac : μ ≪ haar d) (D : KData d) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ), ∀ k : Fin d,
      SharpLSI.weakGradC (SharpLSI.kerC2 D.K) X 0 k = D.G1 (X 0) (X 1) k ∧
      SharpLSI.weakGradC (SharpLSI.kerC2 D.K) X 1 k = D.G2 (X 0) (X 1) k := by
  have hLip1 : ∀ y, TorusLipschitzWith D.B fun x => D.K x y :=
    fun y x x' => D.lip1 x x' y
  have hLip2 : ∀ x, TorusLipschitzWith D.B fun y => D.K x y :=
    fun x y y' => D.swap.lip1 y y' x
  have hs1 : ∀ y, SharpLSI.lipGrad (fun x => D.K x y) =ᵐ[haar d]
      fun x k => D.G1 x y k := fun y =>
    SharpLSI.weakGrad_ae_unique
      (SharpLSI.isWeakGrad_lipGrad (D.slice_cont y)
        (DGPS.RelativeFisher.lipschitzWith_comp_lift (hLip1 y)))
      (D.g1 y).isWeakGrad
  have hs2 : ∀ x, SharpLSI.lipGrad (fun y => D.K x y) =ᵐ[haar d]
      fun y k => D.G2 x y k := fun x =>
    SharpLSI.weakGrad_ae_unique
      (SharpLSI.isWeakGrad_lipGrad (D.swap.slice_cont x)
        (DGPS.RelativeFisher.lipschitzWith_comp_lift (hLip2 x)))
      (D.g2 x).isWeakGrad
  have hp1 : ∀ k : Fin d, ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ),
      SharpLSI.lipGrad (fun x => D.K x (X 1)) (X 0) k = D.G1 (X 0) (X 1) k := by
    intro k
    have hm : MeasurableSet {p : Torus d × Torus d |
        SharpLSI.lipGrad (fun x => D.K x p.2) p.1 k = D.G1 p.1 p.2 k} :=
      measurableSet_eq_fun (SharpLSI.measurable_slice_lipGrad D.Kc k).1
        ((EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).measurable.comp D.G1m)
    have hh : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ,
        SharpLSI.lipGrad (fun x => D.K x y) x k = D.G1 x y k :=
      Eventually.of_forall fun y => by
        have hy : SharpLSI.lipGrad (fun x => D.K x y) =ᵐ[μ] fun x k => D.G1 x y k :=
          hac.ae_le (hs1 y)
        exact hy.mono fun x hx => congrFun hx k
    have hp : ∀ᵐ p ∂μ.prod μ,
        SharpLSI.lipGrad (fun x => D.K x p.2) p.1 k = D.G1 p.1 p.2 k :=
      (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hh)
    exact SharpLSI.ae_pi_two_of_ae_prod (d := d) (μ := μ)
      (p := fun x y => SharpLSI.lipGrad (fun x => D.K x y) x k = D.G1 x y k) hp
  have hp2 : ∀ k : Fin d, ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => μ),
      SharpLSI.lipGrad (fun y => D.K (X 0) y) (X 1) k = D.G2 (X 0) (X 1) k := by
    intro k
    have hm : MeasurableSet {p : Torus d × Torus d |
        SharpLSI.lipGrad (fun y => D.K p.1 y) p.2 k = D.G2 p.1 p.2 k} :=
      measurableSet_eq_fun (SharpLSI.measurable_slice_lipGrad D.Kc k).2
        ((EuclideanSpace.proj k : Tangent d →L[ℝ] ℝ).measurable.comp D.G2m)
    have hh : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
        SharpLSI.lipGrad (fun y => D.K x y) y k = D.G2 x y k :=
      Eventually.of_forall fun x => by
        have hx : SharpLSI.lipGrad (fun y => D.K x y) =ᵐ[μ] fun y k => D.G2 x y k :=
          hac.ae_le (hs2 x)
        exact hx.mono fun y hy => congrFun hy k
    exact SharpLSI.ae_pi_two_of_ae_prod (d := d) (μ := μ)
      (p := fun x y => SharpLSI.lipGrad (fun y => D.K x y) y k = D.G2 x y k)
      ((Measure.ae_prod_iff_ae_ae hm).mpr hh)
  have hw := SharpLSI.weakGradC_kerC_ae hac D.Kc D.B_nonneg D.B_nonneg
    (fun y a b => (le_abs_self _).trans (lift_lipschitz D.B_nonneg (hLip1 y) a b))
    (fun x a b => (le_abs_self _).trans (lift_lipschitz D.B_nonneg (hLip2 x) a b))
  filter_upwards [hw, ae_all_iff.mpr hp1, ae_all_iff.mpr hp2] with X hX h1 h2
  intro k
  exact ⟨(hX k).1.trans (h1 k), (hX k).2.trans (h2 k)⟩

/-- The squared legacy pair gradient is the sum of the two explicit Euclidean squared norms. -/
theorem legacy_pair_gradSqC_ae {d : ℕ} (S : Spec d) (_aux : Aux S) (D : KData d) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => S.mu),
      SharpLSI.gradSqC (SharpLSI.kerC2 D.K) X =
        ‖D.G1 (X 0) (X 1)‖ ^ 2 + ‖D.G2 (X 0) (X 1)‖ ^ 2 := by
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  filter_upwards [legacy_pair_weakGrad_ae (μ := S.mu)
    DGPS.Analysis.CompactResolvent.wMeasure_ac_haar D] with X hX
  simp only [SharpLSI.gradSqC, Fin.sum_univ_two]
  calc
    (∑ k, SharpLSI.weakGradC (SharpLSI.kerC2 D.K) X 0 k ^ 2) +
        ∑ k, SharpLSI.weakGradC (SharpLSI.kerC2 D.K) X 1 k ^ 2
        = (∑ k, D.G1 (X 0) (X 1) k ^ 2) + ∑ k, D.G2 (X 0) (X 1) k ^ 2 := by
          congr 1
          · exact Finset.sum_congr rfl fun k _ => congrArg (fun t : ℝ => t ^ 2) (hX k).1
          · exact Finset.sum_congr rfl fun k _ => congrArg (fun t : ℝ => t ^ 2) (hX k).2
    _ = _ := by simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

end DGPS.Lipschitz
