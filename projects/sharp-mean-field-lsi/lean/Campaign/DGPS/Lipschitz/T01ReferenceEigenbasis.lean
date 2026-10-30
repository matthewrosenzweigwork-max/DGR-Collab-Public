import DGPS.Lipschitz.T01DependencyBridge
import DGPS.Analysis.LSITensorization
import SharpSymmetricLSI.Paper.EnergyParseval2

/-!
# Reference eigenbasis conversion for the direct-Lipschitz replacement argument

The old replacement engine uses the lifted weak-gradient definition. The campaign tests weak
gradients against periodic functions. Mollification and the existing closed-graph theorem
identify these definitions on the actual two-sided weighted Sobolev domain.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace DGPS.Lipschitz

open DGPS.Analysis DGPS.Analysis.CompactResolvent KernelApproximation

/-- A legacy weak-gradient pair with square-integrable function and Euclidean gradient
satisfies the campaign periodic weak-gradient identity. -/
theorem isWeakGradient_of_legacy_pair {d : ℕ} {u : Torus d → ℝ}
    {g : Torus d → Fin d → ℝ} (hw : SharpLSI.IsWeakGrad u g)
    (hu : MemLp u 2 (haar d))
    (hg : MemLp (fun x => WithLp.toLp 2 (g x)) 2 (haar d)) :
    IsWeakGradient u (fun x => WithLp.toLp 2 (g x)) := by
  have hu1 := hu.integrable one_le_two
  have hgj : ∀ j, MemLp (fun x => g x j) 2 (haar d) :=
    fun j => memLp_coord hg j
  have hpair : ∀ n, IsWeakGradient (SharpLSI.moll n u)
      (fun x => WithLp.toLp 2 (fun j => SharpLSI.moll n (fun y => g y j) x)) := by
    intro n
    have hs : IsSmoothPeriodic (SharpLSI.moll n u) :=
      SharpLSI.moll_comp_liftT_contDiff n hu1
    convert hs.isWeakGradient using 1
    funext x
    apply WithLp.ofLp_injective
    funext j
    change SharpLSI.moll n (fun y => g y j) x = coordPartial j (SharpLSI.moll n u) x
    unfold coordPartial
    rw [SharpLSI.moll_comp_liftT, SharpLSI.fderiv_mollL_of_isWeakGrad hw n (SharpLSI.secT x) j]
    rfl
  exact IsWeakGradient.of_tendsto_L1 hu hg hpair
    (tendsto_lintegral_moll_sub hu) (fun j => tendsto_lintegral_moll_sub (hgj j))

/-- On a campaign weighted reference, every legacy Sobolev test has its genuine chosen
gradient in the campaign domain. -/
theorem isWeakGradient_of_legacy_memH1 {d : ℕ} (S : Spec d) {u : Torus d → ℝ}
    (hu : SharpLSI.MemH1 S.mu u) :
    IsWeakGradient u (fun x => WithLp.toLp 2 (SharpLSI.weakGrad u x)) := by
  let : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hu2 : MemLp u 2 (haar d) := (memLp_wMeasure_iff S.pos S.bound).1 hu.2.1
  have hg2 : MemLp (fun x => WithLp.toLp 2 (SharpLSI.weakGrad u x)) 2 (haar d) := by
    refine memLp_piLp_iff.mpr fun j => ?_
    exact (memLp_wMeasure_iff S.pos S.bound).1
      (SharpLSI.memLp_grad_comp wMeasure_ac_haar hu j)
  exact isWeakGradient_of_legacy_pair (SharpLSI.isWeakGrad_weakGrad hu.1) hu2 hg2

/-- The exact campaign weak eigen-equation gives the legacy reference-eigenbasis interface.
The order and eigen-equation hypotheses are retained by `exists_spec_aux_eigen`; no
semiconvexity or particle lower bound occurs here. -/
theorem legacy_reference_eigenbasis {d : ℕ} (S : Spec d) (A : Aux S)
    (hmono : Monotone S.lam)
    (heig : ∀ j (f : Hw d S.w) (Y : Torus d → Tangent d),
      IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm S.w (A.g j) Y = S.lam j * inner ℝ (S.e j) f) :
    SharpLSI.IsRefEigenbasis S.mu S.v S.lam where
  zero := funext A.v0
  memH1 := fun j => by
    obtain ⟨hj, -⟩ := Analysis.legacy_memH1 (A.gw j)
    exact ⟨hj.1, (memLp_wMeasure_iff S.pos S.bound).2 hj.2.1,
      (memLp_wMeasure_iff S.pos S.bound).2 hj.2.2⟩
  orthonormal := S.orth
  complete := fun f hf hz => by
    have hs := S.hasSum_sq hf
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0)] at hs
    have hi : ∫ x, f x ^ 2 ∂S.mu = 0 := hs.unique hasSum_zero
    have hsq : (fun x => f x ^ 2) =ᵐ[S.mu] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hf.integrable_sq).1 hi
    filter_upwards [hsq] with x hx
    exact (sq_eq_zero_iff).1 hx
  eigen := fun j φ hφ => by
    have hW := isWeakGradient_of_legacy_memH1 S hφ
    let Y : Torus d → Tangent d := fun x => WithLp.toLp 2 (SharpLSI.weakGrad φ x)
    have hW' : IsWeakGradient ((hφ.2.1.toLp φ : Hw d S.w) : Torus d → ℝ) Y :=
      hW.congr_ae (S.ae_haar hφ.2.1.coeFn_toLp.symm) (EventuallyEq.refl _ _)
    have hj := S.ae_mu (Analysis.legacy_memH1 (A.gw j)).2
    calc
      (∫ x, ∑ k, SharpLSI.weakGrad (S.v j) x k * SharpLSI.weakGrad φ x k ∂S.mu)
          = ∫ x, inner ℝ (A.g j x) (Y x) ∂S.mu := by
            refine integral_congr_ae ?_
            filter_upwards [hj] with x hx
            simp [hx, Y, PiLp.inner_apply, mul_comm]
      _ = weightedForm S.w (A.g j) Y := by
            unfold weightedForm
            rw [S.integral_mu]
            congr 1
            funext x
            simp [smul_eq_mul, mul_comm]
      _ = S.lam j * inner ℝ (S.e j) (hφ.2.1.toLp φ) := heig j _ Y hW'
      _ = S.lam j * ∫ x, S.v j x * φ x ∂S.mu := by
            rw [S.coeff_eq hφ.2.1]
            congr 1
            exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  mono := hmono

end DGPS.Lipschitz
