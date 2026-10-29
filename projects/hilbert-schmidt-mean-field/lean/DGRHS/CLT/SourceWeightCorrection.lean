/- Proper source Gibbs weights from actual canonical moments and an actual
bounded one-body potential. Measurability of the canonical exponent is derived
from proper integrability of its exponential. No source moment is assumed. -/
import DGRHS.CLT.SourceEnergyTilt
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma sourceParticleExponent_mul_parameter (h : S × S → ℝ) (F : S → ℝ)
    (I β p : ℝ) (N : ℕ) (x : Fin N → S) :
    sourceParticleExponent h F I (p*β) N x = p*sourceParticleExponent h F I β N x := by
  dsimp [sourceParticleExponent]
  ring

theorem sourceWeight_of_canonical_moments (h : S × S → ℝ) (F : S → ℝ)
    (hF : Integrable F μ) (K : ℝ) (hK : ∀ᵐ x ∂μ,F x ≤ K)
    (I γ : ℝ) (hγ : 0 ≤ γ) (C : ℝ)
    (hProper : ∀ N,1 ≤ N → Integrable
      (fun x : Fin N → S => Real.exp (-γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)))
    (hBound : ∀ N,1 ≤ N → (∫ x : Fin N → S,
      Real.exp (-γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) :
    ∀ N,Integrable (fun x : Fin N → S => Real.exp (sourceParticleExponent h F I γ N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → S,Real.exp (sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
        max (Real.exp (γ*(K-I))*C) (Real.exp (-γ*I)) := by
  classical
  intro N
  by_cases hN : N = 0
  · subst N
    have he : (fun x : Fin 0 → S => Real.exp (sourceParticleExponent h F I γ 0 x)) =
        fun _ => Real.exp (-γ*I) := by
      funext x
      simp [sourceParticleExponent,DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
        DGRHS.CanonicalVariance.offDiagonalSum]
    rw [he]
    exact ⟨integrable_const _,by simpa using le_max_right (Real.exp (γ*(K-I))*C) (Real.exp (-γ*I))⟩
  have hn : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
  let P := Measure.pi (fun _ : Fin N => μ)
  let A : (Fin N → S) → ℝ := fun x => -γ/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x
  have hiA : Integrable (fun x => Real.exp (A x)) P := hProper N hn
  have hA : AEMeasurable A P := by
    have ha := Real.measurable_log.comp_aemeasurable hiA.aestronglyMeasurable.aemeasurable
    simpa only [Function.comp_def,Real.log_exp] using ha
  have hFi : ∀ i : Fin N,AEMeasurable (fun x : Fin N → S => F (x i)) P :=
    fun i => hF.aestronglyMeasurable.aemeasurable.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving
  have hsum : ∀ s : Finset (Fin N),AEMeasurable (fun x : Fin N → S => ∑ i ∈ s,F (x i)) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (aemeasurable_const : AEMeasurable (fun _ : Fin N → S => (0 : ℝ)) P)
    | @insert i s hi ih =>
      have ha := (hFi i).add ih
      convert ha using 1
      funext x
      simp only [Finset.sum_insert hi, Pi.add_apply]
  have hY : AEMeasurable (sourceParticleExponent h F I γ N) P := by
    exact ((hA.add (((hsum Finset.univ).const_mul (N : ℝ)⁻¹).const_mul γ)).sub aemeasurable_const)
  have hcoord : ∀ i : Fin N,∀ᵐ x ∂P,F (x i) ≤ K :=
    fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hK
  have hDom : ∀ᵐ x ∂P,Real.exp (sourceParticleExponent h F I γ N x) ≤
      Real.exp (γ*(K-I))*Real.exp (A x) := by
    filter_upwards [ae_all_iff.mpr hcoord] with x hx
    have hsumK : (∑ i : Fin N,F (x i)) ≤ (N : ℝ)*K := by
      calc
        _ ≤ ∑ _i : Fin N,K := Finset.sum_le_sum (fun i _ => hx i)
        _ = _ := by simp
    have hn' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have havg : (N : ℝ)⁻¹*∑ i : Fin N,F (x i) ≤ K := by
      have ht := mul_le_mul_of_nonneg_left hsumK (inv_nonneg.mpr (Nat.cast_nonneg N))
      simpa only [←mul_assoc,inv_mul_cancel₀ hn',one_mul] using ht
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [sourceParticleExponent,A]
    nlinarith [mul_le_mul_of_nonneg_left havg hγ]
  have hi : Integrable (fun x => Real.exp (sourceParticleExponent h F I γ N x)) P :=
    (hiA.const_mul (Real.exp (γ*(K-I)))).mono'
      (Real.measurable_exp.comp_aemeasurable hY).aestronglyMeasurable
      (hDom.mono fun x hx => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx)
  refine ⟨hi,?_⟩
  apply le_trans _ (le_max_left _ _)
  calc
    _ ≤ ∫ x,Real.exp (γ*(K-I))*Real.exp (A x) ∂P :=
      integral_mono_ae hi (hiA.const_mul _) hDom
    _ = Real.exp (γ*(K-I))*(∫ x,Real.exp (A x) ∂P) := integral_const_mul _ _
    _ ≤ Real.exp (γ*(K-I))*C := mul_le_mul_of_nonneg_left (hBound N hn) (Real.exp_pos _).le
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceParticleExponent_mul_parameter
#print axioms DGRHS.CLT.sourceWeight_of_canonical_moments
#check @DGRHS.CLT.sourceWeight_of_canonical_moments
