import DGRHS.Gaussian.PeriodicParticleStarIntegral
import Mathlib.Analysis.Convex.Jensen

/-! Actual beta<2d partition properness by Jensen over particle stars.
All star integrals are computed under the genuine normalized Haar product.
No collision-stratum integrability is assumed. -/
noncomputable section
open MeasureTheory Set Filter Real
open scoped Classical BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicParticleStar_eq_exp (γ : ℝ) (N : ℕ) (i : Fin N) (x : Fin N → PeriodicTorus ι) :
    periodicParticleStar γ N i x =
      Real.exp (γ*∑ j : Fin N,if i=j then 0 else periodicLogKernel (x i-x j)) := by
  rw [Finset.mul_sum,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i=j <;> simp [periodicParticleStar,hij]

lemma periodicParticleExponent_star_jensen (β : ℝ) (N : ℕ) (hN : 1≤N)
    (x : Fin N → PeriodicTorus ι) :
    Real.exp (periodicParticleExponent β N x) ≤
      (N:ℝ)⁻¹*∑ i : Fin N,periodicParticleStar (β/2) N i x := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  have hw : (∑ _i : Fin N,(N:ℝ)⁻¹)=1 := by simp [hn]
  have hj := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := fun _ : Fin N => (N:ℝ)⁻¹)
    (p := fun i => β/2*∑ j : Fin N,if i=j then 0 else periodicLogKernel (x i-x j))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg N)) hw (fun _ _ => mem_univ _)
  simp only [smul_eq_mul,← Finset.mul_sum,← periodicParticleStar_eq_exp] at hj
  convert hj using 1
  congr 1
  unfold periodicParticleExponent
  field_simp
  <;> ring

/-- Proper actual Gibbs density and a finite upper bound for every N>=1. -/
theorem periodicParticleDensity_integrable_upper (β : ℝ) (hβ0 : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (periodicParticleExponent β N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    (∫ x : Fin N → PeriodicTorus ι,Real.exp (periodicParticleExponent β N x)
      ∂Measure.pi (fun _ : Fin N => periodicHaar ι)) ≤ (periodicGreenExponentialMass (ι := ι) (β/2))^(N-1) := by
  have hγ0 : 0≤β/2 := by positivity
  have hγd : β/2<(Fintype.card ι:ℝ) := by linarith
  have hs := fun i : Fin N => periodicParticleStar_integrable_integral (β/2) hγ0 hγd N i
  let G := fun x : Fin N → PeriodicTorus ι => (N:ℝ)⁻¹*∑ i : Fin N,periodicParticleStar (β/2) N i x
  have hG : Integrable G (Measure.pi (fun _ : Fin N => periodicHaar ι)) :=
    (integrable_finsetSum _ (fun i _ => (hs i).1)).const_mul _
  have hi : Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (periodicParticleExponent β N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) := by
    apply hG.mono' (Real.continuous_exp.measurable.comp (periodicParticleExponent_measurable β N)).aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      simp only [Function.comp_apply,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact periodicParticleExponent_star_jensen β N hN x)
  refine ⟨hi,(integral_mono hi hG (periodicParticleExponent_star_jensen β N hN)).trans_eq ?_⟩
  unfold G
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => (hs i).1)]
  simp_rw [(hs _).2]
  have hn : (N:ℝ)≠0 := by exact_mod_cast (by omega : N≠0)
  simp [hn]

/-- Actual source partition, with a proper real integral representation below
collision. Infinite values are not silently replaced by totalized zero. -/
theorem periodicAttractivePartition_eq_ofReal (β : ℝ) (hβ0 : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    periodicAttractivePartition (ι := ι) β N =
      ENNReal.ofReal (∫ x : Fin N → PeriodicTorus ι,Real.exp (periodicParticleExponent β N x)
        ∂Measure.pi (fun _ : Fin N => periodicHaar ι)) :=
  (ofReal_integral_eq_lintegral_ofReal (periodicParticleDensity_integrable_upper β hβ0 hβd N hN).1
    (Eventually.of_forall (fun x => (Real.exp_pos _).le))).symm

theorem periodicAttractivePartition_finite_upper (β : ℝ) (hβ0 : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    periodicAttractivePartition (ι := ι) β N ≤ ENNReal.ofReal ((periodicGreenExponentialMass (ι := ι) (β/2))^(N-1)) ∧
      periodicAttractivePartition (ι := ι) β N<∞ := by
  rw [periodicAttractivePartition_eq_ofReal β hβ0 hβd N hN]
  exact ⟨ENNReal.ofReal_le_ofReal (periodicParticleDensity_integrable_upper β hβ0 hβd N hN).2,ENNReal.ofReal_lt_top⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicParticleExponent_star_jensen
#print axioms DGRHS.Periodic.periodicParticleDensity_integrable_upper
#print axioms DGRHS.Periodic.periodicAttractivePartition_eq_ofReal
#print axioms DGRHS.Periodic.periodicAttractivePartition_finite_upper
#check @DGRHS.Periodic.periodicAttractivePartition_finite_upper
