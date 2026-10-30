import DGPS.FiniteN.AnisotropicQuarticHubbard
import DGPS.FiniteN.ScalarFoldFIN064

/-! Actual smooth symmetric quartic rare-region tests on the original particle law.
The retained native H1 constructor supplies the exact physical energy identity. -/

open MeasureTheory
open DGPS.Models DGPS.FiniteN.Tools.GaussianCoupling
open DGPS.FiniteN.ScalarFoldFIN064
open scoped ContDiff

namespace DGPS.FiniteN

noncomputable def quarticEmpiricalCos (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  1 + quarticKappa * (∑ i, scalarCos (x i)) / (N : ℝ)

noncomputable def quarticEmpiricalSin (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  (quarticKappa * quarticEta) * (∑ i, scalarSin (x i)) / (N : ℝ)

theorem quartic_empirical_coordinates (N : ℕ+) (x : ParticleSpace 1 N) :
    posteriorCenter quarticHubbardD quarticHubbardField quarticHubbardFeature N x =
      ![quarticEmpiricalCos N x, quarticEmpiricalSin N x] :=
  quartic_hubbard_posterior_center N x

theorem quartic_empirical_cos_smooth (N : ℕ+) : IsSmoothPeriodicParticle (quarticEmpiricalCos N) := by
  change ContDiff ℝ ∞ (fun a : Fin N → Fin 1 → ℝ =>
    1 + quarticKappa * (∑ i, scalarCos (torusLift (a i))) / (N : ℝ))
  simp_rw [scalarCos_lift]
  fun_prop

theorem quartic_empirical_sin_smooth (N : ℕ+) : IsSmoothPeriodicParticle (quarticEmpiricalSin N) := by
  change ContDiff ℝ ∞ (fun a : Fin N → Fin 1 → ℝ =>
    (quarticKappa * quarticEta) * (∑ i, scalarSin (torusLift (a i))) / (N : ℝ))
  simp_rw [scalarSin_lift]
  fun_prop

noncomputable def quarticRareTest (δ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : ℝ :=
  chiFIN064 ((2 / δ) * (quarticEmpiricalCos N x + 4)) *
    chiFIN064 ((N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x)

theorem quarticRareTest_smooth (δ : ℝ) (N : ℕ+) : IsSmoothPeriodicParticle (quarticRareTest δ N) := by
  have hx : IsSmoothPeriodicParticle (fun x => (2 / δ) * (quarticEmpiricalCos N x + 4)) :=
    contDiff_const.mul ((quartic_empirical_cos_smooth N).add contDiff_const)
  have hy : IsSmoothPeriodicParticle (fun x => (N : ℝ) ^ (1 / 4 : ℝ) * quarticEmpiricalSin N x) :=
    contDiff_const.mul (quartic_empirical_sin_smooth N)
  exact (isSmooth_comp_FIN064 hx chi_contDiff_FIN064).mul
    (isSmooth_comp_FIN064 hy chi_contDiff_FIN064)

theorem quarticRareTest_bounds (δ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) :
    0 ≤ quarticRareTest δ N x ∧ quarticRareTest δ N x ≤ 1 := by
  constructor
  · exact mul_nonneg (chi_nonneg_FIN064 _) (chi_nonneg_FIN064 _)
  · exact mul_le_one₀ (chi_le_one_FIN064 _) (chi_nonneg_FIN064 _) (chi_le_one_FIN064 _)

theorem quarticRareTest_permute (δ : ℝ) (N : ℕ+) (σ : Equiv.Perm (Fin N))
    (x : ParticleSpace 1 N) : quarticRareTest δ N (permuteParticles σ x) = quarticRareTest δ N x := by
  have hc : (∑ i, scalarCos (permuteParticles σ x i)) = ∑ i, scalarCos (x i) :=
    Equiv.sum_comp σ (fun i => scalarCos (x i))
  have hs : (∑ i, scalarSin (permuteParticles σ x i)) = ∑ i, scalarSin (x i) :=
    Equiv.sum_comp σ (fun i => scalarSin (x i))
  simp only [quarticRareTest, quarticEmpiricalCos, quarticEmpiricalSin, hc, hs]

/-- The original full native particle H1 carrier, exact physical energy, and actual
permutation symmetry are constructed for the concrete tests, rather than assumed. -/
theorem quartic_rare_test_family (δ : ℝ) :
    ∃ f : (N : ℕ+) → ParticleH1 anisotropicQuarticSaddle N,
      (∀ N x, f N x = quarticRareTest δ N x) ∧
      (∀ N, IsSymmetricParticleTest (f N)) ∧
      ∀ N, particleEnergy anisotropicQuarticSaddle N (f N) =
        ∫ x, ∑ i, particlePartial i 0 (quarticRareTest δ N) x ^ 2
          ∂particleLaw anisotropicQuarticSaddle N := by
  have h : ∀ N : ℕ+, ∃ f : ParticleH1 anisotropicQuarticSaddle N,
      f.1 = quarticRareTest δ N ∧ particleEnergy anisotropicQuarticSaddle N f =
        ∫ x, ∑ i, particlePartial i 0 (quarticRareTest δ N) x ^ 2
          ∂particleLaw anisotropicQuarticSaddle N := fun N =>
    smooth_h1_FIN064 anisotropicQuarticSaddle N (quarticRareTest_smooth δ N)
  choose f hf hE using h
  refine ⟨f, fun N x => congrFun (hf N) x, fun N => ?_, hE⟩
  rw [isSymmetricParticleTest_iff]
  intro σ
  refine Filter.Eventually.of_forall fun x => ?_
  change (f N).1 (permuteParticles σ x) = (f N).1 x
  rw [hf]
  exact quarticRareTest_permute δ N σ x

end DGPS.FiniteN
