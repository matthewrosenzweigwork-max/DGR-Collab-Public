import DGPS.FiniteN.SecondHarmonicPerturbation
import DGPS.FiniteN.Tools.Linearization
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Foundations.NormalizationChecks

/-!
# Strict particle LSI and the `N = 1` equality (FIN094)

For every `κ > 0` (second-harmonic model `V = 0`, `W = κ[cos 4π(x−y) − 1]`) and
`a₀ = 4π²`:

* `r_1^all = r_1^sym = a₀`: at `N = 1` the Hamiltonian vanishes identically, so the Gibbs law is
  Haar measure, the rates depend on the interaction only through the Gibbs law, and the free
  circle rates are `a₀` (DEF024/DEF032);
* for every `N ≥ 2`: `r_N^all ≤ r_N^sym < a₀`.  The strict Poincare quotient `< a₀` of the smooth
  symmetric centered test `g = F_N − η R_N` (FIN093), together with the bounded-test
  linearization `r_N^sym ≤ E(g)/Var(g)` (FIN003, i.e. the test `1 + δ g` for small `δ`), gives the
  strict upper bound; `r_N^all ≤ r_N^sym` is competitor-set inclusion (DEF019).
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.FiniteN

/-- Particle rates depend on the interaction only through the Gibbs law. -/
theorem particleRates_congr_of_law_eq {d : ℕ} {A B : DGPS.InteractionData d} {N : ℕ+}
    (h : DGPS.particleLaw A N = DGPS.particleLaw B N) :
    DGPS.particleRateAll A N = DGPS.particleRateAll B N ∧
      DGPS.particleRateSym A N = DGPS.particleRateSym B N := by
  have hmem : ∀ f, DGPS.MemParticleH1 A N f ↔ DGPS.MemParticleH1 B N f := fun f => by
    rw [DGPS.memParticleH1_iff, DGPS.memParticleH1_iff]
  let e : DGPS.ParticleH1 A N ≃ DGPS.ParticleH1 B N :=
    { toFun := fun f => ⟨f.1, (hmem _).1 f.2⟩
      invFun := fun f => ⟨f.1, (hmem _).2 f.2⟩
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  have hent : ∀ f : DGPS.ParticleH1 A N,
      DGPS.particleEntropy A N f = DGPS.particleEntropy B N (e f) := fun f => by
    unfold DGPS.particleEntropy
    rw [h]
    rfl
  have hen : ∀ f : DGPS.ParticleH1 A N,
      DGPS.particleEnergy A N f = DGPS.particleEnergy B N (e f) := fun f => by
    have hgA := DGPS.isParticleWeakGradient_particleWeakGradient f
    have hgB : DGPS.IsParticleWeakGradient B N (e f).1 (DGPS.particleWeakGradient f) :=
      (DGPS.isParticleWeakGradient_iff B N _ _).2 ((DGPS.isParticleWeakGradient_iff A N _ _).1 hgA)
    rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient f hgA,
      DGPS.particleEnergy_eq_of_isParticleWeakGradient (e f) hgB, h]
  have hq : ∀ f : DGPS.ParticleH1 A N,
      DGPS.particleQuotient A N f = DGPS.particleQuotient B N (e f) := fun f => by
    unfold DGPS.particleQuotient
    rw [← hent f, ← hen f]
  have hs : ∀ f : DGPS.ParticleH1 A N,
      DGPS.IsSymmetricParticleTest f ↔ DGPS.IsSymmetricParticleTest (e f) := fun f => by
    unfold DGPS.IsSymmetricParticleTest DGPS.IsSymmetricParticleFun
    rw [h]
    rfl
  refine ⟨?_, ?_⟩
  · unfold DGPS.particleRateAll
    exact Equiv.iInf_congr (e.subtypeEquiv fun f => by rw [hent f]) (fun f => (hq f.1).symm)
  · unfold DGPS.particleRateSym
    let eS : DGPS.SymmetricParticleH1 A N ≃ DGPS.SymmetricParticleH1 B N := e.subtypeEquiv hs
    exact Equiv.iInf_congr (eS.subtypeEquiv fun f => by
      show 0 < DGPS.particleEntropy A N f.1 ↔ 0 < DGPS.particleEntropy B N (e f.1)
      rw [hent f.1]) (fun f => (hq f.1.1).symm)

/-- At `N = 1` the second-harmonic Gibbs law is Haar measure. -/
theorem secondHarmonic_particleLaw_one (κ : ℝ) :
    DGPS.particleLaw (secondHarmonicData κ) 1 = DGPS.particleLaw (DGPS.InteractionData.zero 1) 1 := by
  have hH : DGPS.particleHamiltonian (secondHarmonicData κ) 1 =
      DGPS.particleHamiltonian (DGPS.InteractionData.zero 1) 1 := by
    funext x
    have h1 : ∑ i : Fin ((1 : ℕ+) : ℕ), ∑ j : Fin ((1 : ℕ+) : ℕ),
        secondHarmonicW κ (x i) (x j) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      have hij : i = j := Fin.ext (by have := i.2; have := j.2; simp at *; omega)
      rw [hij]
      exact (secondHarmonicData κ).W_diag _
    simp [DGPS.particleHamiltonian, secondHarmonicData, DGPS.InteractionData.zero]
    exact h1
  unfold DGPS.particleLaw DGPS.particleDensity DGPS.particlePartition
  rw [hH]

/-- **FIN094.** For every `κ > 0`: `r_1^all = r_1^sym = a₀`, and for every `N ≥ 2`,
`r_N^all ≤ r_N^sym < a₀`. -/
theorem strict_particle_lsi_and_n_one_equality (κ : ℝ) (hκ : 0 < κ) :
    (DGPS.particleRateAll (secondHarmonicData κ) 1 =
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 ∧
      DGPS.particleRateSym (secondHarmonicData κ) 1 =
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0) ∧
    ∀ N : ℕ+, 2 ≤ N →
      DGPS.particleRateAll (secondHarmonicData κ) N ≤ DGPS.particleRateSym (secondHarmonicData κ) N ∧
      DGPS.particleRateSym (secondHarmonicData κ) N <
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 := by
  refine ⟨?_, fun N hN => ⟨DGPS.particleRateAll_le_sym _ N, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := particleRates_congr_of_law_eq (secondHarmonic_particleLaw_one κ)
    obtain ⟨-, h3, h4⟩ := DGPS.circle_free_rates (DGPS.AbsoluteDrift.zero 1)
    exact ⟨h1.trans h3, h2.trans h4⟩
  · obtain ⟨η, -, g, hg1, -, -, hsym, hmean, hvar, -, -, hquot⟩ :=
      strict_symmetric_perturbation_quotient κ hκ N hN
    have hgc : Continuous g.1 := by
      rw [hg1]
      exact (continuous_harmonicTrial N).sub (continuous_const.mul
        (continuous_secondHarmonicResidual κ N))
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hgc.continuousOn
    obtain ⟨-, -, -, hsymle⟩ := bounded_test_lsi_linearization (secondHarmonicData κ) N g M
      (fun x => hM x (Set.mem_univ x)) hmean hvar
    refine lt_of_le_of_lt (hsymle hsym) ?_
    refine lt_of_le_of_lt (le_of_eq ?_) hquot
    unfold DGPS.particlePoincareQuotient
    rw [ENNReal.ofReal_div_of_pos hvar]

end DGPS.FiniteN
