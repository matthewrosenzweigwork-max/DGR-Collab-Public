import DGPS.Lipschitz.T01FixedParticleDefective
import DGPS.Lipschitz.T01ParticleDefective

/-!
# Uniform defective constants including the finite particle prefix

The genuine fixed-particle inequality has the same prescribed energy coefficient as the
uniform tail. All fixed-particle constants are chosen before the particle number and test;
a finite nonnegative sum bounds the prefix. The scalar endpoint retains a.e. symmetry.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Lipschitz

/-- A uniform tail and the proved fixed-particle estimate give one mass constant for all
particle numbers, for any subclass of the canonical tests. -/
theorem particle_defective_uniform_of_eventual {d : ℕ} (A : InteractionData d)
    {η : ℝ} (hη : 0 < η) (P : ∀ N : ℕ+, ParticleH1 A N → Prop)
    (htail : ∃ N₀ : ℕ, ∃ B : ℝ, ∀ N : ℕ+, N₀ ≤ N → ∀ f : ParticleH1 A N,
      P N f → particleEntropy A N f ≤ ENNReal.ofReal (η * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ+, ∀ f : ParticleH1 A N, P N f →
      particleEntropy A N f ≤ ENNReal.ofReal (η * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  classical
  obtain ⟨N₀, Btail, htail⟩ := htail
  choose B hB using fun N : ℕ+ => fixed_particle_defective A N hη
  let C : ℕ → ℝ := fun n => max 0 (B ⟨n + 1, Nat.succ_pos n⟩)
  have hC (n : ℕ) : 0 ≤ C n := le_max_left _ _
  let Btotal := max 0 Btail + ∑ n ∈ Finset.range N₀, C n
  have hsum : 0 ≤ ∑ n ∈ Finset.range N₀, C n := Finset.sum_nonneg fun n _ => hC n
  refine ⟨Btotal, add_nonneg (le_max_left _ _) hsum, fun N f hf => ?_⟩
  have hmono (B₁ : ℝ) (h₁ : B₁ ≤ Btotal)
      (hb : particleEntropy A N f ≤ ENNReal.ofReal (η * particleEnergy A N f) +
        ENNReal.ofReal B₁ * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N) :
      particleEntropy A N f ≤ ENNReal.ofReal (η * particleEnergy A N f) +
        ENNReal.ofReal Btotal * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N :=
    hb.trans (add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal h₁) le_rfl))
  by_cases hN : N₀ ≤ (N : ℕ)
  · apply hmono Btail ((le_max_right 0 Btail).trans (le_add_of_nonneg_right hsum))
    exact htail N hN f hf
  · have hi : (N : ℕ) - 1 ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have he : (⟨(N : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = N := by
      apply Subtype.ext
      change (N : ℕ) - 1 + 1 = (N : ℕ)
      have hpos : (1 : ℕ) ≤ (N : ℕ) := Nat.succ_le_of_lt N.pos
      exact Nat.sub_add_cancel hpos
    have hterm : B N ≤ C ((N : ℕ) - 1) := by
      dsimp [C]
      rw [he]
      exact le_max_right _ _
    have hprefix : C ((N : ℕ) - 1) ≤ ∑ n ∈ Finset.range N₀, C n :=
      Finset.single_le_sum (fun n _ => hC n) hi
    apply hmono (B N) (hterm.trans (hprefix.trans (le_add_of_nonneg_left (le_max_left _ _))))
    exact hB N f

/-- The species subrate gives an actual all-particle uniform defective inequality. -/
theorem t01_uniform_particle_defective {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) {r : ℝ} (hr : 0 < r)
    (hrr : ENNReal.ofReal r < speciesRate A b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ+, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  obtain ⟨N₀, B, _, htail⟩ := t01_eventual_particle_defective A hA hd b hrate hr hrr
  obtain ⟨C, hC, hbound⟩ := particle_defective_uniform_of_eventual A
    (by positivity : 0 < 2 / r) (fun _ _ => True) ⟨N₀, B, fun N hN f _ => htail N hN f⟩
  exact ⟨C, hC, fun N f => hbound N f trivial⟩

/-- The scalar subrate gives the all-particle uniform defect on the full a.e. symmetric class. -/
theorem t01_uniform_symmetric_particle_defective {d : ℕ} (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (b : AbsoluteDrift A)
    (hrate : 0 < scalarRate A b) {r : ℝ} (hr : 0 < r)
    (hrr : ENNReal.ofReal r < scalarRate A b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ+, ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂particleLaw A N := by
  obtain ⟨N₀, B, _, htail⟩ := t01_eventual_symmetric_particle_defective A hA hd b hrate hr hrr
  exact particle_defective_uniform_of_eventual A (by positivity : 0 < 2 / r)
    (fun _ f => IsSymmetricParticleTest f) ⟨N₀, B, htail⟩

end DGPS.Lipschitz
