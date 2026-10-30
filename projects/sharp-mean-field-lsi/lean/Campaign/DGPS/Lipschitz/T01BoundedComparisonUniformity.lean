import DGPS.Lipschitz.T01BoundedObservableComparison
import DGPS.Foundations.WeakContractions

/-! Uniformity in the bounded observable and the exact finite-entropy conversion. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

private theorem exists_zero_particle_test {d : ℕ} (J : InteractionData d) (N : ℕ+) :
    ∃ z : ParticleH1 J N, (∀ X, z X = 0) ∧ particleEnergy J N z = 0 := by
  have hzero : IsParticleHaarWeakGradient (d := d) N
      (fun _ : ParticleSpace d N => (0 : ℝ)) (fun _ : ParticleSpace d N => 0) := by
    apply isParticleHaarWeakGradient_iff_weakGradient.2
    simpa only [Function.comp_def, particleGradT_zero] using
      (isWeakGradient_const (d := (N : ℕ) * d) 0)
  have hz := (isParticleWeakGradient_iff J N _ _).2 hzero
  let z : ParticleH1 J N := ⟨fun _ => 0, ⟨_, hz⟩⟩
  refine ⟨z, fun _ => rfl, ?_⟩
  rw [particleEnergy_eq_of_isParticleWeakGradient z hz]
  simp [particleTangentNormSq]

/-- Bounded canonical tests have finite entropy; full H1 representatives are retained. -/
theorem particleEntropy_ne_top_of_bound {d : ℕ} {J : InteractionData d} {N : ℕ+}
    (f : ParticleH1 J N) {B : ℝ} (hB : ∀ X, |f X| ≤ B) :
    particleEntropy J N f ≠ ⊤ := by
  have hf := (isParticleWeakGradient_particleWeakGradient f).memLp
  have hm := hf.aestronglyMeasurable
  have hsq : ∀ X, f X ^ 2 ≤ B ^ 2 := fun X => by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (f X)) (hB X) 2
  have hlogm : AEStronglyMeasurable (fun X => f X ^ 2 * Real.log (f X ^ 2)) (particleLaw J N) :=
    ((hm.pow 2).aemeasurable.mul
      (Real.measurable_log.comp_aemeasurable (hm.pow 2).aemeasurable)).aestronglyMeasurable
  have hi : Integrable (fun X => f X ^ 2 * Real.log (f X ^ 2)) (particleLaw J N) := by
    refine Integrable.of_bound hlogm (B ^ 2 * |Real.log (B ^ 2)| + 1) ?_
    exact Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs, abs_le]
      obtain ⟨hlo, hhi⟩ := SharpLSI.FL.fa_mul_log_bounds (sq_nonneg (f X)) (hsq X)
      have hnn := mul_nonneg (sq_nonneg B) (abs_nonneg (Real.log (B ^ 2)))
      constructor <;> linarith
  rw [particleEntropy, FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hf.integrable_sq,
    SharpLSI.ent_eq_formula (particleLaw J N) _ (fun X => sq_nonneg _) hf.integrable_sq hi]
  exact ENNReal.ofReal_ne_top

/-- Estimates for every bounded full-domain family imply an estimate uniform over its tests.
The measurable representative is not restricted: selection takes place in the actual H1 subtype. -/
theorem uniform_bounded_comparison_of_family {d : ℕ} (J : InteractionData d) {b : ℝ}
    (hb : 0 ≤ b)
    (hfamily : ∀ (B E0 : ℝ), 0 < B → 0 < E0 →
      ∀ f : (N : ℕ+) → ParticleH1 J N, (∀ N X, |f N X| ≤ B) →
        (∀ N, particleEnergy J N (f N) ≤ E0) → ∀ ε : ℝ, 0 < ε →
          ∀ᶠ N : ℕ+ in atTop,
            -ε ≤ particleEnergy J N (f N) - b / 2 * (particleEntropy J N (f N)).toReal) :
    ∀ B E0 ε : ℝ, 0 < B → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N,
        (∀ X, |f X| ≤ B) → particleEnergy J N f ≤ E0 →
        ENNReal.ofReal (b / 2) * particleEntropy J N f ≤
          ENNReal.ofReal (particleEnergy J N f + ε) := by
  classical
  intro B E0 ε hB0 hE0 hε
  let Bad (N : ℕ+) (f : ParticleH1 J N) : Prop :=
    (∀ X, |f X| ≤ B) ∧ particleEnergy J N f ≤ E0 ∧
      ¬(-ε ≤ particleEnergy J N f - b / 2 * (particleEntropy J N f).toReal)
  have hex (N : ℕ+) : ∃ f : ParticleH1 J N, (∀ X, |f X| ≤ B) ∧
      particleEnergy J N f ≤ E0 ∧ ((∃ g, Bad N g) →
        ¬(-ε ≤ particleEnergy J N f - b / 2 * (particleEntropy J N f).toReal)) := by
    by_cases h : ∃ g, Bad N g
    · obtain ⟨g, hg⟩ := h
      exact ⟨g, hg.1, hg.2.1, fun _ => hg.2.2⟩
    · obtain ⟨z, hz, hEz⟩ := exists_zero_particle_test J N
      exact ⟨z, fun X => by rw [hz X, abs_zero]; exact hB0.le,
        by rw [hEz]; exact hE0.le, fun he => False.elim (h he)⟩
  choose f hfB hfE hbad using hex
  filter_upwards [hfamily B E0 hB0 hE0 f hfB hfE ε hε] with N hN g hgB hgE
  have hreal : -ε ≤ particleEnergy J N g - b / 2 * (particleEntropy J N g).toReal := by
    by_contra hfail
    exact hbad N ⟨g, hgB, hgE, hfail⟩ hN
  rw [← ENNReal.ofReal_toReal (particleEntropy_ne_top_of_bound g hgB),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ b / 2)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end DGPS.Lipschitz
