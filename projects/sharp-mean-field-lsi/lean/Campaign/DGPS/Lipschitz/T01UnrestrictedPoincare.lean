import DGPS.Particle.Contractions
import DGPS.Particle.Rates
import DGPS.Basic.EntropyUniformIntegrability
import DGPS.FiniteN.Tools.Rothaus
import FullLabeledLSI.Paper.Lem25Trunc

/-!
# Unrestricted Poincare contradiction on the actual particle domain

This is the truncation and bounded-observable argument from the accepted Lipschitz proof,
Section 10.4. Its two analytic inputs remain explicit: bounded comparison for actual Gibbs
tests and uniform square integrability of the normalized violating sequence. No compactness of
unrestricted coefficient arrays or semiconvexity hypothesis is used.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

/-- A normalized mean-zero particle sequence of energy below `b` contradicts bounded
comparison at `b`, provided its squares are uniformly integrable. -/
theorem poincare_sequence_contradiction_of_scalar_stable_class {d : ℕ} (A : InteractionData d)
    (P : ∀ N : ℕ+, ParticleH1 A N → Prop)
    (hscalar : ∀ (N : ℕ+) (f g : ParticleH1 A N) (ψ : ℝ → ℝ),
      Continuous ψ → P N f → g.1 = (fun x => ψ (f x)) → P N g)
    {b κ : ℝ} (hb : 0 < b) (hκ : 0 ≤ κ) (hκb : κ < b)
    (hcomp : ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ g : ParticleH1 A N,
        P N g → (∀ x, |g x| ≤ M) → particleEnergy A N g ≤ E0 →
        ENNReal.ofReal (b / 2) * particleEntropy A N g ≤
          ENNReal.ofReal (particleEnergy A N g + ε))
    (Ns : ℕ → ℕ+) (hNs : Tendsto Ns atTop atTop)
    (f : (k : ℕ) → ParticleH1 A (Ns k))
    (hP : ∀ k, P (Ns k) (f k))
    (hzero : ∀ k, ∫ x, f k x ∂particleLaw A (Ns k) = 0)
    (hone : ∀ k, ∫ x, f k x ^ 2 ∂particleLaw A (Ns k) = 1)
    (hE : ∀ k, particleEnergy A (Ns k) (f k) ≤ κ)
    (hUI : Analysis.UniformSquareIntegrable (fun k => particleLaw A (Ns k))
      (fun k => (f k).1)) : False := by
  let γ : ℝ := b - κ
  have hγ : 0 < γ := sub_pos.mpr hκb
  let ε : ℝ := min 1 ((γ / (6 * b)) ^ 2)
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hsq : Real.sqrt ε ≤ γ / (6 * b) := by
    calc Real.sqrt ε ≤ Real.sqrt ((γ / (6 * b)) ^ 2) :=
          Real.sqrt_le_sqrt (min_le_right _ _)
      _ = γ / (6 * b) := Real.sqrt_sq (by positivity)
  obtain ⟨M, hM⟩ := hUI ε hε
  let T : ℝ := Real.sqrt (max M 1)
  have hmax : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hT : 0 < T := Real.sqrt_pos.mpr hmax
  have hT2 : T ^ 2 = max M 1 := Real.sq_sqrt hmax.le
  have htail : ∀ k, ∫⁻ x in {x | T ^ 2 < f k x ^ 2},
      ENNReal.ofReal (f k x ^ 2) ∂particleLaw A (Ns k) ≤ ENNReal.ofReal ε := by
    intro k
    have hi := (isParticleWeakGradient_particleWeakGradient (f k)).memLp.integrable_sq
    have hm : ∫⁻ x in {x | M < f k x ^ 2},
        ENNReal.ofReal (f k x ^ 2) ∂particleLaw A (Ns k) ≤ ENNReal.ofReal ε := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
        (Eventually.of_forall fun x => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hM k)
    refine (lintegral_mono_set (fun x hx => ?_)).trans hm
    change M < f k x ^ 2
    have hx' : T ^ 2 < f k x ^ 2 := hx
    rw [hT2] at hx'
    exact lt_of_le_of_lt (le_max_left _ _) hx'
  let gmin : (k : ℕ) → ParticleH1 A (Ns k) := fun k =>
    ⟨fun x => min (f k x) T, (f k).2.min_const T⟩
  let g : (k : ℕ) → ParticleH1 A (Ns k) := fun k =>
    ⟨fun x => max (gmin k x) (-T), (gmin k).2.max_const (-T)⟩
  have hg : ∀ k x, g k x = SharpLSI.FL.truncR T (f k x) := by
    intro k x
    exact max_comm _ _
  have hgP : ∀ k, P (Ns k) (g k) := by
    intro k
    have hmP : P (Ns k) (gmin k) :=
      hscalar (Ns k) (f k) (gmin k) (fun z => min z T) (by fun_prop) (hP k) rfl
    exact hscalar (Ns k) (gmin k) (g k) (fun z => max z (-T)) (by fun_prop) hmP rfl
  have hgE : ∀ k, particleEnergy A (Ns k) (g k) ≤ κ := fun k =>
    (particleEnergy_max_const_le (gmin k) (g k) (-T) rfl).trans
      ((particleEnergy_min_const_le (f k) (gmin k) T rfl).trans (hE k))
  have hgb : ∀ k x, |g k x| ≤ T := by
    intro k x
    rw [hg]
    exact SharpLSI.FL.abs_truncR_le hT.le _
  have hgvar : ∀ k, 1 - 2 * Real.sqrt ε ≤
      (∫ x, g k x ^ 2 ∂particleLaw A (Ns k)) -
        (∫ x, g k x ∂particleLaw A (Ns k)) ^ 2 := by
    intro k
    simpa only [hg] using SharpLSI.FL.trunc_var_lower (particleLaw A (Ns k))
      (isParticleWeakGradient_particleWeakGradient (f k)).memLp
      (hzero k) (hone k) hT hε hε1 (htail k)
  let K : ℝ := 1 + 25 * b * T ^ 3 / 2
  have hK : 0 < K := by positivity
  let t : ℝ := min (min 1 (1 / (16 * T))) (γ / (3 * K))
  have ht : 0 < t := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have htT : t * T ≤ 1 / 16 := by
    have hh : t ≤ 1 / (16 * T) := (min_le_left _ _).trans (min_le_right _ _)
    calc t * T ≤ 1 / (16 * T) * T := mul_le_mul_of_nonneg_right hh hT.le
      _ = 1 / 16 := by field_simp
  have htK : t * K ≤ γ / 3 := by
    have hh : t ≤ γ / (3 * K) := min_le_right _ _
    calc t * K ≤ γ / (3 * K) * K := mul_le_mul_of_nonneg_right hh hK.le
      _ = γ / 3 := by field_simp
  let u : (k : ℕ) → ParticleH1 A (Ns k) := fun k =>
    ⟨fun x => t * g k x + 1, (g k).2.affine t 1⟩
  have hu : ∀ k x, u k x = 1 + t * g k x := fun _ _ => add_comm _ _
  have huP : ∀ k, P (Ns k) (u k) := fun k =>
    hscalar (Ns k) (g k) (u k) (fun z => t * z + 1) (by fun_prop) (hgP k) rfl
  have huE : ∀ k, particleEnergy A (Ns k) (u k) ≤ t ^ 2 * κ := by
    intro k
    rw [particleEnergy_affine (g k) (u k) t 1 rfl]
    exact mul_le_mul_of_nonneg_left (hgE k) (sq_nonneg _)
  have hub : ∀ k x, |u k x| ≤ 2 := by
    intro k x
    have htg : |t * g k x| ≤ 1 / 16 := by
      rw [abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left (hgb k x) ht.le).trans htT
    rw [hu]
    exact (abs_add_le _ _).trans (by rw [abs_one]; linarith)
  have huE' : ∀ k, particleEnergy A (Ns k) (u k) ≤ κ + 1 := by
    intro k
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right ht2 hκ
    linarith [huE k]
  have hcomp' := hNs.eventually (hcomp 2 (κ + 1) (t ^ 3)
    (by norm_num) (by linarith) (by positivity))
  obtain ⟨k, hk⟩ := hcomp'.exists
  have hc := hk (u k) (huP k) (hub k) (huE' k)
  have hintu := (isParticleWeakGradient_particleWeakGradient (u k)).memLp.integrable_sq
  have hent : ENNReal.ofReal
      (2 * t ^ 2 * ((∫ x, g k x ^ 2 ∂particleLaw A (Ns k)) -
        (∫ x, g k x ∂particleLaw A (Ns k)) ^ 2) - 25 * t ^ 3 * T ^ 3) ≤
      particleEntropy A (Ns k) (u k) := by
    unfold particleEntropy
    rw [FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hintu]
    simpa only [hu] using SharpLSI.FL.ent_one_add_ge (particleLaw A (Ns k)) (g k).1
      (isParticleWeakGradient_particleWeakGradient (g k)).memLp.aestronglyMeasurable
      hT ht htT (hgb k)
  let V : ℝ := (∫ x, g k x ^ 2 ∂particleLaw A (Ns k)) -
    (∫ x, g k x ∂particleLaw A (Ns k)) ^ 2
  have hchain : ENNReal.ofReal (b / 2 * (2 * t ^ 2 * V - 25 * t ^ 3 * T ^ 3)) ≤
      ENNReal.ofReal (t ^ 2 * κ + t ^ 3) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    exact (mul_le_mul' le_rfl hent).trans (hc.trans
      (ENNReal.ofReal_le_ofReal (by linarith [huE k])))
  have hreal : b / 2 * (2 * t ^ 2 * V - 25 * t ^ 3 * T ^ 3) ≤ t ^ 2 * κ + t ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hchain
  have h2 : t ^ 2 * (b * V - 25 / 2 * b * t * T ^ 3 - κ - t) ≤ 0 := by
    nlinarith [hreal]
  have h3 : b * V - 25 / 2 * b * t * T ^ 3 - κ - t ≤ 0 := by
    by_contra hh
    have hh' : 0 < b * V - 25 / 2 * b * t * T ^ 3 - κ - t := lt_of_not_ge hh
    have hh'' := mul_pos (sq_pos_of_pos ht) hh'
    linarith
  have h4 : b * (1 - 2 * Real.sqrt ε) ≤ b * V :=
    mul_le_mul_of_nonneg_left (hgvar k) hb.le
  have h5 : 2 * b * Real.sqrt ε ≤ γ / 3 := by
    calc 2 * b * Real.sqrt ε ≤ 2 * b * (γ / (6 * b)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = γ / 3 := by field_simp; ring
  have h6 : t * K = t + 25 / 2 * b * t * T ^ 3 := by dsimp [K]; ring
  dsimp [γ] at *
  nlinarith

/-- The unrestricted sequence contradiction is the scalar-stable-class theorem for the
full particle domain. Its public statement is unchanged. -/
theorem unrestricted_poincare_sequence_contradiction {d : ℕ} (A : InteractionData d)
    {b κ : ℝ} (hb : 0 < b) (hκ : 0 ≤ κ) (hκb : κ < b)
    (hcomp : ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ g : ParticleH1 A N,
        (∀ x, |g x| ≤ M) → particleEnergy A N g ≤ E0 →
        ENNReal.ofReal (b / 2) * particleEntropy A N g ≤
          ENNReal.ofReal (particleEnergy A N g + ε))
    (Ns : ℕ → ℕ+) (hNs : Tendsto Ns atTop atTop)
    (f : (k : ℕ) → ParticleH1 A (Ns k))
    (hzero : ∀ k, ∫ x, f k x ∂particleLaw A (Ns k) = 0)
    (hone : ∀ k, ∫ x, f k x ^ 2 ∂particleLaw A (Ns k) = 1)
    (hE : ∀ k, particleEnergy A (Ns k) (f k) ≤ κ)
    (hUI : Analysis.UniformSquareIntegrable (fun k => particleLaw A (Ns k))
      (fun k => (f k).1)) : False := by
  apply poincare_sequence_contradiction_of_scalar_stable_class A
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => True.intro) hb hκ hκb
    (fun M E0 ε hM hE0 hε => (hcomp M E0 ε hM hE0 hε).mono fun N hN g _ => hN g)
    Ns hNs f (fun _ => True.intro) hzero hone hE hUI

end DGPS.Lipschitz
