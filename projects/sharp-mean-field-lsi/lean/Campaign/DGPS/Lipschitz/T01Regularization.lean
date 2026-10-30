import DGPS.Lipschitz.T01TighteningBridge
import DGPS.Lipschitz.WeakChainRule
import DGPS.FiniteN.Tools.Rothaus
import SharpSymmetricLSI.Paper.Defective13

/-!
# Full canonical-domain closure of a defective particle inequality

The smooth positive regularizations are actual canonical particle Sobolev tests and contract
the unscaled Dirichlet energy. Mass converges by dominated convergence and entropy is lower
semicontinuous. Consequently the positive bounded proof stage suffices for all `ParticleH1`
tests, including zeros and infinite entropy, without an extra admissibility hypothesis.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ} {A : InteractionData d} {N : ℕ+}

/-- The smooth positive truncation has its genuine chain-rule particle derivative. -/
theorem regularizedParticleTest_isWeakGradient (f : ParticleH1 A N) (n : ℕ) :
    IsParticleWeakGradient A N (fun x => SharpLSI.psiReg n (f x))
      (fun x => deriv (SharpLSI.psiReg n) (f x) • particleWeakGradient f x) := by
  apply (isParticleWeakGradient_iff A N _ _).2
  rw [isParticleHaarWeakGradient_iff_weakGradient, particleGradT_smul]
  have hf := (isParticleWeakGradient_iff A N _ _).1
    (isParticleWeakGradient_particleWeakGradient f)
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hf
  exact WeakChainRule.isWeakGradient_comp ((SharpLSI.contDiff_psiReg n).of_le (by simp))
    (SharpLSI.abs_deriv_psiReg_le n) hf

/-- Positive bounded canonical regularization; no new Sobolev domain is introduced. -/
noncomputable def regularizedParticleTest (f : ParticleH1 A N) (n : ℕ) : ParticleH1 A N :=
  ⟨fun x => SharpLSI.psiReg n (f x), _, regularizedParticleTest_isWeakGradient f n⟩

theorem regularizedParticleTest_bounds (f : ParticleH1 A N) (n : ℕ)
    (x : ParticleSpace d N) :
    1 / ((n : ℝ) + 1) ≤ regularizedParticleTest f n x ∧
      regularizedParticleTest f n x ≤ (n : ℝ) + 2 :=
  ⟨SharpLSI.psiReg_ge n (f x), SharpLSI.psiReg_le n (f x)⟩

/-- The energy has the original, unscaled normalization. -/
theorem regularizedParticleTest_energy_le (f : ParticleH1 A N) (n : ℕ) :
    particleEnergy A N (regularizedParticleTest f n) ≤ particleEnergy A N f := by
  apply particleEnergy_le_of_pointwise f (regularizedParticleTest f n)
    (regularizedParticleTest_isWeakGradient f n)
  intro x
  rw [particleTangentNormSq_smul']
  have h : deriv (SharpLSI.psiReg n) (f x) ^ 2 ≤ 1 := by
    have := SharpLSI.abs_deriv_psiReg_le n (f x)
    nlinarith [sq_abs (deriv (SharpLSI.psiReg n) (f x)),
      abs_nonneg (deriv (SharpLSI.psiReg n) (f x))]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h
    (particleTangentNormSq_nonneg' (particleWeakGradient f x))

/-- Square masses converge even for tests with no pointwise measurable representative chosen. -/
theorem regularizedParticleTest_mass_tendsto (f : ParticleH1 A N) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (regularizedParticleTest f n x ^ 2) ∂particleLaw A N)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N)) := by
  have hf2 := (isParticleWeakGradient_particleWeakGradient f).memLp
  have hfm := hf2.aestronglyMeasurable.aemeasurable
  refine tendsto_lintegral_of_dominated_convergence' (bound := fun x => ENNReal.ofReal (f x ^ 2 + 1))
    (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      (((SharpLSI.contDiff_psiReg n).continuous.measurable.comp_aemeasurable hfm).pow_const 2))
    (fun n => Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (SharpLSI.psiReg_sq_le n (f x)))
    ?_ (Eventually.of_forall fun x => (ENNReal.continuous_ofReal.tendsto _).comp
      (SharpLSI.tendsto_psiReg_sq (f x)))
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt
    (hf2.integrable_sq.add (integrable_const 1)).hasFiniteIntegral).ne

/-- Entropy lower semicontinuity for the raw scalar regularization. Keeping this statement
independent of Sobolev proof witnesses avoids expensive definitional reductions. -/
private theorem raw_regularization_entropy_liminf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : Ω → ℝ) (hv : MemLp v 2 P) :
    homogeneousEntropy P (fun x => v x ^ 2) ≤
      liminf (fun n => homogeneousEntropy P (fun x => SharpLSI.psiReg n (v x) ^ 2)) atTop := by
  let F : ℕ → Ω → ℝ := fun n x => SharpLSI.psiReg n (v x) ^ 2
  have hvm := hv.aestronglyMeasurable.aemeasurable
  have hi : ∀ n, Integrable (F n) P := by
    intro n
    refine Integrable.of_bound
      (((SharpLSI.contDiff_psiReg n).continuous.measurable.comp_aemeasurable hvm).pow_const 2
        |>.aestronglyMeasurable) (((n : ℝ) + 2) ^ 2) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (le_trans (by positivity) (SharpLSI.psiReg_ge n (v x)))
      (SharpLSI.psiReg_le n (v x)) 2
  have hlim : ∀ᵐ x ∂P, Tendsto (fun n => F n x) atTop (𝓝 (v x ^ 2)) :=
    Eventually.of_forall fun x => SharpLSI.tendsto_psiReg_sq (v x)
  have hint : Tendsto (fun n => ∫ x, F n x ∂P) atTop (𝓝 (∫ x, v x ^ 2 ∂P)) := by
    exact tendsto_integral_of_dominated_convergence (F := F) (f := fun x => v x ^ 2)
      (fun x => v x ^ 2 + 1) (fun n => (hi n).aestronglyMeasurable)
      (hv.integrable_sq.add (integrable_const 1))
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact SharpLSI.psiReg_sq_le n (v x)) hlim
  have hlegacy := SharpLSI.ent_le_liminf (F := F) (f := fun x => v x ^ 2)
    hi hv.integrable_sq hlim hint
  have he : (fun n => SharpLSI.ent P (F n)) =
      (fun n => homogeneousEntropy P (F n)) := by
    funext n
    exact (FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent (hi n)).symm
  calc
    homogeneousEntropy P (fun x => v x ^ 2) = SharpLSI.ent P (fun x => v x ^ 2) :=
      FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hv.integrable_sq
    _ ≤ liminf (fun n => SharpLSI.ent P (F n)) atTop := hlegacy
    _ = _ := congrArg (fun w : ℕ → ℝ≥0∞ => liminf w atTop) he

/-- Lower semicontinuity of the extended entropy under the positive regularizations. -/
theorem regularizedParticleTest_entropy_liminf (f : ParticleH1 A N) :
    particleEntropy A N f ≤
      liminf (fun n => particleEntropy A N (regularizedParticleTest f n)) atTop := by
  change homogeneousEntropy (particleLaw A N) (fun x => f x ^ 2) ≤
    liminf (fun n => homogeneousEntropy (particleLaw A N)
      (fun x => SharpLSI.psiReg n (f x) ^ 2)) atTop
  exact raw_regularization_entropy_liminf (particleLaw A N) f.1
    (isParticleWeakGradient_particleWeakGradient f).memLp

/-- A defective bound on the positive bounded proof stage gives the same bound for every
canonical Sobolev test. The coefficient multiplies the exact original energy. -/
theorem particle_defective_of_regularized {a B : ℝ} (f : ParticleH1 A N)
    (hreg : ∀ n, particleEntropy A N (regularizedParticleTest f n) ≤
      ENNReal.ofReal (a * particleEnergy A N (regularizedParticleTest f n)) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (regularizedParticleTest f n x ^ 2) ∂particleLaw A N)
    (ha : 0 ≤ a) :
    particleEntropy A N f ≤ ENNReal.ofReal (a * particleEnergy A N f) +
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N := by
  have hb : Tendsto (fun n => ENNReal.ofReal (a * particleEnergy A N f) +
      ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (regularizedParticleTest f n x ^ 2) ∂particleLaw A N)
      atTop (𝓝 (ENNReal.ofReal (a * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂particleLaw A N)) :=
    tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (regularizedParticleTest_mass_tendsto f)
      (Or.inr ENNReal.ofReal_ne_top))
  calc
    particleEntropy A N f ≤ liminf (fun n => particleEntropy A N (regularizedParticleTest f n)) atTop :=
      regularizedParticleTest_entropy_liminf f
    _ ≤ liminf (fun n => ENNReal.ofReal (a * particleEnergy A N f) +
        ENNReal.ofReal B * ∫⁻ x, ENNReal.ofReal (regularizedParticleTest f n x ^ 2) ∂particleLaw A N) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n => (hreg n).trans
        (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (regularizedParticleTest_energy_le f n) ha)) le_rfl))
    _ = _ := hb.liminf_eq

end DGPS.Lipschitz
