import DGPS.Lipschitz.T01MobilityWeightedError
import DGPS.Lipschitz.T01FluctuationFourthMoment
import SharpSymmetricLSI.Paper.TestEnergy9
import SharpSymmetricLSI.Paper.FormLiminfS14a

/-!
# Native cylinder-test energies under the actual particle law

The actual weak cylinder gradient gives the exact empirical-mobility formula. The actual
mobility error then vanishes, and the bounded continuous diagonal term is tested against
the genuine joint law. The stored Sobolev witness is arbitrary and proof-irrelevant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction RealInnerProductSpace

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

/-- Exact actual particle energy of a finite cylinder, using a genuine weak gradient. -/
theorem t01_particle_cylinder_energy_eq {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (e : ℕ → Torus d → ℝ) (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT)) (c : Cyl)
    (hmem : MemParticleH1 A N
      (fun X => c.φ (dualZ N (fun i : Fin c.J => e (i.val + 1)) X))) :
    particleEnergy A N ⟨_, hmem⟩ =
      ∫ X, ∑ i : Fin c.J, ∑ j : Fin c.J,
        cylD c i (zC e N c.J X) * cylD c j (zC e N c.J X) * mobA e N X i j
        ∂particleLaw A N := by
  have hv : ∀ i : Fin c.J, ParabolicChainRule.IsC1Periodic (e (i.val + 1)) := fun i => hφ _
  have hg := (isParticleWeakGradient_iff A N _ _).mpr
    (dg_cyl (N := N) hv (c.smooth.of_le (by simp)))
  rw [particleEnergy_eq_of_isParticleWeakGradient ⟨_, hmem⟩ hg]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro X
  have hZ : dualZ N (fun i : Fin c.J => e (i.val + 1)) X = zC e N c.J X := by
    funext i
    exact t01_dualZ_eq_fluct e N i X
  have hscale : (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]
  simp only [particleTangentNormSq_eq, PiLp.toLp_apply, hZ]
  have hsum : ∀ l : Fin N, ∀ k : Fin d,
      (Real.sqrt (N : ℝ))⁻¹ * ∑ i : Fin c.J,
        fderiv ℝ c.φ (zC e N c.J X) (Pi.single i 1) * coordPartial k (e (i.val + 1)) (X l) =
      ∑ i : Fin c.J, cylD c i (zC e N c.J X) *
        ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (e (i.val + 1)) (X l) k) := by
    intro l k
    rw [hscale, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change _ = fderiv ℝ c.φ (zC e N c.J X) (Pi.single i 1) *
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * coordPartial k (e (i.val + 1)) (X l))
    ring
  simp_rw [hsum]
  rw [sum_sq_regroup (fun (i : Fin c.J) (l : Fin N) (k : Fin d) =>
    cylD c i (zC e N c.J X) *
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * cgrad (e (i.val + 1)) (X l) k))]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  unfold mobA
  rw [← rpow_neg_half_sq (N : ℕ), Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Actual native cylinder energy converges to the Gaussian cylinder form. The inputs are
actual reference/density data and the genuine bounded joint law; energy convergence is proved. -/
theorem t01_particle_cylinder_energy_tendsto {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hfix : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (hac : (μ : Measure (Torus d)) ≪ haar d)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    {p Bp : ℝ} (hp : 1 < p) (hBp : 0 ≤ Bp)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A μ N X ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ Bp)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    {C : ℕ → ℕ → ℝ} {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
    (f : (k : ℕ) → ParticleSpace d (Ns k) → ℝ) (F : (ℕ → ℝ) → ℝ)
    (hlaw : ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f k X, fun i => fluct e (Ns k) i X)
        ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, g (F z, fun i => z i) ∂γ)))
    (c : Cyl) (hmem : ∀ k, MemParticleH1 A (Ns k)
      (fun X => c.φ (dualZ (Ns k) (fun i : Fin c.J => e (i.val + 1)) X))) :
    Tendsto (fun k => particleEnergy A (Ns k) ⟨_, hmem k⟩) atTop
      (𝓝 (c.form (lamShift lam) γ).toReal) := by
  haveI := hγ.1
  let z := fun k (X : ParticleSpace d (Ns k)) => zC e (Ns k) c.J X
  let a := fun k (i : Fin c.J) (X : ParticleSpace d (Ns k)) => cylD c i (z k X)
  let Y := fun k (i j : Fin c.J) (X : ParticleSpace d (Ns k)) =>
    mobA e (Ns k) X i j - if i.val = j.val then lam (i.val + 1) else 0
  obtain ⟨Ka, hKa0, hKa⟩ := exists_bound_fderiv_cyl c
  have bam : ∀ k (i : Fin c.J), BddMeas (a k i) := fun k i =>
    bddMeas_comp_zC hφ (Ns k) (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  have bab : ∀ k (i : Fin c.J) X, |a k i X| ≤ Ka := fun k i X => hKa (z k X) i
  have baL : ∀ k (i : Fin c.J) (q : ℝ≥0∞), MemLp (a k i) q (particleLaw A (Ns k)) :=
    fun k i q => MemLp.of_bound (bam k i).1.aestronglyMeasurable Ka
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact bab k i X)
  have ha2 : ∀ k (i : Fin c.J), MemLp (a k i) 2 (particleLaw A (Ns k)) ∧
      ∫ X, a k i X ^ 2 ∂particleLaw A (Ns k) ≤ Ka ^ 2 := by
    intro k i
    refine ⟨baL k i 2, ?_⟩
    calc
      (∫ X, a k i X ^ 2 ∂particleLaw A (Ns k)) ≤ ∫ _, Ka ^ 2 ∂particleLaw A (Ns k) := by
        apply integral_mono (baL k i 2).integrable_sq (integrable_const _)
        intro X
        change a k i X ^ 2 ≤ Ka ^ 2
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (bab k i X) 2
      _ = _ := by simp
  have ha4 : ∀ k (i : Fin c.J), MemLp (a k i) 4 (particleLaw A (Ns k)) ∧
      ∫ X, a k i X ^ 4 ∂particleLaw A (Ns k) ≤ Ka ^ 4 := by
    intro k i
    have hi : Integrable (fun X => a k i X ^ 4) (particleLaw A (Ns k)) :=
      integrable_of_bdd ((bam k i).1.pow_const 4) (fun X => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (bab k i X) 4)
    refine ⟨baL k i 4, ?_⟩
    calc
      (∫ X, a k i X ^ 4 ∂particleLaw A (Ns k)) ≤ ∫ _, Ka ^ 4 ∂particleLaw A (Ns k) := by
        apply integral_mono hi (integrable_const _)
        intro X
        change a k i X ^ 4 ≤ Ka ^ 4
        rw [← Even.pow_abs (by decide : Even 4) (a k i X)]
        exact pow_le_pow_left₀ (abs_nonneg _) (bab k i X) 4
      _ = _ := by simp
  have bY : ∀ k (i j : Fin c.J), BddMeas (Y k i j) := fun k i j =>
    (bddMeas_mobA hφ (Ns k) i j).sub (BddMeas.const _)
  have herrI : ∀ k (i j : Fin c.J), Integrable
      (fun X => a k i X * a k j X * Y k i j X) (particleLaw A (Ns k)) := by
    intro k i j
    simpa only [one_mul] using integrable_mul_of_bddMeas
      (memLp_const (1 : ℝ) : MemLp (fun _ => (1 : ℝ)) 2 (particleLaw A (Ns k)))
      (((bam k i).mul (bam k j)).mul (bY k i j))
  have herr : ∀ i j : Fin c.J, Tendsto (fun k =>
      ∫ X, a k i X * a k j X * Y k i j X ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
    intro i j
    have hh := t01_mobility_weighted_error A μ hfix hac he hφ
      (fun _ => EventuallyEq.rfl) hp hBp hρ Ns hNs
      (fun k => (bam k i).1.aestronglyMeasurable) (fun k => ha2 k i) (fun k => ha4 k j) i j
    refine squeeze_zero_norm (fun k => ?_) hh
    rw [Real.norm_eq_abs]
    exact abs_integral_le_integral_abs
  have hlam : ∀ i, 0 ≤ lamShift lam i := fun i => he.lam_nonneg' (i + 1)
  obtain ⟨KH, hKH⟩ := cylH_bounds hlam c
  have hHI : ∀ k, Integrable (fun X => cylH (lamShift lam) c (z k X))
      (particleLaw A (Ns k)) := fun k =>
    integrable_of_bdd ((continuous_cylH _ c).measurable.comp (measurable_zC hφ (Ns k) c.J))
      (fun X => by rw [abs_of_nonneg (hKH _).1]; exact (hKH _).2)
  have hHγ : Integrable (fun w : ℕ → ℝ => cylH (lamShift lam) c (fun i => w i)) γ :=
    integrable_of_bdd ((continuous_cylH _ c).measurable.comp (measurable_zBlock c.J))
      (fun w => by rw [abs_of_nonneg (hKH _).1]; exact (hKH _).2)
  have hForm : (c.form (lamShift lam) γ).toReal =
      ∫ w : ℕ → ℝ, cylH (lamShift lam) c (fun i => w i) ∂γ := by
    unfold Cyl.form
    change (∫⁻ w : ℕ → ℝ, ENNReal.ofReal (cylH (lamShift lam) c (fun i => w i)) ∂γ).toReal = _
    rw [← ofReal_integral_eq_lintegral_ofReal hHγ
      (Eventually.of_forall fun w => (hKH _).1),
      ENNReal.toReal_ofReal (integral_nonneg fun w => (hKH _).1)]
  have hmain : Tendsto (fun k =>
      ∫ X, cylH (lamShift lam) c (z k X) ∂particleLaw A (Ns k)) atTop
      (𝓝 (∫ w : ℕ → ℝ, cylH (lamShift lam) c (fun i => w i) ∂γ)) := by
    change Tendsto (fun k => ∫ X, cylH (lamShift lam) c
      (fun i : Fin c.J => fluct e (Ns k) i X) ∂particleLaw A (Ns k)) atTop
      (𝓝 (∫ w : ℕ → ℝ, cylH (lamShift lam) c (fun i => w i) ∂γ))
    have hh := hlaw c.J ((cylHb hlam c).compContinuous ⟨Prod.snd, continuous_snd⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      cylHb_apply, Function.comp_def] using hh
  have hdiff : ∀ k, particleEnergy A (Ns k) ⟨_, hmem k⟩ =
      (∑ i : Fin c.J, ∑ j : Fin c.J,
        ∫ X, a k i X * a k j X * Y k i j X ∂particleLaw A (Ns k)) +
      ∫ X, cylH (lamShift lam) c (z k X) ∂particleLaw A (Ns k) := by
    intro k
    rw [t01_particle_cylinder_energy_eq A (Ns k) e hφ c (hmem k)]
    have hpt : ∀ X : ParticleSpace d (Ns k),
        (∑ i : Fin c.J, ∑ j : Fin c.J, a k i X * a k j X * mobA e (Ns k) X i j) =
        (∑ i : Fin c.J, ∑ j : Fin c.J, a k i X * a k j X * Y k i j X) +
          cylH (lamShift lam) c (z k X) := by
      intro X
      simp only [Y, cylH, lamShift]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ =>
        sum_mul_sub_ite (fun i => a k i X) (fun i j => mobA e (Ns k) X i j)
          (fun i => lam (i.val + 1)) i
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_add (integrable_finset_sum _ fun i _ =>
        integrable_finset_sum _ fun j _ => herrI k i j) (hHI k),
      integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => herrI k i j]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => herrI k i j
  have hsum : Tendsto (fun k => ∑ i : Fin c.J, ∑ j : Fin c.J,
      ∫ X, a k i X * a k j X * Y k i j X ∂particleLaw A (Ns k)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin c.J)) fun j _ => herr i j
  rw [hForm]
  simp_rw [hdiff]
  simpa only [zero_add] using hsum.add hmain

end DGPS.Lipschitz
