import DGPS.Lipschitz.T01SymmetricLower
import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Particle.ProductForceFisher

/-!
# Fixed-particle ground-state Sobolev transfer

The canonical centered Gibbs density has a bounded weakly differentiable square root under
direct Lipschitz assumptions. Consequently the ground-state transform preserves the full
particle Sobolev domain. Bounds in this file are for fixed particle number; uniform reference
energy estimates require the separate defective inequality and entropy-force comparison.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz

open KernelApproximation DGPS.Particle.ProductForceFisher

variable {d : ℕ}

theorem centeredParticlePotential_has_bounded_weakGradient (A : InteractionData d)
    (hA : LipschitzData A) (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    ∃ g : ParticleSpace d N → Fin N → Tangent d,
      IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g ∧
        MemLp g ∞ (particleHaar d N) := by
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  have hDK : D.K = DGPS.centeredKernel A μ := hD
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient A hA (μ : Measure (Torus d))
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by
    rw [hD]
    exact hδ
  let g : ParticleSpace d N → Fin N → Tangent d := fun x i =>
    (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, D.G1 (x i) (x j) +
      (2 * (N : ℝ))⁻¹ • gδ (x i)
  refine ⟨g, ?_, ?_⟩
  · unfold centeredParticlePotential
    have h := df_core
      (fun x y => by rw [hDK]; exact DGPS.centeredKernel_symm A μ x y)
      D.Kc D.G1m D.G1b D.g1 (df_isWeakGradient_const (d := d) 0) hδ' N
    simpa only [hDK, Finset.sum_const_zero, zero_add, g] using h
  · refine memLp_pi_iff.2 fun i => ?_
    have hG : ∀ j : Fin N, MemLp (fun x : ParticleSpace d N => D.G1 (x i) (x j))
        ∞ (particleHaar d N) := by
      intro j
      have hp : Measurable (fun x : ParticleSpace d N => (x i, x j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      have hm : Measurable (fun x : ParticleSpace d N => D.G1 (x i) (x j)) :=
        D.G1m.comp hp
      exact MemLp.of_bound hm.aestronglyMeasurable D.B
        (Eventually.of_forall fun x => D.G1b (x i) (x j))
    have hδN : MemLp (fun x : ParticleSpace d N => gδ (x i)) ∞ (particleHaar d N) :=
      MemLp.of_bound (hδm.comp (measurable_pi_apply i)).aestronglyMeasurable Mδ
        (Eventually.of_forall fun x => hδb (x i))
    exact ((memLp_finsetSum _ fun j _ => hG j).const_smul ((N : ℝ)⁻¹)).add
      (hδN.const_smul ((2 * (N : ℝ))⁻¹))

theorem sqrt_centeredParticleDensity_eq (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (x : ParticleSpace d N) :
    Real.sqrt (centeredParticleDensity A μ N x) =
      (Real.sqrt (centeredParticleNormalizer A μ N))⁻¹ *
        Real.exp (-centeredParticlePotential A μ N x / 2) := by
  have hE : Real.exp (-centeredParticlePotential A μ N x) =
      Real.exp (-centeredParticlePotential A μ N x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [centeredParticleDensity, Real.sqrt_div (Real.exp_pos _).le, hE,
    Real.sqrt_sq (Real.exp_pos _).le, div_eq_mul_inv, mul_comm]

theorem sqrt_centeredParticleDensity_weakGradient (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+)
    {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g) :
    IsParticleHaarWeakGradient N (fun x => Real.sqrt (centeredParticleDensity A μ N x))
      (fun x => (-Real.sqrt (centeredParticleDensity A μ N x) / 2) • g x) := by
  rw [isParticleHaarWeakGradient_iff_weakGradient] at hU ⊢
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (centeredParticlePotential_continuous A μ N).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (fun _ => 0) (Set.mem_univ _))
  have hab : -M < M + 1 := by linarith
  have hrng : ∀ z : Torus ((N : ℕ) * d),
      centeredParticlePotential A μ N ((particleTorusEquiv d N).symm z) ∈ Icc (-M) (M + 1) := by
    intro z
    have h := hM ((particleTorusEquiv d N).symm z) (Set.mem_univ _)
    rw [Real.norm_eq_abs, abs_le] at h
    exact ⟨h.1, by linarith [h.2]⟩
  let F : ℝ → ℝ := fun t => (Real.sqrt (centeredParticleNormalizer A μ N))⁻¹ *
    Real.exp (-t / 2)
  have hFd : ContDiffOn ℝ ∞ F (Icc (-M) (M + 1)) :=
    (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))).contDiffOn
  have hch := chain_rule_of_cont_rep hU
    ((centeredParticlePotential_continuous A μ N).comp continuous_particleTorusEquiv_symm)
    (Eventually.of_forall fun _ => rfl) hab hrng hFd
  have hderiv : ∀ t ∈ Icc (-M) (M + 1), derivWithin F (Icc (-M) (M + 1)) t =
      -F t / 2 := by
    intro t ht
    have hd : HasDerivAt F
        ((Real.sqrt (centeredParticleNormalizer A μ N))⁻¹ *
          (Real.exp (-t / 2) * (-1 / 2))) t := by
      simpa only [F, id_eq, Pi.neg_apply, neg_div] using
        (((hasDerivAt_id t).neg.div_const 2).exp.const_mul
          (Real.sqrt (centeredParticleNormalizer A μ N))⁻¹)
    rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab t ht)]
    dsimp only [F]
    ring
  rw [particleGradT_smul]
  refine hch.congr_ae (Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · exact (sqrt_centeredParticleDensity_eq A μ N _).symm
  · simp only [Function.comp_apply, hderiv _ (hrng z), F,
      sqrt_centeredParticleDensity_eq]

/-- The multiplier used for arbitrary Sobolev tests has bounded weak derivative. -/
theorem sqrt_centeredParticleDensity_W1infty (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+)
    {g : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) g)
    (hg : MemLp g ∞ (particleHaar d N)) :
    IsParticleHaarWeakGradientLp ∞ N
      (fun x => Real.sqrt (centeredParticleDensity A μ N x))
      (fun x => (-Real.sqrt (centeredParticleDensity A μ N x) / 2) • g x) := by
  have hw := sqrt_centeredParticleDensity_weakGradient A μ N hU
  have hc : Continuous (fun x : ParticleSpace d N =>
      Real.sqrt (centeredParticleDensity A μ N x)) :=
    Real.continuous_sqrt.comp (centeredParticleDensity_continuous A μ N)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hwtop : MemLp (fun x => Real.sqrt (centeredParticleDensity A μ N x))
      ∞ (particleHaar d N) :=
    MemLp.of_bound hc.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (Set.mem_univ x))
  have hgwtop : MemLp (fun x => (-Real.sqrt (centeredParticleDensity A μ N x) / 2) • g x)
      ∞ (particleHaar d N) := by
    have hcoef : MemLp (fun x => -Real.sqrt (centeredParticleDensity A μ N x) / 2)
        ∞ (particleHaar d N) := by
      convert hwtop.const_mul (-1 / 2 : ℝ) using 1
      funext x
      ring
    exact hcoef.smul (r := ∞) hg
  exact ⟨hwtop, hgwtop, hw.ibp⟩

/-- Full Sobolev-domain transfer; no boundedness assumption on the particle test. -/
theorem centeredParticleRoot_memH1 (A : InteractionData d) (hA : LipschitzData A)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleH1 A N) :
    MemParticleHaarH1 N (centeredParticleRoot A μ N f) := by
  obtain ⟨g, hU, hg⟩ := centeredParticlePotential_has_bounded_weakGradient A hA μ N
  have hw' := sqrt_centeredParticleDensity_W1infty A μ N hU hg
  have hf := ((isParticleWeakGradient_iff A N _ _).1
    (isParticleWeakGradient_particleWeakGradient f)).mul_W1infty hw'
  exact ⟨_, hf⟩

/-- The gradient formula for the ground-state root when `gU` is the weak gradient of its
centered potential. The definition itself is an algebraic expression. -/
noncomputable def centeredParticleRootGradient (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleH1 A N)
    (gU : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) :
    Fin N → Tangent d :=
  Real.sqrt (centeredParticleDensity A μ N x) • particleWeakGradient f x -
    (centeredParticleRoot A μ N f x / 2) • gU x

theorem centeredParticleRootGradient_isWeakGradient (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleH1 A N)
    {gU : ParticleSpace d N → Fin N → Tangent d}
    (hU : IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) gU)
    (hgU : MemLp gU ∞ (particleHaar d N)) :
    IsParticleHaarWeakGradient N (centeredParticleRoot A μ N f)
      (centeredParticleRootGradient A μ N f gU) := by
  have hprod := ((isParticleWeakGradient_iff A N _ _).1
    (isParticleWeakGradient_particleWeakGradient f)).mul_W1infty
      (sqrt_centeredParticleDensity_W1infty A μ N hU hgU)
  have heq : (fun x => Real.sqrt (centeredParticleDensity A μ N x) • particleWeakGradient f x +
      f x • ((-Real.sqrt (centeredParticleDensity A μ N x) / 2) • gU x)) =
      centeredParticleRootGradient A μ N f gU := by
    funext x
    dsimp only [centeredParticleRootGradient, centeredParticleRoot]
    module
  rw [← heq]
  exact hprod

theorem centeredParticleRootGradient_covariant (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleH1 A N)
    (gU : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) :
    centeredParticleRootGradient A μ N f gU x +
        (centeredParticleRoot A μ N f x / 2) • gU x =
      Real.sqrt (centeredParticleDensity A μ N x) • particleWeakGradient f x :=
  sub_add_cancel _ _

theorem centeredParticleRootGradient_sq_le (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) (f : ParticleH1 A N)
    (gU : ParticleSpace d N → Fin N → Tangent d) (x : ParticleSpace d N) :
    particleTangentNormSq (centeredParticleRootGradient A μ N f gU x) ≤
      2 * centeredParticleDensity A μ N x * particleTangentNormSq (particleWeakGradient f x) +
      (centeredParticleDensity A μ N x * f x ^ 2 / 2) * particleTangentNormSq (gU x) := by
  have hsub (v w : Fin N → Tangent d) :
      particleTangentNormSq (v - w) ≤ 2 * particleTangentNormSq v + 2 * particleTangentNormSq w := by
    simp only [particleTangentNormSq_eq, Pi.sub_apply]
    calc
      (∑ i, ∑ j, (v i j - w i j) ^ 2) ≤
          ∑ i, ∑ j, (2 * v i j ^ 2 + 2 * w i j ^ 2) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          nlinarith [sq_nonneg (v i j + w i j)]
      _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold centeredParticleRootGradient
  refine (hsub _ _).trans_eq ?_
  rw [particleTangentNormSq_smul', particleTangentNormSq_smul',
    Real.sq_sqrt (centeredParticleDensity_pos A μ N x).le, div_pow,
    centeredParticleRoot_sq]
  ring

theorem lintegral_particleLaw_eq_centered (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (h : ParticleSpace d N → ℝ≥0∞) :
    ∫⁻ x, h x ∂particleLaw A N =
      ∫⁻ x, ENNReal.ofReal (centeredParticleDensity A μ N x) * h x
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  rw [particleLaw_eq_centered_reference A μ hμ N]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    (centeredParticleDensity_continuous A μ N).measurable.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) h

/-- Exact covariant form of the particle energy in the equilibrium product reference. -/
theorem centeredParticleRoot_energy_identity (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleH1 A N) (gU : ParticleSpace d N → Fin N → Tangent d) :
    ENNReal.ofReal (particleEnergy A N f) =
      ∫⁻ x, ENNReal.ofReal (particleTangentNormSq
        (centeredParticleRootGradient A μ N f gU x +
          (centeredParticleRoot A μ N f x / 2) • gU x))
        ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  simp_rw [centeredParticleRootGradient_covariant, particleTangentNormSq_smul',
    Real.sq_sqrt (centeredParticleDensity_pos A μ N _).le,
    ENNReal.ofReal_mul (centeredParticleDensity_pos A μ N _).le]
  rw [← lintegral_particleLaw_eq_centered A μ hμ N]
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_particleTangentNormSq (isParticleWeakGradient_particleWeakGradient f).memLp_grad)
    (Eventually.of_forall fun x => particleTangentNormSq_nonneg' _)

/-- Reference energy bound with its exact force error, in extended nonnegative values.
Uniform-in-particle-number estimates enter through the final force integral. -/
theorem centeredParticleRoot_reference_energy_bound (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (N : ℕ+)
    (f : ParticleH1 A N) (gU : ParticleSpace d N → Fin N → Tangent d) :
    (∫⁻ x, ENNReal.ofReal (particleTangentNormSq (centeredParticleRootGradient A μ N f gU x))
      ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))) ≤
      2 * ENNReal.ofReal (particleEnergy A N f) +
      ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x,
        ENNReal.ofReal (f x ^ 2 * particleTangentNormSq (gU x)) ∂particleLaw A N) := by
  let Q := Measure.pi fun _ : Fin N => (μ : Measure (Torus d))
  let p := centeredParticleDensity A μ N
  let e := fun x => particleTangentNormSq (particleWeakGradient f x)
  let h := fun x => f x ^ 2 * particleTangentNormSq (gU x)
  have he0 : ∀ x, 0 ≤ e x := fun x => particleTangentNormSq_nonneg' _
  have hh0 : ∀ x, 0 ≤ h x := fun x => mul_nonneg (sq_nonneg _) (particleTangentNormSq_nonneg' _)
  have hp0 : ∀ x, 0 ≤ p x := fun x => (centeredParticleDensity_pos A μ N x).le
  have hgc : Continuous (fun v : Fin N → Tangent d => particleTangentNormSq v) := by
    unfold particleTangentNormSq
    fun_prop
  have hem : AEMeasurable e Q := hgc.measurable.comp_aemeasurable
    (((isParticleWeakGradient_particleWeakGradient f).memLp_grad.aestronglyMeasurable.mono_ac
      (reference_absolutelyContinuous_particleLaw A μ hμ N)).aemeasurable)
  have hpm : Measurable p := (centeredParticleDensity_continuous A μ N).measurable
  have hint : Integrable e (particleLaw A N) :=
    integrable_particleTangentNormSq (isParticleWeakGradient_particleWeakGradient f).memLp_grad
  calc
    (∫⁻ x, ENNReal.ofReal (particleTangentNormSq (centeredParticleRootGradient A μ N f gU x)) ∂Q)
      ≤ ∫⁻ x, (2 : ℝ≥0∞) * (ENNReal.ofReal (p x) * ENNReal.ofReal (e x)) +
        ENNReal.ofReal (1 / 2 : ℝ) * (ENNReal.ofReal (p x) * ENNReal.ofReal (h x)) ∂Q := by
      refine lintegral_mono fun x => ?_
      have hpoint := ENNReal.ofReal_le_ofReal (centeredParticleRootGradient_sq_le A μ N f gU x)
      convert hpoint using 1
      rw [← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (hp0 x), ← ENNReal.ofReal_mul zero_le_two,
        ← ENNReal.ofReal_mul (hp0 x), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← ENNReal.ofReal_add
          (mul_nonneg zero_le_two (mul_nonneg (hp0 x) (he0 x)))
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (mul_nonneg (hp0 x) (hh0 x)))]
      congr 1
      dsimp only [p, e, h]
      ring
    _ = 2 * (∫⁻ x, ENNReal.ofReal (p x) * ENNReal.ofReal (e x) ∂Q) +
        ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ x, ENNReal.ofReal (p x) * ENNReal.ofReal (h x) ∂Q) := by
      have hmfirst : AEMeasurable (fun x => (2 : ℝ≥0∞) *
          (ENNReal.ofReal (p x) * ENNReal.ofReal (e x))) Q :=
        measurable_const.aemeasurable.mul
          (hpm.ennreal_ofReal.aemeasurable.mul hem.ennreal_ofReal)
      rw [lintegral_add_left' (f := fun x => (2 : ℝ≥0∞) *
        (ENNReal.ofReal (p x) * ENNReal.ofReal (e x))) hmfirst
        (fun x => ENNReal.ofReal (1 / 2 : ℝ) *
          (ENNReal.ofReal (p x) * ENNReal.ofReal (h x))),
        lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      rw [← lintegral_particleLaw_eq_centered A μ hμ N,
        ← lintegral_particleLaw_eq_centered A μ hμ N,
        ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall he0)]
      rfl

end DGPS.Lipschitz
