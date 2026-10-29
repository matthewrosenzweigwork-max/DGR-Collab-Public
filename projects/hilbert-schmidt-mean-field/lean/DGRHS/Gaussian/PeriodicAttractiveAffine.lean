import DGRHS.Gaussian.PeriodicAttractiveCanonicalRate
import DGRHS.Gaussian.PeriodicLogOriginalRate
import DGRHS.Gaussian.PeriodicRieszSingularPartition
import DGRHS.Concentration.SourceAffineComparison
import DGRHS.Attractive.FactorialCanonicalComparison

/-!
Packet P11b, unit 2 (clause 2, step 5): the torus one-body restoration for the attractive LOG gas.
Automatic hypotheses on the torus (Remark 2.1 and the sentence after Theorem 2.6, TeX 646): for a
bounded background density `ρ ≤ M` the attractive one-body potential is bounded (so
`e^{c h_μ^att} ∈ L¹(μ)` for every `c`, and `h_μ^att ∈ L²`), and the singular pair-`L¹` hypothesis
holds (the periodic kernel is Haar-integrable and the capped-density law has no atoms).
`periodicAttractiveLog_source_affine_comparison` is the torus form of
`DGRHS.Attractive.attractiveLog_source_affine_comparison` (TeX 2907-2944).
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The singular pair-`L¹` hypothesis `g_att ∈ L¹(μ⊗²)` holds for every bounded background density. -/
theorem periodicSingularAbsLog_density_finite (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∫⁻ p, periodicSingularAbsLog p ∂(periodicCappedDensityMeasure ρ).prod
      (periodicCappedDensityMeasure ρ)) < ∞ :=
  (periodicSingularAbsLog_finite_iff _).mpr
    ⟨periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable,
      ae_periodicCappedDensity_pair_ne ρ⟩

lemma periodicAttractivePotential_eq_neg (μ : Measure (PeriodicTorus ι)) (x : PeriodicTorus ι) :
    DGRHS.potential μ periodicAttractiveInteraction x =
      -DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x := by
  simp only [DGRHS.potential, periodicAttractiveInteraction, integral_neg]

lemma periodicAttractivePotential_memLp (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (DGRHS.potential (periodicCappedDensityMeasure ρ) periodicAttractiveInteraction) 2
      (periodicCappedDensityMeasure ρ) := by
  have h := (periodicLogPotential_memLp ρ M hM hρ).neg
  have he : DGRHS.potential (periodicCappedDensityMeasure ρ) periodicAttractiveInteraction =
      -DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) := by
    funext x
    exact periodicAttractivePotential_eq_neg _ x
  rw [he]
  exact h

/-- `e^{c h_μ^att} ∈ L¹(μ)` for every `c`: the attractive one-body potential is bounded on the torus. -/
theorem periodicAttractivePotential_exp_integrable (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (c : ℝ) :
    Integrable (fun x => Real.exp (c * DGRHS.potential (periodicCappedDensityMeasure ρ)
      periodicAttractiveInteraction x)) (periodicCappedDensityMeasure ρ) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  set B : ℝ := M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι with hB
  have hmeas := (periodicAttractivePotential_memLp ρ M hM hρ).aestronglyMeasurable
  refine (integrable_const (Real.exp (|c| * B))).mono'
    (Real.continuous_exp.comp_aestronglyMeasurable (hmeas.const_mul c))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hb := periodicLogKernel_potential_abs_le ρ M hM hρ x
  rw [periodicAttractivePotential_eq_neg]
  calc c * -DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x
      ≤ |c * -DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x| :=
        le_abs_self _
    _ = |c| * |DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x| := by
        rw [abs_mul, abs_neg]
    _ ≤ |c| * B := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

theorem periodicAttractiveLog_source_affine_comparison
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M C β : ℝ) (hM : 0 ≤ M) (hC : 0 < C) (hβ : 0 < β)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hrows : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
        periodicAttractiveInteraction x y| ^ p) ∂periodicCappedDensityMeasure ρ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hsmall : (2 * β) * (attractiveMomentConstant * C) < 1) :
    let μ := periodicCappedDensityMeasure ρ
    let h := fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2
    let F := DGRHS.potential μ periodicAttractiveInteraction
    let I := DGRHS.interactionEnergy μ periodicAttractiveInteraction
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N →
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
        (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      |(∫ x : Fin N → PeriodicTorus ι, Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
        Real.exp (β * I) * DGRHS.Concentration.canonicalPartition μ β h N| ≤ D / Real.sqrt (N : ℝ) := by
  intro μ h F I
  have hpair := periodicSingularAbsLog_density_finite ρ M hρ
  have hWi : Integrable (Function.uncurry (periodicAttractiveInteraction (ι := ι))) (μ.prod μ) := by
    rw [periodicAttractiveInteraction_uncurry]
    exact ((periodicSingularAbsLog_finite_iff μ).mp hpair).1.neg
  have hWm : StronglyMeasurable (Function.uncurry (periodicAttractiveInteraction (ι := ι))) := by
    rw [periodicAttractiveInteraction_uncurry]
    exact measurable_periodicLogKernelPair.neg.stronglyMeasurable
  have hm : Measurable h := (stronglyMeasurable_hoeffdingCentered μ _ hWm).measurable
  have hr : RowFactorialMoments μ h C := rowFactorialMoments_of_lintegral μ h hm C hC.le hrows
  have h2 := joint_memLp μ h hm C hr 2 (by omega)
  have hF := periodicAttractivePotential_memLp ρ M hM hρ
  have hs : ∀ x y, h (x, y) = h (y, x) :=
    DGRHS.centeredKernel_symmetric μ _ periodicAttractiveInteraction_symm
  have hc : ∀ᵐ y ∂μ, ∫ x, h (x, y) ∂μ = 0 := DGRHS.integral_centeredKernel_left μ _ hWi
  have hbase : β * (attractiveMomentConstant * C) < 1 := by
    nlinarith [mul_nonneg attractiveMomentConstant_pos.le hC.le]
  let MS := periodicAttractiveUniformConstant μ C (2 * β)
  let MC := 2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2)
  let D := |β| * Real.sqrt (variance F μ) * (Real.sqrt MS + Real.exp (β * I) * Real.sqrt MC)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro N hN
  have hn : 0 < N := by omega
  have ht2 : Integrable (fun x => Real.exp (2 * (2 * β) * F x)) μ :=
    periodicAttractivePotential_exp_integrable ρ M hM hρ (2 * (2 * β))
  have hu := periodicAttractiveLog_source_uniform μ hpair C (2 * β) hC.le hrows
    (by positivity) hsmall ht2 N hn
  simp_rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ hn] at hu
  have he (x : Fin N → PeriodicTorus ι) :
      2 * DGRHS.CLT.sourceParticleExponent h F I β N x =
        DGRHS.CLT.sourceParticleExponent h F I (2 * β) N x := by
    unfold DGRHS.CLT.sourceParticleExponent
    ring
  have hiS : Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
      (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N => μ)) := by
    simp_rw [he]
    simpa only [DGRHS.CLT.sourceParticleExponent, h, F, I] using hu.1
  have hbS : (∫ x : Fin N → PeriodicTorus ι, Real.exp
      (2 * DGRHS.CLT.sourceParticleExponent h F I β N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ MS := by
    simp_rw [he]
    simpa only [DGRHS.CLT.sourceParticleExponent, h, F, I, MS, periodicAttractiveUniformConstant] using hu.2
  have hcanon := attractiveCanonical_uniform_exponential μ h hm C hr hs hc β
    (by simpa only [abs_of_nonneg hβ.le] using hbase) N
  have hcE (x : Fin N → PeriodicTorus ι) : β * attractiveNormalizedStatistic N h x =
      -β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    rw [attractiveStatistic_eq_neg_normalized]
    ring
  simp_rw [hcE] at hcanon
  have hz := DGRHS.Concentration.sourceAffinePartition_comparison μ β I h h2 F hF
    N hN MS MC hiS hcanon.1 hbS hcanon.2
  have hscalar : β * (∫ x, F x ∂μ) - β * I = β * I := by
    rw [DGRHS.integral_potential μ periodicAttractiveInteraction hWi]
    dsimp [I]
    ring
  rw [hscalar] at hz
  constructor
  · simpa only [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ hn,
      DGRHS.CLT.sourceParticleExponent, h, F, I, μ] using hz.1
  · rw [DGRHS.Concentration.sourceEnergy_partition_eq_affine μ β I h F N hN]
    exact hz.2.2

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicSingularAbsLog_density_finite
#print axioms DGRHS.Periodic.periodicAttractivePotential_memLp
#print axioms DGRHS.Periodic.periodicAttractivePotential_exp_integrable
#print axioms DGRHS.Periodic.periodicAttractiveLog_source_affine_comparison
