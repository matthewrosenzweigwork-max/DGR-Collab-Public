import DGRHS.Kinetic.ParticleMaxwellian
import DGRHS.CLT.EquilibriumCollisionWeight
import DGRHS.CLT.SourceEquilibriumAllN
import DGRHS.CLT.SourceEnergyMeasurable
import DGRHS.Commutator.SourceT28FullRange
import DGRHS.Gaussian.GaussianLogFullPositivity
import DGRHS.Gaussian.GaussianRieszCenteredComparison

/-! Packet P15: the kinetic Gibbs identification for the singular laws
(Remark 2.1 `rem:torus-kinetic-variants`, kinetic half, TeX 495; Remark 2.12, TeX 833).

Printed claim (TeX 495): "If the starting Hamiltonian `H_N` is augmented by the standard
quadratic kinetic energy, then the velocity variables tensorize as an independent Maxwellian
factor."  Remark 2.12: "When `μ = μ_β` is the thermal equilibrium law,
`Q_{N,β}(μ_β) = P_{N,β}`."  Combined: the kinetic canonical Gibbs measure
`∝ e^{-β(H_N + Σ|v_i|²/2)} dX dV` equals `Q_{N,β}(μ_β) ⊗ Maxwellian`, where `H_N` is the
SINGULAR (collision-zero) Hamiltonian (TeX 333-339).

Here the kinetic objects are DEFINED from the collision-zero weight of `H_N`, the kinetic
energy and the Lebesgue velocity reference (not from a product), and the tensorization is
proved:
* (A) `kineticCanonicalSingularLaw_eq_prod`: generic over a σ-finite `ν₀`;
* (B) `kinetic_sourceLogGibbs_prod_eq_tilted`, `kinetic_sourceRieszGibbs_prod_eq_tilted`:
  the modulated side, the kinetic modulated Hamiltonian `N F_N + KE`;
* (C) `kineticCanonicalSingularLaw_log_eq`, `kineticCanonicalSingularLaw_riesz_eq`:
  the statement of the paper, under the hypotheses of the P3 exports. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
universe u
namespace DGRHS.Kinetic
open DGRHS.Gaussian DGRHS.CLT DGRHS.Commutator

section generic
variable {S : Type*} [MeasurableSpace S]

/-- The kinetic canonical collision-zero partition function: the literal `∫⁻` of the
numerator `1_{no collision} e^{-β H_N(x)} e^{-β Σ|v_i|²/2}` over the reference
`ν₀^{⊗N} ⊗ Lebesgue(ℝ^{N d})`.  It is NOT assumed to factorize. -/
def kineticCanonicalSingularPartition (ι : Type*) [Fintype ι]
    (ν₀ : Measure S) (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : (Fin N → S) × ((Fin N × ι) → ℝ),
    canonicalSingularWeight W V β N z.1 *
      ENNReal.ofReal (Real.exp (-β * particleKineticEnergy N z.2))
    ∂((Measure.pi fun _ : Fin N => ν₀).prod (volume : Measure ((Fin N × ι) → ℝ)))

/-- The kinetic canonical collision-zero Gibbs law of `H_N + Σ|v_i|²/2`, defined as the
normalized density of the collision-zero weight times `e^{-β KE}` against the reference
`ν₀^{⊗N} ⊗ Lebesgue`. -/
def kineticCanonicalSingularLaw {ι : Type*} [Fintype ι]
    (ν₀ : Measure S) (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (N : ℕ) :
    Measure ((Fin N → S) × ((Fin N × ι) → ℝ)) :=
  ((Measure.pi fun _ : Fin N => ν₀).prod (volume : Measure ((Fin N × ι) → ℝ))).withDensity
    (fun z => canonicalSingularWeight W V β N z.1 *
      ENNReal.ofReal (Real.exp (-β * particleKineticEnergy N z.2)) /
      kineticCanonicalSingularPartition ι ν₀ W V β N)

variable {ι : Type*} [Fintype ι]

/-- Velocity side of the partition function: the Gaussian integral in `ℝ≥0∞`. -/
lemma lintegral_ofReal_exp_particleKineticEnergy (β : ℝ) (hβ : 0 < β) (N : ℕ) :
    (∫⁻ v : (Fin N × ι) → ℝ, ENNReal.ofReal (Real.exp (-β * particleKineticEnergy N v))) =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi / β)) ^ (N * Fintype.card ι)) := by
  have hint : Integrable (fun v : (Fin N × ι) → ℝ =>
      Real.exp (-β * particleKineticEnergy N v)) volume := by
    simp_rw [← particle_kinetic_exponent]
    exact kinetic_exp_integrable β hβ
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun v => (Real.exp_pos _).le)]
  rw [particle_kinetic_partition β hβ N]

/-- The kinetic partition function is `Z_{N,β} · (√(2π/β))^{N·card ι}`, derived (not assumed),
as soon as the collision-zero weight is a.e. measurable for the reference measure. -/
theorem kineticCanonicalSingularPartition_eq (ν₀ : Measure S) [SigmaFinite ν₀]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    (hw : AEMeasurable (canonicalSingularWeight W V β N) (Measure.pi fun _ : Fin N => ν₀)) :
    kineticCanonicalSingularPartition ι ν₀ W V β N =
      canonicalSingularPartition ν₀ W V β N *
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi / β)) ^ (N * Fintype.card ι)) := by
  have hm : Measurable (fun v : (Fin N × ι) → ℝ =>
      ENNReal.ofReal (Real.exp (-β * particleKineticEnergy N v))) := by
    unfold particleKineticEnergy
    fun_prop
  unfold kineticCanonicalSingularPartition canonicalSingularPartition
  rw [lintegral_prod_mul (f := canonicalSingularWeight W V β N) hw hm.aemeasurable,
    lintegral_ofReal_exp_particleKineticEnergy β hβ N]

/-- **(A)** The kinetic canonical collision-zero Gibbs law of `H_N + KE` (Lebesgue velocity
reference) is the product `canonicalSingularLaw ⊗ Maxwellian`. Premises: `β > 0`, `ν₀` σ-finite,
and a.e. measurability of the collision-zero weight (implied by integrability of the Boltzmann
factor together with collision-nullness, see
`canonicalSingularWeight_aemeasurable_of_integrable`).  No positivity or finiteness of the
partition functions is needed. -/
theorem kineticCanonicalSingularLaw_eq_prod (ν₀ : Measure S) [SigmaFinite ν₀]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    (hw : AEMeasurable (canonicalSingularWeight W V β N) (Measure.pi fun _ : Fin N => ν₀)) :
    kineticCanonicalSingularLaw (ι := ι) ν₀ W V β N =
      (canonicalSingularLaw ν₀ W V β N).prod (maxwellian (Fin N × ι) β) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi / β)) ^ (N * Fintype.card ι) := by
    have : 0 < Real.sqrt (2 * Real.pi / β) := Real.sqrt_pos.mpr (by positivity)
    positivity
  have hZ : AEMeasurable (fun x => canonicalSingularWeight W V β N x /
      canonicalSingularPartition ν₀ W V β N) (Measure.pi fun _ : Fin N => ν₀) := by
    simpa only [div_eq_mul_inv] using hw.mul_const _
  have hg : Measurable (fun v : (Fin N × ι) → ℝ => ENNReal.ofReal
      (Real.exp (-β * particleKineticEnergy N v) /
        (Real.sqrt (2 * Real.pi / β)) ^ (N * Fintype.card ι))) := by
    unfold particleKineticEnergy
    fun_prop
  rw [particle_maxwellian_density β hβ N]
  unfold canonicalSingularLaw
  rw [prod_withDensity₀ hZ hg.aemeasurable]
  unfold kineticCanonicalSingularLaw
  rw [kineticCanonicalSingularPartition_eq ν₀ W V β hβ N hw]
  apply congrArg
  funext z
  have key : ∀ (w Z a c : ℝ≥0∞), c ≠ 0 → c ≠ ∞ → w * a / (Z * c) = w / Z * (a / c) := by
    intro w Z a c h0 htop
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inr htop) (Or.inr h0)]
    ring
  rw [ENNReal.ofReal_div_of_pos hc]
  exact key _ _ _ _ (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top

/-- The collision-zero weight is a.e. measurable when the Boltzmann factor is integrable and
collisions are null (the premises of `canonicalSingularLaw_eq_tilted`). -/
lemma canonicalSingularWeight_aemeasurable_of_integrable (ν₀ : Measure S)
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (N : ℕ)
    (hi : Integrable (fun x => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi fun _ : Fin N => ν₀))
    (hc : ∀ᵐ x : Fin N → S ∂Measure.pi fun _ : Fin N => ν₀,
      ∀ i j : Fin N, i ≠ j → x i ≠ x j) :
    AEMeasurable (canonicalSingularWeight W V β N) (Measure.pi fun _ : Fin N => ν₀) := by
  classical
  have hw : canonicalSingularWeight W V β N =ᵐ[Measure.pi fun _ : Fin N => ν₀]
      (fun x => ENNReal.ofReal (Real.exp (-β * sourceHamiltonian W V N x))) := by
    filter_upwards [hc] with x hx
    simp only [canonicalSingularWeight, if_pos hx]
  exact hi.aemeasurable.ennreal_ofReal.congr hw.symm

/-- **(A), with the premises of `canonicalSingularLaw_eq_tilted`.** -/
theorem kineticCanonicalSingularLaw_eq_prod_of_integrable (ν₀ : Measure S) [SigmaFinite ν₀]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    (hi : Integrable (fun x => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi fun _ : Fin N => ν₀))
    (hc : ∀ᵐ x : Fin N → S ∂Measure.pi fun _ : Fin N => ν₀,
      ∀ i j : Fin N, i ≠ j → x i ≠ x j) :
    kineticCanonicalSingularLaw (ι := ι) ν₀ W V β N =
      (canonicalSingularLaw ν₀ W V β N).prod (maxwellian (Fin N × ι) β) :=
  kineticCanonicalSingularLaw_eq_prod ν₀ W V β hβ N
    (canonicalSingularWeight_aemeasurable_of_integrable ν₀ W V β N hi hc)

end generic

section modulated
variable {ι : Type u} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Generic modulated kinetic tilt: a spatial tilt by `-β N F_N` tensorizes with the
Maxwellian under the kinetic modulated Hamiltonian `N F_N + KE` (Lebesgue velocity reference). -/
theorem kinetic_modulated_tilted_prod {X : Type*} [MeasurableSpace X] (P : Measure X)
    [SFinite P] (FN : X → ℝ) (hFN : Measurable FN) (β : ℝ) (N : ℕ) :
    (P.prod (volume : Measure ((Fin N × ι) → ℝ))).tilted
      (fun z => -β * ((N : ℝ) * FN z.1 + particleKineticEnergy N z.2)) =
      (P.tilted (fun x => -β * (N : ℝ) * FN x)).prod (maxwellian (Fin N × ι) β) := by
  have h := particle_kinetic_gibbs_factorization (ι := ι) P (fun x => (N : ℝ) * FN x)
    (hFN.const_mul _) β N
  have e : (fun x => -β * (N : ℝ) * FN x) = fun x => -β * ((N : ℝ) * FN x) := by
    funext x; ring
  rw [e]
  exact h

/-- **(B), logarithmic case `s = 0`.** `Q_{N,β}(μ) ⊗ Maxwellian` is the tilt of
`μ^{⊗N} ⊗ Lebesgue` by the kinetic modulated Hamiltonian `N F_N + Σ|v_i|²/2`. -/
theorem kinetic_sourceLogGibbs_prod_eq_tilted (β : ℝ≥0)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : E => logPhysicalPair (a, b)
    (sourceT28Gibbs 0 β ρ N).prod (maxwellian (Fin N × ι) (β : ℝ)) =
      ((Measure.pi fun _ : Fin N => μ).prod (volume : Measure ((Fin N × ι) → ℝ))).tilted
        (fun z => -(β : ℝ) * ((N : ℝ) *
          sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N z.1 +
          particleKineticEnergy N z.2)) := by
  dsimp only
  have hFm : StronglyMeasurable (DGRHS.potential (gaussianRieszDensityMeasure ρ)
      (fun a b : E => logPhysicalPair (a, b))) := by
    change StronglyMeasurable (fun x => ∫ y, logPhysicalPair (x, y) ∂gaussianRieszDensityMeasure ρ)
    exact stronglyMeasurable_logPhysicalPair.integral_prod_right'
  have hEm := (stronglyMeasurable_sourceCanonicalModulatedEnergy
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
    (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b : E => logPhysicalPair (a, b)))
    (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => logPhysicalPair (a, b)))
    (stronglyMeasurable_hoeffdingCentered _ _ stronglyMeasurable_logPhysicalPair) hFm N).measurable
  rw [sourceT28Gibbs_zero, sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,
    ← sourceEnergyTilt_eq _ _ _ (β : ℝ) N, ← kinetic_modulated_tilted_prod _ _ hEm]

/-- **(B), Riesz case `0 < s < d/2`.** -/
theorem kinetic_sourceRieszGibbs_prod_eq_tilted (s : ℝ) (β : ℝ≥0) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s) (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : E => gaussianRieszPhysicalPair s (a, b)
    (sourceT28Gibbs s β ρ N).prod (maxwellian (Fin N × ι) (β : ℝ)) =
      ((Measure.pi fun _ : Fin N => μ).prod (volume : Measure ((Fin N × ι) → ℝ))).tilted
        (fun z => -(β : ℝ) * ((N : ℝ) *
          sourceCanonicalModulatedEnergy (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N z.1 +
          particleKineticEnergy N z.2)) := by
  dsimp only
  have hFm : StronglyMeasurable (DGRHS.potential (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b))) := by
    change StronglyMeasurable (fun x =>
      ∫ y, gaussianRieszPhysicalPair s (x, y) ∂gaussianRieszDensityMeasure ρ)
    exact (stronglyMeasurable_gaussianRieszPhysicalPair s).integral_prod_right'
  have hEm := (stronglyMeasurable_sourceCanonicalModulatedEnergy
    (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
    (DGRHS.potential (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b)))
    (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
      (fun a b : E => gaussianRieszPhysicalPair s (a, b)))
    (stronglyMeasurable_hoeffdingCentered _ _ (stronglyMeasurable_gaussianRieszPhysicalPair s))
    hFm N).measurable
  rw [sourceT28Gibbs_of_ne_zero hs.ne', sourceRieszSingularGibbs_eq s (β : ℝ) hs β.coe_nonneg
    ha ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ (β : ℝ) N,
    ← kinetic_modulated_tilted_prod _ _ hEm]

/-- Under the equilibrium relation, the collision-zero weight is a.e. measurable for the
Lebesgue product reference (for `N ≥ 1` from integrability of the Boltzmann factor, for
`N = 0` trivially). -/
lemma canonicalSingularWeight_aemeasurable_euclid [Nonempty ι] (ρ : E → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (W : E → E → ℝ) (V : E → ℝ) (β : ℝ) (f : E → ℝ)
    (hEL : (volume : Measure E).tilted f = gaussianRieszDensityMeasure ρ) (N : ℕ)
    (hi : 1 ≤ N → Integrable (fun x => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi fun _ : Fin N => (volume : Measure E))) :
    AEMeasurable (canonicalSingularWeight W V β N)
      (Measure.pi fun _ : Fin N => (volume : Measure E)) := by
  by_cases hz : N = 0
  · subst hz
    exact (Subsingleton.measurable).aemeasurable
  · have href := equilibrium_product_reference (volume : Measure E)
      (gaussianRieszDensityMeasure ρ) f hEL N
    have hcollision := href.1.ae_le (density_iid_collision_free ρ N)
    exact canonicalSingularWeight_aemeasurable_of_integrable _ W V β N
      (hi (Nat.one_le_iff_ne_zero.mpr hz)) hcollision

/-- **(C), logarithmic case.** Under the hypotheses of `exists_sourceLogCanonicalStatic`
(P3 export C2), the kinetic canonical ensemble of `H_N + KE` (Lebesgue velocity reference,
spatial reference `volume^{⊗N}`) is `Q_{N,β}(μ) ⊗ Maxwellian`, `Q_{N,β}(μ) = sourceT28Gibbs 0`. -/
theorem kineticCanonicalSingularLaw_log_eq (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (V : E → ℝ)
    (hEL : (volume : Measure E).tilted (fun x => -(β : ℝ) *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => logPhysicalPair (a, b)) x)) = gaussianRieszDensityMeasure ρ) (N : ℕ) :
    kineticCanonicalSingularLaw (ι := ι) (volume : Measure E)
        (fun a b => logPhysicalPair (a, b)) V (β : ℝ) N =
      (sourceT28Gibbs 0 β ρ N).prod (maxwellian (Fin N × ι) (β : ℝ)) := by
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  rw [sourceT28Gibbs_zero, sourceLog_equilibrium_law_allN β hβ hd ρ M hM hρ hpair V hEL N]
  refine kineticCanonicalSingularLaw_eq_prod _ _ _ _ hβ N
    (canonicalSingularWeight_aemeasurable_euclid ρ _ V (β : ℝ) _ hEL N fun hN => ?_)
  exact (sourceLog_equilibrium_canonical β hβ hd ρ M hM hρ hpair V hEL N hN).1

/-- **(C), Riesz case.** Under the hypotheses of `exists_sourceRieszCanonicalStatic`
(P3 export C1; `β : ℝ≥0` with `0 < (β : ℝ)` instead of `β : ℝ`, `0 < β`), the kinetic canonical
ensemble of `H_N + KE` is `Q_{N,β}(μ) ⊗ Maxwellian`, `Q_{N,β}(μ) = sourceT28Gibbs s`. -/
theorem kineticCanonicalSingularLaw_riesz_eq (s : ℝ) (β : ℝ≥0) (hs : 0 < s)
    (hβ : 0 < (β : ℝ)) (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (V : E → ℝ)
    (hEL : (volume : Measure E).tilted (fun x => -(β : ℝ) *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a, b)) x)) = gaussianRieszDensityMeasure ρ)
    (N : ℕ) :
    kineticCanonicalSingularLaw (ι := ι) (volume : Measure E)
        (fun a b => gaussianRieszPhysicalPair s (a, b)) V (β : ℝ) N =
      (sourceT28Gibbs s β ρ N).prod (maxwellian (Fin N × ι) (β : ℝ)) := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  rw [sourceT28Gibbs_of_ne_zero hs.ne',
    sourceRiesz_equilibrium_law_allN s (β : ℝ) hs hβ ha ρ M hM hρ V hEL N]
  refine kineticCanonicalSingularLaw_eq_prod _ _ _ _ hβ N
    (canonicalSingularWeight_aemeasurable_euclid ρ _ V (β : ℝ) _ hEL N fun hN => ?_)
  exact (sourceRiesz_equilibrium_canonical s (β : ℝ) hs hβ ha ρ M hM hρ V hEL N hN).1

/-- **(C), Riesz case, real inverse temperature exactly as in the P3 export C1**
(`exists_sourceRieszCanonicalStatic`: `β : ℝ`, `0 < β`); the right side is the literal
`sourceRieszSingularGibbs s β ρ N`. -/
theorem kineticCanonicalSingularLaw_riesz_eq_real (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ) / 2 - s)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (V : E → ℝ)
    (hEL : (volume : Measure E).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => gaussianRieszPhysicalPair s (a, b)) x)) = gaussianRieszDensityMeasure ρ)
    (N : ℕ) :
    kineticCanonicalSingularLaw (ι := ι) (volume : Measure E)
        (fun a b => gaussianRieszPhysicalPair s (a, b)) V β N =
      (sourceRieszSingularGibbs s β ρ N).prod (maxwellian (Fin N × ι) β) := by
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  rw [sourceRiesz_equilibrium_law_allN s β hs hβ ha ρ M hM hρ V hEL N]
  refine kineticCanonicalSingularLaw_eq_prod _ _ _ _ hβ N
    (canonicalSingularWeight_aemeasurable_euclid ρ _ V β _ hEL N fun hN => ?_)
  exact (sourceRiesz_equilibrium_canonical s β hs hβ ha ρ M hM hρ V hEL N hN).1

end modulated

end DGRHS.Kinetic
#check @DGRHS.Kinetic.kineticCanonicalSingularPartition
#print axioms DGRHS.Kinetic.kineticCanonicalSingularPartition
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw
#check @DGRHS.Kinetic.kineticCanonicalSingularPartition_eq
#print axioms DGRHS.Kinetic.kineticCanonicalSingularPartition_eq
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod_of_integrable
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw_eq_prod_of_integrable
#check @DGRHS.Kinetic.kinetic_modulated_tilted_prod
#print axioms DGRHS.Kinetic.kinetic_modulated_tilted_prod
#check @DGRHS.Kinetic.kinetic_sourceLogGibbs_prod_eq_tilted
#print axioms DGRHS.Kinetic.kinetic_sourceLogGibbs_prod_eq_tilted
#check @DGRHS.Kinetic.kinetic_sourceRieszGibbs_prod_eq_tilted
#print axioms DGRHS.Kinetic.kinetic_sourceRieszGibbs_prod_eq_tilted
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw_log_eq
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw_log_eq
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq
#check @DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq_real
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq_real
#print axioms DGRHS.Kinetic.kineticCanonicalSingularLaw_riesz_eq
