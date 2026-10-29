import DGRHS.CLT.SourceEquilibriumMacroscopic
import DGRHS.CLT.SourceRieszThermalEquilibrium
import DGRHS.CLT.EquilibriumFinitePotential
import DGRHS.Entropy.BoundedDensityLogMoment
import DGRHS.Gaussian.PeriodicRieszSingularPartition

/-!
Packet P9h, unit 1 (part 1): kernel-generic torus equilibrium splitting for Corollary 2.3
(`cor:equilibriumFreeEnergyCorrection`, TeX 558-595; Remark 2.1, TeX 492-496).

The reference measure is normalized Haar measure on the torus (`periodicHaar ι`), the equilibrium
law is `μ = periodicCappedDensityMeasure ρ` with Euler-Lagrange relation
`(periodicHaar ι).tilted (-β (V + h_μ)) = μ`, and the interaction is `W a b = g (a - b)` for an
even Haar-integrable periodic kernel `g`.  Every lemma below is the torus transcription of the
Euclidean chain `DGRHS/CLT/SourceEquilibriumPhysical.lean`, `SourceEquilibriumPartition.lean`,
`SourceEquilibriumMacroscopic.lean`, `SourceRieszThermalEquilibrium.lean`,
`EquilibriumFinitePotential.lean`, reusing the kernel-generic lemmas
`equilibrium_modulated_eq_canonical`, `equilibrium_partition_factor`, `equilibrium_product_reference`,
`canonicalSingularLaw_eq_tilted`, `canonicalSingularPartition_eq_ofReal`,
`equilibrium_entropy_free_energy`, `equilibrium_thermal_combined_cost`,
`equilibrium_integrable_potential_of_entropy`, `equilibrium_macroscopic_prefactor`,
`equilibrium_thermal_macroscopic_prefactor` unchanged.  Collision-nullness of the Haar product is
derived from the iid collision-freeness of the capped-density law (`periodic_iid_collision_free`)
and `Haar^N << μ^N`, the latter being a consequence of the Euler-Lagrange relation.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Canonical properness and the exact reduction `Z_{N,β} = (∫e^{-β(V+h_μ)})^N e^{β N I_μ} K_{N,β}(μ)`
(TeX 390-396, `eq:intro-Z-to-K-reduction`, in real form), for any even torus kernel. -/
theorem periodic_equilibrium_canonical_partition (g : PeriodicTorus ι → ℝ)
    (hge : ∀ x, g (-x) = g x) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (V : PeriodicTorus ι → ℝ) (β : ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)) x)) =
      periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N)
    (hmod : Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      sourceCanonicalModulatedEnergy
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
        (DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ) (fun a b => g (a - b))) N x))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => g (a - b)
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) ∧
    0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
    canonicalSingularPartition (periodicHaar ι) W V β N < ∞ ∧
    (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      (∫ x, Real.exp (-β * (V x + DGRHS.potential μ W x)) ∂periodicHaar ι) ^ N *
        Real.exp (β * (N : ℝ) * DGRHS.interactionEnergy μ W) *
        (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
          sourceCanonicalModulatedEnergy
            (hoeffdingCentered μ
              (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) := by
  intro μ W
  have hW : ∀ x y, W x y = W y x := by
    intro x y
    show g (x - y) = g (y - x)
    rw [← neg_sub y x, hge]
  have hproper := equilibrium_modulated_eq_canonical (μ := μ) W hW V β N (by omega) hEL hmod
  have href := equilibrium_product_reference (periodicHaar ι) μ
    (fun x => -β * (V x + DGRHS.potential μ W x)) hEL N
  letI : NeZero (Measure.pi (fun _ : Fin N => periodicHaar ι)) := ⟨href.2⟩
  have hc := href.1.ae_le (periodic_iid_collision_free ρ N)
  obtain ⟨hp, hfin, -⟩ := canonicalSingularLaw_eq_tilted (periodicHaar ι) W V β N hproper.1 hc
  refine ⟨hproper.1, hp, hfin, ?_⟩
  rw [canonicalSingularPartition_eq_ofReal (periodicHaar ι) W V β N hproper.1 hc,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le))]
  exact equilibrium_partition_factor (μ := μ) W hW V β N (by omega) hEL hmod

/-- Separate-integral form (TeX 543-556): `Z_{N,β} = e^{-β N F_{β,V}(μ)} K_{N,β}(μ)` and the
entropy of the equilibrium law is integrable, for `V` integrable against the equilibrium law. -/
theorem periodic_equilibrium_macroscopic_generic (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι)) (hge : ∀ x, g (-x) = g x) (ρ : PeriodicTorus ι → ℝ)
    (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (V : PeriodicTorus ι → ℝ) (hV : Integrable V (periodicCappedDensityMeasure ρ)) (β : ℝ)
    (hβ : β ≠ 0)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)) x)) =
      periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N)
    (hmod : Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      sourceCanonicalModulatedEnergy
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
        (DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ) (fun a b => g (a - b))) N x))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => g (a - b)
    (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
      canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
    Integrable (llr μ (periodicHaar ι)) μ ∧
    (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
          sourceCanonicalModulatedEnergy
            (hoeffdingCentered μ
              (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) := by
  intro μ W
  have hpair : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ g hg
  obtain ⟨-, hpos, hfin, hfac⟩ := periodic_equilibrium_canonical_partition g hge ρ V β hEL N hN hmod
  have hent := equilibrium_entropy_free_energy (periodicHaar ι) μ W V β hβ hpair hV hEL
  have hpre := equilibrium_macroscopic_prefactor (periodicHaar ι) μ W V β hβ hpair hV hEL N
  rw [hpre] at hfac
  exact ⟨⟨hpos, hfin⟩, hent.1, hfac⟩

/-- Combined-cost (thermal) form: potential and entropy are combined before integration, so no
integrability of `V` or of the entropy is assumed; the combined cost is a conclusion
(`DGRHS.CLT.equilibrium_thermal_combined_cost`). -/
theorem periodic_equilibrium_thermal_generic (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι)) (hge : ∀ x, g (-x) = g x) (ρ : PeriodicTorus ι → ℝ)
    (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (V : PeriodicTorus ι → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)) x)) =
      periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N)
    (hmod : Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      sourceCanonicalModulatedEnergy
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
        (DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ) (fun a b => g (a - b))) N x))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => g (a - b)
    (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
      canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
    Integrable (fun x => β * V x + llr μ (periodicHaar ι) x) μ ∧
    (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
          sourceCanonicalModulatedEnergy
            (hoeffdingCentered μ
              (fun q : PeriodicTorus ι × PeriodicTorus ι => g (q.1 - q.2)))
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
          ∂Measure.pi (fun _ : Fin N => μ)) := by
  intro μ W
  have hpair : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ g hg
  obtain ⟨-, hpos, hfin, hfac⟩ := periodic_equilibrium_canonical_partition g hge ρ V β hEL N hN hmod
  have hcost := equilibrium_thermal_combined_cost (periodicHaar ι) μ W V β hβ hpair hEL
  have hpre := equilibrium_thermal_macroscopic_prefactor (periodicHaar ι) μ W V β hβ hpair hEL N
  rw [hpre] at hfac
  exact ⟨⟨hpos, hfin⟩, hcost.1, hfac⟩

/-! ### Finite entropy of a bounded-density law on the torus -/

/-- The log-likelihood ratio of a capped-density law with respect to Haar measure is bounded above
by `log (1 + M)` almost everywhere (torus form of `DGRHS.Entropy.llr_densityMeasure_le`). -/
lemma periodic_llr_densityMeasure_le (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      llr (periodicCappedDensityMeasure ρ) (periodicHaar ι) x ≤ Real.log (1 + M) := by
  let μ := periodicCappedDensityMeasure ρ
  have hμ : μ ≪ periodicHaar ι := withDensity_absolutelyContinuous _ _
  obtain ⟨g, hgm, hg, hgeq⟩ := exists_measurable_le_withDensity_eq
    (periodicHaar ι) (fun x => ENNReal.ofReal (ρ x))
  have hRN : μ.rnDeriv (periodicHaar ι) =ᵐ[periodicHaar ι] g := by
    change ((periodicHaar ι).withDensity (fun x => ENNReal.ofReal (ρ x))).rnDeriv
      (periodicHaar ι) =ᵐ[periodicHaar ι] g
    rw [← hgeq]
    exact Measure.rnDeriv_withDensity (periodicHaar ι) hgm
  filter_upwards [hμ.ae_le hRN, hμ.ae_le hρ, Measure.rnDeriv_pos hμ] with x hx hρx hp
  change Real.log (μ.rnDeriv (periodicHaar ι) x).toReal ≤ Real.log (1 + M)
  apply Real.log_le_log (ENNReal.toReal_pos hp.ne' ?_) ?_
  · rw [hx]
    exact ne_of_lt ((hg x).trans_lt ENNReal.ofReal_lt_top)
  · have hh : (μ.rnDeriv (periodicHaar ι) x).toReal ≤ M := by
      rw [hx, ← ENNReal.toReal_ofReal hM]
      exact ENNReal.toReal_mono (by simp) ((hg x).trans (ENNReal.ofReal_le_ofReal hρx))
    linarith

/-- A bounded-density law on the torus has integrable differential entropy (the reference measure
is a probability measure, so no logarithmic moment is needed). -/
theorem periodic_integrable_llr (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Integrable (llr (periodicCappedDensityMeasure ρ) (periodicHaar ι))
      (periodicCappedDensityMeasure ρ) :=
  DGRHS.Entropy.integrable_llr_of_upper_bound_and_reference (periodicHaar ι)
    (periodicCappedDensityMeasure ρ) (withDensity_absolutelyContinuous _ _) (fun _ => (0 : ℝ))
    (Real.log (1 + M)) (by simpa using integrable_const (1 : ℝ)) (integrable_zero _ _ _)
    (periodic_llr_densityMeasure_le ρ M hM hρ)

/-- Under the Euler-Lagrange relation, `V` is integrable against a bounded-density equilibrium law
whose pair interaction is integrable (finite entropy plus finite potential energy). -/
theorem periodic_equilibrium_integrable_potential (g : PeriodicTorus ι → ℝ)
    (hg : Integrable g (periodicHaar ι)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (V : PeriodicTorus ι → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ) (fun a b => g (a - b)) x)) =
      periodicCappedDensityMeasure ρ) :
    Integrable V (periodicCappedDensityMeasure ρ) :=
  equilibrium_integrable_potential_of_entropy (periodicHaar ι) (periodicCappedDensityMeasure ρ)
    (fun a b => g (a - b)) V β hβ (periodicDensityPair_integrable_of_haar ρ M hρ g hg)
    (periodic_integrable_llr ρ M hM hρ) hEL

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodic_equilibrium_canonical_partition
#print axioms DGRHS.Periodic.periodic_equilibrium_macroscopic_generic
#print axioms DGRHS.Periodic.periodic_equilibrium_thermal_generic
#print axioms DGRHS.Periodic.periodic_llr_densityMeasure_le
#print axioms DGRHS.Periodic.periodic_integrable_llr
#print axioms DGRHS.Periodic.periodic_equilibrium_integrable_potential
