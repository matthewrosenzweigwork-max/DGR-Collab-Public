import DGRHS.Gaussian.PeriodicHeatParticleDomination

/-! Actual proper heat-regularized partition functions and their limit to
the source partition. Dominated convergence uses a proved common particle
bound and genuine subcollision integrability, never totalized integration. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatAttractivePartition (β τ : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : Fin N → PeriodicTorus ι,ENNReal.ofReal (Real.exp (periodicHeatParticleExponent β τ N x))
    ∂Measure.pi (fun _ : Fin N => periodicHaar ι)

lemma periodicHeatParticleDensity_integrable (hd : 2≤Fintype.card ι) (β τ : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (hτ : 0≤τ) (N : ℕ) (hN : 1≤N) :
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (periodicHeatParticleExponent β τ N x))
      (Measure.pi (fun _ : Fin N => periodicHaar ι)) := by
  have hdens := periodicHeatParticleDensity_domination hd β hβ hβd N hN
  exact hdens.1.mono' ((periodicHeatParticleExponent_measurable β τ N).exp).aestronglyMeasurable
    (hdens.2.mono (fun _ hx => hx τ hτ))

lemma periodicHeatAttractivePartition_eq_ofReal (hd : 2≤Fintype.card ι) (β τ : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (hτ : 0≤τ) (N : ℕ) (hN : 1≤N) :
    periodicHeatAttractivePartition (ι := ι) β τ N=
      ENNReal.ofReal (∫ x : Fin N → PeriodicTorus ι,Real.exp (periodicHeatParticleExponent β τ N x)
        ∂Measure.pi (fun _ : Fin N => periodicHaar ι)) :=
  (ofReal_integral_eq_lintegral_ofReal (periodicHeatParticleDensity_integrable hd β τ hβ hβd hτ N hN)
    (Eventually.of_forall (fun x => (Real.exp_pos _).le))).symm

lemma periodicHeatAttractivePartition_finite (hd : 2≤Fintype.card ι) (β τ : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (hτ : 0≤τ) (N : ℕ) (hN : 1≤N) :
    periodicHeatAttractivePartition (ι := ι) β τ N<∞ := by
  rw [periodicHeatAttractivePartition_eq_ofReal hd β τ hβ hβd hτ N hN]
  exact ENNReal.ofReal_lt_top

lemma periodicHeatParticleDensity_tendsto_ae (hd : 2≤Fintype.card ι) (β : ℝ) (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => periodicHaar ι),
      Tendsto (fun τ : ℝ => Real.exp (periodicHeatParticleExponent β τ N x))
        (𝓝[Ici 0] 0) (𝓝 (Real.exp (periodicParticleExponent β N x))) := by
  filter_upwards [periodicHeatRegularizedGreen_particle_good_ae hd N] with x hx
  apply Real.continuous_exp.continuousAt.tendsto.comp
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  by_cases hij : i=j
  · simp only [hij,ite_true]
    exact tendsto_const_nhds
  · simpa only [if_neg hij] using (hx i j hij).2

lemma periodicHeatParticleIntegral_tendsto (hd : 2≤Fintype.card ι) (β : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    Tendsto (fun τ : ℝ => ∫ x : Fin N → PeriodicTorus ι,Real.exp (periodicHeatParticleExponent β τ N x)
      ∂Measure.pi (fun _ : Fin N => periodicHaar ι)) (𝓝[Ici 0] 0)
      (𝓝 (∫ x : Fin N → PeriodicTorus ι,Real.exp (periodicParticleExponent β N x)
        ∂Measure.pi (fun _ : Fin N => periodicHaar ι))) := by
  have hdens := periodicHeatParticleDensity_domination hd β hβ hβd N hN
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (β*((N:ℝ)-1)/2*periodicHeatComparisonConstant ι)*Real.exp (periodicParticleExponent β N x))
  · exact Eventually.of_forall (fun τ => ((periodicHeatParticleExponent_measurable β τ N).exp).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact hdens.2.mono (fun _ hx => hx τ hτ)
  · exact hdens.1
  · exact periodicHeatParticleDensity_tendsto_ae hd β N

/-- The actual source heat-regularization limit, for every fixed N below
collision. Both sides are genuine extended partitions, and are proved finite. -/
theorem periodicHeatAttractivePartition_tendsto (hd : 2≤Fintype.card ι) (β : ℝ) (hβ : 0≤β)
    (hβd : β<2*(Fintype.card ι:ℝ)) (N : ℕ) (hN : 1≤N) :
    Tendsto (fun τ : ℝ => periodicHeatAttractivePartition (ι := ι) β τ N)
      (𝓝[Ici 0] 0) (𝓝 (periodicAttractivePartition (ι := ι) β N)) := by
  rw [periodicAttractivePartition_eq_ofReal β hβ hβd N hN]
  apply (ENNReal.tendsto_ofReal (periodicHeatParticleIntegral_tendsto hd β hβ hβd N hN)).congr'
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (periodicHeatAttractivePartition_eq_ofReal hd β τ hβ hβd hτ N hN).symm

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatParticleDensity_tendsto_ae
#print axioms DGRHS.Periodic.periodicHeatParticleIntegral_tendsto
#print axioms DGRHS.Periodic.periodicHeatAttractivePartition_tendsto
#check @DGRHS.Periodic.periodicHeatAttractivePartition_tendsto
