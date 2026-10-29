import DGRHS.Gaussian.GaussianRieszCenteredConvergence

/-! Legitimate iid off-diagonal convergence and actual singular-limit uniform
exponential integrability. The full moment is derived from cutoff bounds and
the proved physical convergence, through the checked Fatou primitive. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators ENNReal Topology
namespace DGRHS.Gaussian
open DGRHS.Concentration

lemma physical_tendsto_finset_sum {J : Type*} (S : Finset J)
    (f : ℕ → J → ℝ) (g : J → ℝ)
    (hf : ∀ i ∈ S,Tendsto (fun j => f j i) atTop (𝓝 (g i))) :
    Tendsto (fun j => ∑ i ∈ S,f j i) atTop (𝓝 (∑ i ∈ S,g i)) := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty =>
    intro hf
    simpa only [Finset.sum_empty] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | @insert i S hi ih =>
    intro hf
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

variable {ι : Type*} [Fintype ι]

lemma ae_tendsto_gaussianRieszParticleCutoff (s β : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (η : ℕ → ℝ) (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0)) (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      Tendsto (fun j => β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s (η j))) ω)
        atTop (𝓝 (β*iidNegativeStatistic n
          (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω)) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hpair : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i j : Fin n,i ≠ j → ω i ≠ ω j := by
    apply ae_all_iff.2
    intro i
    apply ae_all_iff.2
    intro j
    by_cases hij : i=j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · filter_upwards [(measurePreserving_distinct_particle_pair n i j hij).quasiMeasurePreserving.ae
        (ae_gaussianRieszDensity_pair_ne ρ)] with ω hω
      exact fun _ => hω
  filter_upwards [hpair] with ω hω
  have ht : Tendsto (fun j => iidCoupledSum n
      (hoeffdingCentered μ (gaussianRieszTruncatedPair s (η j))) ω) atTop
      (𝓝 (iidCoupledSum n (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) ω)) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    apply physical_tendsto_finset_sum
    intro i hi
    apply physical_tendsto_finset_sum
    intro k hk
    by_cases hik : i ≠ k
    · simp only [if_pos hik]
      exact tendsto_gaussianRieszCenteredCutoff s hs ha ρ M hM hρ η hη hη0 (ω i,ω k) (hω i k hik)
    · simp only [if_neg hik]
      exact tendsto_const_nhds
  exact ((ht.neg).div_const (2*(n : ℝ))).const_mul β

theorem gaussianRieszPhysical_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω))
          (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) ω)
          ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨C,hC⟩ := gaussianRieszCutoff_uniform_exponential s β hs hβ ha ρ M hM hρ
  let η := fun j : ℕ => (((j+1 : ℕ) : ℝ))⁻¹
  have hη : ∀ j,0 < η j := by intro j;dsimp [η];positivity
  have hcast : Tendsto (fun j : ℕ => ((j+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hη0 : Tendsto η atTop (𝓝 0) := hcast.inv_tendsto_atTop
  refine ⟨C,?_⟩
  intro n hn
  exact exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ))
    (fun j ω => β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszTruncatedPair s (η j))) ω)
    (fun ω => β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianRieszPhysicalPair s)) ω) (fun j => (hC (η j) (hη j) n hn).1) C
    (fun j => (hC (η j) (hη j) n hn).2)
    (ae_tendsto_gaussianRieszParticleCutoff s β hs ha ρ M hM hρ η hη hη0 n)

end DGRHS.Gaussian

#check DGRHS.Gaussian.physical_tendsto_finset_sum
#print axioms DGRHS.Gaussian.physical_tendsto_finset_sum

#check DGRHS.Gaussian.ae_tendsto_gaussianRieszParticleCutoff
#print axioms DGRHS.Gaussian.ae_tendsto_gaussianRieszParticleCutoff

#check DGRHS.Gaussian.gaussianRieszPhysical_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianRieszPhysical_uniform_exponential
