import DGRHS.Gaussian.GaussianLogInfraredConvergence
import DGRHS.Gaussian.GaussianRieszFullMoment

/-! Actual finite-iid source exponent convergence for the
literal logarithmic kernel. The positive-Riesz import supplies only the checked
generic finite-sum continuity helper. No positive-Riesz zero-exponent identity
or uniform exponential conclusion is invoked. Root owns the original source
energy measure export; this exponent retains its exact affine correction. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators Topology
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma tendsto_gaussianLogInfraredCentered (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (hp : p.1 ≠ p.2) :
    Tendsto (fun j => hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianLogInfraredPair (T j)) p) atTop
      (𝓝 (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair p)) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hraw := tendsto_gaussianLogAnchored T hT ‖p.1-p.2‖ (norm_pos_iff.mpr (sub_ne_zero.mpr hp))
  have h1 := tendsto_gaussianLogInfrared_potential T hT hd ρ M hM hρ hpair p.1
  have h2 := tendsto_gaussianLogInfrared_potential T hT hd ρ M hM hρ hpair p.2
  have hm := tendsto_gaussianLogInfrared_pairMean T hT hd ρ hpair
  have hs (S : ℝ) : (fun x => gaussianLogInfraredPair S (x,p.2)) =
      (fun x => gaussianLogInfraredPair S (p.2,x)) := by
    funext x; unfold gaussianLogInfraredPair; rw [norm_sub_rev]
  have hl : (fun x => logPhysicalPair (x,p.2)) = (fun x => logPhysicalPair (p.2,x)) := by
    funext x; unfold logPhysicalPair; rw [norm_sub_rev]
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp_rw [hs, hl]
  exact ((hraw.sub h1).sub h2).add hm

def gaussianLogSourceApproxExponent (μ : Measure (EuclideanSpace ℝ ι))
    (β T : ℝ) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) : ℝ :=
  β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogInfraredPair T)) ω +
    β/(n : ℝ)*(∑ i, ∫ y,gaussianLogInfraredPair T (ω i,y) ∂μ) -
    β/2*(∫ p,gaussianLogInfraredPair T p ∂μ.prod μ)

def logPhysicalMomentExponent (μ : Measure (EuclideanSpace ℝ ι))
    (β : ℝ) (n : ℕ) (ω : Fin n → EuclideanSpace ℝ ι) : ℝ :=
  β*iidNegativeStatistic n (hoeffdingCentered μ logPhysicalPair) ω +
    β/(n : ℝ)*(∑ i,logPhysicalPotential μ (ω i)) -
    β/2*(∫ p,logPhysicalPair p ∂μ.prod μ)

lemma ae_tendsto_gaussianLogSourceApproxExponent (T : ℕ → ℝ) (hT : Tendsto T atTop atTop)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (β : ℝ) (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ),
      Tendsto (fun j => gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β (T j) n ω)
        atTop (𝓝 (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n ω)) := by
  classical
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hp : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => μ),
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
  filter_upwards [hp] with ω hω
  have ht : Tendsto (fun j => iidCoupledSum n
      (hoeffdingCentered μ (gaussianLogInfraredPair (T j))) ω) atTop
      (𝓝 (iidCoupledSum n (hoeffdingCentered μ logPhysicalPair) ω)) := by
    unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
    apply physical_tendsto_finset_sum
    intro i hi
    apply physical_tendsto_finset_sum
    intro k hk
    by_cases hik : i ≠ k
    · simp only [if_pos hik]
      exact tendsto_gaussianLogInfraredCentered T hT hd ρ M hM hρ hpair (ω i,ω k) (hω i k hik)
    · simp only [if_neg hik]
      exact tendsto_const_nhds
  have hneg := ((ht.neg).div_const (2*(n : ℝ))).const_mul β
  have hpot : Tendsto (fun j => ∑ i : Fin n,∫ y,gaussianLogInfraredPair (T j) (ω i,y) ∂μ)
      atTop (𝓝 (∑ i : Fin n,logPhysicalPotential μ (ω i))) := by
    apply physical_tendsto_finset_sum
    intro i hi
    exact tendsto_gaussianLogInfrared_potential T hT hd ρ M hM hρ hpair (ω i)
  have hm := (tendsto_gaussianLogInfrared_pairMean T hT hd ρ hpair).const_mul (β/2)
  exact (hneg.add (hpot.const_mul (β/(n : ℝ)))).sub hm

end DGRHS.Gaussian

#check @DGRHS.Gaussian.tendsto_gaussianLogInfraredCentered
#print axioms DGRHS.Gaussian.tendsto_gaussianLogInfraredCentered

#check @DGRHS.Gaussian.gaussianLogSourceApproxExponent
#print axioms DGRHS.Gaussian.gaussianLogSourceApproxExponent

#check @DGRHS.Gaussian.logPhysicalMomentExponent
#print axioms DGRHS.Gaussian.logPhysicalMomentExponent

#check @DGRHS.Gaussian.ae_tendsto_gaussianLogSourceApproxExponent
#print axioms DGRHS.Gaussian.ae_tendsto_gaussianLogSourceApproxExponent

