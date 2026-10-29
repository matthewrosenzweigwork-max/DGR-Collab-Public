/- Literal logarithmic Appendix constants, derived from the actual physical
local numerator. Both signs, all particle numbers, original piecewise epsilon.
The remaining-temperature partition cap is constructed, not supplied. -/
import DGRHS.Commutator.SourceLogTransportLocal
import DGRHS.Entropy.GibbsHolderBootstrap
import DGRHS.Entropy.SourceLogForcingNormalization
import DGRHS.Concentration.MasterUniform
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy

def sourceLogTransportCem (β βloc I L Cub : ℝ) : ℝ :=
  if β ≤ βloc then Real.exp (-β * I) * (Real.exp 1 + L)
  else Real.exp (-β * I) * Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub

lemma sourceLogTransportCem_pos (β βloc I L Cub : ℝ)
    (hL : 0 ≤ L) (hCub : 1 ≤ Cub) : 0 < sourceLogTransportCem β βloc I L Cub := by
  unfold sourceLogTransportCem
  split_ifs <;> positivity

lemma sourceLogTransportEpsilon_pos (β βloc Csr A : ℝ)
    (hβ : 0 < β) (hloc : 0 < βloc) (hC : 0 < Csr) (hA : 0 < A) :
    0 < sourceLogTransportEpsilon β βloc Csr A := by
  unfold sourceLogTransportEpsilon
  split_ifs <;> positivity

variable {ι : Type*} [Fintype ι]

/-- Csr is independent of the velocity and density; the local threshold is
chosen before beta. The source's large-beta remaining cap is an actual
uniform partition bound at 2 beta - beta_loc. -/
theorem exists_sourceLogTransport_gibbs_moments (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub : ℝ, 1 ≤ Cub ∧
      (∀ N : ℕ, 1 ≤ N → ∀ hlarge : βloc < (β : ℝ),
        (sourceLogSingularPartition
          (⟨2 * (β : ℝ) - βloc, by linarith [hlarge, β.coe_nonneg]⟩ : ℝ≥0) ρ N).toReal ≤ Cub) ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
      let μ := gaussianRieszDensityMeasure ρ
      let a := fun x : Fin N → EuclideanSpace ℝ ι =>
        (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      Integrable (fun x => Real.exp (σ * ε * a x)) (sourceLogSingularGibbs β ρ N) ∧
      (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤
        sourceLogTransportCem (β : ℝ) βloc
          (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b)))
          DGRHS.Concentration.glzUniversalTailConstant Cub := by
  obtain ⟨Csr, hC, hlocal⟩ := exists_sourceLogTransport_local_numerator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hnum⟩ := hlocal hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  let μ := gaussianRieszDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
  let L := DGRHS.Concentration.glzUniversalTailConstant
  have hL : 0 ≤ L := DGRHS.Concentration.glzUniversalTailConstant_pos.le
  by_cases hsmall : (β : ℝ) ≤ βloc
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · intro N hN hlarge
      exact False.elim (not_lt_of_ge hsmall hlarge)
    intro σ hσ N hN
    let a := fun x : Fin N → EuclideanSpace ℝ ι =>
      (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
    let ε := (β : ℝ) / (4 * Csr * (K : ℝ)^n)
    obtain ⟨hi, hb⟩ := hnum (β : ℝ) β.coe_nonneg hsmall σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_exponential_bound β hd ρ M hM hρ hpair N hN
      (fun x => σ * ε * a x) (Real.exp 1) hi hb
    refine ⟨by simpa only [sourceLogTransportEpsilon, if_pos hsmall] using hq, ?_⟩
    have hr : Real.exp 1 / Real.exp ((β : ℝ)*I) = Real.exp (-(β : ℝ)*I)*Real.exp 1 := by
      rw [div_eq_mul_inv, ←Real.exp_neg]
      ring
    simp only [sourceLogTransportEpsilon, if_pos hsmall, sourceLogTransportCem, if_pos hsmall]
    change (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤ _
    change (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤
      Real.exp 1 / Real.exp ((β : ℝ)*I) at hqb
    rw [hr] at hqb
    simpa only [sourceLogTransportCem, if_pos hsmall] using
      hqb.trans (mul_le_mul_of_nonneg_left (by linarith : Real.exp 1 ≤ Real.exp 1 + L)
        (Real.exp_pos (-(β : ℝ)*I)).le)
  · have hlarge : βloc < (β : ℝ) := lt_of_not_ge hsmall
    let γ : ℝ≥0 := ⟨βloc, hloc.le⟩
    have hγβ : (γ : ℝ) ≤ (β : ℝ) := hlarge.le
    let θ : ℝ≥0 := ⟨2*(β : ℝ)-(γ : ℝ), by linarith [β.coe_nonneg]⟩
    obtain ⟨Cub, hCub, hcap⟩ := sourceLogPartition_original_bounds_one_le θ hd ρ M hM hρ hpair
    refine ⟨Cub, hCub, ?_, ?_⟩
    · intro N hN _
      exact (hcap N hN).2
    intro σ hσ N hN
    let a := fun x : Fin N → EuclideanSpace ℝ ι =>
      (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
    let t := σ * (βloc / (4 * Csr * (K : ℝ)^n))
    obtain ⟨hi, hb⟩ := hnum βloc hloc.le le_rfl σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_holder_bound β γ hγβ hd ρ M hM hρ hpair
      N hN a t (Real.exp 1) Cub hi hb (hcap N hN).2
    have he : t / 2 = σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n) := by
      dsimp [t, sourceLogTransportEpsilon]
      rw [if_neg hsmall]
      ring
    simp_rw [he] at hq hqb
    refine ⟨hq, ?_⟩
    simp only [sourceLogTransportCem, if_neg hsmall]
    change (∫ x, Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr
      ((K : ℝ)^n) * a x) ∂sourceLogSingularGibbs β ρ N) ≤
        Real.exp (-(β : ℝ)*I)*Real.sqrt (Real.exp 1+L)*Real.sqrt Cub
    exact hqb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : Real.exp 1 ≤ Real.exp 1 + L))
        (Real.exp_pos _).le) (Real.sqrt_nonneg _))

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceLogTransport_gibbs_moments
#print axioms DGRHS.Commutator.exists_sourceLogTransport_gibbs_moments
#print axioms DGRHS.Commutator.sourceLogTransportCem_pos
#print axioms DGRHS.Commutator.sourceLogTransportEpsilon_pos
