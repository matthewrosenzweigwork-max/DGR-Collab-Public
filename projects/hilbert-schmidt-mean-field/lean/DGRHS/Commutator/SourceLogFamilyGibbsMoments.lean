/- Common literal logarithmic Gibbs constants, chosen before every density
and velocity in a scalar-controlled family. The I >= -J prefactor is kept.
No favorable family partition, numerator or Gibbs moment is supplied. -/
import DGRHS.Commutator.SourceLogFamilyLiteralBounds
import DGRHS.Commutator.SourceLogTransportFamilyLocal
import DGRHS.Commutator.SourceLogTransportGibbsMoments
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

theorem exists_log_transport_family_gibbs_moments (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) →
      ∀ M : ℝ, 0 ≤ M → 0 < (Fintype.card ι : ℝ) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) → ∀ J : ℝ,
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc (-J)
        DGRHS.Concentration.glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι, LipschitzWith K v →
      ∀ ρ : EuclideanSpace ℝ ι → ℝ,
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      -J ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
        (fun a b => logPhysicalPair (a,b)) →
      (∀ N : ℕ, 1 ≤ N → (sourceLogSingularPartition β ρ N).toReal ≤ Cpf) ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun x => Real.exp (σ*ε*((N : ℝ)*sourceTransportEnergy
        (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x)))
        (sourceLogSingularGibbs β ρ N) ∧
      (∫ x, Real.exp (σ*ε*((N : ℝ)*sourceTransportEnergy
        (gaussianRieszDensityMeasure ρ) (sourceLogTransportKernel n v) N x))
        ∂sourceLogSingularGibbs β ρ N) ≤ Cem := by
  obtain ⟨Csr, hC, hlocal⟩ := exists_log_transport_family_local_numerator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K hK M hM hd
  obtain ⟨βloc, hloc, hnum⟩ := hlocal K hK M hM hd
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ J
  let B : ℝ≥0 := ⟨2*(β : ℝ), by positivity⟩
  obtain ⟨Cub, hCub, hwindow⟩ := exists_log_family_literal_window (ι := ι) B (by change 0 < 2*(β : ℝ); positivity) hd M hM
  obtain ⟨C, hC1, hcap⟩ := exists_log_family_literal_cap (ι := ι) β hd M hM
  let Cpf := max C (Real.exp (-(β : ℝ)*J))
  have hCpf : 1 ≤ Cpf := hC1.trans (le_max_left _ _)
  have hforcingLower : Real.exp (-(β : ℝ)*J) ≤ Cpf := le_max_right _ _
  let L := DGRHS.Concentration.glzUniversalTailConstant
  have hL : 0 ≤ L := DGRHS.Concentration.glzUniversalTailConstant_pos.le
  let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
  let Cem := sourceLogTransportCem (β : ℝ) βloc (-J) L Cub
  have hε : 0 < ε := sourceLogTransportEpsilon_pos _ _ _ _ hβ hloc hC (pow_pos hK n)
  have hCem : 0 < Cem := sourceLogTransportCem_pos _ _ _ _ _ hL hCub
  have hforcing : 0 ≤ Real.log Cpf + Real.log Cem := by
    dsimp only [Cem, sourceLogTransportCem]
    split_ifs
    · simpa only [neg_mul, mul_neg, neg_neg] using
        log_small_Cem_forcing_nonnegative (-(β : ℝ)*J) Cpf L hforcingLower hL
    · simpa only [neg_mul, mul_neg, neg_neg] using
        log_large_Cem_forcing_nonnegative (-(β : ℝ)*J) Cpf L Cub hforcingLower hL hCub
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, ?_⟩
  intro v hv ρ hμ hρ hpair hI
  refine ⟨fun N hN => (hcap ρ hρ hpair N hN).trans (le_max_left _ _), ?_⟩
  intro σ hσ N hN
  let μ := gaussianRieszDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
  let a := fun x : Fin N → EuclideanSpace ℝ ι =>
    (N : ℝ)*sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  have hpre : Real.exp (-(β : ℝ)*I) ≤ Real.exp ((β : ℝ)*J) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hI β.coe_nonneg
    change (β : ℝ)*(-J) ≤ (β : ℝ)*I at hmul
    nlinarith
  by_cases hsmall : (β : ℝ) ≤ βloc
  · let t := σ*((β : ℝ)/(4*Csr*(K : ℝ)^n))
    obtain ⟨hi, hb⟩ := hnum v hv ρ hρ hpair (β : ℝ) β.coe_nonneg hsmall σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_exponential_bound β hd ρ M hM hρ hpair N hN
      (fun x => t*a x) (Real.exp 1+L) hi (hb.trans (by linarith))
    refine ⟨by simpa only [t, ε, sourceLogTransportEpsilon, if_pos hsmall] using hq, ?_⟩
    simp only [ε, sourceLogTransportEpsilon, if_pos hsmall, Cem, sourceLogTransportCem,
      if_pos hsmall, neg_mul, mul_neg, neg_neg]
    calc
      _ ≤ (Real.exp 1+L)/Real.exp ((β : ℝ)*I) := hqb
      _ = Real.exp (-(β : ℝ)*I)*(Real.exp 1+L) := by
        rw [div_eq_mul_inv, ←Real.exp_neg]
        ring
      _ ≤ Real.exp ((β : ℝ)*J)*(Real.exp 1+L) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
  · have hlarge : βloc < (β : ℝ) := lt_of_not_ge hsmall
    let γ : ℝ≥0 := ⟨βloc, hloc.le⟩
    have hγβ : (γ : ℝ) ≤ (β : ℝ) := hlarge.le
    let θ : ℝ≥0 := ⟨2*(β : ℝ)-(γ : ℝ), by linarith [β.coe_nonneg]⟩
    have hθB : (θ : ℝ) ≤ (B : ℝ) := by change 2*(β : ℝ)-βloc ≤ 2*(β : ℝ); linarith
    have hcapθ := hwindow ρ hρ hpair θ hθB N hN
    let t := σ*(βloc/(4*Csr*(K : ℝ)^n))
    obtain ⟨hi, hb⟩ := hnum v hv ρ hρ hpair βloc hloc.le le_rfl σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_holder_bound β γ hγβ hd ρ M hM hρ hpair N hN
      a t (Real.exp 1+L) Cub hi (hb.trans (by linarith)) hcapθ
    have he : t/2 = σ*ε := by
      dsimp [t, ε, sourceLogTransportEpsilon]
      rw [if_neg hsmall]
      ring
    simp_rw [he] at hq hqb
    refine ⟨hq, ?_⟩
    simp only [Cem, sourceLogTransportCem, if_neg hsmall, neg_mul, mul_neg, neg_neg]
    exact hqb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpre (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_log_transport_family_gibbs_moments
#print axioms DGRHS.Commutator.exists_log_transport_family_gibbs_moments
