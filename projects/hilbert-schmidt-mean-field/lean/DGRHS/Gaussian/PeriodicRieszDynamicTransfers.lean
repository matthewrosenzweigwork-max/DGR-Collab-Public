import DGRHS.Gaussian.PeriodicDynamicBase
import DGRHS.Gaussian.PeriodicRieszEntropicCommutatorPrinted

/-!
Packet P11c, unit 2 (Riesz): Lemma 8.1 (`lem:dynamicEntropyTransfers`, TeX 3771-3794) on the flat
torus (Remark 2.1, TeX 492-496), Riesz branch `0 < s < d/2`.

Torus form of `DGRHS.Commutator.sourceRieszDynamic_entropy_transfers`.  The printed lemma assumes the
hypotheses of Theorem 2.13, in particular the uniform partition bounds (ii)
(`K_{N,β}(μ^t) ≤ C_{β,T}`, `K_{N,2β}(μ^t) ≤ C_{2β,T}`, TeX 877-881); they enter here as the
hypotheses `K_{N,β}(ρ) ≤ Cpart` and `K_{N,2β}(ρ) ≤ C₂` (the Euclidean Riesz export derives them from
the ρ-uniform Theorem 2.2(i); the torus P9 partition theorems are `∃ C` after `ρ`, see the P9h return
packet, deviation 1).  The lower bound `K_{N,β}(ρ₀) ≥ 1` is derived (Jensen, `I_{μ} ≥ 0`), so no
`Amax` is needed, exactly as in the Euclidean Riesz statement.  All three constants `H, Dc, Dl` are
chosen before `N`, both densities, the law, the velocity, the test and the Gronwall coefficients.
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The extended free energy of the literal initial Gibbs law is `-log K_{N,β}/(βN)`. -/
lemma periodicRieszDynamic_initial_Gibbs_objective (s β M : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N (periodicRieszSingularGibbs s β hs2 ρ N) =
      (-Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) / (β * (N : ℝ)) : ℝ) := by
  letI := periodicRieszSingularGibbs_probability s β hs hβ.le hs2 ρ M hM hρ N
  rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M hM β hβ ρ hρ N hN]
  simp [div_eq_mul_inv]

/-- Entropy from the Gronwall estimate: `KL(ν‖Q_{N,β}(ρ)) < ∞` and the printed bound
`-A log K(ρ₀) + β B + log K(ρ)` (TeX 3797-3808). -/
theorem periodicRieszDynamic_entropy_from_gronwall (s β M : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (ρ₀ ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ₀ : ∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (A B : ℝ)
    (hE : periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν ≤
      (A : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 ρ₀ M β N
        (periodicRieszSingularGibbs s β hs2 ρ₀ N) + (B / (N : ℝ) : ℝ)) :
    klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ ∧
    (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal ≤
      -A * Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ₀ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) + β * B +
        Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
  rw [periodicRieszDynamic_initial_Gibbs_objective s β M hs hβ hs2 hM ρ₀ hρ₀ N hN,
    ← EReal.coe_mul, ← EReal.coe_add] at hE
  have hbr : 0 < β * (N : ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0 < N))
  have hKL : klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ := by
    intro ht
    rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M hM β hβ ρ hρ N hN ν,
      ht, EReal.coe_ennreal_top, EReal.top_sub_coe,
      EReal.top_mul_coe_of_pos (inv_pos.mpr hbr)] at hE
    exact EReal.coe_ne_top _ (top_le_iff.mp hE)
  rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M hM β hβ ρ hρ N hN ν,
    ← EReal.coe_ennreal_toReal hKL, ← EReal.coe_sub, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hE
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hh := mul_le_mul_of_nonneg_right hE hbr.le
  have hl : (((klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal -
      Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) * (β * (N : ℝ))⁻¹) *
        (β * (N : ℝ)) =
      (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal -
      Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
    field_simp [hbr.ne']
  have hr : (A * (-Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) / (β * (N : ℝ))) +
      B / (N : ℝ)) * (β * (N : ℝ)) =
      -A * Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ₀ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) + β * B := by
    field_simp [hβ.ne', hn.ne'] <;> ring
  rw [hl, hr] at hh
  exact ⟨hKL, by linarith⟩

/-- The doubled partition integral from the printed bound `K_{N,2β} ≤ C₂`. -/
lemma periodicRiesz_partition_integral_le (s γ : ℝ) (hs : 0 < s) (hγ : 0 ≤ γ)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (C : ℝ)
    (h : (periodicRieszSingularPartition s γ hs2 ρ N).toReal ≤ C) :
    (∫ ω, Real.exp (periodicRieszParticleExponent s ρ γ N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  rwa [periodicRieszSingularPartition_toReal_eq s γ hs hγ hs2 ρ M hM hρ N hN] at h

/-- Common entropy constant `H = β Bmax + |log Cpart|`. -/
theorem periodicRieszDynamic_common_entropy (s β M Bmax Cpart : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∀ (ρ₀ ρ : PeriodicTorus ι → ℝ)
      [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
      [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν], ∀ A B : ℝ, 0 ≤ A → B ≤ Bmax →
      (periodicRieszSingularPartition s β hs2 ρ N).toReal ≤ Cpart →
      periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν ≤
        (A : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 ρ₀ M β N
          (periodicRieszSingularGibbs s β hs2 ρ₀ N) + (B / (N : ℝ) : ℝ) →
      klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ ∧
      (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal ≤ H := by
  refine ⟨β * Bmax + |Real.log Cpart|, add_nonneg (mul_nonneg hβ.le hBmax) (abs_nonneg _), ?_⟩
  intro N hN ρ₀ ρ hμ₀ hμ hρ₀ hρ ν hν A B hA hB hCp hE
  obtain ⟨hKL, hb⟩ := periodicRieszDynamic_entropy_from_gronwall s β M hs hβ hs2 hM ρ₀ ρ hρ₀ hρ N hN
    ν A B hE
  obtain ⟨_, _, hP₀⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ₀ M hM hρ₀
  have hlog₀ : 0 ≤ Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) :=
    Real.log_nonneg (hP₀ N hN).2.1
  obtain ⟨_, _, hP⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hp : 0 < (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by linarith [(hP N hN).2.1]
  have hlog := Real.log_le_log hp (periodicRiesz_partition_integral_le s β hs hβ.le hs2 ρ M hM hρ N hN
    Cpart hCp)
  have hB' := mul_le_mul_of_nonneg_left hB hβ.le
  exact ⟨hKL, by nlinarith [mul_nonneg hA hlog₀, le_abs_self (Real.log Cpart)]⟩

/-- The common Gibbs exponential moments of the transport energy, with constants chosen from the
printed partition bound `K_{N,2β} ≤ C₂` only. -/
theorem periodicRieszDynamic_gibbs_moments (s β M C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (K : ℝ≥0) :
    let ε := periodicRieszPositiveTransportParameter s hs2 M 1 K β
    let Cem := periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
      glzUniversalTailConstant (1 + max C₂ 0)
    0 < ε ∧ 1 ≤ Cem ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicRieszSingularPartition s (2 * β) hs2 ρ N).toReal ≤ C₂) →
      ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (σ * ε * (N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω))
          (periodicRieszSingularGibbs s β hs2 ρ N) ∧
        (∫ ω, Real.exp (σ * ε * (N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω)
          ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ Cem := by
  intro ε Cem
  have hε : 0 < ε := periodicRieszPositiveTransportParameter_pos s hs hs2 M hM 1 K β hβ
  have hCub1 : 1 ≤ 1 + max C₂ 0 := by linarith [le_max_right C₂ 0]
  have hCem1 : 1 ≤ Cem := one_le_periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
    glzUniversalTailConstant (1 + max C₂ 0) glzUniversalTailConstant_pos.le hCub1
  refine ⟨hε, hCem1, ?_⟩
  intro v hv ρ hprob hρ hC₂
  have hβloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  obtain ⟨_, _, hP₂⟩ := periodicRieszParticleWeight_uniform s (2 * β) hs (by positivity) hs2 ρ M hM hρ
  obtain ⟨_, _, hP₁⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hCubfam : periodicRieszLocalBeta s hs2 M < β → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ
        (2 * β - periodicRieszLocalBeta s hs2 M) N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszParticleExponent s ρ (2 * β - periodicRieszLocalBeta s hs2 M) N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ 1 + max C₂ 0 := by
    intro hlarge N hN
    have hn' : 0 < N := by omega
    have hpt (ω : Fin N → PeriodicTorus ι) :
        Real.exp (periodicRieszParticleExponent s ρ (2 * β - periodicRieszLocalBeta s hs2 M) N ω) ≤
          1 + Real.exp (periodicRieszParticleExponent s ρ (2 * β) N ω) := by
      rw [periodicRieszParticleExponent_background, periodicRieszParticleExponent_background]
      have h := exp_mul_le_one_add_exp_mul (a := 2 * β - periodicRieszLocalBeta s hs2 M) (b := 2 * β)
        (by linarith) (by linarith) (-(periodicRieszTransportBackgroundEnergy s ρ N ω))
      simpa only [mul_neg, neg_mul] using h
    have hint : Integrable (fun ω => 1 + Real.exp (periodicRieszParticleExponent s ρ (2 * β) N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
      (integrable_const 1).add (hP₂ N hN).1
    have hmeas := measurable_periodicRieszParticleExponent s hs hs2 ρ
      (2 * β - periodicRieszLocalBeta s hs2 M) N hn'
    have hi : Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ
        (2 * β - periodicRieszLocalBeta s hs2 M) N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
      hint.mono' (Real.measurable_exp.comp hmeas).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact hpt ω)
    refine ⟨hi, ?_⟩
    calc _ ≤ ∫ ω, (1 + Real.exp (periodicRieszParticleExponent s ρ (2 * β) N ω))
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) :=
          integral_mono hi hint hpt
      _ = 1 + ∫ ω, Real.exp (periodicRieszParticleExponent s ρ (2 * β) N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
          rw [integral_add (integrable_const 1) (hP₂ N hN).1]
          simp
      _ ≤ 1 + max C₂ 0 := by
          have := periodicRiesz_partition_integral_le s (2 * β) hs (by positivity) hs2 ρ M hM hρ N hN
            C₂ (hC₂ N hN)
          linarith [le_max_left C₂ 0]
  have hNum := periodicRieszTransport_numerator_explicit s M 1 le_rfl hs hs2 hM β hβ (1 + max C₂ 0)
    hv ρ hρ hCubfam
  exact periodicRieszTransport_Gibbs_moment_of_numerator_lower s M 1 le_rfl hs hs2 hM β hβ
    Cem 1 Cem hCem1 one_pos (by linarith) hv ρ hρ hNum (fun N hN => (hP₁ N hN).2.1)

/-- Lemma 8.1(ii): absolute commutator expectation under finite relative entropy. -/
theorem periodicRieszDynamic_common_commutator (s β M C₂ H : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (K : ℝ≥0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicRieszSingularPartition s (2 * β) hs2 ρ N).toReal ≤ C₂) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ →
      (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal ≤ H →
      Integrable (periodicRieszTransportEnergy s 1 v ρ N) ν ∧
      (∫ ω, |periodicRieszTransportEnergy s 1 v ρ N ω| ∂ν) ≤ D / (N : ℝ) := by
  obtain ⟨hε, hCem1, hmom⟩ := periodicRieszDynamic_gibbs_moments s β M C₂ hs hβ hs2 hM K
  let ε := periodicRieszPositiveTransportParameter s hs2 M 1 K β
  let Cem := periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M)
    glzUniversalTailConstant (1 + max C₂ 0)
  refine ⟨max (ε⁻¹ * (H + Real.log (2 * Cem))) 0, le_max_right _ _, ?_⟩
  intro v hv ρ hprob hρ hC₂ N hN ν hν hKL hH
  haveI := periodicRieszSingularGibbs_probability s β hs hβ.le hs2 ρ M hM hρ N
  have hp := hmom hv ρ hρ hC₂ 1 (by norm_num) N hN
  have hm := hmom hv ρ hρ hC₂ (-1) (by norm_num) N hN
  have hp' : Integrable (fun ω => Real.exp (ε * ((N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω)))
      (periodicRieszSingularGibbs s β hs2 ρ N) := by
    simpa only [one_mul, mul_assoc] using hp.1
  have hm' : Integrable (fun ω => Real.exp (-(ε * ((N : ℝ) *
      periodicRieszTransportEnergy s 1 v ρ N ω)))) (periodicRieszSingularGibbs s β hs2 ρ N) := by
    simpa only [neg_one_mul, neg_mul, mul_assoc, one_mul] using hm.1
  have hbP : (∫ ω, Real.exp (ε * ((N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω))
      ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ Cem := by
    simpa only [one_mul, mul_assoc] using hp.2
  have hbM : (∫ ω, Real.exp (-(ε * ((N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω)))
      ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ Cem := by
    simpa only [neg_one_mul, neg_mul, mul_assoc, one_mul] using hm.2
  exact dynCommutator_absolute_of_moments (periodicRieszSingularGibbs s β hs2 ρ N) ν N hN
    (periodicRieszTransportEnergy s 1 v ρ N)
    (measurable_periodicRieszScaledTransportEnergy s 1 le_rfl hs hs2 hv ρ N hN).stronglyMeasurable
    ε hε hp' hm' hKL H hH Cem hbP hbM

/-- Lemma 8.1(iii): absolute empirical fluctuation of an oscillation-bounded test. -/
theorem periodicRieszDynamic_common_oscillation (s β M C₂ H L : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      (periodicRieszSingularPartition s (2 * β) hs2 ρ N).toReal ≤ C₂ →
      ∀ (q : PeriodicTorus ι → ℝ), Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
      sSup (Set.range q) - sInf (Set.range q) ≤ L →
      ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ →
      (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal ≤ H →
      Integrable q (periodicCappedDensityMeasure ρ) ∧
      (∀ ω, Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
      Integrable (dynRawFluctuation (periodicCappedDensityMeasure ρ) q N) ν ∧
      Integrable (dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N ω| ∂ν) ≤ D / Real.sqrt N := by
  let D := max (H + Real.log (2 * (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / 1))) 0
  refine ⟨D, le_max_right _ _, ?_⟩
  intro ρ hprob hρ N hN hC₂ q hq hlo hup hosc ν hν hKL hH
  have hqb : ∀ x, q x ∈ Set.Icc (sInf (Set.range q)) (sSup (Set.range q)) :=
    fun x => subset_Icc_csInf_csSup hlo hup (Set.mem_range_self x)
  have hwidth : ‖sSup (Set.range q) - sInf (Set.range q)‖ ≤ L := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr
      (csInf_le_csSup (Set.range_nonempty q) hlo hup))]
    exact hosc
  have hab : ∀ x, |q x| ≤ max |sInf (Set.range q)| |sSup (Set.range q)| := by
    intro x
    rw [abs_le]
    constructor
    · have := (hqb x).1
      have := le_max_left |sInf (Set.range q)| |sSup (Set.range q)|
      have := neg_abs_le (sInf (Set.range q))
      linarith
    · exact ((hqb x).2.trans (le_abs_self _)).trans (le_max_right _ _)
  have hiq : Integrable q (periodicCappedDensityMeasure ρ) :=
    (integrable_const (max |sInf (Set.range q)| |sSup (Set.range q)|)).mono' hq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hab x)
  obtain ⟨_, _, hP₂⟩ := periodicRieszParticleWeight_uniform s (2 * β) hs (by positivity) hs2 ρ M hM hρ
  obtain ⟨_, _, hP₁⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hn' : 0 < N := by omega
  have hu : Measurable (periodicRieszParticleExponent s ρ β N) :=
    measurable_periodicRieszParticleExponent s hs hs2 ρ β N hn'
  have h2 (ω : Fin N → PeriodicTorus ι) :
      2 * periodicRieszParticleExponent s ρ β N ω = periodicRieszParticleExponent s ρ (2 * β) N ω := by
    unfold periodicRieszParticleExponent
    ring
  have hu2 : Integrable (fun ω => Real.exp (2 * periodicRieszParticleExponent s ρ β N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
    simpa only [h2] using (hP₂ N hN).1
  have hC₂' : (∫ ω, Real.exp (2 * periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C₂ := by
    simp_rw [h2]
    exact periodicRiesz_partition_integral_le s (2 * β) hs (by positivity) hs2 ρ M hM hρ N hN C₂ hC₂
  have hGibbs := periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN
  rw [hGibbs] at hKL hH
  obtain ⟨hr, he, hb⟩ := dynEmpirical_absolute_bound (periodicCappedDensityMeasure ρ) N hN
    (periodicRieszParticleExponent s ρ β N) hu (hP₁ N hN).1 hu2 1 C₂ one_pos (hP₁ N hN).2.1 hC₂' q hq
    (sInf (Set.range q)) (sSup (Set.range q)) hqb L hwidth ν hKL H hH
  exact ⟨hiq, fun ω => integrable_sourceRieszLocalEmpiricalLaw N ω q, hr, he, hb⟩

/-- Lemma 8.1 (i)-(iii) on the torus, Riesz branch.  The partition bounds (ii) are the printed
`N`-uniform ones. -/
theorem periodicRieszDynamic_entropy_transfers (s β M Bmax L Cpart C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax) (hL : 0 ≤ L) (K : ℝ≥0) :
    ∃ H Dc Dl : ℝ, 0 ≤ H ∧ 0 ≤ Dc ∧ 0 ≤ Dl ∧ ∀ (ρ₀ ρ : PeriodicTorus ι → ℝ),
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
        [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicRieszSingularPartition s β hs2 ρ N).toReal ≤ Cpart) →
      (∀ N : ℕ, 1 ≤ N → (periodicRieszSingularPartition s (2 * β) hs2 ρ N).toReal ≤ C₂) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      ∀ A B : ℝ, 0 ≤ A → B ≤ Bmax →
      periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν ≤
        (A : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 ρ₀ M β N
          (periodicRieszSingularGibbs s β hs2 ρ₀ N) + (B / (N : ℝ) : ℝ) →
      klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞ ∧
      (klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N)).toReal ≤ H ∧
      ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) ∧
      Integrable (periodicRieszTransportBackgroundEnergy s ρ N) ν ∧
      Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν ∧
      periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν =
        (periodicRieszTransportProperFreeEnergy s ρ β N ν : ℝ) ∧
      (∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
        Integrable (periodicRieszTransportEnergy s 1 v ρ N) ν ∧
        (∫ ω, |periodicRieszTransportEnergy s 1 v ρ N ω| ∂ν) ≤ Dc / (N : ℝ)) ∧
      ∀ (q : PeriodicTorus ι → ℝ), Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
        sSup (Set.range q) - sInf (Set.range q) ≤ L →
        Integrable q (periodicCappedDensityMeasure ρ) ∧
        (∀ ω, Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
        Integrable (dynRawFluctuation (periodicCappedDensityMeasure ρ) q N) ν ∧
        Integrable (dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N) ν ∧
        (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N ω| ∂ν) ≤
          Dl / Real.sqrt N := by
  obtain ⟨H, hH, hentropy⟩ := periodicRieszDynamic_common_entropy (ι := ι) s β M Bmax Cpart hs hβ hs2
    hM hBmax
  obtain ⟨Dc, hDc, hcomm⟩ := periodicRieszDynamic_common_commutator (ι := ι) s β M C₂ H hs hβ hs2 hM K
  obtain ⟨Dl, hDl, hlinear⟩ := periodicRieszDynamic_common_oscillation (ι := ι) s β M C₂ H L hs hβ
    hs2 hM hL
  refine ⟨H, Dc, Dl, hH, hDc, hDl, ?_⟩
  intro ρ₀ ρ hμ₀ hμ hρ₀ hρ hCp hC₂ N hN ν hν A B hA hB hE
  obtain ⟨hKL, hHb⟩ := hentropy N hN ρ₀ ρ hρ₀ hρ ν A B hA hB (hCp N hN) hE
  have hv0 : LipschitzWith 0 (fun _ : PeriodicTorus ι => (0 : E)) := by intro x y; simp
  obtain ⟨hε, hCem1, hmom⟩ := periodicRieszDynamic_gibbs_moments s β M C₂ hs hβ hs2 hM 0
  obtain ⟨hac, hbg, hllr, -, -⟩ := periodicRieszTransport_finiteKL_entropic_of_moments s M 1 le_rfl hs
    hs2 hM β hβ Cpart _ hv0 ρ hρ (hmom hv0 ρ hρ hC₂)
    (fun N' hN' => periodicRiesz_partition_integral_le s β hs hβ.le hs2 ρ M hM hρ N' hN' Cpart
      (hCp N' hN')) N hN ν hKL
  have heq := periodicRieszTransportExtendedFreeEnergy_eq_proper s hs hs2 M hM β hβ ρ hρ N hN ν hac hbg
    hllr
  refine ⟨hKL, hHb, hac, hbg, hllr, heq, ?_, ?_⟩
  · intro v hv
    exact hcomm hv ρ hρ hC₂ N hN ν hKL hHb
  · intro q hq hlo hup hosc
    exact hlinear ρ hρ N hN (hC₂ N hN) q hq hlo hup hosc ν hKL hHb

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszDynamic_initial_Gibbs_objective
#print axioms DGRHS.Periodic.periodicRieszDynamic_entropy_from_gronwall
#print axioms DGRHS.Periodic.periodicRieszDynamic_common_entropy
#print axioms DGRHS.Periodic.periodicRieszDynamic_gibbs_moments
#print axioms DGRHS.Periodic.periodicRieszDynamic_common_commutator
#print axioms DGRHS.Periodic.periodicRieszDynamic_common_oscillation
#print axioms DGRHS.Periodic.periodicRieszDynamic_entropy_transfers
