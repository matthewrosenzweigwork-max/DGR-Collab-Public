import DGRHS.Gaussian.PeriodicLogDynamicMoments

/-!
Packet P11c, unit 2 (LOG): Lemma 8.1 (`lem:dynamicEntropyTransfers`, TeX 3771-3794) on the flat torus
(Remark 2.1, TeX 492-496), logarithmic branch `s = 0`.

Torus form of `DGRHS.Dynamics.exists_sourceLog_dynamic_entropy_transfers`.  The printed lemma assumes
the hypotheses of Theorem 2.13: the uniform background and partition bounds
(`sup_t ‖μ^t‖_∞ ≤ M`, `A^t ≤ Amax`, `B^t ≤ Bmax`, `K_{N,β}(μ^t) ≤ Cpart`, `K_{N,2β}(μ^t) ≤ C₂`, the
`N`-uniform bounds of TeX 877-881).  On the torus the pair-log integrability and the lower bound
`I_{μ^t} ≥ -J` of `eq:dynamicUniformLogEnergy` are theorems (the periodic LOG kernel is bounded below,
`periodicLogInteraction_lower`), and the lower partition bound `K_{N,β}(ρ₀) ≥ c` holds with the explicit
`c = exp(-β J₀)`, `J₀ = periodicLogPairLower/2`, by Jensen; so neither `J` nor `c` is a hypothesis.
The three constants `H, Dc, Dl` are chosen before `N`, both densities, the law, the velocity, the test
and the Gronwall coefficients.  The Lipschitz constant `K` of the transport is positive, as in the
Euclidean LOG export (a constant velocity is covered by any positive `K`).
-/

noncomputable section
open MeasureTheory InformationTheory Set
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The extended free energy of the literal initial Gibbs law is `-log K_{N,β}/(βN)`. -/
lemma periodicLogDynamic_initial_Gibbs_objective (β M : ℝ) (hβ : 0 < β) (hM : 0 ≤ M)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    periodicLogTransportExtendedFreeEnergy ρ M β N (periodicLogSingularGibbs β ρ N) =
      (-Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) / (β * (N : ℝ)) : ℝ) := by
  have hprob := periodicLogSingularGibbs_probability β hβ.le ρ M hM hρ N
  rw [periodicLogTransportExtendedFreeEnergy_rewrite M hM β hβ ρ hρ N hN]
  simp [div_eq_mul_inv]

/-- Entropy from the Gronwall estimate (TeX 3797-3808). -/
theorem periodicLogDynamic_entropy_from_gronwall (β M : ℝ) (hβ : 0 < β) (hM : 0 ≤ M)
    (ρ₀ ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ₀ : ∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (A B : ℝ)
    (hE : periodicLogTransportExtendedFreeEnergy ρ M β N ν ≤
      (A : EReal) * periodicLogTransportExtendedFreeEnergy ρ₀ M β N
        (periodicLogSingularGibbs β ρ₀ N) + (B / (N : ℝ) : ℝ)) :
    klDiv ν (periodicLogSingularGibbs β ρ N) ≠ ∞ ∧
    (klDiv ν (periodicLogSingularGibbs β ρ N)).toReal ≤
      -A * Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ₀ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) + β * B +
        Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
  rw [periodicLogDynamic_initial_Gibbs_objective β M hβ hM ρ₀ hρ₀ N hN,
    ← EReal.coe_mul, ← EReal.coe_add] at hE
  have hbr : 0 < β * (N : ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0 < N))
  have hKL : klDiv ν (periodicLogSingularGibbs β ρ N) ≠ ∞ := by
    intro ht
    rw [periodicLogTransportExtendedFreeEnergy_rewrite M hM β hβ ρ hρ N hN ν,
      ht, EReal.coe_ennreal_top, EReal.top_sub_coe,
      EReal.top_mul_coe_of_pos (inv_pos.mpr hbr)] at hE
    exact EReal.coe_ne_top _ (top_le_iff.mp hE)
  rw [periodicLogTransportExtendedFreeEnergy_rewrite M hM β hβ ρ hρ N hN ν,
    ← EReal.coe_ennreal_toReal hKL, ← EReal.coe_sub, ← EReal.coe_mul,
    EReal.coe_le_coe_iff] at hE
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hh := mul_le_mul_of_nonneg_right hE hbr.le
  have hl : (((klDiv ν (periodicLogSingularGibbs β ρ N)).toReal -
      Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) * (β * (N : ℝ))⁻¹) *
        (β * (N : ℝ)) =
      (klDiv ν (periodicLogSingularGibbs β ρ N)).toReal -
      Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
    field_simp [hbr.ne']
  have hr : (A * (-Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) / (β * (N : ℝ))) +
      B / (N : ℝ)) * (β * (N : ℝ)) =
      -A * Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ₀ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) + β * B := by
    field_simp [hβ.ne', hn.ne'] <;> ring
  rw [hl, hr] at hh
  exact ⟨hKL, by linarith⟩

/-- The partition integral from the printed bound `K_{N,γ} ≤ C`. -/
lemma periodicLog_partition_integral_le (γ : ℝ) (hγ : 0 ≤ γ) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) (C : ℝ)
    (h : (periodicLogSingularPartition γ ρ N).toReal ≤ C) :
    (∫ ω, Real.exp (periodicLogParticleExponent ρ γ N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  rwa [periodicLogSingularPartition_toReal_eq γ hγ ρ M hM hρ N hN] at h

/-- Common entropy constant `H = Amax β J₀ + β Bmax + |log Cpart|`. -/
theorem periodicLogDynamic_common_entropy (β M Bmax Amax Cpart : ℝ) (hβ : 0 < β) (hM : 0 ≤ M)
    (hBmax : 0 ≤ Bmax) (hAmax : 0 ≤ Amax) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ N : ℕ, 1 ≤ N → ∀ (ρ₀ ρ : PeriodicTorus ι → ℝ)
      [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
      [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν], ∀ A B : ℝ, 0 ≤ A → A ≤ Amax →
      B ≤ Bmax → (periodicLogSingularPartition β ρ N).toReal ≤ Cpart →
      periodicLogTransportExtendedFreeEnergy ρ M β N ν ≤
        (A : EReal) * periodicLogTransportExtendedFreeEnergy ρ₀ M β N
          (periodicLogSingularGibbs β ρ₀ N) + (B / (N : ℝ) : ℝ) →
      klDiv ν (periodicLogSingularGibbs β ρ N) ≠ ∞ ∧
      (klDiv ν (periodicLogSingularGibbs β ρ N)).toReal ≤ H := by
  have hJ := periodicLogPairLower_nonneg (ι := ι)
  refine ⟨Amax * (β * (periodicLogPairLower ι / 2)) + β * Bmax + |Real.log Cpart|,
    add_nonneg (add_nonneg (mul_nonneg hAmax (mul_nonneg hβ.le (by positivity)))
      (mul_nonneg hβ.le hBmax)) (abs_nonneg _), ?_⟩
  intro N hN ρ₀ ρ hμ₀ hμ hρ₀ hρ ν hν A B hA hAA hB hCp hE
  obtain ⟨hKL, hb⟩ := periodicLogDynamic_entropy_from_gronwall β M hβ hM ρ₀ ρ hρ₀ hρ N hN ν A B hE
  have hlow₀ := periodicLog_partition_ge β hβ.le ρ₀ M hM hρ₀ N hN
  have hpos₀ : 0 < ∫ ω, Real.exp (periodicLogParticleExponent ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀) :=
    lt_of_lt_of_le (Real.exp_pos _) hlow₀
  have hlog₀ : -(β * (periodicLogPairLower ι / 2)) ≤ Real.log (∫ ω, Real.exp
      (periodicLogParticleExponent ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) := by
    have := Real.log_le_log (Real.exp_pos _) hlow₀
    rwa [Real.log_exp] at this
  have hpos := lt_of_lt_of_le (Real.exp_pos _) (periodicLog_partition_ge β hβ.le ρ M hM hρ N hN)
  have hlog := Real.log_le_log hpos (periodicLog_partition_integral_le β hβ.le ρ M hM hρ N hN Cpart hCp)
  have h1 : -A * Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ₀ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ₀)) ≤
      Amax * (β * (periodicLogPairLower ι / 2)) := by
    calc _ ≤ -A * (-(β * (periodicLogPairLower ι / 2))) :=
          mul_le_mul_of_nonpos_left hlog₀ (by linarith)
      _ = A * (β * (periodicLogPairLower ι / 2)) := by ring
      _ ≤ Amax * (β * (periodicLogPairLower ι / 2)) :=
          mul_le_mul_of_nonneg_right hAA (mul_nonneg hβ.le (by positivity))
  have h2 := mul_le_mul_of_nonneg_left hB hβ.le
  exact ⟨hKL, by linarith [le_abs_self (Real.log Cpart)]⟩

/-- Lemma 8.1(ii): absolute commutator expectation under finite relative entropy. -/
theorem periodicLogDynamic_common_commutator (β : ℝ) (hβ : 0 < β) (K : ℝ≥0) (hK : 0 < (K : ℝ))
    (M Cpart C₂ H : ℝ) (hM : 0 ≤ M) (hCpart : 0 < Cpart) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition β ρ N).toReal ≤ Cpart) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition (2 * β) ρ N).toReal ≤ C₂) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      klDiv ν (periodicLogSingularGibbs β ρ N) ≠ ∞ →
      (klDiv ν (periodicLogSingularGibbs β ρ N)).toReal ≤ H →
      Integrable (sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicLogTransportKernel 1 v) N) ν ∧
      (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicLogTransportKernel 1 v) N ω| ∂ν) ≤ D / (N : ℝ) := by
  obtain ⟨Csr, hCsr, hfam⟩ := periodicLog_capped_gibbs_moments (ι := ι) 1 le_rfl
  let ε := periodicLogFamilyBeta β Cpart / (8 * Csr * (K : ℝ) ^ 1)
  have hε : 0 < ε := by
    have := periodicLogFamilyBeta_pos hβ hCpart
    unfold ε
    positivity
  let Cem := Real.exp (β * (periodicLogPairLower ι / 2)) *
    (Real.sqrt (Real.exp 1) * Real.sqrt (1 + max C₂ 0))
  refine ⟨max (ε⁻¹ * (H + Real.log (2 * Cem))) 0, le_max_right _ _, ?_⟩
  intro v hv ρ hprob hρ hCp hC₂ N hN ν hν hKL hH
  haveI hQ := periodicLogSingularGibbs_probability β hβ.le ρ M hM hρ N
  let μ := periodicCappedDensityMeasure ρ
  have hm := periodicLogTransportKernel_measurable (ι := ι) 1 hv
  have hsa : StronglyMeasurable (fun x : Fin N → PeriodicTorus ι => (N : ℝ) *
      sourceTransportEnergy μ (periodicLogTransportKernel 1 v) N x) :=
    (stronglyMeasurable_sourceTransportEnergy μ _ hm N).const_mul (N : ℝ)
  have hp := hfam hv hK β Cpart C₂ M hβ hCpart hM ρ hρ hCp hC₂ 1 (by norm_num) N hN
  have hmn := hfam hv hK β Cpart C₂ M hβ hCpart hM ρ hρ hCp hC₂ (-1) (by norm_num) N hN
  have hp' : Integrable (fun x => Real.exp (ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel 1 v) N x))) (periodicLogSingularGibbs β ρ N) := by
    simpa only [one_mul] using hp.1
  have hm' : Integrable (fun x => Real.exp (-(ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel 1 v) N x)))) (periodicLogSingularGibbs β ρ N) := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hmn.1
  have hbP : (∫ x, Real.exp (ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel 1 v) N x)) ∂periodicLogSingularGibbs β ρ N) ≤ Cem := by
    simpa only [one_mul] using hp.2
  have hbM : (∫ x, Real.exp (-(ε * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel 1 v) N x))) ∂periodicLogSingularGibbs β ρ N) ≤ Cem := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hmn.2
  exact dynCommutator_absolute_of_moments (periodicLogSingularGibbs β ρ N) ν N hN
    (sourceTransportEnergy μ (periodicLogTransportKernel 1 v) N) hsa ε hε hp' hm' hKL H hH Cem hbP hbM

/-- Lemma 8.1(iii): absolute empirical fluctuation of an oscillation-bounded test. -/
theorem periodicLogDynamic_common_oscillation (β C₂ M H L : ℝ) (hβ : 0 < β) (hM : 0 ≤ M)
    (hL : 0 ≤ L) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
      (periodicLogSingularPartition (2 * β) ρ N).toReal ≤ C₂ →
      ∀ (q : PeriodicTorus ι → ℝ), Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
      sSup (Set.range q) - sInf (Set.range q) ≤ L →
      ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      klDiv ν (periodicLogSingularGibbs β ρ N) ≠ ∞ →
      (klDiv ν (periodicLogSingularGibbs β ρ N)).toReal ≤ H →
      Integrable q (periodicCappedDensityMeasure ρ) ∧
      (∀ ω, Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
      Integrable (dynRawFluctuation (periodicCappedDensityMeasure ρ) q N) ν ∧
      Integrable (dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N) ν ∧
      (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N ω| ∂ν) ≤ D / Real.sqrt N := by
  let Zlow := Real.exp (-(β * (periodicLogPairLower ι / 2)))
  let D := max (H + Real.log (2 * (Real.sqrt (Real.exp (L ^ 2 / 2)) * Real.sqrt C₂ / Zlow))) 0
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
  obtain ⟨_, _, hP₂⟩ := periodicLogParticleWeight_uniform (2 * β) (by positivity) ρ M hM hρ
  obtain ⟨_, _, hP₁⟩ := periodicLogParticleWeight_uniform β hβ.le ρ M hM hρ
  have hn' : 0 < N := by omega
  have hu : Measurable (periodicLogParticleExponent ρ β N) :=
    measurable_periodicLogParticleExponent ρ β N hn'
  have h2 (ω : Fin N → PeriodicTorus ι) :
      2 * periodicLogParticleExponent ρ β N ω = periodicLogParticleExponent ρ (2 * β) N ω := by
    unfold periodicLogParticleExponent
    ring
  have hu2 : Integrable (fun ω => Real.exp (2 * periodicLogParticleExponent ρ β N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
    simpa only [h2] using (hP₂ N hN).1
  have hC₂' : (∫ ω, Real.exp (2 * periodicLogParticleExponent ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C₂ := by
    simp_rw [h2]
    exact periodicLog_partition_integral_le (2 * β) (by positivity) ρ M hM hρ N hN C₂ hC₂
  have hGibbs := periodicLogSingularGibbs_eq_particle β hβ.le ρ M hM hρ N hN
  rw [hGibbs] at hKL hH
  obtain ⟨hr, he, hb⟩ := dynEmpirical_absolute_bound (periodicCappedDensityMeasure ρ) N hN
    (periodicLogParticleExponent ρ β N) hu (hP₁ N hN).1 hu2 Zlow C₂ (Real.exp_pos _)
    (periodicLog_partition_ge β hβ.le ρ M hM hρ N hN) hC₂' q hq
    (sInf (Set.range q)) (sSup (Set.range q)) hqb L hwidth ν hKL H hH
  exact ⟨hiq, fun ω => integrable_sourceRieszLocalEmpiricalLaw N ω q, hr, he, hb⟩

/-- Lemma 8.1 (i)-(iii) on the torus, LOG branch. -/
theorem periodicLogDynamic_entropy_transfers (β : ℝ≥0) (hβ : 0 < (β : ℝ)) (K : ℝ≥0)
    (hK : 0 < (K : ℝ)) (M : ℝ) (hM : 0 ≤ M) (Cpart C₂ Amax Bmax L : ℝ) (hCpart : 0 < Cpart)
    (hAmax : 0 ≤ Amax) (hBmax : 0 ≤ Bmax) (hL : 0 ≤ L) :
    ∃ H Dc Dl : ℝ, 0 ≤ H ∧ 0 ≤ Dc ∧ 0 ≤ Dl ∧ ∀ (ρ₀ ρ : PeriodicTorus ι → ℝ),
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ₀)]
        [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ₀ x ≤ M) → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition (β : ℝ) ρ N).toReal ≤ Cpart) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition (2 * (β : ℝ)) ρ N).toReal ≤ C₂) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      ∀ A B : ℝ, 0 ≤ A → A ≤ Amax → B ≤ Bmax →
      periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν ≤
        (A : EReal) * periodicLogTransportExtendedFreeEnergy ρ₀ M (β : ℝ) N
          (periodicLogSingularGibbs (β : ℝ) ρ₀ N) + (B / (N : ℝ) : ℝ) →
      klDiv ν (periodicLogSingularGibbs (β : ℝ) ρ N) ≠ ∞ ∧
      (klDiv ν (periodicLogSingularGibbs (β : ℝ) ρ N)).toReal ≤ H ∧
      ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) ∧
      Integrable (periodicLogTransportBackgroundEnergy ρ N) ν ∧
      Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν ∧
      periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν =
        (periodicLogTransportProperFreeEnergy ρ (β : ℝ) N ν : ℝ) ∧
      (∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
        Integrable (sourceTransportEnergy (periodicCappedDensityMeasure ρ)
          (periodicLogTransportKernel 1 v) N) ν ∧
        (∫ ω, |sourceTransportEnergy (periodicCappedDensityMeasure ρ)
          (periodicLogTransportKernel 1 v) N ω| ∂ν) ≤ Dc / (N : ℝ)) ∧
      ∀ (q : PeriodicTorus ι → ℝ), Measurable q → BddBelow (Set.range q) → BddAbove (Set.range q) →
        sSup (Set.range q) - sInf (Set.range q) ≤ L →
        Integrable q (periodicCappedDensityMeasure ρ) ∧
        (∀ ω, Integrable q (sourceRieszLocalEmpiricalLaw N ω)) ∧
        Integrable (dynRawFluctuation (periodicCappedDensityMeasure ρ) q N) ν ∧
        Integrable (dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N) ν ∧
        (∫ ω, |dynEmpiricalDifference (periodicCappedDensityMeasure ρ) q N ω| ∂ν) ≤
          Dl / Real.sqrt N := by
  obtain ⟨H, hH, hentropy⟩ := periodicLogDynamic_common_entropy (ι := ι) (β : ℝ) M Bmax Amax Cpart
    hβ hM hBmax hAmax
  obtain ⟨Dc, hDc, hcomm⟩ := periodicLogDynamic_common_commutator (ι := ι) (β : ℝ) hβ K hK M Cpart C₂ H
    hM hCpart
  obtain ⟨Dl, hDl, hlinear⟩ := periodicLogDynamic_common_oscillation (ι := ι) (β : ℝ) C₂ M H L hβ hM hL
  refine ⟨H, Dc, Dl, hH, hDc, hDl, ?_⟩
  intro ρ₀ ρ hμ₀ hμ hρ₀ hρ hCp hC₂ N hN ν hν A B hA hAA hB hE
  obtain ⟨hKL, hHb⟩ := hentropy N hN ρ₀ ρ hρ₀ hρ ν A B hA hAA hB (hCp N hN) hE
  -- properness from finite Gibbs relative entropy
  obtain ⟨_, _, hP⟩ := periodicLogParticleWeight_uniform (β : ℝ) hβ.le ρ M hM hρ
  have hcap := periodicLogParticleExponent_cap M hM ρ hρ (β : ℝ) hβ N hN
  have hGibbs := periodicLogSingularGibbs_eq_particle (β : ℝ) hβ.le ρ M hM hρ N hN
  have hfin : klDiv ν ((Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
      (periodicLogParticleExponent ρ (β : ℝ) N)) ≠ ∞ := by
    rw [← hGibbs]; exact hKL
  obtain ⟨hac, hu, hllr⟩ := (gibbsKL_finite_domain
    (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ν
    (periodicLogParticleExponent ρ (β : ℝ) N) _ hcap (hP N hN).1).mp hfin
  have hbg : Integrable (periodicLogTransportBackgroundEnergy ρ N) ν := by
    have h := hu.const_mul (-(β : ℝ))⁻¹
    refine h.congr (ae_of_all _ fun ω => ?_)
    show (-(β : ℝ))⁻¹ * periodicLogParticleExponent ρ (β : ℝ) N ω =
      periodicLogTransportBackgroundEnergy ρ N ω
    rw [periodicLogParticleExponent_background]
    field_simp
  have heq := periodicLogTransportExtendedFreeEnergy_eq_proper M hM (β : ℝ) hβ ρ hρ N hN ν hac hbg hllr
  refine ⟨hKL, hHb, hac, hbg, hllr, heq, ?_, ?_⟩
  · intro v hv
    exact hcomm hv ρ hρ hCp hC₂ N hN ν hKL hHb
  · intro q hq hlo hup hosc
    exact hlinear ρ hρ N hN (hC₂ N hN) q hq hlo hup hosc ν hKL hHb

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogDynamic_initial_Gibbs_objective
#print axioms DGRHS.Periodic.periodicLogDynamic_entropy_from_gronwall
#print axioms DGRHS.Periodic.periodicLogDynamic_common_entropy
#print axioms DGRHS.Periodic.periodicLogDynamic_common_commutator
#print axioms DGRHS.Periodic.periodicLogDynamic_common_oscillation
#print axioms DGRHS.Periodic.periodicLogDynamic_entropy_transfers
