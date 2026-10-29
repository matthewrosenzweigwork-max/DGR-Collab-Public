import DGRHS.Gaussian.PeriodicRieszEntropicCommutator

/-!
Packet P9h, unit 2 (part 31, final): Theorem 2.8 (`thm:entropicCommutator`, TeX 691-736) on the flat
torus (Remark 2.1, TeX 492-496), Riesz branch `0 < s < d/2`, with the printed constants of Remark A.1
(`eq:CemLargeBetaDef`, rows 1 and 3, TeX 4144-4156):
`C_em = e + L` for `β ≤ β_loc` and `C_em = e^{-β I_μ} (e + L)^{1/2} C_ub(2β - β_loc, μ)^{1/2}` for
`β > β_loc`.

Torus version of `DGRHS.Commutator.exists_sourceRiesz_entropic_commutator_printed_constants`.
Quantifier order: the threshold `β_loc` is chosen first (it depends only on `d, s, M`), then `β`, then
the background density `ρ ≤ M`, and then the partition constants `C_ub`, `C_pf` (which, as in the printed
statement `C_pf(β, μ)`, `C_em(β, μ, v, n)`, may depend on `μ`), and finally the transport `v` with its
Lipschitz constant `K`; the transport parameter `ε` does not depend on `ρ`.
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Theorem 2.8 on the torus, Riesz branch, with the printed constants (`C_em` with `e^{-β I_μ}`). -/
theorem exists_periodicRiesz_entropic_commutator_printed_constants (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
        (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
          (periodicRieszSingularPartition s (2 * (β : ℝ) - βloc) hs2 ρ N).toReal ≤ Cub) ∧
      (∀ N : ℕ, 1 ≤ N →
          1 ≤ (periodicRieszSingularPartition s (β : ℝ) hs2 ρ N).toReal ∧
          (periodicRieszSingularPartition s (β : ℝ) hs2 ρ N).toReal ≤ Cpf) ∧
      ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      let ε := periodicRieszPositiveTransportParameter s hs2 M n K (β : ℝ)
      0 < ε ∧
      let Cem := periodicRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
      1 ≤ Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) *
          periodicRieszTransportEnergy s n v ρ N x)))
          (periodicRieszSingularGibbs s (β : ℝ) hs2 ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N x))
          ∂periodicRieszSingularGibbs s (β : ℝ) hs2 ρ N) ≤ Cem) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
        klDiv ν (periodicRieszSingularGibbs s (β : ℝ) hs2 ρ N) ≠ ∞ →
        (∃ e : ℝ, periodicRieszTransportExtendedFreeEnergy s hs2 ρ M (β : ℝ) N ν = (e : EReal)) ∧
        Integrable (fun x => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) ν ∧
        ((|∫ x, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N x ∂ν| : ℝ) : EReal) ≤
          (((β : ℝ) / ε) * (N : ℝ) : ℝ) *
              periodicRieszTransportExtendedFreeEnergy s hs2 ρ M (β : ℝ) N ν +
            (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  refine ⟨periodicRieszLocalBeta s hs2 M, hloc, ?_⟩
  intro β hβ ρ hprob hρ
  have hβ' : 0 < (β : ℝ) := hβ
  obtain ⟨Cub, hCub1, hCubfam⟩ : ∃ Cub : ℝ, 1 ≤ Cub ∧
      (periodicRieszLocalBeta s hs2 M < (β : ℝ) → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ
          (2 * (β : ℝ) - periodicRieszLocalBeta s hs2 M) N ω))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ ω, Real.exp (periodicRieszParticleExponent s ρ
          (2 * (β : ℝ) - periodicRieszLocalBeta s hs2 M) N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cub) := by
    by_cases hlarge : periodicRieszLocalBeta s hs2 M < (β : ℝ)
    · obtain ⟨Cp1, hCp1, hP1⟩ := periodicRieszParticleWeight_uniform s
        (2 * (β : ℝ) - periodicRieszLocalBeta s hs2 M) hs (by linarith) hs2 ρ M hM hρ
      refine ⟨max Cp1 1, le_max_right _ _, fun _ N hN => ?_⟩
      have h := hP1 N hN
      exact ⟨h.1, h.2.2.trans (le_max_left _ _)⟩
    · exact ⟨1, le_rfl, fun h => absurd h hlarge⟩
  obtain ⟨Cp, hCp, hPf⟩ := periodicRieszParticleWeight_uniform s (β : ℝ) hs hβ'.le hs2 ρ M hM hρ
  refine ⟨Cub, max Cp 1, hCub1, le_max_right _ _, ?_, ?_, ?_⟩
  · intro N hN hlarge
    rw [periodicRieszSingularPartition_toReal_eq s _ hs (by linarith) hs2 ρ M hM hρ N hN]
    exact (hCubfam hlarge N hN).2
  · intro N hN
    rw [periodicRieszSingularPartition_toReal_eq s _ hs hβ'.le hs2 ρ M hM hρ N hN]
    have h := hPf N hN
    exact ⟨h.2.1, h.2.2.trans (le_max_left _ _)⟩
  · intro K v hv
    dsimp only
    have hε := periodicRieszPositiveTransportParameter_pos s hs hs2 M hM n K (β : ℝ) hβ'
    refine ⟨hε, ?_⟩
    have hNum := periodicRieszTransport_numerator_explicit s M n hn1 hs hs2 hM (β : ℝ) hβ' Cub
      hv ρ hρ (fun hl N hN => hCubfam hl N hN)
    have hCnum1 := one_le_periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
      glzUniversalTailConstant Cub glzUniversalTailConstant_pos.le hCub1
    set I := DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) with hI
    set Cem := periodicRieszPrintedCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
      glzUniversalTailConstant Cub I with hCemdef
    -- the partition lower bound and the division constant
    obtain ⟨Zlow, hZpos, hZlow, hdiv⟩ : ∃ Zlow : ℝ, 0 < Zlow ∧
        (∀ N : ℕ, 1 ≤ N → Zlow ≤ (∫ ω, Real.exp (periodicRieszParticleExponent s ρ (β : ℝ) N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ∧
        periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
          glzUniversalTailConstant Cub ≤ Cem * Zlow := by
      by_cases hsmall : (β : ℝ) ≤ periodicRieszLocalBeta s hs2 M
      · refine ⟨1, one_pos, fun N hN => (hPf N hN).2.1, ?_⟩
        have : Cem = periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
            glzUniversalTailConstant Cub := by
          rw [hCemdef]
          unfold periodicRieszPrintedCem periodicRieszTransportCem
          rw [ite_eq_left hsmall, ite_eq_left hsmall]
        rw [this, mul_one]
      · refine ⟨Real.exp ((β : ℝ) * I), Real.exp_pos _,
          fun N hN => periodicRieszJensen_lower_integral s (β : ℝ) hs hβ'.le hs2 ρ M hM hρ N hN, ?_⟩
        have : Cem = Real.exp (-((β : ℝ) * I)) *
            periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
              glzUniversalTailConstant Cub := by
          rw [hCemdef]
          unfold periodicRieszPrintedCem periodicRieszTransportCem
          rw [ite_eq_right hsmall, ite_eq_right hsmall]
        rw [this]
        have hmul : Real.exp (-((β : ℝ) * I)) * Real.exp ((β : ℝ) * I) = 1 := by
          rw [← Real.exp_add]; simp
        calc periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
              glzUniversalTailConstant Cub
            = (Real.exp (-((β : ℝ) * I)) * Real.exp ((β : ℝ) * I)) *
              periodicRieszTransportCem (β : ℝ) (periodicRieszLocalBeta s hs2 M)
                glzUniversalTailConstant Cub := by rw [hmul, one_mul]
          _ = _ := by ring
          _ ≤ _ := le_rfl
    -- 1 ≤ Cem from the numerator bound at σ = 0 (the partition function itself)
    have hCem1 : 1 ≤ Cem := by
      have h0 := (hNum 0 (by simp) 1 le_rfl).2
      have hz : (fun ω : Fin 1 → PeriodicTorus ι => Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n
          (β : ℝ) 0 K v ρ 1 ω)) = fun ω => Real.exp (periodicRieszParticleExponent s ρ (β : ℝ) 1 ω) := by
        funext ω
        simp [periodicRieszTransportAllBetaExponent]
      rw [hz] at h0
      have h1 := hZlow 1 le_rfl
      have h2 : Zlow * 1 ≤ Zlow * Cem := by
        calc Zlow * 1 = Zlow := mul_one _
          _ ≤ _ := h1
          _ ≤ _ := h0
          _ ≤ Cem * Zlow := hdiv
          _ = Zlow * Cem := mul_comm _ _
      exact le_of_mul_le_mul_left h2 hZpos
    have hlog : 0 ≤ Real.log (max Cp 1) + Real.log Cem := by
      have h1 := Real.log_nonneg (le_max_right Cp 1)
      have h2 := Real.log_nonneg hCem1
      linarith
    have hMom := periodicRieszTransport_Gibbs_moment_of_numerator_lower s M n hn1 hs hs2 hM (β : ℝ) hβ'
      _ Zlow Cem hCem1 hZpos hdiv hv ρ hρ hNum hZlow
    refine ⟨hCem1, hlog, ?_, ?_⟩
    · intro σ hσ N hN
      have h := hMom σ (le_of_eq hσ) N hN
      simpa only [mul_assoc] using h
    · intro N hN ν hν hKL
      obtain ⟨hac, hbg, hllr, ha, hb⟩ := periodicRieszTransport_finiteKL_entropic_of_moments s M n
        hn1 hs hs2 hM (β : ℝ) hβ' (max Cp 1) Cem hv ρ hρ hMom
        (fun N hN => (hPf N hN).2.2.trans (le_max_left _ _)) N hN ν hKL
      have hext := periodicRieszTransportExtendedFreeEnergy_eq_proper s hs hs2 M hM (β : ℝ) hβ' ρ hρ
        N hN ν hac hbg hllr
      refine ⟨⟨_, hext⟩, ha, ?_⟩
      rw [hext, ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_le_coe_iff.mpr hb

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicRiesz_entropic_commutator_printed_constants
