import DGRHS.Commutator.SourceT28FullRange
import DGRHS.Commutator.SourceRieszEntropicCommutatorPrinted

/-! Source Theorem 2.8, full range `0 ≤ s < d/2`, with the printed constants of Remark A.1
(`eq:CemLargeBetaDef`, TeX 4130-4156) exposed in the statement.

Same statement as `exists_source_entropic_commutator_full_range` (hypotheses, the
existential `ε Cpf Cem`, the exponential moments (2.21), the entropic inequality (2.22) and
the constants (2.23) are unchanged), with one additional conjunct that pins the witnesses to
the printed formulas:

* `s > 0`: `ε = sourceRieszPositiveTransportParameter` and
  `Cem = sourceRieszPrintedCem β βloc L Cub I_μ`, i.e. `e + L` for `β ≤ β_loc` and
  `e^{-β I_μ} (e+L)^{1/2} C_ub^{1/2}` for `β > β_loc`, with `C_ub` a cap on the partition
  function at `2β - β_loc` and `I_μ = interactionEnergy μ (‖x-y‖^{-s}/s)`;
* `s = 0`, `‖∇v‖ > 0`: `ε = sourceLogTransportEpsilon`,
  `Cem = sourceLogTransportCem β βloc I_μ L Cub`
  (`e^{-β I_μ}(e+L)` resp. `e^{-β I_μ}(e+L)^{1/2} C_ub^{1/2}`) with `I_μ` the log
  interaction energy;
* `s = 0`, Lipschitz constant `0`: `ε = 1`, `Cem = 1` (Remark A.1, `‖∇v‖ = 0`).

The existing full-range module and its statement are not modified. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Concentration
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Source Theorem 2.8 for `0 ≤ s < d/2` with the printed constants exposed (Remark A.1). -/
theorem exists_sourceT28_full_range_printed (n : ℕ) (hn : 0 < n) (s : ℝ)
    (hs : 0 ≤ s) (hd : 2 * s < (Fintype.card ι : ℝ))
    {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : s = 0 → Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ ε Cpf Cem : ℝ, 0 < ε ∧ 1 ≤ Cpf ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      (s = 0 →
        (K = 0 → ε = 1 ∧ Cem = 1) ∧
        (0 < (K : ℝ) → ∃ Csr Cub : ℝ, 0 < Csr ∧ 1 ≤ Cub ∧
          (∀ N : ℕ, 1 ≤ N → ∀ hlarge : βloc < (β : ℝ),
            (sourceLogSingularPartition
              (⟨2 * (β : ℝ) - βloc, by linarith [hlarge, β.coe_nonneg]⟩ : ℝ≥0) ρ N).toReal ≤
              Cub) ∧
          ε = sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) ∧
          Cem = sourceLogTransportCem (β : ℝ) βloc
            (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
              (fun a b => logPhysicalPair (a, b)))
            glzUniversalTailConstant Cub)) ∧
      (0 < s → ∃ Cub : ℝ, 1 ≤ Cub ∧
        (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
          (sourceRieszSingularPartition s (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
        ε = sourceRieszPositiveTransportParameter (ι := ι) s M n K (β : ℝ) ∧
        Cem = sourceRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
            (fun a b : E => gaussianRieszPhysicalPair s (a, b)))) ∧
      (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * ε * ((N : ℝ) * sourceT28Observable s n v ρ N x)))
          (sourceT28Gibbs s β ρ N) ∧
        (∫ x, Real.exp (σ * ε * ((N : ℝ) * sourceT28Observable s n v ρ N x))
          ∂sourceT28Gibbs s β ρ N) ≤ Cem) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → E)) [IsProbabilityMeasure ν],
        (s = 0 ∨ klDiv ν (sourceT28Gibbs s β ρ N) ≠ ∞) →
        Integrable (fun x => (N : ℝ) * sourceT28Observable s n v ρ N x) ν ∧
        ((|∫ x, (N : ℝ) * sourceT28Observable s n v ρ N x ∂ν| : ℝ) : EReal) ≤
          (((β : ℝ)/ε)*(N : ℝ) : ℝ) * sourceT28FreeEnergy s β ρ M N ν +
            (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) := by
  by_cases h0 : s = 0
  · subst h0
    have hd' : 0 < (Fintype.card ι : ℝ) := by linarith
    have hpair := hlog rfl
    by_cases hK : K = 0
    · subst hK
      refine ⟨1, one_pos, ?_⟩
      intro β hβ
      obtain ⟨Cpf, hCpf, hfam⟩ := sourceLog_entropic_commutator_zero (ι := ι) n hn hv β hβ hd' ρ M
        hM hρ hpair 1 one_pos
      refine ⟨1, Cpf, 1, one_pos, hCpf, one_pos, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Real.log_one, add_zero]
        exact Real.log_nonneg hCpf
      · exact fun _ => ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd h (by simp)⟩
      · exact fun h => absurd h (lt_irrefl _)
      · intro σ hσ N hN
        obtain ⟨hi, hI⟩ := (hfam N hN).1 σ
        simp only [sourceT28Observable_zero, sourceT28Gibbs_zero]
        exact ⟨hi, hI.le⟩
      · intro N hN ν hν _
        simp only [sourceT28Observable_zero, sourceT28FreeEnergy_zero]
        exact (hfam N hN).2 ν
    · have hKpos : 0 < (K : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hK)
      obtain ⟨Csr, hC, hfactory⟩ := exists_sourceLog_entropic_commutator (ι := ι) n hn
      obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hKpos hd' ρ M hM hρ hpair
      refine ⟨βloc, hloc, ?_⟩
      intro β hβ
      obtain ⟨Cub, Cpf, hCub, hCpf, hrem, hlet⟩ := hβfactory β hβ
      obtain ⟨hε, hCem, hcap, hforc, hmom, hent⟩ := hlet
      refine ⟨sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n), Cpf,
        sourceLogTransportCem (β : ℝ) βloc
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
            (fun a b => logPhysicalPair (a, b)))
          glzUniversalTailConstant Cub, hε, hCpf, hCem, hforc, ?_, ?_, ?_, ?_⟩
      · exact fun _ => ⟨fun h => absurd h hK,
          fun _ => ⟨Csr, Cub, hC, hCub, hrem, rfl, rfl⟩⟩
      · exact fun h => absurd h (lt_irrefl _)
      · intro σ hσ N hN
        simp only [sourceT28Observable_zero, sourceT28Gibbs_zero]
        exact hmom σ hσ N hN
      · intro N hN ν hν _
        simp only [sourceT28Observable_zero, sourceT28FreeEnergy_zero]
        exact hent N hN ν
  · have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    obtain ⟨βloc, hloc, hfam⟩ :=
      exists_sourceRiesz_entropic_commutator_printed_constants (ι := ι) n hn s hs0 hd M hM
    refine ⟨βloc, hloc, ?_⟩
    intro β hβ
    obtain ⟨Cub, Cpf, hCub, hCpf, hCubp, hCpfp, hK⟩ := hfam β hβ
    obtain ⟨hε, hmain⟩ := hK hv
    obtain ⟨hCem, hforc, hmom, hent⟩ := hmain ρ hρ
    refine ⟨sourceRieszPositiveTransportParameter (ι := ι) s M n K (β : ℝ), Cpf,
      sourceRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
          (fun a b : E => gaussianRieszPhysicalPair s (a, b))),
      hε, hCpf, by linarith, hforc, ?_, ?_, ?_, ?_⟩
    · exact fun h => absurd h h0
    · exact fun _ => ⟨Cub, hCub, fun N hN hl => hCubp ρ hρ N hN hl, rfl, rfl⟩
    · intro σ hσ N hN
      simp only [sourceT28Observable_of_ne_zero h0, sourceT28Gibbs_of_ne_zero h0]
      exact hmom σ hσ N hN
    · intro N hN ν hν hdisj
      have hKL : klDiv ν (sourceRieszSingularGibbs s (β : ℝ) ρ N) ≠ ∞ := by
        rcases hdisj with h | h
        · exact absurd h h0
        · rwa [sourceT28Gibbs_of_ne_zero h0] at h
      obtain ⟨_, hint, hineq⟩ := hent N hN ν hKL
      simp only [sourceT28Observable_of_ne_zero h0, sourceT28FreeEnergy_of_ne_zero h0]
      exact ⟨hint, hineq⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceT28_full_range_printed
#print axioms DGRHS.Commutator.exists_sourceT28_full_range_printed
