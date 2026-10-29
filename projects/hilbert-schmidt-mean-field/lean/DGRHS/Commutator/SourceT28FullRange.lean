import DGRHS.Commutator.SourceLogEntropicCommutator
import DGRHS.Commutator.SourceRieszEntropicCommutator

/-! Source Theorem 2.8, full range `0 ≤ s < d/2`, as ONE statement.

The two kernel regimes are dispatched on the endpoint `s = 0` (logarithmic
kernel, collision free energy, assumption (2.3) as integrability of
`logPhysicalPair`) versus `0 < s` (Riesz kernel, finite-relative-entropy
convention).  Each branch supplies its own constants; the constants
`βloc, ε, Cpf, Cem` of the unified statement are those of the active branch.
No totalized integral is used on either branch. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- `A_n(v, X_N, μ)` (times the factor used in the printed normalization),
for the active kernel. -/
def sourceT28Observable (s : ℝ) (n : ℕ) (v : E → E) (ρ : E → ℝ) (N : ℕ)
    (x : Fin N → E) : ℝ :=
  if s = 0 then sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
    (sourceLogTransportKernel n v) N x
  else sourceRieszLocalTransportEnergy ρ s n v N x

/-- The literal singular Gibbs law `Q_{N,β}(μ)` of the active kernel. -/
def sourceT28Gibbs (s : ℝ) (β : ℝ≥0) (ρ : E → ℝ) (N : ℕ) : Measure (Fin N → E) :=
  if s = 0 then sourceLogSingularGibbs β ρ N
  else sourceRieszSingularGibbs s (β : ℝ) ρ N

/-- The modulated free energy `E_N(ν, μ)` of the active kernel, in `EReal`. -/
def sourceT28FreeEnergy (s : ℝ) (β : ℝ≥0) (ρ : E → ℝ) (M : ℝ) (N : ℕ)
    (ν : Measure (Fin N → E)) : EReal :=
  if s = 0 then sourceLogCollisionFreeEnergy β ρ M N ν
  else sourceRieszTransportExtendedFreeEnergy ρ s M (β : ℝ) N ν

lemma sourceT28Observable_zero (n : ℕ) (v : E → E) (ρ : E → ℝ) (N : ℕ) (x : Fin N → E) :
    sourceT28Observable 0 n v ρ N x = sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
      (sourceLogTransportKernel n v) N x := by
  unfold sourceT28Observable
  exact ite_eq_left rfl

lemma sourceT28Observable_of_ne_zero {s : ℝ} (hs : s ≠ 0) (n : ℕ) (v : E → E) (ρ : E → ℝ)
    (N : ℕ) (x : Fin N → E) :
    sourceT28Observable s n v ρ N x = sourceRieszLocalTransportEnergy ρ s n v N x := by
  unfold sourceT28Observable
  exact ite_eq_right hs

lemma sourceT28Gibbs_zero (β : ℝ≥0) (ρ : E → ℝ) (N : ℕ) :
    sourceT28Gibbs 0 β ρ N = sourceLogSingularGibbs β ρ N := by
  unfold sourceT28Gibbs
  exact ite_eq_left rfl

lemma sourceT28Gibbs_of_ne_zero {s : ℝ} (hs : s ≠ 0) (β : ℝ≥0) (ρ : E → ℝ) (N : ℕ) :
    sourceT28Gibbs s β ρ N = sourceRieszSingularGibbs s (β : ℝ) ρ N := by
  unfold sourceT28Gibbs
  exact ite_eq_right hs

lemma sourceT28FreeEnergy_zero (β : ℝ≥0) (ρ : E → ℝ) (M : ℝ) (N : ℕ)
    (ν : Measure (Fin N → E)) :
    sourceT28FreeEnergy 0 β ρ M N ν = sourceLogCollisionFreeEnergy β ρ M N ν := by
  unfold sourceT28FreeEnergy
  exact ite_eq_left rfl

lemma sourceT28FreeEnergy_of_ne_zero {s : ℝ} (hs : s ≠ 0) (β : ℝ≥0) (ρ : E → ℝ) (M : ℝ)
    (N : ℕ) (ν : Measure (Fin N → E)) :
    sourceT28FreeEnergy s β ρ M N ν =
      sourceRieszTransportExtendedFreeEnergy ρ s M (β : ℝ) N ν := by
  unfold sourceT28FreeEnergy
  exact ite_eq_right hs

/-- Source Theorem 2.8 for `0 ≤ s < d/2`: exponential moment (2.21) for both
signs and entropic inequality (2.22), with logarithmic constants (2.23).
Hypotheses are the printed ones: `0 ≤ s < d/2`, `ρ` a bounded probability
density (`ρ ≤ M`), `v` globally Lipschitz (constant `K`), `β > 0`, and, for
`s = 0` only, the log-energy assumption (2.3).  For `s > 0` the inequality (2.22)
is asserted for laws with finite relative entropy to the Gibbs law (owner
convention); for `s = 0` it holds for every probability law. -/
theorem exists_source_entropic_commutator_full_range (n : ℕ) (hn : 0 < n) (s : ℝ)
    (hs : 0 ≤ s) (hd : 2 * s < (Fintype.card ι : ℝ))
    {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : s = 0 → Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ ε Cpf Cem : ℝ, 0 < ε ∧ 1 ≤ Cpf ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
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
      refine ⟨1, Cpf, 1, one_pos, hCpf, one_pos, ?_, ?_, ?_⟩
      · rw [Real.log_one, add_zero]
        exact Real.log_nonneg hCpf
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
      refine ⟨_, Cpf, _, hε, hCpf, hCem, hforc, ?_, ?_⟩
      · intro σ hσ N hN
        simp only [sourceT28Observable_zero, sourceT28Gibbs_zero]
        exact hmom σ hσ N hN
      · intro N hN ν hν _
        simp only [sourceT28Observable_zero, sourceT28FreeEnergy_zero]
        exact hent N hN ν
  · have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    obtain ⟨βloc, hloc, hfam⟩ := exists_sourceRiesz_entropic_commutator (ι := ι) n hn s hs0 hd M hM
    refine ⟨βloc, hloc, ?_⟩
    intro β hβ
    obtain ⟨Cub, Cpf, hCub, hCpf, hCubp, hCpfp, hK⟩ := hfam β hβ
    obtain ⟨hε, hCem, hforc, hmain⟩ := hK hv
    obtain ⟨hmom, hent⟩ := hmain ρ hρ
    refine ⟨_, Cpf, _, hε, hCpf, by linarith, hforc, ?_, ?_⟩
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
#check @DGRHS.Commutator.sourceT28Observable
#print axioms DGRHS.Commutator.sourceT28Observable
#check @DGRHS.Commutator.sourceT28Gibbs
#print axioms DGRHS.Commutator.sourceT28Gibbs
#check @DGRHS.Commutator.sourceT28FreeEnergy
#print axioms DGRHS.Commutator.sourceT28FreeEnergy
#check @DGRHS.Commutator.exists_source_entropic_commutator_full_range
#print axioms DGRHS.Commutator.exists_source_entropic_commutator_full_range
