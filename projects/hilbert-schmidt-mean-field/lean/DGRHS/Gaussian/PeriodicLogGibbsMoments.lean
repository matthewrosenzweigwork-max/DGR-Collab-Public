import DGRHS.Gaussian.PeriodicLogTransportMoments

/-!
Packet P9h, unit 3 (LOG, part 11): the Gibbs exponential moments of the torus LOG transport energy
with the printed piecewise parameter `ε` and constant `C_em` (Remark A.1, `eq:CemLargeBetaDef`),
for both signs and every particle number (torus version of
`exists_sourceLogTransport_gibbs_moments`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

theorem periodicLog_gibbs_moments (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v → 0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub : ℝ, 1 ≤ Cub ∧
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
        (periodicLogSingularPartition (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x))) (periodicLogSingularGibbs (β : ℝ) ρ N) ∧
        (∫ x, Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x)) ∂periodicLogSingularGibbs (β : ℝ) ρ N) ≤
          sourceLogTransportCem (β : ℝ) βloc
            (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
              (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
            glzUniversalTailConstant Cub := by
  obtain ⟨Csr, hC, hlocal⟩ := periodicLog_local_numerator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  obtain ⟨βloc, hloc, hnum⟩ := hlocal hv hK ρ M hM hρ
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  let μ := periodicCappedDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
  let L := glzUniversalTailConstant
  have hL : 0 ≤ L := glzUniversalTailConstant_pos.le
  have hKn : 0 < (K : ℝ) ^ n := pow_pos hK n
  by_cases hsmall : (β : ℝ) ≤ βloc
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · intro N hN hlarge
      exact absurd hlarge (not_lt_of_ge hsmall)
    intro σ hσ N hN
    obtain ⟨Cp, hCp, hrep⟩ := periodicLogParticleWeight_uniform (β : ℝ) β.coe_nonneg ρ M hM hρ
    obtain ⟨hui, hz, -⟩ := hrep N hN
    obtain ⟨hi, hb⟩ := hnum (β : ℝ) β.coe_nonneg hsmall σ hσ N (by omega)
    rw [periodicLogSingularGibbs_eq_particle (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    have hε : sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) =
        (β : ℝ) / (4 * Csr * (K : ℝ) ^ n) := by
      unfold sourceLogTransportEpsilon
      rw [ite_eq_left hsmall]
    obtain ⟨hq, hqb⟩ := gibbs_moment_of_numerator
      (Measure.pi (fun _ : Fin N => μ)) (periodicLogParticleExponent ρ (β : ℝ) N)
      (fun x => (σ * (β / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) hui
      (Real.exp ((β : ℝ) * I)) (Real.exp 1) (Real.exp_pos _) hz hi hb
    have hfun : (fun x : Fin N → PeriodicTorus ι => Real.exp (σ *
        sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x))) =
        fun x => Real.exp ((σ * ((β : ℝ) / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) := by
      funext x
      rw [hε]
    rw [hfun]
    refine ⟨hq, ?_⟩
    have hc : sourceLogTransportCem (β : ℝ) βloc I L 1 =
        Real.exp (-(β : ℝ) * I) * (Real.exp 1 + L) := by
      unfold sourceLogTransportCem
      rw [ite_eq_left hsmall]
    have hr : Real.exp 1 / Real.exp ((β : ℝ) * I) = Real.exp (-(β : ℝ) * I) * Real.exp 1 := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring
    calc _ ≤ Real.exp 1 / Real.exp ((β : ℝ) * I) := hqb
      _ = Real.exp (-(β : ℝ) * I) * Real.exp 1 := hr
      _ ≤ Real.exp (-(β : ℝ) * I) * (Real.exp 1 + L) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by
        unfold sourceLogTransportCem
        rw [ite_eq_left hsmall]
  · have hlarge : βloc < (β : ℝ) := lt_of_not_ge hsmall
    obtain ⟨Cp1, hCp1, hP1⟩ := periodicLogParticleWeight_uniform (2 * (β : ℝ) - βloc)
      (by linarith [β.coe_nonneg]) ρ M hM hρ
    obtain ⟨Cp, hCp, hrep⟩ := periodicLogParticleWeight_uniform (β : ℝ) β.coe_nonneg ρ M hM hρ
    obtain ⟨Cp0, hCp0, hrep0⟩ := periodicLogParticleWeight_uniform βloc hloc.le ρ M hM hρ
    refine ⟨max Cp1 1, le_max_right _ _, ?_, ?_⟩
    · intro N hN _
      rw [periodicLogSingularPartition_toReal_eq (2 * (β : ℝ) - βloc) (by linarith [β.coe_nonneg])
        ρ M hM hρ N hN]
      exact (hP1 N hN).2.2.trans (le_max_left _ _)
    intro σ hσ N hN
    obtain ⟨hui, hz, -⟩ := hrep N hN
    obtain ⟨hi, hb⟩ := hnum βloc hloc.le le_rfl σ hσ N (by omega)
    obtain ⟨hu2, -, hu2b⟩ := hP1 N hN
    rw [periodicLogSingularGibbs_eq_particle (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    have hε : sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) =
        βloc / (8 * Csr * (K : ℝ) ^ n) := by
      unfold sourceLogTransportEpsilon
      rw [ite_eq_right hsmall]
    obtain ⟨hq, hqb⟩ := gibbs_moment_holder
      (Measure.pi (fun _ : Fin N => μ)) (periodicLogParticleExponent ρ (β : ℝ) N)
      (periodicLogParticleExponent ρ βloc N) (periodicLogParticleExponent ρ (2 * (β : ℝ) - βloc) N)
      (fun x => (σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
      (fun x => by unfold periodicLogParticleExponent; ring) hui hi (Real.exp 1) hb hu2
      (max Cp1 1) (hu2b.trans (le_max_left _ _)) (Real.exp ((β : ℝ) * I)) (Real.exp_pos _) hz
    have hfun : (fun x : Fin N → PeriodicTorus ι => Real.exp (σ *
        sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x))) =
        fun x => Real.exp (((σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) / 2) := by
      funext x
      rw [hε]
      congr 1
      simp only [periodicLogA]
      ring
    rw [hfun]
    refine ⟨hq, ?_⟩
    refine hqb.trans ?_
    have hI : Real.sqrt (Real.exp 1) * Real.sqrt (max Cp1 1) / Real.exp ((β : ℝ) * I) =
        Real.exp (-(β : ℝ) * I) * Real.sqrt (Real.exp 1) * Real.sqrt (max Cp1 1) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring
    rw [hI]
    unfold sourceLogTransportCem
    rw [ite_eq_right hsmall]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.exp_pos _).le)
      (Real.sqrt_nonneg _)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_gibbs_moments
