import DGRHS.Gaussian.PeriodicRieszMasterBand
import DGRHS.Gaussian.PeriodicRieszTimeParticleSplit
import DGRHS.Gaussian.GaussianRieszAdaptiveScale

/-!
Packet P9b, unit 4 (periodic analogue of `gaussianRieszAdaptiveScale` / `Band` / `Cap` and of the
adaptive event comparison, i.e. the periodic (M1)/(M2) layer of TeX 1557-1643).

Route note.  The periodic chain here follows the Euclidean *Lean* route (physical-space
Gaussian-profile / heat-time band, see reviews/T22_CORRESPONDENCE_20261006.md) and not the
Fourier-cutoff route of P8/P9a: the periodic heat-time band, near-field and tail pieces already exist
(`PeriodicRieszMasterBand`, `PeriodicRieszTimeParticleSplit`), and all of them are uniform in the heat
shift `τ ≥ 0`, which includes the exact kernel `τ = 0`.

The fixed upper heat time is `a` (a small constant with `a ≤ 1`), the adaptive lower heat time is the
square of the Euclidean adaptive length scale `min{√a, (u/(A n))^{1/(d-s)}}`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Adaptive lower heat time: the square of the adaptive length scale with cap `√a`. -/
def periodicRieszAdaptiveTime (s a A : ℝ) (n : ℕ) (u : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^ 2

lemma periodicRieszAdaptiveTime_pos_le (s a A u : ℝ) (n : ℕ) (ha : 0 < a) (hA : 0 < A)
    (hn : 1 ≤ n) (hu : 0 < u) :
    0 < periodicRieszAdaptiveTime s a A n u ι ∧ periodicRieszAdaptiveTime s a A n u ι ≤ a := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have h := gaussianRieszAdaptiveScale_pos_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu
  refine ⟨pow_pos h.1 2, ?_⟩
  calc _ ≤ (Real.sqrt a) ^ 2 := pow_le_pow_left₀ h.1.le h.2 2
    _ = a := Real.sq_sqrt ha.le

lemma sq_rpow_neg_half (l s : ℝ) (hl : 0 < l) : (l ^ 2) ^ (-s / 2) = l ^ (-s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
  congr 1
  push_cast
  ring

lemma sq_rpow_half_sub (l d s : ℝ) (hl : 0 < l) : (l ^ 2) ^ ((d - s) / 2) = l ^ (d - s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
  congr 1
  push_cast
  ring

/-- Adaptive master band (centered heat-time band between the adaptive lower time and `a`). -/
def periodicRieszAdaptiveBand (s τ a β A : ℝ) (n : ℕ) (u : ℝ) (ρ : PeriodicTorus ι → ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  periodicRieszMasterBand s τ (periodicRieszAdaptiveTime s a A n u ι) a (2 * β) ρ

/-- Deterministic cap of the adaptive band's iid negative statistic. -/
def periodicRieszAdaptiveCap (s a β A : ℝ) (n : ℕ) (u : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  1 + 4 * β * (periodicRieszMasterEnvelope s ι * (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2))

def periodicRieszAdaptiveC0 (s a β : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  1 + 8 * β * periodicRieszMasterEnvelope s ι * (Real.sqrt a) ^ (-s)

def periodicRieszAdaptiveC1 (s β A : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  8 * β * periodicRieszMasterEnvelope s ι * A ^ (s / ((Fintype.card ι : ℝ) - s))

lemma periodicRieszAdaptiveTime_rpow_neg_le (s a A u : ℝ) (n : ℕ) (ha : 0 < a) (hA : 0 < A)
    (hn : 1 ≤ n) (hu : 0 < u) (hs : 0 < s) (hsd : s < (Fintype.card ι : ℝ)) :
    (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) ≤
      (Real.sqrt a) ^ (-s) + A ^ (s / ((Fintype.card ι : ℝ) - s)) *
        ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have h := gaussianRieszAdaptiveScale_pos_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu
  have hp := gaussianRieszAdaptiveScale_inverse_power_le (Real.sqrt a) A (n : ℝ) u
    (Fintype.card ι : ℝ) s 0 (Real.sqrt_pos.mpr ha) hA hn' hu hs (by linarith)
  rw [max_eq_left h.1.le] at hp
  unfold periodicRieszAdaptiveTime
  rw [sq_rpow_neg_half _ _ h.1]
  exact hp

lemma periodicRieszAdaptiveBand_cap_ess_bounds (s τ a β A : ℝ) (hs : 0 < s)
    (hsd : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hβ : 0 ≤ β) (hA : 0 < A) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : 1 ≤ u) :
    0 ≤ periodicRieszAdaptiveC0 s a β ι ∧ 0 ≤ periodicRieszAdaptiveC1 s β A ι ∧
      0 < periodicRieszAdaptiveCap s a β A n u ι ∧
      periodicRieszAdaptiveCap s a β A n u ι ≤
        periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι *
          ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) ∧
      (eLpNormEssSup (periodicRieszAdaptiveBand s τ a β A n u ρ)
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))).toReal ≤
        periodicRieszAdaptiveC0 s a β ι + periodicRieszAdaptiveC1 s β A ι *
          ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd' : s < (Fintype.card ι : ℝ) := by linarith
  have hu0 : 0 < u := by linarith
  have hE := periodicRieszMasterEnvelope_nonneg (ι := ι) s hs
  have hT := periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn hu0
  have hR := periodicRieszAdaptiveTime_rpow_neg_le (ι := ι) s a A u n ha hA hn hu0 hs hsd'
  have hpos : 0 ≤ (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) :=
    Real.rpow_nonneg hT.1.le _
  have hb : 8 * β * periodicRieszMasterEnvelope s ι * (periodicRieszAdaptiveTime s a A n u ι) ^ (-s / 2) ≤
      periodicRieszAdaptiveC0 s a β ι - 1 + periodicRieszAdaptiveC1 s β A ι *
        ((n : ℝ) / u) ^ (s / ((Fintype.card ι : ℝ) - s)) := by
    unfold periodicRieszAdaptiveC0 periodicRieszAdaptiveC1
    have hc : 0 ≤ 8 * β * periodicRieszMasterEnvelope s ι := by positivity
    have := mul_le_mul_of_nonneg_left hR hc
    nlinarith only [this]
  have he := essential_periodicRieszMasterBand_le s τ (periodicRieszAdaptiveTime s a A n u ι) a
    (2 * β) hs hτ hT.1 ha1 ρ
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * β)] at he
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold periodicRieszAdaptiveC0
    have : 0 ≤ (Real.sqrt a) ^ (-s) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    positivity
  · unfold periodicRieszAdaptiveC1
    positivity
  · unfold periodicRieszAdaptiveCap
    positivity
  · unfold periodicRieszAdaptiveCap
    nlinarith [mul_nonneg hβ (mul_nonneg hE hpos)]
  · unfold periodicRieszAdaptiveBand
    nlinarith only [he, hb]

/-- The adaptive near-field/tail comparison (periodic (M1)): on the event that the full
(heat-shifted) centered statistic reaches `u`, the adaptive band statistic reaches `u`. -/
lemma ae_periodicRieszParticle_adaptive_comparison (s τ a β A u₀ u : ℝ) (hs : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n) (hA : 0 < A)
    (hAcontrol : 4 * β * (M * (periodicRieszMellinFactor ι s /
      (((Fintype.card ι : ℝ) - s) / 2))) ≤ A)
    (hu₀ : 1 ≤ u₀)
    (hlow : 4 * (β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
      (a ^ (-s / 2) / (s / 2)))) ≤ u₀)
    (hu : u₀ ≤ u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ),
      u ≤ β * iidNegativeStatistic n (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszMellinGreen s τ (q.1 - q.2))) ω →
      u ≤ iidNegativeStatistic n (periodicRieszAdaptiveBand s τ a β A n u ρ) ω := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hn)
  have hu0 : 0 < u := by linarith
  have hT := periodicRieszAdaptiveTime_pos_le (ι := ι) s a A u n ha hA hn hu0
  have hl := gaussianRieszAdaptiveScale_pos_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu0
  have hdim : 0 < (Fintype.card ι : ℝ) - s := by linarith
  have hp := gaussianRieszAdaptiveScale_power_le (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s
    (Real.sqrt_pos.mpr ha) hA hn' hu0 hdim
  have hp' : (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) * (A * (n : ℝ)) ≤ u := (le_div_iff₀ (mul_pos hA hn')).1 hp
  have hF := (periodicRieszMellinFactor_pos (ι := ι) s hs).le
  have hh : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  have hnearpow : (periodicRieszAdaptiveTime s a A n u ι) ^ (((Fintype.card ι : ℝ) - s) / 2) =
      (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
        ((Fintype.card ι : ℝ) - s) := by
    unfold periodicRieszAdaptiveTime
    exact sq_rpow_half_sub _ _ _ hl.1
  have hlp : 0 ≤ (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) := Real.rpow_nonneg hl.1.le _
  set P := (gaussianRieszAdaptiveScale (Real.sqrt a) A (n : ℝ) u (Fintype.card ι : ℝ) s) ^
      ((Fintype.card ι : ℝ) - s) with hP
  set Cn := M * (periodicRieszMellinFactor ι s / (((Fintype.card ι : ℝ) - s) / 2)) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  have hnear : β * (n : ℝ) * (M * (periodicRieszMellinFactor ι s *
      ((periodicRieszAdaptiveTime s a A n u ι) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2)))) ≤ u / 4 := by
    rw [hnearpow]
    have e : β * (n : ℝ) * (M * (periodicRieszMellinFactor ι s *
        (P / (((Fintype.card ι : ℝ) - s) / 2)))) = (β * Cn) * ((n : ℝ) * P) := by
      rw [hCn]; ring
    rw [e]
    have h1 : 4 * β * Cn * ((n : ℝ) * P) ≤ A * ((n : ℝ) * P) :=
      mul_le_mul_of_nonneg_right hAcontrol (by positivity)
    nlinarith only [h1, hp']
  have htail : β * (2 * periodicRieszMellinFactor ι s * periodicHeatDiagonalGlobalConstant ι *
      (a ^ (-s / 2) / (s / 2))) ≤ u / 4 := by linarith
  filter_upwards [periodicRieszMellinGreen_particle_comparison s τ
    (periodicRieszAdaptiveTime s a A n u ι) a β hs hsd hτ hT.1 hT.2 ha1 hβ ρ M hM hρ n hn] with ω hω
  intro hx
  unfold periodicRieszAdaptiveBand periodicRieszMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  nlinarith only [hω, hx, hnear, htail]

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRieszAdaptiveTime_pos_le
#print axioms DGRHS.Periodic.periodicRieszAdaptiveTime_rpow_neg_le
#print axioms DGRHS.Periodic.periodicRieszAdaptiveBand_cap_ess_bounds
#print axioms DGRHS.Periodic.ae_periodicRieszParticle_adaptive_comparison
