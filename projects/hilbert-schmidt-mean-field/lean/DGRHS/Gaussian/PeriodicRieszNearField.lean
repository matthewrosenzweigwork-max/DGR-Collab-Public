import DGRHS.Gaussian.PeriodicRieszPairs
import DGRHS.Gaussian.PeriodicPositiveMellinCutoff
import DGRHS.Gaussian.PeriodicPositiveMellinNearField
import DGRHS.Gaussian.PeriodicRieszSingularPartition

/-!
Packet P9h, unit 2 (part 17): near-field estimate of the short pair kernel.  The short Riesz sum is
almost everywhere the positive short heat-time piece `periodicRieszPositiveShort s 0 (2π²η²)`, whose Haar
mass is `F (2π²η²)^{(d-s)/2} / ((d-s)/2)`; hence its potential against a bounded density is `≲ η^{d-s}`.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The short kernel as a function on the torus. -/
def periodicRieszShortFun (s η : ℝ) (x : PeriodicTorus ι) : ℝ :=
  if x = 0 then 0 else periodicRieszShortSum s η (periodicCenteredLift x)

lemma periodicRieszShortPair_eq (s η : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszShortPair s η p = periodicRieszShortFun s η (p.1 - p.2) := by
  simp only [periodicRieszShortPair, periodicRieszShortFun, sub_eq_zero]

lemma periodicRieszShortFun_nonneg (s η : ℝ) (hs : 0 < s) (x : PeriodicTorus ι) :
    0 ≤ periodicRieszShortFun s η x := by
  unfold periodicRieszShortFun
  split_ifs
  · exact le_rfl
  · exact periodicRieszShortSum_nonneg s η hs _

lemma periodicRieszShortSum_eq_positiveShort (s η : ℝ) (hs : 0 < s) (hη : 0 < η) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    periodicRieszShortSum s η z = periodicRieszPositiveShort s 0 (periodicHeatCut η) (periodicLift z) := by
  obtain ⟨-, hint⟩ := periodic_short_heat_integral s η hs hη hz
  unfold periodicRieszShortSum periodicRieszPositiveShort periodicPositiveMellinShort
    periodicPositiveMellinIntegrand periodicRieszSmoothCoeff
  rw [← periodicProfileSum_const_mul, ← hint]
  simp only [add_zero, periodicHeatCut]

lemma periodicRieszShortFun_ae (s η : ℝ) (hs : 0 < s) (hη : 0 < η) :
    periodicRieszShortFun s η =ᵐ[periodicHaar ι]
      periodicRieszPositiveShort s 0 (periodicHeatCut η) := by
  have hn := periodicHaar_nullSingletonClass (ι := ι)
  have h3 : ∀ᵐ x ∂periodicHaar ι, x ≠ 0 := (periodicHaar ι).ae_ne 0
  filter_upwards [h3] with x hx
  unfold periodicRieszShortFun
  rw [ite_eq_right hx, periodicRieszShortSum_eq_positiveShort s η hs hη (periodicCenteredLift_mem_offLattice hx),
    periodicLift_centeredLift]

lemma periodicRieszShortFun_integrable (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) : Integrable (periodicRieszShortFun s η) (periodicHaar ι) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  exact (periodicRieszPositiveShort_integrable (ι := ι) s 0 (periodicHeatCut η) (by linarith) le_rfl).congr
    (periodicRieszShortFun_ae s η hs hη).symm

lemma periodicRieszShortFun_mass (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) :
    (∫ x, periodicRieszShortFun s η x ∂periodicHaar ι) =
      periodicRieszMellinFactor ι s * ((periodicHeatCut η) ^ (((Fintype.card ι : ℝ) - s) / 2) /
        (((Fintype.card ι : ℝ) - s) / 2)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  rw [integral_congr_ae (periodicRieszShortFun_ae s η hs hη)]
  exact periodicRieszPositiveShort_mass (ι := ι) s 0 (periodicHeatCut η) (by linarith) le_rfl
    (periodicHeatCut_pos hη).le

/-- Near-field (short potential) constant. -/
def periodicRieszShortPotentialConst (ι : Type u) [Fintype ι] (s M : ℝ) : ℝ :=
  M * periodicRieszMellinFactor ι s * (2 * Real.pi ^ 2) ^ (((Fintype.card ι : ℝ) - s) / 2) /
    (((Fintype.card ι : ℝ) - s) / 2)

lemma periodicRieszShortFun_potential_le (s η : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    ∫ y, periodicRieszShortFun s η (x - y) ∂periodicCappedDensityMeasure ρ ≤
      periodicRieszShortPotentialConst ι s M * η ^ ((Fintype.card ι : ℝ) - s) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have h := periodicDensityRow_nonnegative_bound ρ M hM hρ (periodicRieszShortFun s η)
    (periodicRieszShortFun_integrable s η hs hs2 hη) (periodicRieszShortFun_nonneg s η hs) x
  rw [periodicRieszShortFun_mass s η hs hs2 hη] at h
  refine h.trans (le_of_eq ?_)
  unfold periodicRieszShortPotentialConst periodicHeatCut
  have hexp : (2 * Real.pi ^ 2 * η ^ 2) ^ (((Fintype.card ι : ℝ) - s) / 2) =
      (2 * Real.pi ^ 2) ^ (((Fintype.card ι : ℝ) - s) / 2) * η ^ ((Fintype.card ι : ℝ) - s) := by
    rw [Real.mul_rpow (by positivity) (sq_nonneg η), ← Real.rpow_natCast η 2, ← Real.rpow_mul hη.le]
    congr 2
    push_cast
    ring
  rw [hexp]
  ring

end DGRHS.Periodic
