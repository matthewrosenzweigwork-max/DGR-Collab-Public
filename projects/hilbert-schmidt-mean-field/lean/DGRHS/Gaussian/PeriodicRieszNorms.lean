import DGRHS.Gaussian.PeriodicRieszPairProperties

/-!
Packet P9h, unit 2 (part 19): `L²` control of the positive majorant `Ψ = f_1` of the torus Riesz kernels
and the row bounds against a bounded density.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The positive majorant as a function on the torus. -/
abbrev periodicRieszMajorantFun (s : ℝ) : PeriodicTorus ι → ℝ := periodicRieszShortFun s 1

lemma periodicRieszMajorantFun_memLp (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    MemLp (periodicRieszMajorantFun (ι := ι) s) 2 (periodicHaar ι) := by
  have hker := periodicRieszKernel_memLp (ι := ι) s hs2
  have hae := periodicRieszSmoothLift_ae (ι := ι) s 1 hs hs2 one_pos
  haveI := periodicHaar_nullSingletonClass (ι := ι)
  have h3 : ∀ᵐ x ∂periodicHaar ι, x ≠ 0 := (periodicHaar ι).ae_ne 0
  let Lfun : PeriodicTorus ι → ℝ := fun x =>
    periodicRieszLongKernel s (periodicHeatCut 1) (periodicCenteredLift x)
  let c0 : ℝ := periodicRieszMellinFactor ι s * (periodicHeatCut 1) ^ (((Fintype.card ι : ℝ) - s) / 2) /
    (((Fintype.card ι : ℝ) - s) / 2)
  have hLcont : Continuous (periodicRieszLongKernel (ι := ι) s (periodicHeatCut 1)) :=
    (contDiff_periodicRieszLongKernel s _ hs hs2 (periodicHeatCut_pos one_pos) 0).continuous
  have hLm : Measurable Lfun := hLcont.measurable.comp measurable_periodicCenteredLift
  have hLb : ∀ x, ‖Lfun x‖ ≤ ∑' k : PeriodicFrequency ι, periodicRieszLCCoeff s (periodicHeatCut 1) k *
      (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ 0 := by
    intro x
    have := norm_iteratedFDeriv_periodicRieszLongKernel_le (ι := ι) s (periodicHeatCut 1) hs hs2
      (periodicHeatCut_pos one_pos) 0 (periodicCenteredLift x)
    simpa [norm_iteratedFDeriv_zero, Lfun] using this
  have hL : MemLp Lfun 2 (periodicHaar ι) :=
    MemLp.of_bound hLm.aestronglyMeasurable _ (Filter.Eventually.of_forall hLb)
  have hsum : MemLp (fun x => periodicRieszKernel s hs2 x - Lfun x + c0) 2 (periodicHaar ι) :=
    (hker.sub hL).add (memLp_const c0)
  refine hsum.ae_eq ?_
  filter_upwards [hae, h3] with x hx hx3
  unfold periodicRieszMajorantFun periodicRieszShortFun
  rw [ite_eq_right hx3]
  unfold periodicRieszShortSum
  rw [← hx]
  simp only [periodicRieszSmoothLift_eq, periodicHeatCut, Lfun, c0]
  ring

end DGRHS.Periodic
