/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.Definitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-! Unfolding the half-open fundamental cube for an arbitrary nonnegative
measurable function. The lattice action and Haar normalization are explicit. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace DGRHS.Gaussian.D11Imported.PeriodizationCube
open HighDim

local instance integerAction (d : ℕ) : AddAction (Frequency d) (Fin d → ℝ) where
  vadd n x := fun i => (n i : ℝ) + x i
  zero_vadd x := by
    funext i
    change ((0:ℤ):ℝ)+x i = x i
    simp
  add_vadd m n x := by
    funext i
    change ((m i+n i:ℤ):ℝ)+x i = (m i:ℝ)+((n i:ℝ)+x i)
    simp [add_assoc]

local instance (d : ℕ) : MeasurableConstVAdd (Frequency d) (Fin d → ℝ) where
  measurable_const_vadd n := by
    change Measurable (fun x : Fin d → ℝ => (fun i => (n i : ℝ)) + x)
    fun_prop

local instance (d : ℕ) : VAddInvariantMeasure (Frequency d) (Fin d → ℝ) volume where
  measure_preimage_vadd n s hs := by
    exact (measurePreserving_add_left volume (fun i => (n i : ℝ))).measure_preimage hs.nullMeasurableSet

def cube (d : ℕ) : Set (Fin d → ℝ) :=
  univ.pi (fun _ => Ico (-(1/2 : ℝ)) (1/2))

lemma cube_measurable (d : ℕ) : MeasurableSet (cube d) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

lemma cube_fundamental (d : ℕ) : IsAddFundamentalDomain (Frequency d) (cube d) volume := by
  apply IsAddFundamentalDomain.mk' (cube_measurable d).nullMeasurableSet
  intro x
  have hex (i : Fin d) : ∃! n : ℤ, (n:ℝ)+x i ∈ Ico (-(1/2:ℝ)) (1/2) := by
    simpa only [zsmul_eq_mul, Int.cast_smul_eq_zsmul, mul_one,
      show -(1/2:ℝ)+1 = 1/2 by norm_num, add_comm] using
      existsUnique_add_zsmul_mem_Ico (by norm_num : (0:ℝ)<1) (x i) (-(1/2:ℝ))
  choose n hn hunique using hex
  refine ⟨n, fun i _ => hn i, ?_⟩
  intro m hm
  funext i
  exact hunique i (m i) (hm i (mem_univ i))

lemma unfold_lintegral (d : ℕ) (f : (Fin d → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in cube d, ∑' n : Frequency d, f (fun i => x i+(n i:ℝ))) = ∫⁻ x, f x := by
  rw [lintegral_tsum (fun n : Frequency d =>
    (show Measurable (fun x : Fin d → ℝ => f (fun i => x i+(n i:ℝ))) from hf.comp (by fun_prop)).aemeasurable)]
  have h := (cube_fundamental d).lintegral_eq_tsum' f
  rw [h]
  have he := (Equiv.neg (Frequency d)).tsum_eq
    (fun n => ∫⁻ x in cube d, f (fun i => x i+(n i:ℝ)))
  rw [← he]
  apply tsum_congr
  intro n
  apply lintegral_congr
  intro x
  congr 1
  funext i
  change x i + ((-n) i : ℝ) = ((-n) i : ℝ) + x i
  ring

lemma quotient_measurePreserving (d : ℕ) :
    MeasurePreserving (fun x : Fin d → ℝ => fun i => (x i : UnitAddCircle))
      (volume.restrict (cube d)) (torusMeasure d) := by
  have hc : MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Ico (-(1/2:ℝ)) (1/2))) AddCircle.haarAddCircle := by
    rw [restrict_Ico_eq_restrict_Ioc]
    have h := AddCircle.measurePreserving_mk (T := 1) (-(1/2:ℝ))
    have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa only [ENNReal.ofReal_one, one_smul] using AddCircle.volume_eq_smul_haarAddCircle (T := 1)
    norm_num only [show -(1/2:ℝ)+1 = 1/2 by norm_num] at h
    rwa [hv] at h
  have h := measurePreserving_pi (fun _ : Fin d => volume.restrict (Ico (-(1/2:ℝ)) (1/2)))
    (fun _ : Fin d => AddCircle.haarAddCircle) (fun _ => hc)
  rw [← Measure.restrict_pi_pi, ← volume_pi] at h
  exact h

#print axioms unfold_lintegral
end DGRHS.Gaussian.D11Imported.PeriodizationCube
