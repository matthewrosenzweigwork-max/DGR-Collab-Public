import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-! UNCOMPILED source-facing analytic adapter. A scalar static weak evolution
with a continuous generator has its actual derivative at every interior time.
Conversely, a bounded interior derivative and endpoint continuity imply AC.
Neither statement assumes a moving-test identity or an endpoint identity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
namespace DGRHS.Commutator

lemma hasDerivAt_of_ac_continuous_generator
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ContinuousOn g (Icc a b))
    (he : deriv f =ᵐ[volume.restrict (Ioc a b)] g)
    (r : ℝ) (hr : r ∈ Ioo a b) : HasDerivAt f (g r) r := by
  have hab : a ≤ b := hr.1.le.trans hr.2.le
  let c : ℝ → ℝ := fun u => max a (min b u)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (u : ℝ) : c u ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hce (u : ℝ) (hu : u ∈ Icc a b) : c u = u := by
    dsimp only [c]
    rw [min_eq_right hu.2, max_eq_right hu.1]
  let G : ℝ → ℝ := g ∘ c
  have hG : Continuous G := hg.comp_continuous hc hcm
  have hGe (u : ℝ) (hu : u ∈ Icc a b) : G u = g u := by
    change g (c u) = g u
    rw [hce u hu]
  have hrep (u : ℝ) (hu : u ∈ Icc a b) :
      f u = f a + ∫ v in a..u, G v := by
    have hsub : uIcc a u ⊆ uIcc a b := by
      rw [uIcc_of_le hu.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hu.2
    have ht := (hf.mono hsub).integral_deriv_eq_sub
    have hei : (∫ v in a..u, deriv f v) = ∫ v in a..u, G v := by
      rw [intervalIntegral.integral_of_le hu.1, intervalIntegral.integral_of_le hu.1]
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Ioc_subset_Ioc_right hu.2) he, ae_restrict_mem measurableSet_Ioc] with v hv hvu
      exact hv.trans (hGe v ⟨hvu.1.le, hvu.2.trans hu.2⟩).symm
    rw [hei] at ht
    linarith
  have hd : HasDerivAt (fun u => f a + ∫ v in a..u, G v) (G r) r :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable a r)
      hG.aestronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add (f a)
  rw [hGe r ⟨hr.1.le, hr.2.le⟩] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with u hu
  exact hrep u ⟨hu.1.le, hu.2.le⟩

lemma ac_of_continuousOn_bounded_interior_derivative
    (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hg : ∀ r ∈ Ioo a b, HasDerivAt f (g r) r)
    (C : ℝ≥0) (hC : ∀ r ∈ Ioo a b, ‖g r‖ ≤ (C : ℝ)) :
    AbsolutelyContinuousOnInterval f a b := by
  have hL : LipschitzOnWith C f (Ioo a b) :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (hg r hr).hasDerivWithinAt)
      (fun r hr => by exact_mod_cast hC r hr)
  have hc : ContinuousOn f (closure (Ioo a b)) := by
    simpa only [closure_Ioo hab.ne] using hf
  have hLc : LipschitzOnWith C f (uIcc a b) := by
    simpa only [closure_Ioo hab.ne, uIcc_of_le hab.le] using LipschitzOnWith.closure hc hL
  exact hLc.absolutelyContinuousOnInterval

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.hasDerivAt_of_ac_continuous_generator
#print axioms DGRHS.Commutator.hasDerivAt_of_ac_continuous_generator
#check @DGRHS.Commutator.ac_of_continuousOn_bounded_interior_derivative
#print axioms DGRHS.Commutator.ac_of_continuousOn_bounded_interior_derivative
