import SharpSymmetricLSI.Paper.ForceApprox7
import SharpSymmetricLSI.Paper.ForceApprox6
import SharpSymmetricLSI.Paper.LemmaA2_11

/-!
# R31 groundwork: continuity of `∂₁K_R` and the uniform force bound of (6.4)
-/

open MeasureTheory Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

theorem continuous_cgrad {F : Torus d → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT)) (k : Fin d) :
    Continuous fun y => cgrad F y k := by
  have hc : Continuous fun x => fderiv ℝ (F ∘ liftT) x (Pi.single k 1) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact continuous_comp_secT hc fun m x => by
    show fderiv ℝ (F ∘ liftT) (x + intVec m) (Pi.single k 1) =
      fderiv ℝ (F ∘ liftT) x (Pi.single k 1)
    rw [fderiv_lift_periodic]

theorem continuous_of_contDiff_lift' {F : Torus d → ℝ} (hF : ContDiff ℝ 1 (F ∘ liftT)) :
    Continuous F := by
  have h := continuous_comp_secT hF.continuous fun m x => by
    simp only [Function.comp_apply, liftT_add_intVec]
  simpa only [Function.comp_apply, liftT_secT] using h

theorem continuous_finKerD {φ : ℕ → Torus d → ℝ} (hφ : ∀ i, ContDiff ℝ 1 (φ i ∘ liftT))
    (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (k : Fin d) :
    Continuous fun p : Torus d × Torus d => finKerD φ s a p.1 p.2 k := by
  unfold finKerD
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (continuous_const.mul ((continuous_cgrad (hφ i) k).comp continuous_fst)).mul
    ((continuous_of_contDiff_lift' (hφ j)).comp continuous_snd)

/-- A continuous function bounded almost everywhere for a measure dominating a measure that is
positive on open sets is bounded everywhere. -/
theorem le_of_ae_le_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {ν ν' : Measure X} [ν'.IsOpenPosMeasure] (hνν' : ν' ≪ ν)
    {f : X → ℝ} (hf : Continuous f) {B : ℝ} (h : ∀ᵐ x ∂ν, f x ≤ B) (x : X) : f x ≤ B := by
  by_contra hx
  push Not at hx
  have hopen : IsOpen {y | B < f y} := isOpen_lt continuous_const hf
  have hne : ({y | B < f y} : Set X).Nonempty := ⟨x, hx⟩
  have hpos := hopen.measure_pos ν' hne
  have hzero : ν {y | B < f y} = 0 := by
    have := ae_iff.1 h
    simpa only [not_le] using this
  exact absurd (hνν' hzero) hpos.ne'

end SharpLSI
