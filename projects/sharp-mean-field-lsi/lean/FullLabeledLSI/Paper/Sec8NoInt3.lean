import FullLabeledLSI.Paper.Sec8NoInt2

/-!
# Section 8.5: tagged functions and the identity `r_N^all = r_LS(μ)` for `W = 0`
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem tagged_aux (hyp : Hyp V W KV KW) {N : ℕ} (i : Fin N) {ν : Measure (Torus d)}
    (hmarg : (gibbs V W N).map (fun X => X i) = ν) (hνac : ν ≪ volume)
    {h : Torus d → ℝ} (hh : MemH1 (haar d) h) :
    MemH1C (gibbs V W N) (fun X => h (X i)) ∧
    ent (gibbs V W N) (fun X => h (X i) ^ 2) = ent ν (fun x => h x ^ 2) ∧
    energy V W N (fun X => h (X i)) = dirichlet ν h := by
  have hπ : Measurable fun X : Config N d => X i := measurable_pi_apply i
  have hw := isWeakGrad_weakGrad hh.1
  refine ⟨memH1C_comp_eval hyp i hh, ?_, ?_⟩
  · have hu : AEStronglyMeasurable (fun x => h x ^ 2) ((gibbs V W N).map fun X => X i) := by
      rw [hmarg]; exact (hh.2.1.aestronglyMeasurable.mono_ac hνac).pow 2
    rw [ent_comp _ hπ hu, hmarg]
  · rw [energy_comp_eval hyp i hh]
    have hm : AEMeasurable (fun x => ENNReal.ofReal (sqNorm (weakGrad h x)))
        ((gibbs V W N).map fun X => X i) := by
      rw [hmarg]
      exact (ENNReal.measurable_ofReal.comp_aemeasurable
        hw.aestronglyMeasurable_sqNorm.aemeasurable).mono_ac hνac
    rw [← lintegral_map' hm hπ.aemeasurable, hmarg]
    rfl

theorem rAll_le_rLS_of_pi (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) {q : Torus d → ℝ}
    {c C : ℝ} [IsProbabilityMeasure (densMeasure q)] (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C)
    (hgp : gibbs V W N = Measure.pi fun _ : Fin N => densMeasure q) :
    rAll V W N ≤ rLS (densMeasure q) := by
  unfold rLS
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hfH, hent⟩ := hf
  set i : Fin N := ⟨0, hN⟩
  have hac : densMeasure q ≪ volume := withDensity_absolutelyContinuous _ _
  have hmarg : (gibbs V W N).map (fun X => X i) = densMeasure q := by
    rw [hgp]; exact (measurePreserving_eval (fun _ : Fin N => densMeasure q) i).map_eq
  have hh : MemH1 (haar d) f := memH1_haar_of_dens hc (fun x => (hbd x).1) hfH
  obtain ⟨h1, h2, h3⟩ := tagged_aux hyp i hmarg hac hh
  refine (iInf₂_le (fun X => f (X i)) ⟨h1, ?_⟩).trans (le_of_eq ?_)
  · rw [h2, h3]
  · rw [h2]; exact hent

end Sec8
end SharpLSI.FL
