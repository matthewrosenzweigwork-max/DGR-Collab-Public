import SharpSymmetricLSI.Paper.PartitionLimit
import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D09_ParticleRates
import SharpSymmetricLSI.Infra.Mollify

/-!
# (2.10): the entropy of product states (Phase 3, lane D; R6)

`N^{-1} H(ρ^{⊗N}|P_N) = H(ρ|m) + ρ(V) + ((N-1)/(2N)) W(ρ,ρ) + N^{-1} log Z_N → G(ρ)`,
from the Gibbs variational identity, tensorization and Lemma 2.4.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem isOpenQuotientMap_liftT : IsOpenQuotientMap (liftT (ι := Fin d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem IsSmoothT.continuous {f : Torus d → ℝ} (hf : IsSmoothT f) : Continuous f :=
  isOpenQuotientMap_liftT.continuous_comp_iff.mp (ContDiff.continuous hf)

theorem klDiv_densMeasure_ne_top_of_continuous {ρ : Torus d → ℝ} (hc : Continuous ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1) :
    klDiv (densMeasure ρ) (haar d) ≠ ⊤ := by
  obtain ⟨B, hB⟩ := exists_bound_of_continuous hc
  exact (klDiv_densMeasure_bdd hc.measurable hρ0 hρ1 fun x => (le_abs_self _).trans (hB x)).1

theorem gap_eq_coe (hyp : Hyp V W KV KW) {ρ : Measure (Torus d)} (h : klDiv ρ (haar d) ≠ ⊤) :
    gap V W ρ = (((klDiv ρ (haar d)).toReal + energyMF V W ρ - (Fstar V W).toReal : ℝ) : EReal) := by
  unfold gap
  rw [freeEnergy_eq _ h]
  nth_rw 1 [Fstar_eq_coe hyp]
  rw [← EReal.coe_sub]

/-- (2.10). -/
theorem product_state_entropy_aux (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ}
    (hs : IsSmoothT ρ) (hpos : ∀ x, 0 < ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) :
    (∀ N : ℕ, 1 ≤ N →
      klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) ≠ ⊤ ∧
      (klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal / N =
        (klDiv (densMeasure ρ) (haar d)).toReal + potE V (densMeasure ρ) +
          ((N : ℝ) - 1) / (2 * N) * interE W (densMeasure ρ) (densMeasure ρ) +
          Real.log (partitionFn V W N) / N) ∧
    gap V W (densMeasure ρ) ≠ ⊤ ∧
    Tendsto (fun N : ℕ => (klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal / N) atTop
      (𝓝 (gap V W (densMeasure ρ)).toReal) := by
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hpos x).le
  haveI := isProbabilityMeasure_densMeasure' hρ0 h1
  have hk := klDiv_densMeasure_ne_top_of_continuous hs.continuous hρ0 h1
  set KL := (klDiv (densMeasure ρ) (haar d)).toReal
  set Pt := potE V (densMeasure ρ)
  set I := interE W (densMeasure ρ) (densMeasure ρ)
  have hid : ∀ N : ℕ, 1 ≤ N → klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N) ≠ ⊤ ∧
      (klDiv (Measure.pi fun _ : Fin N => densMeasure ρ) (gibbs V W N)).toReal / N =
        KL + Pt + ((N : ℝ) - 1) / (2 * N) * I + Real.log (partitionFn V W N) / N := by
    intro N hN
    have hp := klDiv_pi (N := N) hk
    have hg := klDiv_gibbs hyp hp.1
    refine ⟨hg.1, ?_⟩
    rw [hg.2, hp.2, integral_hamiltonian_pi hyp hN]
    have hN0 : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                                 exact this.ne'
    field_simp
    ring
  refine ⟨hid, ?_, ?_⟩
  · rw [gap_eq_coe hyp hk]; exact EReal.coe_ne_top _
  · rw [gap_eq_coe hyp hk, EReal.toReal_coe]
    have hlim : Tendsto (fun N : ℕ => KL + Pt + ((N : ℝ) - 1) / (2 * N) * I +
        Real.log (partitionFn V W N) / N) atTop
        (𝓝 (KL + Pt + 1 / 2 * I + -(Fstar V W).toReal)) := by
      have hq : Tendsto (fun N : ℕ => ((N : ℝ) - 1) / (2 * N)) atTop (𝓝 (1 / 2)) := by
        have : Tendsto (fun N : ℕ => (1 : ℝ) / 2 - 1 / (2 * (N : ℝ))) atTop (𝓝 (1 / 2 - 0)) := by
          refine tendsto_const_nhds.sub ?_
          have := tendsto_const_div_atTop_nhds_zero_nat (1 / 2 : ℝ)
          refine this.congr fun N => ?_
          ring
        rw [sub_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                                     exact this.ne'
        field_simp
      exact ((tendsto_const_nhds.add (hq.mul_const I)).add (tendsto_log_partition hyp))
    have e : KL + Pt + 1 / 2 * I + -(Fstar V W).toReal = KL + energyMF V W (densMeasure ρ) -
        (Fstar V W).toReal := by unfold energyMF; ring
    rw [e] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hid N hN).2.symm

end SharpLSI
