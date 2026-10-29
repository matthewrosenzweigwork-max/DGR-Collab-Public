import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Constructions.Pi

/-! UNCOMPILED CANDIDATE (Claude complete physical d1 return, 2026-10-03).
Finite-product tensorization of the native Mathlib Kullback-Leibler divergence.
Only pinned native statements are used: the data-processing inequality
`klDiv_map_le` (twice, for a measurable equivalence and its inverse), the chain
rule `klDiv_compProd_eq_add`, `klDiv_compProd_left`, `Measure.compProd_const`,
`Measure.prod_swap` and `measurePreserving_piFinSuccAbove`. The identities are
exact in `ℝ≥0∞`, so infinite divergences are retained rather than totalized.
No entropy, density or integrability hypothesis is assumed. -/
noncomputable section
open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Periodic

/-- Kullback-Leibler divergence is invariant under a measurable equivalence. -/
theorem klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : α ≃ᵐ β) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  haveI : IsFiniteMeasure (μ.map e) := Measure.isFiniteMeasure_map μ e
  haveI : IsFiniteMeasure (ν.map e) := Measure.isFiniteMeasure_map ν e
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h

/-- The second chain-rule term for a product with a common first factor. -/
theorem klDiv_prod_left_common {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (μ' ν' : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    klDiv (μ.prod μ') (μ.prod ν') = klDiv μ' ν' := by
  have hs := klDiv_map_measurableEquiv (μ'.prod μ) (ν'.prod μ)
    (MeasurableEquiv.prodComm : β × α ≃ᵐ α × β)
  have hc : (⇑(MeasurableEquiv.prodComm : β × α ≃ᵐ α × β)) = Prod.swap := rfl
  rw [hc, Measure.prod_swap, Measure.prod_swap] at hs
  rw [hs]
  have hk := klDiv_compProd_left μ' ν' (Kernel.const β μ)
  simpa only [Measure.compProd_const] using hk

/-- Exact two-factor tensorization, including the infinite cases. -/
theorem klDiv_prod_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (μ' ν' : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν'] :
    klDiv (μ.prod μ') (ν.prod ν') = klDiv μ ν + klDiv μ' ν' := by
  have hc := klDiv_compProd_eq_add μ ν (Kernel.const α μ') (Kernel.const α ν')
  simp only [Measure.compProd_const] at hc
  rw [hc, klDiv_prod_left_common μ μ' ν']

/-- Exact iid tensorization on `Fin N`, with the source particle index type. -/
theorem klDiv_pi_iid {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    klDiv (Measure.pi fun _ : Fin N => μ) (Measure.pi fun _ : Fin N => ν) =
      (N : ℝ≥0∞) * klDiv μ ν := by
  induction N with
  | zero =>
    have h : (Measure.pi fun _ : Fin 0 => μ) = Measure.pi fun _ : Fin 0 => ν := by
      rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
    rw [h, klDiv_self, Nat.cast_zero, zero_mul]
  | succ n ih =>
    have hμ : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) 0)
        (Measure.pi fun _ : Fin (n+1) => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0
    have hν : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) 0)
        (Measure.pi fun _ : Fin (n+1) => ν) (ν.prod (Measure.pi fun _ : Fin n => ν)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0
    rw [← klDiv_map_measurableEquiv (Measure.pi fun _ : Fin (n+1) => μ)
      (Measure.pi fun _ : Fin (n+1) => ν)
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) 0), hμ.map_eq, hν.map_eq,
      klDiv_prod_prod μ ν (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν), ih]
    push_cast
    ring

/-- Finite one-law divergence gives a finite iid particle divergence. -/
theorem klDiv_pi_iid_ne_top {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) (h : klDiv μ ν ≠ ∞) :
    klDiv (Measure.pi fun _ : Fin N => μ) (Measure.pi fun _ : Fin N => ν) ≠ ∞ := by
  rw [klDiv_pi_iid]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) h

theorem klDiv_pi_iid_toReal {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N : ℕ) :
    (klDiv (Measure.pi fun _ : Fin N => μ) (Measure.pi fun _ : Fin N => ν)).toReal =
      (N : ℝ) * (klDiv μ ν).toReal := by
  rw [klDiv_pi_iid, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end DGRHS.Periodic
