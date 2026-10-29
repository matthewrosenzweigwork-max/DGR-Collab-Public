import SharpSymmetricLSI.Paper.DensMeasure
import SharpSymmetricLSI.Infra.TorusLift

/-!
# Cubic cells of `𝕋^d` (Phase 3, lane D; R5)

The partition of `𝕋^d` into the `K^d` cubes `∏ⱼ (aⱼ/K, (aⱼ+1)/K]`, each of Haar measure `K^{-d}`
and flat diameter `≤ 1/K` (method-of-types route for the upper half of Lemma 2.4).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {K : ℕ} [NeZero K]

/-- `n ↦ min (n-1) (K-1)` as an element of `Fin K`. -/
def cellNat (K : ℕ) [NeZero K] (n : ℕ) : Fin K :=
  ⟨min (n - 1) (K - 1), by have := NeZero.pos K; omega⟩

/-- The cell index of `x ∈ 𝕋^d` at resolution `K`. -/
noncomputable def cellIdx (K : ℕ) [NeZero K] (x : Torus d) : Fin d → Fin K :=
  fun j => cellNat K ⌈(K : ℝ) * secT x j⌉₊

/-- The corner `((aⱼ+1)/K)ⱼ` of the cell `a`. -/
noncomputable def cellPt (K : ℕ) (a : Fin d → Fin K) : Torus d :=
  liftT fun j => ((a j : ℝ) + 1) / K

theorem measurable_cellIdx : Measurable (cellIdx (d := d) K) :=
  measurable_pi_iff.mpr fun j => (measurable_from_top (f := cellNat K)).comp
    (Nat.measurable_ceil.comp (measurable_const.mul ((measurable_pi_apply j).comp measurable_secT)))

theorem secT_mem (x : Torus d) (j : Fin d) : secT x j ∈ Ioc (0 : ℝ) 1 := by
  have := ((AddCircle.measurableEquivIoc 1 0) (x j)).2
  show ((AddCircle.measurableEquivIoc 1 0) (x j) : ℝ) ∈ Ioc 0 1
  simpa using this

theorem cellNat_ceil_eq_iff {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (k : Fin K) :
    cellNat K ⌈(K : ℝ) * s⌉₊ = k ↔ s ∈ Ioc ((k : ℝ) / K) (((k : ℝ) + 1) / K) := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have h1 : 1 ≤ ⌈(K : ℝ) * s⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact mul_pos hK hs.1)
  have h2 : ⌈(K : ℝ) * s⌉₊ ≤ K := Nat.ceil_le.mpr (by
    calc (K : ℝ) * s ≤ K * 1 := by gcongr; exact hs.2
      _ = K := mul_one _)
  have e : (cellNat K ⌈(K : ℝ) * s⌉₊ : ℕ) = ⌈(K : ℝ) * s⌉₊ - 1 := by
    simp only [cellNat]; omega
  rw [Fin.ext_iff, e]
  constructor
  · intro h
    have hc : ⌈(K : ℝ) * s⌉₊ = k + 1 := by omega
    rw [Nat.ceil_eq_iff (by omega)] at hc
    simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at hc
    refine ⟨?_, ?_⟩
    · rw [div_lt_iff₀ hK]; linarith [hc.1]
    · rw [le_div_iff₀ hK]; linarith [hc.2]
  · rintro ⟨h3, h4⟩
    rw [div_lt_iff₀ hK] at h3
    rw [le_div_iff₀ hK] at h4
    have hc : ⌈(K : ℝ) * s⌉₊ = k + 1 := by
      rw [Nat.ceil_eq_iff (by omega)]
      simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith
    omega

theorem cellIdx_liftT {y : Fin d → ℝ} (hy : y ∈ unitBox (Fin d)) (a : Fin d → Fin K) :
    cellIdx K (liftT y) = a ↔ y ∈ univ.pi fun j => Ioc ((a j : ℝ) / K) (((a j : ℝ) + 1) / K) := by
  simp only [cellIdx, secT_liftT hy, funext_iff, Set.mem_pi, mem_univ, true_implies]
  exact forall_congr' fun j => cellNat_ceil_eq_iff (by simpa using hy j (mem_univ j)) (a j)

theorem cellIdx_cellPt (a : Fin d → Fin K) : cellIdx K (cellPt K a) = a := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hy : (fun j => ((a j : ℝ) + 1) / K) ∈ unitBox (Fin d) := fun j _ => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hK]; exact_mod_cast (a j).2
  rw [cellPt, cellIdx_liftT hy]
  intro j _
  refine ⟨?_, le_rfl⟩
  exact div_lt_div_of_pos_right (by linarith) hK

theorem volume_cell (a : Fin d → Fin K) :
    (haar d) {x | cellIdx K x = a} = ((K : ℝ≥0∞) ^ d)⁻¹ := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hm : MeasurableSet {x : Torus d | cellIdx K x = a} :=
    measurable_cellIdx (measurableSet_singleton a)
  rw [haar, ← (measurePreserving_liftT (ι := Fin d)).measure_preimage hm.nullMeasurableSet,
    Measure.restrict_apply (measurable_liftT hm)]
  have hset : liftT ⁻¹' {x : Torus d | cellIdx K x = a} ∩ unitBox (Fin d) =
      univ.pi fun j => Ioc ((a j : ℝ) / K) (((a j : ℝ) + 1) / K) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact (cellIdx_liftT h2 a).mp h1
    · intro h
      have hy : y ∈ unitBox (Fin d) := fun j _ => by
        obtain ⟨h3, h4⟩ := h j (mem_univ j)
        refine ⟨lt_of_le_of_lt (by positivity) h3, h4.trans ?_⟩
        rw [div_le_one hK]; exact_mod_cast (a j).2
      exact ⟨(cellIdx_liftT hy a).mpr h, hy⟩
  rw [hset, Real.volume_pi_Ioc]
  have : ∀ j, ENNReal.ofReal (((a j : ℝ) + 1) / K - (a j : ℝ) / K) = (K : ℝ≥0∞)⁻¹ := fun j => by
    rw [← sub_div, add_sub_cancel_left, one_div, ENNReal.ofReal_inv_of_pos hK, ENNReal.ofReal_natCast]
  simp_rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.inv_pow]

theorem dist_coe_le (u v : ℝ) : dist (u : UnitAddCircle) (v : UnitAddCircle) ≤ |u - v| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]
  simpa using round_le (u - v) 0

theorem dist_cellPt (x : Torus d) : dist x (cellPt K (cellIdx K x)) ≤ 1 / K := by
  have hK : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
  have hy : secT x ∈ unitBox (Fin d) := fun j _ => secT_mem x j
  have hc := (cellIdx_liftT hy (cellIdx K x)).mp (by rw [liftT_secT])
  rw [show dist x (cellPt K (cellIdx K x)) = dist (liftT (secT x)) (cellPt K (cellIdx K x)) by
    rw [liftT_secT]]
  refine (dist_pi_le_iff (by positivity)).mpr fun j => (dist_coe_le _ _).trans ?_
  obtain ⟨h1, h2⟩ := hc j (mem_univ j)
  rw [abs_le]
  constructor
  · have : ((cellIdx K x j : ℝ) + 1) / K - 1 / K = (cellIdx K x j : ℝ) / K := by ring
    linarith
  · have : 0 < 1 / (K : ℝ) := by positivity
    linarith

end SharpLSI
