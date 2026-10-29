import SharpSymmetricLSI.Infra.EntropyTensor
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Subadditivity of entropy on products, for unbounded integrable functions (plan, section 5)

`ent_prod_le`: for probability measures `P`, `Q` and a measurable `g ≥ 0` on `X × Y` with `g` and
`g log g` integrable on `P.prod Q`,
`entR (P.prod Q) g ≤ ∫ entR Q (g (x,·)) dP + ∫ entR P (g (·,y)) dQ`.
It is derived from the bounded `entR_prod_le` by the clipping `g_n = max (n+1)⁻¹ (min g (n+1))`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

/-- The clipping `max (n+1)⁻¹ (min t (n+1))`. -/
noncomputable def clipM (n : ℕ) (t : ℝ) : ℝ := max (((n : ℝ) + 1)⁻¹) (min t ((n : ℝ) + 1))

theorem continuous_clipM (n : ℕ) : Continuous (clipM n) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem inv_succ_le_one (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])

theorem clipM_ge (n : ℕ) (t : ℝ) : ((n : ℝ) + 1)⁻¹ ≤ clipM n t := le_max_left _ _

theorem clipM_pos (n : ℕ) (t : ℝ) : 0 < clipM n t :=
  lt_of_lt_of_le (by positivity) (clipM_ge n t)

theorem clipM_le_top (n : ℕ) (t : ℝ) : clipM n t ≤ (n : ℝ) + 1 :=
  max_le ((inv_succ_le_one n).trans (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])) (min_le_right _ _)

theorem clipM_le_add (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : clipM n t ≤ t + 1 :=
  max_le ((inv_succ_le_one n).trans (by linarith)) ((min_le_left _ _).trans (by linarith))

theorem clipM_eq {n : ℕ} {t : ℝ} (h1 : ((n : ℝ) + 1)⁻¹ ≤ t) (h2 : t ≤ (n : ℝ) + 1) :
    clipM n t = t := by
  unfold clipM; rw [min_eq_left h2, max_eq_right h1]

theorem tendsto_clipM {t : ℝ} (ht : 0 ≤ t) : Tendsto (fun n : ℕ => clipM n t) atTop (𝓝 t) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h2 : Tendsto (fun n : ℕ => min t ((n : ℝ) + 1)) atTop (𝓝 t) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈t⌉₊] with n hn
    have : t ≤ n := (Nat.le_ceil t).trans (by exact_mod_cast hn)
    rw [min_eq_left (by linarith)]
  simpa [clipM, max_eq_right ht] using h1.max h2

theorem mul_log_ge (t : ℝ) (ht : 0 ≤ t) : t - 1 ≤ t * Real.log t := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp
  · have := Real.one_sub_inv_le_log_of_pos h
    have h2 := mul_le_mul_of_nonneg_left this h.le
    have e : t * (1 - t⁻¹) = t - 1 := by field_simp
    linarith

theorem abs_mul_log_le_one {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) : |c * Real.log c| ≤ 1 := by
  rw [abs_le]
  have h1 := mul_log_ge c hc.le
  have h2 : c * Real.log c ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc.le (Real.log_nonpos hc.le hc1)
  constructor <;> linarith

theorem abs_mul_log_clipM (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |clipM n t * Real.log (clipM n t)| ≤ |t * Real.log t| + 1 := by
  have hm1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hc1 := inv_succ_le_one n
  have hcpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  by_cases hlow : t < ((n : ℝ) + 1)⁻¹
  · have : clipM n t = ((n : ℝ) + 1)⁻¹ := by
      unfold clipM; rw [max_eq_left]; exact (min_le_left _ _).trans hlow.le
    rw [this]
    linarith [abs_mul_log_le_one hcpos hc1, abs_nonneg (t * Real.log t)]
  by_cases hhigh : (n : ℝ) + 1 < t
  · have : clipM n t = (n : ℝ) + 1 := by
      unfold clipM; rw [min_eq_right hhigh.le, max_eq_right (hc1.trans hm1)]
    rw [this]
    have hl0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hm1
    have hlt : Real.log ((n : ℝ) + 1) ≤ Real.log t := Real.log_le_log (by linarith) hhigh.le
    have hl1 : 0 ≤ Real.log t := hl0.trans hlt
    rw [abs_of_nonneg (mul_nonneg (by linarith) hl0), abs_of_nonneg (mul_nonneg ht hl1)]
    have := mul_le_mul hhigh.le hlt hl0 ht
    linarith
  · push_neg at hlow hhigh
    rw [clipM_eq hlow hhigh]; linarith

theorem entR_nonneg_of_bdd {α : Type*} [MeasurableSpace α] {ρ : Measure α} [IsProbabilityMeasure ρ]
    {f : α → ℝ} (hf : AEStronglyMeasurable f ρ) {c C : ℝ} (hc : 0 < c) (hfc : ∀ z, c ≤ f z)
    (hfC : ∀ z, f z ≤ C) : 0 ≤ entR ρ f := by
  have hfi : Integrable f ρ := by
    refine Integrable.of_bound hf (max |C| 0) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hc (hfc z))]
    exact (hfC z).trans ((le_abs_self C).trans (le_max_left _ _))
  have hgi : Integrable (fun z => f z * Real.log (f z)) ρ :=
    Integrable.of_bound (Real.continuous_mul_log.comp_aestronglyMeasurable hf)
      (C * (|Real.log c| + |Real.log C|)) (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact abs_mul_log_le hc (hfc z) (hfC z))
  have := Real.convexOn_mul_log.map_integral_le (μ := ρ) (f := f) Real.continuous_mul_log.continuousOn
    isClosed_Ici (Eventually.of_forall fun z => (lt_of_lt_of_le hc (hfc z)).le) hfi hgi
  unfold entR
  linarith

section clip
variable {γ : Type*} [MeasurableSpace γ] {ρ : Measure γ} [IsProbabilityMeasure ρ]

theorem tendsto_entR_clip {f : γ → ℝ} (hf : Measurable f) (hf0 : ∀ z, 0 ≤ f z)
    (hfi : Integrable f ρ) (hfl : Integrable (fun z => f z * Real.log (f z)) ρ) :
    Tendsto (fun n : ℕ => entR ρ (fun z => clipM n (f z))) atTop (𝓝 (entR ρ f)) := by
  have hm : ∀ n : ℕ, Measurable fun z => clipM n (f z) := fun n =>
    (continuous_clipM n).measurable.comp hf
  have h1 : Tendsto (fun n : ℕ => ∫ z, clipM n (f z) * Real.log (clipM n (f z)) ∂ρ) atTop
      (𝓝 (∫ z, f z * Real.log (f z) ∂ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => |f z * Real.log (f z)| + 1)
      (fun n => (Real.continuous_mul_log.comp_aestronglyMeasurable (hm n).aestronglyMeasurable))
      (hfl.abs.add (integrable_const 1)) (fun n => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · rw [Real.norm_eq_abs]; exact abs_mul_log_clipM n (hf0 z)
    · exact (Real.continuous_mul_log.tendsto _).comp (tendsto_clipM (hf0 z))
  have h2 : Tendsto (fun n : ℕ => ∫ z, clipM n (f z) ∂ρ) atTop (𝓝 (∫ z, f z ∂ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => f z + 1)
      (fun n => (hm n).aestronglyMeasurable) (hfi.add (integrable_const 1))
      (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => tendsto_clipM (hf0 z))
    rw [Real.norm_eq_abs, abs_of_pos (clipM_pos n _)]
    exact clipM_le_add n (hf0 z)
  exact h1.sub ((Real.continuous_mul_log.tendsto _).comp h2)

end clip

section slice
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {P : Measure X} {Q : Measure Y}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

theorem tendsto_slice {g : X × Y → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgi : Integrable g (P.prod Q))
    (hgl : Integrable (fun z => g z * Real.log (g z)) (P.prod Q)) :
    Tendsto (fun n : ℕ => ∫ x, entR Q (fun y => clipM n (g (x, y))) ∂P) atTop
      (𝓝 (∫ x, entR Q (fun y => g (x, y)) ∂P)) := by
  have hcm : ∀ n : ℕ, Measurable fun z => clipM n (g z) := fun n =>
    (continuous_clipM n).measurable.comp hg
  set D : X → ℝ := fun x => (∫ y, (|g (x, y) * Real.log (g (x, y))| + 1) ∂Q) + 1 with hD
  have hDint : Integrable D P :=
    ((hgl.abs.add (integrable_const 1)).integral_prod_left).add (integrable_const 1)
  have hslL : ∀ᵐ x ∂P, Integrable (fun y => g (x, y) * Real.log (g (x, y))) Q :=
    hgl.prod_right_ae
  have hslI : ∀ᵐ x ∂P, Integrable (fun y => g (x, y)) Q := hgi.prod_right_ae
  refine tendsto_integral_of_dominated_convergence D (fun n => ?_) hDint (fun n => ?_) ?_
  · exact (integrable_entR_left (μ := P) (ν := Q) (hcm n) (c := ((n : ℝ) + 1)⁻¹)
      (C := (n : ℝ) + 1) (by positivity) (fun z => clipM_ge n _) (fun z => clipM_le_top n _)).1
  · filter_upwards [hslL] with x hx
    have hcx : Measurable fun y => clipM n (g (x, y)) := (hcm n).comp measurable_prodMk_left
    have hnn : 0 ≤ entR Q (fun y => clipM n (g (x, y))) :=
      entR_nonneg_of_bdd hcx.aestronglyMeasurable (by positivity) (fun y => clipM_ge n _)
        (fun y => clipM_le_top n _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    unfold entR
    have hb : Integrable (fun y => clipM n (g (x, y)) * Real.log (clipM n (g (x, y)))) Q := by
      refine Integrable.of_bound ((Real.continuous_mul_log.comp_aestronglyMeasurable
        hcx.aestronglyMeasurable)) (((n : ℝ) + 1) * (|Real.log ((n : ℝ) + 1)⁻¹| +
          |Real.log ((n : ℝ) + 1)|)) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      exact abs_mul_log_le (by positivity) (clipM_ge n _) (clipM_le_top n _)
    have h1 : ∫ y, clipM n (g (x, y)) * Real.log (clipM n (g (x, y))) ∂Q ≤
        ∫ y, (|g (x, y) * Real.log (g (x, y))| + 1) ∂Q :=
      integral_mono hb (hx.abs.add (integrable_const 1)) fun y =>
        (le_abs_self _).trans (abs_mul_log_clipM n (hg0 _))
    have h2 := mul_log_ge (∫ y, clipM n (g (x, y)) ∂Q)
      (integral_nonneg fun y => (clipM_pos n _).le)
    have hG0 : 0 ≤ ∫ y, clipM n (g (x, y)) ∂Q := integral_nonneg fun y => (clipM_pos n _).le
    simp only [hD]
    linarith
  · filter_upwards [hslL, hslI] with x hx hxi
    exact tendsto_entR_clip (ρ := Q) (f := fun y => g (x, y)) (hg.comp measurable_prodMk_left)
      (fun y => hg0 _) hxi hx

end slice

section main
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {P : Measure X} {Q : Measure Y}
  [IsProbabilityMeasure P] [IsProbabilityMeasure Q]

/-- **Subadditivity of entropy** on a product of probability spaces, for measurable `g ≥ 0` with
`g` and `g log g` integrable. -/
theorem ent_prod_le {g : X × Y → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z)
    (hgi : Integrable g (P.prod Q))
    (hgl : Integrable (fun z => g z * Real.log (g z)) (P.prod Q)) :
    entR (P.prod Q) g ≤ ∫ x, entR Q (fun y => g (x, y)) ∂P +
      ∫ y, entR P (fun x => g (x, y)) ∂Q := by
  have hcm : ∀ n : ℕ, Measurable fun z => clipM n (g z) := fun n =>
    (continuous_clipM n).measurable.comp hg
  have hle : ∀ n : ℕ, entR (P.prod Q) (fun z => clipM n (g z)) ≤
      ∫ x, entR Q (fun y => clipM n (g (x, y))) ∂P +
        ∫ y, entR P (fun x => clipM n (g (x, y))) ∂Q := fun n =>
    entR_prod_le (hcm n) (c := ((n : ℝ) + 1)⁻¹) (C := (n : ℝ) + 1) (by positivity)
      (fun z => clipM_ge n _) (fun z => clipM_le_top n _)
  have hT1 := tendsto_entR_clip (ρ := P.prod Q) hg hg0 hgi hgl
  have hT2 := tendsto_slice (P := P) (Q := Q) hg hg0 hgi hgl
  have hT3 := tendsto_slice (P := Q) (Q := P) (g := g ∘ Prod.swap) (hg.comp measurable_swap)
    (fun z => hg0 _) hgi.swap hgl.swap
  exact le_of_tendsto_of_tendsto' hT1 (hT2.add hT3) hle

end main

end SharpLSI.FL
