import SharpSymmetricLSI.Paper.AppAPicard3

/-!
# Lemma A.1, existence (4): the Picard iteration (lemma (b))

`ρ^{n+1}_t = e^{tΔ}ρ₀ + ∫_{(0,t]} ∇·e^{(t-u)Δ} N(ρ^n_u) du` (`t > 0`), `ρ^n_0 = ρ₀`, with the
modified flux `N`. All iterates are jointly measurable with `|ρ^n_t| ≤ 2M e^{μ₁t}`; on `[0,T]` the
iteration contracts in the weighted norm `sup_t e^{-μ₂ t} ‖·‖_∞`, so it converges everywhere to a
jointly measurable solution of the modified mild equation (`exists_modMild`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The Picard map of the modified mild equation. -/
noncomputable def picardMap (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ₀ : Torus d → ℝ)
    (η : ℝ → Torus d → ℝ) (t : ℝ) (x : Torus d) : ℝ :=
  if 0 < t then heatT t ρ₀ x + duhamel (fun u => modFlux V W (η u)) t x else ρ₀ x

/-- The Picard iterates. -/
noncomputable def picardSeq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ₀ : Torus d → ℝ) :
    ℕ → ℝ → Torus d → ℝ
  | 0 => fun _ => ρ₀
  | n + 1 => picardMap V W ρ₀ (picardSeq V W ρ₀ n)

theorem appA_integrable_of_abs_le {f : Torus d → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    Integrable f (haar d) :=
  (MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hb x)).integrable le_top

section Picard

variable (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hρ₀ : Measurable ρ₀) {M : ℝ}
  (hM : ∀ x, |ρ₀ x| ≤ M) {LV Cb : ℝ} (hLV0 : 0 ≤ LV) (hCb0 : 0 ≤ Cb)
  (hLV : ∀ x k, |lipGrad V x k| ≤ LV) (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb)

include hyp hρ₀ in
theorem measurable_picardMap {η : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η)) :
    Measurable (Function.uncurry (picardMap V W ρ₀ η)) := by
  have e : Function.uncurry (picardMap V W ρ₀ η) = fun p : ℝ × Torus d =>
      if 0 < p.1 then heatT p.1 ρ₀ p.2 + duhamel (fun u => modFlux V W (η u)) p.1 p.2
      else ρ₀ p.2 := rfl
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((measurable_heatT_joint hρ₀).add (measurable_duhamel fun k => measurable_modFlux hyp hη k))
    (hρ₀.comp measurable_snd)

include hyp hρ₀ in
theorem measurable_picardSeq (n : ℕ) : Measurable (Function.uncurry (picardSeq V W ρ₀ n)) := by
  induction n with
  | zero => exact hρ₀.comp measurable_snd
  | succ n ih => exact measurable_picardMap hyp hρ₀ ih

theorem section_measurable {η : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η)) (u : ℝ) :
    Measurable (η u) :=
  hη.comp measurable_prodMk_left

include hyp hρ₀ hM hLV hCb hLV0 hCb0 in
/-- One step of the a priori bound. -/
theorem abs_picardMap_le {η : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η))
    {K μ : ℝ} (hK : 0 ≤ K) (hμ : 0 < μ) (hηb : ∀ u, 0 ≤ u → ∀ y, |η u y| ≤ K * Real.exp (μ * u))
    {t : ℝ} (ht : 0 < t) (x : Torus d) :
    |picardMap V W ρ₀ η t x| ≤ M + d * ((LV + Cb) * K) * Real.exp (μ * t) / Real.sqrt μ := by
  have hA : 0 ≤ LV + Cb := add_nonneg hLV0 hCb0
  unfold picardMap
  rw [if_pos ht]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact abs_heatT_le ht hρ₀.aestronglyMeasurable (Eventually.of_forall hM) x
  · have := abs_duhamel_le (N := fun u => modFlux V W (η u)) ht (mul_nonneg hA hK) hμ
      (fun u hu y k => by
        refine (abs_modFlux_le hLV hCb hyp
          (appA_integrable_of_abs_le (section_measurable hη u) (hηb u hu.1.le)) y k).trans ?_
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hηb u hu.1.le y) hA) x
    simpa using this

include hyp hρ₀ hLV hCb hLV0 hCb0 in
/-- One step of the contraction. -/
theorem abs_picardMap_sub_le {η ζ : ℝ → Torus d → ℝ} (hη : Measurable (Function.uncurry η))
    (hζ : Measurable (Function.uncurry ζ)) {T K δ ν : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hν : 0 < ν)
    (hηb : ∀ u ∈ Icc 0 T, ∀ y, |η u y| ≤ K) (hζb : ∀ u ∈ Icc 0 T, ∀ y, |ζ u y| ≤ K)
    (hd : ∀ u ∈ Icc 0 T, ∀ y, |η u y - ζ u y| ≤ δ * Real.exp (ν * u))
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (x : Torus d) :
    |picardMap V W ρ₀ η t x - picardMap V W ρ₀ ζ t x| ≤
      d * ((LV + Cb + 2 * Cb * K) * δ) * Real.exp (ν * t) / Real.sqrt ν := by
  have hA : 0 ≤ LV + Cb := add_nonneg hLV0 hCb0
  unfold picardMap
  rw [if_pos ht, if_pos ht, add_sub_add_left_eq_sub]
  have hmη := fun k => measurable_modFlux hyp hη k
  have hmζ := fun k => measurable_modFlux hyp hζ k
  have hIcc : ∀ u ∈ Ioc 0 t, u ∈ Icc 0 T := fun u hu => ⟨hu.1.le, hu.2.trans htT⟩
  have hbη : ∀ u ∈ Ioc 0 t, ∀ y k, |modFlux V W (η u) y k| ≤ (LV + Cb) * K * Real.exp (0 * u) :=
    fun u hu y k => by
      rw [zero_mul, Real.exp_zero, mul_one]
      refine (abs_modFlux_le hLV hCb hyp
        (appA_integrable_of_abs_le (section_measurable hη u) (hηb u (hIcc u hu))) y k).trans ?_
      exact mul_le_mul_of_nonneg_left (hηb u (hIcc u hu) y) hA
  have hbζ : ∀ u ∈ Ioc 0 t, ∀ y k, |modFlux V W (ζ u) y k| ≤ (LV + Cb) * K * Real.exp (0 * u) :=
    fun u hu y k => by
      rw [zero_mul, Real.exp_zero, mul_one]
      refine (abs_modFlux_le hLV hCb hyp
        (appA_integrable_of_abs_le (section_measurable hζ u) (hζb u (hIcc u hu))) y k).trans ?_
      exact mul_le_mul_of_nonneg_left (hζb u (hIcc u hu) y) hA
  rw [duhamel_sub hmη hmζ ht (mul_nonneg hA hK) le_rfl hbη hbζ]
  have hL : 0 ≤ LV + Cb + 2 * Cb * K := by positivity
  have key : ∀ u ∈ Ioc 0 t, ∀ y k, |modFlux V W (η u) y k - modFlux V W (ζ u) y k| ≤
      (LV + Cb + 2 * Cb * K) * δ * Real.exp (ν * u) := fun u hu y k => by
    have hu := hIcc u hu
    have hiη := appA_integrable_of_abs_le (section_measurable hη u) (hηb u hu)
    have hiζ := appA_integrable_of_abs_le (section_measurable hζ u) (hζb u hu)
    have hint : ∫ z, |η u z - ζ u z| ∂haar d ≤ δ * Real.exp (ν * u) := by
      have := integral_mono_of_nonneg (μ := haar d) (Eventually.of_forall fun z => abs_nonneg _)
        (integrable_const (δ * Real.exp (ν * u))) (Eventually.of_forall fun z => hd u hu z)
      simpa using this
    refine (abs_modFlux_sub_le hLV hCb hyp hiη hiζ y k).trans ?_
    have hδe : 0 ≤ δ * Real.exp (ν * u) := by positivity
    calc (LV + Cb) * |η u y - ζ u y| + |ζ u y| * (2 * Cb * ∫ z, |η u z - ζ u z| ∂haar d)
        ≤ (LV + Cb) * (δ * Real.exp (ν * u)) + K * (2 * Cb * (δ * Real.exp (ν * u))) := by
          gcongr
          · exact hd u hu y
          · exact hζb u hu y
      _ = (LV + Cb + 2 * Cb * K) * δ * Real.exp (ν * u) := by ring
  have := abs_duhamel_le (N := fun u y k => modFlux V W (η u) y k - modFlux V W (ζ u) y k) ht
    (mul_nonneg hL hδ) hν key x
  simpa using this

end Picard

end SharpLSI
