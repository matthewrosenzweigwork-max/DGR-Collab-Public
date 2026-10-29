import SharpSymmetricLSI.Paper.Sec5_2

/-!
# R19 (Lemma 5.2), part 3: joint coercivity (5.8)

For a scaled centered kernel `sK` whose mean-field functional is coercive,
`c' H(ρ|μ) ≤ H(ρ|μ) + s J(ρ)`, and a symmetric `ν` with `H_0 = H(ν|μ^{⊗N}) < ∞`:
`H_0 + s E_ν U_N ≥ (c'/4) H_0 - C`, uniformly in `N` (`joint_coercive`).

Route (manuscript proof of Lemma 5.2): for `N ≥ 3` take `ℓ = ⌊N/2⌋`, `M = N - ℓ`, `k = 2`,
`B = sK/2`, `δ = 1/2` in (5.5); `E_ν B(ρ_j^{⊗2}) = E_ν sJ(ρ_j) ≥ -(1 - c'/2) h_j`; monotonicity of
`h_j` gives `(N/ℓ) ∑_{j<ℓ} h_j ≤ H_0`; the `√H_0` error is absorbed. For `N ≤ 2`, `|U_N| ≤ 2‖K‖_∞`.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section joint
variable (hyp : Hyp V W KV KW)
include hyp

theorem abs_Ucentered_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : ∀ x y, |centeredKernel W μ x y| ≤ B) (N : ℕ) (X : Config N d) :
    |Ucentered W μ N X| ≤ N * B / 2 := by
  unfold Ucentered
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  have hN : (0 : ℝ) < N := by exact_mod_cast h
  rw [abs_mul, abs_of_pos (by positivity)]
  have hs : |∑ i, ∑ j, centeredKernel W μ (X i) (X j)| ≤ N * N * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, ∑ j, |centeredKernel W μ (X i) (X j)| ≤ ∑ _i : Fin N, ∑ _j : Fin N, B :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hB _ _
      _ = N * N * B := by simp; ring
  calc 1 / (2 * (N : ℝ)) * |∑ i, ∑ j, centeredKernel W μ (X i) (X j)| ≤
      1 / (2 * (N : ℝ)) * (N * N * B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = N * B / 2 := by field_simp

/-- `E_ν B(ρ_j^{⊗2}) = E_ν s J(ρ_j)` for `B = sK/2`. -/
theorem condProductMean_eq_J (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (s : ℝ) {N : ℕ}
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) :
    condProductMean ν 2 (fun z => s * centeredKernel W μ (z 0) (z 1) / 2) j =
      ∫ X, s * Jfun W μ (condNext ν j hj (past j hj.le X)) ∂ν := by
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μ
  unfold condProductMean
  rw [dif_pos hj]
  congr 1
  funext X
  have hm : Measurable (Function.uncurry fun x y => s * centeredKernel W μ x y / 2) :=
    ((measurable_centeredKernel hyp μ).const_mul s).div_const 2
  have hb : ∀ x y, |s * centeredKernel W μ x y / 2| ≤ |s| * BK / 2 := fun x y => by
    rw [abs_div, abs_mul, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hBK x y) (abs_nonneg _))
      zero_le_two
  rw [integral_pi_two_S5 (F := fun x y => s * centeredKernel W μ x y / 2) hm hb]
  unfold Jfun interE
  simp_rw [integral_div, integral_const_mul]
  ring

/-- `∑_{j<ℓ} E_ν B(ρ_j^{⊗2}) ≥ -(1 - c'/2) ∑_{j<ℓ} h_j`. -/
theorem sum_condProductMean_ge (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {s c' : ℝ}
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ)
    {N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ ≤ N) :
    -((1 - c' / 2) * ∑ j ∈ Finset.range ℓ, (hCondT ν μ j).toReal) ≤
      ∑ j ∈ Finset.range ℓ, condProductMean ν 2 (fun z => s * centeredKernel W μ (z 0) (z 1) / 2) j := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjN : j < N := by simp at hj; omega
  rw [condProductMean_eq_J hyp μ s ν hjN]
  have ha : 0 ≤ 1 - c' / 2 := by linarith
  have hT : hCondT ν μ j = hCond ν μ j hjN := by unfold hCondT; rw [dif_pos hjN]
  have hfin : hCond ν μ j hjN ≠ ⊤ := hT ▸ hCondT_ne_top μ ν hH j
  rw [hT]
  refine neg_le_integral_of_le ha (H := fun X => klDiv (condNext ν j hjN (past j hjN.le X)) μ)
    (fun X => ?_) hfin
  set ρ := condNext ν j hjN (past j hjN.le X)
  by_cases hρ : klDiv ρ μ = ⊤
  · rw [hρ, ENNReal.mul_top (by simp; linarith)]
    exact le_top
  · have h1 := hcoer ρ inferInstance hρ
    have h0 : 0 ≤ (klDiv ρ μ).toReal := ENNReal.toReal_nonneg
    have h2 : -(s * Jfun W μ ρ) ≤ (1 - c' / 2) * (klDiv ρ μ).toReal := by nlinarith
    calc ENNReal.ofReal (-(s * Jfun W μ ρ)) ≤ ENNReal.ofReal ((1 - c' / 2) * (klDiv ρ μ).toReal) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (1 - c' / 2) * klDiv ρ μ := by
          rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_toReal hρ]

/-- **Joint coercivity** (5.8), uniformly in `N`. -/
theorem joint_coercive (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {s c' : ℝ} (hs : 0 ≤ s)
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        c' / 4 * (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal - C ≤
          (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal + s * ∫ X, Ucentered W μ N X ∂ν := by
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp μ
  set B : (Fin 2 → Torus d) → ℝ := fun z => s * centeredKernel W μ (z 0) (z 1) / 2 with hBdef
  have hBm : Measurable B := by
    have h := (((measurable_centeredKernel hyp μ).comp ((measurable_pi_apply 0).prodMk
      (measurable_pi_apply 1) : Measurable fun z : Fin 2 → Torus d => (z 0, z 1))).const_mul s).div_const 2
    exact h
  have hBb : ∃ c, ∀ z, |B z| ≤ c := ⟨|s| * BK / 2, fun z => by
    simp only [hBdef]
    rw [abs_div, abs_mul, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hBK _ _) (abs_nonneg _))
      zero_le_two⟩
  obtain ⟨C1, hC1⟩ := conditional_empirical_aux μ 2 B hBm hBb
  set C1' := max C1 0
  have hC1' : 0 ≤ C1' := le_max_right _ _
  set BK' := max BK 0
  refine ⟨3 * C1' + 18 * C1' ^ 2 / c' + s * (2 * BK'), fun N hN ν hν hsym hH => ?_⟩
  set P := Measure.pi fun _ : Fin N => μ
  set H0 := (klDiv ν P).toReal
  have hH0 : 0 ≤ H0 := ENNReal.toReal_nonneg
  have hUb : ∀ X, |Ucentered W μ N X| ≤ N * BK' / 2 := fun X =>
    (abs_Ucentered_le hyp μ hBK N X).trans (by
      have := le_max_left BK 0
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith)
  have hUm := measurable_Ucentered hyp μ N
  have hUi : Integrable (Ucentered W μ N) ν :=
    Integrable.of_bound hUm.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hUb X)
  have hextra : 0 ≤ 3 * C1' + 18 * C1' ^ 2 / c' := by positivity
  by_cases hN3 : N ≤ 2
  · -- few particles: `|U_N| ≤ ‖K‖_∞`
    have hE : |∫ X, Ucentered W μ N X ∂ν| ≤ N * BK' / 2 := by
      have := norm_integral_le_of_norm_le_const (μ := ν)
        (Filter.Eventually.of_forall fun X => (show ‖Ucentered W μ N X‖ ≤ N * BK' / 2 by
          rw [Real.norm_eq_abs]; exact hUb X))
      simpa [Real.norm_eq_abs] using this
    have hNB : (N : ℝ) * BK' / 2 ≤ 2 * BK' := by
      have : (N : ℝ) ≤ 2 := by exact_mod_cast hN3
      have := le_max_right BK 0
      nlinarith
    have h1 : -(s * (2 * BK')) ≤ s * ∫ X, Ucentered W μ N X ∂ν := by
      have := neg_le_of_abs_le (hE.trans hNB)
      nlinarith
    nlinarith
  · push_neg at hN3
    set ℓ := N / 2 with hℓdef
    set M := N - ℓ with hMdef
    have hℓN : ℓ ≤ N := Nat.div_le_self _ _
    have hℓ1 : 1 ≤ ℓ := by omega
    have hNM : N - M = ℓ := by omega
    have hMN : M ≤ N := Nat.sub_le _ _
    have h2M : 2 ≤ M := by omega
    have hδ : (1 / 2 : ℝ) ≤ (M : ℝ) / N := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      rw [le_div_iff₀ hNpos]
      have : (N : ℝ) ≤ 2 * M := by exact_mod_cast (show N ≤ 2 * M by omega)
      linarith
    have hN3ℓ : (N : ℝ) ≤ 3 * ℓ := by exact_mod_cast (show N ≤ 3 * ℓ by omega)
    have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast hℓ1
    -- (5.5)
    have h55 := hC1 N M (1 / 2) ν hsym hH hMN h2M (by norm_num) hδ
    rw [hNM] at h55
    set E := ∫ X, empiricalTensor 2 B X ∂ν
    set Sc := ∑ j ∈ Finset.range ℓ, condProductMean ν 2 B j
    set S := ∑ j ∈ Finset.range ℓ, (hCondT ν μ j).toReal
    -- the conditional mean-field lower bound
    have hSc : -((1 - c' / 2) * S) ≤ Sc := sum_condProductMean_ge hyp μ hc'0 hc'1 hcoer ν hH hℓN
    -- monotonicity: `N S ≤ ℓ H_0`
    have hS : (N : ℝ) * S ≤ ℓ * H0 := by
      have hmono := mul_sum_range_le_of_mono (r := fun j => (hCondT ν μ j).toReal) hℓN
        (fun i i' hii hi' => ENNReal.toReal_mono (hCondT_ne_top μ ν hH i')
          (hCondT_mono μ ν hsym hH hii hi'))
      have hchain : ∑ j ∈ Finset.range N, (hCondT ν μ j).toReal = H0 := by
        rw [← ENNReal.toReal_sum (fun j _ => hCondT_ne_top μ ν hH j), chain_rule μ ν hH]
      rwa [hchain] at hmono
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    -- `s E_ν U_N = N E`
    have hUE : s * ∫ X, Ucentered W μ N X ∂ν = N * E := by
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1
      funext X
      have e := mul_empiricalTensor_two (fun x y => s * centeredKernel W μ x y) X
      rw [show (N : ℝ) * empiricalTensor 2 B X = _ from e]
      unfold Ucentered
      rw [Finset.mul_sum, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    -- the error term
    set u := Real.sqrt (H0 / (1 / 2))
    have hu0 : 0 ≤ u := Real.sqrt_nonneg _
    have hu2 : u ^ 2 = 2 * H0 := by
      rw [Real.sq_sqrt (by positivity)]; ring
    have hlE : -((1 - c' / 2) * S) - C1' * (1 + u) ≤ ℓ * E := by
      have h55' : |Sc - ℓ * E| ≤ C1 * (1 + u) := h55
      have := (abs_le.mp h55').2
      have : C1 * (1 + u) ≤ C1' * (1 + u) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith
    -- combine: `ℓ (N E) ≥ -ℓ (1 - c'/2) H_0 - 3ℓ C1' (1 + u)`
    have hcomb : (ℓ : ℝ) * (N * E) ≥ ℓ * (-((1 - c' / 2) * H0) - 3 * C1' * (1 + u)) := by
      have ha : 0 ≤ 1 - c' / 2 := by linarith
      have e1 : (N : ℝ) * (ℓ * E) ≥ N * (-((1 - c' / 2) * S) - C1' * (1 + u)) :=
        mul_le_mul_of_nonneg_left hlE (Nat.cast_nonneg _)
      have e2 : (N : ℝ) * ((1 - c' / 2) * S) ≤ ℓ * ((1 - c' / 2) * H0) := by
        nlinarith [mul_le_mul_of_nonneg_left hS ha]
      have e3 : (N : ℝ) * (C1' * (1 + u)) ≤ 3 * ℓ * (C1' * (1 + u)) :=
        mul_le_mul_of_nonneg_right hN3ℓ (by positivity)
      nlinarith
    have hNE : -((1 - c' / 2) * H0) - 3 * C1' * (1 + u) ≤ N * E :=
      le_of_mul_le_mul_left (by linarith [hcomb]) hℓpos
    -- absorb `3 C1' u ≤ (c'/4) H_0 + 18 C1'² / c'`
    have hab : 3 * C1' * u ≤ c' / 4 * H0 + 18 * C1' ^ 2 / c' := by
      have hsq := sq_nonneg (c' * u - 12 * C1')
      have hcu : c' ^ 2 * u ^ 2 = 2 * c' ^ 2 * H0 := by rw [hu2]; ring
      have h1 : (3 * C1' * u - c' / 4 * H0) * c' ≤ 18 * C1' ^ 2 := by nlinarith [hsq, hcu]
      have h2 := (le_div_iff₀ hc'0).mpr h1
      linarith
    have hsBK : 0 ≤ s * (2 * BK') := mul_nonneg hs (by positivity)
    rw [hUE]
    nlinarith

end joint

end SharpLSI
