import DGPS.Lipschitz.T01SymmetricLower
import DGPS.Particle.ConditionalProducts
import SharpSymmetricLSI.Paper.Sec5_4

/-!
# Uniform reference moments from direct mean-field entropy coercivity

The conditional-entropy argument of the existing `Sec5_3` and `Sec5_4` proofs uses only
measurability and boundedness of the centered kernel. These versions retain those exact inputs
instead of the old semiconvex interaction wrapper. Mean-field coercivity is a genuine upstream
inequality; neither joint particle coercivity nor a uniform partition bound is assumed.
-/

open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace DGPS.Lipschitz.ReferenceMoments

open SharpLSI

variable {d : ℕ} {W : Torus d → Torus d → ℝ}

theorem measurable_Ucentered {μ : Measure (Torus d)}
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ))) (N : ℕ) :
    Measurable (Ucentered W μ N) := by
  unfold Ucentered
  exact (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    hKm.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))).const_mul _

theorem abs_Ucentered_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {B : ℝ}
    (hB : ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B) (N : ℕ) (X : Config N d) :
    |Ucentered W μ N X| ≤ N * B / 2 := by
  unfold Ucentered
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  have hN : (0 : ℝ) < N := by exact_mod_cast h
  rw [abs_mul, abs_of_pos (by positivity)]
  have hs : |∑ i, ∑ j, SharpLSI.centeredKernel W μ (X i) (X j)| ≤ N * N * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, ∑ j, |SharpLSI.centeredKernel W μ (X i) (X j)| ≤ ∑ _i : Fin N, ∑ _j : Fin N, B :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hB _ _
      _ = N * N * B := by simp; ring
  calc 1 / (2 * (N : ℝ)) * |∑ i, ∑ j, SharpLSI.centeredKernel W μ (X i) (X j)| ≤
      1 / (2 * (N : ℝ)) * (N * N * B) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = N * B / 2 := by field_simp

/-- `E_ν B(ρ_j^{⊗2}) = E_ν s J(ρ_j)` for `B = sK/2`. -/
theorem condProductMean_eq_J (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B) (s : ℝ) {N : ℕ}
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) :
    condProductMean ν 2 (fun z => s * SharpLSI.centeredKernel W μ (z 0) (z 1) / 2) j =
      ∫ X, s * Jfun W μ (condNext ν j hj (past j hj.le X)) ∂ν := by
  obtain ⟨BK, hBK⟩ := hKb
  unfold condProductMean
  rw [dif_pos hj]
  congr 1
  funext X
  have hm : Measurable (Function.uncurry fun x y => s * SharpLSI.centeredKernel W μ x y / 2) :=
    ((hKm).const_mul s).div_const 2
  have hb : ∀ x y, |s * SharpLSI.centeredKernel W μ x y / 2| ≤ |s| * BK / 2 := fun x y => by
    rw [abs_div, abs_mul, abs_two]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hBK x y) (abs_nonneg _))
      zero_le_two
  rw [integral_pi_two_S5 (F := fun x y => s * SharpLSI.centeredKernel W μ x y / 2) hm hb]
  unfold Jfun interE
  simp_rw [integral_div, integral_const_mul]
  ring

/-- `∑_{j<ℓ} E_ν B(ρ_j^{⊗2}) ≥ -(1 - c'/2) ∑_{j<ℓ} h_j`. -/
theorem sum_condProductMean_ge (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B) {s c' : ℝ}
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ)
    {N : ℕ} (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ ≤ N) :
    -((1 - c' / 2) * ∑ j ∈ Finset.range ℓ, (hCondT ν μ j).toReal) ≤
      ∑ j ∈ Finset.range ℓ, condProductMean ν 2 (fun z => s * SharpLSI.centeredKernel W μ (z 0) (z 1) / 2) j := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjN : j < N := by simp at hj; omega
  rw [condProductMean_eq_J μ hKm hKb s ν hjN]
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
theorem joint_coercive (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B) {s c' : ℝ} (hs : 0 ≤ s)
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Config N d), IsProbabilityMeasure ν →
      IsSymmetricMeasure ν → klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤ →
        c' / 4 * (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal - C ≤
          (klDiv ν (Measure.pi fun _ : Fin N => μ)).toReal + s * ∫ X, Ucentered W μ N X ∂ν := by
  obtain ⟨BK, hBK⟩ := hKb
  set B : (Fin 2 → Torus d) → ℝ := fun z => s * SharpLSI.centeredKernel W μ (z 0) (z 1) / 2 with hBdef
  have hBm : Measurable B := by
    have h := (((hKm).comp ((measurable_pi_apply 0).prodMk
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
    (abs_Ucentered_le μ hBK N X).trans (by
      have := le_max_left BK 0
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith)
  have hUm := measurable_Ucentered hKm N
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
    have hSc : -((1 - c' / 2) * S) ≤ Sc :=
      sum_condProductMean_ge μ hKm ⟨BK, hBK⟩ hc'0 hc'1 hcoer ν hH hℓN
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
      have e := mul_empiricalTensor_two (fun x y => s * SharpLSI.centeredKernel W μ x y) X
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


theorem log_partition_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B) {s c' : ℝ} (hs : 0 ≤ s)
    (hc'0 : 0 < c') (hc'1 : c' ≤ 1)
    (hcoer : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c' * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + s * Jfun W μ ρ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Real.log (∫ X, exp (-(s * Ucentered W μ N X)) ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  obtain ⟨C, hC⟩ := joint_coercive μ hKm hKb hs hc'0 hc'1 hcoer
  refine ⟨C, fun N hN => ?_⟩
  set P := Measure.pi fun _ : Fin N => μ
  obtain ⟨BK, hBK⟩ := hKb
  have hUm := measurable_Ucentered hKm N
  have hUb := abs_Ucentered_le μ hBK N
  set f : Config N d → ℝ := fun X => -(s * Ucentered W μ N X) with hf
  have hfm : Measurable f := (hUm.const_mul s).neg
  have hfB : ∀ X, |f X| ≤ s * (N * BK / 2) := fun X => by
    simp only [hf, abs_neg, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (hUb X) hs
  have hfB' : ∀ X, |-f X| ≤ s * (N * BK / 2) := fun X => by rw [abs_neg]; exact hfB X
  have hei : Integrable (fun X => exp (f X)) P :=
    Integrable.of_bound (measurable_exp.comp hfm).aestronglyMeasurable (exp (s * (N * BK / 2)))
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (hfB X)))
  haveI hQ : IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hei
  set Q := P.tilted f
  -- `Q` is symmetric and of finite entropy relative to `μ^{⊗N}`
  have hsym : IsSymmetricMeasure Q :=
    isSymmetricMeasure_tilted μ hfm fun σ X => by simp only [hf, Ucentered_comp_perm_S5]
  have hback : Q.tilted (fun X => -f X) = P := by
    rw [tilted_tilted hei]
    have : (f + fun X => -f X) = 0 := by funext X; simp
    rw [this, tilted_zero]
  have hQP : klDiv Q P ≠ ⊤ := by
    have h0 : klDiv Q Q ≠ ⊤ := by simp
    have := (klDiv_tilted (ρ := Q) (ν := Q) (f := fun X => -f X) hfm.neg hfB' h0).1
    rwa [hback] at this
  -- the exact identity at `ν = Q`
  have hid := (klDiv_tilted (ρ := Q) (ν := P) (f := f) hfm hfB hQP).2
  rw [klDiv_self, ENNReal.toReal_zero] at hid
  have hJ := hC N hN Q hQ hsym hQP
  have hH0 : 0 ≤ (klDiv Q P).toReal := ENNReal.toReal_nonneg
  have hint : ∫ X, f X ∂Q = -(s * ∫ X, Ucentered W μ N X ∂Q) := by
    simp only [hf]; rw [integral_neg, integral_const_mul]
  rw [hint] at hid
  have : c' / 4 * (klDiv Q P).toReal ≥ 0 := by positivity
  linarith


theorem integral_Ucentered (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B)
    (hcenter : ∀ x, ∫ y, SharpLSI.centeredKernel W μ x y ∂μ = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, Ucentered W μ N X ∂Measure.pi (fun _ : Fin N => μ) =
      (∫ x, SharpLSI.centeredKernel W μ x x ∂μ) / 2 := by
  obtain ⟨B, hB⟩ := hKb
  have hij : ∀ i j : Fin N, ∫ X, SharpLSI.centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) =
      if i = j then ∫ x, SharpLSI.centeredKernel W μ x x ∂μ else 0 := by
    intro i j
    split_ifs with h
    · subst h
      have hm : Measurable fun x => SharpLSI.centeredKernel W μ x x := hKm.comp (measurable_id.prodMk measurable_id)
      calc ∫ X, SharpLSI.centeredKernel W μ (X i) (X i) ∂Measure.pi (fun _ : Fin N => μ)
          = ∫ x, SharpLSI.centeredKernel W μ x x ∂((Measure.pi fun _ : Fin N => μ).map fun X => X i) :=
            (integral_map (μ := Measure.pi fun _ : Fin N => μ) (φ := fun X : Config N d => X i)
              (f := fun x => SharpLSI.centeredKernel W μ x x) (measurable_pi_apply i).aemeasurable
              hm.aestronglyMeasurable).symm
        _ = _ := by rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
    · have hp : Measurable fun X : Config N d => (X i, X j) := by fun_prop
      have := integral_map (μ := Measure.pi fun _ : Fin N => μ) hp.aemeasurable
        hKm.aestronglyMeasurable
      simp only [Function.uncurry] at this
      rw [← this, map_pair_pi h, integral_prod (fun q : Torus d × Torus d =>
        SharpLSI.centeredKernel W μ q.1 q.2) (integrable_of_bdd hKm fun q => hB q.1 q.2)]
      simp only
      simp_rw [hcenter]
      simp
  have hint : ∀ i j : Fin N, Integrable (fun X : Config N d => SharpLSI.centeredKernel W μ (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) := fun i j =>
    integrable_of_bdd (hKm.comp (by fun_prop : Measurable fun X : Config N d => (X i, X j)))
      fun X => hB _ _
  have hsum : ∫ X, ∑ i, ∑ j, SharpLSI.centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) =
      ∑ i, ∑ j, ∫ X, SharpLSI.centeredKernel W μ (X i) (X j) ∂Measure.pi (fun _ : Fin N => μ) := by
    rw [integral_finset_sum (μ := Measure.pi fun _ : Fin N => μ) Finset.univ
      (f := fun i X => ∑ j, SharpLSI.centeredKernel W μ (X i) (X j)) fun i _ =>
        integrable_finset_sum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_finset_sum (μ := Measure.pi fun _ : Fin N => μ) Finset.univ
      (f := fun j X => SharpLSI.centeredKernel W μ (X i) (X j)) fun j _ => hint i j
  unfold Ucentered
  rw [integral_const_mul, hsum]
  simp_rw [hij]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp

/-- Genuine mean-field entropy coercivity gives a bounded centered normalizer and a uniform
moment of its normalized density, with an exponent strictly greater than one. -/
theorem uniform_log_and_density_moments (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hKm : Measurable (Function.uncurry (SharpLSI.centeredKernel W μ)))
    (hKb : ∃ B, ∀ x y, |SharpLSI.centeredKernel W μ x y| ≤ B)
    (hcenter : ∀ x, ∫ y, SharpLSI.centeredKernel W μ x y ∂μ = 0)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + Jfun W μ ρ) :
    ∃ C p : ℝ, 0 ≤ C ∧ 1 < p ∧ ∀ N : ℕ, 1 ≤ N →
      |Real.log (centeredPartition W μ N)| ≤ C ∧
      ∫ X, (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p
        ∂Measure.pi (fun _ : Fin N => μ) ≤ C := by
  obtain ⟨BK, hBK⟩ := hKb
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK default default)
  have hco1 : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + 1 * Jfun W μ ρ := by
    simpa only [one_mul] using hc
  let p : ℝ := 1 + c / 2
  have hp1 : 1 < p := by dsimp [p]; linarith
  have hcop : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ → klDiv ρ μ ≠ ⊤ →
      c / 2 * (klDiv ρ μ).toReal ≤ (klDiv ρ μ).toReal + p * Jfun W μ ρ := by
    intro ρ hρ hfin
    have h1 := hc ρ hρ hfin
    have h0 : 0 ≤ (klDiv ρ μ).toReal := ENNReal.toReal_nonneg
    dsimp [p]
    nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + c / 2),
      mul_nonneg (sq_nonneg c) h0]
  obtain ⟨C1, hC1⟩ := log_partition_le μ hKm ⟨BK, hBK⟩ zero_le_one hc0 hc1 hco1
  obtain ⟨Cp, hCp⟩ := log_partition_le μ hKm ⟨BK, hBK⟩
    (by linarith : 0 ≤ p) (by linarith : 0 < c / 2) (by linarith : c / 2 ≤ 1) hcop
  let CA := max C1 (BK / 2)
  let C := max CA (exp (Cp + p * CA))
  have hCA0 : 0 ≤ CA := le_trans (by positivity) (le_max_right _ _)
  refine ⟨C, p, hCA0.trans (le_max_left _ _), hp1, fun N hN => ?_⟩
  let P := Measure.pi fun _ : Fin N => μ
  have hUm := measurable_Ucentered hKm N
  have hUb := abs_Ucentered_le μ hBK N
  have hlogK : |Real.log (centeredPartition W μ N)| ≤ CA := by
    have hup : Real.log (centeredPartition W μ N) ≤ C1 := by
      simpa only [centeredPartition, one_mul] using hC1 N hN
    have hlo := neg_integral_le_log_integral_exp (P := P) hUm hUb
    rw [integral_Ucentered μ hKm ⟨BK, hBK⟩ hcenter hN] at hlo
    have hdiag : |∫ x, SharpLSI.centeredKernel W μ x x ∂μ| ≤ BK :=
      abs_integral_le_of_bdd fun x => hBK x x
    rw [abs_le]
    constructor
    · have := (abs_le.mp hdiag).2
      have := le_max_right C1 (BK / 2)
      change -max C1 (BK / 2) ≤ _
      unfold centeredPartition
      linarith
    · exact hup.trans (le_max_left _ _)
  refine ⟨hlogK.trans (le_max_left _ _), ?_⟩
  have hK : 0 < centeredPartition W μ N := by
    unfold centeredPartition
    exact integral_exp_pos (integrable_of_bdd (measurable_exp.comp hUm.neg)
      (C := exp (N * BK / 2)) fun X => by
        rw [abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((neg_le_abs _).trans (hUb X)))
  have hZp : 0 < ∫ X, exp (-(p * Ucentered W μ N X)) ∂P := by
    refine integral_exp_pos (integrable_of_bdd ((measurable_exp.comp (hUm.const_mul p).neg))
      (C := exp (p * (N * BK / 2))) fun X => ?_)
    rw [abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have := neg_le_abs (Ucentered W μ N X)
    have := hUb X
    nlinarith
  have hrw : ∀ X, (exp (-Ucentered W μ N X) / centeredPartition W μ N) ^ p =
      exp (-(p * Ucentered W μ N X)) / centeredPartition W μ N ^ p := by
    intro X
    rw [Real.div_rpow (exp_pos _).le hK.le, ← Real.exp_mul]
    ring_nf
  simp_rw [hrw]
  rw [integral_div]
  have hlog : Real.log ((∫ X, exp (-(p * Ucentered W μ N X)) ∂P) /
      centeredPartition W μ N ^ p) ≤ Cp + p * CA := by
    rw [Real.log_div hZp.ne' (Real.rpow_pos_of_pos hK p).ne', Real.log_rpow hK]
    have := hCp N hN
    have := (abs_le.mp hlogK).1
    nlinarith
  have hpos : 0 < (∫ X, exp (-(p * Ucentered W μ N X)) ∂P) / centeredPartition W μ N ^ p :=
    div_pos hZp (Real.rpow_pos_of_pos hK p)
  calc (∫ X, exp (-(p * Ucentered W μ N X)) ∂P) / centeredPartition W μ N ^ p
      = exp (Real.log ((∫ X, exp (-(p * Ucentered W μ N X)) ∂P) /
          centeredPartition W μ N ^ p)) := (Real.exp_log hpos).symm
    _ ≤ exp (Cp + p * CA) := exp_le_exp.mpr hlog
    _ ≤ C := le_max_right _ _

end DGPS.Lipschitz.ReferenceMoments

namespace DGPS.Lipschitz

/-- The legacy conditional-entropy machinery uses the same pointwise centered kernel. -/
theorem t01_legacy_centeredKernel_eq {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (x y : Torus d) :
    SharpLSI.centeredKernel A.W (μ : Measure (Torus d)) x y = DGPS.centeredKernel A μ x y := by
  have hm : SharpLSI.interE A.W μ μ = DGPS.meanInteraction A μ := by
    unfold SharpLSI.interE DGPS.meanInteraction
    exact (integral_prod_symm _ (A.W_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).symm
  simp only [SharpLSI.centeredKernel, DGPS.centeredKernel, SharpLSI.convMeas,
    DGPS.interactionConvolution, hm]

theorem t01_centeredParticlePotential_eq_legacy {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    centeredParticlePotential A μ N = SharpLSI.Ucentered A.W μ N := by
  funext X
  simp only [centeredParticlePotential, SharpLSI.Ucentered, t01_legacy_centeredKernel_eq]

/-- The exact reference expectation includes the centered kernel's nonzero diagonal. -/
theorem t01_centeredParticlePotential_reference_mean {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (N : ℕ+) :
    ∫ X, centeredParticlePotential A μ N X
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      (∫ x, DGPS.centeredKernel A μ x x ∂(μ : Measure (Torus d))) / 2 := by
  have hm : Measurable (Function.uncurry (SharpLSI.centeredKernel A.W μ)) := by
    change Measurable (fun p : Torus d × Torus d => SharpLSI.centeredKernel A.W μ p.1 p.2)
    simp_rw [t01_legacy_centeredKernel_eq]
    exact (DGPS.continuous_centeredKernel A μ).measurable
  obtain ⟨B, -, hB⟩ := DGPS.centeredKernel_bounded A μ
  have hb : ∀ x y, |SharpLSI.centeredKernel A.W μ x y| ≤ B := by
    simpa only [t01_legacy_centeredKernel_eq] using hB
  have hc : ∀ x, ∫ y, SharpLSI.centeredKernel A.W μ x y ∂(μ : Measure (Torus d)) = 0 := by
    simpa only [t01_legacy_centeredKernel_eq] using DGPS.integral_centeredKernel_right A μ
  rw [t01_centeredParticlePotential_eq_legacy]
  simpa only [t01_legacy_centeredKernel_eq] using
    ReferenceMoments.integral_Ucentered (μ : Measure (Torus d)) hm ⟨B, hb⟩ hc N.pos

/-- Uniform density moments for the actual centered particle law follow from a genuine
mean-field entropy-coercivity inequality. Constants are uniform in particle number. -/
theorem t01_reference_density_moments_of_entropy_coercivity {d : ℕ} (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ ρ : ProbabilityMeasure (Torus d),
      InformationTheory.klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
      c * (InformationTheory.klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
        (InformationTheory.klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
          (1 / 2 : ℝ) * ∫ p, DGPS.centeredKernel A μ p.1 p.2
            ∂((ρ : Measure (Torus d)).prod (ρ : Measure (Torus d)))) :
    ∃ C p : ℝ, 0 ≤ C ∧ 1 < p ∧ ∀ N : ℕ+,
      |Real.log (centeredParticleNormalizer A μ N)| ≤ C ∧
      ∫ X, centeredParticleDensity A μ N X ^ p
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ C := by
  have hm : Measurable (Function.uncurry (SharpLSI.centeredKernel A.W μ)) := by
    change Measurable (fun p : Torus d × Torus d => SharpLSI.centeredKernel A.W μ p.1 p.2)
    simp_rw [t01_legacy_centeredKernel_eq]
    exact (DGPS.continuous_centeredKernel A μ).measurable
  obtain ⟨B, -, hB⟩ := DGPS.centeredKernel_bounded A μ
  have hb : ∀ x y, |SharpLSI.centeredKernel A.W μ x y| ≤ B := by
    simpa only [t01_legacy_centeredKernel_eq] using hB
  have hcenter : ∀ x, ∫ y, SharpLSI.centeredKernel A.W μ x y ∂(μ : Measure (Torus d)) = 0 := by
    simpa only [t01_legacy_centeredKernel_eq] using DGPS.integral_centeredKernel_right A μ
  have hco : ∀ ρ : Measure (Torus d), IsProbabilityMeasure ρ →
      InformationTheory.klDiv ρ (μ : Measure (Torus d)) ≠ ⊤ →
      c * (InformationTheory.klDiv ρ (μ : Measure (Torus d))).toReal ≤
        (InformationTheory.klDiv ρ (μ : Measure (Torus d))).toReal + SharpLSI.Jfun A.W μ ρ := by
    intro ρ hρ hfin
    have h := hc ⟨ρ, hρ⟩ hfin
    have hJ : SharpLSI.Jfun A.W μ ρ =
        (1 / 2 : ℝ) * ∫ p, DGPS.centeredKernel A μ p.1 p.2 ∂(ρ.prod ρ) := by
      unfold SharpLSI.Jfun SharpLSI.interE
      simp only [t01_legacy_centeredKernel_eq]
      rw [integral_prod_symm _ ((DGPS.continuous_centeredKernel A μ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))]
      ring
    rwa [hJ]
  obtain ⟨C, p, hC, hp, hN⟩ := ReferenceMoments.uniform_log_and_density_moments
    (μ : Measure (Torus d)) hm ⟨B, hb⟩ hcenter hc0 hc1 hco
  refine ⟨C, p, hC, hp, fun N => ?_⟩
  have hnormal : centeredParticleNormalizer A μ N = SharpLSI.centeredPartition A.W μ N := by
    rw [centeredParticleNormalizer_eq_integral A μ hμ N]
    simp only [SharpLSI.centeredPartition, t01_centeredParticlePotential_eq_legacy]
  simpa only [centeredParticleDensity, hnormal, t01_centeredParticlePotential_eq_legacy] using
    hN N N.pos

end DGPS.Lipschitz
