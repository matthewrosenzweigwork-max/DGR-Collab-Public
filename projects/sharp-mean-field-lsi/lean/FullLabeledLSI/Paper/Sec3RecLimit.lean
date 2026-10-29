import FullLabeledLSI.Paper.Sec3RecEntropy
import FullLabeledLSI.Paper.Sec3RecAssign
import SharpSymmetricLSI.Paper.ProductEntropy

/-!
# Proposition 3.2: the entropy limit for nonidentical products (smooth case)

For group sizes `n_s` and an assignment `a` with these fibre sizes:
`N⁻¹ H(ν_N|P_N) = ∑ₛ (n_s/N)(H_s + ρ_s(V)) + ½ ∑_{s,t} (n_s n_t/N²) W(ρ_s,ρ_t)
   - (2N)⁻¹ ∑ₛ (n_s/N) W(ρ_s,ρ_s) + N⁻¹ log Z_N`.
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sum_fiber {N q : ℕ} (a : Fin N → Fin q) (n : Fin q → ℕ)
    (hfib : ∀ s, (Finset.univ.filter fun i => a i = s).card = n s) (g : Fin q → ℝ) :
    ∑ i, g (a i) = ∑ s, (n s : ℝ) * g s := by
  rw [← Finset.sum_fiberwise Finset.univ a (fun i => g (a i))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g s) (fun i hi => by
    rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, hfib s, nsmul_eq_mul]

theorem sum_pair_fiber {N q : ℕ} (a : Fin N → Fin q) (n : Fin q → ℕ)
    (hfib : ∀ s, (Finset.univ.filter fun i => a i = s).card = n s) (F : Fin q → Fin q → ℝ) :
    ∑ i, ∑ j, (if i = j then 0 else F (a i) (a j)) =
      ∑ s, ∑ t, (n s : ℝ) * n t * F s t - ∑ s, (n s : ℝ) * F s s := by
  have h1 : ∀ i j : Fin N, (if i = j then 0 else F (a i) (a j)) =
      F (a i) (a j) - (if i = j then F (a i) (a i) else 0) := fun i j => by
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [h1, Finset.sum_sub_distrib]
  have e1 : ∑ i, ∑ j, F (a i) (a j) = ∑ s, ∑ t, (n s : ℝ) * n t * F s t := by
    have h1 : ∀ i, ∑ j, F (a i) (a j) = ∑ t, (n t : ℝ) * F (a i) t := fun i =>
      sum_fiber a n hfib (fun t => F (a i) t)
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ t, ∑ i, (n t : ℝ) * F (a i) t = ∑ s, (n s : ℝ) * ((n t : ℝ) * F s t) := fun t => by
      rw [← Finset.mul_sum, sum_fiber a n hfib (fun s => F s t), Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    simp_rw [h2]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
  have e2 : ∑ i, ∑ j, (if i = j then F (a i) (a i) else 0) = ∑ s, (n s : ℝ) * F s s := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_fiber a n hfib (fun s => F s s)
  rw [e1, e2]


theorem entropy_expr (hyp : Hyp V W KV KW) {q N : ℕ} (hN : 1 ≤ N) (ρ : Fin q → Torus d → ℝ)
    (hρ : ∀ s, (∀ x, 0 ≤ ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1 ∧
      klDiv (densMeasure (ρ s)) (haar d) ≠ ⊤)
    (a : Fin N → Fin q) (n : Fin q → ℕ)
    (hfib : ∀ s, (Finset.univ.filter fun i => a i = s).card = n s) :
    klDiv (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N) ≠ ⊤ ∧
      (klDiv (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N)).toReal / N =
        ∑ s, ((n s : ℝ) / N) * ((klDiv (densMeasure (ρ s)) (haar d)).toReal +
            potE V (densMeasure (ρ s))) +
          (1 / 2) * ∑ s, ∑ t, ((n s : ℝ) / N) * ((n t : ℝ) / N) *
            interE W (densMeasure (ρ s)) (densMeasure (ρ t)) -
          1 / (2 * (N : ℝ)) * ∑ s, ((n s : ℝ) / N) * interE W (densMeasure (ρ s)) (densMeasure (ρ s)) +
          Real.log (partitionFn V W N) / N := by
  haveI : ∀ s, IsProbabilityMeasure (densMeasure (ρ s)) := fun s =>
    isProbabilityMeasure_densMeasure' (hρ s).1 (hρ s).2.1
  haveI : ∀ i : Fin N, IsProbabilityMeasure (densMeasure (ρ (a i))) := fun i => inferInstance
  obtain ⟨hne, hval⟩ := product_entropy_gen (V := V) (W := W) hyp (N := N)
    (ρ := fun i => densMeasure (ρ (a i))) (fun i => (hρ (a i)).2.2)
  refine ⟨hne, ?_⟩
  rw [hval]
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  rw [sum_fiber a n hfib (fun s => (klDiv (densMeasure (ρ s)) (haar d)).toReal),
    sum_fiber a n hfib (fun s => potE V (densMeasure (ρ s))),
    sum_pair_fiber a n hfib (fun s t => interE W (densMeasure (ρ s)) (densMeasure (ρ t)))]
  have e1 : ∀ s, ((n s : ℝ) / N) * ((klDiv (densMeasure (ρ s)) (haar d)).toReal +
      potE V (densMeasure (ρ s))) = ((n s : ℝ) * (klDiv (densMeasure (ρ s)) (haar d)).toReal +
        (n s : ℝ) * potE V (densMeasure (ρ s))) / N := fun s => by ring
  simp_rw [e1]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have e2 : ∑ s, ∑ t, ((n s : ℝ) / N) * ((n t : ℝ) / N) *
      interE W (densMeasure (ρ s)) (densMeasure (ρ t)) =
      (∑ s, ∑ t, (n s : ℝ) * n t * interE W (densMeasure (ρ s)) (densMeasure (ρ t))) / (N : ℝ) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun t _ => by field_simp
  have e3 : ∑ s, ((n s : ℝ) / N) * interE W (densMeasure (ρ s)) (densMeasure (ρ s)) =
      (∑ s, (n s : ℝ) * interE W (densMeasure (ρ s)) (densMeasure (ρ s))) / N := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2, e3]
  field_simp
  ring


theorem tendsto_entropy_expr {q : ℕ} (x : ℕ → Fin q → ℝ) (θ : Fin q → ℝ)
    (hx : ∀ s, Tendsto (fun N => x N s) atTop (𝓝 (θ s))) (c : Fin q → ℝ)
    (I : Fin q → Fin q → ℝ) (g : ℕ → ℝ) (L : ℝ) (hg : Tendsto g atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑ s, x N s * c s + 1 / 2 * ∑ s, ∑ t, x N s * x N t * I s t -
        1 / (2 * (N : ℝ)) * ∑ s, x N s * I s s + g N) atTop
      (𝓝 (∑ s, θ s * c s + 1 / 2 * ∑ s, ∑ t, θ s * θ t * I s t - 0 * ∑ s, θ s * I s s + L)) := by
  have h1 : Tendsto (fun N : ℕ => ∑ s, x N s * c s) atTop (𝓝 (∑ s, θ s * c s)) :=
    tendsto_finsetSum _ fun s _ => (hx s).mul_const _
  have h2 : Tendsto (fun N : ℕ => ∑ s, ∑ t, x N s * x N t * I s t) atTop
      (𝓝 (∑ s, ∑ t, θ s * θ t * I s t)) :=
    tendsto_finsetSum _ fun s _ => tendsto_finsetSum _ fun t _ => ((hx s).mul (hx t)).mul_const _
  have h3 : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ))) atTop (𝓝 0) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at this
    refine this.congr fun N => ?_
    field_simp
  have h4 : Tendsto (fun N : ℕ => ∑ s, x N s * I s s) atTop (𝓝 (∑ s, θ s * I s s)) :=
    tendsto_finsetSum _ fun s _ => (hx s).mul_const _
  exact ((h1.add (h2.const_mul _)).sub (h3.mul h4)).add hg


section Mix

variable {q : ℕ} (θ : Fin q → ℝ) (ρ : Fin q → Torus d → ℝ)

theorem potE_mix (hyp : Hyp V W KV KW) (hρ0 : ∀ s x, 0 ≤ ρ s x)
    (hρ1 : ∀ s, ∫ x, ρ s x ∂haar d = 1) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1) :
    potE V (densMeasure (fun x => ∑ s, θ s * ρ s x)) = ∑ s, θ s * potE V (densMeasure (ρ s)) := by
  have hρi : ∀ s, Integrable (ρ s) (haar d) := fun s => integrable_of_integral_eq_one' (hρ1 s)
  have hbar0 : ∀ x, 0 ≤ ∑ s, θ s * ρ s x := fun x =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hθ0 s) (hρ0 s x)
  have hbar1 : ∫ x, (∑ s, θ s * ρ s x) ∂haar d = 1 := by
    rw [integral_finsetSum _ fun s _ => (hρi s).const_mul _]
    simp_rw [integral_const_mul, hρ1, mul_one]; exact hθ1
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  have hint : ∀ s, Integrable (fun x => ρ s x * V x) (haar d) := fun s => by
    have := (hρi s).bdd_mul (c := BV) hyp.continuous_V.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBV x)
    simpa [mul_comm] using this
  unfold potE
  rw [integral_densMeasure' hbar0 hbar1]
  have e : ∀ x, (∑ s, θ s * ρ s x) * V x = ∑ s, θ s * (ρ s x * V x) := fun x => by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => (hint s).const_mul _]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, integral_densMeasure' (hρ0 s) (hρ1 s)]

theorem interE_mix (hyp : Hyp V W KV KW) (hρc : ∀ s, Continuous (ρ s)) (hρ0 : ∀ s x, 0 ≤ ρ s x)
    (hρ1 : ∀ s, ∫ x, ρ s x ∂haar d = 1) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1) :
    interE W (densMeasure (fun x => ∑ s, θ s * ρ s x)) (densMeasure (fun x => ∑ s, θ s * ρ s x)) =
      ∑ s, ∑ t, θ s * θ t * interE W (densMeasure (ρ s)) (densMeasure (ρ t)) := by
  have hρi : ∀ s, Integrable (ρ s) (haar d) := fun s => integrable_of_integral_eq_one' (hρ1 s)
  have hbar0 : ∀ x, 0 ≤ ∑ s, θ s * ρ s x := fun x =>
    Finset.sum_nonneg fun s _ => mul_nonneg (hθ0 s) (hρ0 s x)
  have hbar1 : ∫ x, (∑ s, θ s * ρ s x) ∂haar d = 1 := by
    rw [integral_finsetSum _ fun s _ => (hρi s).const_mul _]
    simp_rw [integral_const_mul, hρ1, mul_one]; exact hθ1
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hWc : Continuous (Function.uncurry W) := hyp.continuous_W
  -- `J_s y = ∫ ρ_s x W x y dx`
  set J : Fin q → Torus d → ℝ := fun s y => ∫ x, ρ s x * W x y ∂haar d with hJ
  have hint1 : ∀ s y, Integrable (fun x => ρ s x * W x y) (haar d) := fun s y => by
    have := (hρi s).bdd_mul (c := BW)
      (hWc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hBW (x, y))
    simpa [mul_comm] using this
  have hJm : ∀ s, Measurable (J s) := fun s => by
    have hm : Measurable (Function.uncurry fun (y : Torus d) (x : Torus d) => ρ s x * W x y) :=
      ((hρc s).measurable.comp measurable_snd).mul
        (hWc.measurable.comp (measurable_snd.prodMk measurable_fst))
    exact (hm.stronglyMeasurable.integral_prod_right (ν := haar d)
      (f := fun y x => ρ s x * W x y)).measurable
  have hJb : ∀ s y, |J s y| ≤ BW := fun s y => by
    simp only [hJ]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |ρ s x * W x y| ∂haar d ≤ ∫ x, BW * ρ s x ∂haar d := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            ((hρi s).const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          show |ρ s x * W x y| ≤ BW * ρ s x
          rw [abs_mul, abs_of_nonneg (hρ0 s x), mul_comm]
          exact mul_le_mul_of_nonneg_right (hBW (x, y)) (hρ0 s x)
      _ = BW := by rw [integral_const_mul, hρ1, mul_one]
  have hint2 : ∀ t s, Integrable (fun y => ρ t y * J s y) (haar d) := fun t s => by
    have := (hρi t).bdd_mul (c := BW) (hJm s).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hJb s y)
    simpa [mul_comm] using this
  -- the general formula `interE (dens f) (dens g) = ∫ g y * ∫ f x W x y`
  have hgen : ∀ (f g : Torus d → ℝ), (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → ∫ x, f x ∂haar d = 1 →
      ∫ x, g x ∂haar d = 1 → interE W (densMeasure f) (densMeasure g) =
        ∫ y, g y * ∫ x, f x * W x y ∂haar d ∂haar d := fun f g hf0 hg0 hf1 hg1 => by
    unfold interE
    rw [integral_densMeasure' hg0 hg1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_densMeasure' hf0 hf1]
  rw [hgen _ _ hbar0 hbar0 hbar1 hbar1]
  have hin : ∀ y, ∫ x, (∑ s, θ s * ρ s x) * W x y ∂haar d = ∑ s, θ s * J s y := fun y => by
    have e : ∀ x, (∑ s, θ s * ρ s x) * W x y = ∑ s, θ s * (ρ s x * W x y) := fun x => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun s _ => (hint1 s y).const_mul _]
    exact Finset.sum_congr rfl fun s _ => by rw [integral_const_mul]
  simp_rw [hin]
  have e2 : ∀ y, (∑ t, θ t * ρ t y) * ∑ s, θ s * J s y =
      ∑ t, ∑ s, θ t * θ s * (ρ t y * J s y) := fun y => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp_rw [e2]
  rw [integral_finsetSum _ fun t _ => integrable_finsetSum _ fun s _ => (hint2 t s).const_mul _]
  have hinner : ∀ t, ∫ y, ∑ s, θ t * θ s * (ρ t y * J s y) ∂haar d =
      ∑ s, θ t * θ s * ∫ y, ρ t y * J s y ∂haar d := fun t => by
    rw [integral_finsetSum _ fun s _ => (hint2 t s).const_mul _]
    exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [hgen _ _ (hρ0 s) (hρ0 t) (hρ1 s) (hρ1 t)]
  simp only [hJ]
  ring

end Mix

end SharpLSI.FL
