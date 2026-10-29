import SharpSymmetricLSI.Paper.CondForce1

/-!
# Lemma 5.4, the three expectations (Phase 3, lane D; R21)

For a bounded measurable field `b(x,y) ∈ ℝ^d` and one-body term `c(x)`, with
`B_j(p,x) = ∫ b(x,y) dρ_j(p)(y)` and `G = N⁻¹(∑_{l≠j} b(X_j,X_l) + c(X_j))`,
`E|B_j(X_j) - G|² ≤ K(√(2D_{j,2}) + √(2D_{j,3}) + 1/N)`: each of `E|B_j|²`, `E B_j·G`,
`E|G|²` is within this error of `C₃ = E b(X₀,X₁)·b(X₀,X₂)` (conditional Pinsker and
exchangeability).
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

/-- `B_j(p,x) = ∫ b(x,y) dρ_j(p)(y)`. -/
def Babs (b : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d)) [IsFiniteMeasure ν]
    (j : ℕ) (hj : j < N) (p : Fin j → Torus d) (x : Torus d) (k : Fin d) : ℝ :=
  ∫ y, b x y k ∂condNext ν j hj p

/-- `G = N⁻¹(∑_{l≠j} b(X_j,X_l) + c(X_j))`. -/
def Gabs (b : Torus d → Torus d → Fin d → ℝ) (c : Torus d → Fin d → ℝ) (j : Fin N)
    (X : Config N d) (k : Fin d) : ℝ :=
  (N : ℝ)⁻¹ * ((∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) + c (X j) k)

/-- `b(x,y)·b(x,z)`. -/
def dot3 (b : Torus d → Torus d → Fin d → ℝ) (x y z : Torus d) : ℝ := ∑ k, b x y k * b x z k

/-- `C₃ = E b(X₀,X₁)·b(X₀,X₂)`. -/
def C3 (b : Torus d → Torus d → Fin d → ℝ) (ν : Measure (Config N d)) (h3 : 3 ≤ N) : ℝ :=
  ∫ X, dot3 b (X ⟨0, by omega⟩) (X ⟨1, by omega⟩) (X ⟨2, by omega⟩) ∂ν

section abstract
variable {b : Torus d → Torus d → Fin d → ℝ} (hb : ∀ k, Measurable (Function.uncurry fun x y => b x y k))
  {M : ℝ} (hbM : ∀ x y k, |b x y k| ≤ M)

include hb in
theorem measurable_dot3 : Measurable fun q : Torus d × Torus d × Torus d => dot3 b q.1 q.2.1 q.2.2 := by
  unfold dot3
  refine Finset.measurable_sum _ fun k _ => ?_
  have h1 : Measurable fun q : Torus d × Torus d × Torus d => (q.1, q.2.1) := by fun_prop
  have h2 : Measurable fun q : Torus d × Torus d × Torus d => (q.1, q.2.2) := by fun_prop
  exact ((hb k).comp h1).mul ((hb k).comp h2)

include hbM in
theorem abs_dot3_le (hM0 : 0 ≤ M) (x y z : Torus d) : |dot3 b x y z| ≤ d * M ^ 2 := by
  unfold dot3
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |b x y k * b x z k| ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
        rw [abs_mul, sq]; exact mul_le_mul (hbM x y k) (hbM x z k) (abs_nonneg _) hM0
    _ = d * M ^ 2 := by simp

include hb in
/-- Exchangeability: `E b(X_a,X_{a'})·b(X_a,X_{a''}) = C₃` for distinct `a, a', a''`. -/
theorem integral_dot3_eq_C3 {ν : Measure (Config N d)} (hsym : IsSymmetricMeasure ν)
    (h3 : 3 ≤ N) {a a' a'' : Fin N} (h1 : a ≠ a') (h2 : a ≠ a'') (h12 : a' ≠ a'') :
    ∫ X, dot3 b (X a) (X a') (X a'') ∂ν = C3 b ν h3 := by
  have hB : Measurable fun z : Fin 3 → Torus d => dot3 b (z 0) (z 1) (z 2) := by
    have hp : Measurable fun z : Fin 3 → Torus d => (z 0, z 1, z 2) := by fun_prop
    exact (measurable_dot3 hb).comp hp
  have hinj : ∀ u v w : Fin N, u ≠ v → u ≠ w → v ≠ w → Function.Injective ![u, v, w] := by
    intro u v w huv huw hvw x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
  have := integral_comp_inj_eq hsym hB (hinj a a' a'' h1 h2 h12)
    (hinj ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff]))
  simpa [C3] using this

include hb in
theorem measurable_Babs (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (k : Fin d) : Measurable (Function.uncurry fun p x => Babs b ν j hj p x k) := by
  have hp : Measurable fun q : ((Fin j → Torus d) × Torus d) × Torus d => (q.1.2, q.2) := by
    fun_prop
  have hf := Measurable.comp (g := Function.uncurry fun x y => b x y k) (hb k) hp
  have := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (condNext ν j hj).comap Prod.fst measurable_fst)
  convert this.measurable using 1
  funext q
  rw [Kernel.comap_apply]
  rfl

include hbM in
theorem abs_Babs_le (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (p : Fin j → Torus d) (x : Torus d) (k : Fin d) : |Babs b ν j hj p x k| ≤ M :=
  abs_integral_le_of_bdd fun y => hbM x y k

include hb hbM in
/-- `|B_j(p,x)|² = ∫∫ b(x,y)·b(x,w) dρ_j(y) dρ_j(w)`. -/
theorem sumsq_Babs_eq (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (p : Fin j → Torus d) (x : Torus d) :
    ∑ k, Babs b ν j hj p x k ^ 2 =
      ∫ y, ∫ w, dot3 b x y w ∂condNext ν j hj p ∂condNext ν j hj p := by
  set ρ := condNext ν j hj p
  have hm : ∀ k, Measurable fun y => b x y k := fun k => (hb k).of_uncurry_left
  have hi : ∀ k, Integrable (fun y => b x y k) ρ := fun k => integrable_of_bdd (hm k) (hbM x · k)
  have inner : ∀ y, ∫ w, dot3 b x y w ∂ρ = ∑ k, b x y k * Babs b ν j hj p x k := fun y => by
    unfold dot3
    rw [integral_finset_sum _ fun k _ => (hi k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; rfl
  simp_rw [inner]
  rw [integral_finset_sum _ fun k _ => (hi k).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, sq]; rfl

include hb hbM in
/-- **First expectation**: `|E|B_j(X_j)|² - C₃| ≤ dM²√(2D_{j,3})`. -/
theorem P1_sub_C3 (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hM0 : 0 ≤ M)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) (h : j + 3 ≤ N) :
    |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν - C3 b ν (by omega)| ≤
      d * M ^ 2 * Real.sqrt (2 * (DCond ν j 3 hj h).toReal) := by
  have hF : Measurable (Function.uncurry fun p x => ∑ k, Babs b ν j hj p x k ^ 2) :=
    Finset.measurable_sum _ fun k _ => (measurable_Babs hb ν hj k).pow_const 2
  have hFb : ∀ p x, |∑ k, Babs b ν j hj p x k ^ 2| ≤ d * M ^ 2 := fun p x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |Babs b ν j hj p x k ^ 2| ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_Babs_le hbM ν hj p x k) 2
      _ = d * M ^ 2 := by simp
  have hT : Measurable (Function.uncurry fun (_ : Fin j → Torus d) (z : Fin 3 → Torus d) =>
      dot3 b (z 0) (z 1) (z 2)) := by
    have hp : Measurable fun q : (Fin j → Torus d) × (Fin 3 → Torus d) =>
        (q.2 0, q.2 1, q.2 2) := by fun_prop
    exact (measurable_dot3 hb).comp hp
  have hTb : ∀ (_ : Fin j → Torus d) (z : Fin 3 → Torus d), |dot3 b (z 0) (z 1) (z 2)| ≤ d * M ^ 2 :=
    fun _ z => abs_dot3_le hbM hM0 _ _ _
  have e1 : ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν =
      ∫ p, ∫ z, dot3 b (z 0) (z 1) (z 2) ∂(Measure.pi fun _ : Fin 3 => condNext ν j hj p)
        ∂(ν.map (past j hj.le)) := by
    rw [integral_pastNext ν hj hF hFb]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    rw [integral_pi_three (measurable_dot3 hb) (fun x y w => abs_dot3_le hbM hM0 x y w)]
    exact integral_congr_ae (Eventually.of_forall fun x => sumsq_Babs_eq hb hbM ν hj p x)
  have e2 : ∫ X, dot3 b (block j 3 h X 0) (block j 3 h X 1) (block j 3 h X 2) ∂ν =
      C3 b ν (by omega) :=
    integral_dot3_eq_C3 hb hsym (by omega) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  rw [e1, ← e2]
  exact pastTest_sub_block μ ν hsym hH hj h hT hTb

theorem sumsq_Gabs (c : Torus d → Fin d → ℝ) (j : Fin N) (X : Config N d) :
    ∑ k, Gabs b c j X k ^ 2 = ((N : ℝ)⁻¹) ^ 2 *
      ((∑ l ∈ Finset.univ.erase j, ∑ l' ∈ Finset.univ.erase j, dot3 b (X j) (X l) (X l')) +
        ∑ k, (2 * (∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) * c (X j) k + c (X j) k ^ 2)) := by
  unfold Gabs dot3
  simp_rw [mul_pow, ← Finset.mul_sum]
  congr 1
  have e : ∀ k, ((∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) + c (X j) k) ^ 2 =
      (∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) * (∑ l' ∈ Finset.univ.erase j, b (X j) (X l') k) +
      (2 * (∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) * c (X j) k + c (X j) k ^ 2) := fun k => by
    ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]

include hb hbM in
/-- **Third expectation**: `|E|G|² - C₃| ≤ 6dM²/N`. -/
theorem P3_sub_C3 (hM0 : 0 ≤ M) {c : Torus d → Fin d → ℝ} (hc : ∀ k, Measurable fun x => c x k)
    (hcM : ∀ x k, |c x k| ≤ M) (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hsym : IsSymmetricMeasure ν) (h3 : 3 ≤ N) (j : Fin N) :
    |∫ X, ∑ k, Gabs b c j X k ^ 2 ∂ν - C3 b ν h3| ≤ 6 * d * M ^ 2 / N := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set E := Finset.univ.erase j with hE
  have hcard : (E.card : ℝ) = N - 1 := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]; simp
  have hmb : ∀ (a a' : Fin N) k, Measurable fun X : Config N d => b (X a) (X a') k := fun a a' k => by
    have hp : Measurable fun X : Config N d => (X a, X a') := by fun_prop
    exact (hb k).comp hp
  have hmd : ∀ a a' a'' : Fin N, Measurable fun X : Config N d => dot3 b (X a) (X a') (X a'') :=
    fun a a' a'' => by
      have hp : Measurable fun X : Config N d => (X a, X a', X a'') := by fun_prop
      exact (measurable_dot3 hb).comp hp
  have hid : ∀ a a' a'' : Fin N, Integrable (fun X : Config N d => dot3 b (X a) (X a') (X a'')) ν :=
    fun a a' a'' => integrable_of_bdd (hmd a a' a'') fun X => abs_dot3_le hbM hM0 _ _ _
  set R : Config N d → ℝ := fun X => ∑ k, (2 * (∑ l ∈ E, b (X j) (X l) k) * c (X j) k +
    c (X j) k ^ 2) with hR
  have hRb : ∀ X, |R X| ≤ 2 * N * d * M ^ 2 := fun X => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hk : ∀ k, |2 * (∑ l ∈ E, b (X j) (X l) k) * c (X j) k + c (X j) k ^ 2| ≤ 2 * N * M ^ 2 :=
      fun k => by
        have hS : |∑ l ∈ E, b (X j) (X l) k| ≤ (N - 1) * M := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_card_nsmul _ _ M fun l _ => hbM _ _ _).trans (le_of_eq ?_)
          rw [nsmul_eq_mul, hcard]
        have hcc := hcM (X j) k
        have h1 : |2 * (∑ l ∈ E, b (X j) (X l) k) * c (X j) k| ≤ 2 * ((N - 1) * M) * M := by
          rw [abs_mul, abs_mul, abs_two]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hS zero_le_two) hcc (abs_nonneg _)
            (by have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
                positivity)
        have h2 : |c (X j) k ^ 2| ≤ M ^ 2 := by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hcc 2
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        refine (abs_add_le _ _).trans ?_
        nlinarith [sq_nonneg M]
    calc ∑ k, |2 * (∑ l ∈ E, b (X j) (X l) k) * c (X j) k + c (X j) k ^ 2|
        ≤ ∑ _k : Fin d, 2 * N * M ^ 2 := Finset.sum_le_sum fun k _ => hk k
      _ = 2 * N * d * M ^ 2 := by simp; ring
  have hRm : Measurable R := Finset.measurable_sum _ fun k _ =>
    ((measurable_const.mul (Finset.measurable_sum _ fun l _ => hmb j l k)).mul
      ((hc k).comp (measurable_pi_apply j))).add (((hc k).comp (measurable_pi_apply j)).pow_const 2)
  -- the double sum
  have hA : ∫ X, (∑ l ∈ E, ∑ l' ∈ E, dot3 b (X j) (X l) (X l')) ∂ν =
      (N - 1) * (N - 2) * C3 b ν h3 + ∑ l ∈ E, ∫ X, dot3 b (X j) (X l) (X l) ∂ν := by
    rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun l' _ => hid _ _ _]
    have hrow : ∀ l ∈ E, ∫ X, (∑ l' ∈ E, dot3 b (X j) (X l) (X l')) ∂ν =
        (N - 2) * C3 b ν h3 + ∫ X, dot3 b (X j) (X l) (X l) ∂ν := fun l hl => by
      rw [integral_finset_sum _ fun l' _ => hid _ _ _, ← Finset.add_sum_erase _ _ hl]
      have hjl : j ≠ l := fun h => (Finset.mem_erase.mp hl).1 h.symm
      have hrest : ∑ l' ∈ E.erase l, ∫ X, dot3 b (X j) (X l) (X l') ∂ν = (N - 2) * C3 b ν h3 := by
        rw [Finset.sum_congr rfl fun l' hl' => integral_dot3_eq_C3 hb hsym h3 hjl
          (fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp hl').2).1 h.symm)
          (fun h => (Finset.mem_erase.mp hl').1 h.symm), Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem hl]
        rw [Nat.cast_sub (Finset.card_pos.mpr ⟨l, hl⟩ : 0 < E.card)]
        congr 1; rw [hcard]; push_cast; ring
      rw [hrest]; ring
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    ring
  have hdiag : |∑ l ∈ E, ∫ X, dot3 b (X j) (X l) (X l) ∂ν| ≤ (N - 1) * (d * M ^ 2) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (d * M ^ 2) fun l _ =>
      abs_integral_le_of_bdd fun X => abs_dot3_le hbM hM0 _ _ _).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, hcard]
  have hC3 : |C3 b ν h3| ≤ d * M ^ 2 := abs_integral_le_of_bdd fun X => abs_dot3_le hbM hM0 _ _ _
  have hRi : |∫ X, R X ∂ν| ≤ 2 * N * d * M ^ 2 := abs_integral_le_of_bdd hRb
  have e1 : ∫ X, ∑ k, Gabs b c j X k ^ 2 ∂ν = ((N : ℝ)⁻¹) ^ 2 *
      ((N - 1) * (N - 2) * C3 b ν h3 + (∑ l ∈ E, ∫ X, dot3 b (X j) (X l) (X l) ∂ν) +
        ∫ X, R X ∂ν) := by
    simp_rw [sumsq_Gabs]
    rw [integral_const_mul, integral_add (integrable_finset_sum _ fun l _ =>
      integrable_finset_sum _ fun l' _ => hid _ _ _) (integrable_of_bdd hRm hRb), hA]
  rw [e1]
  set A := ∑ l ∈ E, ∫ X, dot3 b (X j) (X l) (X l) ∂ν
  set r := ∫ X, R X ∂ν
  set C := C3 b ν h3
  have key : ((N : ℝ)⁻¹) ^ 2 * ((N - 1) * (N - 2) * C + A + r) - C =
      ((N : ℝ)⁻¹) ^ 2 * ((2 - 3 * N) * C + A + r) := by field_simp; ring
  rw [key, abs_mul, abs_of_nonneg (by positivity)]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hb1 : |(2 - 3 * (N : ℝ)) * C + A + r| ≤ 6 * N * (d * M ^ 2) := by
    have h3a := abs_add_three ((2 - 3 * (N : ℝ)) * C) A r
    have hx : |(2 - 3 * (N : ℝ)) * C| ≤ 3 * N * (d * M ^ 2) := by
      rw [abs_mul]
      have : |2 - 3 * (N : ℝ)| ≤ 3 * N := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul this hC3 (abs_nonneg _) (by positivity)
    have hdM : (0 : ℝ) ≤ d * M ^ 2 := by positivity
    nlinarith
  calc ((N : ℝ)⁻¹) ^ 2 * |(2 - 3 * (N : ℝ)) * C + A + r| ≤ ((N : ℝ)⁻¹) ^ 2 * (6 * N * (d * M ^ 2)) :=
        mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = 6 * d * M ^ 2 / N := by field_simp

include hb hbM in
theorem sum_Babs_mul (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N)
    (p : Fin j → Torus d) (x q : Torus d) :
    ∑ k, Babs b ν j hj p x k * b x q k = ∫ y, dot3 b x y q ∂condNext ν j hj p := by
  have hi : ∀ k, Integrable (fun y => b x y k) (condNext ν j hj p) := fun k =>
    integrable_of_bdd (hb k).of_uncurry_left (hbM x · k)
  unfold dot3
  rw [integral_finset_sum _ fun k _ => (hi k).mul_const _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const]; rfl

include hb hbM in
/-- Cross term with a past particle `l < j`. -/
theorem Qpast_sub_C3 (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hM0 : 0 ≤ M)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) (h2 : j + 2 ≤ N)
    (h3 : 3 ≤ N) {l : ℕ} (hl : l < j) :
    |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k * b (X ⟨j, hj⟩) (X ⟨l, by omega⟩) k ∂ν -
      C3 b ν h3| ≤ d * M ^ 2 * Real.sqrt (2 * (DCond ν j 2 hj h2).toReal) := by
  have hF : Measurable (Function.uncurry fun (p : Fin j → Torus d) x =>
      ∑ k, Babs b ν j hj p x k * b x (p ⟨l, hl⟩) k) := by
    refine Finset.measurable_sum _ fun k _ => (measurable_Babs hb ν hj k).mul ?_
    have hp : Measurable fun q : (Fin j → Torus d) × Torus d => (q.2, q.1 ⟨l, hl⟩) := by fun_prop
    exact (hb k).comp hp
  have hFb : ∀ (p : Fin j → Torus d) x, |∑ k, Babs b ν j hj p x k * b x (p ⟨l, hl⟩) k| ≤
      d * M ^ 2 := fun p x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |Babs b ν j hj p x k * b x (p ⟨l, hl⟩) k| ≤ ∑ _k : Fin d, M ^ 2 :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, sq]
            exact mul_le_mul (abs_Babs_le hbM ν hj p x k) (hbM _ _ _) (abs_nonneg _) hM0
      _ = d * M ^ 2 := by simp
  have hT : Measurable (Function.uncurry fun (p : Fin j → Torus d) (z : Fin 2 → Torus d) =>
      dot3 b (z 0) (z 1) (p ⟨l, hl⟩)) := by
    have hp : Measurable fun q : (Fin j → Torus d) × (Fin 2 → Torus d) =>
        (q.2 0, q.2 1, q.1 ⟨l, hl⟩) := by fun_prop
    exact (measurable_dot3 hb).comp hp
  have hTb : ∀ (p : Fin j → Torus d) (z : Fin 2 → Torus d),
      |dot3 b (z 0) (z 1) (p ⟨l, hl⟩)| ≤ d * M ^ 2 := fun _ _ => abs_dot3_le hbM hM0 _ _ _
  have e1 : ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
      b (X ⟨j, hj⟩) (X ⟨l, by omega⟩) k ∂ν =
      ∫ p, ∫ z, dot3 b (z 0) (z 1) (p ⟨l, hl⟩) ∂(Measure.pi fun _ : Fin 2 => condNext ν j hj p)
        ∂(ν.map (past j hj.le)) := by
    have := integral_pastNext ν hj hF hFb
    rw [show (fun X : Config N d => ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
      b (X ⟨j, hj⟩) (X ⟨l, by omega⟩) k) = fun X => ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
      b (X ⟨j, hj⟩) (past j hj.le X ⟨l, hl⟩) k from rfl, this]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    rw [integral_pi_two (f := fun x y => dot3 b x y (p ⟨l, hl⟩)) (by
      have hp : Measurable fun q : Torus d × Torus d => (q.1, q.2, p ⟨l, hl⟩) := by fun_prop
      exact (measurable_dot3 hb).comp hp) (fun x y => abs_dot3_le hbM hM0 _ _ _)]
    exact integral_congr_ae (Eventually.of_forall fun x => sum_Babs_mul hb hbM ν hj p x _)
  have e2 : ∫ X, dot3 b (block j 2 h2 X 0) (block j 2 h2 X 1) (past j hj.le X ⟨l, hl⟩) ∂ν =
      C3 b ν h3 :=
    integral_dot3_eq_C3 hb hsym h3 (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
      (by simp [Fin.ext_iff]; omega)
  rw [e1, ← e2]
  exact pastTest_sub_block μ ν hsym hH hj h2 hT hTb

include hb hbM in
/-- Cross term with the next particle: `|E B_j(X_j)·b(X_j,X_{j+1}) - E|B_j(X_j)|²| ≤ dM²√(2D_{j,2})`. -/
theorem Qnext_sub_P1 (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hM0 : 0 ≤ M)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) (h2 : j + 2 ≤ N) :
    |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
        b (X ⟨j, hj⟩) (X ⟨j + 1, by omega⟩) k ∂ν -
      ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν| ≤
      d * M ^ 2 * Real.sqrt (2 * (DCond ν j 2 hj h2).toReal) := by
  have hT : Measurable (Function.uncurry fun (p : Fin j → Torus d) (z : Fin 2 → Torus d) =>
      ∑ k, Babs b ν j hj p (z 0) k * b (z 0) (z 1) k) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    have hp1 : Measurable fun q : (Fin j → Torus d) × (Fin 2 → Torus d) => (q.1, q.2 0) := by
      fun_prop
    have hp2 : Measurable fun q : (Fin j → Torus d) × (Fin 2 → Torus d) => (q.2 0, q.2 1) := by
      fun_prop
    exact ((measurable_Babs hb ν hj k).comp hp1).mul ((hb k).comp hp2)
  have hTb : ∀ (p : Fin j → Torus d) (z : Fin 2 → Torus d),
      |∑ k, Babs b ν j hj p (z 0) k * b (z 0) (z 1) k| ≤ d * M ^ 2 := fun p z => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |Babs b ν j hj p (z 0) k * b (z 0) (z 1) k| ≤ ∑ _k : Fin d, M ^ 2 :=
          Finset.sum_le_sum fun k _ => by
            rw [abs_mul, sq]
            exact mul_le_mul (abs_Babs_le hbM ν hj p _ k) (hbM _ _ _) (abs_nonneg _) hM0
      _ = d * M ^ 2 := by simp
  have hF : Measurable (Function.uncurry fun p x => ∑ k, Babs b ν j hj p x k ^ 2) :=
    Finset.measurable_sum _ fun k _ => (measurable_Babs hb ν hj k).pow_const 2
  have hFb : ∀ p x, |∑ k, Babs b ν j hj p x k ^ 2| ≤ d * M ^ 2 := fun p x => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k, |Babs b ν j hj p x k ^ 2| ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_Babs_le hbM ν hj p x k) 2
      _ = d * M ^ 2 := by simp
  have e1 : ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν =
      ∫ p, ∫ z, ∑ k, Babs b ν j hj p (z 0) k * b (z 0) (z 1) k
        ∂(Measure.pi fun _ : Fin 2 => condNext ν j hj p) ∂(ν.map (past j hj.le)) := by
    rw [integral_pastNext ν hj hF hFb]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    have hm2 : Measurable (Function.uncurry fun x y => ∑ k, Babs b ν j hj p x k * b x y k) := by
      refine Finset.measurable_sum _ fun k _ => ?_
      have hp1 : Measurable fun q : Torus d × Torus d => (p, q.1) := by fun_prop
      exact ((measurable_Babs hb ν hj k).comp hp1).mul (hb k)
    rw [integral_pi_two (f := fun x y => ∑ k, Babs b ν j hj p x k * b x y k) hm2 (fun x y =>
      hTb p ![x, y])]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    have hi : ∀ k, Integrable (fun y => b x y k) (condNext ν j hj p) := fun k =>
      integrable_of_bdd (hb k).of_uncurry_left (hbM x · k)
    rw [integral_finset_sum _ fun k _ => (hi k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, sq]; rfl
  rw [e1, abs_sub_comm]
  exact pastTest_sub_block μ ν hsym hH hj h2 hT hTb

include hb in
/-- Exchangeability of later particles: `E B_j(X_j)·b(X_j,X_l) = E B_j(X_j)·b(X_j,X_{j+1})`. -/
theorem Qlater_eq (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    {j : ℕ} (hj : j < N) (h2 : j + 2 ≤ N) {l : ℕ} (hl : j < l) (hlN : l < N) :
    ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k * b (X ⟨j, hj⟩) (X ⟨l, hlN⟩) k ∂ν =
      ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
        b (X ⟨j, hj⟩) (X ⟨j + 1, by omega⟩) k ∂ν := by
  set σ := Equiv.swap (⟨l, hlN⟩ : Fin N) ⟨j + 1, by omega⟩
  have hm : Measurable fun X : Config N d => X ∘ σ := measurable_pi_iff.mpr fun a => measurable_pi_apply _
  have hFm : Measurable fun X : Config N d => ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
      b (X ⟨j, hj⟩) (X ⟨l, hlN⟩) k := by
    refine Finset.measurable_sum _ fun k _ => ?_
    have hp1 : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
      (measurable_past _).prodMk (measurable_pi_apply _)
    have hp2 : Measurable fun X : Config N d => (X ⟨j, hj⟩, X ⟨l, hlN⟩) := by fun_prop
    exact ((measurable_Babs hb ν hj k).comp hp1).mul ((hb k).comp hp2)
  set F := fun X : Config N d => ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
      b (X ⟨j, hj⟩) (X ⟨l, hlN⟩) k with hF
  have e0 : ∫ X, F X ∂ν = ∫ X, F X ∂(ν.map fun X => X ∘ σ) := by rw [hsym σ]
  rw [e0, integral_map hm.aemeasurable hFm.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [hF]
  have hpast : past j hj.le (X ∘ σ) = past j hj.le X := by
    funext i
    simp only [past, Function.comp]
    congr 1
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff] <;> omega
  have hj' : (X ∘ σ) ⟨j, hj⟩ = X ⟨j, hj⟩ := by
    simp only [Function.comp]
    congr 1
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff] <;> omega
  have hl' : (X ∘ σ) ⟨l, hlN⟩ = X ⟨j + 1, by omega⟩ := by
    simp only [Function.comp, σ, Equiv.swap_apply_left]
  rw [hpast, hj', hl']

include hb hbM in
/-- **Second expectation**: `|E B_j·G - C₃| ≤ dM²(√(2D₂) + √(2D₃)) + 2dM²/N`. -/
theorem P2_sub_C3 (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hM0 : 0 ≤ M)
    {c : Torus d → Fin d → ℝ} (hc : ∀ k, Measurable fun x => c x k) (hcM : ∀ x k, |c x k| ≤ M)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) (h3j : j + 3 ≤ N) :
    |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k * Gabs b c ⟨j, hj⟩ X k ∂ν -
      C3 b ν (by omega)| ≤
      d * M ^ 2 * (Real.sqrt (2 * (DCond ν j 2 hj (by omega)).toReal) +
        Real.sqrt (2 * (DCond ν j 3 hj h3j).toReal)) + 2 * d * M ^ 2 / N := by
  have h3 : 3 ≤ N := by omega
  have h2 : j + 2 ≤ N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set e := d * M ^ 2 * (Real.sqrt (2 * (DCond ν j 2 hj h2).toReal) +
    Real.sqrt (2 * (DCond ν j 3 hj h3j).toReal)) with he
  set E := Finset.univ.erase (⟨j, hj⟩ : Fin N) with hE
  have hcard : (E.card : ℝ) = N - 1 := by
    rw [hE, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]; simp
  set Bx : Config N d → Fin d → ℝ := fun X k => Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k
    with hBx
  have hBm : ∀ k, Measurable fun X => Bx X k := fun k =>
    (measurable_Babs hb ν hj k).comp ((measurable_past _).prodMk (measurable_pi_apply _))
  have hBb : ∀ X k, |Bx X k| ≤ M := fun X k => abs_Babs_le hbM ν hj _ _ k
  have hprod : ∀ (f : Config N d → Fin d → ℝ), (∀ k, Measurable fun X => f X k) →
      (∀ X k, |f X k| ≤ M) → Integrable (fun X => ∑ k, Bx X k * f X k) ν ∧
        ∀ X, |∑ k, Bx X k * f X k| ≤ d * M ^ 2 := fun f hf hfb => by
    have hb' : ∀ X, |∑ k, Bx X k * f X k| ≤ d * M ^ 2 := fun X => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k, |Bx X k * f X k| ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
            rw [abs_mul, sq]; exact mul_le_mul (hBb X k) (hfb X k) (abs_nonneg _) hM0
        _ = d * M ^ 2 := by simp
    exact ⟨integrable_of_bdd (Finset.measurable_sum _ fun k _ => (hBm k).mul (hf k)) hb', hb'⟩
  have hbl : ∀ l : Fin N, ∀ k, Measurable fun X : Config N d => b (X ⟨j, hj⟩) (X l) k :=
    fun l k => by
      have hp : Measurable fun X : Config N d => (X ⟨j, hj⟩, X l) := by fun_prop
      exact (hb k).comp hp
  have hcj : ∀ k, Measurable fun X : Config N d => c (X ⟨j, hj⟩) k := fun k =>
    (hc k).comp (measurable_pi_apply _)
  -- pointwise expansion
  have hpt : ∀ X, ∑ k, Bx X k * Gabs b c ⟨j, hj⟩ X k = (N : ℝ)⁻¹ *
      ((∑ l ∈ E, ∑ k, Bx X k * b (X ⟨j, hj⟩) (X l) k) + ∑ k, Bx X k * c (X ⟨j, hj⟩) k) := by
    intro X
    unfold Gabs
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hE]; ring
  have hQ : ∀ l ∈ E, |∫ X, ∑ k, Bx X k * b (X ⟨j, hj⟩) (X l) k ∂ν - C3 b ν h3| ≤ e := by
    intro l hl
    have hlj : l ≠ ⟨j, hj⟩ := (Finset.mem_erase.mp hl).1
    have he2 : 0 ≤ d * M ^ 2 * Real.sqrt (2 * (DCond ν j 3 hj h3j).toReal) := by positivity
    rcases lt_or_gt_of_ne (fun h : l.val = j => hlj (Fin.ext h)) with hlt | hgt
    · have := Qpast_sub_C3 hb hbM μ hM0 ν hsym hH hj h2 h3 hlt
      refine this.trans ?_
      rw [he, mul_add]; linarith
    · rw [Qlater_eq hb ν hsym hj h2 hgt l.isLt]
      have h1 := Qnext_sub_P1 hb hbM μ hM0 ν hsym hH hj h2
      have h2' := P1_sub_C3 hb hbM μ hM0 ν hsym hH hj h3j
      calc _ ≤ |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k *
              b (X ⟨j, hj⟩) (X ⟨j + 1, by omega⟩) k ∂ν -
            ∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν| +
            |∫ X, ∑ k, Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k ^ 2 ∂ν - C3 b ν h3| :=
            abs_sub_le _ _ _
        _ ≤ e := by rw [he, mul_add]; exact add_le_add h1 h2'
  have hint : ∀ l : Fin N, Integrable (fun X => ∑ k, Bx X k * b (X ⟨j, hj⟩) (X l) k) ν :=
    fun l => (hprod _ (hbl l) fun X k => hbM _ _ _).1
  obtain ⟨hci, hcb⟩ := hprod (fun X k => c (X ⟨j, hj⟩) k) hcj fun X k => hcM _ _
  have e1 : ∫ X, ∑ k, Bx X k * Gabs b c ⟨j, hj⟩ X k ∂ν = (N : ℝ)⁻¹ *
      ((∑ l ∈ E, ∫ X, ∑ k, Bx X k * b (X ⟨j, hj⟩) (X l) k ∂ν) +
        ∫ X, ∑ k, Bx X k * c (X ⟨j, hj⟩) k ∂ν) := by
    simp_rw [hpt]
    rw [integral_const_mul, integral_add (integrable_finset_sum _ fun l _ => hint l) hci,
      integral_finset_sum _ fun l _ => hint l]
  rw [e1]
  set Q : Fin N → ℝ := fun l => ∫ X, ∑ k, Bx X k * b (X ⟨j, hj⟩) (X l) k ∂ν
  set Rc := ∫ X, ∑ k, Bx X k * c (X ⟨j, hj⟩) k ∂ν
  set C := C3 b ν h3
  have hC : |C| ≤ d * M ^ 2 := abs_integral_le_of_bdd fun X => abs_dot3_le hbM hM0 _ _ _
  have hRc : |Rc| ≤ d * M ^ 2 := abs_integral_le_of_bdd hcb
  have key : (N : ℝ)⁻¹ * ((∑ l ∈ E, Q l) + Rc) - C =
      (N : ℝ)⁻¹ * ((∑ l ∈ E, (Q l - C)) + (Rc - C)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard]
    field_simp; ring
  rw [key, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  have hsum : |∑ l ∈ E, (Q l - C)| ≤ (N - 1) * e := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ e hQ).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, hcard]
  have he0 : 0 ≤ e := by positivity
  calc (N : ℝ)⁻¹ * |(∑ l ∈ E, (Q l - C)) + (Rc - C)| ≤
      (N : ℝ)⁻¹ * ((N - 1) * e + 2 * (d * M ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hsum ?_))
          (by positivity)
        exact (abs_sub _ _).trans (by linarith)
    _ ≤ e + 2 * d * M ^ 2 / N := by
        rw [mul_add, ← mul_assoc, show (N : ℝ)⁻¹ * (N - 1) = 1 - (N : ℝ)⁻¹ by field_simp]
        have : (N : ℝ)⁻¹ * e ≥ 0 := by positivity
        rw [div_eq_mul_inv]
        nlinarith

include hb hbM in
theorem Gabs_props (hM0 : 0 ≤ M) {c : Torus d → Fin d → ℝ} (hc : ∀ k, Measurable fun x => c x k)
    (hcM : ∀ x k, |c x k| ≤ M) (j : Fin N) :
    (∀ k, Measurable fun X : Config N d => Gabs b c j X k) ∧ ∀ X k, |Gabs b c j X k| ≤ M := by
  refine ⟨fun k => ?_, fun X k => ?_⟩
  · unfold Gabs
    refine measurable_const.mul ((Finset.measurable_sum _ fun l _ => ?_).add
      ((hc k).comp (measurable_pi_apply j)))
    have hp : Measurable fun X : Config N d => (X j, X l) := by fun_prop
    exact (hb k).comp hp
  · have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos j
    unfold Gabs
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
    have h1 : |(∑ l ∈ Finset.univ.erase j, b (X j) (X l) k) + c (X j) k| ≤ N * M := by
      refine (abs_add_le _ _).trans ?_
      have h2 : |∑ l ∈ Finset.univ.erase j, b (X j) (X l) k| ≤ ((N : ℝ) - 1) * M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_card_nsmul _ _ M fun l _ => hbM _ _ _).trans (le_of_eq ?_)
        rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_sub (Fin.pos j)]
        simp
      linarith [hcM (X j) k]
    calc (N : ℝ)⁻¹ * |_| ≤ (N : ℝ)⁻¹ * (N * M) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M := by field_simp

include hb hbM in
/-- **Per-`j` bound**: `E|B_j(X_j) - G|² ≤ 10dM²(√(2D_{j,2}) + √(2D_{j,3}) + 1/N)`. -/
theorem sq_diff_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hM0 : 0 ≤ M)
    {c : Torus d → Fin d → ℝ} (hc : ∀ k, Measurable fun x => c x k) (hcM : ∀ x k, |c x k| ≤ M)
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j : ℕ} (hj : j < N) (h3j : j + 3 ≤ N) :
    ∫ X, ∑ k, (Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k - Gabs b c ⟨j, hj⟩ X k) ^ 2 ∂ν ≤
      10 * d * M ^ 2 * (Real.sqrt (2 * (DCond ν j 2 hj (by omega)).toReal) +
        Real.sqrt (2 * (DCond ν j 3 hj h3j).toReal) + 1 / N) := by
  have h3 : 3 ≤ N := by omega
  have hN : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hGm, hGb⟩ := Gabs_props hb hbM hM0 hc hcM (⟨j, hj⟩ : Fin N)
  set Bx : Config N d → Fin d → ℝ := fun X k => Babs b ν j hj (past j hj.le X) (X ⟨j, hj⟩) k
    with hBx
  set Gx : Config N d → Fin d → ℝ := fun X k => Gabs b c ⟨j, hj⟩ X k with hGx
  have hBm : ∀ k, Measurable fun X => Bx X k := fun k =>
    (measurable_Babs hb ν hj k).comp ((measurable_past _).prodMk (measurable_pi_apply _))
  have hBb : ∀ X k, |Bx X k| ≤ M := fun X k => abs_Babs_le hbM ν hj _ _ k
  have hbd : ∀ (f g : Config N d → Fin d → ℝ), (∀ k, Measurable fun X => f X k) →
      (∀ k, Measurable fun X => g X k) → (∀ X k, |f X k| ≤ M) → (∀ X k, |g X k| ≤ M) →
      Integrable (fun X => ∑ k, f X k * g X k) ν := fun f g hf hg hfb hgb =>
    integrable_of_bdd (C := d * M ^ 2) (Finset.measurable_sum _ fun k _ => (hf k).mul (hg k))
      fun X => by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ k, |f X k * g X k| ≤ ∑ _k : Fin d, M ^ 2 := Finset.sum_le_sum fun k _ => by
              rw [abs_mul, sq]; exact mul_le_mul (hfb X k) (hgb X k) (abs_nonneg _) hM0
          _ = d * M ^ 2 := by simp
  have iBB := hbd Bx Bx hBm hBm hBb hBb
  have iBG := hbd Bx Gx hBm hGm hBb hGb
  have iGG := hbd Gx Gx hGm hGm hGb hGb
  have e : ∫ X, ∑ k, (Bx X k - Gx X k) ^ 2 ∂ν =
      ∫ X, ∑ k, Bx X k ^ 2 ∂ν - 2 * ∫ X, ∑ k, Bx X k * Gx X k ∂ν + ∫ X, ∑ k, Gx X k ^ 2 ∂ν := by
    have ept : ∀ X, ∑ k, (Bx X k - Gx X k) ^ 2 =
        ∑ k, Bx X k * Bx X k - 2 * ∑ k, Bx X k * Gx X k + ∑ k, Gx X k * Gx X k := fun X => by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have sq1 : ∀ X, ∑ k, Bx X k ^ 2 = ∑ k, Bx X k * Bx X k := fun X =>
      Finset.sum_congr rfl fun k _ => sq _
    have sq2 : ∀ X, ∑ k, Gx X k ^ 2 = ∑ k, Gx X k * Gx X k := fun X =>
      Finset.sum_congr rfl fun k _ => sq _
    simp_rw [ept, sq1, sq2]
    rw [integral_add (f := fun X => ∑ k, Bx X k * Bx X k - 2 * ∑ k, Bx X k * Gx X k)
      (g := fun X => ∑ k, Gx X k * Gx X k) (iBB.sub (iBG.const_mul 2)) iGG,
      integral_sub (f := fun X => ∑ k, Bx X k * Bx X k) (g := fun X => 2 * ∑ k, Bx X k * Gx X k)
        iBB (iBG.const_mul 2), integral_const_mul]
  rw [e]
  have b1 := P1_sub_C3 hb hbM μ hM0 ν hsym hH hj h3j
  have b2 := P2_sub_C3 hb hbM μ hM0 hc hcM ν hsym hH hj h3j
  have b3 := P3_sub_C3 hb hbM hM0 hc hcM ν hsym h3 (⟨j, hj⟩ : Fin N)
  set s2 := Real.sqrt (2 * (DCond ν j 2 hj (by omega)).toReal)
  set s3 := Real.sqrt (2 * (DCond ν j 3 hj h3j).toReal)
  have hs2 : 0 ≤ s2 := Real.sqrt_nonneg _
  have hs3 : 0 ≤ s3 := Real.sqrt_nonneg _
  have hdM : 0 ≤ d * M ^ 2 := by positivity
  have hiN : 0 ≤ (N : ℝ)⁻¹ := by positivity
  rw [abs_le] at b1 b2 b3
  have e1 : (2 : ℝ) * d * M ^ 2 / N = 2 * (d * M ^ 2) * (N : ℝ)⁻¹ := by ring
  have e2 : (6 : ℝ) * d * M ^ 2 / N = 6 * (d * M ^ 2) * (N : ℝ)⁻¹ := by ring
  rw [e1] at b2; rw [e2] at b3
  have e3 : 10 * (d : ℝ) * M ^ 2 * (s2 + s3 + 1 / N) =
      10 * (d * M ^ 2) * s2 + 10 * (d * M ^ 2) * s3 + 10 * (d * M ^ 2) * (N : ℝ)⁻¹ := by ring
  rw [e3]
  nlinarith [mul_nonneg hdM hs2, mul_nonneg hdM hs3, mul_nonneg hdM hiN]

end abstract

end SharpLSI
