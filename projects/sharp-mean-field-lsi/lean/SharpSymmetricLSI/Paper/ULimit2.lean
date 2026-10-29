import SharpSymmetricLSI.Paper.ULimit1

/-!
# Gaussian moments and the second-chaos orthogonality under `γ` (Phase 3, lane D; R26)

Moments `E z = 0`, `E z² = 1`, `E z⁴ = 3` of the standard Gaussian (from the moment generating
function), independence of the coordinates under `γ = gaussianRef`, and orthogonality of the
products `z_i z_j - δ_{ij}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

namespace SharpLSI

/-! ### Moments of the standard Gaussian -/

theorem deriv_poly_mul_exp {p q p' : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (p' t) t)
    (hq : ∀ t, q t = p' t + t * p t) :
    deriv (fun t => p t * rexp (t ^ 2 / 2)) = fun t => q t * rexp (t ^ 2 / 2) := by
  funext t
  have h : HasDerivAt (fun t => p t * rexp (t ^ 2 / 2))
      (p' t * rexp (t ^ 2 / 2) + p t * (rexp (t ^ 2 / 2) * (↑2 * t ^ (2 - 1) / 2))) t :=
    (hp t).mul (((hasDerivAt_pow 2 t).div_const 2).exp)
  rw [h.deriv, hq]
  push_cast; ring

theorem mgf_std_gaussian : mgf id (gaussianReal 0 1) = fun t => rexp (t ^ 2 / 2) := by
  rw [mgf_id_gaussianReal]; funext t; simp

theorem iteratedDeriv_two_exp :
    iteratedDeriv 2 (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
  have h0 : iteratedDeriv 0 (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => (1 : ℝ) * rexp (t ^ 2 / 2) := by
    simp
  have h1 : iteratedDeriv 1 (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h0]
    exact deriv_poly_mul_exp (p' := fun _ => 0) (fun t => hasDerivAt_const t 1) fun t => by ring
  rw [iteratedDeriv_succ, h1]
  exact deriv_poly_mul_exp (p' := fun _ => 1) (fun t => hasDerivAt_id' t) fun t => by ring

theorem iteratedDeriv_four_exp :
    iteratedDeriv 4 (fun t : ℝ => rexp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
  have h3 : iteratedDeriv 3 (fun t : ℝ => rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, iteratedDeriv_two_exp]
    exact deriv_poly_mul_exp (p' := fun t => ((2 : ℕ) : ℝ) * t ^ (2 - 1))
      (fun t => (hasDerivAt_pow 2 t).const_add 1) fun t => by push_cast; ring
  rw [iteratedDeriv_succ, h3]
  exact deriv_poly_mul_exp (p' := fun t => 3 * 1 + ((3 : ℕ) : ℝ) * t ^ (3 - 1))
    (fun t => ((hasDerivAt_id' t).const_mul 3).add (hasDerivAt_pow 3 t)) fun t => by push_cast; ring

theorem moment_std_gaussian (n : ℕ) :
    ∫ x, x ^ n ∂(gaussianReal 0 1) = iteratedDeriv n (fun t : ℝ => rexp (t ^ 2 / 2)) 0 := by
  rw [← mgf_std_gaussian, iteratedDeriv_mgf_zero (by simp [integrableExpSet_id_gaussianReal])]
  rfl

theorem integral_std_gaussian_id : ∫ x, x ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem integral_std_gaussian_sq : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  rw [moment_std_gaussian, iteratedDeriv_two_exp]; simp

theorem integral_std_gaussian_four : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [moment_std_gaussian, iteratedDeriv_four_exp]; simp

theorem integrable_std_gaussian_pow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · refine (memLp_id_gaussianReal (μ := 0) (v := 1) (n : ℝ≥0)).integrable_norm_pow ?_ |>.mono'
      ?_ ?_
    · exact_mod_cast hn.ne'
    · exact (measurable_id.pow_const n).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by simp [norm_pow]


/-! ### Coordinates under `γ` -/

instance gammaRef_isProb : IsProbabilityMeasure gammaRef := by unfold gammaRef; infer_instance

theorem iIndep_coord : iIndepFun (fun (m : ℕ) (ω : ℕ → ℝ) => ω m) gammaRef :=
  iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id

theorem map_coord (m : ℕ) : gammaRef.map (fun ω : ℕ → ℝ => ω m) = gaussianReal 0 1 := by
  unfold gammaRef; exact Measure.infinitePi_map_eval _ m

theorem integral_coord (m : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω m) ∂gammaRef = ∫ x, f x ∂(gaussianReal 0 1) := by
  rw [← map_coord m, integral_map (measurable_pi_apply m).aemeasurable hf.aestronglyMeasurable]

theorem integrable_coord (m : ℕ) {f : ℝ → ℝ} (hf : Measurable f)
    (hi : Integrable f (gaussianReal 0 1)) : Integrable (fun ω : ℕ → ℝ => f (ω m)) gammaRef := by
  rw [← map_coord m] at hi
  exact hi.comp_measurable (measurable_pi_apply m)

/-- Independence of one coordinate from a finite block of others. -/
theorem integral_mul_indep {u : ℕ} {T : Finset ℕ} (hu : u ∉ T) {f : ℝ → ℝ} (hf : Measurable f)
    {G : (T → ℝ) → ℝ} (hG : Measurable G) :
    ∫ ω, f (ω u) * G (fun t : T => ω t) ∂gammaRef =
      (∫ x, f x ∂(gaussianReal 0 1)) * ∫ ω, G (fun t : T => ω t) ∂gammaRef := by
  have hind := iIndep_coord.indepFun_finset {u} T (Finset.disjoint_singleton_left.mpr hu)
    fun m => measurable_pi_apply m
  have h2 := hind.comp (φ := fun w : ({u} : Finset ℕ) → ℝ => f (w ⟨u, Finset.mem_singleton_self u⟩))
    (ψ := G) (hf.comp (measurable_pi_apply _)) hG
  have h3 := h2.integral_mul_eq_mul_integral
    ((hf.comp (measurable_pi_apply u)).aestronglyMeasurable)
    ((hG.comp (by fun_prop : Measurable fun ω : ℕ → ℝ => fun t : T => ω t)).aestronglyMeasurable)
  rw [← integral_coord u hf]
  exact h3

/-! ### The products `z_i z_j - δ_{ij}` -/

/-- `z_i z_j - δ_{ij}`. -/
def chaosH (i j : ℕ) (ω : ℕ → ℝ) : ℝ := ω i * ω j - if i = j then 1 else 0

theorem chaosH_symm (i j : ℕ) : chaosH i j = chaosH j i := by
  funext ω; unfold chaosH; rw [mul_comm]; by_cases h : i = j <;> simp [h, eq_comm]

theorem measurable_chaosH (i j : ℕ) : Measurable (chaosH i j) := by
  unfold chaosH; fun_prop

theorem integral_sq_sub_one : ∫ x, (x ^ 2 - 1) ∂(gaussianReal 0 1) = 0 := by
  rw [integral_sub (integrable_std_gaussian_pow 2) (integrable_const 1), integral_std_gaussian_sq]
  simp

theorem integral_chaosH_mul_of_ne {i j k l : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) :
    ∫ ω, chaosH i j ω * chaosH k l ω ∂gammaRef = 0 := by
  set T : Finset ℕ := {j, k, l}
  have hu : i ∉ T := by simp [T, hij, hik, hil]
  let G : (T → ℝ) → ℝ := fun w => w ⟨j, by simp [T]⟩ *
    (w ⟨k, by simp [T]⟩ * w ⟨l, by simp [T]⟩ - if k = l then 1 else 0)
  have hG : Measurable G := by fun_prop
  have e : ∀ ω : ℕ → ℝ, chaosH i j ω * chaosH k l ω = id (ω i) * G (fun t : T => ω t) := by
    intro ω; simp only [chaosH, G, id, hij, ite_false]; ring
  simp_rw [e]
  rw [integral_mul_indep hu measurable_id hG]
  simp

theorem integral_chaosH_mul_eq_zero {i j k l : ℕ} (hij : i ≠ j)
    (h : (i ≠ k ∧ i ≠ l) ∨ (j ≠ k ∧ j ≠ l)) :
    ∫ ω, chaosH i j ω * chaosH k l ω ∂gammaRef = 0 := by
  rcases h with h | h
  · exact integral_chaosH_mul_of_ne hij h.1 h.2
  · rw [chaosH_symm i j]; exact integral_chaosH_mul_of_ne (Ne.symm hij) h.1 h.2

theorem integral_chaosH_diag_mul {a b : ℕ} (hab : a ≠ b) :
    ∫ ω, chaosH a a ω * chaosH b b ω ∂gammaRef = 0 := by
  set T : Finset ℕ := {b}
  have hu : a ∉ T := by simp [T, hab]
  let G : (T → ℝ) → ℝ := fun w => w ⟨b, by simp [T]⟩ ^ 2 - 1
  have hG : Measurable G := by fun_prop
  have e : ∀ ω : ℕ → ℝ, chaosH a a ω * chaosH b b ω =
      (fun x : ℝ => x ^ 2 - 1) (ω a) * G (fun t : T => ω t) := by
    intro ω; simp only [chaosH, G, ite_true]; ring
  simp_rw [e]
  have h := integral_mul_indep hu (f := fun x : ℝ => x ^ 2 - 1) (by fun_prop) hG
  rw [h, integral_sq_sub_one, zero_mul]

theorem integral_chaosH_sq_of_ne {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, chaosH i j ω ^ 2 ∂gammaRef = 1 := by
  set T : Finset ℕ := {j}
  have hu : i ∉ T := by simp [T, hij]
  let G : (T → ℝ) → ℝ := fun w => w ⟨j, by simp [T]⟩ ^ 2
  have hG : Measurable G := by fun_prop
  have e : ∀ ω : ℕ → ℝ, chaosH i j ω ^ 2 = (fun x : ℝ => x ^ 2) (ω i) * G (fun t : T => ω t) := by
    intro ω; simp only [chaosH, G, hij, ite_false]; ring
  simp_rw [e]
  have h := integral_mul_indep hu (f := fun x : ℝ => x ^ 2) (by fun_prop) hG
  rw [h, integral_std_gaussian_sq, one_mul]
  exact (integral_coord j (f := fun x => x ^ 2) (by fun_prop)).trans integral_std_gaussian_sq

theorem integral_chaosH_sq_diag (i : ℕ) : ∫ ω, chaosH i i ω ^ 2 ∂gammaRef = 2 := by
  have e : ∀ ω : ℕ → ℝ, chaosH i i ω ^ 2 = (fun x : ℝ => x ^ 4 - 2 * x ^ 2 + 1) (ω i) := by
    intro ω; simp only [chaosH, ite_true]; ring
  simp_rw [e]
  have h := integral_coord i (f := fun x : ℝ => x ^ 4 - 2 * x ^ 2 + 1) (by fun_prop)
  rw [h,
    integral_add (f := fun x : ℝ => x ^ 4 - 2 * x ^ 2) ((integrable_std_gaussian_pow 4).sub
      ((integrable_std_gaussian_pow 2).const_mul 2)) (integrable_const 1),
    integral_sub (f := fun x : ℝ => x ^ 4) (g := fun x : ℝ => 2 * x ^ 2)
      (integrable_std_gaussian_pow 4) ((integrable_std_gaussian_pow 2).const_mul 2),
    integral_const_mul, integral_std_gaussian_four, integral_std_gaussian_sq]
  simp; norm_num

/-- Orthogonality of `z_i z_j - δ_{ij}` over pairs `i ≤ j`. -/
theorem integral_chaosH_orth {p q : ℕ × ℕ} (hp : p.1 ≤ p.2) (hq : q.1 ≤ q.2) (hpq : p ≠ q) :
    ∫ ω, chaosH p.1 p.2 ω * chaosH q.1 q.2 ω ∂gammaRef = 0 := by
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  simp only [ne_eq, Prod.mk.injEq] at hp hq hpq ⊢
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      exact integral_chaosH_diag_mul fun h => hpq ⟨h, h⟩
    · simp_rw [mul_comm (chaosH i i _)]
      refine integral_chaosH_mul_eq_zero hkl ?_
      by_cases hki : k = i
      · subst hki; exact Or.inr ⟨Ne.symm hkl, Ne.symm hkl⟩
      · exact Or.inl ⟨hki, hki⟩
  · refine integral_chaosH_mul_eq_zero hij ?_
    by_contra hc
    simp only [not_or, not_and_or, not_not] at hc
    omega

/-- Second moments of the `chaosH` over pairs `i ≤ j`. -/
theorem integral_chaosH_sq {i j : ℕ} :
    ∫ ω, chaosH i j ω ^ 2 ∂gammaRef = if i = j then 2 else 1 := by
  split_ifs with h
  · subst h; exact integral_chaosH_sq_diag i
  · exact integral_chaosH_sq_of_ne h

theorem memLp_chaosH (i j : ℕ) : MemLp (chaosH i j) 2 gammaRef := by
  refine (memLp_two_iff_integrable_sq (measurable_chaosH i j).aestronglyMeasurable).mpr ?_
  have h4 : ∀ m, Integrable (fun ω : ℕ → ℝ => ω m ^ 4) gammaRef := fun m =>
    integrable_coord m (by fun_prop) (integrable_std_gaussian_pow 4)
  refine Integrable.mono' (((h4 i).add (h4 j)).add (integrable_const 2))
    ((measurable_chaosH i j).pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [chaosH, Pi.add_apply]
  have hc : (if i = j then (1 : ℝ) else 0) ^ 2 ≤ 1 := by split_ifs <;> norm_num
  nlinarith [sq_nonneg (ω i ^ 2 - ω j ^ 2), sq_nonneg (ω i * ω j - (if i = j then (1 : ℝ) else 0)),
    sq_nonneg (ω i * ω j + (if i = j then (1 : ℝ) else 0)), sq_nonneg (ω i * ω j)]

end SharpLSI
