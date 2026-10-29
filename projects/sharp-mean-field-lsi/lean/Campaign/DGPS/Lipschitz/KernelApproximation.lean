import DGPS.Lipschitz.KernelParseval

/-!
# Kernel approximation (LIP011b)
-/


/-!
# Kernel approximation (LIP011, part II), part A: auxiliary data and weights
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem Spec.real_univ (S : Spec d) : S.mu.real univ = 1 := by
  have h := S.integral_mu (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h]
  have := S.prob
  simpa using this

theorem Spec.orth (S : Spec d) (i k : ℕ) :
    ∫ x, S.v i x * S.v k x ∂S.mu = if i = k then 1 else 0 := by
  have h := orthonormal_iff_ite.mp S.e.orthonormal i k
  rw [inner_Hw_eq_integral] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [S.ae_mu (S.ve i), S.ae_mu (S.ve k)] with x h1 h2
  rw [h1, h2]

/-- Extra upstream facts about the eigenbasis of a `Spec`: gradient representatives (LIP009/010),
the Weyl growth bound (LIP009), and the two spectral-form facts about the semigroup (LIP008). -/
structure Aux (S : Spec d) where
  hd : 0 < d
  g : ℕ → Torus d → Tangent d
  gm : ∀ i, Measurable (g i)
  gw : ∀ i, IsWeakGradient (S.v i) (g i)
  gd : ∀ i (y : Tangent d), HasFDerivAt (fun z : Tangent d => S.v i (torusLift z.ofLp))
    (InnerProductSpace.toDual ℝ (Tangent d) (g i (torusLift y.ofLp))) y
  Kc : ℝ
  Kc_nonneg : 0 ≤ Kc
  c1 : ∀ i x, |S.v i x| + ‖g i x‖ ≤ Kc * (1 + S.lam i) ^ d
  a : ℝ
  a_pos : 0 < a
  weyl : ∀ j : ℕ, 1 ≤ j → a * (j : ℝ) ^ (2 / (d : ℝ)) ≤ S.lam j
  v0 : ∀ x, S.v 0 x = 1
  κ : ℝ
  κ_nonneg : 0 ≤ κ
  sg_lip : ∀ t : ℝ, 0 < t → ∀ L : ℝ, 0 ≤ L → ∀ f u : Torus d → ℝ, TorusLipschitzWith L f →
    Continuous u → (∀ i, ∫ x, u x * S.v i x ∂S.mu =
      Real.exp (-(t * S.lam i)) * ∫ x, f x * S.v i x ∂S.mu) →
    TorusLipschitzWith (2 * L * Real.exp (κ * t)) u
  sg_sup : ∀ t : ℝ, 0 < t → ∀ M : ℝ, 0 ≤ M → ∀ f u : Torus d → ℝ, Continuous f →
    (∀ x, |f x| ≤ M) → Continuous u →
    (∀ i, ∫ x, u x * S.v i x ∂S.mu =
      Real.exp (-(t * S.lam i)) * ∫ x, f x * S.v i x ∂S.mu) → ∀ x, |u x| ≤ M

/-! ### Weights -/

theorem exp_neg_le_fact_div {s : ℝ} (hs : 0 < s) (n : ℕ) :
    Real.exp (-s) ≤ n.factorial / s ^ n := by
  have h := Real.pow_div_factorial_le_exp s hs.le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hp : 0 < s ^ n := pow_pos hs n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]
  rw [div_le_iff₀ hf] at h
  nlinarith

theorem poly_exp_le (n : ℕ) {t l : ℝ} (ht : 0 < t) (hl : 0 ≤ l) :
    (1 + l) ^ n * Real.exp (-(t * l)) ≤
      n.factorial * (2 / t) ^ n * Real.exp (t / 2) * Real.exp (-((t / 2) * l)) := by
  have h := Real.pow_div_factorial_le_exp ((t / 2) * (1 + l)) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [div_le_iff₀ hf, mul_pow] at h
  have h2 : (1 + l) ^ n ≤ n.factorial * (2 / t) ^ n * Real.exp (t / 2) * Real.exp ((t / 2) * l) := by
    have e1 : (t / 2) ^ n * (1 + l) ^ n ≤ Real.exp ((t / 2) * (1 + l)) * n.factorial := h
    have e2 : Real.exp ((t / 2) * (1 + l)) = Real.exp (t / 2) * Real.exp ((t / 2) * l) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2] at e1
    have e3 : (0 : ℝ) < (t / 2) ^ n := by positivity
    have e4 : (2 / t) ^ n * (t / 2) ^ n = 1 := by
      rw [← mul_pow]; rw [show 2 / t * (t / 2) = 1 by field_simp]; simp
    calc (1 + l) ^ n = (2 / t) ^ n * ((t / 2) ^ n * (1 + l) ^ n) := by
          rw [← mul_assoc, e4, one_mul]
      _ ≤ (2 / t) ^ n * (Real.exp (t / 2) * Real.exp ((t / 2) * l) * n.factorial) := by
          gcongr
      _ = _ := by ring
  calc (1 + l) ^ n * Real.exp (-(t * l))
      ≤ (n.factorial * (2 / t) ^ n * Real.exp (t / 2) * Real.exp ((t / 2) * l)) *
          Real.exp (-(t * l)) := by gcongr
    _ = _ := by
        rw [mul_assoc _ (Real.exp ((t / 2) * l)), ← Real.exp_add]
        rw [show (t / 2) * l + -(t * l) = -((t / 2) * l) by ring]

theorem summable_exp_lam (S : Spec d) (A : Aux S) {s : ℝ} (hs : 0 < s) :
    Summable (fun i : ℕ => Real.exp (-(s * S.lam i))) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast A.hd
  set u := s * A.a with hu
  have hu0 : 0 < u := mul_pos hs A.a_pos
  have hsum : Summable (fun j : ℕ =>
      (d.factorial : ℝ) / u ^ d * (1 / ((j + 1 : ℕ) : ℝ) ^ 2)) := by
    refine Summable.mul_left _ ?_
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun j => ?_) hsum
  have hj : 1 ≤ j + 1 := by omega
  have hw := A.weyl (j + 1) hj
  set x : ℝ := ((j + 1 : ℕ) : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 : Real.exp (-(s * S.lam (j + 1))) ≤ Real.exp (-(u * x ^ (2 / (d : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    have : u * x ^ (2 / (d : ℝ)) ≤ s * S.lam (j + 1) := by
      calc _ = s * (A.a * x ^ (2 / (d : ℝ))) := by rw [hu]; ring
        _ ≤ _ := by gcongr
    linarith
  refine h1.trans ?_
  have hy : 0 < u * x ^ (2 / (d : ℝ)) := by positivity
  refine (exp_neg_le_fact_div hy d).trans ?_
  have hxx : (x ^ (2 / (d : ℝ))) ^ d = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    rw [show 2 / (d : ℝ) * (d : ℝ) = ((2 : ℕ) : ℝ) by push_cast; field_simp, Real.rpow_natCast]
  have : (u * x ^ (2 / (d : ℝ))) ^ d = u ^ d * x ^ 2 := by
    rw [mul_pow, hxx]
  rw [this]
  apply le_of_eq
  field_simp

/-- The weight `(1+λ_i)^d e^{-tλ_i}`. -/
noncomputable def wt (S : Spec d) (t : ℝ) (i : ℕ) : ℝ :=
  (1 + S.lam i) ^ d * Real.exp (-(t * S.lam i))

theorem wt_nonneg (S : Spec d) (t : ℝ) (i : ℕ) : 0 ≤ wt S t i := by
  unfold wt
  have := S.lam_nonneg i
  positivity

theorem summable_wt (S : Spec d) (A : Aux S) {t : ℝ} (ht : 0 < t) : Summable (wt S t) := by
  have h := (summable_exp_lam S A (half_pos ht)).mul_left
    ((d.factorial : ℝ) * (2 / t) ^ d * Real.exp (t / 2))
  refine Summable.of_nonneg_of_le (wt_nonneg S t) (fun i => ?_) h
  exact poly_exp_le d ht (S.lam_nonneg i)

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part B: generic eigenfunction series
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem Aux.vbd {S : Spec d} (A : Aux S) (i : ℕ) (x : Torus d) :
    |S.v i x| ≤ A.Kc * (1 + S.lam i) ^ d :=
  (le_add_of_nonneg_right (norm_nonneg _)).trans (A.c1 i x)

theorem Aux.gbd {S : Spec d} (A : Aux S) (i : ℕ) (x : Torus d) :
    ‖A.g i x‖ ≤ A.Kc * (1 + S.lam i) ^ d :=
  (le_add_of_nonneg_left (abs_nonneg _)).trans (A.c1 i x)

/-- Coefficient summability condition. -/
def Coef (S : Spec d) (c : ℕ → ℝ) : Prop := Summable fun i => |c i| * (1 + S.lam i) ^ d

theorem Coef.summable_v {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (x : Torus d) :
    Summable fun i => ‖c i * S.v i x‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hc.mul_left A.Kc)
  rw [norm_mul, Real.norm_eq_abs]
  calc |c i| * |S.v i x| ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
        mul_le_mul_of_nonneg_left (A.vbd i x) (abs_nonneg _)
    _ = _ := by ring

theorem Coef.summable_g {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (x : Torus d) :
    Summable fun i => ‖c i • A.g i x‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) (hc.mul_left A.Kc)
  rw [norm_smul, Real.norm_eq_abs]
  calc |c i| * ‖A.g i x‖ ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
        mul_le_mul_of_nonneg_left (A.gbd i x) (abs_nonneg _)
    _ = _ := by ring

theorem tsum_cont {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) :
    Continuous fun x => ∑' i, c i * S.v i x := by
  refine continuous_tsum (u := fun i => A.Kc * (|c i| * (1 + S.lam i) ^ d))
    (fun i => continuous_const.mul (S.vc i)) (hc.mul_left A.Kc) (fun i x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |c i| * |S.v i x| ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
        mul_le_mul_of_nonneg_left (A.vbd i x) (abs_nonneg _)
    _ = _ := by ring

theorem tsum_bound {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (x : Torus d) :
    |∑' i, c i * S.v i x| ≤ A.Kc * ∑' i, |c i| * (1 + S.lam i) ^ d := by
  have h := norm_tsum_le_tsum_norm (hc.summable_v A x)
  rw [Real.norm_eq_abs] at h
  refine h.trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (hc.summable_v A x) (hc.mul_left A.Kc)
  rw [norm_mul, Real.norm_eq_abs]
  calc |c i| * |S.v i x| ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
        mul_le_mul_of_nonneg_left (A.vbd i x) (abs_nonneg _)
    _ = _ := by ring

theorem tsum_coeff {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (k : ℕ) :
    ∫ x, (∑' i, c i * S.v i x) * S.v k x ∂S.mu = c k := by
  obtain ⟨Mk, hMk0, hMk⟩ := S.vbound k
  set F : ℕ → Torus d → ℝ := fun i x => c i * S.v i x * S.v k x with hF
  have hFc : ∀ i, Continuous (F i) := fun i =>
    (continuous_const.mul (S.vc i)).mul (S.vc k)
  have hFi : ∀ i, Integrable (F i) S.mu := fun i =>
    (hFc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable fun i => ∫ x, ‖F i x‖ ∂S.mu := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _)
      (fun i => ?_) ((hc.mul_left (A.Kc * Mk)).mul_right (S.mu.real univ))
    have hb : ∀ᵐ x ∂S.mu, ‖‖F i x‖‖ ≤ (A.Kc * Mk) * (|c i| * (1 + S.lam i) ^ d) :=
      Eventually.of_forall fun x => by
        rw [norm_norm, hF]
        simp only [norm_mul, Real.norm_eq_abs]
        calc |c i| * |S.v i x| * |S.v k x|
            ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) * Mk := by
              have h1 := A.vbd i x
              have h2 := hMk x
              have h3 := abs_nonneg (c i)
              have h4 := abs_nonneg (S.v i x)
              have h5 := abs_nonneg (S.v k x)
              calc |c i| * |S.v i x| * |S.v k x| ≤ (|c i| * (A.Kc * (1 + S.lam i) ^ d)) * |S.v k x| := by
                    gcongr
                _ ≤ _ := by
                    have h6 : 0 ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
                      mul_nonneg h3 (mul_nonneg A.Kc_nonneg (pow_nonneg
                        (by linarith [S.lam_nonneg i]) _))
                    exact mul_le_mul_of_nonneg_left h2 h6
          _ = _ := by ring
    have := norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  have h1 := hasSum_integral_of_summable_integral_norm hFi hsum
  have h2 : ∀ i, ∫ x, F i x ∂S.mu = if i = k then c k else 0 := fun i => by
    have : ∫ x, F i x ∂S.mu = c i * ∫ x, S.v i x * S.v k x ∂S.mu := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hF]; ring
    rw [this, S.orth]
    by_cases h : i = k
    · subst h; simp
    · simp [h]
  simp only [h2] at h1
  have h3 := hasSum_ite_eq k (c k)
  have h4 := h1.unique h3
  rw [← h4]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hF]
  rw [tsum_mul_right]

theorem toDual_tsum (f : ℕ → Tangent d) :
    InnerProductSpace.toDual ℝ (Tangent d) (∑' i, f i) =
      ∑' i, InnerProductSpace.toDual ℝ (Tangent d) (f i) :=
  (InnerProductSpace.toDual ℝ (Tangent d)).toContinuousLinearEquiv.map_tsum

theorem tsum_hasFDerivAt {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (y : Tangent d) :
    HasFDerivAt (fun z : Tangent d => ∑' i, c i * S.v i (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d) (∑' i, c i • A.g i (torusLift y.ofLp))) y := by
  have h := hasFDerivAt_tsum (𝕜 := ℝ)
    (f := fun i (z : Tangent d) => c i * S.v i (torusLift z.ofLp))
    (f' := fun i z => c i • InnerProductSpace.toDual ℝ (Tangent d) (A.g i (torusLift z.ofLp)))
    (u := fun i => A.Kc * (|c i| * (1 + S.lam i) ^ d)) (hc.mul_left A.Kc)
    (fun i z => (A.gd i z).const_mul (c i)) (fun i z => ?_)
    (x₀ := y) ((hc.summable_v A (torusLift y.ofLp)).of_norm) y
  · convert h using 1
    rw [toDual_tsum]
    congr 1
    ext i : 1
    simp
  · rw [← map_smul, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs]
    calc |c i| * ‖A.g i (torusLift z.ofLp)‖ ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
          mul_le_mul_of_nonneg_left (A.gbd i _) (abs_nonneg _)
      _ = _ := by ring

theorem tsum_gbound {S : Spec d} (A : Aux S) {c : ℕ → ℝ} (hc : Coef S c) (x : Torus d) :
    ‖∑' i, c i • A.g i x‖ ≤ A.Kc * ∑' i, |c i| * (1 + S.lam i) ^ d := by
  refine (norm_tsum_le_tsum_norm (hc.summable_g A x)).trans ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun i => ?_) (hc.summable_g A x) (hc.mul_left A.Kc)
  rw [norm_smul, Real.norm_eq_abs]
  calc |c i| * ‖A.g i x‖ ≤ |c i| * (A.Kc * (1 + S.lam i) ^ d) :=
        mul_le_mul_of_nonneg_left (A.gbd i x) (abs_nonneg _)
    _ = _ := by ring

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part C: damped double series and truncation
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

/-- The damping factor `e^{-tλ_i}`. -/
noncomputable def ee (S : Spec d) (t : ℝ) (i : ℕ) : ℝ := Real.exp (-(t * S.lam i))

theorem ee_pos (S : Spec d) (t : ℝ) (i : ℕ) : 0 < ee S t i := Real.exp_pos _

theorem ee_le_one (S : Spec d) {t : ℝ} (ht : 0 ≤ t) (i : ℕ) : ee S t i ≤ 1 := by
  unfold ee
  rw [Real.exp_le_one_iff]
  have := S.lam_nonneg i
  nlinarith

theorem wt_eq (S : Spec d) (t : ℝ) (i : ℕ) : wt S t i = (1 + S.lam i) ^ d * ee S t i := rfl

/-- The sum of all weights. -/
noncomputable def Wsum (S : Spec d) (t : ℝ) : ℝ := ∑' i, wt S t i

theorem Wsum_nonneg (S : Spec d) (t : ℝ) : 0 ≤ Wsum S t :=
  tsum_nonneg (wt_nonneg S t)

theorem coef_of_bound {S : Spec d} (A : Aux S) {t : ℝ} (ht : 0 < t) {c : ℕ → ℝ} {M : ℝ}
    (hc : ∀ j, |c j| ≤ M * ee S t j) : Coef S c := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) ((summable_wt S A ht).mul_left M)
  · have := S.lam_nonneg j
    positivity
  · have h0 : 0 ≤ (1 + S.lam j) ^ d := by
      have := S.lam_nonneg j
      positivity
    calc |c j| * (1 + S.lam j) ^ d ≤ (M * ee S t j) * (1 + S.lam j) ^ d :=
          mul_le_mul_of_nonneg_right (hc j) h0
      _ = M * wt S t j := by rw [wt_eq]; ring

/-- The `i`-th `y`-dependent coefficient of the smoothed kernel. -/
noncomputable def cT (S : Spec d) (t : ℝ) (T : ℕ → ℕ → ℝ) (i : ℕ) (y : Torus d) : ℝ :=
  ∑' j, (ee S t j * T i j) * S.v j y

/-- The smoothed kernel series, valued in a Banach space. -/
noncomputable def Sm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Spec d) (t : ℝ)
    (T : ℕ → ℕ → ℝ) (ψ : ℕ → Torus d → E) (x y : Torus d) : E :=
  ∑' i, (ee S t i * cT S t T i y) • ψ i x

/-- The finite truncation. -/
noncomputable def Sfin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Spec d) (t : ℝ)
    (T : ℕ → ℕ → ℝ) (ψ : ℕ → Torus d → E) (N : ℕ) (x y : Torus d) : E :=
  ∑ i ∈ Finset.range N, (ee S t i * ∑ j ∈ Finset.range N, (ee S t j * T i j) * S.v j y) • ψ i x

theorem coefT {S : Spec d} (A : Aux S) {t : ℝ} (ht : 0 < t) {T : ℕ → ℕ → ℝ} {M0 : ℝ}
    (hT : ∀ i j, |T i j| ≤ M0) (i : ℕ) : Coef S (fun j => ee S t j * T i j) := by
  refine coef_of_bound A ht (M := M0) fun j => ?_
  rw [abs_mul, abs_of_pos (ee_pos S t j), mul_comm]
  exact mul_le_mul_of_nonneg_right (hT i j) (ee_pos S t j).le

theorem cT_bd {S : Spec d} (A : Aux S) {t : ℝ} (ht : 0 < t) {T : ℕ → ℕ → ℝ} {M0 : ℝ}
    (hT : ∀ i j, |T i j| ≤ M0) (i : ℕ) (y : Torus d) :
    |cT S t T i y| ≤ M0 * A.Kc * Wsum S t := by
  have h := tsum_bound A (coefT A ht hT i) y
  refine h.trans ?_
  have hs := (summable_wt S A ht).mul_left M0
  have h2 : ∑' j, |ee S t j * T i j| * (1 + S.lam j) ^ d ≤ M0 * Wsum S t := by
    rw [Wsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (coefT A ht hT i) hs
    rw [abs_mul, abs_of_pos (ee_pos S t j), wt_eq]
    have h0 : 0 ≤ (1 + S.lam j) ^ d := by
      have := S.lam_nonneg j
      positivity
    have := mul_le_mul_of_nonneg_left (hT i j) (ee_pos S t j).le
    nlinarith [mul_le_mul_of_nonneg_right this h0]
  calc A.Kc * ∑' j, |ee S t j * T i j| * (1 + S.lam j) ^ d ≤ A.Kc * (M0 * Wsum S t) :=
        mul_le_mul_of_nonneg_left h2 A.Kc_nonneg
    _ = _ := by ring

theorem u_bd {S : Spec d} (A : Aux S) {t : ℝ} {T : ℕ → ℕ → ℝ} {M0 : ℝ}
    (hT : ∀ i j, |T i j| ≤ M0) (i j : ℕ) (y : Torus d) :
    ‖(ee S t j * T i j) * S.v j y‖ ≤ M0 * A.Kc * wt S t j := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (ee_pos S t j)]
  have h0 : 0 ≤ (1 + S.lam j) ^ d := by
    have := S.lam_nonneg j
    positivity
  have h1 := mul_le_mul (hT i j) (A.vbd j y) (abs_nonneg _) (by
    have := (abs_nonneg (T i j)).trans (hT i j)
    exact this)
  have h2 := mul_le_mul_of_nonneg_left h1 (ee_pos S t j).le
  rw [wt_eq]
  nlinarith [h2]

theorem u_summable {S : Spec d} (A : Aux S) {t : ℝ} (ht : 0 < t) {T : ℕ → ℕ → ℝ} {M0 : ℝ}
    (hT : ∀ i j, |T i j| ≤ M0) (i : ℕ) (y : Torus d) :
    Summable fun j => (ee S t j * T i j) * S.v j y :=
  Summable.of_norm_bounded ((summable_wt S A ht).mul_left (M0 * A.Kc)) (fun j => u_bd A hT i j y)

theorem Sm_sub_Sfin_bd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Spec d} (A : Aux S) {t : ℝ} (ht : 0 < t) {T : ℕ → ℕ → ℝ} {M0 : ℝ}
    (hM0 : 0 ≤ M0) (hT : ∀ i j, |T i j| ≤ M0) (ψ : ℕ → Torus d → E)
    (hψ : ∀ i x, ‖ψ i x‖ ≤ A.Kc * (1 + S.lam i) ^ d) (N : ℕ) (x y : Torus d) :
    ‖Sm S t T ψ x y - Sfin S t T ψ N x y‖ ≤
      2 * (M0 * A.Kc ^ 2 * Wsum S t * ∑' i, wt S t (i + N)) := by
  set K := A.Kc with hK
  set W := Wsum S t with hW
  set τ := ∑' i, wt S t (i + N) with hτ
  have hK0 : 0 ≤ K := A.Kc_nonneg
  have hws := summable_wt S A ht
  have hws' : Summable fun i => wt S t (i + N) := (summable_nat_add_iff N).mpr hws
  have hτ0 : 0 ≤ τ := tsum_nonneg fun i => wt_nonneg S t _
  have hψ0 : ∀ i, 0 ≤ (1 + S.lam i) ^ d := fun i => by
    have := S.lam_nonneg i
    positivity
  -- tail of the inner sum
  have hin : ∀ i, |cT S t T i y - ∑ j ∈ Finset.range N, (ee S t j * T i j) * S.v j y| ≤
      M0 * K * τ := by
    intro i
    have h1 := (u_summable A ht hT i y).sum_add_tsum_nat_add N
    have h2 : cT S t T i y - ∑ j ∈ Finset.range N, (ee S t j * T i j) * S.v j y =
        ∑' j, (ee S t (j + N) * T i (j + N)) * S.v (j + N) y := by
      rw [cT]; linarith
    rw [h2, ← Real.norm_eq_abs]
    have hh := tsum_of_norm_bounded (hws'.mul_left (M0 * K)).hasSum
      (fun j => u_bd A hT i (j + N) y)
    rw [tsum_mul_left] at hh
    exact hh
  have hcT : ∀ i, |cT S t T i y| ≤ M0 * K * W := fun i => cT_bd A ht hT i y
  set a : ℕ → ℝ := fun i => ee S t i * cT S t T i y with ha
  have hterm : ∀ i, ‖a i • ψ i x‖ ≤ M0 * K ^ 2 * W * wt S t i := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, ha]
    simp only [abs_mul, abs_of_pos (ee_pos S t i)]
    have h1 := mul_le_mul (hcT i) (hψ i x) (norm_nonneg _) (by
      have := (abs_nonneg _).trans (hcT 0)
      exact this)
    have h2 := mul_le_mul_of_nonneg_left h1 (ee_pos S t i).le
    rw [wt_eq]
    nlinarith [h2]
  have hsf : Summable fun i => a i • ψ i x :=
    Summable.of_norm_bounded (hws.mul_left (M0 * K ^ 2 * W)) hterm
  have hdec := hsf.sum_add_tsum_nat_add N
  have hSm : Sm S t T ψ x y = ∑ i ∈ Finset.range N, a i • ψ i x +
      ∑' i, a (i + N) • ψ (i + N) x := by
    rw [Sm]; exact hdec.symm
  have hfin : Sm S t T ψ x y - Sfin S t T ψ N x y =
      ∑ i ∈ Finset.range N, (a i • ψ i x - (ee S t i * ∑ j ∈ Finset.range N,
        (ee S t j * T i j) * S.v j y) • ψ i x) + ∑' i, a (i + N) • ψ (i + N) x := by
    rw [hSm, Sfin, Finset.sum_sub_distrib]; abel
  rw [hfin]
  refine (norm_add_le _ _).trans ?_
  have hA : ‖∑ i ∈ Finset.range N, (a i • ψ i x - (ee S t i * ∑ j ∈ Finset.range N,
        (ee S t j * T i j) * S.v j y) • ψ i x)‖ ≤ M0 * K ^ 2 * W * τ := by
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ i ∈ Finset.range N, ‖a i • ψ i x - (ee S t i * ∑ j ∈ Finset.range N,
        (ee S t j * T i j) * S.v j y) • ψ i x‖ ≤ (M0 * K ^ 2 * τ) * wt S t i := by
      intro i _
      rw [← sub_smul, norm_smul, Real.norm_eq_abs, ha]
      simp only
      rw [← mul_sub, abs_mul, abs_of_pos (ee_pos S t i)]
      have h1 := mul_le_mul (hin i) (hψ i x) (norm_nonneg _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (ee_pos S t i).le
      rw [wt_eq]
      nlinarith [h2]
    refine (Finset.sum_le_sum hb).trans ?_
    rw [← Finset.mul_sum]
    have : ∑ i ∈ Finset.range N, wt S t i ≤ W := hws.sum_le_tsum _ (fun i _ => wt_nonneg S t i)
    have h0 : 0 ≤ M0 * K ^ 2 * τ := by positivity
    calc M0 * K ^ 2 * τ * ∑ i ∈ Finset.range N, wt S t i ≤ M0 * K ^ 2 * τ * W :=
          mul_le_mul_of_nonneg_left this h0
      _ = M0 * K ^ 2 * W * τ := by ring
  have hB : ‖∑' i, a (i + N) • ψ (i + N) x‖ ≤ M0 * K ^ 2 * W * τ := by
    have := tsum_of_norm_bounded (hws'.mul_left (M0 * K ^ 2 * W)).hasSum
      (fun i => hterm (i + N))
    rw [tsum_mul_left] at this
    exact this
  linarith

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part D: coefficient bounds and the Lipschitz transfer
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem abs_le_of_hasSum_sq {a : ℕ → ℝ} {s M : ℝ} (h : HasSum (fun i => a i ^ 2) s)
    (hs : s ≤ M ^ 2) (hM : 0 ≤ M) (i : ℕ) : |a i| ≤ M := by
  have h1 : a i ^ 2 ≤ s := le_hasSum h i (fun j _ => sq_nonneg _)
  exact abs_le_of_sq_le_sq (h1.trans hs) hM

theorem Spec.int_cont (S : Spec d) {f : Torus d → ℝ} (hf : Continuous f) : Integrable f S.mu :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Spec.integral_sq_le (S : Spec d) {f : Torus d → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : ∫ x, f x ^ 2 ∂S.mu ≤ M ^ 2 := by
  have h : ∫ x, f x ^ 2 ∂S.mu ≤ ∫ _x, M ^ 2 ∂S.mu :=
    integral_mono (S.int_cont (hf.pow 2)) (integrable_const _) fun x => by
      rw [← sq_abs (f x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  rw [integral_const, smul_eq_mul, S.real_univ, one_mul] at h
  exact h

theorem aK_abs_le (S : Spec d) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) (i : ℕ)
    (y : Torus d) : |aK S D.K i y| ≤ M :=
  abs_le_of_hasSum_sq (slice_sq S D y) (S.integral_sq_le (D.slice_cont y) fun x => hM x y)
    ((abs_nonneg _).trans (hM y y)) i

theorem TK_abs_le (S : Spec d) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) (i j : ℕ) :
    |TK S D.K i j| ≤ M :=
  abs_le_of_hasSum_sq (hasSum_TK_sq S D i)
    (S.integral_sq_le (aK_continuous S D i) fun y => aK_abs_le S D hM i y)
    ((abs_nonneg _).trans (hM 0 0)) j

theorem integral_tsum_bd (S : Spec d) {f : ℕ → Torus d → ℝ} (hc : ∀ j, Continuous (f j))
    {u : ℕ → ℝ} (hu : Summable u) (hb : ∀ j x, |f j x| ≤ u j) :
    ∫ x, ∑' j, f j x ∂S.mu = ∑' j, ∫ x, f j x ∂S.mu := by
  have hFi : ∀ j, Integrable (f j) S.mu := fun j => S.int_cont (hc j)
  have hsum : Summable fun j => ∫ x, ‖f j x‖ ∂S.mu := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _)
      (fun j => ?_) (hu.mul_right (S.mu.real univ))
    have hb' : ∀ᵐ x ∂S.mu, ‖‖f j x‖‖ ≤ u j := Eventually.of_forall fun x => by
      rw [norm_norm, Real.norm_eq_abs]; exact hb j x
    have := norm_integral_le_of_norm_le_const hb'
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)] at this
    exact this
  exact (integral_tsum_of_summable_integral_norm hFi hsum).symm

/-! ### Weak gradient algebra -/

theorem wg_sub {u v : Torus d → ℝ} {g k : Torus d → Tangent d} (hg : IsWeakGradient u g)
    (hk : IsWeakGradient v k) :
    IsWeakGradient (fun x => u x - v x) (fun x => g x - k x) :=
  (hg.add (hk.smul (-1))).congr_ae
    (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
    (Eventually.of_forall fun x => by simp [sub_eq_add_neg])

theorem wg_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) {u : ι → Torus d → ℝ}
    {g : ι → Torus d → Tangent d} (h : ∀ i ∈ s, IsWeakGradient (u i) (g i)) :
    IsWeakGradient (fun x => ∑ i ∈ s, c i * u i x) (fun x => ∑ i ∈ s, c i • g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isWeakGradient_zero (d := d))
  | insert a s ha ih =>
    have := ((h a (Finset.mem_insert_self a s)).smul (c a)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine this.congr_ae (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_) <;>
      simp [Finset.sum_insert ha]

/-! ### Lipschitz data of a kernel -/

theorem KData.B_nonneg (D : KData d) : 0 ≤ D.B := (norm_nonneg _).trans (D.G1b 0 0)

theorem KData.lip1 (D : KData d) (x x' y : Torus d) :
    |D.K x y - D.K x' y| ≤ D.B * torusDist x x' :=
  torusLipschitz_of_weakGradient_bound (D.slice_cont y) (D.g1 y) (fun x => D.G1b x y) x x'

theorem rel_sub (S : Spec d) {t : ℝ} {f1 f2 u1 u2 : Torus d → ℝ} (hf1 : Continuous f1)
    (hf2 : Continuous f2) (hu1 : Continuous u1) (hu2 : Continuous u2) {i : ℕ}
    (h1 : ∫ x, u1 x * S.v i x ∂S.mu = Real.exp (-(t * S.lam i)) * ∫ x, f1 x * S.v i x ∂S.mu)
    (h2 : ∫ x, u2 x * S.v i x ∂S.mu = Real.exp (-(t * S.lam i)) * ∫ x, f2 x * S.v i x ∂S.mu) :
    ∫ x, (u1 x - u2 x) * S.v i x ∂S.mu =
      Real.exp (-(t * S.lam i)) * ∫ x, (f1 x - f2 x) * S.v i x ∂S.mu := by
  simp only [sub_mul]
  have e1 : Integrable (fun x => u1 x * S.v i x) S.mu := S.int_cont (hu1.mul (S.vc i))
  have e2 : Integrable (fun x => u2 x * S.v i x) S.mu := S.int_cont (hu2.mul (S.vc i))
  have e3 : Integrable (fun x => f1 x * S.v i x) S.mu := S.int_cont (hf1.mul (S.vc i))
  have e4 : Integrable (fun x => f2 x * S.v i x) S.mu := S.int_cont (hf2.mul (S.vc i))
  rw [integral_sub e1 e2, integral_sub e3 e4, h1, h2, mul_sub]

section StepA

variable {S : Spec d} (A : Aux S) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) {t : ℝ}
  (ht : 0 < t)

/-- `k̃(x, y) = Σ_j e^{-tλ_j} a_j(x) v_j(y)`: the semigroup applied in the second variable. -/
noncomputable def ktil (S : Spec d) (D : KData d) (t : ℝ) (x y : Torus d) : ℝ :=
  ∑' j, (ee S t j * aK S D.swap.K j x) * S.v j y

include A hM ht in
theorem ktil_coef (x : Torus d) : Coef S (fun j => ee S t j * aK S D.swap.K j x) := by
  refine coef_of_bound A ht (M := M) fun j => ?_
  rw [abs_mul, abs_of_pos (ee_pos S t j), mul_comm]
  exact mul_le_mul_of_nonneg_right (aK_abs_le S D.swap (fun x y => hM y x) j x) (ee_pos S t j).le

include A hM ht in
theorem ktil_cont (x : Torus d) : Continuous (ktil S D t x) :=
  tsum_cont A (ktil_coef A D hM ht x)

include A hM ht in
theorem ktil_coeff (x : Torus d) (i : ℕ) :
    ∫ y, ktil S D t x y * S.v i y ∂S.mu = ee S t i * aK S D.swap.K i x :=
  tsum_coeff A (ktil_coef A D hM ht x) i

include A hM ht in
theorem ktil_rel (x : Torus d) (i : ℕ) :
    ∫ y, ktil S D t x y * S.v i y ∂S.mu =
      Real.exp (-(t * S.lam i)) * ∫ y, D.K x y * S.v i y ∂S.mu := by
  rw [ktil_coeff A D hM ht]
  rfl

include A hM ht in
theorem ktil_sup (x y : Torus d) : |ktil S D t x y| ≤ M :=
  A.sg_sup t ht M ((abs_nonneg _).trans (hM x x)) (fun y => D.K x y)
    (ktil S D t x) (D.Kc.comp (continuous_const.prodMk continuous_id)) (hM x)
    (ktil_cont A D hM ht x) (ktil_rel A D hM ht x) y

include A hM ht in
theorem ktil_lip (y : Torus d) : TorusLipschitzWith D.B (fun x => ktil S D t x y) := by
  intro x x'
  have hKc : ∀ z : Torus d, Continuous fun y => D.K z y :=
    fun z => D.Kc.comp (continuous_const.prodMk continuous_id)
  have hB0 : 0 ≤ D.B * torusDist x x' := by
    have h := (abs_nonneg _).trans (D.lip1 x x' y)
    have h2 : 0 ≤ D.B * torusDist x x' := h
    exact h2
  exact A.sg_sup t ht (D.B * torusDist x x') hB0 (fun y => D.K x y - D.K x' y)
    (fun y => ktil S D t x y - ktil S D t x' y) ((hKc x).sub (hKc x'))
    (fun y' => D.lip1 x x' y')
    ((ktil_cont A D hM ht x).sub (ktil_cont A D hM ht x'))
    (fun i => rel_sub S (hKc x) (hKc x') (ktil_cont A D hM ht x) (ktil_cont A D hM ht x')
      (ktil_rel A D hM ht x i) (ktil_rel A D hM ht x' i)) y

end StepA

theorem tangent_grad_le {u : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hu : TorusLipschitzWith L u)
    {G z : Tangent d}
    (h : HasFDerivAt (fun z : Tangent d => u (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d) G) z) : ‖G‖ ≤ L := by
  have hl : LipschitzWith L.toNNReal (fun z : Tangent d => u (torusLift z.ofLp)) := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ hL]
    calc |u (torusLift z.ofLp) - u (torusLift z'.ofLp)|
        ≤ L * torusDist (torusLift z.ofLp) (torusLift z'.ofLp) := hu _ _
      _ ≤ L * Real.sqrt (∑ j, (z.ofLp j - z'.ofLp j) ^ 2) :=
          mul_le_mul_of_nonneg_left (torusDist_liftT_le _ _) hL
      _ = L * dist z z' := by
          rw [EuclideanSpace.dist_eq]
          congr 2
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Real.dist_eq, sq_abs]
  have := h.le_of_lipschitz hl
  rwa [LinearIsometryEquiv.norm_map, Real.coe_toNNReal _ hL] at this

section StepB

variable {S : Spec d} (A : Aux S) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) {t : ℝ}
  (ht : 0 < t)

/-- The smoothed kernel `K_t = Σ_{i,j} e^{-t(λ_i+λ_j)} T_ij e_i ⊗ e_j` (iterated sum). -/
noncomputable def Kt (S : Spec d) (D : KData d) (t : ℝ) (x y : Torus d) : ℝ :=
  Sm S t (TK S D.K) S.v x y

/-- The `x`-gradient series of the smoothed kernel. -/
noncomputable def G1t (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (x y : Torus d) : Tangent d :=
  Sm S t (TK S D.K) A.g x y

theorem Kt_eq (S : Spec d) (D : KData d) (t : ℝ) (x y : Torus d) :
    Kt S D t x y = ∑' i, (ee S t i * cT S t (TK S D.K) i y) * S.v i x := by
  simp only [Kt, Sm, smul_eq_mul]

include A hM ht in
theorem Kt_coef (y : Torus d) : Coef S (fun i => ee S t i * cT S t (TK S D.K) i y) := by
  refine coef_of_bound A ht (M := M * A.Kc * Wsum S t) fun i => ?_
  rw [abs_mul, abs_of_pos (ee_pos S t i), mul_comm]
  exact mul_le_mul_of_nonneg_right (cT_bd A ht (TK_abs_le S D hM) i y) (ee_pos S t i).le

include A hM ht in
theorem Kt_cont (y : Torus d) : Continuous (fun x => Kt S D t x y) := by
  have : (fun x => Kt S D t x y) =
      fun x => ∑' i, (ee S t i * cT S t (TK S D.K) i y) * S.v i x :=
    funext fun x => Kt_eq S D t x y
  rw [this]
  exact tsum_cont A (Kt_coef A D hM ht y)

include A hM ht in
theorem Kt_coeff (y : Torus d) (i : ℕ) :
    ∫ x, Kt S D t x y * S.v i x ∂S.mu = ee S t i * cT S t (TK S D.K) i y := by
  have := tsum_coeff A (Kt_coef A D hM ht y) i
  simpa only [Kt_eq] using this

include A hM ht in
theorem ktil_int (y : Torus d) (i : ℕ) :
    ∫ x, ktil S D t x y * S.v i x ∂S.mu = cT S t (TK S D.K) i y := by
  obtain ⟨Vi, hVi0, hVi⟩ := S.vbound i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hterm : ∀ x, ktil S D t x y * S.v i x =
      ∑' j, ((ee S t j * aK S D.swap.K j x) * S.v j y) * S.v i x := fun x => by
    rw [ktil, tsum_mul_right]
  simp_rw [hterm]
  have hb : ∀ j x, |((ee S t j * aK S D.swap.K j x) * S.v j y) * S.v i x| ≤
      M * Vi * A.Kc * wt S t j := by
    intro j x
    have hee := ee_pos S t j
    have h0 : 0 ≤ (1 + S.lam j) ^ d := by
      have := S.lam_nonneg j
      positivity
    have h1 : |aK S D.swap.K j x| ≤ M := aK_abs_le S D.swap (fun x y => hM y x) j x
    have h2 := A.vbd j y
    have h3 := hVi x
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hee]
    have s1 : ee S t j * |aK S D.swap.K j x| ≤ ee S t j * M :=
      mul_le_mul_of_nonneg_left h1 hee.le
    have s2 : (ee S t j * |aK S D.swap.K j x|) * |S.v j y| ≤
        (ee S t j * M) * (A.Kc * (1 + S.lam j) ^ d) :=
      mul_le_mul s1 h2 (abs_nonneg _) (mul_nonneg hee.le hM0)
    have s3 : ((ee S t j * |aK S D.swap.K j x|) * |S.v j y|) * |S.v i x| ≤
        ((ee S t j * M) * (A.Kc * (1 + S.lam j) ^ d)) * Vi :=
      mul_le_mul s2 h3 (abs_nonneg _)
        (mul_nonneg (mul_nonneg hee.le hM0) (mul_nonneg A.Kc_nonneg h0))
    refine s3.trans (le_of_eq ?_)
    rw [wt_eq]; ring
  have hcont : ∀ j, Continuous
      (fun x => ((ee S t j * aK S D.swap.K j x) * S.v j y) * S.v i x) := fun j =>
    (((continuous_const.mul (aK_continuous S D.swap j)).mul continuous_const).mul (S.vc i))
  rw [integral_tsum_bd S (f := fun j x => ((ee S t j * aK S D.swap.K j x) * S.v j y) * S.v i x)
    (u := fun j => M * Vi * A.Kc * wt S t j) hcont
    ((summable_wt S A ht).mul_left _) hb]
  refine tsum_congr fun j => ?_
  have h1 : ∫ x, aK S D.swap.K j x * S.v i x ∂S.mu = TK S D.K i j := by
    rw [← TK_eq, TK_swap]
  calc ∫ x, ((ee S t j * aK S D.swap.K j x) * S.v j y) * S.v i x ∂S.mu
      = ∫ x, (ee S t j * S.v j y) * (aK S D.swap.K j x * S.v i x) ∂S.mu :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
    _ = (ee S t j * S.v j y) * ∫ x, aK S D.swap.K j x * S.v i x ∂S.mu := integral_const_mul _ _
    _ = (ee S t j * TK S D.K i j) * S.v j y := by rw [h1]; ring

include A hM ht in
theorem Kt_rel (y : Torus d) (i : ℕ) :
    ∫ x, Kt S D t x y * S.v i x ∂S.mu =
      Real.exp (-(t * S.lam i)) * ∫ x, ktil S D t x y * S.v i x ∂S.mu := by
  rw [Kt_coeff A D hM ht, ktil_int A D hM ht]
  rfl

include A hM ht in
theorem Kt_lip (y : Torus d) :
    TorusLipschitzWith (2 * D.B * Real.exp (A.κ * t)) (fun x => Kt S D t x y) :=
  A.sg_lip t ht D.B D.B_nonneg (fun x => ktil S D t x y) (fun x => Kt S D t x y)
    (ktil_lip A D hM ht y) (Kt_cont A D hM ht y) (fun i => Kt_rel A D hM ht y i)

include A hM ht in
theorem Kt_sup (x y : Torus d) : |Kt S D t x y| ≤ M :=
  A.sg_sup t ht M ((abs_nonneg _).trans (hM x x)) (fun x => ktil S D t x y)
    (fun x => Kt S D t x y) (torusLipschitz_continuous (ktil_lip A D hM ht y))
    (fun x => ktil_sup A D hM ht x y) (Kt_cont A D hM ht y) (fun i => Kt_rel A D hM ht y i) x

include A hM ht in
theorem Kt_hasFDerivAt (y : Torus d) (z : Tangent d) :
    HasFDerivAt (fun z : Tangent d => Kt S D t (torusLift z.ofLp) y)
      (InnerProductSpace.toDual ℝ (Tangent d) (G1t S A D t (torusLift z.ofLp) y)) z := by
  have h := tsum_hasFDerivAt A (Kt_coef A D hM ht y) z
  have e : (fun z : Tangent d => Kt S D t (torusLift z.ofLp) y) =
      fun z => ∑' i, (ee S t i * cT S t (TK S D.K) i y) * S.v i (torusLift z.ofLp) :=
    funext fun z => Kt_eq S D t _ y
  rw [e]
  exact h

include A hM ht in
theorem G1t_bound (x y : Torus d) : ‖G1t S A D t x y‖ ≤ 2 * D.B * Real.exp (A.κ * t) := by
  obtain ⟨z, hz⟩ : ∃ z : Tangent d, torusLift z.ofLp = x :=
    ⟨WithLp.toLp 2 (SharpLSI.secT x), by simp [SharpLSI.liftT_secT]⟩
  have hL : 0 ≤ 2 * D.B * Real.exp (A.κ * t) := by
    have := D.B_nonneg
    positivity
  have h := Kt_hasFDerivAt A D hM ht y z
  rw [hz] at h
  exact tangent_grad_le hL (Kt_lip A D hM ht y) h

end StepB

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part E: the finite truncations
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

/-- The finite truncation of the smoothed kernel. -/
noncomputable def Kfin (S : Spec d) (D : KData d) (t : ℝ) (N : ℕ) (x y : Torus d) : ℝ :=
  Sfin S t (TK S D.K) S.v N x y

/-- The `x`-gradient of the truncation. -/
noncomputable def G1fin (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ)
    (x y : Torus d) : Tangent d :=
  Sfin S t (TK S D.K) A.g N x y

/-- The `y`-gradient of the truncation. -/
noncomputable def G2fin (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ)
    (x y : Torus d) : Tangent d :=
  ∑ j ∈ Finset.range N, (ee S t j * ∑ i ∈ Finset.range N,
    (ee S t i * TK S D.K i j) * S.v i x) • A.g j y

theorem Kfin_eq_swap (S : Spec d) (D : KData d) (t : ℝ) (N : ℕ) (x y : Torus d) :
    Kfin S D t N x y = ∑ j ∈ Finset.range N, (ee S t j * ∑ i ∈ Finset.range N,
      (ee S t i * TK S D.K i j) * S.v i x) * S.v j y := by
  simp only [Kfin, Sfin, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem G2fin_eq (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (x y : Torus d) :
    G2fin S A D t N x y = G1fin S A D.swap t N y x := by
  have h : ∀ i j, TK S D.swap.K i j = TK S D.K j i := fun i j => TK_swap S D j i
  simp only [G2fin, G1fin, Sfin, h]

theorem Kfin_wg1 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (y : Torus d) :
    IsWeakGradient (fun x => Kfin S D t N x y) (fun x => G1fin S A D t N x y) := by
  have := wg_sum (Finset.range N)
    (fun i => ee S t i * ∑ j ∈ Finset.range N, (ee S t j * TK S D.K i j) * S.v j y)
    (fun i _ => A.gw i)
  simpa [Kfin, G1fin, Sfin] using this

theorem Kfin_wg2 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (x : Torus d) :
    IsWeakGradient (fun y => Kfin S D t N x y) (fun y => G2fin S A D t N x y) := by
  have := wg_sum (Finset.range N)
    (fun j => ee S t j * ∑ i ∈ Finset.range N, (ee S t i * TK S D.K i j) * S.v i x)
    (fun j _ => A.gw j)
  have e : (fun y => Kfin S D t N x y) = fun y => ∑ j ∈ Finset.range N,
      (ee S t j * ∑ i ∈ Finset.range N, (ee S t i * TK S D.K i j) * S.v i x) * S.v j y :=
    funext fun y => Kfin_eq_swap S D t N x y
  rw [e]
  simpa [G2fin] using this

theorem Kfin_cont (S : Spec d) (D : KData d) (t : ℝ) (N : ℕ) :
    Continuous (Function.uncurry (Kfin S D t N)) := by
  unfold Kfin Sfin
  simp only [smul_eq_mul]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.mul (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)) ?_
  · exact (continuous_const.mul continuous_const).mul ((S.vc j).comp continuous_snd)
  · exact (S.vc i).comp continuous_fst

theorem G1fin_meas (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) :
    Measurable (Function.uncurry (G1fin S A D t N)) := by
  show Measurable fun p : Torus d × Torus d => G1fin S A D t N p.1 p.2
  unfold G1fin Sfin
  refine Finset.measurable_sum _ fun i _ => ?_
  have hc : Measurable fun p : Torus d × Torus d => ee S t i * ∑ j ∈ Finset.range N,
      (ee S t j * TK S D.K i j) * S.v j p.2 := by
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact (measurable_const.mul measurable_const).mul ((S.vc j).measurable.comp measurable_snd)
  exact hc.smul ((A.gm i).comp measurable_fst)

theorem G2fin_meas (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) :
    Measurable (Function.uncurry (G2fin S A D t N)) := by
  show Measurable fun p : Torus d × Torus d => G2fin S A D t N p.1 p.2
  unfold G2fin
  refine Finset.measurable_sum _ fun j _ => ?_
  have hc : Measurable fun p : Torus d × Torus d => ee S t j * ∑ i ∈ Finset.range N,
      (ee S t i * TK S D.K i j) * S.v i p.1 := by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (measurable_const.mul measurable_const).mul ((S.vc i).measurable.comp measurable_fst)
  exact hc.smul ((A.gm j).comp measurable_snd)

theorem Kfin_hasFDerivAt1 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (y : Torus d)
    (z : Tangent d) :
    HasFDerivAt (fun z : Tangent d => Kfin S D t N (torusLift z.ofLp) y)
      (InnerProductSpace.toDual ℝ (Tangent d) (G1fin S A D t N (torusLift z.ofLp) y)) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.range N)
    (A := fun i (z : Tangent d) => (ee S t i * ∑ j ∈ Finset.range N,
      (ee S t j * TK S D.K i j) * S.v j y) * S.v i (torusLift z.ofLp))
    (A' := fun i => (ee S t i * ∑ j ∈ Finset.range N, (ee S t j * TK S D.K i j) * S.v j y) •
      InnerProductSpace.toDual ℝ (Tangent d) (A.g i (torusLift z.ofLp)))
    (x := z) (fun i _ => (A.gd i z).const_mul _)
  have e : (fun z : Tangent d => Kfin S D t N (torusLift z.ofLp) y) = fun z => ∑ i ∈ Finset.range N,
      (ee S t i * ∑ j ∈ Finset.range N, (ee S t j * TK S D.K i j) * S.v j y) *
        S.v i (torusLift z.ofLp) := by
    funext z; simp [Kfin, Sfin]
  rw [e]
  convert h using 1
  simp only [G1fin, Sfin, map_sum, map_smul]

theorem Kfin_hasFDerivAt2 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (x : Torus d)
    (z : Tangent d) :
    HasFDerivAt (fun z : Tangent d => Kfin S D t N x (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d) (G2fin S A D t N x (torusLift z.ofLp))) z := by
  have h := HasFDerivAt.fun_sum (u := Finset.range N)
    (A := fun j (z : Tangent d) => (ee S t j * ∑ i ∈ Finset.range N,
      (ee S t i * TK S D.K i j) * S.v i x) * S.v j (torusLift z.ofLp))
    (A' := fun j => (ee S t j * ∑ i ∈ Finset.range N, (ee S t i * TK S D.K i j) * S.v i x) •
      InnerProductSpace.toDual ℝ (Tangent d) (A.g j (torusLift z.ofLp)))
    (x := z) (fun j _ => (A.gd j z).const_mul _)
  have e : (fun z : Tangent d => Kfin S D t N x (torusLift z.ofLp)) = fun z => ∑ j ∈ Finset.range N,
      (ee S t j * ∑ i ∈ Finset.range N, (ee S t i * TK S D.K i j) * S.v i x) *
        S.v j (torusLift z.ofLp) := by
    funext z; exact Kfin_eq_swap S D t N x _
  rw [e]
  convert h using 1
  simp only [G2fin, map_sum, map_smul]

/-! ### Bounds -/

/-- The truncation error bound. -/
noncomputable def errB (S : Spec d) (A : Aux S) (M t : ℝ) (N : ℕ) : ℝ :=
  2 * (M * A.Kc ^ 2 * Wsum S t * ∑' i, wt S t (i + N))

theorem errB_nonneg (S : Spec d) (A : Aux S) {M : ℝ} (hM : 0 ≤ M) (t : ℝ) (N : ℕ) :
    0 ≤ errB S A M t N := by
  unfold errB
  have := Wsum_nonneg S t
  have h2 : 0 ≤ ∑' i, wt S t (i + N) := tsum_nonneg fun i => wt_nonneg S t _
  have := A.Kc_nonneg
  positivity

section Bounds

variable {S : Spec d} (A : Aux S) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) {t : ℝ}
  (ht : 0 < t)

include A hM ht in
theorem Kfin_bd (N : ℕ) (x y : Torus d) : |Kfin S D t N x y| ≤ M + errB S A M t N := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have h := Sm_sub_Sfin_bd A ht hM0 (TK_abs_le S D hM) S.v
    (fun i x => by rw [Real.norm_eq_abs]; exact A.vbd i x) N x y
  rw [Real.norm_eq_abs] at h
  have h2 := Kt_sup A D hM ht x y
  have h3 : Kt S D t x y = Sm S t (TK S D.K) S.v x y := rfl
  have h4 : Kfin S D t N x y = Sfin S t (TK S D.K) S.v N x y := rfl
  rw [← h3, ← h4] at h
  unfold errB
  calc |Kfin S D t N x y| = |Kt S D t x y - (Kt S D t x y - Kfin S D t N x y)| := by ring_nf
    _ ≤ |Kt S D t x y| + |Kt S D t x y - Kfin S D t N x y| := abs_sub _ _
    _ ≤ _ := by linarith

include A hM ht in
theorem G1fin_bd (N : ℕ) (x y : Torus d) :
    ‖G1fin S A D t N x y‖ ≤ 2 * D.B * Real.exp (A.κ * t) + errB S A M t N := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have h := Sm_sub_Sfin_bd A ht hM0 (TK_abs_le S D hM) A.g (fun i x => A.gbd i x) N x y
  have h2 := G1t_bound A D hM ht x y
  have h3 : G1t S A D t x y = Sm S t (TK S D.K) A.g x y := rfl
  have h4 : G1fin S A D t N x y = Sfin S t (TK S D.K) A.g N x y := rfl
  rw [← h3, ← h4] at h
  unfold errB
  calc ‖G1fin S A D t N x y‖ = ‖G1t S A D t x y - (G1t S A D t x y - G1fin S A D t N x y)‖ := by
        congr 1; abel
    _ ≤ ‖G1t S A D t x y‖ + ‖G1t S A D t x y - G1fin S A D t N x y‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

include A hM ht in
theorem G2fin_bd (N : ℕ) (x y : Torus d) :
    ‖G2fin S A D t N x y‖ ≤ 2 * D.B * Real.exp (A.κ * t) + errB S A M t N := by
  rw [G2fin_eq]
  exact G1fin_bd A D.swap (fun x y => hM y x) ht N y x

end Bounds

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part F: the H1 error of the truncation
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem TK_integrable (S : Spec d) {f : Torus d → Torus d → ℝ}
    (hf : Continuous (Function.uncurry f)) (i j : ℕ) :
    Integrable (fun p : Torus d × Torus d => f p.1 p.2 * (S.v i p.1 * S.v j p.2))
      (S.mu.prod S.mu) :=
  (hf.mul (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))
    ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Kfin_eq_double (S : Spec d) (D : KData d) (t : ℝ) (N : ℕ) (x y : Torus d) :
    Kfin S D t N x y = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      (ee S t a * ee S t b * TK S D.K a b) * (S.v a x * S.v b y) := by
  simp only [Kfin, Sfin, smul_eq_mul]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem TK_Kfin (S : Spec d) (D : KData d) (t : ℝ) (N i j : ℕ) :
    TK S (Kfin S D t N) i j = if i < N ∧ j < N then ee S t i * ee S t j * TK S D.K i j else 0 := by
  have hint : ∀ a b : ℕ, Integrable (fun p : Torus d × Torus d =>
      (ee S t a * ee S t b * TK S D.K a b) * (S.v a p.1 * S.v b p.2) * (S.v i p.1 * S.v j p.2))
      (S.mu.prod S.mu) := fun a b =>
    ((continuous_const.mul (((S.vc a).comp continuous_fst).mul ((S.vc b).comp continuous_snd))).mul
      (((S.vc i).comp continuous_fst).mul ((S.vc j).comp continuous_snd))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∀ p : Torus d × Torus d, Kfin S D t N p.1 p.2 * (S.v i p.1 * S.v j p.2) =
      ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        (ee S t a * ee S t b * TK S D.K a b) * (S.v a p.1 * S.v b p.2) *
          (S.v i p.1 * S.v j p.2) := fun p => by
    rw [Kfin_eq_double, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have key : TK S (Kfin S D t N) i j = ∫ p : Torus d × Torus d,
      Kfin S D t N p.1 p.2 * (S.v i p.1 * S.v j p.2) ∂S.mu.prod S.mu := rfl
  rw [key]
  simp_rw [h1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hint a b)]
  have h2 : ∀ a ∈ Finset.range N, ∫ p : Torus d × Torus d, ∑ b ∈ Finset.range N,
      (ee S t a * ee S t b * TK S D.K a b) * (S.v a p.1 * S.v b p.2) *
        (S.v i p.1 * S.v j p.2) ∂S.mu.prod S.mu =
      ∑ b ∈ Finset.range N, (ee S t a * ee S t b * TK S D.K a b) *
        ((if a = i then 1 else 0) * (if b = j then 1 else 0)) := by
    intro a _
    rw [integral_finsetSum _ (fun b _ => hint a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∀ p : Torus d × Torus d,
        (ee S t a * ee S t b * TK S D.K a b) * (S.v a p.1 * S.v b p.2) *
          (S.v i p.1 * S.v j p.2) =
        (ee S t a * ee S t b * TK S D.K a b) *
          ((S.v a p.1 * S.v i p.1) * (S.v b p.2 * S.v j p.2)) := fun p => by ring
    simp_rw [this]
    rw [integral_const_mul, integral_prod_mul (fun x => S.v a x * S.v i x)
      (fun y => S.v b y * S.v j y), S.orth, S.orth]
  rw [Finset.sum_congr rfl h2]
  by_cases hi : i < N <;> by_cases hj : j < N <;> simp [hi, hj, mul_ite]

/-- The residual kernel `K - K_fin` as a `KData`. -/
noncomputable def Dres (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (B' : ℝ)
    (h1 : ∀ x y, ‖G1fin S A D t N x y‖ ≤ B') (h2 : ∀ x y, ‖G2fin S A D t N x y‖ ≤ B') :
    KData d where
  K x y := D.K x y - Kfin S D t N x y
  G1 x y := D.G1 x y - G1fin S A D t N x y
  G2 x y := D.G2 x y - G2fin S A D t N x y
  Kc := D.Kc.sub (Kfin_cont S D t N)
  G1m := D.G1m.sub (G1fin_meas S A D t N)
  G2m := D.G2m.sub (G2fin_meas S A D t N)
  B := D.B + B'
  G1b x y := (norm_sub_le _ _).trans (add_le_add (D.G1b x y) (h1 x y))
  G2b x y := (norm_sub_le _ _).trans (add_le_add (D.G2b x y) (h2 x y))
  g1 y := wg_sub (D.g1 y) (Kfin_wg1 S A D t N y)
  g2 x := wg_sub (D.g2 x) (Kfin_wg2 S A D t N x)

theorem TK_Dres (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) (B' : ℝ)
    (h1 : ∀ x y, ‖G1fin S A D t N x y‖ ≤ B') (h2 : ∀ x y, ‖G2fin S A D t N x y‖ ≤ B') (i j : ℕ) :
    TK S (Dres S A D t N B' h1 h2).K i j =
      TK S D.K i j - (if i < N ∧ j < N then ee S t i * ee S t j * TK S D.K i j else 0) := by
  rw [← TK_Kfin]
  unfold TK
  have e1 := TK_integrable S D.Kc i j
  have e2 := TK_integrable S (Kfin_cont S D t N) i j
  have : ∀ p : Torus d × Torus d, (Dres S A D t N B' h1 h2).K p.1 p.2 * (S.v i p.1 * S.v j p.2) =
      D.K p.1 p.2 * (S.v i p.1 * S.v j p.2) -
        Kfin S D t N p.1 p.2 * (S.v i p.1 * S.v j p.2) := fun p => by
    show (D.K p.1 p.2 - Kfin S D t N p.1 p.2) * _ = _
    ring
  simp_rw [this]
  exact integral_sub e1 e2

/-- The weight `1 + λ_i + λ_j`. -/
noncomputable def pw (S : Spec d) (p : ℕ × ℕ) : ℝ := 1 + S.lam p.1 + S.lam p.2

theorem pw_nonneg (S : Spec d) (p : ℕ × ℕ) : 0 ≤ pw S p := by
  have := S.lam_nonneg p.1
  have := S.lam_nonneg p.2
  unfold pw; linarith

/-- The smoothing part of the error. -/
noncomputable def Aterm (S : Spec d) (D : KData d) (t : ℝ) (p : ℕ × ℕ) : ℝ :=
  pw S p * TK S D.K p.1 p.2 ^ 2 * (1 - ee S t p.1 * ee S t p.2) ^ 2

/-- The truncation part of the error. -/
noncomputable def Bterm (S : Spec d) (D : KData d) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  pw S p * TK S D.K p.1 p.2 ^ 2 * (if p.1 < N ∧ p.2 < N then 0 else 1)

theorem base_summable (S : Spec d) (D : KData d) :
    Summable fun p : ℕ × ℕ => pw S p * TK S D.K p.1 p.2 ^ 2 :=
  (product_parseval S D).summable

theorem Aterm_le (S : Spec d) (D : KData d) {t : ℝ} (ht : 0 ≤ t) (p : ℕ × ℕ) :
    ‖Aterm S D t p‖ ≤ pw S p * TK S D.K p.1 p.2 ^ 2 := by
  have h0 : 0 ≤ pw S p * TK S D.K p.1 p.2 ^ 2 := mul_nonneg (pw_nonneg S p) (sq_nonneg _)
  have e1 := ee_pos S t p.1
  have e2 := ee_pos S t p.2
  have e3 := ee_le_one S ht p.1
  have e4 := ee_le_one S ht p.2
  have h1 : 0 ≤ 1 - ee S t p.1 * ee S t p.2 := by nlinarith
  have h2 : 1 - ee S t p.1 * ee S t p.2 ≤ 1 := by nlinarith
  have h3 : (1 - ee S t p.1 * ee S t p.2) ^ 2 ≤ 1 := by nlinarith
  unfold Aterm
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  calc _ ≤ pw S p * TK S D.K p.1 p.2 ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 h0
    _ = _ := mul_one _

theorem Bterm_le (S : Spec d) (D : KData d) (N : ℕ) (p : ℕ × ℕ) :
    ‖Bterm S D N p‖ ≤ pw S p * TK S D.K p.1 p.2 ^ 2 := by
  have h0 : 0 ≤ pw S p * TK S D.K p.1 p.2 ^ 2 := mul_nonneg (pw_nonneg S p) (sq_nonneg _)
  unfold Bterm
  split_ifs
  · simpa using h0
  · rw [mul_one, Real.norm_eq_abs, abs_of_nonneg h0]

theorem Aterm_tendsto (S : Spec d) (D : KData d) :
    Tendsto (fun t => ∑' p, Aterm S D t p) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun t p => Aterm S D t p) (g := fun _ => (0 : ℝ))
    (bound := fun p : ℕ × ℕ => pw S p * TK S D.K p.1 p.2 ^ 2) (base_summable S D)
    (fun p => ?_) ?_
  · simpa using h
  · have hc : Continuous fun t : ℝ => Aterm S D t p := by
      unfold Aterm ee
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have e : Aterm S D 0 p = 0 := by simp [Aterm, ee]
    rwa [e] at this
  · filter_upwards [self_mem_nhdsWithin] with t ht p
    exact Aterm_le S D (le_of_lt ht) p

theorem Bterm_tendsto (S : Spec d) (D : KData d) :
    Tendsto (fun N => ∑' p, Bterm S D N p) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ))
    (f := fun N p => Bterm S D N p) (g := fun _ => (0 : ℝ))
    (bound := fun p : ℕ × ℕ => pw S p * TK S D.K p.1 p.2 ^ 2) (base_summable S D)
    (fun p => ?_) ?_
  · simpa using h
  · refine tendsto_atTop_of_eventually_const (i₀ := max p.1 p.2 + 1) fun N hN => ?_
    have h1 : p.1 < N := by omega
    have h2 : p.2 < N := by omega
    simp [Bterm, h1, h2]
  · exact Eventually.of_forall fun N p => Bterm_le S D N p

section Err

variable {S : Spec d} (A : Aux S) (D : KData d) {M : ℝ} (hM : ∀ x y, |D.K x y| ≤ M) {t : ℝ}
  (ht : 0 < t)

include A hM ht in
theorem H1err_le (N : ℕ) :
    ∫ p, (D.K p.1 p.2 - Kfin S D t N p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
      ∫ p, ‖D.G1 p.1 p.2 - G1fin S A D t N p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
      ∫ p, ‖D.G2 p.1 p.2 - G2fin S A D t N p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu ≤
    ∑' p, Aterm S D t p + ∑' p, Bterm S D N p := by
  have h1 := G1fin_bd A D hM ht N
  have h2 := G2fin_bd A D hM ht N
  have hP := product_parseval S (Dres S A D t N _ h1 h2)
  have hA := Summable.of_norm_bounded (base_summable S D) (Aterm_le S D ht.le)
  have hB := Summable.of_norm_bounded (base_summable S D) (Bterm_le S D N)
  refine hasSum_le (f := fun p : ℕ × ℕ => pw S p *
      TK S (Dres S A D t N _ h1 h2).K p.1 p.2 ^ 2) (g := fun p => Aterm S D t p + Bterm S D N p)
    (fun p => ?_) hP (hA.hasSum.add hB.hasSum)
  by_cases hb : p.1 < N ∧ p.2 < N
  · rw [TK_Dres]
    simp only [Aterm, Bterm, hb, and_self, ↓reduceIte]
    apply le_of_eq
    ring
  · rw [TK_Dres]
    simp only [Aterm, Bterm, hb, ↓reduceIte]
    have h := mul_nonneg (mul_nonneg (pw_nonneg S p) (sq_nonneg (TK S D.K p.1 p.2)))
      (sq_nonneg (1 - ee S t p.1 * ee S t p.2))
    nlinarith [h]

end Err

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part G: choice of the parameters
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem wt_tail_tendsto (S : Spec d) (A : Aux S) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ∑' i, wt S t (i + n)) atTop (𝓝 0) := by
  have hs := summable_wt S A ht
  have h := (tendsto_const_nhds (x := ∑' i, wt S t i)).sub hs.hasSum.tendsto_sum_nat
  rw [sub_self] at h
  refine h.congr fun n => ?_
  have := hs.sum_add_tsum_nat_add n
  linarith

theorem exists_tau (S : Spec d) (D : KData d) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ ε ∧ ∀ t : ℝ, 0 < t → t ≤ τ → ∑' p, Aterm S D t p ≤ ε := by
  have h := (Aterm_tendsto S D).eventually (ge_mem_nhds hε)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h
  refine ⟨min u ε, lt_min hu hε, min_le_right _ _, fun t ht0 htu => ?_⟩
  exact hsub ⟨ht0, htu.trans (min_le_left _ _)⟩

theorem exists_params {S : Spec d} (A : Aux S) (D : KData d) {Mb : ℝ} (hM : ∀ x y, |D.K x y| ≤ Mb) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ), (∀ R, 0 < t R) ∧ Antitone t ∧ (∀ R, t R ≤ 1 / ((R : ℝ) + 1)) ∧
      StrictMono m ∧ (∀ R, errB S A Mb (t R) (m R + 1) ≤ 1) ∧
      (∀ R, ∑' p, Aterm S D (t R) p + ∑' p, Bterm S D (m R + 1) p ≤ 2 / ((R : ℝ) + 1)) := by
  have hpos : ∀ R : ℕ, (0 : ℝ) < 1 / ((R : ℝ) + 1) := fun R => by positivity
  choose τ hτ0 hτe hτ using fun R : ℕ => exists_tau S D (hpos R)
  let t : ℕ → ℝ := fun R => Nat.rec (τ 0) (fun k tk => min tk (τ (k + 1))) R
  have ht_succ : ∀ R, t (R + 1) = min (t R) (τ (R + 1)) := fun R => rfl
  have ht_pos : ∀ R, 0 < t R := by
    intro R
    induction R with
    | zero => exact hτ0 0
    | succ k ih => rw [ht_succ]; exact lt_min ih (hτ0 _)
  have ht_le : ∀ R, t R ≤ τ R := by
    intro R
    cases R with
    | zero => exact le_rfl
    | succ k => rw [ht_succ]; exact min_le_right _ _
  have ht_anti : Antitone t := antitone_nat_of_succ_le fun R => by
    rw [ht_succ]; exact min_le_left _ _
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hM 0 0)
  have hn : ∀ R : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, errB S A Mb (t R) n ≤ 1 ∧
      ∑' p, Bterm S D n p ≤ 1 / ((R : ℝ) + 1) := by
    intro R
    have h1 : Tendsto (fun n => errB S A Mb (t R) n) atTop (𝓝 0) := by
      have := ((wt_tail_tendsto S A (ht_pos R)).const_mul (Mb * A.Kc ^ 2 * Wsum S (t R))).const_mul 2
      simpa [errB] using this
    have e1 := h1.eventually (ge_mem_nhds (zero_lt_one : (0 : ℝ) < 1))
    have e2 := (Bterm_tendsto S D).eventually (ge_mem_nhds (hpos R))
    exact eventually_atTop.mp (e1.and e2)
  choose n0 hn0 using hn
  refine ⟨t, fun R => R + ∑ k ∈ Finset.range (R + 1), n0 k, ht_pos, ht_anti,
    fun R => (ht_le R).trans (hτe R), ?_, fun R => ?_, fun R => ?_⟩
  · refine strictMono_nat_of_lt_succ fun R => ?_
    rw [Finset.sum_range_succ _ (R + 1)]
    omega
  · have : n0 R ≤ R + ∑ k ∈ Finset.range (R + 1), n0 k + 1 := by
      have := Finset.single_le_sum (s := Finset.range (R + 1)) (f := n0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : R < R + 1))
      omega
    exact (hn0 R _ this).1
  · have : n0 R ≤ R + ∑ k ∈ Finset.range (R + 1), n0 k + 1 := by
      have := Finset.single_le_sum (s := Finset.range (R + 1)) (f := n0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : R < R + 1))
      omega
    have h1 := hτ R (t R) (ht_pos R) (ht_le R)
    have h2 := (hn0 R _ this).2
    calc _ ≤ 1 / ((R : ℝ) + 1) + 1 / ((R : ℝ) + 1) := add_le_add h1 h2
      _ = _ := by ring

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part H: the smoothed finite-rank kernels
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

/-- The smoothed finite-rank kernel
`K_R = Σ_{i,j ≤ m} exp(-t(λ_i+λ_j)) T_ij e_i ⊗ e_j`. -/
noncomputable def smoothK (S : Spec d) (D : KData d) (t : ℝ) (m : ℕ) (x y : Torus d) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j * (S.v i x * S.v j y)

/-- The `x`-gradient of the smoothed kernel. -/
noncomputable def smoothG1 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ)
    (x y : Torus d) : Tangent d :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    (Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j * S.v j y) • A.g i x

/-- The `y`-gradient of the smoothed kernel. -/
noncomputable def smoothG2 (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ)
    (x y : Torus d) : Tangent d :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    (Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j * S.v i x) • A.g j y

theorem ee_mul_ee (S : Spec d) (t : ℝ) (i j : ℕ) :
    ee S t i * ee S t j = Real.exp (-(t * (S.lam i + S.lam j))) := by
  unfold ee
  rw [← Real.exp_add]; congr 1; ring

theorem smoothK_eq (S : Spec d) (D : KData d) (t : ℝ) (m : ℕ) :
    smoothK S D t m = Kfin S D t (m + 1) := by
  funext x y
  rw [Kfin_eq_double]
  unfold smoothK
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← ee_mul_ee]

theorem smoothG1_eq (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ) :
    smoothG1 S A D t m = G1fin S A D t (m + 1) := by
  funext x y
  unfold smoothG1 G1fin Sfin
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ee_mul_ee]
  congr 1
  ring

theorem smoothG2_eq (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ) :
    smoothG2 S A D t m = G2fin S A D t (m + 1) := by
  funext x y
  unfold smoothG2 G2fin
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ee_mul_ee]
  congr 1
  ring

/-! ### Lipschitz estimate on the product -/

theorem res_lip (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (N : ℕ) {C : ℝ}
    (hC1 : ∀ x y, ‖G1fin S A D t N x y‖ ≤ C) (hC2 : ∀ x y, ‖G2fin S A D t N x y‖ ≤ C)
    (p q : Torus d × Torus d) :
    |(D.K p.1 p.2 - Kfin S D t N p.1 p.2) - (D.K q.1 q.2 - Kfin S D t N q.1 q.2)| ≤
      2 * (D.B + C) * Real.sqrt d * dist p q := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC1 0 0)
  have hL : 0 ≤ D.B + C := add_nonneg D.B_nonneg hC0
  have hx : ∀ y, TorusLipschitzWith (D.B + C) (fun x => D.K x y - Kfin S D t N x y) := by
    intro y x x'
    have h1 := D.lip1 x x' y
    have h2 : |Kfin S D t N x y - Kfin S D t N x' y| ≤ C * torusDist x x' :=
      torusLipschitz_of_weakGradient_bound
      ((Kfin_cont S D t N).comp (continuous_id.prodMk continuous_const))
      (Kfin_wg1 S A D t N y) (fun x => hC1 x y) x x'
    calc _ = |(D.K x y - D.K x' y) - (Kfin S D t N x y - Kfin S D t N x' y)| := by ring_nf
      _ ≤ |D.K x y - D.K x' y| + |Kfin S D t N x y - Kfin S D t N x' y| := abs_sub _ _
      _ ≤ _ := by linarith
  have hy : ∀ x, TorusLipschitzWith (D.B + C) (fun y => D.K x y - Kfin S D t N x y) := by
    intro x y y'
    have h1 : |D.K x y - D.K x y'| ≤ D.B * torusDist y y' :=
      torusLipschitz_of_weakGradient_bound
      (D.Kc.comp (continuous_const.prodMk continuous_id)) (D.g2 x) (fun y => D.G2b x y) y y'
    have h2 : |Kfin S D t N x y - Kfin S D t N x y'| ≤ C * torusDist y y' :=
      torusLipschitz_of_weakGradient_bound
      ((Kfin_cont S D t N).comp (continuous_const.prodMk continuous_id))
      (Kfin_wg2 S A D t N x) (fun y => hC2 x y) y y'
    calc _ = |(D.K x y - D.K x y') - (Kfin S D t N x y - Kfin S D t N x y')| := by ring_nf
      _ ≤ |D.K x y - D.K x y'| + |Kfin S D t N x y - Kfin S D t N x y'| := abs_sub _ _
      _ ≤ _ := by linarith
  have e1 := torusLipschitz_dist hL (hx p.2) p.1 q.1
  have e2 := torusLipschitz_dist hL (hy q.1) p.2 q.2
  have d1 : dist p.1 q.1 ≤ dist p q := by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have d2 : dist p.2 q.2 ≤ dist p q := by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hs : 0 ≤ (D.B + C) * Real.sqrt d := mul_nonneg hL (Real.sqrt_nonneg _)
  calc _ ≤ |(D.K p.1 p.2 - Kfin S D t N p.1 p.2) - (D.K q.1 p.2 - Kfin S D t N q.1 p.2)| +
        |(D.K q.1 p.2 - Kfin S D t N q.1 p.2) - (D.K q.1 q.2 - Kfin S D t N q.1 q.2)| :=
        abs_sub_le _ _ _
    _ ≤ (D.B + C) * Real.sqrt d * dist p.1 q.1 + (D.B + C) * Real.sqrt d * dist p.2 q.2 :=
        add_le_add e1 e2
    _ ≤ (D.B + C) * Real.sqrt d * dist p q + (D.B + C) * Real.sqrt d * dist p q :=
        add_le_add (mul_le_mul_of_nonneg_left d1 hs) (mul_le_mul_of_nonneg_left d2 hs)
    _ = _ := by ring

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part I: the approximation theorem
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem smoothed_approximation (S : Spec d) (A : Aux S) (D : KData d) {Mb : ℝ}
    (hM : ∀ x y, |D.K x y| ≤ Mb) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (C : ℝ), (∀ R, 0 < t R) ∧ Antitone t ∧
      Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧ 0 ≤ C ∧
      (∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) ∧
      (∀ R x y, ‖smoothG1 S A D (t R) (m R) x y‖ ≤ C) ∧
      (∀ R x y, ‖smoothG2 S A D (t R) (m R) x y‖ ≤ C) ∧
      (∀ R (y : Torus d) (z : Tangent d),
        HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) (torusLift z.ofLp) y)
          (InnerProductSpace.toDual ℝ (Tangent d)
            (smoothG1 S A D (t R) (m R) (torusLift z.ofLp) y)) z) ∧
      (∀ R (x : Torus d) (z : Tangent d),
        HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) x (torusLift z.ofLp))
          (InnerProductSpace.toDual ℝ (Tangent d)
            (smoothG2 S A D (t R) (m R) x (torusLift z.ofLp))) z) ∧
      TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
        (fun p => D.K p.1 p.2) atTop ∧
      Tendsto (fun R =>
        ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
        atTop (𝓝 0) := by
  obtain ⟨t, m, ht0, hanti, ht1, hm, herr, hsum⟩ := exists_params A D hM
  have hM0 : 0 ≤ Mb := (abs_nonneg _).trans (hM 0 0)
  set C : ℝ := max (Mb + 1) (2 * D.B * Real.exp A.κ + 1) with hC
  have hCK : Mb + 1 ≤ C := le_max_left _ _
  have hCG : 2 * D.B * Real.exp A.κ + 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have ht_le1 : ∀ R, t R ≤ 1 := fun R => (ht1 R).trans (by
    rw [div_le_one (by positivity)]; have : (0:ℝ) ≤ R := Nat.cast_nonneg R; linarith)
  have hexp : ∀ R, Real.exp (A.κ * t R) ≤ Real.exp A.κ := fun R =>
    Real.exp_le_exp.mpr (by nlinarith [A.κ_nonneg, ht_le1 R])
  have hG : ∀ R, 2 * D.B * Real.exp (A.κ * t R) + errB S A Mb (t R) (m R + 1) ≤ C := fun R => by
    have := mul_le_mul_of_nonneg_left (hexp R) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) D.B_nonneg)
    linarith [herr R]
  have hbK : ∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C := fun R x y => by
    rw [smoothK_eq]
    exact (Kfin_bd A D hM (ht0 R) (m R + 1) x y).trans (by linarith [herr R])
  have hb1 : ∀ R x y, ‖smoothG1 S A D (t R) (m R) x y‖ ≤ C := fun R x y => by
    rw [smoothG1_eq]
    exact (G1fin_bd A D hM (ht0 R) (m R + 1) x y).trans (hG R)
  have hb2 : ∀ R x y, ‖smoothG2 S A D (t R) (m R) x y‖ ≤ C := fun R x y => by
    rw [smoothG2_eq]
    exact (G2fin_bd A D hM (ht0 R) (m R + 1) x y).trans (hG R)
  have hH1 : ∀ R,
      ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu
        ≤ 2 / ((R : ℝ) + 1) := fun R => by
    simp only [smoothK_eq, smoothG1_eq, smoothG2_eq]
    exact (H1err_le A D hM (ht0 R) (m R + 1)).trans (hsum R)
  have hn1 : ∀ R, 0 ≤ ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2
      ∂S.mu.prod S.mu := fun R => integral_nonneg fun p => by positivity
  have hn2 : ∀ R, 0 ≤ ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2
      ∂S.mu.prod S.mu := fun R => integral_nonneg fun p => by positivity
  have hn0 : ∀ R, 0 ≤ ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2
      ∂S.mu.prod S.mu := fun R => integral_nonneg fun p => by positivity
  have hlim : Tendsto (fun R : ℕ => 2 / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
    rw [mul_zero] at this
    refine this.congr fun R => ?_
    rw [mul_one_div]
  refine ⟨t, m, C, ht0, hanti, ?_, hm, hC0, hbK, hb1, hb2, ?_, ?_, ?_, ?_⟩
  · refine squeeze_zero (fun R => (ht0 R).le) ht1 ?_
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · intro R y z
    simp only [smoothK_eq, smoothG1_eq]
    exact Kfin_hasFDerivAt1 S A D (t R) (m R + 1) y z
  · intro R x z
    simp only [smoothK_eq, smoothG2_eq]
    exact Kfin_hasFDerivAt2 S A D (t R) (m R + 1) x z
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have : BorelSpace (Torus d × Torus d) := Prod.borelSpace (α := Torus d) (β := Torus d)
    obtain ⟨η, hη, hηh⟩ := uniform_of_lipschitz_L2 (X := Torus d × Torus d)
      (S.mu.prod S.mu) (K := 2 * (D.B + C) * Real.sqrt d)
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg D.B_nonneg hC0)) (Real.sqrt_nonneg _))
      (half_pos hε)
    have hev : ∀ᶠ R : ℕ in atTop, 2 / ((R : ℝ) + 1) ≤ η :=
      hlim.eventually (Iic_mem_nhds hη)
    filter_upwards [hev] with R hR p
    have hl := hηh (fun p => D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2)
      (fun p q => by
        simp only [smoothK_eq]
        exact res_lip S A D (t R) (m R + 1) (C := C) (fun x y => by
          rw [← smoothG1_eq]; exact hb1 R x y) (fun x y => by
          rw [← smoothG2_eq]; exact hb2 R x y) p q)
      (by linarith [hH1 R, hn1 R, hn2 R]) p
    rw [Real.dist_eq]
    linarith
  · refine squeeze_zero (fun R => by linarith [hn0 R, hn1 R, hn2 R]) hH1 hlim

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part J: semigroup facts from spectral coefficients
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace LinearPMap

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem sg_rep (S0 : Spec d) {Lg : Hw d S0.w →ₗ.[ℝ] Hw d S0.w}
    {S : ℝ≥0 → Hw d S0.w →L[ℝ] Hw d S0.w} (hS : IsWeightedSemigroup S0.w Lg S)
    (G : ℕ → Torus d → Tangent d)
    (hG : ∀ j, IsWeakGradient ((S0.e j : Hw d S0.w) : Torus d → ℝ) (G j))
    (hE : ∀ j (f : Hw d S0.w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm S0.w (G j) Y = S0.lam j * ⟪S0.e j, f⟫_ℝ)
    {t : ℝ} (ht : 0 < t) {f u : Torus d → ℝ} (hf : Continuous f) (hu : Continuous u)
    (hcoef : ∀ i, ∫ x, u x * S0.v i x ∂S0.mu =
      Real.exp (-(t * S0.lam i)) * ∫ x, f x * S0.v i x ∂S0.mu) :
    ∃ F : Hw d S0.w, ((F : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] f ∧
      u =ᵐ[S0.mu] ((S t.toNNReal F : Hw d S0.w) : Torus d → ℝ) := by
  have hFm := S0.memLp_mu hf
  have hUm := S0.memLp_mu hu
  set F : Hw d S0.w := hFm.toLp f with hFdef
  set U : Hw d S0.w := hUm.toLp u with hUdef
  have hF : ((F : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] f := hFm.coeFn_toLp
  have hU : ((U : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] u := hUm.coeFn_toLp
  obtain ⟨-, -, hc, hu'⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg S hS.selfAdjoint
    (fun f hf => (hS.mem_domain_iff f).mp hf) hS.form hS.zero hS.add hS.symm hS.cont hS.deriv
    S0.e S0.lam G hG hE
  have hee : ∀ i, ((S0.e i : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] S0.v i := fun i =>
    (S0.ae_mu (S0.ve i)).mono fun x hx => hx.symm
  have hinner : ∀ (a : Hw d S0.w) (h : Torus d → ℝ), ((a : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] h →
      ∀ i, ⟪a, S0.e i⟫_ℝ = ∫ x, h x * S0.v i x ∂S0.mu := fun a h hah i => by
    rw [inner_Hw_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hah, hee i] with x h1 h2
    rw [h1, h2]
  have hUS : U = S t.toNNReal F := by
    refine hu' F U t.toNNReal fun j => ?_
    rw [hinner U u hU j, hinner F f hF j, hcoef j, Real.coe_toNNReal _ ht.le]
    congr 2
    ring
  refine ⟨F, hF, ?_⟩
  rw [← hUS]
  exact hU.symm

theorem sg_facts (S0 : Spec d) {Lg : Hw d S0.w →ₗ.[ℝ] Hw d S0.w}
    {S : ℝ≥0 → Hw d S0.w →L[ℝ] Hw d S0.w} (hS : IsWeightedSemigroup S0.w Lg S)
    (G : ℕ → Torus d → Tangent d)
    (hG : ∀ j, IsWeakGradient ((S0.e j : Hw d S0.w) : Torus d → ℝ) (G j))
    (hE : ∀ j (f : Hw d S0.w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm S0.w (G j) Y = S0.lam j * ⟪S0.e j, f⟫_ℝ) (κ : ℝ)
    (hlip : ∀ L : ℝ, 0 ≤ L → ∀ f : Torus d → ℝ, TorusLipschitzWith L f →
      ∀ t : ℝ, 0 < t → ∀ F : Hw d S0.w, ((F : Hw d S0.w) : Torus d → ℝ) =ᵐ[S0.mu] f →
        ∃ ũ : Torus d → ℝ, ũ =ᵐ[S0.mu] ((S t.toNNReal F : Hw d S0.w) : Torus d → ℝ) ∧
          TorusLipschitzWith (2 * L * Real.exp (κ * t)) ũ)
    (hsup : ∀ (t : ℝ≥0) (F : Hw d S0.w) {M : ℝ}, 0 ≤ M →
      (∀ᵐ x ∂S0.mu, ‖((F : Hw d S0.w) : Torus d → ℝ) x‖ ≤ M) →
      ∀ᵐ x ∂S0.mu, ‖((S t F : Hw d S0.w) : Torus d → ℝ) x‖ ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ L : ℝ, 0 ≤ L → ∀ f u : Torus d → ℝ, TorusLipschitzWith L f →
      Continuous u → (∀ i, ∫ x, u x * S0.v i x ∂S0.mu =
        Real.exp (-(t * S0.lam i)) * ∫ x, f x * S0.v i x ∂S0.mu) →
      TorusLipschitzWith (2 * L * Real.exp (κ * t)) u) ∧
    (∀ t : ℝ, 0 < t → ∀ M : ℝ, 0 ≤ M → ∀ f u : Torus d → ℝ, Continuous f →
      (∀ x, |f x| ≤ M) → Continuous u →
      (∀ i, ∫ x, u x * S0.v i x ∂S0.mu =
        Real.exp (-(t * S0.lam i)) * ∫ x, f x * S0.v i x ∂S0.mu) → ∀ x, |u x| ≤ M) := by
  refine ⟨fun t ht L hL f u hf hu hcoef => ?_, fun t ht M hM f u hf hfM hu hcoef => ?_⟩
  · obtain ⟨F, hF, hUF⟩ := sg_rep S0 hS G hG hE ht (torusLipschitz_continuous hf) hu hcoef
    obtain ⟨ũ, h1, h2⟩ := hlip L hL f hf t ht F hF
    have hue : u = ũ := (Continuous.ae_eq_iff_eq S0.mu hu (torusLipschitz_continuous h2)).mp
      (hUF.trans h1.symm)
    rw [hue]; exact h2
  · obtain ⟨F, hF, hUF⟩ := sg_rep S0 hS G hG hE ht hf hu hcoef
    have hFM : ∀ᵐ x ∂S0.mu, ‖((F : Hw d S0.w) : Torus d → ℝ) x‖ ≤ M := by
      filter_upwards [hF] with x hx
      rw [hx, Real.norm_eq_abs]; exact hfM x
    have h := hsup t.toNNReal F hM hFM
    have hu_ae : ∀ᵐ x ∂S0.mu, |u x| ≤ M := by
      filter_upwards [hUF, h] with x h1 h2
      rw [h1, ← Real.norm_eq_abs]; exact h2
    by_contra hcon
    push Not at hcon
    obtain ⟨x0, hx0⟩ := hcon
    have hopen : IsOpen {x | M < |u x|} := isOpen_lt continuous_const (continuous_abs.comp hu)
    have hpos : 0 < S0.mu {x | M < |u x|} := hopen.measure_pos _ ⟨x0, hx0⟩
    have hz : S0.mu {x | M < |u x|} = 0 := by
      rw [← compl_compl {x | M < |u x|}]
      have := (ae_iff.mp hu_ae)
      simpa [not_le] using this
    exact absurd hz hpos.ne'

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part K: the Gibbs spectral data
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace LinearPMap

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.ParabolicChainRule

variable {d : ℕ}

theorem grad_continuous {v : Torus d → ℝ} {g : Torus d → Tangent d} (hv : IsC1Periodic v)
    (hg : ∀ y : Tangent d, HasFDerivAt (fun z : Tangent d => v (torusLift z.ofLp))
      (InnerProductSpace.toDual ℝ (Tangent d) (g (torusLift y.ofLp))) y) : Continuous g := by
  apply continuous_of_comp_torusLift
  have hφ : ContDiff ℝ 1 (fun z : Tangent d => v (torusLift z.ofLp)) :=
    hv.comp (PiLp.contDiff_ofLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin d => ℝ))
  have hc : Continuous fun z : Tangent d => fderiv ℝ (fun z : Tangent d => v (torusLift z.ofLp)) z :=
    hφ.continuous_fderiv (by simp)
  have key : ∀ z : Fin d → ℝ, (g ∘ torusLift) z = (InnerProductSpace.toDual ℝ (Tangent d)).symm
      (fderiv ℝ (fun z : Tangent d => v (torusLift z.ofLp)) (WithLp.toLp 2 z)) := fun z => by
    rw [(hg (WithLp.toLp 2 z)).fderiv]
    simp
  rw [show (g ∘ torusLift) = fun z => (InnerProductSpace.toDual ℝ (Tangent d)).symm
      (fderiv ℝ (fun z : Tangent d => v (torusLift z.ofLp)) (WithLp.toLp 2 z)) from funext key]
  exact (InnerProductSpace.toDual ℝ (Tangent d)).symm.continuous.comp
    (hc.comp (PiLp.continuous_toLp 2 _))


/-- The Gibbs spectral data (LIP008, LIP009, LIP010 combined). -/
theorem exists_spec_aux {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (S : Spec d) (_ : Aux S), S.w = WeightedGenerator.gibbsW Φ := by
  obtain ⟨c, C, hW0⟩ := WeightedGenerator.gibbs_wdata hL hΦ
  have hwb : ∀ᵐ x ∂haar d, c ≤ WeightedGenerator.gibbsW Φ x ∧
      WeightedGenerator.gibbsW Φ x ≤ C := Eventually.of_forall hW0.bound
  have hint := integral_gibbsW_eq_one hΦ
  obtain ⟨e, lam, G, he0, hl0, hl01, hmono, htend, hG, hE, hform, hweyl⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW0.meas hW0.pos hwb hint
  obtain ⟨Lg, S, hS, hlipS, -, -⟩ := volterra_gradient_estimate_and_semigroup_convergence hd hL hΦ hb
  obtain ⟨-, -, -, b', -, hb'B, hb'ae, -⟩ :=
    bounded_drift_mild_solution_with_continuous_gradient hd hL hΦ hb
  have hM : ∀ᵐ x ∂haar d, ‖(fun x => -DGPS.smoothGrad Φ x) x‖ ≤ LΦ := by
    filter_upwards [hb'ae, WeightedGenerator.log_gibbs_grad hL hΦ hb] with x h1 h2
    rw [← h2, ← h1]; exact hb'B x
  obtain ⟨K, hK0, hK⟩ := eigenfunction_c1_bounds_without_differentiating_drift hd hW0 hM
  have hlam_nn : ∀ j, 0 ≤ lam j := fun j => by
    have := hmono (Nat.zero_le j)
    rwa [hl0] at this
  have hnorm : ∀ j, ‖e j‖ = 1 := fun j => e.orthonormal.norm_eq_one j
  choose v g hv1 hve hge hgd hbd using fun j =>
    (hK (lam j) (hlam_nn j) (e j) (G j) (hnorm j) (hG j) (hE j)).2
  let S0 : Spec d :=
    { w := WeightedGenerator.gibbsW Φ, c := c, C := C, meas := hW0.meas, pos := hW0.pos,
      bound := hwb, prob := hint, e := e, lam := lam, lam_nonneg := hlam_nn, v := v,
      vc := fun j => (hv1 j).continuous_torus, ve := hve, form := hform }
  have hv0 : ∀ x, v 0 x = 1 := by
    have h1 : v 0 =ᵐ[haar d] fun _ => (1 : ℝ) := by
      have h2 : ((e 0 : Hw d _) : Torus d → ℝ) =ᵐ[haar d] fun _ => (1 : ℝ) :=
        (haar_ac_wMeasure hW0.pos hwb).ae_le he0
      filter_upwards [hve 0, h2] with x hx hy
      rw [hx, hy]
    exact fun x => congrFun (continuous_ae_eq (hv1 0).continuous_torus continuous_const h1) x
  have hsg := sg_facts S0 hS G hG hE (4 * LΦ ^ 2)
    (fun L hL0 f hf t ht F hF => by
      obtain ⟨ũ, -, h1, h2⟩ := hlipS L hL0 f hf t ht F hF
      exact ⟨ũ, h1, h2⟩)
    (fun t F M hM0 hF =>
      gibbs_semigroup_sup_contraction hd hL hΦ hb hS t F hM0 hF)
  refine ⟨S0, ?_, rfl⟩
  exact
    { hd := hd
      g := g
      gm := fun j => (grad_continuous (hv1 j) (hgd j)).measurable
      gw := fun j => (hG j).congr_ae (hve j).symm (hge j).symm
      gd := hgd
      Kc := K
      Kc_nonneg := hK0
      c1 := hbd
      a := 4 * Real.pi ^ 2 * c / (25 * C)
      a_pos := by
        have h1 := hW0.pos
        have h2 : 0 < C := lt_of_lt_of_le h1 ((hW0.bound 0).1.trans (hW0.bound 0).2)
        positivity
      weyl := hweyl
      v0 := hv0
      κ := 4 * LΦ ^ 2
      κ_nonneg := by positivity
      sg_lip := hsg.1
      sg_sup := hsg.2 }

end DGPS.Lipschitz.KernelApproximation


/-!
# Kernel approximation, part L: the packet theorem
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal InnerProductSpace

namespace DGPS.Lipschitz.KernelApproximation

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ}

theorem smoothed_approximation' (S : Spec d) (A : Aux S) (D : KData d) :
    ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (C : ℝ), (∀ R, 0 < t R) ∧ Antitone t ∧
      Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧ 0 ≤ C ∧
      (∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) ∧
      (∀ R x y, ‖smoothG1 S A D (t R) (m R) x y‖ ≤ C) ∧
      (∀ R x y, ‖smoothG2 S A D (t R) (m R) x y‖ ≤ C) ∧
      (∀ R (y : Torus d) (z : Tangent d),
        HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) (torusLift z.ofLp) y)
          (InnerProductSpace.toDual ℝ (Tangent d)
            (smoothG1 S A D (t R) (m R) (torusLift z.ofLp) y)) z) ∧
      (∀ R (x : Torus d) (z : Tangent d),
        HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) x (torusLift z.ofLp))
          (InnerProductSpace.toDual ℝ (Tangent d)
            (smoothG2 S A D (t R) (m R) x (torusLift z.ofLp))) z) ∧
      TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
        (fun p => D.K p.1 p.2) atTop ∧
      Tendsto (fun R =>
        ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
        ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
        atTop (𝓝 0) := by
  obtain ⟨Mb, hMb⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := Function.uncurry D.K) D.Kc.continuousOn
  exact smoothed_approximation S A D (Mb := Mb) fun x y => by
    simpa using hMb (x, y) (mem_univ _)

end DGPS.Lipschitz.KernelApproximation

namespace DGPS.Lipschitz

open DGPS DGPS.Lipschitz.KernelApproximation

theorem product_form_parseval_and_smoothed_finite_rank_kernels {d : ℕ}
    {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (S : Spec d) (A : Aux S), S.w = WeightedGenerator.gibbsW Φ ∧
      ∀ D : KData d, (∀ y, ∫ x, D.K x y ∂S.mu = 0) → (∀ x y, D.K x y = D.K y x) →
        HasSum (fun p : {p : ℕ × ℕ // 1 ≤ p.1 ∧ 1 ≤ p.2} =>
            (1 + S.lam p.1.1 + S.lam p.1.2) * TK S D.K p.1.1 p.1.2 ^ 2)
          (∫ p, D.K p.1 p.2 ^ 2 ∂S.mu.prod S.mu + ∫ p, ‖D.G1 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu
            + ∫ p, ‖D.G2 p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu) ∧
        ∃ (t : ℕ → ℝ) (m : ℕ → ℕ) (C : ℝ), (∀ R, 0 < t R) ∧ Antitone t ∧
          Filter.Tendsto t Filter.atTop (nhds 0) ∧ StrictMono m ∧ 0 ≤ C ∧
          (∀ R x y, |smoothK S D (t R) (m R) x y| ≤ C) ∧
          (∀ R x y, ‖smoothG1 S A D (t R) (m R) x y‖ ≤ C) ∧
          (∀ R x y, ‖smoothG2 S A D (t R) (m R) x y‖ ≤ C) ∧
          (∀ R (y : Torus d) (z : Tangent d),
            HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) (torusLift z.ofLp) y)
              (InnerProductSpace.toDual ℝ (Tangent d)
                (smoothG1 S A D (t R) (m R) (torusLift z.ofLp) y)) z) ∧
          (∀ R (x : Torus d) (z : Tangent d),
            HasFDerivAt (fun z : Tangent d => smoothK S D (t R) (m R) x (torusLift z.ofLp))
              (InnerProductSpace.toDual ℝ (Tangent d)
                (smoothG2 S A D (t R) (m R) x (torusLift z.ofLp))) z) ∧
          TendstoUniformly (fun R (p : Torus d × Torus d) => smoothK S D (t R) (m R) p.1 p.2)
            (fun p => D.K p.1 p.2) Filter.atTop ∧
          Filter.Tendsto (fun R =>
            ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu +
            ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
            ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)
            Filter.atTop (nhds 0) := by
  obtain ⟨S, A, hw⟩ := exists_spec_aux hd hL hΦ hb
  exact ⟨S, A, hw, fun D hc hsym =>
    ⟨product_parseval_centered S D A.v0 hc hsym, smoothed_approximation' S A D⟩⟩

end DGPS.Lipschitz

