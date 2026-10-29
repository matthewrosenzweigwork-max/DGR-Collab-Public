import Mathlib

/-!
# Bonami's inequality for multilinear polynomials in independent standard Gaussians

Let `γ = gaussianReal 0 1` and `p ≥ 1` a natural number.  For a multilinear polynomial
`mlin a z = ∑_α a α ∏_{s ∈ α} z s` of degree `≤ D` in independent standard Gaussians `z s`,
Bonami's inequality reads
`E[(mlin a)^(2p)] ≤ (2p-1)^(pD) (∑_α a α ^ 2)^p`.

The proof is the elementary induction on the number of variables:
* `gauss_moment_ineq` : `E (a + b y)^(2p) ≤ (a² + (2p-1) b²)^p` (Gaussian moments);
* `lintegral_minkowski_sq_sum` / `minkowski_sq_sum` : Minkowski for sums of squares;
* `bonami_fin` : the induction on `n`, splitting off one variable with `Fin.cons`;
* `gaussian_bonami` : transfer to an arbitrary finite index type;
* `gaussian_bonami_family`, `gaussian_bonami_curried` : the injective-family and curried forms.
We also provide the integrability of `(mlin a)^(2p)` and the `∫⁻` forms.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SharpLSI.FL.Bonami

/-! ### Gaussian moments -/

section Moments

lemma integrable_pow_mul_exp (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num) (s := (n : ℝ))
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
  simpa [Real.rpow_natCast] using h

/-- Integration by parts for the Gaussian weight: `∫ x^(n+2) e^{-x²/2} = (n+1) ∫ x^n e^{-x²/2}`. -/
lemma ibp_moment (n : ℕ) :
    ∫ x : ℝ, x ^ (n + 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
      ((n : ℝ) + 1) * ∫ x : ℝ, x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  have hud : ∀ x ∈ tsupport (fun x : ℝ => -Real.exp (-(1 / 2 : ℝ) * x ^ 2)),
      HasDerivAt (fun x : ℝ => x ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
    intro x _
    simpa using hasDerivAt_pow (n + 1) x
  have hvd : ∀ x ∈ tsupport (fun x : ℝ => x ^ (n + 1)),
      HasDerivAt (fun x : ℝ => -Real.exp (-(1 / 2 : ℝ) * x ^ 2))
        (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => -(1 / 2 : ℝ) * x ^ 2) (-(1 / 2 : ℝ) * (2 * x)) x := by
      have := (hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))
      convert this using 1
      simp
    have h2 := h1.exp.neg
    convert h2 using 1
    ring
  have i1 : Integrable ((fun x : ℝ => x ^ (n + 1)) *
      (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2))) :=
    (integrable_pow_mul_exp (n + 2)).congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]; ring)
  have i2 : Integrable ((fun x : ℝ => ((n : ℝ) + 1) * x ^ n) *
      (fun x : ℝ => -Real.exp (-(1 / 2 : ℝ) * x ^ 2))) :=
    (((integrable_pow_mul_exp n).const_mul ((n : ℝ) + 1)).neg).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have i3 : Integrable ((fun x : ℝ => x ^ (n + 1)) *
      (fun x : ℝ => -Real.exp (-(1 / 2 : ℝ) * x ^ 2))) :=
    ((integrable_pow_mul_exp (n + 1)).neg).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable hud hvd i1 i2 i3
  have h3 : ∫ x : ℝ, ((n : ℝ) + 1) * x ^ n * (-Real.exp (-(1 / 2 : ℝ) * x ^ 2)) =
      -(((n : ℝ) + 1) * ∫ x : ℝ, x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1
    funext x
    ring
  calc ∫ x : ℝ, x ^ (n + 2) * Real.exp (-(1 / 2 : ℝ) * x ^ 2)
      = ∫ x : ℝ, x ^ (n + 1) * (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
        congr 1; funext x; ring
    _ = -∫ x : ℝ, ((n : ℝ) + 1) * x ^ n * (-Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := key
    _ = ((n : ℝ) + 1) * ∫ x : ℝ, x ^ n * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        rw [h3, neg_neg]

lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

lemma gauss_moment_eq (k : ℕ) :
    ∫ x, x ^ k ∂gaussianReal 0 1 =
      (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, x ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, gaussianPDFReal_std]
  ring

/-- The moment recursion `E y^(n+2) = (n+1) E y^n`. -/
lemma gauss_moment_succ_succ (n : ℕ) :
    ∫ x, x ^ (n + 2) ∂gaussianReal 0 1 = ((n : ℝ) + 1) * ∫ x, x ^ n ∂gaussianReal 0 1 := by
  rw [gauss_moment_eq, gauss_moment_eq, ibp_moment n]
  ring

lemma gauss_moment_one : ∫ x : ℝ, x ^ 1 ∂gaussianReal 0 1 = 0 := by
  simp

lemma gauss_moment_odd (k : ℕ) : ∫ x : ℝ, x ^ (2 * k + 1) ∂gaussianReal 0 1 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := gauss_moment_succ_succ (2 * k + 1)
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, h, ih, mul_zero]

/-- `(2k-1)!! = ∏_{i<k} (2i+1)`. -/
def dfac (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, (2 * i + 1)

lemma dfac_succ (k : ℕ) : dfac (k + 1) = dfac k * (2 * k + 1) := by
  simp [dfac, Finset.prod_range_succ]

lemma gauss_moment_even (k : ℕ) : ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1 = (dfac k : ℝ) := by
  induction k with
  | zero => simp [dfac]
  | succ k ih =>
    have h := gauss_moment_succ_succ (2 * k)
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, h, ih, dfac_succ]
    push_cast
    ring

lemma integrable_pow_gauss (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have hmem : MemLp id (k : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' (k : ℝ≥0∞) (ENNReal.natCast_ne_top _)
  have h := hmem.integrable_norm_pow'
  have hm : AEStronglyMeasurable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
    (measurable_id.pow_const k).aestronglyMeasurable
  rw [← integrable_norm_iff hm]
  simpa [norm_pow] using h

end Moments

/-! ### The combinatorial inequality -/

section Comb

lemma choose_dfac_le (p : ℕ) : ∀ k : ℕ, k ≤ p →
    (Nat.choose (2 * p) (2 * k) : ℝ) * (dfac k : ℝ) ≤
      (Nat.choose p k : ℝ) * (2 * (p : ℝ) - 1) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp [dfac]
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    obtain ⟨r, hr⟩ : ∃ r, p = k + 1 + r := ⟨p - (k + 1), by omega⟩
    have h1 := Nat.choose_succ_right_eq (2 * p) (2 * k)
    have h2 := Nat.choose_succ_right_eq (2 * p) (2 * k + 1)
    have h3 := Nat.choose_succ_right_eq p k
    have e1 : 2 * p - 2 * k = 2 * r + 2 := by omega
    have e2 : 2 * p - (2 * k + 1) = 2 * r + 1 := by omega
    have e3 : p - k = r + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    have hpr : (p : ℝ) = k + 1 + r := by exact_mod_cast hr
    have h1' : (Nat.choose (2 * p) (2 * k + 1) : ℝ) * (2 * k + 1) =
        (Nat.choose (2 * p) (2 * k) : ℝ) * (2 * r + 2) := by exact_mod_cast h1
    have h2' : (Nat.choose (2 * p) (2 * k + 1 + 1) : ℝ) * (2 * k + 1 + 1) =
        (Nat.choose (2 * p) (2 * k + 1) : ℝ) * (2 * r + 1) := by exact_mod_cast h2
    have h3' : (Nat.choose p (k + 1) : ℝ) * (k + 1) = (Nat.choose p k : ℝ) * (r + 1) := by
      exact_mod_cast h3
    have hc : 2 * (p : ℝ) - 1 = 2 * k + 2 * r + 1 := by rw [hpr]; ring
    rw [hc] at ih' ⊢
    rw [dfac_succ, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    push_cast
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    refine le_of_mul_le_mul_left ?_ hk1
    have hq : (0 : ℝ) ≤ (Nat.choose p k : ℝ) * (2 * (k : ℝ) + 2 * r + 1) ^ k := by positivity
    calc ((k : ℝ) + 1) * ((Nat.choose (2 * p) (2 * k + 1 + 1) : ℝ) *
          ((dfac k : ℝ) * (2 * k + 1)))
        = (Nat.choose (2 * p) (2 * k) : ℝ) * (dfac k : ℝ) * ((r + 1) * (2 * r + 1)) := by
          linear_combination ((dfac k : ℝ) * (2 * k + 1) / 2) * h2' +
            ((dfac k : ℝ) * (2 * r + 1) / 2) * h1'
      _ ≤ (Nat.choose p k : ℝ) * (2 * (k : ℝ) + 2 * r + 1) ^ k * ((r + 1) * (2 * r + 1)) :=
          mul_le_mul_of_nonneg_right ih' (by positivity)
      _ ≤ (Nat.choose p k : ℝ) * (2 * (k : ℝ) + 2 * r + 1) ^ k *
            ((r + 1) * (2 * k + 2 * r + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ hq
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith
      _ = ((k : ℝ) + 1) * ((Nat.choose p (k + 1) : ℝ) *
          ((2 * (k : ℝ) + 2 * r + 1) ^ k * (2 * k + 2 * r + 1))) := by
          linear_combination (-((2 * (k : ℝ) + 2 * r + 1) ^ k * (2 * k + 2 * r + 1))) * h3'

end Comb

/-! ### Item 1: the Gaussian moment inequality -/

lemma sum_range_two_mul_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (hodd : ∀ k, f (2 * k + 1) = 0) (p : ℕ) :
    ∑ m ∈ Finset.range (2 * p + 1), f m = ∑ k ∈ Finset.range (p + 1), f (2 * k) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 1 + 1 by ring,
      Finset.sum_range_succ f (2 * p + 1 + 1), Finset.sum_range_succ f (2 * p + 1), ih,
      Finset.sum_range_succ (fun k => f (2 * k)) (p + 1), hodd p, add_zero,
      show 2 * p + 1 + 1 = 2 * (p + 1) by ring]

/-- **Item 1.**  For a standard Gaussian `y`, `E (a + b y)^(2p) ≤ (a² + (2p-1) b²)^p`. -/
theorem gauss_moment_ineq (p : ℕ) (_hp : 1 ≤ p) (a b : ℝ) :
    ∫ y, (a + b * y) ^ (2 * p) ∂gaussianReal 0 1 ≤
      (a ^ 2 + ((2 * p : ℝ) - 1) * b ^ 2) ^ p := by
  have hexp : ∀ y : ℝ, (a + b * y) ^ (2 * p) =
      ∑ m ∈ Finset.range (2 * p + 1),
        (b ^ m * a ^ (2 * p - m) * (Nat.choose (2 * p) m : ℝ)) * y ^ m := by
    intro y
    rw [add_comm a (b * y), add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]
    ring
  have hL : ∫ y, (a + b * y) ^ (2 * p) ∂gaussianReal 0 1 =
      ∑ m ∈ Finset.range (2 * p + 1),
        (b ^ m * a ^ (2 * p - m) * (Nat.choose (2 * p) m : ℝ)) *
          ∫ y, y ^ m ∂gaussianReal 0 1 := by
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun m _ => (integrable_pow_gauss m).const_mul _)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
  have hodd : ∀ k, (fun m : ℕ => (b ^ m * a ^ (2 * p - m) * (Nat.choose (2 * p) m : ℝ)) *
      ∫ y, y ^ m ∂gaussianReal 0 1) (2 * k + 1) = 0 := by
    intro k
    simp only [gauss_moment_odd, mul_zero]
  rw [hL, sum_range_two_mul_succ _ hodd p]
  have hR : (a ^ 2 + ((2 * p : ℝ) - 1) * b ^ 2) ^ p =
      ∑ k ∈ Finset.range (p + 1),
        (((2 * p : ℝ) - 1) * b ^ 2) ^ k * (a ^ 2) ^ (p - k) * (Nat.choose p k : ℝ) := by
    rw [add_comm (a ^ 2), add_pow]
  rw [hR]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkp : k ≤ p := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  simp only [gauss_moment_even]
  have h := choose_dfac_le p k hkp
  have hW : 0 ≤ (b ^ 2) ^ k * (a ^ 2) ^ (p - k) := by positivity
  have e1 : b ^ (2 * k) = (b ^ 2) ^ k := by rw [pow_mul]
  have e2 : a ^ (2 * p - 2 * k) = (a ^ 2) ^ (p - k) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [e1, e2, mul_pow]
  have := mul_le_mul_of_nonneg_left h hW
  nlinarith [this]

/-! ### Minkowski for sums of squares -/

section Minkowski

variable {Ω : Type*} [MeasurableSpace Ω]

lemma memLp_of_integrable_pow {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    {q : ℕ} (hq : q ≠ 0) (h : Integrable (fun ω => f ω ^ (2 * q)) μ) :
    MemLp f ((2 * q : ℕ) : ℝ≥0∞) μ := by
  rw [← integrable_norm_rpow_iff hf (Nat.cast_ne_zero.2 (by omega)) (ENNReal.natCast_ne_top _)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  show f ω ^ (2 * q) = |f ω| ^ (2 * q)
  rw [pow_mul, pow_mul, sq_abs]

lemma integrable_pow_of_memLp {μ : Measure Ω} {f : Ω → ℝ} {q : ℕ} (hq : q ≠ 0)
    (h : MemLp f ((2 * q : ℕ) : ℝ≥0∞) μ) : Integrable (fun ω => f ω ^ (2 * q)) μ := by
  have := h.integrable_norm_pow (by omega : 2 * q ≠ 0)
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  rw [pow_mul, pow_mul, sq_abs]

lemma memLp_of_integrable_pow_nonneg {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (hnn : ∀ ω, 0 ≤ f ω) {p : ℕ} (hp : p ≠ 0) (h : Integrable (fun ω => f ω ^ p) μ) :
    MemLp f (p : ℝ≥0∞) μ := by
  rw [← integrable_norm_rpow_iff hf (Nat.cast_ne_zero.2 hp) (ENNReal.natCast_ne_top _)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [abs_of_nonneg (hnn ω)]

lemma eLpNorm_eq_root {μ : Measure Ω} {g : Ω → ℝ} (hnn : ∀ ω, 0 ≤ g ω) {p : ℕ} (hp : p ≠ 0)
    (hg : MemLp g (p : ℝ≥0∞) μ) :
    eLpNorm g (p : ℝ≥0∞) μ = ENNReal.ofReal ((∫ ω, g ω ^ p ∂μ) ^ ((1 : ℝ) / p)) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (Nat.cast_ne_zero.2 hp) (ENNReal.natCast_ne_top _)]
  have hab : ∀ a, |g a| = g a := fun a => abs_of_nonneg (hnn a)
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs, one_div, hab]

/-- Minkowski's inequality for a finite sum of nonnegative functions with `f i ^ p` integrable:
`‖∑ f i‖_p ≤ ∑ ‖f i‖_p`, written for the `p`-th powers. -/
theorem minkowski_pow_sum {μ : Measure Ω} {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) {p : ℕ}
    (hp : 1 ≤ p) (hmeas : ∀ i, AEStronglyMeasurable (f i) μ) (hnn : ∀ i ω, 0 ≤ f i ω)
    (hint : ∀ i, Integrable (fun ω => f i ω ^ p) μ) :
    Integrable (fun ω => (∑ i ∈ s, f i ω) ^ p) μ ∧
      ∫ ω, (∑ i ∈ s, f i ω) ^ p ∂μ ≤
        (∑ i ∈ s, (∫ ω, f i ω ^ p ∂μ) ^ ((1 : ℝ) / p)) ^ p := by
  have hp0 : p ≠ 0 := by omega
  have hmem : ∀ i, MemLp (f i) (p : ℝ≥0∞) μ := fun i =>
    memLp_of_integrable_pow_nonneg (hmeas i) (hnn i) hp0 (hint i)
  have hsum : MemLp (fun ω => ∑ i ∈ s, f i ω) (p : ℝ≥0∞) μ :=
    memLp_finsetSum s (fun i _ => hmem i)
  have hsnn : ∀ ω, 0 ≤ ∑ i ∈ s, f i ω := fun ω => Finset.sum_nonneg (fun i _ => hnn i ω)
  have hI : Integrable (fun ω => (∑ i ∈ s, f i ω) ^ p) μ := by
    have := hsum.integrable_norm_pow hp0
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hsnn ω)]
  refine ⟨hI, ?_⟩
  have hle : eLpNorm (fun ω => ∑ i ∈ s, f i ω) (p : ℝ≥0∞) μ ≤
      ∑ i ∈ s, eLpNorm (f i) (p : ℝ≥0∞) μ := by
    have h := eLpNorm_sum_le (f := f) (s := s) (μ := μ) (p := (p : ℝ≥0∞))
      (by exact_mod_cast hp)
    have e : (∑ i ∈ s, f i) = fun ω => ∑ i ∈ s, f i ω := by
      ext ω
      simp [Finset.sum_apply]
    rwa [e] at h
  have hY : ∀ i, 0 ≤ (∫ ω, f i ω ^ p ∂μ) ^ ((1 : ℝ) / p) := fun i =>
    Real.rpow_nonneg (integral_nonneg fun ω => pow_nonneg (hnn i ω) p) _
  have hX : 0 ≤ (∫ ω, (∑ i ∈ s, f i ω) ^ p ∂μ) ^ ((1 : ℝ) / p) :=
    Real.rpow_nonneg (integral_nonneg fun ω => pow_nonneg (hsnn ω) p) _
  rw [eLpNorm_eq_root hsnn hp0 hsum,
    Finset.sum_congr rfl (fun i _ => eLpNorm_eq_root (hnn i) hp0 (hmem i)),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hY i)] at hle
  have hle' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ => hY i)).1 hle
  calc ∫ ω, (∑ i ∈ s, f i ω) ^ p ∂μ
      = ((∫ ω, (∑ i ∈ s, f i ω) ^ p ∂μ) ^ ((1 : ℝ) / p)) ^ p := by
        rw [one_div, Real.rpow_inv_natCast_pow
          (integral_nonneg fun ω => pow_nonneg (hsnn ω) p) hp0]
    _ ≤ _ := pow_le_pow_left₀ hX hle' p

/-- **Item 2** (Minkowski for sums of squares).  -/
theorem minkowski_sq_sum {μ : Measure Ω} {ι : Type*} (s : Finset ι) (P : ι → Ω → ℝ) {p : ℕ}
    (hp : 1 ≤ p) (hP : ∀ i, AEStronglyMeasurable (P i) μ)
    (hint : ∀ i, Integrable (fun ω => P i ω ^ (2 * p)) μ) :
    Integrable (fun ω => (∑ i ∈ s, P i ω ^ 2) ^ p) μ ∧
      ∫ ω, (∑ i ∈ s, P i ω ^ 2) ^ p ∂μ ≤
        (∑ i ∈ s, (∫ ω, P i ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / p)) ^ p := by
  have h := minkowski_pow_sum s (fun i ω => P i ω ^ 2) hp (fun i => (hP i).pow 2)
    (fun i ω => sq_nonneg _) (fun i => by simpa only [← pow_mul] using hint i)
  simpa only [← pow_mul] using h

/-- `∫⁻` form of Minkowski for sums of squares. -/
theorem lintegral_minkowski_sq_sum {μ : Measure Ω} {ι : Type*} (s : Finset ι) (P : ι → Ω → ℝ)
    {p : ℕ} (hp : 1 ≤ p) (hP : ∀ i, AEStronglyMeasurable (P i) μ)
    (hint : ∀ i, Integrable (fun ω => P i ω ^ (2 * p)) μ) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ s, P i ω ^ 2) ^ p) ∂μ ≤
      ENNReal.ofReal ((∑ i ∈ s, (∫ ω, P i ω ^ (2 * p) ∂μ) ^ ((1 : ℝ) / p)) ^ p) := by
  obtain ⟨h1, h2⟩ := minkowski_sq_sum s P hp hP hint
  rw [← ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun ω => ?_)]
  · exact ENNReal.ofReal_le_ofReal h2
  · simp only [Pi.zero_apply]
    exact pow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) p

/-- Two-term Minkowski. -/
theorem minkowski_two {μ : Measure Ω} {f g : Ω → ℝ} {p : ℕ} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable (fun ω => f ω ^ p) μ) (hgi : Integrable (fun ω => g ω ^ p) μ) :
    Integrable (fun ω => (f ω + g ω) ^ p) μ ∧
      ∫ ω, (f ω + g ω) ^ p ∂μ ≤
        ((∫ ω, f ω ^ p ∂μ) ^ ((1 : ℝ) / p) + (∫ ω, g ω ^ p ∂μ) ^ ((1 : ℝ) / p)) ^ p := by
  have h := minkowski_pow_sum (Finset.univ : Finset Bool) (fun b ω => if b then f ω else g ω) hp
    (by intro b; cases b <;> simpa) (by intro b ω; cases b <;> simp [hf0, hg0])
    (by intro b; cases b <;> simpa)
  simpa [Fintype.sum_bool] using h

end Minkowski

/-- Elementary root lemmas. -/
lemma root_le {p : ℕ} (hp : p ≠ 0) {I t : ℝ} (hI : 0 ≤ I) (ht : 0 ≤ t) (h : I ≤ t ^ p) :
    I ^ ((1 : ℝ) / p) ≤ t := by
  calc I ^ ((1 : ℝ) / p) ≤ (t ^ p) ^ ((1 : ℝ) / p) :=
        Real.rpow_le_rpow hI h (by positivity)
    _ = t := by rw [one_div, Real.pow_rpow_inv_natCast ht hp]

lemma root_mul_pow {p : ℕ} (hp : p ≠ 0) {c I : ℝ} (hc : 0 ≤ c) (hI : 0 ≤ I) :
    (c ^ p * I) ^ ((1 : ℝ) / p) = c * I ^ ((1 : ℝ) / p) := by
  rw [Real.mul_rpow (pow_nonneg hc p) hI, one_div, Real.pow_rpow_inv_natCast hc hp]

/-! ### Multilinear polynomials -/

/-- The multilinear polynomial `z ↦ ∑_α a α ∏_{s ∈ α} z s`. -/
def mlin {S : Type} [Fintype S] [DecidableEq S] (a : Finset S → ℝ) (z : S → ℝ) : ℝ :=
  ∑ α : Finset S, a α * ∏ s ∈ α, z s

section Poly

variable {S : Type} [Fintype S] [DecidableEq S]

lemma measurable_mlin (a : Finset S → ℝ) : Measurable (mlin a) := by
  have h : mlin a = fun z => ∑ α : Finset S, a α * ∏ s ∈ α, z s := rfl
  rw [h]
  refine Finset.measurable_sum _ (fun α _ => ?_)
  exact (Finset.measurable_prod _ (fun s _ => measurable_pi_apply s)).const_mul _

lemma integrable_prod_pow (q : ℕ) (α : Finset S) :
    Integrable (fun z : S → ℝ => (∏ s ∈ α, z s) ^ q)
      (Measure.pi fun _ : S => gaussianReal 0 1) := by
  have h : ∀ z : S → ℝ, (∏ s ∈ α, z s) ^ q = ∏ s : S, (if s ∈ α then z s ^ q else 1) := by
    intro z
    rw [← Finset.prod_pow, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [h]
  exact Integrable.fintype_prod (f := fun s (x : ℝ) => if s ∈ α then x ^ q else 1)
    (fun s => by
      by_cases hs : s ∈ α
      · simpa only [hs, ite_true] using integrable_pow_gauss q
      · simpa only [hs, ite_false] using integrable_const (1 : ℝ))

lemma memLp_prod (q : ℕ) (hq : q ≠ 0) (α : Finset S) :
    MemLp (fun z : S → ℝ => ∏ s ∈ α, z s) ((2 * q : ℕ) : ℝ≥0∞)
      (Measure.pi fun _ : S => gaussianReal 0 1) :=
  memLp_of_integrable_pow
    (Finset.measurable_prod _ (fun s _ => measurable_pi_apply s)).aestronglyMeasurable hq
    (integrable_prod_pow (2 * q) α |>.congr (Filter.Eventually.of_forall fun z => by
      simp only [pow_mul]))

/-- Every power `(mlin a)^(2p)` is integrable against the product Gaussian measure. -/
theorem integrable_mlin_pow (p : ℕ) {S : Type} [Fintype S] [DecidableEq S] (a : Finset S → ℝ) :
    Integrable (fun z => (mlin a z) ^ (2 * p)) (Measure.pi fun _ : S => gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have hmem : MemLp (mlin a) ((2 * p : ℕ) : ℝ≥0∞) (Measure.pi fun _ : S => gaussianReal 0 1) := by
      have h : mlin a = fun z => ∑ α ∈ (Finset.univ : Finset (Finset S)), a α * ∏ s ∈ α, z s :=
        rfl
      rw [h]
      exact memLp_finsetSum _ (fun α _ => (memLp_prod p hp.ne' α).const_mul (a α))
    exact integrable_pow_of_memLp hp.ne' hmem

end Poly

/-! ### Splitting off the first variable -/

lemma sum_finset_fin_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (g : Finset (Fin (n + 1)) → M) :
    ∑ α : Finset (Fin (n + 1)), g α =
      ∑ β : Finset (Fin n), g (β.image Fin.succ) +
        ∑ β : Finset (Fin n), g (insert 0 (β.image Fin.succ)) := by
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ (Finset.univ : Finset (Fin n)).image Fin.succ := by simp
  have hinj : Set.InjOn (fun β : Finset (Fin n) => β.image Fin.succ)
      (↑(Finset.univ : Finset (Fin n)).powerset) :=
    Finset.image_injOn_powerset_of_injOn (Fin.succ_injective n).injOn
  calc ∑ α : Finset (Fin (n + 1)), g α
      = ∑ α ∈ (Finset.univ : Finset (Fin (n + 1))).powerset, g α := by
        rw [Finset.powerset_univ]
    _ = ∑ α ∈ (insert 0 ((Finset.univ : Finset (Fin n)).image Fin.succ)).powerset, g α := by
        rw [← hu]
    _ = ∑ α ∈ ((Finset.univ : Finset (Fin n)).image Fin.succ).powerset, g α +
          ∑ α ∈ ((Finset.univ : Finset (Fin n)).image Fin.succ).powerset, g (insert 0 α) :=
        Finset.sum_powerset_insert h0 g
    _ = _ := by
        rw [Finset.powerset_image, Finset.sum_image hinj, Finset.sum_image hinj,
          Finset.powerset_univ]

lemma mlin_cons {n : ℕ} (a : Finset (Fin (n + 1)) → ℝ) (aA aB : Finset (Fin n) → ℝ)
    (hA : ∀ β, aA β = a (β.image Fin.succ))
    (hB : ∀ β, aB β = a (insert 0 (β.image Fin.succ)))
    (x : ℝ) (y : Fin n → ℝ) :
    mlin a (Fin.cons x y : Fin (n + 1) → ℝ) = mlin aA y + mlin aB y * x := by
  unfold mlin
  rw [sum_finset_fin_succ n
    (fun α => a α * ∏ s ∈ α, (Fin.cons x y : Fin (n + 1) → ℝ) s), Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.prod_image (Fin.succ_injective n).injOn, hA]
    simp
  · refine Finset.sum_congr rfl fun β _ => ?_
    have h0 : (0 : Fin (n + 1)) ∉ β.image Fin.succ := by simp
    rw [Finset.prod_insert h0, Finset.prod_image (Fin.succ_injective n).injOn, hB]
    simp
    ring

lemma piFinSuccAbove_zero_symm' {n : ℕ} (x : ℝ) (y : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (x, y) =
      (Fin.cons x y : Fin (n + 1) → ℝ) := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_zero' x y

lemma mp_cons (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1))
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).symm

lemma integral_pi_succ_prod (n : ℕ) (H : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ x, H x ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      ∫ z, H (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ)
        ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  rw [← (mp_cons n).integral_comp' H]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact congrArg H (piFinSuccAbove_zero_symm' z.1 z.2)

lemma integrable_cons_prod (n : ℕ) {H : (Fin (n + 1) → ℝ) → ℝ}
    (hH : Integrable H (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => H (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  have h := ((mp_cons n).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (g := H)).2 hH
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  exact congrArg H (piFinSuccAbove_zero_symm' z.1 z.2)

/-! ### Bonami's inequality on `Fin n` -/

theorem bonami_fin (p : ℕ) (hp : 1 ≤ p) (c : ℝ) (hc : c = (2 * p : ℝ) - 1) :
    ∀ (n D : ℕ) (a : Finset (Fin n) → ℝ), (∀ α : Finset (Fin n), D < α.card → a α = 0) →
      ∫ z, (mlin a z) ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤
        c ^ (p * D) * (∑ α, a α ^ 2) ^ p := by
  have hp0 : p ≠ 0 := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hc1 : 1 ≤ c := by
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    rw [hc]; linarith
  have hc0 : 0 ≤ c := by linarith
  intro n
  induction n with
  | zero =>
    intro D a ha
    have hsub : ∀ α : Finset (Fin 0), α = ∅ := fun α =>
      Finset.eq_empty_of_forall_notMem (fun x _ => x.elim0)
    have hsum : ∀ g : Finset (Fin 0) → ℝ, ∑ α, g α = g ∅ := fun g =>
      Finset.sum_eq_single_of_mem ∅ (Finset.mem_univ _) (fun α _ hne => (hne (hsub α)).elim)
    have hm : ∀ z : Fin 0 → ℝ, mlin a z = a ∅ := by
      intro z
      unfold mlin
      rw [hsum]
      simp
    simp_rw [hm]
    rw [hsum (fun α => a α ^ 2)]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← pow_mul]
    exact le_mul_of_one_le_left ((even_two_mul p).pow_nonneg _)
      (one_le_pow₀ hc1)
  | succ n ih =>
    intro D a ha
    obtain ⟨aA, haA⟩ : ∃ aA : Finset (Fin n) → ℝ, ∀ β, aA β = a (β.image Fin.succ) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨aB, haB⟩ : ∃ aB : Finset (Fin n) → ℝ,
        ∀ β, aB β = a (insert 0 (β.image Fin.succ)) := ⟨_, fun _ => rfl⟩
    have hcons : ∀ (x : ℝ) (y : Fin n → ℝ),
        mlin a (Fin.cons x y : Fin (n + 1) → ℝ) = mlin aA y + mlin aB y * x :=
      fun x y => mlin_cons a aA aB haA haB x y
    have hAvan : ∀ β : Finset (Fin n), D < β.card → aA β = 0 := by
      intro β hβ
      rw [haA]
      apply ha
      rwa [Finset.card_image_of_injective _ (Fin.succ_injective n)]
    have hBvan : ∀ β : Finset (Fin n), D ≤ β.card → aB β = 0 := by
      intro β hβ
      rw [haB]
      apply ha
      have h0 : (0 : Fin (n + 1)) ∉ β.image Fin.succ := by simp
      rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injective _ (Fin.succ_injective n)]
      omega
    have hsq : ∑ α, a α ^ 2 = ∑ β, aA β ^ 2 + ∑ β, aB β ^ 2 := by
      have := sum_finset_fin_succ n (fun α : Finset (Fin (n + 1)) => a α ^ 2)
      simpa [haA, haB] using this
    have hSA : 0 ≤ ∑ β, aA β ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hSB : 0 ≤ ∑ β, aB β ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hIA : Integrable (fun y => mlin aA y ^ (2 * p))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := integrable_mlin_pow p aA
    have hIB : Integrable (fun y => mlin aB y ^ (2 * p))
        (Measure.pi fun _ : Fin n => gaussianReal 0 1) := integrable_mlin_pow p aB
    have hF : Integrable (fun z => mlin a z ^ (2 * p))
        (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := integrable_mlin_pow p a
    have hprod := integrable_cons_prod n hF
    have hnnA : 0 ≤ ∫ y, mlin aA y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      integral_nonneg fun y => (even_two_mul p).pow_nonneg _
    have hnnB : 0 ≤ ∫ y, mlin aB y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
      integral_nonneg fun y => (even_two_mul p).pow_nonneg _
    -- Fubini
    have step1 : ∫ z, mlin a z ^ (2 * p) ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
        ∫ y, ∫ x, mlin a (Fin.cons x y : Fin (n + 1) → ℝ) ^ (2 * p) ∂gaussianReal 0 1
          ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
      rw [integral_pi_succ_prod n (fun z => mlin a z ^ (2 * p))]
      exact integral_prod_symm
        (fun z : ℝ × (Fin n → ℝ) => mlin a (Fin.cons z.1 z.2 : Fin (n + 1) → ℝ) ^ (2 * p)) hprod
    have hlhs := hprod.integral_prod_right
    -- the pointwise Gaussian bound
    have hinner : ∀ y : Fin n → ℝ,
        ∫ x, mlin a (Fin.cons x y : Fin (n + 1) → ℝ) ^ (2 * p) ∂gaussianReal 0 1 ≤
          (mlin aA y ^ 2 + c * mlin aB y ^ 2) ^ p := by
      intro y
      have h := gauss_moment_ineq p hp (mlin aA y) (mlin aB y)
      rw [← hc] at h
      simp only [hcons]
      exact h
    -- Minkowski
    have eA : ∀ y : Fin n → ℝ, (mlin aA y ^ 2) ^ p = mlin aA y ^ (2 * p) :=
      fun y => (pow_mul _ 2 p).symm
    have eB : ∀ y : Fin n → ℝ, (c * mlin aB y ^ 2) ^ p = c ^ p * mlin aB y ^ (2 * p) :=
      fun y => by rw [mul_pow, ← pow_mul]
    have hMk := minkowski_two (μ := Measure.pi fun _ : Fin n => gaussianReal 0 1) hp
      (f := fun y => mlin aA y ^ 2) (g := fun y => c * mlin aB y ^ 2)
      ((measurable_mlin aA).pow_const 2).aestronglyMeasurable
      ((measurable_mlin aB).pow_const 2 |>.const_mul c).aestronglyMeasurable
      (fun y => sq_nonneg _) (fun y => mul_nonneg hc0 (sq_nonneg _))
      (by simpa only [eA] using hIA)
      (by simpa only [eB] using hIB.const_mul (c ^ p))
    simp only [eA, eB, integral_const_mul] at hMk
    obtain ⟨hI2, hM⟩ := hMk
    -- the induction hypotheses
    have ihA := ih D aA hAvan
    have hU : (∫ y, mlin aA y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ^
        ((1 : ℝ) / p) ≤ c ^ D * ∑ β, aA β ^ 2 := by
      refine root_le hp0 hnnA (mul_nonneg (pow_nonneg hc0 D) hSA) ?_
      calc _ ≤ c ^ (p * D) * (∑ β, aA β ^ 2) ^ p := ihA
        _ = (c ^ D * ∑ β, aA β ^ 2) ^ p := by rw [mul_pow, ← pow_mul, mul_comm D p]
    have hV : c * (∫ y, mlin aB y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ^
        ((1 : ℝ) / p) ≤ c ^ D * ∑ β, aB β ^ 2 := by
      rcases D with _ | D'
      · have hB0 : ∀ β, aB β = 0 := fun β => hBvan β (Nat.zero_le _)
        have hm0 : ∀ y, mlin aB y = 0 := fun y => by
          unfold mlin
          exact Finset.sum_eq_zero fun β _ => by rw [hB0, zero_mul]
        have hI0 : ∫ y, mlin aB y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = 0 := by
          simp [hm0, zero_pow (by omega : 2 * p ≠ 0)]
        have hS0 : ∑ β, aB β ^ 2 = 0 := by simp [hB0]
        rw [hI0, hS0, Real.zero_rpow (one_div_ne_zero hpR.ne')]
        simp
      · have ihB := ih D' aB (fun β hβ => hBvan β (by omega))
        have hroot : (∫ y, mlin aB y ^ (2 * p)
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ^ ((1 : ℝ) / p) ≤
            c ^ D' * ∑ β, aB β ^ 2 := by
          refine root_le hp0 hnnB (mul_nonneg (pow_nonneg hc0 D') hSB) ?_
          calc _ ≤ c ^ (p * D') * (∑ β, aB β ^ 2) ^ p := ihB
            _ = (c ^ D' * ∑ β, aB β ^ 2) ^ p := by rw [mul_pow, ← pow_mul, mul_comm D' p]
        calc _ ≤ c * (c ^ D' * ∑ β, aB β ^ 2) := mul_le_mul_of_nonneg_left hroot hc0
          _ = c ^ (D' + 1) * ∑ β, aB β ^ 2 := by ring
    rw [root_mul_pow hp0 hc0 hnnB] at hM
    have hU0 : 0 ≤ (∫ y, mlin aA y ^ (2 * p) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ^
        ((1 : ℝ) / p) := Real.rpow_nonneg hnnA _
    have hV0 : 0 ≤ c * (∫ y, mlin aB y ^ (2 * p)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)) ^ ((1 : ℝ) / p) :=
      mul_nonneg hc0 (Real.rpow_nonneg hnnB _)
    calc ∫ z, mlin a z ^ (2 * p) ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
        = ∫ y, ∫ x, mlin a (Fin.cons x y : Fin (n + 1) → ℝ) ^ (2 * p) ∂gaussianReal 0 1
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := step1
      _ ≤ ∫ y, (mlin aA y ^ 2 + c * mlin aB y ^ 2) ^ p
            ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
          integral_mono hlhs hI2 hinner
      _ ≤ _ := hM
      _ ≤ (c ^ D * (∑ β, aA β ^ 2 + ∑ β, aB β ^ 2)) ^ p :=
          pow_le_pow_left₀ (add_nonneg hU0 hV0) (by nlinarith [hU, hV]) p
      _ = c ^ (p * D) * (∑ α, a α ^ 2) ^ p := by
          rw [hsq, mul_pow, ← pow_mul, mul_comm D p]

/-! ### Transfer to an arbitrary finite index type -/

/-- **Item 3** (Bonami's inequality).  -/
theorem gaussian_bonami (D p : ℕ) (hp : 1 ≤ p) {S : Type} [Fintype S] [DecidableEq S]
    (a : Finset S → ℝ) (ha : ∀ α, D < α.card → a α = 0) :
    ∫ z, (mlin a z) ^ (2 * p) ∂(Measure.pi fun _ : S => gaussianReal 0 1) ≤
      ((2 * p : ℝ) - 1) ^ (p * D) * (∑ α, a α ^ 2) ^ p := by
  classical
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let e' : Finset (Fin (Fintype.card S)) ≃ Finset S := Equiv.finsetCongr e.symm
  let a' : Finset (Fin (Fintype.card S)) → ℝ := fun β => a (e' β)
  have ha' : ∀ β : Finset (Fin (Fintype.card S)), D < β.card → a' β = 0 := by
    intro β hβ
    apply ha
    simpa [e'] using hβ
  have hmp := measurePreserving_piCongrLeft (α := fun _ : Fin (Fintype.card S) => ℝ)
    (fun _ => gaussianReal 0 1) e
  have hw : ∀ (z : S → ℝ) (j : Fin (Fintype.card S)),
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) e z j = z (e.symm j) := by
    intro z j
    have h := MeasurableEquiv.piCongrLeft_apply_apply e (β := fun _ => ℝ) z (e.symm j)
    rwa [e.apply_symm_apply] at h
  have hm : ∀ z : S → ℝ, mlin a z = mlin a' (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e z) := by
    intro z
    unfold mlin
    rw [← Equiv.sum_comp e' (fun α => a α * ∏ s ∈ α, z s)]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [a', e', Equiv.finsetCongr_apply, Finset.prod_map, hw]
    rfl
  have key := bonami_fin p hp _ rfl (Fintype.card S) D a' ha'
  have hsum : ∑ β, a' β ^ 2 = ∑ α, a α ^ 2 := Equiv.sum_comp e' (fun α => a α ^ 2)
  rw [hsum] at key
  calc ∫ z, (mlin a z) ^ (2 * p) ∂(Measure.pi fun _ : S => gaussianReal 0 1)
      = ∫ z, (fun w => mlin a' w ^ (2 * p)) (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e z)
          ∂(Measure.pi fun _ : S => gaussianReal 0 1) := by
        simp_rw [hm]
    _ = ∫ w, mlin a' w ^ (2 * p) ∂(Measure.pi fun _ : Fin (Fintype.card S) => gaussianReal 0 1) :=
        hmp.integral_comp' (fun w => mlin a' w ^ (2 * p))
    _ ≤ _ := key

/-- `∫⁻` form of Bonami's inequality. -/
theorem lintegral_gaussian_bonami (D p : ℕ) (hp : 1 ≤ p) {S : Type} [Fintype S] [DecidableEq S]
    (a : Finset S → ℝ) (ha : ∀ α, D < α.card → a α = 0) :
    ∫⁻ z, ENNReal.ofReal ((mlin a z) ^ (2 * p)) ∂(Measure.pi fun _ : S => gaussianReal 0 1) ≤
      ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (p * D) * (∑ α, a α ^ 2) ^ p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_mlin_pow p a)
    (Filter.Eventually.of_forall fun z => ?_)]
  · exact ENNReal.ofReal_le_ofReal (gaussian_bonami D p hp a ha)
  · simp only [Pi.zero_apply]
    exact (even_two_mul p).pow_nonneg _

/-- `∫⁻` Minkowski for sums of squares of multilinear polynomials. -/
theorem lintegral_minkowski_mlin {S ι : Type} [Fintype S] [DecidableEq S] (s : Finset ι)
    (a : ι → Finset S → ℝ) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal ((∑ i ∈ s, mlin (a i) z ^ 2) ^ p)
        ∂(Measure.pi fun _ : S => gaussianReal 0 1) ≤
      ENNReal.ofReal ((∑ i ∈ s, (∫ z, mlin (a i) z ^ (2 * p)
        ∂(Measure.pi fun _ : S => gaussianReal 0 1)) ^ ((1 : ℝ) / p)) ^ p) :=
  lintegral_minkowski_sq_sum s (fun i => mlin (a i)) hp
    (fun i => (measurable_mlin (a i)).aestronglyMeasurable) (fun i => integrable_mlin_pow p (a i))

/-! ### Item 4: injective families -/

section Family

variable {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι]

lemma exists_coeff (D : ℕ) (supp : ι → Finset S) (hinj : Function.Injective supp)
    (hcard : ∀ k, (supp k).card ≤ D) (c : ι → ℝ) :
    ∃ a : Finset S → ℝ, (∀ z : S → ℝ, mlin a z = ∑ k, c k * ∏ s ∈ supp k, z s) ∧
      (∀ α : Finset S, D < α.card → a α = 0) ∧ ∑ α, a α ^ 2 = ∑ k, c k ^ 2 := by
  classical
  refine ⟨fun α => ∑ k, if supp k = α then c k else 0, ?_, ?_, ?_⟩
  · intro z
    unfold mlin
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ite_mul, Finset.sum_ite_eq]
  · intro α hα
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : supp k = α
    · exact absurd (h ▸ hcard k) (not_le.2 hα)
    · simp [h]
  · have hsq : ∀ α : Finset S, (∑ k, if supp k = α then c k else 0) ^ 2 =
        ∑ k, if supp k = α then c k ^ 2 else 0 := by
      intro α
      by_cases hex : ∃ k₀, supp k₀ = α
      · obtain ⟨k₀, hk₀⟩ := hex
        have hiff : ∀ k, supp k = α ↔ k = k₀ := fun k => by
          rw [← hk₀]
          exact hinj.eq_iff
        simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      · have hex' : ∀ k, supp k ≠ α := fun k hk => hex ⟨k, hk⟩
        simp [hex']
    simp only [hsq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq]

theorem integrable_family_pow (p : ℕ) (supp : ι → Finset S) (c : ι → ℝ) :
    Integrable (fun z : S → ℝ => (∑ k, c k * ∏ s ∈ supp k, z s) ^ (2 * p))
      (Measure.pi fun _ : S => gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · exact integrable_pow_of_memLp hp.ne'
      (memLp_finsetSum _ (fun k _ => (memLp_prod p hp.ne' (supp k)).const_mul (c k)))

/-- **Item 4.**  -/
theorem gaussian_bonami_family (D p : ℕ) (hp : 1 ≤ p) {S ι : Type} [Fintype S] [DecidableEq S]
    [Fintype ι] (supp : ι → Finset S) (hinj : Function.Injective supp)
    (hcard : ∀ k, (supp k).card ≤ D) (c : ι → ℝ) :
    ∫ z, (∑ k, c k * ∏ s ∈ supp k, z s) ^ (2 * p) ∂(Measure.pi fun _ : S => gaussianReal 0 1) ≤
      ((2 * p : ℝ) - 1) ^ (p * D) * (∑ k, c k ^ 2) ^ p := by
  obtain ⟨a, hm, hv, hs⟩ := exists_coeff D supp hinj hcard c
  have h := gaussian_bonami D p hp a hv
  simp only [hm] at h
  rwa [hs] at h

/-- `∫⁻` form of item 4. -/
theorem lintegral_gaussian_bonami_family (D p : ℕ) (hp : 1 ≤ p) {S ι : Type} [Fintype S]
    [DecidableEq S] [Fintype ι] (supp : ι → Finset S) (hinj : Function.Injective supp)
    (hcard : ∀ k, (supp k).card ≤ D) (c : ι → ℝ) :
    ∫⁻ z, ENNReal.ofReal ((∑ k, c k * ∏ s ∈ supp k, z s) ^ (2 * p))
        ∂(Measure.pi fun _ : S => gaussianReal 0 1) ≤
      ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (p * D) * (∑ k, c k ^ 2) ^ p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_family_pow p supp c)
    (Filter.Eventually.of_forall fun z => ?_)]
  · exact ENNReal.ofReal_le_ofReal (gaussian_bonami_family D p hp supp hinj hcard c)
  · simp only [Pi.zero_apply]
    exact (even_two_mul p).pow_nonneg _

end Family

/-! ### Item 5: curried form -/

section Curried

lemma mp_curry {ι κ : Type} [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ)
      (Measure.pi fun _ : ι × κ => gaussianReal 0 1)
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  refine ⟨(MeasurableEquiv.curry ι κ ℝ).measurable, ?_⟩
  have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : κ) => gaussianReal 0 1)
  simpa only [Measure.infinitePi_eq_pi] using h

lemma prod_curry {ι κ K : Type} (supp : K → Finset (ι × κ)) (z : ι × κ → ℝ) (k : K) :
    ∏ s ∈ supp k, (MeasurableEquiv.curry ι κ ℝ z) s.1 s.2 = ∏ s ∈ supp k, z s :=
  Finset.prod_congr rfl fun _ _ => rfl

theorem integrable_curried_pow (p : ℕ) {ι κ K : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype K] (supp : K → Finset (ι × κ)) (c : K → ℝ) :
    Integrable (fun y : ι → κ → ℝ => (∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p))
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) := by
  have h := integrable_family_pow p supp c
  refine ((mp_curry (ι := ι) (κ := κ)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)
    (g := fun y : ι → κ → ℝ => (∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p))).1 ?_
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, prod_curry]

/-- **Item 5.**  -/
theorem gaussian_bonami_curried (D p : ℕ) (hp : 1 ≤ p) {ι κ K : Type} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype K]
    (supp : K → Finset (ι × κ)) (hinj : Function.Injective supp)
    (hcard : ∀ k, (supp k).card ≤ D) (c : K → ℝ) :
    ∫ y, (∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p)
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) ≤
      ((2 * p : ℝ) - 1) ^ (p * D) * (∑ k, c k ^ 2) ^ p := by
  have h := gaussian_bonami_family D p hp supp hinj hcard c
  calc ∫ y, (∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p)
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1)
      = ∫ z, (∑ k, c k * ∏ s ∈ supp k, (MeasurableEquiv.curry ι κ ℝ z) s.1 s.2) ^ (2 * p)
          ∂(Measure.pi fun _ : ι × κ => gaussianReal 0 1) :=
        ((mp_curry (ι := ι) (κ := κ)).integral_comp'
          (fun y : ι → κ → ℝ => (∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p))).symm
    _ = ∫ z, (∑ k, c k * ∏ s ∈ supp k, z s) ^ (2 * p)
          ∂(Measure.pi fun _ : ι × κ => gaussianReal 0 1) := by
        simp only [prod_curry]
    _ ≤ _ := h

/-- `∫⁻` form of item 5. -/
theorem lintegral_gaussian_bonami_curried (D p : ℕ) (hp : 1 ≤ p) {ι κ K : Type} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype K]
    (supp : K → Finset (ι × κ)) (hinj : Function.Injective supp)
    (hcard : ∀ k, (supp k).card ≤ D) (c : K → ℝ) :
    ∫⁻ y, ENNReal.ofReal ((∑ k, c k * ∏ s ∈ supp k, y s.1 s.2) ^ (2 * p))
        ∂(Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) ≤
      ENNReal.ofReal (((2 * p : ℝ) - 1) ^ (p * D) * (∑ k, c k ^ 2) ^ p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_curried_pow p supp c)
    (Filter.Eventually.of_forall fun z => ?_)]
  · exact ENNReal.ofReal_le_ofReal (gaussian_bonami_curried D p hp supp hinj hcard c)
  · simp only [Pi.zero_apply]
    exact (even_two_mul p).pow_nonneg _

end Curried

end SharpLSI.FL.Bonami
