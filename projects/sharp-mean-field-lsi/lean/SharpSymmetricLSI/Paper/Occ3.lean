import SharpSymmetricLSI.Paper.Occ2
import SharpSymmetricLSI.Paper.ULimit2

/-!
# Hermite polynomials are orthogonal under the standard Gaussian (Phase 3, lane D; R28)

Stein's identity `E[Z p(Z)] = E[p'(Z)]` for polynomials (integration by parts against the Gaussian
density) gives `E[He_n(Z) q(Z)] = E[q^{(n)}(Z)]`, hence `E[He_m He_k] = k! δ_{mk}`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped ENNReal NNReal

namespace SharpLSI

/-- `E p(Z)` for a real polynomial `p`. -/
def gaussE (p : ℝ[X]) : ℝ := ∫ x, p.eval x ∂(gaussianReal 0 1)

theorem integrable_poly_gaussian (p : ℝ[X]) :
    Integrable (fun x => p.eval x) (gaussianReal 0 1) := by
  have : (fun x => p.eval x) = fun x => ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k := by
    funext x; rw [eval_eq_sum_range]
  rw [this]
  exact integrable_finsetSum _ fun k _ => (integrable_std_gaussian_pow k).const_mul _

theorem integrable_poly_pdf (p : ℝ[X]) :
    Integrable (fun x => gaussianPDFReal 0 1 x * p.eval x) := by
  have h := integrable_poly_gaussian p
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall fun _ => gaussianPDF_lt_top)] at h
  simpa [toReal_gaussianPDF] using h

theorem gaussE_add (p q : ℝ[X]) : gaussE (p + q) = gaussE p + gaussE q := by
  unfold gaussE
  simp only [eval_add]
  exact integral_add (integrable_poly_gaussian p) (integrable_poly_gaussian q)

theorem gaussE_sub (p q : ℝ[X]) : gaussE (p - q) = gaussE p - gaussE q := by
  unfold gaussE
  simp only [eval_sub]
  exact integral_sub (integrable_poly_gaussian p) (integrable_poly_gaussian q)

theorem gaussE_C (a : ℝ) : gaussE (C a) = a := by simp [gaussE]

theorem hasDerivAt_gaussianPDFReal (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
    funext x; rw [gaussianPDFReal]; norm_num; left; ring
  rw [h]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2 / 2)) (-x) x := by
    have := ((hasDerivAt_pow 2 x).div_const 2).neg
    convert this using 1; push_cast; ring
  convert (h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  ring

/-- **Stein's identity** for polynomials. -/
theorem gaussE_X_mul (p : ℝ[X]) : gaussE (X * p) = gaussE (derivative p) := by
  unfold gaussE
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul, eval_mul, eval_X]
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x => p.eval x) (u' := fun x => (derivative p).eval x)
    (v := gaussianPDFReal 0 1) (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => p.hasDerivAt x) (fun x _ => hasDerivAt_gaussianPDFReal x)
    ((integrable_poly_pdf (X * p)).neg.congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.neg_apply, eval_mul, eval_X]; ring))
    ((integrable_poly_pdf (derivative p)).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]; ring))
    ((integrable_poly_pdf p).congr (Eventually.of_forall fun x => by
      simp only [Pi.mul_apply]; ring))
  have e1 : ∫ x, gaussianPDFReal 0 1 x * (x * p.eval x) =
      -∫ x, p.eval x * (-x * gaussianPDFReal 0 1 x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, gaussianPDFReal 0 1 x * (derivative p).eval x =
      ∫ x, (derivative p).eval x * gaussianPDFReal 0 1 x := by
    congr 1; funext x; ring
  rw [e1, e2, hibp, neg_neg]

/-- `E[He_n(Z) q(Z)] = E[q^{(n)}(Z)]`. -/
theorem gaussE_hermite_mul (n : ℕ) (q : ℝ[X]) :
    gaussE ((hermite n).map (Int.castRingHom ℝ) * q) = gaussE (derivative^[n] q) := by
  induction n generalizing q with
  | zero => simp [hermite_zero]
  | succ n ih =>
    set H := (hermite n).map (Int.castRingHom ℝ)
    have hs : (hermite (n + 1)).map (Int.castRingHom ℝ) = X * H - derivative H := by
      rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, map_X, derivative_map]
    rw [hs, sub_mul, gaussE_sub, mul_assoc, gaussE_X_mul, derivative_mul, gaussE_add, ih,
      Function.iterate_succ_apply]
    ring

theorem iterate_derivative_hermite_self (k : ℕ) :
    derivative^[k] ((hermite k).map (Int.castRingHom ℝ)) = C (k.factorial : ℝ) := by
  set H := (hermite k).map (Int.castRingHom ℝ)
  have hdeg : H.natDegree = k := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_hermite]
  have h0 : (derivative^[k] H).natDegree = 0 := by
    have := natDegree_iterate_derivative H k
    omega
  rw [eq_C_of_natDegree_eq_zero h0, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
    coeff_map, coeff_hermite_self]
  simp

/-- **Orthogonality of the Hermite polynomials.** -/
theorem gaussE_hermite_hermite (m k : ℕ) :
    gaussE ((hermite m).map (Int.castRingHom ℝ) * (hermite k).map (Int.castRingHom ℝ)) =
      if m = k then (k.factorial : ℝ) else 0 := by
  have hdeg : ∀ j, ((hermite j).map (Int.castRingHom ℝ)).natDegree = j := fun j => by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_hermite]
  rcases lt_trichotomy m k with h | h | h
  · rw [mul_comm, gaussE_hermite_mul, iterate_derivative_eq_zero (by rw [hdeg]; exact h)]
    simp [gaussE]; intro h'; omega
  · subst h
    rw [gaussE_hermite_mul, iterate_derivative_hermite_self, gaussE_C]
    simp
  · rw [gaussE_hermite_mul, iterate_derivative_eq_zero (by rw [hdeg]; exact h)]
    simp [gaussE]; intro h'; omega


/-! ### The Hermite basis on `ℝ^ℕ` -/

/-- `He_k(x)/√(k!)`. -/
def hermiteN (k : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (hermite k) / Real.sqrt (k.factorial : ℝ)

theorem aeval_hermite_eq (k : ℕ) (x : ℝ) :
    Polynomial.aeval x (hermite k) = ((hermite k).map (Int.castRingHom ℝ)).eval x := by
  rw [aeval_def, eval₂_eq_eval_map]; rfl

theorem continuous_hermiteN (k : ℕ) : Continuous (hermiteN k) := by
  unfold hermiteN
  simp_rw [aeval_hermite_eq]
  exact (Polynomial.continuous _).div_const _

theorem hermiteN_zero (x : ℝ) : hermiteN 0 x = 1 := by simp [hermiteN, hermite_zero]

theorem integral_hermiteN_mul (a b : ℕ) :
    ∫ x, hermiteN a x * hermiteN b x ∂(gaussianReal 0 1) = if a = b then 1 else 0 := by
  have h := gaussE_hermite_hermite a b
  unfold gaussE at h
  simp only [eval_mul] at h
  have e : ∀ x, hermiteN a x * hermiteN b x =
      (Real.sqrt (a.factorial : ℝ) * Real.sqrt (b.factorial : ℝ))⁻¹ *
        (((hermite a).map (Int.castRingHom ℝ)).eval x * ((hermite b).map (Int.castRingHom ℝ)).eval x) :=
    fun x => by unfold hermiteN; rw [aeval_hermite_eq, aeval_hermite_eq]; field_simp
  simp_rw [e]
  rw [integral_const_mul, h]
  split_ifs with hab
  · subst hab
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul_self (Nat.cast_nonneg _)]
    have : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
    field_simp
  · simp

theorem hermiteBasis_eq_prod (α : ℕ →₀ ℕ) {S : Finset ℕ} (hS : α.support ⊆ S) (z : ℕ → ℝ) :
    hermiteBasis α z = ∏ n ∈ S, hermiteN (α n) (z n) := by
  unfold hermiteBasis
  refine Finset.prod_subset hS fun n _ hn => ?_
  have : α n = 0 := by simpa using hn
  rw [this]; exact hermiteN_zero _

/-- Integrals of products of functions of finitely many coordinates under `γ`. -/
theorem integral_gammaRef_prod (S : Finset ℕ) (g : ℕ → ℝ → ℝ) (hg : ∀ n, Continuous (g n)) :
    ∫ z, ∏ n ∈ S, g n (z n) ∂gammaRef = ∏ n ∈ S, ∫ x, g n x ∂(gaussianReal 0 1) := by
  have hmap : gammaRef.map S.restrict = Measure.pi fun _ : S => gaussianReal 0 1 := by
    unfold gammaRef; exact Measure.infinitePi_map_restrict _
  have hF : Continuous fun w : S → ℝ => ∏ i : S, g i (w i) :=
    continuous_finsetProd _ fun i _ => (hg i).comp (continuous_apply i)
  have e1 := integral_map (μ := gammaRef) (Finset.measurable_restrict S).aemeasurable
    hF.aestronglyMeasurable
  rw [hmap, integral_fintype_prod_eq_prod (f := fun (i : S) x => g i x)] at e1
  rw [← Finset.prod_coe_sort S (fun n => ∫ x, g n x ∂(gaussianReal 0 1)), e1]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Finset.restrict]
  exact (Finset.prod_coe_sort S (fun n => g n (z n))).symm

/-- **The Hermite basis is orthonormal in `L²(γ)`.** -/
theorem integral_hermiteBasis_mul (α β : ℕ →₀ ℕ) :
    ∫ z, hermiteBasis α z * hermiteBasis β z ∂gammaRef = if α = β then 1 else 0 := by
  set S := α.support ∪ β.support
  have e : ∀ z, hermiteBasis α z * hermiteBasis β z =
      ∏ n ∈ S, (hermiteN (α n) (z n) * hermiteN (β n) (z n)) := fun z => by
    rw [hermiteBasis_eq_prod α Finset.subset_union_left, hermiteBasis_eq_prod β
      Finset.subset_union_right, ← Finset.prod_mul_distrib]
  simp_rw [e]
  rw [integral_gammaRef_prod S (fun n x => hermiteN (α n) x * hermiteN (β n) x)
    fun n => (continuous_hermiteN _).mul (continuous_hermiteN _)]
  simp_rw [integral_hermiteN_mul]
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    ext n
    by_cases hn : n ∈ S
    · exact h n hn
    · simp only [S, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hn
      rw [hn.1, hn.2]
  · intro h n _; rw [h]

end SharpLSI
