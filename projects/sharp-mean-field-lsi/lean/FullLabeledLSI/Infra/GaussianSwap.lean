import Mathlib

/-!
# Third-order swap lemma (Lindeberg step), pure Mathlib

If two probability measures on `ℝ^J` have the same means and the same second moments and finite
third moments, then a `C^3` function `Ψ` with `‖D³Ψ‖ ≤ K` has integrals under the two measures
differing by at most `K/6 (∫‖y‖³dν + ∫‖y‖³dν')` (second-order Taylor expansion at `0`).
`swap_affine` is the version for `y ↦ Φ (p + M y)`.
-/

open MeasureTheory

namespace SharpLSI.FL

private lemma pow_le_one_add_pow3 {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 3) :
    t ^ k ≤ 1 + t ^ 3 := by
  rcases le_total t 1 with h | h
  · have h1 : t ^ k ≤ 1 := pow_le_one₀ ht h
    have : 0 ≤ t ^ 3 := by positivity
    linarith
  · have : t ^ k ≤ t ^ 3 := pow_le_pow_right₀ h hk
    linarith

private lemma integrable_of_poly_bound {J : ℕ} (ν : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) {f : (Fin J → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f ν) (hC : ∀ y, ‖f y‖ ≤ 1 + ‖y‖ ^ 3) : Integrable f ν := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add h3) hf
    (Filter.Eventually.of_forall fun y => ?_)
  simpa using hC y

private lemma integrable_coord {J : ℕ} (ν : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (m : Fin J) :
    Integrable (fun y : Fin J → ℝ => y m) ν :=
  integrable_of_poly_bound ν h3 (continuous_apply m).aestronglyMeasurable fun y => by
    have h1 : ‖y m‖ ≤ ‖y‖ := norm_le_pi_norm y m
    have h2 := pow_le_one_add_pow3 (norm_nonneg y) (k := 1) (by norm_num)
    simp only [pow_one] at h2
    linarith

private lemma integrable_coord_mul {J : ℕ} (ν : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (m m' : Fin J) :
    Integrable (fun y : Fin J → ℝ => y m * y m') ν :=
  integrable_of_poly_bound ν h3
    ((continuous_apply m).mul (continuous_apply m')).aestronglyMeasurable fun y => by
    have h1 : ‖y m‖ ≤ ‖y‖ := norm_le_pi_norm y m
    have h1' : ‖y m'‖ ≤ ‖y‖ := norm_le_pi_norm y m'
    have h2 := pow_le_one_add_pow3 (norm_nonneg y) (k := 2) (by norm_num)
    rw [norm_mul]
    calc ‖y m‖ * ‖y m'‖ ≤ ‖y‖ * ‖y‖ := by gcongr
      _ = ‖y‖ ^ 2 := by ring
      _ ≤ _ := h2

/-- A polynomial of degree `≤ 2` in the coordinates. -/
private def polyQ {J : ℕ} (a : ℝ) (b : Fin J → ℝ) (c : Fin J → Fin J → ℝ) (y : Fin J → ℝ) : ℝ :=
  a + ∑ m, b m * y m + ∑ m, ∑ m', c m m' * (y m * y m')

private lemma polyQ_continuous {J : ℕ} (a : ℝ) (b : Fin J → ℝ) (c : Fin J → Fin J → ℝ) :
    Continuous (polyQ a b c) := by
  unfold polyQ
  fun_prop

private lemma polyQ_integrable {J : ℕ} (ν : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (a : ℝ) (b : Fin J → ℝ) (c : Fin J → Fin J → ℝ) :
    Integrable (polyQ a b c) ν := by
  unfold polyQ
  refine ((integrable_const a).add ?_).add ?_
  · exact integrable_finsetSum _ fun m _ => (integrable_coord ν h3 m).const_mul _
  · exact integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ =>
      (integrable_coord_mul ν h3 m m').const_mul _

private lemma polyQ_integral {J : ℕ} (ν : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν]
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (a : ℝ) (b : Fin J → ℝ) (c : Fin J → Fin J → ℝ) :
    ∫ y, polyQ a b c y ∂ν = a + ∑ m, b m * ∫ y, y m ∂ν +
      ∑ m, ∑ m', c m m' * ∫ y, y m * y m' ∂ν := by
  unfold polyQ
  have h1 : ∀ m, Integrable (fun y : Fin J → ℝ => b m * y m) ν :=
    fun m => (integrable_coord ν h3 m).const_mul _
  have h2 : ∀ m m', Integrable (fun y : Fin J → ℝ => c m m' * (y m * y m')) ν :=
    fun m m' => (integrable_coord_mul ν h3 m m').const_mul _
  have hs1 : Integrable (fun y : Fin J → ℝ => ∑ m, b m * y m) ν :=
    integrable_finsetSum _ fun m _ => h1 m
  have hs2 : Integrable (fun y : Fin J → ℝ => ∑ m, ∑ m', c m m' * (y m * y m')) ν :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ => h2 m m'
  have hs0 : Integrable (fun y : Fin J → ℝ => a + ∑ m, b m * y m) ν :=
    (integrable_const a).add hs1
  rw [integral_add hs0 hs2, integral_add (integrable_const a) hs1]
  simp only [integral_const, probReal_univ, one_smul]
  have e1 : ∫ y, ∑ m, b m * y m ∂ν = ∑ m, b m * ∫ y, y m ∂ν := by
    rw [integral_finsetSum _ fun m _ => h1 m]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  have e2 : ∫ y, ∑ m, ∑ m', c m m' * (y m * y m') ∂ν =
      ∑ m, ∑ m', c m m' * ∫ y, y m * y m' ∂ν := by
    rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun m' _ => h2 m m']
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_finsetSum _ fun m' _ => h2 m m']
    exact Finset.sum_congr rfl fun m' _ => integral_const_mul _ _
  rw [e1, e2]

private abbrev ebas {J : ℕ} (m : Fin J) : Fin J → ℝ := fun j => if m = j then 1 else 0

private lemma lin_expand {J : ℕ} (L : (Fin J → ℝ) →L[ℝ] ℝ) (y : Fin J → ℝ) :
    L y = ∑ m, L (ebas m) * y m := by
  have := LinearMap.pi_apply_eq_sum_univ (L : (Fin J → ℝ) →ₗ[ℝ] ℝ) y
  simpa [mul_comm] using this

private lemma bilin_expand {J : ℕ} (B : (Fin J → ℝ) →L[ℝ] (Fin J → ℝ) →L[ℝ] ℝ) (y : Fin J → ℝ) :
    B y y = ∑ m, ∑ m', B (ebas m) (ebas m') * (y m * y m') := by
  have h1 : B y = ∑ m, y m • B (ebas m) := by
    have := LinearMap.pi_apply_eq_sum_univ (B : (Fin J → ℝ) →ₗ[ℝ] ((Fin J → ℝ) →L[ℝ] ℝ)) y
    simpa using this
  rw [h1]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lin_expand (B (ebas m)) y, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m' _ => by ring

private lemma taylor_bound {J : ℕ} {Ψ : (Fin J → ℝ) → ℝ} (hΨ : ContDiff ℝ 3 Ψ) {K : ℝ}
    (hK : ∀ z, ‖iteratedFDeriv ℝ 3 Ψ z‖ ≤ K) (y : Fin J → ℝ) :
    |Ψ y - ∑ k ∈ Finset.range 3,
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k Ψ 0 (fun _ => y))| ≤ K / 6 * ‖y‖ ^ 3 := by
  have hT := map_add_eq_sum_add_integral_iteratedFDeriv (f := Ψ) (x := 0) (y := y) (n := 2)
    (fun t _ => hΨ.contDiffAt.of_le (by norm_num))
  rw [zero_add] at hT
  have hb : ∀ t : ℝ, ‖iteratedFDeriv ℝ (2 + 1) Ψ (0 + t • y) (fun _ => y)‖ ≤ K * ‖y‖ ^ 3 := by
    intro t
    calc ‖iteratedFDeriv ℝ (2 + 1) Ψ (0 + t • y) (fun _ => y)‖
        ≤ ‖iteratedFDeriv ℝ 3 Ψ (0 + t • y)‖ * ∏ _i : Fin 3, ‖y‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ K * ‖y‖ ^ 3 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hK _) (by positivity)
  have h13 : ∫ t in (0:ℝ)..1, (1 - t) ^ 2 = 1 / 3 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ 2) 1]
    norm_num [integral_pow]
  have hint : ‖∫ t in (0:ℝ)..1, (1 - t) ^ 2 • iteratedFDeriv ℝ (2 + 1) Ψ (0 + t • y) (fun _ => y)‖
      ≤ ∫ t in (0:ℝ)..1, (1 - t) ^ 2 * (K * ‖y‖ ^ 3) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      (Filter.Eventually.of_forall fun t _ => ?_)
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb t) (by positivity)
  rw [intervalIntegral.integral_mul_const, h13] at hint
  have hR : Ψ y - ∑ k ∈ Finset.range 3,
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k Ψ 0 (fun _ => y)) =
      ((2 : ℕ).factorial : ℝ)⁻¹ • ∫ t in (0:ℝ)..1, (1 - t) ^ 2 •
        iteratedFDeriv ℝ (2 + 1) Ψ (0 + t • y) (fun _ => y) := by
    rw [hT]; ring
  rw [hR, ← Real.norm_eq_abs, norm_smul]
  have h2 : ‖((2 : ℕ).factorial : ℝ)⁻¹‖ = 1 / 2 := by norm_num [Nat.factorial]
  rw [h2]
  linarith [hint]

/-- The degree-`≤ 2` Taylor polynomial at `0` is a polynomial `polyQ` in the coordinates. -/
private lemma taylor_poly_form {J : ℕ} (Ψ : (Fin J → ℝ) → ℝ) :
    ∃ (a : ℝ) (b : Fin J → ℝ) (c : Fin J → Fin J → ℝ), ∀ y : Fin J → ℝ,
      ∑ k ∈ Finset.range 3, ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k Ψ 0 (fun _ => y)) =
        polyQ a b c y := by
  refine ⟨Ψ 0, fun m => fderiv ℝ Ψ 0 (ebas m),
    fun m m' => (1 / 2) * fderiv ℝ (fderiv ℝ Ψ) 0 (ebas m) (ebas m'), fun y => ?_⟩
  have h2 : (1 / 2 : ℝ) * (fderiv ℝ (fderiv ℝ Ψ) 0 y y) =
      ∑ m, ∑ m', (1 / 2) * fderiv ℝ (fderiv ℝ Ψ) 0 (ebas m) (ebas m') * (y m * y m') := by
    rw [bilin_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m' _ => by ring
  unfold polyQ
  rw [← h2, ← lin_expand (fderiv ℝ Ψ 0) y]
  simp [Finset.sum_range_succ, iteratedFDeriv_two_apply, Nat.factorial]

/-- Third-order swap lemma. -/
theorem swap_lemma {J : ℕ} {Ψ : (Fin J → ℝ) → ℝ} (hΨ : ContDiff ℝ 3 Ψ) {K : ℝ}
    (hK : ∀ z, ‖iteratedFDeriv ℝ 3 Ψ z‖ ≤ K)
    (ν ν' : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (h3' : Integrable (fun y => ‖y‖ ^ 3) ν')
    (hmean : ∀ m, ∫ y, y m ∂ν = ∫ y, y m ∂ν')
    (hcov : ∀ m m', ∫ y, y m * y m' ∂ν = ∫ y, y m * y m' ∂ν') :
    |∫ y, Ψ y ∂ν - ∫ y, Ψ y ∂ν'| ≤ K / 6 * (∫ y, ‖y‖ ^ 3 ∂ν + ∫ y, ‖y‖ ^ 3 ∂ν') := by
  obtain ⟨a, b, c, hP⟩ := taylor_poly_form Ψ
  set R : (Fin J → ℝ) → ℝ := fun y => Ψ y - polyQ a b c y with hR
  have hRb : ∀ y, ‖R y‖ ≤ K / 6 * ‖y‖ ^ 3 := fun y => by
    have := taylor_bound hΨ hK y
    rw [hP y] at this
    simpa [hR, Real.norm_eq_abs] using this
  have hRc : Continuous R := hΨ.continuous.sub (polyQ_continuous a b c)
  have hΨR : Ψ = fun y => polyQ a b c y + R y := by
    funext y; simp [hR]
  have key : ∀ (μ : Measure (Fin J → ℝ)), Integrable (fun y => ‖y‖ ^ 3) μ →
      Integrable R μ ∧ ‖∫ y, R y ∂μ‖ ≤ K / 6 * ∫ y, ‖y‖ ^ 3 ∂μ := fun μ hμ => by
    refine ⟨Integrable.mono' (hμ.const_mul (K / 6)) hRc.aestronglyMeasurable
      (Filter.Eventually.of_forall hRb), ?_⟩
    have := norm_integral_le_of_norm_le (hμ.const_mul (K / 6)) (Filter.Eventually.of_forall hRb)
    rwa [integral_const_mul] at this
  obtain ⟨hRi, hRn⟩ := key ν h3
  obtain ⟨hRi', hRn'⟩ := key ν' h3'
  have hpoly : ∫ y, polyQ a b c y ∂ν = ∫ y, polyQ a b c y ∂ν' := by
    rw [polyQ_integral ν h3, polyQ_integral ν' h3']
    simp only [hmean, hcov]
  have hsplit : ∀ (μ : Measure (Fin J → ℝ)) [IsProbabilityMeasure μ], Integrable (fun y => ‖y‖ ^ 3) μ → Integrable R μ →
      ∫ y, Ψ y ∂μ = ∫ y, polyQ a b c y ∂μ + ∫ y, R y ∂μ := fun μ _ hμ hRμ => by
    rw [hΨR]
    exact integral_add (polyQ_integrable μ hμ a b c) hRμ
  have hdiff : ∫ y, Ψ y ∂ν - ∫ y, Ψ y ∂ν' = ∫ y, R y ∂ν - ∫ y, R y ∂ν' := by
    rw [hsplit ν h3 hRi, hsplit ν' h3' hRi', hpoly]; ring
  rw [hdiff]
  calc |∫ y, R y ∂ν - ∫ y, R y ∂ν'|
      ≤ |∫ y, R y ∂ν| + |∫ y, R y ∂ν'| := abs_sub _ _
    _ ≤ _ := by
      rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
      linarith

/-- The swap lemma for `y ↦ Φ (p + M y)`, `M` a continuous linear map into a normed space. -/
theorem swap_affine {J : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {Φ : H → ℝ} (hΦ : ContDiff ℝ 3 Φ) {K₃ : ℝ} (hK : ∀ z, ‖iteratedFDeriv ℝ 3 Φ z‖ ≤ K₃)
    (p : H) (M : (Fin J → ℝ) →L[ℝ] H)
    (ν ν' : Measure (Fin J → ℝ)) [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (h3 : Integrable (fun y => ‖y‖ ^ 3) ν) (h3' : Integrable (fun y => ‖y‖ ^ 3) ν')
    (hmean : ∀ m, ∫ y, y m ∂ν = ∫ y, y m ∂ν')
    (hcov : ∀ m m', ∫ y, y m * y m' ∂ν = ∫ y, y m * y m' ∂ν') :
    |∫ y, Φ (p + M y) ∂ν - ∫ y, Φ (p + M y) ∂ν'| ≤
      K₃ * ‖M‖ ^ 3 / 6 * (∫ y, ‖y‖ ^ 3 ∂ν + ∫ y, ‖y‖ ^ 3 ∂ν') := by
  have hΦ' : ContDiff ℝ 3 (fun w => Φ (p + w)) := hΦ.comp (contDiff_const.add contDiff_id)
  have hΨ : ContDiff ℝ 3 (fun y : Fin J → ℝ => Φ (p + M y)) := hΦ'.comp M.contDiff
  refine swap_lemma (K := K₃ * ‖M‖ ^ 3) hΨ (fun z => ?_) ν ν' h3 h3' hmean hcov
  have h1 : iteratedFDeriv ℝ 3 (fun y : Fin J → ℝ => Φ (p + M y)) z =
      (iteratedFDeriv ℝ 3 Φ (p + M z)).compContinuousLinearMap fun _ => M := by
    have := M.iteratedFDeriv_comp_right hΦ' z (i := 3) le_rfl
    rw [show (fun y : Fin J → ℝ => Φ (p + M y)) = (fun w => Φ (p + w)) ∘ M from rfl, this,
      iteratedFDeriv_comp_add_left]
  rw [h1]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hK _) (by positivity)

end SharpLSI.FL
