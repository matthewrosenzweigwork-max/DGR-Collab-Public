import LeanResearch.PeriodicAttractiveLogGas.CanonicalWordBounds
import LeanResearch.PeriodicAttractiveLogGas.CanonicalWordEnumeration
import LeanResearch.PeriodicAttractiveLogGas.CanonicalExponentialMoment

/-! The canonical pair-sum theorem from the corrected manuscript, in its
coordinate product-law formulation. The random-partition argument is the one
attributed in the manuscript to Rudelson--Vershynin, proof of Theorem 1.1,
Step 2; its actual finite-product proof is in CanonicalDecoupling.
This module discharges the analytic and counting inputs from the source hypotheses. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators ENNReal Topology

namespace PeriodicAttractiveLogGas.CanonicalPairs
open CanonicalDecoupling CanonicalRowHolder CanonicalWordMoments
open CanonicalWordBounds CanonicalWordEnumeration CanonicalPairCounts

variable {m : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
  (ν : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
  (h : ∀ i j, α i → α j → ℝ)

/-- The actual upper-triangular extension used in the supplied proof. -/
def upperKernel (i j : Fin m) (x : α i) (y : α j) : ℝ :=
  if i < j then h i j x y else 0

omit [∀ i, MeasurableSpace (α i)] in
theorem upperKernel_triangular :
    ∀ i j, ¬ i < j → ∀ x y, upperKernel h i j x y = 0 := by
  intro i j hij x y
  simp [upperKernel, hij]

omit [∀ i, MeasurableSpace (α i)] in
theorem upperKernel_of_lt {i j : Fin m} (hij : i < j) : upperKernel h i j = h i j := by
  funext x y
  simp [upperKernel, hij]

omit [∀ i, MeasurableSpace (α i)] in
theorem upperKernel_of_not_lt {i j : Fin m} (hij : ¬ i < j) :
    upperKernel h i j = fun _ _ => 0 := by
  funext x y
  simp [upperKernel, hij]

theorem measurable_upperKernel
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j))) :
    ∀ i j, Measurable (Function.uncurry (upperKernel h i j)) := by
  intro i j
  by_cases hij : i < j
  · rw [upperKernel_of_lt h hij]
    exact hf i j hij
  · rw [upperKernel_of_not_lt h hij]
    exact measurable_const

omit [∀ i, IsProbabilityMeasure (ν i)] in
theorem upperKernel_left
    (hleft : ∀ i j, i < j → ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0) :
    ∀ i j, ∀ᵐ y ∂ν j, (∫ x, upperKernel h i j x y ∂ν i) = 0 := by
  intro i j
  by_cases hij : i < j
  · simpa [upperKernel, hij] using hleft i j hij
  · simp [upperKernel, hij]

omit [∀ i, IsProbabilityMeasure (ν i)] in
theorem upperKernel_right
    (hright : ∀ i j, i < j → ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0) :
    ∀ i j, ∀ᵐ x ∂ν i, (∫ y, upperKernel h i j x y ∂ν j) = 0 := by
  intro i j
  by_cases hij : i < j
  · simpa [upperKernel, hij] using hright i j hij
  · simp [upperKernel, hij]

/-- Positive moment orders make the omitted kernels' two extended moments zero. -/
theorem upperKernel_factorial {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (upperKernel h i j) p) (ν j) +
        essSup (rightMoment (ν j) (upperKernel h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ)) := by
  intro p hp i j
  by_cases hij : i < j
  · rw [upperKernel_of_lt h hij]
    exact hsource p hp i j hij
  · rw [upperKernel_of_not_lt h hij]
    change essSup (fun _y : α j => ∫⁻ _x : α i, ‖(0 : ℝ)‖ₑ ^ p ∂ν i) (ν j) +
      essSup (fun _x : α i => ∫⁻ _y : α j, ‖(0 : ℝ)‖ₑ ^ p ∂ν j) (ν i) ≤ _
    simp [show p ≠ 0 by omega]

theorem measurable_pairSum
    (hf : ∀ i j, Measurable (Function.uncurry (h i j))) : Measurable (pairSum h) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact (hf i j).comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

/-- The finite moment expansion restricted to precisely the surviving words. -/
theorem integral_decoupledSum_pow_eq_surviving {k : ℕ} (hk : 1 ≤ k)
    (hf : ∀ i j, Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ}
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    (∫ Z, decoupledSum h Z ^ (2 * k) ∂(Measure.pi ν).prod (Measure.pi ν)) =
      ∑ r ∈ singletonFreeWords m k, ∑ c ∈ singletonFreeWords m k,
        ∫ Z, wordProduct h r c Z ∂(Measure.pi ν).prod (Measure.pi ν) := by
  have hn : 1 ≤ 2 * k := by omega
  have hm := pairwise_memLp_of_essSup_sum ν h hn hf (hsource _ hn)
  rw [integral_decoupledSum_pow_eq_sum ν h hn hm]
  have hrow (r : Fin (2 * k) → Fin m) (hr : r ∉ singletonFreeWords m k)
      (c : Fin (2 * k) → Fin m) :
      (∫ Z, wordProduct h r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
    have hex : ∃ i, wordMultiplicity r i = 1 := by
      simpa only [mem_singletonFreeWords, not_forall, not_not] using hr
    obtain ⟨i, hi⟩ := hex
    exact integral_wordProduct_eq_zero_of_row_count_one ν h hn hf hm hleft r c i hi
  have hcol (r c : Fin (2 * k) → Fin m) (hc : c ∉ singletonFreeWords m k) :
      (∫ Z, wordProduct h r c Z ∂(Measure.pi ν).prod (Measure.pi ν)) = 0 := by
    have hex : ∃ i, wordMultiplicity c i = 1 := by
      simpa only [mem_singletonFreeWords, not_forall, not_not] using hc
    obtain ⟨i, hi⟩ := hex
    exact integral_wordProduct_eq_zero_of_column_count_one ν h hn hf hm hright r c i hi
  calc
    _ = ∑ r ∈ singletonFreeWords m k, ∑ c : Fin (2 * k) → Fin m,
        ∫ Z, wordProduct h r c Z ∂(Measure.pi ν).prod (Measure.pi ν) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro r _ hr
      exact Finset.sum_eq_zero (fun c _ => hrow r hr c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun c _ hc => hcol r c hc)

/-- The actual surviving-word sum is bounded using the proved factorial enumeration. -/
theorem integral_decoupledSum_pow_le_counts {k : ℕ} (hk : 1 ≤ k)
    (hf : ∀ i j, Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    (∫ Z, decoupledSum h Z ^ (2 * k) ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
      2 ^ k * L ^ (2 * k) * ((2 * k).factorial : ℝ) * (A m k : ℝ) * (B m k : ℝ) := by
  rw [integral_decoupledSum_pow_eq_surviving ν h hk hf hleft hright hsource]
  calc
    _ ≤ ∑ r ∈ singletonFreeWords m k, ∑ _c ∈ singletonFreeWords m k,
        2 ^ k * L ^ (2 * k) * ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro c _
      exact (le_abs_self _).trans (abs_integral_wordProduct_le ν h hk hf hL hsource r c hr)
    _ = ∑ r ∈ singletonFreeWords m k,
        ((B m k : ℝ) * (2 ^ k * L ^ (2 * k))) *
          ∏ i, ((wordMultiplicity r i).factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      simp only [Finset.sum_const, nsmul_eq_mul, B]
      ring
    _ = ((B m k : ℝ) * (2 ^ k * L ^ (2 * k))) *
        ∑ r ∈ singletonFreeWords m k, ∏ i, ((wordMultiplicity r i).factorial : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      rw [sum_factorials_singletonFreeWords_real]
      ring

/-- The exact numerical identity needed after the count bound. -/
theorem decoupled_constant_identity (m k : ℕ) (L : ℝ) :
    2 ^ k * L ^ (2 * k) * ((2 * k).factorial : ℝ) *
      ((4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k)) =
        (2 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
          ((2 * k).factorial : ℝ) := by
  have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [mul_pow, pow_mul, hs]
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
  ring

/-- Even powers agree with the real absolute powers used by decoupling. -/
theorem abs_rpow_even (x : ℝ) (k : ℕ) : |x| ^ ((2 * k : ℕ) : ℝ) = x ^ (2 * k) := by
  rw [Real.rpow_natCast, pow_mul, sq_abs, ← pow_mul]

/-- The source decoupled moment estimate, including actual integrability. -/
theorem decoupled_even_moment {k : ℕ} (hk : 1 ≤ k)
    (hf : ∀ i j, Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Integrable (fun Z => decoupledSum h Z ^ (2 * k)) ((Measure.pi ν).prod (Measure.pi ν)) ∧
      (∫ Z, decoupledSum h Z ^ (2 * k) ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
        (2 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
          ((2 * k).factorial : ℝ) := by
  have hn : 1 ≤ 2 * k := by omega
  have hm := pairwise_memLp_of_essSup_sum ν h hn hf (hsource _ hn)
  constructor
  · simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_rpow_even] using
      (memLp_decoupledSum ν h hm).integrable_norm_rpow'
  · refine (integral_decoupledSum_pow_le_counts ν h hk hf hleft hright hL hsource).trans ?_
    calc
      2 ^ k * L ^ (2 * k) * ((2 * k).factorial : ℝ) * (A m k : ℝ) * (B m k : ℝ) =
          (2 ^ k * L ^ (2 * k) * ((2 * k).factorial : ℝ)) * ((A m k : ℝ) * (B m k : ℝ)) := by ring
      _ ≤ (2 ^ k * L ^ (2 * k) * ((2 * k).factorial : ℝ)) *
          ((4 * Real.exp 1 ^ 2) ^ k * (m : ℝ) ^ (2 * k)) := by
        apply mul_le_mul_of_nonneg_left (count_product_le m k hk)
        exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hL _)) (Nat.cast_nonneg _)
      _ = _ := decoupled_constant_identity m k L

/-- The original pair-sum even moments, with the exact constant 8 sqrt(2) e. -/
theorem pair_even_moment {k : ℕ} (hk : 1 ≤ k)
    (htri : ∀ i j, ¬ i < j → ∀ x y, h i j x y = 0)
    (hf : ∀ i j, Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j,
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Integrable (fun X => pairSum h X ^ (2 * k)) (Measure.pi ν) ∧
      (∫ X, pairSum h X ^ (2 * k) ∂Measure.pi ν) ≤
        (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
          ((2 * k).factorial : ℝ) := by
  have hn : 1 ≤ 2 * k := by omega
  have hq : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by exact_mod_cast hn
  have hm := pairwise_memLp_of_essSup_sum ν h hn hf (hsource _ hn)
  have hmr : ∀ i j, MemLp (Function.uncurry (h i j))
      (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) ((ν i).prod (ν j)) := by
    simpa only [ENNReal.ofReal_natCast] using hm
  constructor
  · simpa only [ENNReal.toReal_natCast, Real.norm_eq_abs, abs_rpow_even] using
      (memLp_pairSum ν h htri hm).integrable_norm_rpow'
  · have hd := integral_abs_rpow_pairSum_le ν h htri hf hleft hright hq hmr
    simp only [abs_rpow_even] at hd
    simp only [Real.rpow_natCast] at hd
    refine hd.trans ?_
    calc
      (4 : ℝ) ^ (2 * k) * (∫ Z, decoupledSum h Z ^ (2 * k) ∂(Measure.pi ν).prod (Measure.pi ν)) ≤
          4 ^ (2 * k) * ((2 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
            ((2 * k).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (decoupled_even_moment ν h hk hf hleft hright hL hsource).2
          (by positivity)
      _ = _ := by
        rw [← mul_assoc, ← mul_pow]
        congr 2
        ring

/-- The source sum over the strictly upper-triangular pairs. -/
def canonicalSum (X : ∀ i, α i) : ℝ := pairSum (upperKernel h) X

omit [∀ i, MeasurableSpace (α i)] in
theorem canonicalSum_eq_upper_sum (X : ∀ i, α i) :
    canonicalSum h X = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), h i j (X i) (X j) := by
  simp only [canonicalSum, pairSum, upperKernel, Finset.sum_filter]

/-- The rational source upper bound tends to one at zero, without an assumption
of exponential integrability or a restriction on the sign of the parameter. -/
theorem tendsto_rational_bound (L : ℝ) :
    Filter.Tendsto (fun τ : ℝ =>
      (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
        (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2))
      (𝓝 0) (𝓝 1) := by
  have ht : ContinuousAt (fun τ : ℝ =>
      (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
        (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num
  simpa using ht.tendsto

/-- The complete canonical pair-sum theorem on the coordinate product law.
All hypotheses concern only the original kernels above the diagonal. Actual
integrability, centering, even moments and exponential integrability are conclusions. -/
theorem canonical_pairs (hm : 1 ≤ m)
    (hf : ∀ i j, i < j → Measurable (Function.uncurry (h i j)))
    (hleft : ∀ i j, i < j → ∀ᵐ y ∂ν j, (∫ x, h i j x y ∂ν i) = 0)
    (hright : ∀ i j, i < j → ∀ᵐ x ∂ν i, (∫ y, h i j x y ∂ν j) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hsource : ∀ p : ℕ, 1 ≤ p → ∀ i j, i < j →
      essSup (leftMoment (ν i) (h i j) p) (ν j) +
        essSup (rightMoment (ν j) (h i j) p) (ν i) ≤
          ENNReal.ofReal (2 * L ^ p * (p.factorial : ℝ))) :
    Measurable (canonicalSum h) ∧
      Integrable (canonicalSum h) (Measure.pi ν) ∧
      (∫ X, canonicalSum h X ∂Measure.pi ν) = 0 ∧
      (∀ k : ℕ, 1 ≤ k →
        Integrable (fun X => canonicalSum h X ^ (2 * k)) (Measure.pi ν) ∧
          (∫ X, canonicalSum h X ^ (2 * k) ∂Measure.pi ν) ≤
            (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
              ((2 * k).factorial : ℝ)) ∧
      (∀ τ : ℝ, |τ| * (8 * Real.sqrt 2 * Real.exp 1 * L) < 1 →
        Integrable (fun X => Real.exp (τ * canonicalSum h X / (m : ℝ))) (Measure.pi ν) ∧
          (∫ X, Real.exp (τ * canonicalSum h X / (m : ℝ)) ∂Measure.pi ν) ≤
            (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
              (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2)) ∧
      Filter.Tendsto (fun τ : ℝ =>
        (1 + (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2) /
          (1 - (|τ| * (8 * Real.sqrt 2 * Real.exp 1 * L)) ^ 2)) (𝓝 0) (𝓝 1) := by
  have hfm := measurable_upperKernel h hf
  have hl := upperKernel_left ν h hleft
  have hr := upperKernel_right ν h hright
  have hb := upperKernel_factorial ν h hsource
  have ht := upperKernel_triangular h
  have hmem := pairwise_memLp_of_essSup_sum ν (upperKernel h) (a := 1) le_rfl hfm (hb 1 le_rfl)
  have hint (i j : Fin m) :
      Integrable (Function.uncurry (upperKernel h i j)) ((ν i).prod (ν j)) := by
    have hm1 : MemLp (Function.uncurry (upperKernel h i j)) (1 : ℝ≥0∞) ((ν i).prod (ν j)) := by
      simpa only [Nat.cast_one] using hmem i j
    exact MemLp.integrable le_rfl hm1
  have hS : Measurable (canonicalSum h) := measurable_pairSum (upperKernel h) hfm
  have hI : Integrable (canonicalSum h) (Measure.pi ν) :=
    integrable_pairSum ν (upperKernel h) ht hint
  have hmean : (∫ X, canonicalSum h X ∂Measure.pi ν) = 0 :=
    integral_pairSum_eq_zero ν (upperKernel h) ht hint hr
  have hMom : ∀ k : ℕ, 1 ≤ k →
      Integrable (fun X => canonicalSum h X ^ (2 * k)) (Measure.pi ν) ∧
        (∫ X, canonicalSum h X ^ (2 * k) ∂Measure.pi ν) ≤
          (8 * Real.sqrt 2 * Real.exp 1 * L * (m : ℝ)) ^ (2 * k) *
            ((2 * k).factorial : ℝ) := by
    intro k hk
    exact pair_even_moment ν (upperKernel h) hk ht hfm hl hr hL hb
  refine ⟨hS, hI, hmean, hMom, ?_, tendsto_rational_bound L⟩
  intro τ hτ
  exact CanonicalExponentialMoment.integral_exp_normalized_le hS hI hmean hL hm hMom hτ

end PeriodicAttractiveLogGas.CanonicalPairs
