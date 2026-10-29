import SharpSymmetricLSI.Paper.FourierSynth

/-!
# Trigonometric polynomials on `𝕋^ι` and Fourier multipliers (R23 lane, CZ part 1)

Trigonometric polynomials are elements of the group algebra `ℂ[ℤ^ι]`; `synth` is the algebra
homomorphism `c ↦ ∑ₖ cₖ eₖ` into functions on `𝕋^ι` (characters are multiplicative), so products
of trigonometric polynomials are computed in the group algebra. `mult m` is the Fourier multiplier
with symbol `m`. Parseval: `∫ |synth c|² = ∑ₖ |cₖ|²`.
-/

open MeasureTheory Complex
open scoped ENNReal ComplexConjugate
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Trigonometric polynomials: the group algebra `ℂ[ℤ^ι]`. -/
abbrev TP (ι : Type) := AddMonoidAlgebra ℂ (ι → ℤ)

/-- The characters `k ↦ e_k` as a monoid homomorphism. -/
noncomputable def charHom : Multiplicative (ι → ℤ) →* (UnitAddTorus ι → ℂ) where
  toFun k := fun x => mFourier (Multiplicative.toAdd k) x
  map_one' := by funext x; simp [mFourier_zero]
  map_mul' a b := by funext x; simp [mFourier_add]

/-- Synthesis `c ↦ ∑ₖ cₖ eₖ`, an algebra homomorphism. -/
noncomputable def synth : TP ι →ₐ[ℂ] (UnitAddTorus ι → ℂ) :=
  AddMonoidAlgebra.lift ℂ (UnitAddTorus ι → ℂ) (ι → ℤ) charHom

theorem synth_apply (c : TP ι) (x : UnitAddTorus ι) :
    synth c x = ∑ k ∈ c.coeff.support, c.coeff k * mFourier k x := by
  rw [synth, AddMonoidAlgebra.lift_apply, Finsupp.sum, Finset.sum_apply]
  rfl

theorem synth_apply_of_subset (c : TP ι) {S : Finset (ι → ℤ)} (hS : c.coeff.support ⊆ S)
    (x : UnitAddTorus ι) : synth c x = ∑ k ∈ S, c.coeff k * mFourier k x := by
  rw [synth_apply]
  refine Finset.sum_subset hS fun k _ hk => ?_
  rw [Finsupp.notMem_support_iff.mp hk, zero_mul]

theorem continuous_synth (c : TP ι) : Continuous (synth c) := by
  have : synth c = fun x => ∑ k ∈ c.coeff.support, c.coeff k * mFourier k x :=
    funext (synth_apply c)
  rw [this]
  fun_prop

theorem norm_synth_le (c : TP ι) (x : UnitAddTorus ι) :
    ‖synth c x‖ ≤ ∑ k ∈ c.coeff.support, ‖c.coeff k‖ := by
  rw [synth_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourier_le k x)

theorem memLp_synth (c : TP ι) (p : ℝ≥0∞) : MemLp (synth c) p volume :=
  MemLp.of_bound (continuous_synth c).aestronglyMeasurable _
    (Filter.Eventually.of_forall (norm_synth_le c))

/-! ### Fourier coefficients and Parseval -/

theorem integral_mFourier_mul (k l : ι → ℤ) :
    ∫ x : UnitAddTorus ι, mFourier l x * mFourier (-k) x = if l = k then 1 else 0 := by
  have : (fun x : UnitAddTorus ι => mFourier l x * mFourier (-k) x) = fun x => mFourier (l - k) x := by
    funext x; rw [sub_eq_add_neg, mFourier_add]
  rw [this, integral_mFourier]
  simp [sub_eq_zero]

theorem mFourierCoeff_synth (c : TP ι) (k : ι → ℤ) : mFourierCoeff (synth c) k = c.coeff k := by
  rw [mFourierCoeff_eq_integral]
  have : (fun t => mFourier (-k) t • synth c t) =
      fun t => ∑ l ∈ c.coeff.support, c.coeff l * (mFourier l t * mFourier (-k) t) := by
    funext t
    rw [synth_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [this, integral_finsetSum _ fun l _ => by
    exact ((by fun_prop : Continuous fun t => mFourier l t * mFourier (-k) t).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _]
  simp_rw [integral_const_mul, integral_mFourier_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h; exact h.symm

theorem integral_synth (c : TP ι) : ∫ x, synth c x = c.coeff 0 := by
  rw [← mFourierCoeff_synth, mFourierCoeff_eq_integral]
  simp [mFourier_zero]

/-- **Parseval** for trigonometric polynomials. -/
theorem integral_normSq_synth (c : TP ι) {S : Finset (ι → ℤ)} (hS : c.coeff.support ⊆ S) :
    ∫ x, ‖synth c x‖ ^ 2 = ∑ k ∈ S, ‖c.coeff k‖ ^ 2 := by
  have h1 : ∀ x, ((‖synth c x‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ S, ∑ l ∈ S, c.coeff k * conj (c.coeff l) * (mFourier k x * mFourier (-l) x) := by
    intro x
    push_cast
    rw [← Complex.mul_conj', synth_apply_of_subset c hS, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, mFourier_neg]
    ring
  have h2 : ((∫ x, ‖synth c x‖ ^ 2 : ℝ) : ℂ) = ∑ k ∈ S, ((‖c.coeff k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [h1]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      ((by fun_prop : Continuous fun t => mFourier k t * mFourier (-l) t).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ =>
      ((by fun_prop : Continuous fun t => mFourier k t * mFourier (-l) t).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _]
    simp_rw [integral_const_mul, integral_mFourier_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Complex.mul_conj']
    split_ifs with h
    push_cast; rfl
  exact_mod_cast h2

/-! ### Fourier multipliers -/

/-- The Fourier multiplier with symbol `m`. -/
noncomputable def mult (m : (ι → ℤ) → ℂ) : TP ι →ₗ[ℂ] TP ι where
  toFun c := AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite (fun k => m k * c.coeff k)
    (c.coeff.hasFiniteSupport.subset fun k hk => by
      simp only [Function.mem_support, ne_eq] at hk ⊢
      exact fun h => hk (by rw [h, mul_zero])))
  map_add' a b := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp [Finsupp.ofSupportFinite_coe, AddMonoidAlgebra.coeff_ofCoeff, mul_add]
  map_smul' a b := by
    apply AddMonoidAlgebra.coeff_injective
    ext k
    simp [Finsupp.ofSupportFinite_coe, AddMonoidAlgebra.coeff_ofCoeff]
    ring

@[simp]
theorem mult_coeff (m : (ι → ℤ) → ℂ) (c : TP ι) (k : ι → ℤ) :
    (mult m c).coeff k = m k * c.coeff k := by
  simp [mult, Finsupp.ofSupportFinite_coe, AddMonoidAlgebra.coeff_ofCoeff]

theorem mult_support (m : (ι → ℤ) → ℂ) (c : TP ι) :
    (mult m c).coeff.support ⊆ c.coeff.support := by
  intro k hk
  simp only [Finsupp.mem_support_iff, mult_coeff, ne_eq] at hk ⊢
  exact fun h => hk (by rw [h, mul_zero])

theorem mult_mult (m m' : (ι → ℤ) → ℂ) (c : TP ι) :
    mult m (mult m' c) = mult (fun k => m k * m' k) c := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp [mul_assoc]

theorem mult_eq_smul_of_support {m : (ι → ℤ) → ℂ} {c : TP ι} {z : ℂ}
    (h : ∀ k ∈ c.coeff.support, m k = z) : mult m c = z • c := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp only [mult_coeff, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hk : k ∈ c.coeff.support
  · rw [h k hk]
  · rw [Finsupp.notMem_support_iff.mp hk, mul_zero, mul_zero]

/-- Parseval bound for a multiplier with `|m| ≤ 1`. -/
theorem integral_normSq_synth_mult_le {m : (ι → ℤ) → ℂ} (hm : ∀ k, ‖m k‖ ≤ 1) (c : TP ι) :
    ∫ x, ‖synth (mult m c) x‖ ^ 2 ≤ ∫ x, ‖synth c x‖ ^ 2 := by
  rw [integral_normSq_synth _ (mult_support m c), integral_normSq_synth c subset_rfl]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [mult_coeff, norm_mul, mul_pow]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (hm k))

end SharpLSI
