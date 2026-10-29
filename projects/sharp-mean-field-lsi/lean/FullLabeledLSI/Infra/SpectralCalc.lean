import FullLabeledLSI.Infra.SpectralTensor
import FullLabeledLSI.Infra.HypercontrTorus7

/-!
# Spectral calculus for the reference semigroup on `L²(μ^{⊗N})` (stage 1)

Manuscript Section 6.3, "Uniform approximation of the comparison expression".

* (D1) `Lam lam j = ∑ i, lam (j i)`, nonnegativity, finiteness of `{j | Lam lam j ≤ L}` under the
  eigenvalue growth hypothesis, and the finite set `Tset lam N L`.
* (D2) the coefficients `coeff mu e j Ψ = ∫ Ψ · E e j` and Bessel/Parseval:
  `∑' j, coeff j Ψ ^ 2 = ∫ Ψ ^ 2`.
* (D3) spectral multipliers `specMult` (built on `HilbertBasis.repr` and `lp`), the contraction
  property, the coefficient formula and the Parseval identity for `specMult m x - x`; the reference
  semigroup `St t` and a representative `Sfun t Ψ` of `St t Ψ`.
* (D4) the cutoff `Fcut t L Ψ`: the `L²`-distance to `Sfun t Ψ` is at most `exp (-(t L)) ‖Ψ‖₂`,
  `Fcut t L Ψ` is in the spectral range, `‖Fcut t L Ψ‖_{1 + e^{a t}} ≤ ‖Ψ‖₂` (Gross), and
  `‖Fcut t L Ψ‖₂ ≤ ‖Ψ‖₂`.
-/

open MeasureTheory SharpLSI

set_option linter.unusedSectionVars false

noncomputable section

namespace SharpLSI.FL.Spectral

/-! ### Bounded diagonal multipliers in an abstract Hilbert space with a Hilbert basis -/

section Abstract

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open scoped Classical in
/-- Multiplication of an `ℓ²` sequence by a sequence bounded by `1` (junk value `0` otherwise). -/
def mulLp (m : ι → ℝ) (f : lp (fun _ : ι => ℝ) 2) : lp (fun _ : ι => ℝ) 2 :=
  if hm : ∀ j, |m j| ≤ 1 then
    ⟨fun j => m j * f j, (lp.memℓp f).mono' fun j => by
      simpa [Real.norm_eq_abs, abs_mul] using mul_le_of_le_one_left (abs_nonneg (f j)) (hm j)⟩
  else 0

lemma mulLp_apply {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (f : lp (fun _ : ι => ℝ) 2) (j : ι) :
    mulLp m f j = m j * f j := by
  unfold mulLp
  rw [dite_eq_left hm]

variable (b : HilbertBasis ι ℝ H)

/-- The spectral multiplier `∑' j, (m j * ⟪b j, x⟫) • b j` of a Hilbert basis, defined by
conjugating coordinatewise multiplication on `ℓ²` with `b.repr` (junk value `0` unless
`|m j| ≤ 1` for all `j`). -/
def specMultHB (m : ι → ℝ) (x : H) : H := b.repr.symm (mulLp m (b.repr x))

lemma repr_specMultHB {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (x : H) (j : ι) :
    b.repr (specMultHB b m x) j = m j * b.repr x j := by
  rw [specMultHB, LinearIsometryEquiv.apply_symm_apply, mulLp_apply hm]

lemma repr_ext {x y : H} (h : ∀ j, b.repr x j = b.repr y j) : x = y := by
  apply b.repr.injective
  exact lp.ext (funext h)

/-- Parseval in `H`: `‖x‖² = ∑ j, ⟪b j, x⟫²`. -/
lemma norm_sq_hasSum (x : H) : HasSum (fun j => (b.repr x j) ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (E := fun _ : ι => ℝ) (p := 2) (by simp) (b.repr x)
  simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

lemma le_of_sq_le_sq_of_nonneg {a c : ℝ} (hc : 0 ≤ c) (h : a ^ 2 ≤ c ^ 2) : a ≤ c := by
  by_contra hlt
  have h' := not_le.1 hlt
  nlinarith

/-- A multiplier bounded by `1` is a contraction. -/
theorem norm_specMultHB_le {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (x : H) :
    ‖specMultHB b m x‖ ≤ ‖x‖ := by
  have h1 := norm_sq_hasSum b (specMultHB b m x)
  have h2 := norm_sq_hasSum b x
  refine le_of_sq_le_sq_of_nonneg (norm_nonneg _) (hasSum_le (fun k => ?_) h1 h2)
  rw [repr_specMultHB b hm, mul_pow, ← sq_abs (m k)]
  have := pow_le_pow_left₀ (abs_nonneg (m k)) (hm k) 2
  nlinarith [sq_nonneg (b.repr x k)]

/-- Parseval for `specMult m x - x`: `‖M x - x‖² = ∑ (m j - 1)² ⟪b j, x⟫²`. -/
theorem hasSum_norm_sq_specMultHB_sub {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (x : H) :
    HasSum (fun j => ((m j - 1) * b.repr x j) ^ 2) (‖specMultHB b m x - x‖ ^ 2) := by
  have h := norm_sq_hasSum b (specMultHB b m x - x)
  have e : ∀ j, b.repr (specMultHB b m x - x) j = (m j - 1) * b.repr x j := fun j => by
    rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_specMultHB b hm]
    ring
  simpa only [e] using h

open scoped Classical in
/-- Coefficients of a finite partial sum. -/
lemma repr_partial (T : Finset ι) (a : ι → ℝ) (k : ι) :
    b.repr (∑ j ∈ T, a j • b j) k = if k ∈ T then a k else 0 := by
  classical
  rw [HilbertBasis.repr_apply_apply, inner_sum]
  simp_rw [inner_smul_right]
  have h := orthonormal_iff_ite.1 b.orthonormal
  simp_rw [h]
  simp

/-- A finite partial sum of the multiplied series is dominated by `‖x‖`. -/
theorem norm_partial_le {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (T : Finset ι) (x : H) :
    ‖∑ j ∈ T, (m j * b.repr x j) • b j‖ ≤ ‖x‖ := by
  have h1 := norm_sq_hasSum b (∑ j ∈ T, (m j * b.repr x j) • b j)
  have h2 := norm_sq_hasSum b x
  refine le_of_sq_le_sq_of_nonneg (norm_nonneg _) (hasSum_le (fun k => ?_) h1 h2)
  rw [repr_partial]
  split_ifs with hk
  · rw [mul_pow, ← sq_abs (m k)]
    have := pow_le_pow_left₀ (abs_nonneg (m k)) (hm k) 2
    nlinarith [sq_nonneg (b.repr x k)]
  · nlinarith [sq_nonneg (b.repr x k)]

/-- The tail `M x - ∑_{j ∈ T} (m j ⟪b j, x⟫) b j` is controlled by `ρ ‖x‖` when `|m j| ≤ ρ` off
`T`. -/
theorem norm_specMultHB_sub_partial_le {m : ι → ℝ} (hm : ∀ j, |m j| ≤ 1) (T : Finset ι) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hT : ∀ j ∉ T, |m j| ≤ ρ) (x : H) :
    ‖specMultHB b m x - ∑ j ∈ T, (m j * b.repr x j) • b j‖ ≤ ρ * ‖x‖ := by
  classical
  have hry : ∀ k, b.repr (specMultHB b m x - ∑ j ∈ T, (m j * b.repr x j) • b j) k =
      if k ∈ T then 0 else m k * b.repr x k := by
    intro k
    rw [map_sub, lp.coeFn_sub, Pi.sub_apply, repr_specMultHB b hm, repr_partial]
    split_ifs <;> simp
  have h1 := norm_sq_hasSum b (specMultHB b m x - ∑ j ∈ T, (m j * b.repr x j) • b j)
  have h2 := (norm_sq_hasSum b x).mul_left (ρ ^ 2)
  have h3 : ‖specMultHB b m x - ∑ j ∈ T, (m j * b.repr x j) • b j‖ ^ 2 ≤ ρ ^ 2 * ‖x‖ ^ 2 := by
    refine hasSum_le (fun k => ?_) h1 h2
    rw [hry k]
    split_ifs with hk
    · nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (b.repr x k))]
    · rw [mul_pow, ← sq_abs (m k)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hT k hk) 2)
        (sq_nonneg _)
  exact le_of_sq_le_sq_of_nonneg (by positivity) (by rw [mul_pow]; exact h3)

end Abstract

/-! ### Generic `L²` facts -/

section LpFacts

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma inner_toLp_toLp {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp [mul_comm]

/-- `‖y‖² = ∫ y²` for an `L²` class. -/
lemma integral_sq_coe_eq (y : Lp ℝ 2 μ) : ∫ x, (y x) ^ 2 ∂μ = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [RCLike.inner_apply]
  simp [sq]

lemma norm_toLp_sq {f : α → ℝ} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← integral_sq_coe_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

lemma eLpNorm_coe_eq_ofReal_norm (y : Lp ℝ 2 μ) : eLpNorm (⇑y) 2 μ = ENNReal.ofReal ‖y‖ := by
  rw [← Lp.enorm_def, ofReal_norm]

end LpFacts

/-! ### (D1) Eigenvalue sums, finiteness and the cutoff set -/

section D1

/-- `Λ_j = ∑_i λ_{j i}` for `j : Fin N → ℕ`. -/
def Lam (lam : ℕ → ℝ) {N : ℕ} (j : Fin N → ℕ) : ℝ := ∑ i, lam (j i)

lemma Lam_nonneg {lam : ℕ → ℝ} (hlam : ∀ m, 0 ≤ lam m) {N : ℕ} (j : Fin N → ℕ) :
    0 ≤ Lam lam j :=
  Finset.sum_nonneg fun i _ => hlam (j i)

lemma lam_nonneg_of_ref {d : ℕ} {mu : Measure (Torus d)} {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) (m : ℕ) : 0 ≤ lam m := by
  have := hb.mono (Nat.zero_le m)
  rwa [hlam0] at this

/-- **(D1) Finiteness of the spectral cutoff sets** `{j | Λ_j ≤ L}`. -/
theorem Lam_finite {lam : ℕ → ℝ} (hlam : ∀ m, 0 ≤ lam m) {d : ℕ} (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    (N : ℕ) (L : ℝ) : {j : Fin N → ℕ | Lam lam j ≤ L}.Finite := by
  obtain ⟨c, hc, hgr⟩ := hgrow
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hcoord : ∀ m : ℕ, lam m ≤ L → m ≤ ⌈(L / c) ^ ((d : ℝ) / 2)⌉₊ := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · exact Nat.zero_le _
    · have h1 : c * (m : ℝ) ^ (2 / (d : ℝ)) ≤ L := (hgr m hmpos).trans hm
      have h2 : (m : ℝ) ^ (2 / (d : ℝ)) ≤ L / c := by
        rw [le_div_iff₀ hc]
        linarith [mul_comm c ((m : ℝ) ^ (2 / (d : ℝ)))]
      have h3 : (m : ℝ) ≤ (L / c) ^ ((d : ℝ) / 2) := by
        have h4 := Real.rpow_le_rpow (by positivity) h2 (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2)
        rwa [← Real.rpow_mul (by positivity), show 2 / (d : ℝ) * ((d : ℝ) / 2) = 1 by
          field_simp, Real.rpow_one] at h4
      exact_mod_cast h3.trans (Nat.le_ceil _)
  refine Set.Finite.subset (Set.Finite.pi
    (t := fun _ : Fin N => Set.Iic ⌈(L / c) ^ ((d : ℝ) / 2)⌉₊) fun _ => Set.finite_Iic _) ?_
  intro j hj i _
  apply hcoord
  exact (Finset.single_le_sum (f := fun k => lam (j k)) (fun k _ => hlam (j k))
    (Finset.mem_univ i)).trans hj

open scoped Classical in
/-- The finite set `{j | Λ_j ≤ L}` (it is `∅` if this set happens to be infinite; see
`Lam_finite`). -/
def Tset (lam : ℕ → ℝ) (N : ℕ) (L : ℝ) : Finset (Fin N → ℕ) :=
  if h : {j : Fin N → ℕ | Lam lam j ≤ L}.Finite then h.toFinset else ∅

theorem mem_Tset_iff {lam : ℕ → ℝ} {N : ℕ} {L : ℝ}
    (hfin : {j : Fin N → ℕ | Lam lam j ≤ L}.Finite) (j : Fin N → ℕ) :
    j ∈ Tset lam N L ↔ Lam lam j ≤ L := by
  unfold Tset
  rw [dite_eq_left hfin]
  simp

/-- **(D1)** Membership in `Tset` is `Λ_j ≤ L` (under the standing eigenvalue hypotheses). -/
theorem mem_Tset_iff_of_ref {d : ℕ} {mu : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    (N : ℕ) (L : ℝ) (j : Fin N → ℕ) : j ∈ Tset lam N L ↔ Lam lam j ≤ L :=
  mem_Tset_iff (Lam_finite (lam_nonneg_of_ref hb hlam0) hd hgrow N L) j

end D1

/-! ### (D2) Coefficients and Bessel/Parseval -/

section D2

/-- The coefficient `∫ Ψ · E e j` of `Ψ` against the tensor basis function `E e j`. -/
def coeff {α : Type} [MeasurableSpace α] (mu : Measure α) (e : ℕ → α → ℝ) {N : ℕ}
    (j : Fin N → ℕ) (Ψ : (Fin N → α) → ℝ) : ℝ :=
  ∫ ω, Ψ ω * E e j ω ∂(Q mu N)

/-- The finite partial sum `∑_{j ∈ T} (m j * coeff_j(Ψ)) E_j`. -/
def Fpart {α : Type} [MeasurableSpace α] (mu : Measure α) (e : ℕ → α → ℝ) {N : ℕ}
    (m : (Fin N → ℕ) → ℝ) (T : Finset (Fin N → ℕ)) (Ψ : (Fin N → α) → ℝ) (X : Fin N → α) : ℝ :=
  ∑ j ∈ T, m j * coeff mu e j Ψ * E e j X

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

lemma ref_memLp (hb : IsRefEigenbasis mu e lam) (j : ℕ) : MemLp (e j) 2 mu := (hb.memH1 j).2.1

/-- The tensor Hilbert basis of `L²(μ^{⊗N})` built from a reference eigenbasis. -/
def tHB (hb : IsRefEigenbasis mu e lam) (N : ℕ) :
    HilbertBasis (Fin N → ℕ) ℝ (Lp ℝ 2 (Q mu N)) :=
  tensorHB mu e (ref_memLp hb) hb.orthonormal hb.complete N

lemma tHB_ae (hb : IsRefEigenbasis mu e lam) (N : ℕ) (j : Fin N → ℕ) :
    (tHB hb N j : (Fin N → Torus d) → ℝ) =ᵐ[Q mu N] E e j :=
  tensorHB_apply mu e (ref_memLp hb) hb.orthonormal hb.complete N j

/-- The coefficient of `Ψ` is the `j`-th coordinate of any `L²` class representing `Ψ`. -/
lemma coeff_eq_repr_of_ae (hb : IsRefEigenbasis mu e lam) {Ψ : (Fin N → Torus d) → ℝ}
    (x : Lp ℝ 2 (Q mu N)) (hx : (⇑x) =ᵐ[Q mu N] Ψ) (j : Fin N → ℕ) :
    coeff mu e j Ψ = (tHB hb N).repr x j := by
  rw [HilbertBasis.repr_apply_apply, L2.inner_def]
  unfold coeff
  refine integral_congr_ae ?_
  filter_upwards [tHB_ae hb N j, hx] with ω h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp

lemma coeff_eq_repr (hb : IsRefEigenbasis mu e lam) {Ψ : (Fin N → Torus d) → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) (j : Fin N → ℕ) :
    coeff mu e j Ψ = (tHB hb N).repr (hΨ.toLp Ψ) j :=
  coeff_eq_repr_of_ae hb _ hΨ.coeFn_toLp j

/-- **(D2) Parseval/Bessel**: `∑_j coeff_j(Ψ)² = ∫ Ψ²` for `Ψ ∈ L²(μ^{⊗N})`. -/
theorem coeff_sq_hasSum (hb : IsRefEigenbasis mu e lam) {Ψ : (Fin N → Torus d) → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) :
    HasSum (fun j : Fin N → ℕ => coeff mu e j Ψ ^ 2) (∫ ω, Ψ ω ^ 2 ∂(Q mu N)) := by
  have h := norm_sq_hasSum (tHB hb N) (hΨ.toLp Ψ)
  rw [norm_toLp_sq hΨ] at h
  simpa only [coeff_eq_repr hb hΨ] using h

theorem coeff_sq_summable (hb : IsRefEigenbasis mu e lam) {Ψ : (Fin N → Torus d) → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) : Summable (fun j : Fin N → ℕ => coeff mu e j Ψ ^ 2) :=
  (coeff_sq_hasSum hb hΨ).summable

theorem coeff_sq_tsum (hb : IsRefEigenbasis mu e lam) {Ψ : (Fin N → Torus d) → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) :
    ∑' j : Fin N → ℕ, coeff mu e j Ψ ^ 2 = ∫ ω, Ψ ω ^ 2 ∂(Q mu N) :=
  (coeff_sq_hasSum hb hΨ).tsum_eq

end D2

/-! ### (D3) Spectral multipliers, the reference semigroup `St` and its representative `Sfun` -/

section D3

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **(D3) Spectral multiplier** `L²(μ^{⊗N}) → L²(μ^{⊗N})` with symbol `m : (Fin N → ℕ) → ℝ`
(`|m| ≤ 1`; junk value `0` otherwise): `x ↦ ∑' j, (m j * ⟪E_j, x⟫) • E_j`. -/
def specMult (hb : IsRefEigenbasis mu e lam) (N : ℕ) (m : (Fin N → ℕ) → ℝ)
    (x : Lp ℝ 2 (Q mu N)) : Lp ℝ 2 (Q mu N) :=
  specMultHB (tHB hb N) m x

/-- Coefficients of `specMult m x` are `m j` times those of `x`. -/
theorem repr_specMult (hb : IsRefEigenbasis mu e lam) {m : (Fin N → ℕ) → ℝ}
    (hm : ∀ j, |m j| ≤ 1) (x : Lp ℝ 2 (Q mu N)) (j : Fin N → ℕ) :
    (tHB hb N).repr (specMult hb N m x) j = m j * (tHB hb N).repr x j :=
  repr_specMultHB (tHB hb N) hm x j

/-- Contraction. -/
theorem norm_specMult_le (hb : IsRefEigenbasis mu e lam) {m : (Fin N → ℕ) → ℝ}
    (hm : ∀ j, |m j| ≤ 1) (x : Lp ℝ 2 (Q mu N)) : ‖specMult hb N m x‖ ≤ ‖x‖ :=
  norm_specMultHB_le (tHB hb N) hm x

/-- Parseval: `‖specMult m x - x‖² = ∑ (m j - 1)² c_j²`. -/
theorem hasSum_norm_sq_specMult_sub (hb : IsRefEigenbasis mu e lam) {m : (Fin N → ℕ) → ℝ}
    (hm : ∀ j, |m j| ≤ 1) (x : Lp ℝ 2 (Q mu N)) :
    HasSum (fun j => ((m j - 1) * (tHB hb N).repr x j) ^ 2)
      (‖specMult hb N m x - x‖ ^ 2) :=
  hasSum_norm_sq_specMultHB_sub (tHB hb N) hm x

/-- The reference semigroup `S_t = exp(-t Λ)` as a spectral multiplier. -/
def St (hb : IsRefEigenbasis mu e lam) (N : ℕ) (t : ℝ) (x : Lp ℝ 2 (Q mu N)) :
    Lp ℝ 2 (Q mu N) :=
  specMult hb N (fun j => Real.exp (-(t * Lam lam j))) x

lemma St_symbol_bound {lam : ℕ → ℝ} (hlam : ∀ m, 0 ≤ lam m) {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    (j : Fin N → ℕ) : |Real.exp (-(t * Lam lam j))| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.2 (mul_nonneg ht (Lam_nonneg hlam j))

theorem repr_St (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ} (ht : 0 ≤ t)
    (x : Lp ℝ 2 (Q mu N)) (j : Fin N → ℕ) :
    (tHB hb N).repr (St hb N t x) j = Real.exp (-(t * Lam lam j)) * (tHB hb N).repr x j :=
  repr_specMult hb (St_symbol_bound hlam ht) x j

theorem norm_St_le (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) (x : Lp ℝ 2 (Q mu N)) : ‖St hb N t x‖ ≤ ‖x‖ :=
  norm_specMult_le hb (St_symbol_bound hlam ht) x

theorem St_zero (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m)
    (x : Lp ℝ 2 (Q mu N)) : St hb N 0 x = x := by
  refine repr_ext (tHB hb N) fun j => ?_
  rw [repr_St hb hlam le_rfl]
  simp

theorem St_add (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (x : Lp ℝ 2 (Q mu N)) : St hb N (s + t) x = St hb N s (St hb N t x) := by
  refine repr_ext (tHB hb N) fun j => ?_
  rw [repr_St hb hlam (add_nonneg hs ht), repr_St hb hlam hs, repr_St hb hlam ht, ← mul_assoc,
    ← Real.exp_add]
  congr 3
  ring

open scoped Classical in
/-- **(D3)** A representative of `St t Ψ` for `Ψ ∈ L²(μ^{⊗N})` (and `0` otherwise). -/
def Sfun (hb : IsRefEigenbasis mu e lam) (t : ℝ) {N : ℕ} (Ψ : Config N d → ℝ) :
    Config N d → ℝ :=
  if hΨ : MemLp Ψ 2 (Q mu N) then ⇑(St hb N t (hΨ.toLp Ψ)) else 0

theorem Sfun_eq (hb : IsRefEigenbasis mu e lam) (t : ℝ) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) : Sfun hb t Ψ = ⇑(St hb N t (hΨ.toLp Ψ)) := by
  unfold Sfun
  exact dite_eq_left hΨ

theorem Sfun_memLp (hb : IsRefEigenbasis mu e lam) (t : ℝ) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) : MemLp (Sfun hb t Ψ) 2 (Q mu N) := by
  rw [Sfun_eq hb t hΨ]
  exact Lp.memLp _

/-- Coefficients of `Sfun t Ψ`: `coeff_j(S_t Ψ) = exp(-t Λ_j) coeff_j(Ψ)`. -/
theorem coeff_Sfun (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) (j : Fin N → ℕ) :
    coeff mu e j (Sfun hb t Ψ) = Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ := by
  rw [coeff_eq_repr_of_ae hb (St hb N t (hΨ.toLp Ψ)) (by rw [Sfun_eq hb t hΨ]) j,
    repr_St hb hlam ht, coeff_eq_repr hb hΨ]

/-- `S_t` is an `L²` contraction. -/
theorem eLpNorm_Sfun_le (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Sfun hb t Ψ) 2 (Q mu N) ≤ eLpNorm Ψ 2 (Q mu N) := by
  rw [Sfun_eq hb t hΨ, eLpNorm_coe_eq_ofReal_norm,
    ← eLpNorm_congr_ae hΨ.coeFn_toLp, eLpNorm_coe_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_St_le hb hlam ht _)

/-- Parseval for `S_t Ψ - Ψ`:
`∫ (S_t Ψ - Ψ)² = ∑ (exp(-t Λ_j) - 1)² coeff_j(Ψ)²`. -/
theorem hasSum_Sfun_sub_sq (hb : IsRefEigenbasis mu e lam) (hlam : ∀ m, 0 ≤ lam m) {t : ℝ}
    (ht : 0 ≤ t) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    HasSum (fun j : Fin N → ℕ => ((Real.exp (-(t * Lam lam j)) - 1) * coeff mu e j Ψ) ^ 2)
      (∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q mu N)) := by
  have h : HasSum (fun j => ((Real.exp (-(t * Lam lam j)) - 1) * (tHB hb N).repr (hΨ.toLp Ψ) j) ^ 2)
      (‖St hb N t (hΨ.toLp Ψ) - hΨ.toLp Ψ‖ ^ 2) :=
    hasSum_norm_sq_specMult_sub hb (m := fun j => Real.exp (-(t * Lam lam j)))
      (St_symbol_bound hlam ht (N := N)) (hΨ.toLp Ψ)
  have hint : ∫ X, (Sfun hb t Ψ X - Ψ X) ^ 2 ∂(Q mu N) =
      ‖St hb N t (hΨ.toLp Ψ) - hΨ.toLp Ψ‖ ^ 2 := by
    rw [← integral_sq_coe_eq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (St hb N t (hΨ.toLp Ψ)) (hΨ.toLp Ψ), hΨ.coeFn_toLp] with X h1 h2
    rw [h1, Pi.sub_apply, Sfun_eq hb t hΨ, h2]
  rw [hint]
  simpa only [← coeff_eq_repr hb hΨ] using h

end D3

/-! ### (D4) The spectral cutoff `Fcut` -/

section D4

variable {N d : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- **(D4)** The spectral cutoff of `S_t Ψ` at level `L`:
`∑_{j : Λ_j ≤ L} exp(-t Λ_j) coeff_j(Ψ) E_j`. -/
def Fcut {d : ℕ} (mu : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (t L : ℝ) {N : ℕ}
    (Ψ : Config N d → ℝ) (X : Config N d) : ℝ :=
  ∑ j ∈ Tset lam N L, Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ * E e j X

lemma Fcut_eq_Fpart (t L : ℝ) (Ψ : Config N d → ℝ) :
    Fcut mu e lam t L Ψ = Fpart mu e (fun j => Real.exp (-(t * Lam lam j))) (Tset lam N L) Ψ :=
  rfl

/-- The `L²` class of a partial sum is (a.e.) the function `Fpart`. -/
lemma partial_ae (hb : IsRefEigenbasis mu e lam) (m : (Fin N → ℕ) → ℝ)
    (T : Finset (Fin N → ℕ)) {Ψ : (Fin N → Torus d) → ℝ} (x : Lp ℝ 2 (Q mu N))
    (hx : (⇑x) =ᵐ[Q mu N] Ψ) :
    ⇑(∑ j ∈ T, (m j * (tHB hb N).repr x j) • tHB hb N j) =ᵐ[Q mu N] Fpart mu e m T Ψ := by
  have h1 := Lp.coeFn_fun_finsetSum T (fun j => (m j * (tHB hb N).repr x j) • tHB hb N j)
  have h2 : ∀ j ∈ T, ∀ᵐ X ∂(Q mu N),
      ((m j * (tHB hb N).repr x j) • tHB hb N j) X = m j * coeff mu e j Ψ * E e j X := by
    intro j _
    filter_upwards [Lp.coeFn_smul (m j * (tHB hb N).repr x j) (tHB hb N j), tHB_ae hb N j]
      with X h3 h4
    rw [h3, Pi.smul_apply, smul_eq_mul, h4, coeff_eq_repr_of_ae hb x hx j]
  have h5 : ∀ᵐ X ∂(Q mu N), ∀ j ∈ T,
      ((m j * (tHB hb N).repr x j) • tHB hb N j) X = m j * coeff mu e j Ψ * E e j X :=
    (Filter.eventually_all_finset T).2 h2
  filter_upwards [h1, h5] with X hX1 hX5
  rw [hX1]
  exact Finset.sum_congr rfl hX5

theorem memLp_Fpart (hb : IsRefEigenbasis mu e lam) (m : (Fin N → ℕ) → ℝ)
    (T : Finset (Fin N → ℕ)) (Ψ : (Fin N → Torus d) → ℝ) :
    MemLp (Fpart mu e m T Ψ) 2 (Q mu N) := by
  have h : MemLp (fun X => ∑ j ∈ T, (m j * coeff mu e j Ψ) * E e j X) 2 (Q mu N) :=
    memLp_finsetSum T fun j _ => (tensor_memLp mu e (ref_memLp hb) N j).const_mul _
  exact h

theorem memLp_Fcut (hb : IsRefEigenbasis mu e lam) (t L : ℝ) (Ψ : Config N d → ℝ) :
    MemLp (Fcut mu e lam t L Ψ) 2 (Q mu N) :=
  memLp_Fpart hb _ _ Ψ

/-- `‖∑_{j∈T} m_j c_j E_j‖₂ ≤ ‖Ψ‖₂` for `|m| ≤ 1`. -/
theorem eLpNorm_Fpart_le (hb : IsRefEigenbasis mu e lam) {m : (Fin N → ℕ) → ℝ}
    (hm : ∀ j, |m j| ≤ 1) (T : Finset (Fin N → ℕ)) {Ψ : (Fin N → Torus d) → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Fpart mu e m T Ψ) 2 (Q mu N) ≤ eLpNorm Ψ 2 (Q mu N) := by
  have hx : ⇑(hΨ.toLp Ψ) =ᵐ[Q mu N] Ψ := hΨ.coeFn_toLp
  rw [← eLpNorm_congr_ae (partial_ae hb m T _ hx), eLpNorm_coe_eq_ofReal_norm,
    ← eLpNorm_congr_ae hx, eLpNorm_coe_eq_ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (norm_partial_le (tHB hb N) hm T _)

/-- **(D4, P2)** `‖S_t Ψ - F_cut‖₂ ≤ e^{-tL} ‖Ψ‖₂`. -/
theorem eLpNorm_Sfun_sub_Fcut_le (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0)
    (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    {t : ℝ} (ht : 0 ≤ t) (L : ℝ) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (fun X => Sfun hb t Ψ X - Fcut mu e lam t L Ψ X) 2 (Q mu N) ≤
      ENNReal.ofReal (Real.exp (-(t * L))) * eLpNorm Ψ 2 (Q mu N) := by
  have hlam := lam_nonneg_of_ref hb hlam0
  have hm1 : ∀ j : Fin N → ℕ, |Real.exp (-(t * Lam lam j))| ≤ 1 := fun j =>
    St_symbol_bound hlam ht j
  obtain ⟨x, hxdef⟩ : ∃ x : Lp ℝ 2 (Q mu N), x = hΨ.toLp Ψ := ⟨_, rfl⟩
  have hx : ⇑x =ᵐ[Q mu N] Ψ := by rw [hxdef]; exact hΨ.coeFn_toLp
  have hz : Sfun hb t Ψ = ⇑(St hb N t x) := by rw [hxdef]; exact Sfun_eq hb t hΨ
  have hFw := partial_ae hb (fun j => Real.exp (-(t * Lam lam j))) (Tset lam N L) x hx
  have hdiff : (fun X => Sfun hb t Ψ X - Fcut mu e lam t L Ψ X) =ᵐ[Q mu N]
      ⇑(St hb N t x - ∑ j ∈ Tset lam N L,
        (Real.exp (-(t * Lam lam j)) * (tHB hb N).repr x j) • tHB hb N j) := by
    filter_upwards [Lp.coeFn_sub (St hb N t x) (∑ j ∈ Tset lam N L,
        (Real.exp (-(t * Lam lam j)) * (tHB hb N).repr x j) • tHB hb N j), hFw] with X h1 h2
    rw [h1, Pi.sub_apply, h2, hz]
    rfl
  rw [eLpNorm_congr_ae hdiff, eLpNorm_coe_eq_ofReal_norm, ← eLpNorm_congr_ae hx,
    eLpNorm_coe_eq_ofReal_norm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  refine norm_specMultHB_sub_partial_le (tHB hb N) hm1 (Tset lam N L) (Real.exp_pos _).le ?_ x
  intro j hj
  have hlt : L < Lam lam j := by
    by_contra hcon
    exact hj ((mem_Tset_iff_of_ref hb hlam0 hd hgrow N L j).2 (not_lt.1 hcon))
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  have := mul_le_mul_of_nonneg_left hlt.le ht
  linarith

/-- The Gross step: for every finite `T`, `‖∑_{j∈T} e^{-tΛ_j} c_j E_j‖_{1+e^{at}} ≤ ‖Ψ‖₂`. -/
theorem eLpNorm_Fpart_gross_le {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam : ∀ m, 0 ≤ lam m) (T : Finset (Fin N → ℕ)) {t : ℝ} (ht : 0 ≤ t)
    {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Fpart mu e (fun j => Real.exp (-(t * Lam lam j))) T Ψ)
        (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤ eLpNorm Ψ 2 (Q mu N) := by
  have hH := Gross.torus_grossHyp hac hca hb hC1 hae ha hrls T
  set c0 : T → ℝ := fun k => Real.exp (-((t / 2) * Lam lam k.1)) * coeff mu e k.1 Ψ with hc0
  have hG := Gross.gross_finite hH c0 (by linarith : (0 : ℝ) ≤ t / 2)
  have hq : Gross.qexp a (t / 2) = 1 + Real.exp (a * t) := by
    unfold Gross.qexp
    rw [show 2 * a * (t / 2) = a * t by ring]
  have key : ∀ S c : ℝ, Real.exp (-(t / 2 * S)) * (Real.exp (-(t / 2 * S)) * c) =
      Real.exp (-(t * S)) * c := fun S c => by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hflow : Gross.flow (Gross.nuT lam T) (t / 2) c0 =
      fun k : T => Real.exp (-(t * Lam lam k.1)) * coeff mu e k.1 Ψ := by
    funext k
    exact key (Lam lam k.1) (coeff mu e k.1 Ψ)
  have hFae : Fpart mu e (fun j => Real.exp (-(t * Lam lam j))) T Ψ =ᵐ[Q mu N]
      Gross.uFun (Gross.MT eC T) (Gross.flow (Gross.nuT lam T) (t / 2) c0) := by
    rw [hflow]
    filter_upwards [Gross.ae_poly_eq hae T
      (fun j => Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ)] with X hX
    exact hX
  have hu0 : Gross.uFun (Gross.MT eC T) c0 =ᵐ[Q mu N]
      Fpart mu e (fun j => Real.exp (-((t / 2) * Lam lam j))) T Ψ := by
    filter_upwards [Gross.ae_poly_eq hae T
      (fun j => Real.exp (-((t / 2) * Lam lam j)) * coeff mu e j Ψ)] with X hX
    exact hX.symm
  rw [eLpNorm_congr_ae hFae, ← hq]
  refine hG.trans ?_
  rw [eLpNorm_congr_ae hu0]
  exact eLpNorm_Fpart_le hb (fun j => St_symbol_bound hlam (by linarith) j) T hΨ

/-- **(D4, P4/S6a)** `F_cut` lies in the range of the spectral projection `Π_{N,L}`. -/
theorem InSpectralRange_Fcut (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0)
    (hd : 1 ≤ d)
    (hgrow : ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j)
    (t L : ℝ) (Ψ : Config N d → ℝ) : InSpectralRange e lam L (Fcut mu e lam t L Ψ) :=
  ⟨Tset lam N L, fun j => Real.exp (-(t * Lam lam j)) * coeff mu e j Ψ,
    fun j hj => (mem_Tset_iff_of_ref hb hlam0 hd hgrow N L j).1 hj, fun _ => rfl⟩

/-- **(D4, P4/S6b)** Hypercontractivity of the cutoff:
`‖F_cut‖_{1 + e^{at}} ≤ ‖Ψ‖₂`. -/
theorem eLpNorm_Fcut_gross_le {eC : ℕ → Torus d → ℝ} (hac : mu ≪ volume)
    (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, Gross.C1T (eC j))
    (hae : ∀ j, eC j =ᵐ[mu] e j) {a : ℝ} (ha : 0 < a) (hrls : ENNReal.ofReal a ≤ rLS mu)
    (hlam0 : lam 0 = 0) {t : ℝ} (ht : 0 ≤ t) (L : ℝ) {Ψ : Config N d → ℝ}
    (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Fcut mu e lam t L Ψ) (ENNReal.ofReal (1 + Real.exp (a * t))) (Q mu N) ≤
      eLpNorm Ψ 2 (Q mu N) :=
  eLpNorm_Fpart_gross_le hac hca hb hC1 hae ha hrls (lam_nonneg_of_ref hb hlam0)
    (Tset lam N L) ht hΨ

/-- **(D4, P4/S6c)** `‖F_cut‖₂ ≤ ‖Ψ‖₂`. -/
theorem eLpNorm_Fcut_two_le (hb : IsRefEigenbasis mu e lam) (hlam0 : lam 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (L : ℝ) {Ψ : Config N d → ℝ} (hΨ : MemLp Ψ 2 (Q mu N)) :
    eLpNorm (Fcut mu e lam t L Ψ) 2 (Q mu N) ≤ eLpNorm Ψ 2 (Q mu N) :=
  eLpNorm_Fpart_le hb (fun j => St_symbol_bound (lam_nonneg_of_ref hb hlam0) ht j)
    (Tset lam N L) hΨ

end D4

end SharpLSI.FL.Spectral

end
