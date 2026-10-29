import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! The Hilbert-space step in source Lemma 3.7, lines 663–670.

This proof uses iterated Cauchy–Schwarz and scalar powers instead of the
manuscript's spectral projections. Point-dependent exponential constants on
a dense linear subspace produce an actual global operator norm bound, hence
the required quadratic-form bound. No spectral gap is assumed.

All declarations are public. Development evidence and the distinct
protected-acceptance status are recorded outside this source.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace PeriodicAttractiveLogGas.DobrushinSpectralGap

/-- The dyadic exponents are at least their indices. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ n := pow_pos (by norm_num) n
      omega

/-- An exponential bound along the dyadic powers forces the exact base
bound. The coefficient is a single finite real number, not a uniform
coefficient over vectors. The zero-rate case uses the first power. -/
theorem le_of_dyadic_power_bound {a ρ C : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, a ^ (2 ^ n) ≤ C * ρ ^ (2 ^ n)) : a ≤ ρ := by
  by_cases hzero : ρ = 0
  · have hfirst := h 0
    simpa only [pow_zero, pow_one, hzero, mul_zero] using hfirst
  · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hzero)
    by_contra hnot
    have hlt : ρ < a := lt_of_not_ge hnot
    have hratio : 1 < a / ρ := (one_lt_div hpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hratio
    have hdyadic : (a / ρ) ^ (2 ^ n) ≤ C := by
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos hpos _)).mpr (h n)
    have hmono : (a / ρ) ^ n ≤ (a / ρ) ^ (2 ^ n) :=
      pow_le_pow_right₀ hratio.le (nat_le_two_pow n)
    exact (not_lt_of_ge (hmono.trans hdyadic)) hn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual bounds on all iterates of each vector in the given linear
subspace. The finite constant may depend arbitrarily on that vector. -/
def ExponentialBoundOn (K : H →L[ℝ] H) (D : Submodule ℝ H) (ρ : ℝ) : Prop :=
  ∀ f : H, f ∈ D → ∃ C : ℝ, ∀ n : ℕ, ‖(K ^ n) f‖ ≤ C * ρ ^ n

/-- A constant in an all-natural-powers bound is automatically
nonnegative, because the zeroth power is the identity. -/
theorem exponential_coefficient_nonneg {K : H →L[ℝ] H} {f : H} {ρ C : ℝ}
    (h : ∀ n : ℕ, ‖(K ^ n) f‖ ≤ C * ρ ^ n) : 0 ≤ C := by
  have hfirst := h 0
  simp only [pow_zero, one_apply_eq_self, mul_one] at hfirst
  exact (norm_nonneg f).trans hfirst

/-- The actual quadratic-form bound follows directly from an operator
norm bound and Cauchy–Schwarz. Completeness is not needed for this step. -/
theorem quadratic_bound_of_opNorm_le {K : H →L[ℝ] H} {ρ : ℝ} (hK : ‖K‖ ≤ ρ)
    (f : H) : (1 - ρ) * ‖f‖ ^ 2 ≤ ⟪f, (1 - K) f⟫_ℝ := by
  have hn : ‖K f‖ ≤ ρ * ‖f‖ :=
    (K.le_opNorm f).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg f))
  have hi : ⟪f, K f⟫_ℝ ≤ ‖f‖ * (ρ * ‖f‖) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg f))
  change (1 - ρ) * ‖f‖ ^ 2 ≤ ⟪f, f - K f⟫_ℝ
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith

variable [CompleteSpace H]

/-- Self-adjointness moves the first copy of a power through the inner
product; ordinary Cauchy–Schwarz then controls the doubled power. -/
theorem norm_pow_sq_le_norm_double {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    (n : ℕ) (f : H) :
    ‖(K ^ n) f‖ ^ 2 ≤ ‖(K ^ (n + n)) f‖ * ‖f‖ := by
  have hs := (hK.pow n).isSymmetric
  calc
    ‖(K ^ n) f‖ ^ 2 = ⟪(K ^ n) f, (K ^ n) f⟫_ℝ :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ⟪(K ^ n) ((K ^ n) f), f⟫_ℝ := (hs ((K ^ n) f) f).symm
    _ = ⟪(K ^ (n + n)) f, f⟫_ℝ := by rw [pow_add, mul_apply_eq_comp]
    _ ≤ ‖(K ^ (n + n)) f‖ * ‖f‖ := real_inner_le_norm _ _

/-- On a unit vector, repeated Cauchy–Schwarz compares the first-power
norm with arbitrarily high dyadic powers. -/
theorem first_norm_pow_le_dyadic_norm {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {f : H} (hf : ‖f‖ = 1) (n : ℕ) :
    ‖K f‖ ^ (2 ^ n) ≤ ‖(K ^ (2 ^ n)) f‖ := by
  induction n with
  | zero => simp only [pow_zero, pow_one, le_refl]
  | succ n ih =>
      have hdouble := norm_pow_sq_le_norm_double hK (2 ^ n) f
      rw [hf, mul_one] at hdouble
      have hindex : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by
        rw [pow_succ]
        omega
      calc
        ‖K f‖ ^ (2 ^ (n + 1)) = (‖K f‖ ^ (2 ^ n)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ ‖(K ^ (2 ^ n)) f‖ ^ 2 :=
          (sq_le_sq₀ (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)).mpr ih
        _ ≤ ‖(K ^ (2 ^ n + 2 ^ n)) f‖ := hdouble
        _ = ‖(K ^ (2 ^ (n + 1))) f‖ := by rw [hindex]

/-- The exact contraction factor on a unit vector follows from its own
exponential bound. No bound uniform in the unit vector is used. -/
theorem norm_apply_le_of_unit_exponential {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {f : H} (hf : ‖f‖ = 1) {ρ C : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ n : ℕ, ‖(K ^ n) f‖ ≤ C * ρ ^ n) : ‖K f‖ ≤ ρ := by
  apply le_of_dyadic_power_bound hρ
  intro n
  exact (first_norm_pow_le_dyadic_norm hK hf n).trans (h (2 ^ n))

/-- The dense set is a genuine linear subspace, so normalizing a nonzero
vector leaves it in the set on which the exponential bounds are known. -/
theorem norm_apply_le_on_submodule {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {D : Submodule ℝ H} {ρ : ℝ} (hρ : 0 ≤ ρ) (hdecay : ExponentialBoundOn K D ρ)
    {f : H} (hf : f ∈ D) : ‖K f‖ ≤ ρ * ‖f‖ := by
  by_cases hz : f = 0
  · subst f
    simp only [map_zero, norm_zero, mul_zero, le_refl]
  have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hz
  let v : H := ‖f‖⁻¹ • f
  have hvD : v ∈ D := D.smul_mem _ hf
  have hvnorm : ‖v‖ = 1 := by
    change ‖‖f‖⁻¹ • f‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      inv_mul_cancel₀ hnorm.ne']
  obtain ⟨C, hC⟩ := hdecay v hvD
  have hbound := norm_apply_le_of_unit_exponential hK hvnorm hρ hC
  have hnormKv : ‖K v‖ = ‖K f‖ / ‖f‖ := by
    change ‖K (‖f‖⁻¹ • f)‖ = ‖K f‖ / ‖f‖
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact (div_eq_inv_mul _ _).symm
  rw [hnormKv] at hbound
  exact (div_le_iff₀ hnorm).mp hbound

/-- Continuity extends the exact bound from the dense linear subspace.
The closed property is the displayed norm inequality itself. -/
theorem norm_apply_le_of_dense_exponential {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {D : Submodule ℝ H} (hDense : Dense (D : Set H)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hdecay : ExponentialBoundOn K D ρ) (f : H) :
    ‖K f‖ ≤ ρ * ‖f‖ := by
  exact hDense.induction (P := fun v ↦ ‖K v‖ ≤ ρ * ‖v‖)
    (fun v hv ↦ norm_apply_le_on_submodule hK hρ hdecay hv)
    (isClosed_le K.continuous.norm (continuous_const.mul continuous_norm)) f

/-- A point-dependent exponential estimate on a dense linear subspace
forces the actual operator norm bound. Positivity and an a priori
contraction bound are unnecessary for this stronger intermediate result. -/
theorem opNorm_le_of_dense_exponential {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {D : Submodule ℝ H} (hDense : Dense (D : Set H)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hdecay : ExponentialBoundOn K D ρ) : ‖K‖ ≤ ρ :=
  K.opNorm_le_bound hρ (norm_apply_le_of_dense_exponential hK hDense hρ hdecay)

/-- This is the Hilbert-space step without the redundant positivity and
initial-contraction assumptions. -/
theorem quadratic_bound_of_dense_exponential {K : H →L[ℝ] H} (hK : IsSelfAdjoint K)
    {D : Submodule ℝ H} (hDense : Dense (D : Set H)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hdecay : ExponentialBoundOn K D ρ) (f : H) :
    (1 - ρ) * ‖f‖ ^ 2 ≤ ⟪f, (1 - K) f⟫_ℝ :=
  quadratic_bound_of_opNorm_le (opNorm_le_of_dense_exponential hK hDense hρ hdecay) f

/-- Transparent source hypotheses: actual self-adjointness, nonnegative
quadratic form, and actual operator norm at most one. -/
structure PositiveSelfAdjointContraction (K : H →L[ℝ] H) : Prop where
  selfAdjoint : IsSelfAdjoint K
  nonnegative : ∀ f : H, 0 ≤ ⟪f, K f⟫_ℝ
  norm_le_one : ‖K‖ ≤ 1

/-- Source-facing conclusion with a strictly positive gap. The only
decay input is the explicitly displayed bound on actual powers on the
dense linear subspace; no spectral or quadratic gap is supplied. -/
theorem positive_contraction_spectral_gap {K : H →L[ℝ] H}
    (hK : PositiveSelfAdjointContraction K) {D : Submodule ℝ H}
    (hDense : Dense (D : Set H)) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdecay : ExponentialBoundOn K D ρ) :
    ‖K‖ ≤ ρ ∧ 0 < 1 - ρ ∧
      ∀ f : H, (1 - ρ) * ‖f‖ ^ 2 ≤ ⟪f, (1 - K) f⟫_ℝ := by
  have hn := opNorm_le_of_dense_exponential hK.selfAdjoint hDense hρ0 hdecay
  exact ⟨hn, sub_pos.mpr hρ1, quadratic_bound_of_opNorm_le hn⟩

end PeriodicAttractiveLogGas.DobrushinSpectralGap
