import Mathlib
import DGPS.Frontier.LIP051.T09

/-!
# LIP051.10: Exact U-statistic L2 norm

Task id: LIP051.10 (node LIP051, joint Gaussian and quadratic fluctuation limit).
Title: Exact U-statistic L2 norm.

Provides:
* `DGPS.Frontier.LIP051.lip051_10_exact_u_statistic_l2_norm`: for a probability measure `μ` on `E`,
  a measurable symmetric real kernel `F` in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost
  every `y`, and `N ≥ 1`, let `A_N(F) = N⁻¹ ∑_{i<j} F(X_i, X_j)` under `Q_N = Measure.pi (fun _ => μ)`.
  Then `A_N(F)` has mean zero; it lies in `L²(Q_N)` with `‖A_N(F)‖₂² = (N-1)/(2N) ‖F‖₂²`; and
  `‖A_N(F)‖₁ ≤ (1/√2) ‖F‖₂`.
* Helpers (all suffixed `_LIP05110`): `sq_toReal_eLpNorm_two_LIP05110`, the identity
  `‖f‖₂² = ∫ f²` for a real `L²` function; `card_increasing_pairs_LIP05110`, the count
  `#{(i, j) : i < j} = N (N-1) / 2`.

R5 notes:
* Hypotheses. They are exactly those of LIP051.09 (and of its helpers LIP051.38 to LIP051.40): `μ` is
  a probability measure, `F` is measurable (`hF`), symmetric (`hsymm`), in `L²(μ ⊗ μ)` (`hL2`), and
  centered in its first argument for almost every second argument (`hcent`). The one further
  hypothesis is `1 ≤ N`, which is the domain `N ≥ 1` of the specification. No hypothesis is added
  beyond these.
* The sum `∑_{i<j}`. It is written as the finite sum over the Finset of pairs
  `{p : Fin N × Fin N | p.1 < p.2}` with summand `F (x p.1) (x p.2)`, where `x : Fin N → E` is the
  sample. The strict order of `Fin N` is used, so the pairs are exactly the increasing pairs.
* The norms. `‖F‖₂` is the real `L²(μ ⊗ μ)` norm `(eLpNorm (fun p => F p.1 p.2) 2 (μ.prod μ)).toReal`,
  as in LIP051.09. The identity `‖A_N(F)‖₂² = (N-1)/(2N) ‖F‖₂²` is stated with the real norm squared.
  Since `A_N(F)` is shown to lie in `L²(Q_N)`, the real norm is the genuine `L²` norm and is not a
  value of an infinite norm.
* Conclusions beyond the list. The specification states the three displayed identities. The
  conclusion `MemLp A 2 Q` is added as the first conjunct of the second clause. It is the proof step
  "the finite sum is L2" made explicit, and it is needed for the real norm identity to be meaningful.
  No hypothesis is involved.
* The L1 bound. It is stated in extended form: `eLpNorm A 1 Q ≤ ENNReal.ofReal (1/√2) * ‖F‖₂` with
  `‖F‖₂` the extended `L²(μ ⊗ μ)` norm. It is the specification's `‖A_N(F)‖₁ ≤ (1/√2) ‖F‖₂` with no
  real-valued truncation, so it cannot hide an infinite value.
* Mean zero. `∫ A_N(F) dQ_N = 0` is the Bochner integral; integrability of each summand is supplied
  by LIP051.09 (not a hypothesis), so the mean is meaningful.
* Mode indexing (FD-002). No mode index occurs in this unit. The indices are particle labels in
  `Fin N`. There is no basis, no coordinate `e_j`, no Gaussian object and no zero mode. The
  positive-mode and mode-zero issue of FD-002 does not arise, and neither reading is adopted.
* No strengthening of the specification is claimed beyond the conjunct above. The helpers are
  internal, and the public declaration is the single theorem above.
-/

namespace DGPS.Frontier.LIP051

open MeasureTheory ENNReal

/-- For a real function in `L²(ν)`, the squared L2 norm is the integral of its square. -/
lemma sq_toReal_eLpNorm_two_LIP05110 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (f : α → ℝ) (hf : MemLp f 2 ν) :
    (eLpNorm f 2 ν).toReal ^ 2 = ∫ x, f x ^ 2 ∂ν := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂ν :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hcongr : (∫ x, ‖f x‖ ^ (2 : ℝ) ∂ν) = ∫ x, f x ^ 2 ∂ν :=
    integral_congr_ae (ae_of_all _ fun x => by
      simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs])
  simp only [ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), ← hcongr, ← Real.rpow_natCast,
    ← Real.rpow_mul hnn]
  norm_num

/-- The number of increasing pairs `i < j` in `Fin N` is `N (N-1) / 2`, stated as `2 · #P = N (N-1)`. -/
lemma card_increasing_pairs_LIP05110 (N : ℕ) :
    (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)).card * 2 = N * (N - 1) := by
  have h := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N)))
  rw [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] at h
  rw [h, Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd]

/-- **LIP051.10.** Let `μ` be a probability measure on `E`, and `F : E → E → ℝ` a measurable
symmetric kernel in `L²(μ ⊗ μ)` with `∫ F(x, y) dμ(x) = 0` for almost every `y`. For `N ≥ 1`, let
`A_N(F) = N⁻¹ ∑_{i<j} F(X_i, X_j)` on `Fin N → E` under `Q_N = Measure.pi (fun _ => μ)`. Then
`E A_N(F) = 0`, `A_N(F)` lies in `L²(Q_N)` with `‖A_N(F)‖₂² = (N-1)/(2N) ‖F‖₂²`, and
`‖A_N(F)‖₁ ≤ (1/√2) ‖F‖₂`. -/
theorem lip051_10_exact_u_statistic_l2_norm
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (F : E → E → ℝ) (hF : Measurable (fun p : E × E => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : E × E => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0)
    (N : ℕ) (hN : 1 ≤ N) :
    let Q := Measure.pi (fun _ : Fin N => μ)
    let A : (Fin N → E) → ℝ := fun x =>
      (N : ℝ)⁻¹ * ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), F (x p.1) (x p.2)
    (∫ x, A x ∂Q = 0) ∧
    (MemLp A 2 Q ∧
      (eLpNorm A 2 Q).toReal ^ 2 =
        ((N : ℝ) - 1) / (2 * N) * (eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)).toReal ^ 2) ∧
    eLpNorm A 1 Q ≤
      ENNReal.ofReal (1 / Real.sqrt 2) * eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ) := by
  intro Q A
  set P := Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2) with hP
  set c := (eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ)).toReal with hc
  set S : (Fin N → E) → ℝ := fun x => ∑ p ∈ P, F (x p.1) (x p.2) with hS
  have hAS : A = fun x => (N : ℝ)⁻¹ * S x := rfl
  have hmem : ∀ p ∈ P, p.1 < p.2 := fun p hp => (Finset.mem_filter.1 hp).2
  -- each summand: integrable with mean zero, by LIP051.09
  have hint : ∀ p ∈ P, Integrable (fun x : Fin N → E => F (x p.1) (x p.2)) Q ∧
      ∫ x, F (x p.1) (x p.2) ∂Q = 0 := fun p hp =>
    (lip051_09_covariances_distinct_pair_summands μ F hF hsymm hL2 hcent p.1 p.2 p.1 p.2
      (hmem p hp) (hmem p hp)).2.1
  -- products of two summands, by LIP051.09
  have hprod : ∀ p ∈ P, ∀ q ∈ P, Integrable (fun x : Fin N → E => F (x p.1) (x p.2) * F (x q.1) (x q.2)) Q ∧
      ∫ x, F (x p.1) (x p.2) * F (x q.1) (x q.2) ∂Q =
        if (p.1, p.2) = (q.1, q.2) then c ^ 2 else 0 := fun p hp q hq =>
    (lip051_09_covariances_distinct_pair_summands μ F hF hsymm hL2 hcent p.1 p.2 q.1 q.2
      (hmem p hp) (hmem q hq)).1
  have hSsq : ∀ x, S x ^ 2 = ∑ p ∈ P, ∑ q ∈ P, F (x p.1) (x p.2) * F (x q.1) (x q.2) := by
    intro x
    simp only [hS, sq, Finset.sum_mul_sum]
  have hSsq_int : Integrable (fun x => S x ^ 2) Q := by
    simp only [hSsq]
    exact integrable_finsetSum P fun p hp => integrable_finsetSum P fun q hq => (hprod p hp q hq).1
  have hmeas : ∀ p : Fin N × Fin N, Measurable (fun x : Fin N → E => F (x p.1) (x p.2)) := fun p => by
    have hpair : Measurable (fun x : Fin N → E => (x p.1, x p.2)) :=
      (measurable_pi_apply p.1).prodMk (measurable_pi_apply p.2)
    exact hF.comp hpair
  have hS_aesm : AEStronglyMeasurable S Q :=
    (Finset.measurable_fun_sum P fun p _ => hmeas p).aestronglyMeasurable
  have hS_L2 : MemLp S 2 Q := (memLp_two_iff_integrable_sq hS_aesm).2 hSsq_int
  have hS_mean : ∫ x, S x ∂Q = 0 := by
    simp only [hS]
    rw [integral_finsetSum P fun p hp => (hint p hp).1]
    exact Finset.sum_eq_zero fun p hp => (hint p hp).2
  have hS2_val : ∫ x, S x ^ 2 ∂Q = (P.card : ℝ) * c ^ 2 := by
    simp only [hSsq]
    rw [integral_finsetSum P fun p hp => integrable_finsetSum P fun q hq => (hprod p hp q hq).1]
    have hinner : ∀ p ∈ P, ∫ x, ∑ q ∈ P, F (x p.1) (x p.2) * F (x q.1) (x q.2) ∂Q = c ^ 2 := by
      intro p hp
      rw [integral_finsetSum P fun q hq => (hprod p hp q hq).1,
        Finset.sum_congr rfl fun q hq => (hprod p hp q hq).2]
      simp [Prod.mk.eta, hp]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  have hcardR : (P.card : ℝ) * 2 = (N : ℝ) * ((N : ℝ) - 1) := by
    have h := congrArg (Nat.cast (R := ℝ)) (card_increasing_pairs_LIP05110 N)
    push_cast [Nat.cast_sub hN] at h
    exact h
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hAsq : ∫ x, A x ^ 2 ∂Q = ((N : ℝ) - 1) / (2 * N) * c ^ 2 := by
    have hA2 : ∀ x, A x ^ 2 = ((N : ℝ)⁻¹) ^ 2 * S x ^ 2 := fun x => by
      simp only [hAS]; ring
    simp only [hA2]
    rw [integral_const_mul, hS2_val]
    have hPc : (P.card : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by linarith
    rw [hPc]
    field_simp
  have hA_L2 : MemLp A 2 Q := by
    show MemLp (fun x => (N : ℝ)⁻¹ * S x) 2 Q
    exact hS_L2.const_mul _
  have hA_mean : ∫ x, A x ∂Q = 0 := by
    show ∫ x, (N : ℝ)⁻¹ * S x ∂Q = 0
    rw [integral_const_mul, hS_mean, mul_zero]
  have hA_norm : (eLpNorm A 2 Q).toReal ^ 2 = ((N : ℝ) - 1) / (2 * N) * c ^ 2 := by
    rw [sq_toReal_eLpNorm_two_LIP05110 A hA_L2, hAsq]
  have hL1 : eLpNorm A 1 Q ≤ eLpNorm A 2 Q := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hFfin : eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ) = ENNReal.ofReal c :=
    (ENNReal.ofReal_toReal hL2.eLpNorm_lt_top.ne).symm
  have hAfin : eLpNorm A 2 Q = ENNReal.ofReal (eLpNorm A 2 Q).toReal :=
    (ENNReal.ofReal_toReal hA_L2.eLpNorm_lt_top.ne).symm
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have ha0 : 0 ≤ (eLpNorm A 2 Q).toReal := ENNReal.toReal_nonneg
  have hk : ((N : ℝ) - 1) / (2 * N) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsq : (eLpNorm A 2 Q).toReal ^ 2 ≤ ((1 / Real.sqrt 2) * c) ^ 2 := by
    have h12 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [mul_pow, h12, hA_norm]
    exact mul_le_mul_of_nonneg_right hk (sq_nonneg c)
  have hle : (eLpNorm A 2 Q).toReal ≤ (1 / Real.sqrt 2) * c :=
    (pow_le_pow_iff_left₀ ha0 (mul_nonneg (by positivity) hc0) two_ne_zero).1 hsq
  refine ⟨hA_mean, ⟨hA_L2, hA_norm⟩, ?_⟩
  calc eLpNorm A 1 Q ≤ eLpNorm A 2 Q := hL1
    _ = ENNReal.ofReal (eLpNorm A 2 Q).toReal := hAfin
    _ ≤ ENNReal.ofReal ((1 / Real.sqrt 2) * c) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (1 / Real.sqrt 2) * ENNReal.ofReal c :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (1 / Real.sqrt 2) * eLpNorm (fun p : E × E => F p.1 p.2) 2 (μ.prod μ) := by
        rw [hFfin]

end DGPS.Frontier.LIP051
