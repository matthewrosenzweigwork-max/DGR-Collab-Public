import SharpSymmetricLSI.Infra.CZTorus4

/-!
# Gagliardo–Nirenberg interpolation on `𝕋^ι` (R23 lane, CZ part 5)

For `u` with `C²` lift, `|u| ≤ B`, `v = ∂_i u`, `w = ∂_i∂_i u` and `N ≥ 1`:
`∫ v^{2N} = -(2N-1) ∫ u v^{2N-2} w` (integration by parts of `∂_i(u v^{2N-1})` on the torus),
hence by Hölder `∫|v|^{2N} ≤ ((2N-1)B)^N ∫|w|^N` (`gn_torus`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_of_contDiff_lift {u : UnitAddTorus ι → ℝ} {n : ℕ}
    (hu : ContDiff ℝ n (u ∘ liftT)) : Continuous u :=
  continuous_of_liftT' hu.continuous

/-- The integration by parts identity `∫ v^{2N} = -(2N-1) ∫ u v^{2N-2} w`. -/
theorem integral_dpart_pow {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ 2 (u ∘ liftT)) (i : ι)
    (n : ℕ) :
    ∫ y, dpart u i y ^ (n + 2) =
      -((n + 1 : ℕ) : ℝ) * ∫ y, u y * dpart u i y ^ n * dpart (dpart u i) i y := by
  set U := u ∘ liftT with hUdef
  set v := dpart u i
  set V := v ∘ liftT with hVdef
  have hV : V = fun x => fderiv ℝ U x (Pi.single i 1) := dpart_comp_liftT u i
  have hV1 : ContDiff ℝ 1 V := contDiff_dpart (n := 1) hu i
  have hU1 : ContDiff ℝ 1 U := hu.of_le (by norm_num)
  set W : UnitAddTorus ι → ℝ := fun y => u y * v y ^ (n + 1) with hWdef
  have hWl : W ∘ liftT = fun x => U x * V x ^ (n + 1) := rfl
  have hW : ContDiff ℝ 1 (W ∘ liftT) := by rw [hWl]; exact hU1.mul (hV1.pow _)
  have h0 := integral_fderiv_torus_eq_zero hW (Pi.single i 1)
  have hder : ∀ x, fderiv ℝ (W ∘ liftT) x (Pi.single i 1) =
      fderiv ℝ U x (Pi.single i 1) * V x ^ (n + 1) +
        U x * (((n + 1 : ℕ) : ℝ) * V x ^ n * fderiv ℝ V x (Pi.single i 1)) := by
    intro x
    have hUd : HasFDerivAt U (fderiv ℝ U x) x :=
      (hU1.differentiable one_ne_zero x).hasFDerivAt
    have hVd : HasFDerivAt V (fderiv ℝ V x) x :=
      (hV1.differentiable one_ne_zero x).hasFDerivAt
    have h : HasFDerivAt (fun x => U x * V x ^ (n + 1)) _ x := hUd.mul (hVd.pow (n + 1))
    rw [hWl, h.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Nat.add_sub_cancel, nsmul_eq_mul]
    push_cast
    ring
  have hval : ∀ y, fderiv ℝ (W ∘ liftT) (secT y) (Pi.single i 1) =
      v y ^ (n + 2) + ((n + 1 : ℕ) : ℝ) * (u y * v y ^ n * dpart v i y) := by
    intro y
    rw [hder]
    have e1 : U (secT y) = u y := by simp [hUdef, liftT_secT]
    have e2 : V (secT y) = v y := by simp [hVdef, liftT_secT]
    have e3 : fderiv ℝ U (secT y) (Pi.single i 1) = v y := rfl
    have e4 : fderiv ℝ V (secT y) (Pi.single i 1) = dpart v i y := rfl
    rw [e1, e2, e3, e4]
    ring
  simp_rw [hval] at h0
  have hcu : Continuous u := continuous_of_contDiff_lift hu
  have hcv : Continuous v := continuous_of_contDiff_lift hV1
  have hcw : Continuous (dpart v i) :=
    continuous_of_contDiff_lift (contDiff_dpart (n := 0) hV1 i)
  have hi1 : Integrable (fun y => v y ^ (n + 2)) volume :=
    (hcv.pow _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun y => u y * v y ^ n * dpart v i y) volume :=
    ((hcu.mul (hcv.pow _)).mul hcw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add hi1 (hi2.const_mul _), integral_const_mul] at h0
  linarith

theorem memLp_of_continuous_torus {E : Type*} [NormedAddCommGroup E] {f : UnitAddTorus ι → E}
    (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p volume := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hf).isBounded.exists_norm_le
  exact MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC _ ⟨x, Set.mem_univ _, rfl⟩)

theorem integrable_of_continuous_torus {E : Type*} [NormedAddCommGroup E]
    {f : UnitAddTorus ι → E} (hf : Continuous f) : Integrable f volume :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Gagliardo–Nirenberg**: `∫|∂_iu|^{2N} ≤ ((2N-1)B)^N ∫|∂_i∂_iu|^N` for `|u| ≤ B`. -/
theorem gn_torus {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ 2 (u ∘ liftT)) {B : ℝ}
    (hB : ∀ y, |u y| ≤ B) (i : ι) {N : ℕ} (hN : 1 ≤ N) :
    ∫ y, |dpart u i y| ^ (2 * N) ≤
      ((2 * N - 1) * B) ^ N * ∫ y, |dpart (dpart u i) i y| ^ N := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set v := dpart u i
  set w := dpart v i
  have hV1 : ContDiff ℝ 1 (v ∘ liftT) := contDiff_dpart (n := 1) hu i
  have hcu : Continuous u := continuous_of_contDiff_lift hu
  have hcv : Continuous v := continuous_of_contDiff_lift hV1
  have hcw : Continuous w := continuous_of_contDiff_lift (contDiff_dpart (n := 0) hV1 i)
  set I1 := ∫ y, |v y| ^ (2 * N)
  set I2 := ∫ y, |w y| ^ N
  have hI1 : 0 ≤ I1 := integral_nonneg fun _ => by positivity
  have hI2 : 0 ≤ I2 := integral_nonneg fun _ => by positivity
  -- integration by parts
  obtain ⟨n, hnN⟩ : ∃ n, 2 * N = n + 2 := ⟨2 * N - 2, by omega⟩
  have hibp := integral_dpart_pow hu i n
  have hI1eq : I1 = ∫ y, v y ^ (n + 2) := by
    simp only [I1, hnN]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have heven : Even (n + 2) := ⟨N, by omega⟩
    exact heven.pow_abs (v y)
  set J := ∫ y, |v y| ^ n * |w y|
  have hJ : I1 ≤ ((n + 1 : ℕ) : ℝ) * B * J := by
    rw [hI1eq, hibp, neg_mul, ← mul_neg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← integral_const_mul]
    have hint1 : Integrable (fun y => -(u y * v y ^ n * w y)) volume :=
      integrable_of_continuous_torus (((hcu.mul (hcv.pow _)).mul hcw).neg)
    have hint2 : Integrable (fun y => B * (|v y| ^ n * |w y|)) volume :=
      integrable_of_continuous_torus (continuous_const.mul ((hcv.abs.pow _).mul hcw.abs))
    rw [← integral_neg]
    refine integral_mono hint1 hint2 fun y => ?_
    have h1 : -(u y * v y ^ n * w y) ≤ |u y| * (|v y| ^ n * |w y|) :=
      calc -(u y * v y ^ n * w y) ≤ |u y * v y ^ n * w y| := neg_le_abs _
        _ = _ := by rw [abs_mul, abs_mul, abs_pow, mul_assoc]
    exact h1.trans (mul_le_mul_of_nonneg_right (hB y) (by positivity))
  -- Hölder
  have hn2 : (n + 1 : ℕ) = 2 * N - 1 := by omega
  have hcast : (((n + 1 : ℕ) : ℝ)) = 2 * N - 1 := by
    rw [hn2, Nat.cast_sub (by omega)]; push_cast; ring
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · -- `N = 1`, `n = 0`
    have hN1' : N = 1 := by omega
    subst hN1'
    have hn0 : n = 0 := by omega
    subst hn0
    have hJI : J = I2 := by simp only [J, I2, pow_zero, one_mul, pow_one]
    calc I1 ≤ ((0 + 1 : ℕ) : ℝ) * B * J := hJ
      _ = ((2 * ((1 : ℕ) : ℝ) - 1) * B) ^ 1 * I2 := by rw [hJI]; push_cast; ring
  · have hN' : (1 : ℝ) < N := by exact_mod_cast hN2
    set q := Real.conjExponent (N : ℝ)
    have hpq : q.HolderConjugate (N : ℝ) := (Real.HolderConjugate.conjExponent hN').symm
    have hq0 : 0 < q := hpq.pos
    have hqn : (n : ℝ) * q = 2 * N := by
      simp only [q, Real.conjExponent]
      have : (N : ℝ) - 1 ≠ 0 := by linarith
      have hn' : (n : ℝ) = 2 * N - 2 := by
        have : n = 2 * N - 2 := by omega
        rw [this, Nat.cast_sub (by omega)]; push_cast; ring
      rw [hn']
      field_simp <;> ring
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (μ := volume)
      (f := fun y => |v y| ^ n) (g := fun y => |w y|)
      (Filter.Eventually.of_forall fun y => by positivity)
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
      (memLp_of_continuous_torus (hcv.abs.pow _) _) (memLp_of_continuous_torus hcw.abs _)
    have e1 : ∀ y, (|v y| ^ n) ^ q = |v y| ^ (2 * N) := fun y => by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hqn]
      norm_cast
    have e2 : ∀ y, |w y| ^ (N : ℝ) = |w y| ^ N := fun y => Real.rpow_natCast _ _
    simp only [e1, e2] at hH
    -- `J ≤ I1^{1/q} I2^{1/N}` with `1/q = (N-1)/N`
    have hJle : J ≤ I1 ^ (1 / q) * I2 ^ (1 / (N : ℝ)) := hH
    have hsum : 1 / q + 1 / (N : ℝ) = 1 := by
      rw [one_div, one_div]; exact hpq.inv_add_inv_eq_one
    rcases hI1.eq_or_lt with h0 | hpos
    · rw [← h0]
      have : (1 : ℝ) ≤ 2 * N - 1 := by linarith
      exact mul_nonneg (pow_nonneg (mul_nonneg (by linarith) hB0) _) hI2
    -- divide by `I1^{1/q}`
    have hsplit : I1 = I1 ^ (1 / q) * I1 ^ (1 / (N : ℝ)) := by
      rw [← Real.rpow_add hpos, hsum, Real.rpow_one]
    have hq1 : 0 < I1 ^ (1 / q) := Real.rpow_pos_of_pos hpos _
    have hkey : I1 ^ (1 / (N : ℝ)) ≤ (2 * N - 1) * B * I2 ^ (1 / (N : ℝ)) := by
      have h := hJ.trans (mul_le_mul_of_nonneg_left hJle (mul_nonneg (Nat.cast_nonneg _) hB0))
      rw [hcast] at h
      conv_lhs at h => rw [hsplit]
      have : I1 ^ (1 / q) * I1 ^ (1 / (N : ℝ)) ≤
          I1 ^ (1 / q) * ((2 * N - 1) * B * I2 ^ (1 / (N : ℝ))) := by
        calc I1 ^ (1 / q) * I1 ^ (1 / (N : ℝ)) ≤ (2 * N - 1) * B * (I1 ^ (1 / q) * I2 ^ (1 / (N : ℝ))) := h
          _ = _ := by ring
      exact le_of_mul_le_mul_left this hq1
    have hc0 : 0 ≤ (2 * (N : ℝ) - 1) * B := by
      have : (1 : ℝ) ≤ 2 * N - 1 := by linarith
      positivity
    have := pow_le_pow_left₀ (Real.rpow_nonneg hI1 _) hkey N
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← Real.rpow_natCast (I1 ^ (1 / (N : ℝ))), ← Real.rpow_mul hI1, one_div,
      inv_mul_cancel₀ hN0, Real.rpow_one, mul_pow, ← Real.rpow_natCast (I2 ^ _),
      ← Real.rpow_mul hI2, inv_mul_cancel₀ hN0, Real.rpow_one] at this
    exact this

end SharpLSI
