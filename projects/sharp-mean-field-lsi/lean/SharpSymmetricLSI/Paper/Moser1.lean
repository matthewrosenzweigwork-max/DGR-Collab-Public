import SharpSymmetricLSI.Paper.FourierPoincare

/-!
# The Nash inequality on the torus (Phase 3, lane D; boundedness of eigenfunctions)

For `u ∈ L²(𝕋^ι)` with an `L²` weak gradient `g` and every integer `R ≥ 1`,
`∫ u² ≤ (2R+1)^{|ι|} (∫|u|)² + (∑ⱼ ∫ gⱼ²) / (4π² R²)`
(Parseval; `|û_k| ≤ ∫|u|` on the box `|k|_∞ ≤ R`, `ĝⱼ = 2πi kⱼ û` outside it).
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped ENNReal Real

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

theorem norm_mFourierCoeff_le_integral {u : UnitAddTorus ι → ℝ} (hu : Integrable u volume)
    (k : ι → ℤ) :
    ‖mFourierCoeff (fun y => (u y : ℂ)) k‖ ≤ ∫ y, |u y| := by
  rw [mFourierCoeff_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ (Eventually.of_forall fun y => ?_))
  · exact hu.norm.congr (Eventually.of_forall fun y => by simp)
  · dsimp only
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (norm_mFourier_le _ _)

/-- **Nash inequality on `𝕋^ι`.** -/
theorem nash_torus [DecidableEq ι] {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (fun y => g y j) 2 volume)
    {R : ℕ} (hR : 1 ≤ R) :
    ∫ y, u y ^ 2 ≤ ((2 * R + 1 : ℕ) : ℝ) ^ Fintype.card ι * (∫ y, |u y|) ^ 2 +
      (∑ j, ∫ y, g y j ^ 2) / (4 * π ^ 2 * R ^ 2) := by
  have hui : Integrable u volume := hu.integrable one_le_two
  have hgi : ∀ j, Integrable (fun y => g y j) volume := fun j => (hg j).integrable one_le_two
  set c := fun k => mFourierCoeff (fun y => (u y : ℂ)) k with hc
  have hP := hasSum_sq_mFourierCoeff_real hu
  have hG : ∀ j, HasSum (fun k => 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖c k‖ ^ 2)
      (∫ y, g y j ^ 2) := by
    intro j
    have := hasSum_sq_mFourierCoeff_real (hg j)
    convert this using 1
    funext k
    rw [mFourierCoeff_grad h hui hgi k j, norm_mul]
    have : ‖2 * (π : ℂ) * I * (k j : ℂ)‖ = 2 * π * |(k j : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_two]
      rw [show ((k j : ℤ) : ℂ) = (((k j : ℤ) : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [this, mul_pow, mul_pow, mul_pow, sq_abs]
    ring
  have hsum := (hasSum_sum (s := Finset.univ) (fun j _ => hG j)).div_const (4 * π ^ 2 * R ^ 2)
  set B : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
  set A := ∫ y, |u y|
  have hB : HasSum (fun k => if k ∈ B then A ^ 2 else 0) (B.card * A ^ 2) := by
    have : HasSum (fun k : ι → ℤ => if k ∈ B then A ^ 2 else 0)
        (∑ k ∈ B, if k ∈ B then A ^ 2 else 0) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by simp only [hk, ↓reduceIte]
    rw [Finset.sum_ite_of_true (fun k hk => hk), Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard : (B.card : ℝ) = ((2 * R + 1 : ℕ) : ℝ) ^ Fintype.card ι := by
    simp only [B, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : ((R : ℤ) + 1 - -(R : ℤ)).toNat = 2 * R + 1 := by omega
    rw [this]; push_cast; ring
  have hpos : (0 : ℝ) < 4 * π ^ 2 * R ^ 2 := by
    have : (0 : ℝ) < R := by exact_mod_cast hR
    positivity
  have hle := hasSum_le (fun k => ?_) hP (hB.add hsum)
  · rw [hcard] at hle; exact hle
  · by_cases hk : k ∈ B
    · simp only [hk, ↓reduceIte]
      have h1 : ‖c k‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
        (norm_mFourierCoeff_le_integral hui k) 2
      have h2 : 0 ≤ (∑ j, 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖c k‖ ^ 2) / (4 * π ^ 2 * R ^ 2) :=
        div_nonneg (Finset.sum_nonneg fun j _ => by positivity) hpos.le
      linarith
    · simp only [hk, ↓reduceIte, zero_add]
      simp only [B, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
      obtain ⟨j, hj⟩ := hk
      have hkj : (R : ℝ) ^ 2 ≤ ((k j : ℝ)) ^ 2 := by
        have : (R : ℤ) ≤ |k j| := by
          rcases not_and_or.mp hj with h' | h' <;> [rw [abs_of_neg (by omega)]; rw [abs_of_pos (by omega)]] <;> omega
        have h2 : (R : ℝ) ≤ |(k j : ℝ)| := by exact_mod_cast this
        nlinarith [sq_abs (k j : ℝ), abs_nonneg (k j : ℝ), (Nat.cast_nonneg R : (0:ℝ) ≤ R)]
      have hsj : 4 * π ^ 2 * R ^ 2 * ‖c k‖ ^ 2 ≤ ∑ i, 4 * π ^ 2 * ((k i : ℝ)) ^ 2 * ‖c k‖ ^ 2 :=
        calc 4 * π ^ 2 * R ^ 2 * ‖c k‖ ^ 2 ≤ 4 * π ^ 2 * ((k j : ℝ)) ^ 2 * ‖c k‖ ^ 2 := by gcongr
          _ ≤ _ := Finset.single_le_sum (f := fun i => 4 * π ^ 2 * ((k i : ℝ)) ^ 2 * ‖c k‖ ^ 2)
              (fun i _ => by positivity) (Finset.mem_univ j)
      rw [le_div_iff₀ hpos]
      linarith

end SharpLSI
