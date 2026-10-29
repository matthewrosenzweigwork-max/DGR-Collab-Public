import DGRHS.Gaussian.PeriodicLatticeShellSums

/-!
Packet P9g, unit 2 (part 0): the critical-exponent lattice sum.

`Σ_{0<‖k‖≤K} ‖k‖^{-d} ≤ C (1 + log K)` for `K ≥ 1` on `ℤ^d` (the logarithmic divergence of the
LOG Fourier coefficients `ĝ(k) ∝ ‖k‖^{-d}`).  Dyadic doubling: the shell `R < ‖k‖ ≤ 2R` carries at
most `(5R)^d` lattice points each of weight `≤ R^{-d}`, hence adds at most `5^d` to the sum.
This is the torus replacement of `∫_{1≤|ξ|≤K} |ξ|^{-d} dξ = |S^{d-1}| log K` used for the
feature diagonal `g_τ(0) ≲ 1 + log(1/τ)` of the heat-shifted LOG truncation.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The truncated critical sum term `‖k‖^{-d} 1_{0<‖k‖≤R}`. -/
def periodicLogLowTerm (R : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  open Classical in
  if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ R then
    (‖periodicFrequencyVector k‖⁻¹) ^ (Fintype.card ι) else 0

lemma periodicLogLowTerm_nonneg (R : ℝ) (k : PeriodicFrequency ι) : 0 ≤ periodicLogLowTerm R k := by
  unfold periodicLogLowTerm
  split_ifs
  · positivity
  · exact le_rfl

lemma periodicLogLowTerm_mono {R S : ℝ} (hRS : R ≤ S) (k : PeriodicFrequency ι) :
    periodicLogLowTerm R k ≤ periodicLogLowTerm S k := by
  unfold periodicLogLowTerm
  by_cases h : k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ R
  · rw [ite_eq_left h, ite_eq_left ⟨h.1, h.2.trans hRS⟩]
  · rw [ite_eq_right h]
    split_ifs
    · positivity
    · exact le_rfl

lemma periodicLogLowTerm_summable (R : ℝ) (hR : 0 ≤ R) :
    Summable (periodicLogLowTerm (ι := ι) R) := by
  classical
  apply summable_of_hasFiniteSupport
  apply (finite_periodicFrequency_norm_le (ι := ι) R hR).subset
  intro k hk
  by_contra hnot
  apply hk
  unfold periodicLogLowTerm
  rw [ite_eq_right]
  intro h
  exact hnot h.2

/-- Dyadic doubling step. -/
lemma periodicLogLowSum_double (R : ℝ) (hR : 1 ≤ R) :
    ∑' k : PeriodicFrequency ι, periodicLogLowTerm (2 * R) k ≤
      ∑' k : PeriodicFrequency ι, periodicLogLowTerm R k + 5 ^ (Fintype.card ι) := by
  classical
  set d : ℕ := Fintype.card ι with hd
  have hR0 : 0 < R := by linarith
  have hfin := finite_periodicFrequency_norm_le (ι := ι) (2 * R) (by linarith)
  set F : Finset (PeriodicFrequency ι) := hfin.toFinset with hF
  set sh : PeriodicFrequency ι → ℝ := fun k => if k ∈ F then (R⁻¹) ^ d else 0 with hsh
  have hsh_nn : ∀ k, 0 ≤ sh k := fun k => by
    simp only [hsh]; split_ifs
    · positivity
    · exact le_rfl
  have hsh_sum : Summable sh := by
    apply summable_of_hasFiniteSupport
    apply (F.finite_toSet).subset
    intro k hk
    by_contra hnot
    apply hk
    simp only [hsh]
    rw [ite_eq_right (by simpa using hnot)]
  have hpt : ∀ k, periodicLogLowTerm (2 * R) k ≤ periodicLogLowTerm R k + sh k := by
    intro k
    have hnn := periodicLogLowTerm_nonneg (ι := ι) R k
    have hsn := hsh_nn k
    by_cases h1 : k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ R
    · have := periodicLogLowTerm_mono (ι := ι) (show R ≤ 2 * R by linarith) k
      have h2 : periodicLogLowTerm (2 * R) k = periodicLogLowTerm R k := by
        unfold periodicLogLowTerm
        rw [ite_eq_left h1, ite_eq_left ⟨h1.1, h1.2.trans (by linarith)⟩]
      linarith
    · by_cases h2 : k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ 2 * R
      · have hk0 : k ≠ 0 := h2.1
        have hkR : R < ‖periodicFrequencyVector k‖ := by
          by_contra hc
          exact h1 ⟨hk0, not_lt.mp hc⟩
        have hkF : k ∈ F := by
          simp only [hF, Set.Finite.mem_toFinset]
          exact h2.2
        have hlow : periodicLogLowTerm (2 * R) k = (‖periodicFrequencyVector k‖⁻¹) ^ d := by
          unfold periodicLogLowTerm
          rw [ite_eq_left h2]
        have hshk : sh k = (R⁻¹) ^ d := by simp only [hsh]; rw [ite_eq_left hkF]
        rw [hlow, hshk]
        have : (‖periodicFrequencyVector k‖⁻¹) ^ d ≤ (R⁻¹) ^ d :=
          pow_le_pow_left₀ (by positivity) (inv_anti₀ hR0 hkR.le) d
        linarith
      · have : periodicLogLowTerm (2 * R) k = 0 := by
          unfold periodicLogLowTerm
          rw [ite_eq_right h2]
        rw [this]
        linarith
  have hS1 := periodicLogLowTerm_summable (ι := ι) (2 * R) (by linarith)
  have hS2 := periodicLogLowTerm_summable (ι := ι) R hR0.le
  have h1 := hS1.tsum_le_tsum hpt (hS2.add hsh_sum)
  rw [hS2.tsum_add hsh_sum] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  -- the count of the shell
  have hsum_sh : ∑' k, sh k = (F.card : ℝ) * (R⁻¹) ^ d := by
    rw [tsum_eq_sum (s := F) (fun k hk => by simp only [hsh]; rw [ite_eq_right hk])]
    simp only [hsh]
    rw [Finset.sum_congr rfl (fun k hk => ite_eq_left hk), Finset.sum_const, nsmul_eq_mul]
  rw [hsum_sh]
  have hcardE : ((F.card : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * (2 * R) + 1) ^ d) := by
    have h := encard_periodicFrequency_norm_le (ι := ι) (2 * R) (by linarith)
    rw [hfin.encard_eq_coe_toFinset_card] at h
    simpa using h
  have hcard : (F.card : ℝ) ≤ (2 * (2 * R) + 1) ^ d := by
    have hx : 0 ≤ (2 * (2 * R) + 1) ^ d := by positivity
    have h := hcardE
    rw [← ENNReal.ofReal_natCast] at h
    exact (ENNReal.ofReal_le_ofReal_iff hx).mp h
  have h5 : (2 * (2 * R) + 1) ^ d ≤ (5 * R) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  calc (F.card : ℝ) * (R⁻¹) ^ d ≤ (5 * R) ^ d * (R⁻¹) ^ d :=
        mul_le_mul_of_nonneg_right (hcard.trans h5) (by positivity)
    _ = 5 ^ d := by
        rw [mul_pow, mul_assoc, ← mul_pow, mul_inv_cancel₀ hR0.ne', one_pow, mul_one]

lemma periodicLogLowSum_dyadic (J : ℕ) :
    ∑' k : PeriodicFrequency ι, periodicLogLowTerm ((2 : ℝ) ^ J) k ≤
      ∑' k : PeriodicFrequency ι, periodicLogLowTerm (1 : ℝ) k + (J : ℝ) * 5 ^ (Fintype.card ι) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    have h2 := periodicLogLowSum_double (ι := ι) ((2 : ℝ) ^ J) h1
    rw [show (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J by ring]
    push_cast
    linarith

/-- `Σ_{0<‖k‖≤K} ‖k‖^{-d} ≤ C (1 + log K)` for `K ≥ 1`. -/
theorem periodicFrequency_low_sum_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K →
      ∑' k : PeriodicFrequency ι, periodicLogLowTerm K k ≤ C * (1 + Real.log K) := by
  set d : ℕ := Fintype.card ι with hd
  set S1 : ℝ := ∑' k : PeriodicFrequency ι, periodicLogLowTerm (1 : ℝ) k with hS1
  have hS1nn : 0 ≤ S1 := tsum_nonneg (periodicLogLowTerm_nonneg _)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h5 : (0 : ℝ) ≤ 5 ^ d := by positivity
  refine ⟨S1 + 5 ^ d + 5 ^ d / Real.log 2, by positivity, ?_⟩
  intro K hK
  have hK0 : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  set a : ℝ := Real.log K / Real.log 2 with ha
  have ha0 : 0 ≤ a := by positivity
  set J : ℕ := ⌈a⌉₊ with hJ
  have hJa : (J : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hKJ : K ≤ (2 : ℝ) ^ J := by
    have hJ' : a ≤ (J : ℝ) := Nat.le_ceil a
    have h1 : Real.log K ≤ (J : ℝ) * Real.log 2 := by
      have := mul_le_mul_of_nonneg_right hJ' hl2.le
      rwa [ha, div_mul_cancel₀ _ hl2.ne'] at this
    have h2 : (2 : ℝ) ^ J = Real.exp ((J : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2]
    calc K = Real.exp (Real.log K) := (Real.exp_log hK0).symm
      _ ≤ _ := Real.exp_le_exp.mpr h1
  have hmono : ∑' k : PeriodicFrequency ι, periodicLogLowTerm K k ≤
      ∑' k : PeriodicFrequency ι, periodicLogLowTerm ((2 : ℝ) ^ J) k :=
    (periodicLogLowTerm_summable K hK0.le).tsum_le_tsum
      (fun k => periodicLogLowTerm_mono hKJ k)
      (periodicLogLowTerm_summable _ (by positivity))
  refine hmono.trans ((periodicLogLowSum_dyadic J).trans ?_)
  have hJ5 : (J : ℝ) * 5 ^ d ≤ (a + 1) * 5 ^ d := mul_le_mul_of_nonneg_right hJa.le h5
  have hexp : a * 5 ^ d = 5 ^ d / Real.log 2 * Real.log K := by
    rw [ha]; ring
  have hc : 0 ≤ 5 ^ d / Real.log 2 := by positivity
  nlinarith [mul_nonneg hc hlogK, mul_nonneg hS1nn hlogK]

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogLowTerm
#print axioms DGRHS.Periodic.periodicLogLowTerm_nonneg
#print axioms DGRHS.Periodic.periodicLogLowTerm_mono
#print axioms DGRHS.Periodic.periodicLogLowTerm_summable
#print axioms DGRHS.Periodic.periodicLogLowSum_double
#print axioms DGRHS.Periodic.periodicLogLowSum_dyadic
#print axioms DGRHS.Periodic.periodicFrequency_low_sum_log_le
