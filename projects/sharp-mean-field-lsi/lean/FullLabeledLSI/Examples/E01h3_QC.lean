import FullLabeledLSI.Examples.E01h1_Poisson
import FullLabeledLSI.Examples.E01h3_Series

/-!
# Lane D, Task B3 (part 4): `Q_C(σ)` for the Poisson kernel in terms of `c_m, d_m`

Statement skeleton (to be proved).
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI


theorem fourier_neg_eq (n : ℤ) (x : Torus 1) :
    fourier (-n) (x 0) = (cm n x : ℂ) - Complex.I * (sm n x : ℂ) := by
  apply Complex.ext
  · have h := cm_neg_idx n x
    unfold cm at h
    simp [cm, sm]
  · have h := sm_neg_idx n x
    unfold sm at h
    simp [cm, sm]

theorem sigmaHat_eq (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (n : ℤ) :
    sigmaHat α β n = (cI α β 0 n : ℂ) - Complex.I * (sI α β 0 n : ℂ) := by
  have key : ∀ μ : Measure (Torus 1), IsFiniteMeasure μ →
      ∫ x, fourier (-n) (x 0) ∂μ =
        ((∫ x, cm n (x - 0) ∂μ : ℝ) : ℂ) - Complex.I * ((∫ x, sm n (x - 0) ∂μ : ℝ) : ℂ) := by
    intro μ _
    simp only [sub_zero, fourier_neg_eq]
    rw [integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
    · exact (integrable_of_cont (continuous_cm n) μ).ofReal
    · exact ((integrable_of_cont (continuous_sm n) μ).ofReal).const_mul _
  unfold sigmaHat cI sI intS
  rw [key α inferInstance, key β inferInstance]
  push_cast
  ring

theorem normSq_sigmaHat (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (n : ℤ) :
    Complex.normSq (sigmaHat α β n) = cI α β 0 n ^ 2 + sI α β 0 n ^ 2 := by
  rw [sigmaHat_eq, Complex.normSq_apply]
  simp
  ring


/-- The series terms. -/
noncomputable def aSer (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (m : ℕ) : ℝ :=
  (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m * (cI α β 0 (2 * (m : ℤ)) ^ 2 + sI α β 0 (2 * (m : ℤ)) ^ 2)

theorem summable_aSer (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    Summable (aSer α β) := by
  have hs : Summable (fun m : ℕ => (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  refine Summable.of_norm_bounded (hs.mul_right (2 * mass α β ^ 2)) (fun m => ?_)
  unfold aSer
  have hc := abs_cI_le α β 0 (2 * (m : ℤ))
  have hd := abs_sI_le α β 0 (2 * (m : ℤ))
  have hpos : 0 ≤ (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m := by positivity
  have h1 : cI α β 0 (2 * (m : ℤ)) ^ 2 ≤ mass α β ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg (cI α β 0 (2 * (m : ℤ))), neg_abs_le (cI α β 0 (2 * (m : ℤ)))]) (le_trans (le_abs_self _) hc)
    exact this
  have h2 : sI α β 0 (2 * (m : ℤ)) ^ 2 ≤ mass α β ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg (sI α β 0 (2 * (m : ℤ))), neg_abs_le (sI α β 0 (2 * (m : ℤ)))]) (le_trans (le_abs_self _) hd)
    exact this
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem term_even (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (j : ℤ) :
    aCos * ((2 * j : ℤ) : ℝ) ^ 2 * chat poissonKernel (2 * j) *
        Complex.normSq (sigmaHat α β (2 * j)) = 256 * π ^ 2 * aSer α β j.natAbs := by
  rw [normSq_sigmaHat]
  by_cases hj : j = 0
  · subst hj; simp [aSer]
  · rw [chat_poisson_even j hj]
    have e1 : cI α β 0 (2 * j) ^ 2 + sI α β 0 (2 * j) ^ 2 =
        cI α β 0 (2 * (j.natAbs : ℤ)) ^ 2 + sI α β 0 (2 * (j.natAbs : ℤ)) ^ 2 := by
      rcases Int.natAbs_eq j with h | h
      · rw [← h]
      · have h' : 2 * j = -(2 * (j.natAbs : ℤ)) := by omega
        rw [h', cI_neg, sI_neg]; ring
    rw [e1]
    unfold aSer aCos
    have : ((2 * j : ℤ) : ℝ) ^ 2 = 4 * ((j.natAbs : ℕ) : ℝ) ^ 2 := by
      have h : ((j.natAbs : ℕ) : ℝ) ^ 2 = (j : ℝ) ^ 2 := by
        rw [← Int.cast_natCast, ← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
      push_cast
      rw [h]; ring
    rw [this]; ring

theorem term_odd (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (n : ℤ)
    (hn : Odd n) :
    aCos * (n : ℝ) ^ 2 * chat poissonKernel n * Complex.normSq (sigmaHat α β n) = 0 := by
  rw [chat_poisson_odd n hn]; simp

/-- `Q_C(σ) = 512 π² ∑_m m² r^m (c_m² + d_m²)` for `C = poissonKernel`, `r = 1/100`,
`c_m = σ(cos(4π m ·))`, `d_m = σ(sin(4π m ·))` (base point `0`).  Also the series is summable. -/
theorem QC_poisson (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    Summable (fun m : ℕ => (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
        (cI α β 0 (2 * (m : ℤ)) ^ 2 + sI α β 0 (2 * (m : ℤ)) ^ 2)) ∧
    QC poissonKernel α β = 512 * π ^ 2 * ∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
        (cI α β 0 (2 * (m : ℤ)) ^ 2 + sI α β 0 (2 * (m : ℤ)) ^ 2) := by
  have hS := summable_aSer α β
  refine ⟨hS, ?_⟩
  set S := ∑' m : ℕ, aSer α β m with hSdef
  have hSsum : HasSum (aSer α β) S := hS.hasSum
  set t : ℤ → ℝ := fun n => aCos * (n : ℝ) ^ 2 * chat poissonKernel n *
    Complex.normSq (sigmaHat α β n) with htdef
  have hQC : QC poissonKernel α β = ∑' n : {n : ℤ // n ≠ 0}, t n.1 := rfl
  have h0 : aSer α β 0 = 0 := by simp [aSer]
  have hpos : HasSum (fun n : ℕ => aSer α β (n : ℤ).natAbs) S := by
    simpa using hSsum
  have hneg : HasSum (fun n : ℕ => aSer α β (-((n : ℤ) + 1)).natAbs) S := by
    have := (hasSum_nat_add_iff (f := aSer α β) 1).mpr (by simpa [h0] using hSsum)
    convert this using 2 with n
    have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
    rw [this]
  have hZ : HasSum (fun j : ℤ => aSer α β j.natAbs) (S + S) :=
    HasSum.of_nat_of_neg_add_one hpos hneg
  have hZ' : HasSum (fun j : ℤ => 256 * π ^ 2 * aSer α β j.natAbs) (256 * π ^ 2 * (S + S)) :=
    hZ.mul_left _
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun a b h => by simpa using h
  have hT : HasSum t (256 * π ^ 2 * (S + S)) := by
    rw [← hinj.hasSum_iff]
    · convert hZ' using 1
      funext j
      exact term_even α β j
    · intro n hn
      have : Odd n := by
        rcases Int.even_or_odd n with h | h
        · exfalso; apply hn; obtain ⟨k, hk⟩ := h; exact ⟨k, by simp only; omega⟩
        · exact h
      exact term_odd α β n this
  have hsupp : Function.support t ⊆ {n : ℤ | n ≠ 0} := by
    intro n hn h0'
    apply hn
    simp [htdef, h0']
  have hsub : ∑' n : {n : ℤ // n ≠ 0}, t n.1 = ∑' n : ℤ, t n :=
    tsum_subtype_eq_of_support_subset hsupp
  have hS2 : (∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
        (cI α β 0 (2 * (m : ℤ)) ^ 2 + sI α β 0 (2 * (m : ℤ)) ^ 2)) = S := rfl
  rw [hQC, hsub, hT.tsum_eq, hS2]
  ring

end SharpLSI.FL.Ex.LaneD
