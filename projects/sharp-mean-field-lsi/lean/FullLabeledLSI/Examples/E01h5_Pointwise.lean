import FullLabeledLSI.Examples.E01h5_Inst

/-!
# Lane D, Task B5 (part 2): the Hessian bound at a Dirac mass
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

variable (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β]

theorem bdd_cI (x : Torus 1) : ∃ K, ∀ m : ℕ, |cI α β x (2 * (m : ℤ))| ≤ K :=
  ⟨mass α β, fun m => abs_cI_le α β x _⟩

theorem bdd_sI (x : Torus 1) : ∃ K, ∀ m : ℕ, |sI α β x (2 * (m : ℤ))| ≤ K :=
  ⟨mass α β, fun m => abs_sI_le α β x _⟩

theorem cI_nat_zero (hm : α Set.univ = β Set.univ) (x : Torus 1) :
    cI α β x (2 * ((0 : ℕ) : ℤ)) = 0 := by simpa using cI_zero α β x hm

theorem sI_nat_zero (x : Torus 1) : sI α β x (2 * ((0 : ℕ) : ℤ)) = 0 := by
  simpa using sI_zero α β x

/-- `N(y) = ∑ m² r^m (c_m² + d_m²)` at base point `y`. -/
noncomputable def Nsum (x : Torus 1) : ℝ :=
  ∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m * (cI α β x (2 * (m : ℤ)) ^ 2 + sI α β x (2 * (m : ℤ)) ^ 2)

theorem summable_Nsum (x : Torus 1) :
    Summable fun m : ℕ => (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
      (cI α β x (2 * (m : ℤ)) ^ 2 + sI α β x (2 * (m : ℤ)) ^ 2) := by
  have h1 := summable_Ncos_terms (fun m : ℕ => cI α β x (2 * (m : ℤ))) (bdd_cI α β x)
  have h2 := summable_Ncos_terms (fun m : ℕ => sI α β x (2 * (m : ℤ))) (bdd_sI α β x)
  refine (h1.add h2).congr (fun m => ?_)
  ring

theorem Nsum_inv (x : Torus 1) : Nsum α β x = Nsum α β 0 := by
  unfold Nsum
  congr 1; funext m
  rw [cI_sq_add_sI_sq]

theorem Nsum_nonneg (x : Torus 1) : 0 ≤ Nsum α β x :=
  tsum_nonneg fun m => by positivity

/-- The `A` part. -/
theorem A_le {ℓ : ℝ} (hℓ1 : ℓ ≤ aCos) (y : Torus 1) :
    4 * intS (convS (dT (dT poissonKernel)) α β) α β +
        2 * ℓ * intS (convS poissonKernel α β) α β ≤ -(1792 * π ^ 2) * Nsum α β y := by
  set q : ℕ → ℝ := fun m => cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2 with hq
  have h1 := intS_convS_hasSum α β y summable_pa (b := fun _ => (0 : ℝ)) (by simp) hasSum_C
  have h2 := intS_convS_hasSum α β y summable_pa2 (b := fun _ => (0 : ℝ)) (by simp) hasSum_C''
  have hN := (summable_Nsum α β y).hasSum
  have hcomb := (h2.mul_left 4).add (h1.mul_left (2 * ℓ))
  have hrhs := hN.mul_left (-(1792 * π ^ 2))
  unfold Nsum
  refine hasSum_le (fun m => ?_) hcomb hrhs
  by_cases hm0 : m = 0
  · subst hm0; simp [pa, pa2]
  · have hQ : 0 ≤ cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2 := by positivity
    have hR : 0 ≤ (1 / 100 : ℝ) ^ m := by positivity
    have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
      nlinarith
    have hpi : 0 < π ^ 2 := by positivity
    have hl : ℓ ≤ 4 * π ^ 2 := by simpa [aCos] using hℓ1
    have key : -2048 * π ^ 2 * (m : ℝ) ^ 2 + 64 * ℓ ≤ -(1792 * π ^ 2) * (m : ℝ) ^ 2 := by
      nlinarith
    have e1 : 4 * (pa2 m * (cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2)) +
        2 * ℓ * (pa m * (cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2)) =
        ((cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2) * (1 / 100 : ℝ) ^ m) *
          (-2048 * π ^ 2 * (m : ℝ) ^ 2 + 64 * ℓ) := by
      unfold pa pa2; rw [if_neg hm0]; ring
    rw [e1]
    calc _ ≤ ((cI α β y (2 * (m : ℤ)) ^ 2 + sI α β y (2 * (m : ℤ)) ^ 2) * (1 / 100 : ℝ) ^ m) *
          (-(1792 * π ^ 2) * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left key (mul_nonneg hQ hR)
      _ = _ := by ring

/-- The `ρ = δ_y` part. -/
theorem E_le (hm : α Set.univ = β Set.univ) (y : Torus 1) :
    2 * (convS (dT poissonKernel) α β y) ^ 2 +
        4 * intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α β z) α β ≤
      (2 * (128 * π) ^ 2 * (107 / 2000)) * Nsum α β y := by
  set c : ℕ → ℝ := fun m => cI α β y (2 * (m : ℤ)) with hc
  set d : ℕ → ℝ := fun m => sI α β y (2 * (m : ℤ)) with hd
  have hbc : ∃ K, ∀ j, |c j| ≤ K := bdd_cI α β y
  have hbd : ∃ K, ∀ j, |d j| ≤ K := bdd_sI α β y
  have hc0 : c 0 = 0 := cI_nat_zero α β hm y
  have hd0 : d 0 = 0 := sI_nat_zero α β y
  set S1 : ℝ := ∑' m : ℕ, (m : ℝ) * (1 / 100 : ℝ) ^ m * d m with hS1
  have hS1s := summable_lin_terms d hbd
  -- Q₁(y)
  have hQ1 : convS (dT poissonKernel) α β y = 128 * π * S1 := by
    have h := (convS_hasSum α β y (a := fun _ => (0 : ℝ)) (b := pb) (by simp) summable_pb hasSum_C' y).tsum_eq
    rw [← h, hS1, ← tsum_mul_left]
    congr 1; funext m
    simp only [sub_self, cm_zero_pt, sm_zero_pt, mul_one, mul_zero, add_zero, zero_mul, zero_sub]
    simp only [hc, hd, pb]
    ring
  -- cross term
  have hX := cross_hasSum α β y summable_pb hasSum_C'_sm
  have hTc := (summable_Tcos_terms c hbc).hasSum
  have hTs := (summable_Tsin_terms d hbd).hasSum
  set U : ℝ := ∑' p : ℕ × ℕ, wgt p * d p.1 * (d (p.1 + p.2) + sgnk p.1 p.2 * d (Nat.dist p.1 p.2))
    with hU
  have hX' : HasSum (fun p : ℕ × ℕ =>
      (128 * π) ^ 2 / 2 * (wgt p * c p.1 * (c (Nat.dist p.1 p.2) - c (p.1 + p.2))) -
        (128 * π) ^ 2 / 2 * (wgt p * d p.1 * (d (p.1 + p.2) + sgnk p.1 p.2 * d (Nat.dist p.1 p.2))))
      (intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α β z) α β) := by
    convert hX using 1
    funext p
    rw [pb_mul]
    simp only [hc, hd]
    ring
  have hXeq := hX'.unique ((hTc.mul_left ((128 * π) ^ 2 / 2)).sub (hTs.mul_left ((128 * π) ^ 2 / 2)))
  have hTsin : Tsin d = S1 ^ 2 - U := rfl
  have hTcos := Tcos_le c hbc hc0
  have hTsl := Tsin_le d hbd hd0
  have hN : Nsum α β y = Ncos c + Ncos d := by
    unfold Nsum Ncos
    rw [← (summable_Ncos_terms c hbc).tsum_add (summable_Ncos_terms d hbd)]
    congr 1; funext m; simp only [hc, hd]; ring
  have hTcdef : Tcos c = ∑' p : ℕ × ℕ, wgt p * c p.1 * (c (Nat.dist p.1 p.2) - c (p.1 + p.2)) := rfl
  rw [hQ1, hXeq, ← hTcdef, hN]
  have hk : 0 ≤ (128 * π) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hTcos hk, mul_le_mul_of_nonneg_left hTsl hk]

end SharpLSI.FL.Ex.LaneD
