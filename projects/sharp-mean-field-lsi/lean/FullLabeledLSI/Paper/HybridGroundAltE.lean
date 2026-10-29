import FullLabeledLSI.Paper.HybridGroundAltD

/-!
# Hybrid inequality (7.17), alternative route, part E: the torus factors

`Xf e B j = Mtensor e (jb B j)` (for `e 0 = 1`), so the torus orthonormality and eigen-IBP of lane 3
(`tensor_orthonormal`, `torus_eigen_ibp`) give
`∫ X_j X_j' = [j = j' on B]` and `∫ ∇X_j · ∇X_j' = [j = j' on B] ∑_{i ∈ B} λ_{j_i}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section torusfac
variable {N d J : ℕ}

/-- The restriction of a multi-index to `B` (as `ℕ`-valued tuple). -/
def jb (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) : Fin N → ℕ :=
  fun i => if i ∈ B then (j i : ℕ) else 0

theorem jb_eq_iff {B : Finset (Fin N)} {j j' : Fin N → Fin (J + 1)} :
    jb B j = jb B j' ↔ ∀ i, i ∈ B → j i = j' i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simp only [jb, hi, if_true] at this
    exact Fin.ext this
  · intro h
    funext i
    by_cases hi : i ∈ B
    · simp [jb, hi, h i hi]
    · simp [jb, hi]

theorem Xf_eq_Mtensor {e : ℕ → Torus d → ℝ} (he0 : e 0 = fun _ => 1) (B : Finset (Fin N))
    (j : Fin N → Fin (J + 1)) : Xf e B j = Mtensor e (jb B j) := by
  funext x
  unfold Xf Mtensor jb
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ B
  · simp [hi]
  · simp [hi, he0]

variable {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e e' : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}

/-- (a1) Orthonormality of the torus factors. -/
theorem integral_Xf_mul (hb : IsRefEigenbasis mu e lam) (hae : ∀ j, e' j =ᵐ[mu] e j)
    (he0 : e' 0 = fun _ => 1) (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) :
    ∫ x, Xf e' B j x * Xf e' B j' x ∂(Measure.pi fun _ : Fin N => mu) =
      if ∀ i, i ∈ B → j i = j' i then 1 else 0 := by
  rw [Xf_eq_Mtensor he0, Xf_eq_Mtensor he0]
  have := Spectral.tensor_orthonormal mu e' (classical_orth hb hae) N (jb B j) (jb B j')
  simp only [jb_eq_iff] at this ⊢
  exact this

/-- (a2) The torus energy of the torus factors. -/
theorem integral_gradPair_Xf (hac : mu ≪ volume) (hca : volume ≪ mu)
    (hb : IsRefEigenbasis mu e lam) (hC1 : ∀ j, C1T (e' j)) (hae : ∀ j, e' j =ᵐ[mu] e j)
    (he0 : e' 0 = fun _ => 1) (hlam0 : lam 0 = 0) (B : Finset (Fin N))
    (j j' : Fin N → Fin (J + 1)) :
    ∫ x, gradPair (Xf e' B j) (Xf e' B j') x ∂(Measure.pi fun _ : Fin N => mu) =
      if ∀ i, i ∈ B → j i = j' i then ∑ i, (if i ∈ B then lam (j i) else 0) else 0 := by
  have hF : C1C (Xf e' B j) := C1C_Xf hC1 B j
  have h := torus_eigen_ibp hac hca hb hC1 hae (jb B j') hF
  rw [← Xf_eq_Mtensor he0] at h
  rw [← h, integral_Xf_mul hb hae he0]
  by_cases hj : ∀ i, i ∈ B → j i = j' i
  · rw [if_pos hj, if_pos hj, mul_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ B
    · simp [jb, hi, hj i hi]
    · simp [jb, hi, hlam0]
  · rw [if_neg hj, if_neg hj, mul_zero]

end torusfac

end SharpLSI.FL.HLA

end
