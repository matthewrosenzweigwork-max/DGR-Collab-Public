import FullLabeledLSI.Paper.Lindeberg8
import FullLabeledLSI.Paper.Hybrid63AltC

/-!
# Proposition 6.3, step R4b (7.21): moments in the label-wise (pair) world

For `Zfp` (the full fluctuation `Z_N` of one mode), `zP …` (`Z^low`), `pP …` (the polynomial) on the pair
space we collect uniform moment bounds from the interface `HybridPolyMoment`, and the bound
`∫ (Zfp - Zlow)² ≤ Kd · |B_N| / N`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ} {J : ℕ}

/-- The full fluctuation of mode `i` (Lean index `i` stands for the manuscript's `i + 1`). -/
def Zfp (e : ℕ → Torus d → ℝ) (N : ℕ) {J : ℕ} (i : Fin J)
    (w : Fin N → Torus d × (Fin J → ℝ)) : ℝ :=
  (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e ((i : ℕ) + 1) (w l).1

theorem pP_cZ_eq (he0 : e 0 = fun _ => 1) {N : ℕ} (T : Finset (Fin N)) (a : ℝ) (i : Fin J)
    (w : Fin N → Torus d × (Fin J → ℝ)) :
    pP e (cZ Finset.univ a i) Finset.univ w = a * ∑ l, e ((i : ℕ) + 1) (w l).1 ∧
    pP e (cZ T a i) Finset.univ w = a * ∑ l ∈ T, e ((i : ℕ) + 1) (w l).1 := by
  have h := fun (S : Finset (Fin N)) => polyF_cZ (lf e (Finset.univ : Finset (Fin N)))
    (fun l s => lf_zero e he0 Finset.univ l s) S a i w
  have h1 : ∀ S : Finset (Fin N), pP e (cZ S a i) Finset.univ w =
      a * ∑ l ∈ S, e ((i : ℕ) + 1) (w l).1 := by
    intro S
    have := h S
    unfold pP
    rw [show (∑ j, cZ S a i j * ∏ l, lf e Finset.univ l (j l) (w l)) =
        polyF (lf e (Finset.univ : Finset (Fin N))) (cZ S a i) w from rfl, this]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [lf_of_mem e (Finset.mem_univ l)]
    simp
  exact ⟨h1 _, h1 _⟩

theorem pP_cZ_univ (he0 : e 0 = fun _ => 1) {N : ℕ} (a : ℝ) (i : Fin J)
    (w : Fin N → Torus d × (Fin J → ℝ)) :
    pP e (cZ Finset.univ a i) Finset.univ w = a * ∑ l, e ((i : ℕ) + 1) (w l).1 :=
  (pP_cZ_eq he0 Finset.univ a i w).1

theorem pP_cZ_sub (he0 : e 0 = fun _ => 1) {N : ℕ} (T : Finset (Fin N)) (a : ℝ) (i : Fin J)
    (w : Fin N → Torus d × (Fin J → ℝ)) :
    pP e (cZ T a i) Finset.univ w = a * ∑ l ∈ T, e ((i : ℕ) + 1) (w l).1 :=
  (pP_cZ_eq he0 T a i w).2

theorem zP_univ_eq (he0 : e 0 = fun _ => 1) {N : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (i : Fin J) (w : Fin N → Torus d × (Fin J → ℝ)) :
    zP e c δ Finset.univ w i = (Real.sqrt (lowCount c δ))⁻¹ *
      ∑ l ∈ (retained c δ)ᶜ, e ((i : ℕ) + 1) (w l).1 := by
  unfold zP
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lf_of_mem e (Finset.mem_univ l)]
  simp

theorem Zfp_eq_pP (he0 : e 0 = fun _ => 1) {N : ℕ} (i : Fin J)
    (w : Fin N → Torus d × (Fin J → ℝ)) :
    Zfp e N i w = pP e (cZ Finset.univ ((N : ℝ) ^ (-(1 / 2 : ℝ))) i) Finset.univ w :=
  (pP_cZ_univ he0 _ i w).symm

/-- `(N^{-1/2})² = N⁻¹`. -/
theorem rpow_neg_half_sq_alt (N : ℕ) : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num [Real.rpow_neg_one]

theorem rpow_neg_half_eq (N : ℕ) : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg N)]

end SharpLSI.FL

end
