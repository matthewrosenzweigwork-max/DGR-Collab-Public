import SharpSymmetricLSI.Infra.SmoothWeakGrad

/-!
# Lipschitz functions on the torus from Lipschitz lifts (Phase 3, lane D; R13)

Any two points of `𝕋^ι` have lifts at sup-distance at most their torus distance, so a function
whose periodic lift is `L`-Lipschitz (sup norm) is `L`-Lipschitz on `𝕋^ι`.
-/

open scoped NNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_close_lifts (x y : UnitAddTorus ι) :
    ∃ a b : ι → ℝ, liftT a = x ∧ liftT b = y ∧ ‖a - b‖ ≤ dist x y := by
  set r : ι → ℝ := fun i => secT (y - x) i - round (secT (y - x) i) with hr
  have hcoe : ∀ i, ((r i : ℝ) : UnitAddCircle) = (y - x) i := by
    intro i
    have h := congrFun (liftT_secT (y - x)) i
    simp only [liftT] at h
    rw [hr]; simp only
    rw [AddCircle.coe_sub, ← h]
    have : ((round (secT (y - x) i) : ℝ) : UnitAddCircle) = 0 := by
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round (secT (y - x) i), by simp⟩
    rw [this, sub_zero]
  refine ⟨secT x, secT x + r, liftT_secT x, ?_, ?_⟩
  · rw [liftT_add, liftT_secT]
    funext i
    simp only [Pi.add_apply, liftT, hcoe, Pi.sub_apply, add_sub_cancel]
  · rw [show secT x - (secT x + r) = -r by abel, norm_neg]
    refine (pi_norm_le_iff_of_nonneg dist_nonneg).mpr fun i => ?_
    have h1 : ‖((r i : ℝ) : UnitAddCircle)‖ = |r i| := by
      rw [UnitAddCircle.norm_eq, hr]; simp
    rw [Real.norm_eq_abs, ← h1, hcoe, Pi.sub_apply, ← dist_eq_norm, dist_comm]
    exact dist_le_pi_dist x y i

/-- Lipschitz lifts give Lipschitz functions on `𝕋^ι`. -/
theorem lipschitzWith_of_liftT {f : UnitAddTorus ι → ℝ} {L : ℝ≥0}
    (h : LipschitzWith L (f ∘ liftT)) : LipschitzWith L f := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  obtain ⟨a, b, ha, hb, hab⟩ := exists_close_lifts x y
  have := h.dist_le_mul a b
  rw [Function.comp, Function.comp, ha, hb] at this
  exact this.trans (mul_le_mul_of_nonneg_left (by rwa [dist_eq_norm]) L.2)

end SharpLSI
