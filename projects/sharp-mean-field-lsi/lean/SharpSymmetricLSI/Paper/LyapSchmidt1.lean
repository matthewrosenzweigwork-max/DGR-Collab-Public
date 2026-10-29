import Mathlib

/-!
# Section 4.2 (lane s42; R14): a Fredholm alternative

In a Banach space, `A = 1 + R + F` with `‖R‖ < 1` and `F` of finite rank is surjective as soon
as it is injective; it is then a continuous linear equivalence (open mapping). Used for the
invertibility of `I + T` on the complement of its kernel (Lyapunov–Schmidt reduction), with
`T = T_M + (T - T_M)` split by a finite-rank approximation of the kernel.
-/

noncomputable section

namespace SharpLSI

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Fredholm alternative** for `1 + R + F`, `‖R‖ < 1`, `F` of finite rank. -/
theorem surjective_of_injective_one_add {R F : X →L[ℝ] X} (hR : ‖R‖ < 1)
    (hF : FiniteDimensional ℝ (LinearMap.range (F : X →ₗ[ℝ] X)))
    (hinj : Function.Injective ⇑(1 + R + F : X →L[ℝ] X)) :
    Function.Surjective ⇑(1 + R + F : X →L[ℝ] X) := by
  set B : (X →L[ℝ] X)ˣ := Units.oneSub (-R) (by rwa [norm_neg]) with hBdef
  have hB : (B : X →L[ℝ] X) = 1 + R := by
    rw [hBdef, Units.val_oneSub, sub_neg_eq_add]
  set Bi : X →L[ℝ] X := (↑B⁻¹ : X →L[ℝ] X) with hBi
  have hBBi : (B : X →L[ℝ] X) * Bi = 1 := B.mul_inv
  have hBiB : Bi * (B : X →L[ℝ] X) = 1 := B.inv_mul
  set G : X →L[ℝ] X := Bi * F with hG
  have hA : 1 + R + F = (B : X →L[ℝ] X) * (1 + G) := by
    rw [mul_add, mul_one, hG, ← mul_assoc, hBBi, one_mul, hB]
  -- the range of `G` is finite-dimensional
  set V := LinearMap.range (G : X →ₗ[ℝ] X) with hV
  have hVeq : V = (LinearMap.range (F : X →ₗ[ℝ] X)).map (Bi : X →ₗ[ℝ] X) := by
    rw [hV, ← LinearMap.range_comp]
    rfl
  haveI : FiniteDimensional ℝ V := by rw [hVeq]; infer_instance
  -- `1 + G` is injective
  have hinjG : Function.Injective ⇑(1 + G : X →L[ℝ] X) := by
    intro u v huv
    apply hinj
    rw [hA]
    show (B : X →L[ℝ] X) ((1 + G) u) = (B : X →L[ℝ] X) ((1 + G) v)
    rw [huv]
  -- `1 + G` maps `V` into `V`
  have hmaps : ∀ v ∈ V, ((1 + G : X →L[ℝ] X) : X →ₗ[ℝ] X) v ∈ V := by
    intro v hv
    have : ((1 + G : X →L[ℝ] X) : X →ₗ[ℝ] X) v = v + G v := by
      simp [ContinuousLinearMap.add_apply]
    rw [this]
    exact V.add_mem hv ⟨v, rfl⟩
  set L : V →ₗ[ℝ] V := ((1 + G : X →L[ℝ] X) : X →ₗ[ℝ] X).restrict hmaps with hL
  have hLinj : Function.Injective L := by
    intro u v huv
    apply Subtype.ext
    apply hinjG
    have := congrArg Subtype.val huv
    simpa [hL, LinearMap.restrict_apply] using this
  have hLsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinj
  intro f
  set f' := Bi f with hf'
  obtain ⟨⟨v, hv⟩, hv'⟩ := hLsurj ⟨G f', ⟨f', rfl⟩⟩
  have hv'' : v + G v = G f' := by
    have := congrArg Subtype.val hv'
    simpa [hL, LinearMap.restrict_apply, ContinuousLinearMap.add_apply] using this
  refine ⟨f' - v, ?_⟩
  rw [hA]
  have h1 : (1 + G) (f' - v) = f' := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, map_sub]
    rw [← hv'']; abel
  show (B : X →L[ℝ] X) ((1 + G) (f' - v)) = f
  rw [h1, hf', ← ContinuousLinearMap.mul_apply, hBBi, ContinuousLinearMap.one_apply]

/-- The corresponding continuous linear equivalence. -/
theorem isInvertible_one_add {R F : X →L[ℝ] X} (hR : ‖R‖ < 1)
    (hF : FiniteDimensional ℝ (LinearMap.range (F : X →ₗ[ℝ] X)))
    (hinj : Function.Injective ⇑(1 + R + F : X →L[ℝ] X)) :
    (1 + R + F : X →L[ℝ] X).IsInvertible := by
  have hs := surjective_of_injective_one_add hR hF hinj
  refine ⟨ContinuousLinearEquiv.ofBijective (1 + R + F) ?_ ?_, ?_⟩
  · exact LinearMap.ker_eq_bot.mpr hinj
  · exact LinearMap.range_eq_top.mpr hs
  · ext x; rfl

end SharpLSI
