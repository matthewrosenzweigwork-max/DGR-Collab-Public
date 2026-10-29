import SharpSymmetricLSI.Paper.CosineDiagonal

/-!
# Fibres of the torus in one coordinate (Phase 3, lane C)

For a coordinate `p` of `𝕋^ι`, the measurable splitting `𝕋^ι ≅ 𝕋^{ι∖p} × 𝕋^{p}` (Mathlib's
`piEquivPiSubtypeProd`, measure preserving), Fubini along it (`integral_split`), the lift-level
merge `mergeR a b`, and the derivative of `b ↦ Φ (mergeR a b)` (`Dk_fiber`).
-/

open MeasureTheory Set Filter
open scoped Real ContDiff

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι)

/-- The coordinate `p` as a one-point index type. -/
abbrev SpT := {i : ι // ¬i ≠ p}

instance : Unique (SpT p) := ⟨⟨⟨p, not_not.mpr rfl⟩⟩, fun i => Subtype.ext (not_not.mp i.2)⟩

/-- The splitting of `𝕋^ι` along the coordinate `p`. -/
noncomputable abbrev splitT : UnitAddTorus ι ≃ᵐ
    (UnitAddTorus {i // i ≠ p}) × UnitAddTorus (SpT p) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle) (fun i => i ≠ p)

/-- The lift-level merge. -/
def mergeR (a : {i // i ≠ p} → ℝ) (b : SpT p → ℝ) : ι → ℝ :=
  fun i => if h : i ≠ p then a ⟨i, h⟩ else b ⟨i, h⟩

variable {p}

theorem integral_split {G : UnitAddTorus ι → ℝ} (hG : Integrable G volume) :
    ∫ y, G y = ∫ a, ∫ b, G ((splitT p).symm (a, b)) := by
  have hmp := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle)
    (fun i => i ≠ p)).symm
  rw [← hmp.integral_comp' G]
  exact integral_prod _ ((hmp.integrable_comp_emb (splitT p).symm.measurableEmbedding).mpr hG)

theorem integrable_split {G : UnitAddTorus ι → ℝ} (hG : Integrable G volume) :
    Integrable (fun a => ∫ b, G ((splitT p).symm (a, b))) volume := by
  have hmp := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => UnitAddCircle)
    (fun i => i ≠ p)).symm
  exact ((hmp.integrable_comp_emb (splitT p).symm.measurableEmbedding).mpr hG).integral_prod_left

theorem secT_split (a : UnitAddTorus {i // i ≠ p}) (b : UnitAddTorus (SpT p)) :
    secT ((splitT p).symm (a, b)) = mergeR p (secT a) (secT b) := by
  funext i
  by_cases h : i ≠ p
  · simp [secT, mergeR, h, Equiv.piEquivPiSubtypeProd_symm_apply]
  · simp [secT, mergeR, h, Equiv.piEquivPiSubtypeProd_symm_apply]

theorem mergeR_add_single (a : {i // i ≠ p} → ℝ) (b : SpT p → ℝ) (t : ℝ) :
    mergeR p a (b + t • Pi.single default 1) = mergeR p a b + t • Pi.single p 1 := by
  funext i
  by_cases h : i ≠ p
  · simp [mergeR, h, Pi.single_apply]
  · have hi : i = p := not_not.mp h
    subst hi
    simp [mergeR, Pi.single_apply]
    intro h'; exact absurd (Subsingleton.elim _ _) h'

theorem mergeR_add_intVec (a : {i // i ≠ p} → ℝ) (b : SpT p → ℝ) (m : SpT p → ℤ) :
    mergeR p a (b + intVec m) =
      mergeR p a b + intVec (fun i => if h : i ≠ p then 0 else m ⟨i, h⟩) := by
  funext i
  by_cases h : i ≠ p <;> simp [mergeR, h, intVec]

theorem contDiff_mergeR (a : {i // i ≠ p} → ℝ) : ContDiff ℝ ∞ (fun b => mergeR p a b) := by
  refine contDiff_pi.2 fun i => ?_
  by_cases h : i ≠ p
  · simp only [mergeR, dif_pos h]; exact contDiff_const
  · simp only [mergeR, dif_neg h]; exact contDiff_apply ℝ ℝ _

theorem Dk_fiber {Φ : (ι → ℝ) → ℝ} (hΦ : Differentiable ℝ Φ) (a : {i // i ≠ p} → ℝ)
    (b : SpT p → ℝ) :
    Dk (fun b => Φ (mergeR p a b)) default b = Dk Φ p (mergeR p a b) := by
  have hd : DifferentiableAt ℝ (fun b => Φ (mergeR p a b)) b :=
    (hΦ _).comp b ((contDiff_mergeR a).differentiable (by simp) b)
  refine fderiv_apply_of_line hd ?_
  simp_rw [mergeR_add_single]
  have h2 : HasDerivAt (fun t : ℝ => mergeR p a b + t • Pi.single p 1) (Pi.single p 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single p (1 : ℝ))).const_add
      (mergeR p a b)
  exact (hΦ _).hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)

theorem IsPer.fiber {Φ : (ι → ℝ) → ℝ} (hp : IsPer Φ) (a : {i // i ≠ p} → ℝ) :
    IsPer (fun b => Φ (mergeR p a b)) := fun m b => by
  simp only [mergeR_add_intVec, hp _ _]

end SharpLSI
