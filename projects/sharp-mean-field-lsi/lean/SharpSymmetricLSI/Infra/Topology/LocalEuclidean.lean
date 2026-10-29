import SharpSymmetricLSI.Infra.Topology.Gluing
import SharpSymmetricLSI.Vendor.TauCeti.AlgebraicTopology.Singular.DiskSphere
import Mathlib.Analysis.Convex.Contractible

/-!
# Local homology of a Euclidean space at a convex set

Let `E` be a real inner product space of dimension `n ≥ 1`.  For a bounded convex set `K`
containing `x`, both `E ∖ K` and `E ∖ {x}` deformation retract radially from `x` onto a large
sphere about `x`, so the inclusion `E ∖ K ⟶ E ∖ {x}` is a homotopy equivalence.  Since `E` is
contractible, `Hᵢ₊₁(E, E ∖ K) ≅ H̃ᵢ(E ∖ K)`, hence the restriction
`Hᵢ(E, E ∖ K) ⟶ Hᵢ(E, E ∖ {x})` is an isomorphism for `i ≥ 1`.  The local homology at a point is
`H̃ᵢ₋₁(Sⁿ⁻¹)`, which is `𝔽₂` for `i = n` and `0` otherwise.

Consequently every bounded convex set satisfies `Good n` (`good_of_convex`).
-/

universe u

open CategoryTheory Limits Set Metric Module TauCeti

namespace SharpLSI.Topology

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial homotopy `Φ(t, y) = x + ((1 - t) R / ‖y - x‖ + t) • (y - x)`, from the radial
projection onto the sphere of radius `R` about `x` (`t = 0`) to the identity (`t = 1`). -/
noncomputable def radial (x : E) (R t : ℝ) (y : E) : E :=
  x + ((1 - t) * (R / ‖y - x‖) + t) • (y - x)

lemma radial_one (x : E) (R : ℝ) (y : E) : radial x R 1 y = y := by
  simp [radial]

lemma norm_radial_zero_sub (x : E) {R : ℝ} (hR : 0 ≤ R) {y : E} (hy : y ≠ x) :
    ‖radial x R 0 y - x‖ = R := by
  have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  simp only [radial, sub_zero, one_mul, add_zero, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_div, abs_norm, abs_of_nonneg hR]
  field_simp

lemma continuous_radial (x : E) (R : ℝ) {S : Set E} (hxS : x ∉ S) :
    Continuous fun p : ℝ × S ↦ radial x R p.1 p.2 := by
  have hd : Continuous fun p : ℝ × S ↦ R / ‖(p.2 : E) - x‖ :=
    continuous_const.div (by fun_prop) fun p ↦
      norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ hxS (h ▸ p.2.2))
  unfold radial
  fun_prop

lemma radial_coeff_pos {R t d : ℝ} (hR : 0 < R) (hd : 0 < d) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    0 < (1 - t) * (R / d) + t := by
  rcases ht₀.eq_or_lt with h | h
  · subst h; simp only [sub_zero, one_mul, add_zero]; positivity
  · have := mul_nonneg (sub_nonneg.2 ht₁) (div_pos hR hd).le
    linarith

lemma radial_ne (x : E) {R t : ℝ} (hR : 0 < R) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {y : E}
    (hy : y ≠ x) : radial x R t y ≠ x := by
  intro h
  have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hc := radial_coeff_pos hR hd ht₀ ht₁
  have : ((1 - t) * (R / ‖y - x‖) + t) • (y - x) = 0 := by
    have := congrArg (· - x) h
    simpa [radial] using this
  rcases smul_eq_zero.1 this with h' | h'
  · exact hc.ne' h'
  · exact hy (sub_eq_zero.1 h')

/-- The radial homotopy keeps the complement of a convex set `K ∋ x` inside the ball
`ball x R ⊇ K` away from `K`. -/
lemma radial_not_mem {K : Set E} (hK : Convex ℝ K) {x : E} (hx : x ∈ K) {R : ℝ} (hR : 0 < R)
    (hKR : K ⊆ ball x R) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {y : E} (hy : y ∉ K) :
    radial x R t y ∉ K := by
  intro hz
  have hyx : y ≠ x := fun h ↦ hy (h ▸ hx)
  set d := ‖y - x‖ with hd_def
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  set c := (1 - t) * (R / d) + t with hc_def
  have hc := radial_coeff_pos hR hd ht₀ ht₁
  have hz' : radial x R t y = x + c • (y - x) := rfl
  by_cases hc1 : 1 ≤ c
  · -- `y` lies on the segment from `x` to `radial x R t y`.
    have hmem := hK.add_smul_sub_mem hx hz
      (show c⁻¹ ∈ Icc (0 : ℝ) 1 from ⟨inv_nonneg.2 hc.le, inv_le_one_of_one_le₀ hc1⟩)
    rw [hz', add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc.ne', one_smul,
      add_sub_cancel] at hmem
    exact hy hmem
  · -- `radial x R t y` lies outside the ball of radius `R`.
    push Not at hc1
    have hRd : R / d ≤ c := by
      have h1 : R / d < 1 := by
        by_contra h
        push Not at h
        have : (1 - t) * 1 + t ≤ c := by
          have := mul_le_mul_of_nonneg_left h (sub_nonneg.2 ht₁)
          linarith
        linarith
      have := mul_nonneg ht₀ (sub_nonneg.2 h1.le)
      nlinarith
    have hdist : R ≤ dist (radial x R t y) x := by
      rw [dist_eq_norm, hz', add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      calc R = R / d * d := by field_simp
        _ ≤ c * d := by gcongr
    exact (not_lt.2 hdist) (mem_ball.1 (hKR hz))

/-- The radial homotopy on a set `S ∌ x` which it preserves. -/
noncomputable def radialHomotopy (x : E) (R : ℝ) (S : Set E) (hxS : x ∉ S)
    (hS : ∀ y ∈ S, ∀ t : unitInterval, radial x R t y ∈ S) (f₀ f₁ : C(S, S))
    (h₀ : ∀ y, (f₀ y : E) = radial x R 0 y) (h₁ : ∀ y, f₁ y = y) :
    f₀.Homotopy f₁ where
  toFun p := ⟨radial x R p.1 p.2, hS _ p.2.2 p.1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_radial x R hxS).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left y := Subtype.ext (by simp [h₀])
  map_one_left y := Subtype.ext (by simp [h₁, radial_one])

lemma radial_zero_mem_compl {K : Set E} {x : E} {R : ℝ} (hR : 0 < R) (hKR : K ⊆ ball x R)
    (y : ({x}ᶜ : Set E)) : radial x R 0 y ∈ Kᶜ := fun h ↦
  (not_lt.2 (le_of_eq (by rw [dist_eq_norm, norm_radial_zero_sub x hR.le y.2])))
    (mem_ball.1 (hKR h))

lemma radial_zero_sub_mem_sphere {x : E} (y : ({x}ᶜ : Set E)) :
    radial x 1 0 y - x ∈ sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_radial_zero_sub x zero_le_one y.2]

/-- For a bounded convex set `K ∋ x`, the inclusion `E ∖ K ⟶ E ∖ {x}` is a homotopy
equivalence. -/
noncomputable def complConvexHomotopyEquiv {K : Set E} (hK : Convex ℝ K) {x : E} (hx : x ∈ K)
    {R : ℝ} (hR : 0 < R) (hKR : K ⊆ ball x R) :
    ContinuousMap.HomotopyEquiv (Kᶜ : Set E) ({x}ᶜ : Set E) where
  toFun := ⟨Set.inclusion (compl_subset_compl.2 (singleton_subset_iff.2 hx)),
    continuous_inclusion _⟩
  invFun := ⟨fun y ↦ ⟨radial x R 0 y, radial_zero_mem_compl hR hKR y⟩,
    Continuous.subtype_mk ((continuous_radial x R (S := ({x}ᶜ : Set E)) (by simp)).comp
      (continuous_const.prodMk continuous_id)) (fun y ↦ radial_zero_mem_compl hR hKR y)⟩
  left_inv := ⟨radialHomotopy x R (Kᶜ : Set E) (fun h ↦ h hx)
    (fun y hy t ↦ radial_not_mem hK hx hR hKR t.2.1 t.2.2 hy) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)⟩
  right_inv := ⟨radialHomotopy x R ({x}ᶜ : Set E) (by simp)
    (fun y hy t ↦ radial_ne x hR t.2.1 t.2.2 hy) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)⟩

/-- The complement of a point is homotopy equivalent to the unit sphere. -/
noncomputable def complPointHomotopyEquiv (x : E) :
    ContinuousMap.HomotopyEquiv ({x}ᶜ : Set E) (sphere (0 : E) 1) where
  toFun := ⟨fun y ↦ ⟨radial x 1 0 y - x, radial_zero_sub_mem_sphere y⟩,
    Continuous.subtype_mk (((continuous_radial x 1 (S := ({x}ᶜ : Set E)) (by simp)).comp
      (continuous_const.prodMk continuous_id)).sub continuous_const)
      (fun y ↦ radial_zero_sub_mem_sphere y)⟩
  invFun := ⟨fun z ↦ ⟨x + z, by
      simp only [mem_compl_iff, mem_singleton_iff, add_eq_left]
      exact ne_zero_of_mem_unit_sphere z⟩, by fun_prop⟩
  left_inv := ⟨radialHomotopy x 1 ({x}ᶜ : Set E) (by simp)
    (fun y hy t ↦ radial_ne x one_pos t.2.1 t.2.2 hy) _ _
    (fun y ↦ by show x + (radial x 1 0 y - x) = _; abel) (fun _ ↦ rfl)⟩
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id (sphere (0 : E) 1))
    ext z
    have hz : ‖(z : E)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2
    simp [radial, hz]

section Local

instance contractibleSpace_univ : ContractibleSpace (univ : Set E) :=
  (Homeomorph.Set.univ E).contractibleSpace

local notation "𝔼" => TopCat.of E

instance isIso_reducedSingularHomologyδ_univ (s : Set E) (k : ℕ) :
    IsIso ((@TopPair.ofInclusion (TopCat.of E) s univ (subset_univ s)).reducedSingularHomologyδ R2 k) := by
  have : ContractibleSpace (@TopPair.ofInclusion (TopCat.of E) s univ (subset_univ s)).fst :=
    contractibleSpace_univ (E := E)
  infer_instance

/-- For a bounded convex set `K ∋ x`, restriction `Hₖ₊₁(E, E ∖ K) ⟶ Hₖ₊₁(E, E ∖ {x})` is an
isomorphism. -/
theorem isIso_restr_of_convex {K : Set E} (hK : Convex ℝ K) (hKb : Bornology.IsBounded K)
    {x : E} (hx : x ∈ K) (k : ℕ) :
    IsIso (restr (X := 𝔼) (k + 1) (singleton_subset_iff.2 hx)) := by
  obtain ⟨R, hR, hKR⟩ : ∃ R, 0 < R ∧ K ⊆ ball x R := by
    obtain ⟨R, hR⟩ := hKb.subset_ball x
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  let e := complConvexHomotopyEquiv hK hx hR hKR
  let f := pairMap (X := 𝔼) (subset_univ Kᶜ) (subset_univ ({x}ᶜ : Set E))
    (compl_subset_compl.mpr (singleton_subset_iff.2 hx)) subset_rfl
  have nat := TopPair.reducedSingularHomologyδ_naturality R2 f k
  have hsnd : TopPair.Hom.snd f = TopCat.ofHom e.toFun := by ext; rfl
  have : IsIso ((reducedSingularHomologyFunctor R2 k : TopCat.{u} ⥤ ModuleCat.{u} F2.{u}).map (TopPair.Hom.snd f)) := by
    rw [hsnd]
    exact (e.reducedSingularHomologyIso R2 k).isIso_hom
  have : IsIso (TopPair.singularHomologyMap f R2 (k + 1) ≫
      (TopPair.ofInclusion (subset_univ ({x}ᶜ : Set 𝔼))).reducedSingularHomologyδ R2 k) := by
    rw [← nat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((TopPair.ofInclusion (subset_univ ({x}ᶜ : Set 𝔼))).reducedSingularHomologyδ R2 k)

/-- `Hₖ₊₁(E, E ∖ {x}) ≅ H̃ₖ(Sⁿ⁻¹)`. -/
noncomputable def locHPointIso (x : E) (k : ℕ) :
    locH (X := 𝔼) (k + 1) {x} ≅
      (reducedSingularHomologyFunctor R2 k : TopCat.{u} ⥤ ModuleCat.{u} F2.{u}).obj
        (TopCat.of (sphere (0 : E) 1)) :=
  asIso ((TopPair.ofInclusion (subset_univ ({x}ᶜ : Set 𝔼))).reducedSingularHomologyδ R2 k) ≪≫
    (complPointHomotopyEquiv x).reducedSingularHomologyIso R2 k

lemma isZero_locH_point {n : ℕ} (hn : finrank ℝ E = n + 1) (x : E) {k : ℕ} (hk : k ≠ n) : IsZero (locH (X := 𝔼) (k + 1) {x}) :=
  (TauCeti.isZero_reducedSingularHomologyFunctor_sphere_of_ne (E := E) R2 hn hk).of_iso
    (locHPointIso x k)

/-- `Hₙ₊₁(E, E ∖ {x}) ≅ 𝔽₂` where `dim E = n + 1`. -/
noncomputable def locHPointIsoF2 {n : ℕ} (hn : finrank ℝ E = n + 1) (x : E) : locH (X := 𝔼) (n + 1) {x} ≅ R2 :=
  locHPointIso x n ≪≫ TauCeti.reducedSingularHomologySphereIso (E := E) R2 hn

lemma F2_eq_one_of_ne_zero (a : F2.{u}) (ha : a ≠ 0) : a = 1 := by
  obtain ⟨a⟩ := a
  have : a ≠ 0 := fun h ↦ ha (by rw [h]; rfl)
  have : a = 1 := by revert a; decide
  rw [this]; rfl

/-- Any two nonzero local classes at a point agree. -/
lemma locH_point_eq_of_ne_zero {n : ℕ} (hn : finrank ℝ E = n + 1) (x : E) (α β : locH (X := 𝔼) (n + 1) {x}) (hα : α ≠ 0)
    (hβ : β ≠ 0) : α = β := by
  let e := locHPointIsoF2 hn x
  have hinj : Function.Injective e.hom := ConcreteCategory.injective_of_mono_of_preservesPullback _
  apply hinj
  have h1 : e.hom α ≠ 0 := fun h ↦ hα (hinj (h.trans (map_zero _).symm))
  have h2 : e.hom β ≠ 0 := fun h ↦ hβ (hinj (h.trans (map_zero _).symm))
  exact (F2_eq_one_of_ne_zero _ h1).trans (F2_eq_one_of_ne_zero _ h2).symm

lemma exists_locH_point_ne_zero {n : ℕ} (hn : finrank ℝ E = n + 1) (x : E) : ∃ α : locH (X := 𝔼) (n + 1) {x}, α ≠ 0 := by
  let e := locHPointIsoF2 hn x
  refine ⟨e.inv 1, fun h ↦ ?_⟩
  have := congrArg e.hom h
  rw [← ConcreteCategory.comp_apply, e.inv_hom_id, map_zero] at this
  exact one_ne_zero this

/-- **Bounded convex sets are `Good`.** -/
theorem good_of_convex {n : ℕ} (hn : finrank ℝ E = n + 1) {K : Set E} (hK : Convex ℝ K) (hKb : Bornology.IsBounded K) :
    Good (X := 𝔼) (n + 1) K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact good_empty _
  have hbij (x : E) (hx : x ∈ K) (k : ℕ) :
      Function.Bijective (restr (X := 𝔼) (k + 1) (singleton_subset_iff.2 hx)) := by
    have := isIso_restr_of_convex hK hKb hx k
    exact ConcreteCategory.bijective_of_isIso _
  refine ⟨fun i hi α ↦ ?_, fun α hα ↦ ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    apply (hbij x₀ hx₀ k).1
    rw [map_zero]
    exact (ModuleCat.subsingleton_of_isZero (isZero_locH_point hn x₀ (show k ≠ n by omega))).elim _ _
  · exact (hbij x₀ hx₀ n).1 ((hα x₀ hx₀).trans (map_zero _).symm)
  · obtain ⟨β, hβ⟩ := exists_locH_point_ne_zero hn x₀
    obtain ⟨α, rfl⟩ := (hbij x₀ hx₀ n).2 β
    refine ⟨α, fun x hx h ↦ hβ ?_⟩
    have : α = 0 := (hbij x hx n).1 (h.trans (map_zero _).symm)
    rw [this, map_zero]

end Local

end SharpLSI.Topology
