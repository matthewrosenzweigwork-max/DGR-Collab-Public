import DGPS.Topology.LocalHomology

/-!
# Convex compact local class (TOP009)

For a nonempty compact convex set `K` in a chart (an open embedding `e` of a normed space `V`
into a Hausdorff boundaryless `n`-manifold `M`) and `x ∈ e '' K`, the restriction map
`H_i(M, M ∖ e '' K; F2) ⟶ H_i(M, M ∖ {x}; F2)` is an isomorphism for every `i`, and
`H_i(M, M ∖ e '' K; F2) = 0` for `i > n`.  The proof pushes everything into `V` by excision
(TOP004, via `isIso_setPairMap`), and there uses the radial deformation of `V ∖ K` and of
`V ∖ {x₀}` onto a sphere centred at `x₀ ∈ K` enclosing `K`.
-/

open CategoryTheory CategoryTheory.Limits DGPS.Topology.LocalHomology
  DGPS.Topology.MayerVietoris

namespace DGPS.Topology.CompactLocalClass

section Radial

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Radial coefficient interpolating between `R / ‖y - x₀‖` (at `t = 0`) and `1` (at `t = 1`). -/
noncomputable def coeff (x0 : V) (R t : ℝ) (y : V) : ℝ := (1 - t) * (R / ‖y - x0‖) + t

/-- Radial deformation from `y` to the sphere of radius `R` around `x₀`. -/
noncomputable def radial (x0 : V) (R t : ℝ) (y : V) : V := x0 + coeff x0 R t y • (y - x0)

omit [NormedSpace ℝ V] in
lemma coeff_pos {x0 y : V} {R t : ℝ} (hR : 0 < R) (hy : y ≠ x0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < coeff x0 R t y := by
  have hd : 0 < ‖y - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have ha : 0 < R / ‖y - x0‖ := div_pos hR hd
  unfold coeff
  by_cases ht : t = 0
  · simpa [ht] using ha
  · have : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    nlinarith [mul_nonneg (sub_nonneg.2 ht1) ha.le]

lemma radial_ne {x0 y : V} {R t : ℝ} (hR : 0 < R) (hy : y ≠ x0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    radial x0 R t y ≠ x0 := by
  intro h
  have h1 : coeff x0 R t y • (y - x0) = 0 := by
    have : x0 + coeff x0 R t y • (y - x0) = x0 + 0 := by rw [add_zero]; exact h
    exact add_left_cancel this
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact (coeff_pos hR hy ht0 ht1).ne' h2
  · exact hy (sub_eq_zero.1 h2)

lemma radial_notMem {K0 : Set V} (hcv : Convex ℝ K0) {x0 : V} (hx0 : x0 ∈ K0) {R : ℝ}
    (hR : 0 < R) (hball : ∀ z ∈ K0, ‖z - x0‖ < R) {y : V} (hy : y ∉ K0) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : radial x0 R t y ∉ K0 := by
  have hyx : y ≠ x0 := fun h => hy (h ▸ hx0)
  have hd : 0 < ‖y - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  intro hz
  have hs0 : 0 < coeff x0 R t y := coeff_pos hR hyx ht0 ht1
  have hnorm : ‖radial x0 R t y - x0‖ = coeff x0 R t y * ‖y - x0‖ := by
    simp [radial, norm_smul, abs_of_pos hs0]
  have hlt := hball _ hz
  rw [hnorm] at hlt
  have hsd : coeff x0 R t y * ‖y - x0‖ = (1 - t) * R + t * ‖y - x0‖ := by
    unfold coeff; field_simp
  have h1 : 1 ≤ coeff x0 R t y := by
    by_contra h1
    have hd' : ‖y - x0‖ < R := by
      by_contra h
      have h' := not_lt.1 h
      nlinarith [mul_nonneg ht0 (sub_nonneg.2 h')]
    have ha : 1 < R / ‖y - x0‖ := (one_lt_div hd).2 hd'
    have : 1 ≤ coeff x0 R t y := by
      unfold coeff
      nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ha.le)]
    exact h1 this
  apply hy
  have := hcv.add_smul_sub_mem hx0 hz
    (t := (coeff x0 R t y)⁻¹) ⟨inv_nonneg.2 hs0.le, inv_le_one_of_one_le₀ h1⟩
  convert this using 1
  simp [radial, smul_smul, hs0.ne']

lemma continuous_radial {S : Set V} {x0 : V} (hS : ∀ y ∈ S, y ≠ x0) (R : ℝ) :
    Continuous (fun p : unitInterval × S => radial x0 R (p.1 : ℝ) p.2.1) := by
  unfold radial coeff
  have hn : ∀ p : unitInterval × S, ‖p.2.1 - x0‖ ≠ 0 := fun p =>
    norm_ne_zero_iff.2 (sub_ne_zero.2 (hS _ p.2.2))
  have h1 : Continuous (fun p : unitInterval × S => R / ‖p.2.1 - x0‖) :=
    continuous_const.div (by fun_prop) hn
  have h2 : Continuous (fun p : unitInterval × S => (1 - (p.1 : ℝ)) * (R / ‖p.2.1 - x0‖)
      + (p.1 : ℝ)) :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul h1).add
      (continuous_subtype_val.comp continuous_fst)
  exact continuous_const.add (h2.smul (by fun_prop))

end Radial

section Retraction

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma radial_zero_notMem {K0 : Set V} {x0 : V} {R : ℝ} (hR : 0 < R)
    (hball : ∀ z ∈ K0, ‖z - x0‖ < R) {y : V} (hy : y ≠ x0) : radial x0 R 0 y ∉ K0 := by
  intro hz
  have hd : 0 < ‖y - x0‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hs0 : 0 < coeff x0 R 0 y := coeff_pos hR hy le_rfl zero_le_one
  have hnorm : ‖radial x0 R 0 y - x0‖ = coeff x0 R 0 y * ‖y - x0‖ := by
    simp [radial, norm_smul, abs_of_pos hs0]
  have h2 : coeff x0 R 0 y * ‖y - x0‖ = R := by
    unfold coeff; field_simp; ring
  have := hball _ hz
  rw [hnorm, h2] at this
  exact lt_irrefl _ this

/-- The inclusion `V ∖ K ⟶ V ∖ {x₀}` is a quasi-isomorphism on singular chains, for convex `K`
contained in an open ball around `x₀ ∈ K`. -/
theorem quasiIso_incl_compl {K0 : Set V} (hcv : Convex ℝ K0) {x0 : V} (hx0 : x0 ∈ K0) {R : ℝ}
    (hR : 0 < R) (hball : ∀ z ∈ K0, ‖z - x0‖ < R) :
    QuasiIso (singularChains.map
      (inclSub (X := TopCat.of V) (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hx0)))) := by
  have hA : ∀ y ∈ (K0ᶜ : Set V), y ≠ x0 := fun y hy h => hy (h ▸ hx0)
  have hB : ∀ y ∈ (({x0} : Set V)ᶜ : Set V), y ≠ x0 := fun y hy => hy
  let ρ : TopCat.of ↥(({x0} : Set V)ᶜ) ⟶ TopCat.of ↥(K0ᶜ) :=
    TopCat.ofHom ⟨fun y => ⟨radial x0 R 0 y.1, radial_zero_notMem hR hball (hB _ y.2)⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_radial hB R).comp
        ((continuous_const (y := (0 : unitInterval))).prodMk continuous_id)⟩
  refine quasiIso_of_homotopy _ ρ ?_ ?_
  · exact
    { toFun := fun p => ⟨radial x0 R (p.1 : ℝ) p.2.1,
        radial_notMem hcv hx0 hR hball p.2.2 p.1.2.1 p.1.2.2⟩
      continuous_toFun := Continuous.subtype_mk (continuous_radial hA R) _
      map_zero_left := fun x => by
        apply Subtype.ext
        rfl
      map_one_left := fun x => by
        apply Subtype.ext
        change radial x0 R ((1 : unitInterval) : ℝ) x.1 = x.1
        simp [radial, coeff] }
  · exact
    { toFun := fun p => ⟨radial x0 R (p.1 : ℝ) p.2.1,
        radial_ne hR (hB _ p.2.2) p.1.2.1 p.1.2.2⟩
      continuous_toFun := Continuous.subtype_mk (continuous_radial hB R) _
      map_zero_left := fun x => by
        apply Subtype.ext
        rfl
      map_one_left := fun x => by
        apply Subtype.ext
        change radial x0 R ((1 : unitInterval) : ℝ) x.1 = x.1
        simp [radial, coeff] }

end Retraction

section Chart

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- In the normed space `V`, restriction `H_i(V, V ∖ K) ⟶ H_i(V, V ∖ {x₀})` is an isomorphism
for compact convex `K ∋ x₀`. -/
theorem isIso_restrict_space {K0 : Set V} (hc : IsCompact K0) (hcv : Convex ℝ K0) {x0 : V}
    (hx0 : x0 ∈ K0) (i : ℕ) :
    IsIso ((relativeHomology i).map (relPairMap (X := TopCat.of V)
      (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hx0)))) := by
  obtain ⟨r, hr⟩ := hc.isBounded.subset_ball x0
  set R : ℝ := max r 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : ∀ z ∈ K0, ‖z - x0‖ < R := fun z hz => by
    have := hr hz
    rw [Metric.mem_ball, dist_eq_norm] at this
    exact lt_of_lt_of_le this (le_max_left _ _)
  refine isIso_relativeHomology_of_quasiIso _ ?_ ?_ i
  · exact quasiIso_incl_compl hcv hx0 hR hball
  · exact quasiIso_of_isIso (𝟙 _)

end Chart

end DGPS.Topology.CompactLocalClass

namespace DGPS.Topology

open DGPS.Topology.LocalHomology DGPS.Topology.MayerVietoris

/-- **Convex compact local class.**  Let `M` be a Hausdorff boundaryless `n`-manifold (`n > 0`)
and `e : V ⟶ M` an open embedding of a real normed space (a Euclidean chart).  For a nonempty
compact convex `K0 ⊆ V` and `x ∈ e '' K0`: restriction `H_i(M, M ∖ e '' K0; F2) ⟶
H_i(M, M ∖ {x}; F2)` is an isomorphism in every degree `i`; the groups `H_i(M, M ∖ e '' K0; F2)`
vanish for `i > n`; and a local class `s ∈ H_n(M, M ∖ {x})` has a unique class over `e '' K0`
restricting to it. -/
theorem convex_compact_local_class {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type} [TopologicalSpace H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [I.Boundaryless] (n : ℕ) (hn : 0 < n)
    (hE : Module.finrank ℝ E = n)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : TopCat.of V ⟶ TopCat.of M) (he : Topology.IsOpenEmbedding e.hom)
    (K0 : Set V) (hc : IsCompact K0) (hcv : Convex ℝ K0) (hne : K0.Nonempty) :
    (∀ x (hx : x ∈ e.hom '' K0) (i : ℕ),
      IsIso (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) i)) ∧
    (∀ i, n < i → IsZero (localHomology (X := TopCat.of M) (e.hom '' K0) i)) ∧
    (∀ x (hx : x ∈ e.hom '' K0) (s : localHomology (X := TopCat.of M) {x} n),
      ∃! c : localHomology (X := TopCat.of M) (e.hom '' K0) n,
        (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n).hom c = s) := by
  have hT1 : T1Space M := inferInstance
  have hKc : IsClosed (e.hom '' K0) := (hc.image e.hom.continuous).isClosed
  have hpre : e.hom ⁻¹' (e.hom '' K0) = K0 := he.injective.preimage_image K0
  have hiso : ∀ x (hx : x ∈ e.hom '' K0) (i : ℕ),
      IsIso (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) i) := by
    intro x hx i
    obtain ⟨x0, hx0, hxe⟩ := id hx
    subst hxe
    have h1 : IsIso ((relativeHomology i).map (setPairMap e K0 (e.hom '' K0) hpre.le)) :=
      isIso_setPairMap e he K0 _ hpre (by
        rw [hKc.closure_eq]; rintro _ ⟨z, _, rfl⟩; exact ⟨z, rfl⟩) i
    have h2 := isIso_pointPairMap e he x0 i
    have h3 := CompactLocalClass.isIso_restrict_space hc hcv hx0 i
    have hsq : relPairMap (X := TopCat.of V)
          (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hx0)) ≫
        pointPairMap e he.injective x0 =
        setPairMap e K0 (e.hom '' K0) hpre.le ≫
          relPairMap (X := TopCat.of M)
            (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hx)) := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext y; rfl
      · ext y; rfl
    have h4 : IsIso ((relativeHomology i).map (setPairMap e K0 (e.hom '' K0) hpre.le) ≫
        (relativeHomology i).map (relPairMap (X := TopCat.of M)
          (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hx)))) := by
      rw [← Functor.map_comp, ← hsq, Functor.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_left ((relativeHomology i).map (setPairMap e K0 (e.hom '' K0) hpre.le))
      (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) i)
  refine ⟨hiso, ?_, ?_⟩
  · intro i hi
    obtain ⟨x0, hx0⟩ := hne
    have hx : e.hom x0 ∈ e.hom '' K0 := ⟨x0, hx0, rfl⟩
    have := hiso _ hx i
    exact IsZero.of_iso ((local_homology_in_a_chart I n hn hE (e.hom x0)).2.1 i hi)
      (asIso (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) i))
  · intro x hx s
    have := hiso x hx n
    exact (ConcreteCategory.bijective_of_isIso
      (localRestrict (X := TopCat.of M) (Set.singleton_subset_iff.2 hx) n)).existsUnique s

end DGPS.Topology
