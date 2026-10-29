import DGPS.Topology.SmallChains
import DGPS.Topology.SubdivisionSingular
import DGPS.Topology.RelativeHomology

open CategoryTheory Simplicial

namespace DGPS.Topology.Excision

section Bridge

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp Convexity

/-- The weights map of the standard simplex, as a function to `Fin (n+1) → ℝ`. -/
noncomputable def wmap (n : ℕ) (t : Simp n) : Fin (n + 1) → ℝ := fun i => t.weights i

lemma wmap_injective (n : ℕ) : Function.Injective (wmap n) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).injective

lemma list_sum_eq_range {α M : Type*} [AddCommMonoid M] (l : List α) (a : α) (f : α → M) :
    (l.map f).sum = ∑ m ∈ Finset.range l.length, f (l.getD m a) := by
  induction l with
  | nil => simp
  | cons b t ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', ih]
    simp [add_comm]

lemma wmap_bary {n : ℕ} (l : List (Simp n)) (hl : l ≠ []) :
    SmallChains.centroid (l.map (wmap n)) = wmap n (bary l) := by
  ext i
  have hL : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.mpr hl
  simp only [wmap, bary, hl, dite_false, weights_iConvexComb', SmallChains.centroid,
    List.length_map, Pi.smul_apply, smul_eq_mul]
  rw [StdSimplex.weights_subBarycenter, ← Finsupp.sum_finsetSum_index (by simp)
    (by intros; simp [add_smul])]
  rw [list_sum_eq_range l p0 (wmap n)]
  rw [Finset.sum_apply, Finsupp.finsetSum_apply, Finset.mul_sum, Finset.card_range]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finsupp.sum_single_index (by simp)]
  have hm' := Finset.mem_range.1 hm
  simp [wmap]

lemma realize_affine {n : ℕ} (l : List (Simp n)) (k : ℕ) : IsAffineMap ℝ (realize l k) where
  map_sConvexComb s := by
    have h := iConvexComb_assoc s id (fun j : Fin (k + 1) => l.getD j p0)
    rw [iConvexComb_id] at h
    unfold realize
    rw [← h]
    rfl

lemma vert_map_realize {n : ℕ} (l : List (Simp n)) (hl : l.length = n + 1) :
    (vert n).map (realize l n) = l := by
  refine List.ext_getElem (by simp [vert_length, hl]) fun j h1 h2 => ?_
  rw [List.getElem_map]
  simp only [vert, List.getElem_ofFn, realize]
  rw [iConvexComb_single]
  exact SubdivisionSingular.getD_of_lt l p0 h2

lemma eq_of_support {M : Type*} [AddCommGroup M] [Module F2 M] {P : Type*}
    (f g : LChain P →ₗ[F2] M) (y : LChain P)
    (h : ∀ l ∈ y.support, f (single l 1) = g (single l 1)) : f y = g y := by
  have hy : y = ∑ l ∈ y.support, y l • single l (1 : F2) := by
    simp_rw [Finsupp.smul_single_one]; exact (Finsupp.sum_single y).symm
  rw [hy, map_sum, map_sum]
  exact Finset.sum_congr rfl fun l hl => by rw [map_smul, map_smul, h l hl]

lemma mem_of_support {M : Type*} [AddCommGroup M] [Module F2 M] {P : Type*}
    (f : LChain P →ₗ[F2] M) (N : Submodule F2 M) (y : LChain P)
    (h : ∀ l ∈ y.support, f (single l 1) ∈ N) : f y ∈ N := by
  have hy : y = ∑ l ∈ y.support, y l • single l (1 : F2) := by
    simp_rw [Finsupp.smul_single_one]; exact (Finsupp.sum_single y).symm
  rw [hy, map_sum]
  exact Submodule.sum_mem _ fun l hl => by rw [map_smul]; exact Submodule.smul_mem _ _ (h l (by simpa using hl))

lemma sdHom_psi_single {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (l : List (Simp n))
    (hl : l.length = n + 1) :
    (sdHom X n).hom (psi σ n (single l 1)) = psi σ n (sd bary (single l 1)) := by
  simp only [psi_single, hl, ↓reduceIte]
  rw [sdHom_gen, sd_single, one_smul]
  have h : simpEquiv X n (sim σ l n) = σ.comp ⟨realize l n, continuous_realize l n⟩ := by
    simp [sim]
  have hs := mapChain_sdList bary bary
    (⇑(⟨realize l n, continuous_realize l n⟩ : C(Simp n, Simp n)))
    (fun l' hl' => bary_map _ (realize_affine l n) l' hl') (vert n)
  have hv : (vert n).map
      (⇑(⟨realize l n, continuous_realize l n⟩ : C(Simp n, Simp n))) = l :=
    vert_map_realize l hl
  rw [h, psi_comp σ ⟨realize l n, continuous_realize l n⟩ (realize_affine l n), hs, hv]

lemma sdHom_psi {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (y : LChain (Simp n))
    (hy : ∀ l ∈ y.support, l.length = n + 1) :
    (sdHom X n).hom (psi σ n y) = psi σ n (sd bary y) :=
  eq_of_support ((sdHom X n).hom ∘ₗ psi σ n) (psi σ n ∘ₗ sd bary) y
    fun l hl => sdHom_psi_single σ l (hy l hl)

lemma mapChain_sd_wmap {n : ℕ} (y : LChain (Simp n)) :
    mapChain (wmap n) (sd bary y) = sd SmallChains.centroid (mapChain (wmap n) y) := by
  have : (mapChain (wmap n) ∘ₗ sd bary : LChain (Simp n) →ₗ[F2] _) =
      sd SmallChains.centroid ∘ₗ mapChain (wmap n) := by
    refine Finsupp.lhom_ext fun l c => ?_
    rw [← Finsupp.smul_single_one l c]
    simp only [map_smul, LinearMap.comp_apply, sd_single, mapChain_single]
    rw [mapChain_sdList bary SmallChains.centroid (wmap n)
      (fun l' hl' => wmap_bary l' hl') l]
  exact congrArg (fun g => g y) this

lemma mapChain_iter_wmap {n : ℕ} (m : ℕ) (y : LChain (Simp n)) :
    mapChain (wmap n) ((sd bary)^[m] y) =
      (sd SmallChains.centroid)^[m] (mapChain (wmap n) y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', mapChain_sd_wmap, ih]

lemma map_wmap_vert (n : ℕ) : (vert n).map (wmap n) = SmallChains.stdVertices n := by
  classical
  simp only [vert, SmallChains.stdVertices, List.map_ofFn]
  congr 1
  funext i
  ext j
  simp [wmap, Pi.single_apply, Finsupp.single_apply, eq_comm]

lemma map_mem_support_iter {n : ℕ} (m : ℕ) {l : List (Simp n)}
    (hl : l ∈ ((sd bary)^[m] (single (vert n) (1 : F2))).support) :
    l.map (wmap n) ∈ ((sd SmallChains.centroid)^[m]
      (single (SmallChains.stdVertices n) (1 : F2))).support := by
  have h := mapChain_iter_wmap m (single (vert n) (1 : F2))
  rw [mapChain_single, map_wmap_vert] at h
  rw [← h]
  have hinj : Function.Injective (List.map (wmap n)) :=
    List.map_injective_iff.mpr (wmap_injective n)
  have : (mapChain (wmap n) ((sd bary)^[m] (single (vert n) (1 : F2)))).support =
      ((sd bary)^[m] (single (vert n) (1 : F2))).support.image (List.map (wmap n)) := by
    simp only [mapChain, Finsupp.lmapDomain_apply]
    exact Finsupp.mapDomain_support_of_injective hinj _
  rw [this]
  exact Finset.mem_image_of_mem _ hl

lemma length_of_mem_support_iter {n : ℕ} (m : ℕ) {l : List (Simp n)}
    (hl : l ∈ ((sd bary)^[m] (single (vert n) (1 : F2))).support) : l.length = n + 1 := by
  have := (SmallChains.mesh_sd_iterate n (SmallChains.stdVertices n) 1
    (SmallChains.stdVertices_length n) (SmallChains.stdVertices_dist n) m _
    (map_mem_support_iter m hl)).1
  simpa using this

lemma sdHom_iter_psi {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (m : ℕ) :
    ((sdHom X n).hom)^[m] (psi σ n (single (vert n) 1)) =
      psi σ n ((sd bary)^[m] (single (vert n) 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      sdHom_psi σ _ (fun l hl => length_of_mem_support_iter m hl)]

lemma wmap_realize {n : ℕ} (l : List (Simp n)) (t : Simp n) :
    wmap n (realize l n t) = ∑ j : Fin (n + 1), t.weights j • wmap n (l.getD j p0) := by
  ext i
  simp only [wmap, realize, weights_iConvexComb', Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  rw [Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply]
  simp

lemma wmap_realize_mem_hull {n : ℕ} (l : List (Simp n)) (hl : l.length = n + 1) (t : Simp n) :
    wmap n (realize l n t) ∈ convexHull ℝ {v | v ∈ l.map (wmap n)} := by
  rw [wmap_realize]
  refine (convex_convexHull ℝ _).sum_mem (fun j _ => t.nonneg j) ?_ fun j _ => ?_
  · simp
  · apply subset_convexHull
    have hj : (j : ℕ) < l.length := by omega
    rw [SubdivisionSingular.getD_of_lt l p0 hj]
    exact List.mem_map.mpr ⟨l[(j : ℕ)], List.getElem_mem hj, rfl⟩

end Bridge

section Small

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

lemma isSmall_sim {X : TopCat.{0}} {n : ℕ} (U : Set (Set X)) (σ : C(Simp n, X)) (l : List (Simp n))
    (k : ℕ) {A : Set X} (hA : A ∈ U) (hσ : ∀ t, σ (realize l k t) ∈ A) :
    SmallChains.IsSmall U (sim σ l k) := by
  refine ⟨A, hA, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hσ t

lemma psi_mem_smallSub {X : TopCat.{0}} {n : ℕ} (U : Set (Set X)) (σ : C(Simp n, X)) {A : Set X}
    (hA : A ∈ U) (hσ : Set.range σ ⊆ A) (k : ℕ) (y : LChain (Simp n)) :
    psi σ k y ∈ SmallChains.smallSub X U k := by
  refine mem_of_support (psi σ k) _ y fun l _ => ?_
  rw [psi_single]
  split_ifs
  · exact SmallChains.gen_mem_smallSub (isSmall_sim U σ l k hA fun t => hσ ⟨_, rfl⟩)
  · exact zero_mem _

/-- Subdivision data for any open cover: barycentric subdivision `sdNat` with its homotopy to the
identity, preserving small chains, and eventually making every simplex small by the Lebesgue
number lemma. -/
noncomputable def subdivisionData {X : TopCat.{0}} (U : Set (Set X)) (hU : ∀ A ∈ U, IsOpen A)
    (hcov : ⋃₀ U = Set.univ) : SmallChains.SubdivisionData X U where
  S := sdChainMap X
  T := sdHomotopy X
  S_small n x hx := by
    obtain ⟨A, hA, hsub⟩ := hx
    show (sdHom X n).hom (SubdivisionSingular.gen x) ∈ _
    rw [sdHom_gen]
    exact psi_mem_smallSub U _ hA hsub n _
  T_small n m x hx := by
    obtain ⟨A, hA, hsub⟩ := hx
    show (hhom X n m).hom (SubdivisionSingular.gen x) ∈ _
    by_cases h : n + 1 = m
    · subst h
      rw [hhom_succ, hoHom_gen]
      exact psi_mem_smallSub U _ hA hsub _ _
    · simp [hhom, h]
  iter_small n x := by
    obtain ⟨m, hm⟩ := SmallChains.lebesgue_subdivision n (simpEquiv X n x) U hU hcov
    refine ⟨m, ?_⟩
    show ((sdHom X n).hom)^[m] (SubdivisionSingular.gen x) ∈ _
    rw [← psi_vert n x, sdHom_iter_psi]
    refine mem_of_support (psi (simpEquiv X n x) n) _ _ fun l hl => ?_
    obtain ⟨A, hA, hAσ⟩ := hm _ (map_mem_support_iter m hl)
    have hlen := length_of_mem_support_iter m hl
    rw [psi_single]
    simp only [hlen, ↓reduceIte]
    refine SmallChains.gen_mem_smallSub (isSmall_sim U (simpEquiv X n x) l n hA fun t => ?_)
    exact hAσ _ (wmap_realize_mem_hull l hlen t)

end Small

section Closure

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

lemma hom_mem_smallSub {X : TopCat.{0}} {i j : ℕ} (W W' : Set (Set X)) (f : SC X i ⟶ SC X j)
    (h : ∀ x : (TopCat.toSSet.obj X) _⦋i⦌, SmallChains.IsSmall W x →
      f.hom (SubdivisionSingular.gen x) ∈ SmallChains.smallSub X W' j)
    (z : SC X i) (hz : z ∈ SmallChains.smallSub X W i) :
    f.hom z ∈ SmallChains.smallSub X W' j := by
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, hσ, rfl⟩ := hx; exact h σ hσ
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

lemma sdHom_mem {X : TopCat.{0}} (W : Set (Set X)) {k : ℕ} (z : SC X k)
    (hz : z ∈ SmallChains.smallSub X W k) : (sdHom X k).hom z ∈ SmallChains.smallSub X W k :=
  hom_mem_smallSub W W _ (fun x hx => by
    obtain ⟨A, hA, hsub⟩ := hx
    rw [sdHom_gen]
    exact psi_mem_smallSub W _ hA hsub k _) z hz

lemma hoHom_mem {X : TopCat.{0}} (W : Set (Set X)) {k : ℕ} (z : SC X k)
    (hz : z ∈ SmallChains.smallSub X W k) :
    (hoHom X k).hom z ∈ SmallChains.smallSub X W (k + 1) :=
  hom_mem_smallSub W W _ (fun x hx => by
    obtain ⟨A, hA, hsub⟩ := hx
    rw [hoHom_gen]
    exact psi_mem_smallSub W _ hA hsub _ _) z hz

lemma sdHom_iter_mem {X : TopCat.{0}} (W : Set (Set X)) {k : ℕ} (i : ℕ) (z : SC X k)
    (hz : z ∈ SmallChains.smallSub X W k) :
    (sdHom X k).hom^[i] z ∈ SmallChains.smallSub X W k := by
  induction i with
  | zero => exact hz
  | succ i ih => rw [Function.iterate_succ_apply']; exact sdHom_mem W _ ih

lemma d_iter_comm {X : TopCat.{0}} (k i : ℕ) (z : SC X (k + 1)) :
    ((singularChains.obj X).d (k + 1) k).hom ((sdHom X (k + 1)).hom^[i] z) =
      (sdHom X k).hom^[i] (((singularChains.obj X).d (k + 1) k).hom z) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    have h := congr($(sdHom_comm X k) ((⇑(sdHom X (k + 1)).hom)^[i] z))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

lemma dT_zero {X : TopCat.{0}} (w : SC X 0) :
    ((singularChains.obj X).d 1 0).hom ((hoHom X 0).hom w) = (sdHom X 0).hom w + w := by
  have h := congr($(sd_eq_zero X) w)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [h, add_assoc, add_self_eq_zero', add_zero]

lemma dT_succ {X : TopCat.{0}} (k : ℕ) (w : SC X (k + 1)) :
    ((singularChains.obj X).d (k + 1 + 1) (k + 1)).hom ((hoHom X (k + 1)).hom w) =
      (sdHom X (k + 1)).hom w + w + (hoHom X k).hom (((singularChains.obj X).d (k + 1) k).hom w) := by
  have h := congr($(sd_eq_succ X k) w)
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at h
  rw [h]
  generalize ((singularChains.obj X).d (k + 1 + 1) (k + 1)).hom ((hoHom X (k + 1)).hom w) = a
  generalize (hoHom X k).hom (((singularChains.obj X).d (k + 1) k).hom w) = b
  have e : b + a + w + w + b = a + (b + b) + (w + w) := by abel
  rw [e, add_self_eq_zero', add_self_eq_zero', add_zero, add_zero]

lemma tele {M : Type*} [AddCommGroup M] [Module F2 M] (a : ℕ → M) (N : ℕ) :
    ∑ i ∈ Finset.range N, (a (i + 1) + a i) = a N + a 0 := by
  induction N with
  | zero => simp [add_self_eq_zero']
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have e : a N + a 0 + (a (N + 1) + a N) = (a N + a N) + a (N + 1) + a 0 := by abel
    rw [e, add_self_eq_zero', zero_add]

end Closure

section Depth

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

/-- The least number of subdivisions making the simplex `x` small for the cover `V`. -/
noncomputable def mdepth {X : TopCat.{0}} (V : Set (Set X)) {k : ℕ}
    (x : (TopCat.toSSet.obj X) _⦋k⦌) : ℕ :=
  sInf {m | (sdHom X k).hom^[m] (SubdivisionSingular.gen x) ∈ SmallChains.smallSub X V k}

lemma mdepth_spec {X : TopCat.{0}} (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A)
    (hcov : ⋃₀ V = Set.univ) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    (sdHom X k).hom^[mdepth V x] (SubdivisionSingular.gen x) ∈ SmallChains.smallSub X V k :=
  Nat.sInf_mem (s := {m | (sdHom X k).hom^[m] (SubdivisionSingular.gen x) ∈
      SmallChains.smallSub X V k}) (((subdivisionData V hV hcov).iter_small k x))

lemma mdepth_iter_mem {X : TopCat.{0}} (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A)
    (hcov : ⋃₀ V = Set.univ) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) (i : ℕ)
    (hi : mdepth V x ≤ i) :
    (sdHom X k).hom^[i] (SubdivisionSingular.gen x) ∈ SmallChains.smallSub X V k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact sdHom_iter_mem V t _ (mdepth_spec V hV hcov x)

lemma mdepth_eq_zero {X : TopCat.{0}} (V : Set (Set X)) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌)
    (h : SmallChains.IsSmall V x) : mdepth V x = 0 :=
  Nat.sInf_eq_zero.2 (Or.inl (SmallChains.gen_mem_smallSub h))

/-- Face-closed depth: at least the depth of the simplex and of all its faces. -/
noncomputable def depth {X : TopCat.{0}} (V : Set (Set X)) (k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) : ℕ :=
  match k, x with
  | 0, x => mdepth V x
  | k + 1, x => max (mdepth V x)
      (Finset.univ.sup fun j : Fin (k + 2) => depth V k ((TopCat.toSSet.obj X).δ j x))

lemma mdepth_le_depth {X : TopCat.{0}} (V : Set (Set X)) (k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) : mdepth V x ≤ depth V k x := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

lemma depth_face_le {X : TopCat.{0}} (V : Set (Set X)) (k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋k + 1⦌) (j : Fin (k + 2)) :
    depth V k ((TopCat.toSSet.obj X).δ j x) ≤ depth V (k + 1) x :=
  le_max_of_le_right (Finset.le_sup (f := fun j : Fin (k + 2) =>
    depth V k ((TopCat.toSSet.obj X).δ j x)) (Finset.mem_univ j))

lemma depth_eq_zero {X : TopCat.{0}} (V : Set (Set X)) (k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) (h : SmallChains.IsSmall V x) : depth V k x = 0 := by
  induction k with
  | zero => exact mdepth_eq_zero V x h
  | succ k ih =>
    exact Nat.le_zero.1 (max_le (mdepth_eq_zero V x h).le
      (Finset.sup_le fun j _ => (ih _ (SmallChains.isSmall_δ h j)).le))

end Depth

section Hatcher

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

variable {X : TopCat.{0}}

/-- The correcting homotopy component `D_k`: `D x = ∑_{i < M x} T S^i x`. -/
noncomputable def Dk (V : Set (Set X)) (k : ℕ) : SC X k ⟶ SC X (k + 1) :=
  mkHom fun x => ∑ i ∈ Finset.range (depth V k x),
    (hoHom X k).hom ((sdHom X k).hom^[i] (gen x))

lemma Dk_gen (V : Set (Set X)) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    (Dk V k).hom (gen x) = ∑ i ∈ Finset.range (depth V k x),
      (hoHom X k).hom ((sdHom X k).hom^[i] (gen x)) :=
  mkHom_gen _ x

lemma Dk_mem (V W : Set (Set X)) {k : ℕ} (z : SC X k) (hz : z ∈ SmallChains.smallSub X W k) :
    (Dk V k).hom z ∈ SmallChains.smallSub X W (k + 1) :=
  hom_mem_smallSub W W _ (fun x hx => by
    rw [Dk_gen]
    exact sum_mem fun i _ =>
      hoHom_mem W _ (sdHom_iter_mem W i _ (SmallChains.gen_mem_smallSub hx))) z hz

lemma Dk_zero (V : Set (Set X)) {k : ℕ} (z : SC X k) (hz : z ∈ SmallChains.smallSub X V k) :
    (Dk V k).hom z = 0 := by
  have : SmallChains.smallSub X V k ≤ LinearMap.ker (Dk V k).hom := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨σ, hσ, rfl⟩
    show (Dk V k).hom (gen σ) = 0
    rw [Dk_gen, depth_eq_zero V k σ hσ]
    simp
  exact this hz

/-- The homotopy family, supported on `i + 1 = j`. -/
noncomputable def Dhom (V : Set (Set X)) (i j : ℕ) : SC X i ⟶ SC X j :=
  if h : i + 1 = j then Dk V i ≫ eqToHom (by rw [h]) else 0

lemma Dhom_succ (V : Set (Set X)) (i : ℕ) : Dhom V i (i + 1) = Dk V i := by
  simp [Dhom]

lemma Dhom_ne (V : Set (Set X)) {i j : ℕ} (h : ¬ i + 1 = j) : Dhom V i j = 0 := by
  simp [Dhom, h]

lemma Dhom_mem (V W : Set (Set X)) (i j : ℕ) (z : SC X i)
    (hz : z ∈ SmallChains.smallSub X W i) : (Dhom V i j).hom z ∈ SmallChains.smallSub X W j := by
  by_cases h : i + 1 = j
  · subst h
    rw [Dhom_succ]
    exact Dk_mem V W z hz
  · rw [Dhom_ne V h]
    simp

lemma Dhom_zero (V : Set (Set X)) (i j : ℕ) (z : SC X i)
    (hz : z ∈ SmallChains.smallSub X V i) : (Dhom V i j).hom z = 0 := by
  by_cases h : i + 1 = j
  · subst h
    rw [Dhom_succ]
    exact Dk_zero V z hz
  · rw [Dhom_ne V h]
    simp

/-- The chain map `ρ' = 1 + ∂D + D∂`, whose image lies in the small chains. -/
noncomputable def rho (V : Set (Set X)) : singularChains.obj X ⟶ singularChains.obj X :=
  Homotopy.nullHomotopicMap (Dhom V) + 𝟙 _

/-- The homotopy `ρ' ≃ 1`. -/
noncomputable def rhoHomotopy (V : Set (Set X)) :
    Homotopy (rho V) (𝟙 (singularChains.obj X)) where
  hom := Dhom V
  zero i j hij := by
    have h : ¬ (i + 1 = j) := fun h => hij h
    exact Dhom_ne V h
  comm i := by
    rw [rho, HomologicalComplex.add_f_apply]
    rfl

lemma rho_eq_general (V : Set (Set X)) (n : ℕ) (z : SC X n) :
    ((rho V).f n).hom z =
      (Dhom V ((ComplexShape.down ℕ).next n) n).hom (((singularChains.obj X).dFrom n).hom z) +
      ((singularChains.obj X).dTo n).hom ((Dhom V n ((ComplexShape.down ℕ).prev n)).hom z) + z := by
  have h := congr($((rhoHomotopy V).comm n) z)
  simp only [dNext_eq_dFrom_fromNext, prevD_eq_toPrev_dTo, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at h
  exact h.symm

lemma rho_zero (V : Set (Set X)) (z : SC X 0) :
    ((rho V).f 0).hom z = ((singularChains.obj X).d 1 0).hom ((Dk V 0).hom z) + z := by
  have h : (rho V).f 0 = Dk V 0 ≫ (singularChains.obj X).d 1 0 + 𝟙 _ := by
    rw [rho, HomologicalComplex.add_f_apply, ChainComplex.nullHomotopicMap_f_zero, Dhom_succ]
    rfl
  rw [h]
  simp

lemma rho_succ (V : Set (Set X)) (k : ℕ) (z : SC X (k + 1)) :
    ((rho V).f (k + 1)).hom z = (Dk V k).hom (((singularChains.obj X).d (k + 1) k).hom z) +
      ((singularChains.obj X).d (k + 1 + 1) (k + 1)).hom ((Dk V (k + 1)).hom z) + z := by
  have h : (rho V).f (k + 1) = (singularChains.obj X).d (k + 1) k ≫ Dk V k +
      Dk V (k + 1) ≫ (singularChains.obj X).d (k + 1 + 1) (k + 1) + 𝟙 _ := by
    rw [rho, HomologicalComplex.add_f_apply, ChainComplex.nullHomotopicMap_f_succ, Dhom_succ,
      Dhom_succ]
    rfl
  rw [h]
  simp

end Hatcher

section HatcherGen

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

variable {X : TopCat.{0}}

lemma iter_sum {M : Type*} [AddCommGroup M] [Module F2 M] (f : M →ₗ[F2] M) {ι : Type*}
    (s : Finset ι) (g : ι → M) (i : ℕ) : (⇑f)^[i] (∑ j ∈ s, g j) = ∑ j ∈ s, (⇑f)^[i] (g j) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.iterate_succ_apply']

lemma rho_gen_zero (V : Set (Set X)) (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    ((rho V).f 0).hom (gen x) = (sdHom X 0).hom^[depth V 0 x] (gen x) := by
  rw [rho_zero, Dk_gen, map_sum]
  have : ∀ i, ((singularChains.obj X).d 1 0).hom ((hoHom X 0).hom ((sdHom X 0).hom^[i] (gen x))) =
      (sdHom X 0).hom^[i + 1] (gen x) + (sdHom X 0).hom^[i] (gen x) := by
    intro i
    rw [dT_zero, Function.iterate_succ_apply']
  simp only [this]
  rw [tele (fun i => (sdHom X 0).hom^[i] (gen x))]
  simp only [Function.iterate_zero, id_eq]
  rw [add_assoc, add_self_eq_zero', add_zero]

/-- Explicit value of `ρ'` on a higher generator. -/
lemma rho_gen_succ (V : Set (Set X)) (k : ℕ) (x : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    ((rho V).f (k + 1)).hom (gen x) = (sdHom X (k + 1)).hom^[depth V (k + 1) x] (gen x) +
      ∑ j : Fin (k + 2), ∑ i ∈ Finset.Ico (depth V k ((TopCat.toSSet.obj X).δ j x))
        (depth V (k + 1) x),
        (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))) := by
  set M := depth V (k + 1) x with hM
  rw [rho_succ, d_gen, map_sum, Dk_gen, map_sum]
  simp only [Dk_gen]
  have h1 : ∀ i, ((singularChains.obj X).d (k + 1 + 1) (k + 1)).hom
      ((hoHom X (k + 1)).hom ((sdHom X (k + 1)).hom^[i] (gen x))) =
      ((sdHom X (k + 1)).hom^[i + 1] (gen x) + (sdHom X (k + 1)).hom^[i] (gen x)) +
        ∑ j : Fin (k + 2), (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))) := by
    intro i
    rw [dT_succ, d_iter_comm, d_gen, iter_sum, map_sum, Function.iterate_succ_apply']
  simp only [h1]
  rw [Finset.sum_add_distrib, tele (fun i => (sdHom X (k + 1)).hom^[i] (gen x))]
  simp only [Function.iterate_zero, id_eq]
  rw [Finset.sum_comm]
  have h2 : ∀ j : Fin (k + 2), ∑ i ∈ Finset.range (depth V k ((TopCat.toSSet.obj X).δ j x)),
      (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))) =
      ∑ i ∈ Finset.range M, (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))) +
      ∑ i ∈ Finset.Ico (depth V k ((TopCat.toSSet.obj X).δ j x)) M,
        (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))) := by
    intro j
    have e := Finset.sum_range_add_sum_Ico
      (fun i => (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x))))
      (depth_face_le V k x j)
    rw [← e]
    generalize (∑ i ∈ Finset.range (depth V k ((TopCat.toSSet.obj X).δ j x)),
      (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x)))) = a
    generalize (∑ i ∈ Finset.Ico (depth V k ((TopCat.toSSet.obj X).δ j x)) (depth V (k + 1) x),
      (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x)))) = b
    rw [add_assoc, add_self_eq_zero', add_zero]
  rw [Finset.sum_congr rfl (fun j _ => h2 j), Finset.sum_add_distrib, ← hM]
  generalize (∑ j : Fin (k + 2), ∑ i ∈ Finset.range M, (hoHom X k).hom ((sdHom X k).hom^[i]
    (gen ((TopCat.toSSet.obj X).δ j x)))) = A
  generalize (∑ j : Fin (k + 2), ∑ i ∈ Finset.Ico (depth V k ((TopCat.toSSet.obj X).δ j x)) M,
    (hoHom X k).hom ((sdHom X k).hom^[i] (gen ((TopCat.toSSet.obj X).δ j x)))) = B
  generalize (sdHom X (k + 1)).hom^[M] (gen x) = S
  generalize gen x = g
  have e : A + B + (S + g + A) + g = S + B + (A + A) + (g + g) := by abel
  rw [e, add_self_eq_zero', add_self_eq_zero', add_zero, add_zero]

end HatcherGen

section HatcherSmall

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

variable {X : TopCat.{0}}

lemma rho_gen_mem (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A) (hcov : ⋃₀ V = Set.univ) (k : ℕ)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    ((rho V).f k).hom (gen x) ∈ SmallChains.smallSub X V k := by
  cases k with
  | zero =>
    rw [rho_gen_zero]
    exact mdepth_iter_mem V hV hcov x _ (mdepth_le_depth V 0 x)
  | succ k =>
    rw [rho_gen_succ]
    refine add_mem (mdepth_iter_mem V hV hcov x _ (mdepth_le_depth V _ x)) (sum_mem fun j _ => ?_)
    refine sum_mem fun i hi => ?_
    have hi' := (Finset.mem_Ico.1 hi).1
    exact hoHom_mem V _ (mdepth_iter_mem V hV hcov _ i
      ((mdepth_le_depth V k _).trans hi'))

lemma rho_mem (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A) (hcov : ⋃₀ V = Set.univ) (k : ℕ)
    (z : SC X k) : ((rho V).f k).hom z ∈ SmallChains.smallSub X V k := by
  have hz : z ∈ Submodule.span F2 (Set.range (SmallChains.gen X (n := k))) := by
    rw [SmallChains.span_gen_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨σ, rfl⟩ := hx; exact rho_gen_mem V hV hcov k σ
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

lemma rho_mem_W (V W : Set (Set X)) (k : ℕ) (z : SC X k)
    (hz : z ∈ SmallChains.smallSub X W k) : ((rho V).f k).hom z ∈ SmallChains.smallSub X W k := by
  cases k with
  | zero =>
    rw [rho_zero]
    exact add_mem (SmallChains.smallSub_d X W 1 0 _ (Dk_mem V W z hz)) hz
  | succ k =>
    rw [rho_succ]
    exact add_mem (add_mem (Dk_mem V W _ (SmallChains.smallSub_d X W _ _ z hz))
      (SmallChains.smallSub_d X W _ _ _ (Dk_mem V W z hz))) hz

lemma rho_fix (V : Set (Set X)) (k : ℕ) (z : SC X k) (hz : z ∈ SmallChains.smallSub X V k) :
    ((rho V).f k).hom z = z := by
  rw [rho_eq_general, Dhom_zero V _ _ z hz, Dhom_zero V _ _ _ (SmallChains.smallSub_d X V _ _ z hz)]
  simp

/-- The corestricted retraction `ρ : C_*(X) → C_*^V(X)`. -/
noncomputable def rhoSmall (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A) (hcov : ⋃₀ V = Set.univ) :
    singularChains.obj X ⟶ SmallChains.smallChains V where
  f i := ModuleCat.ofHom (LinearMap.codRestrict (SmallChains.smallSub X V i) ((rho V).f i).hom
    (rho_mem V hV hcov i))
  comm' i j _ := by
    ext x
    apply Subtype.ext
    have h := congr($((rho V).comm i j) x)
    exact h

/-- The small-chain inclusion is a chain homotopy equivalence. -/
noncomputable def smallChainsHomotopyEquiv (V : Set (Set X)) (hV : ∀ A ∈ V, IsOpen A)
    (hcov : ⋃₀ V = Set.univ) :
    HomotopyEquiv (SmallChains.smallChains V) (singularChains.obj X) where
  hom := SmallChains.smallChains_inclusion V
  inv := rhoSmall V hV hcov
  homotopyHomInvId := Homotopy.ofEq (by
    ext i x
    apply Subtype.ext
    exact rho_fix V i x.1 x.2)
  homotopyInvHomId := (Homotopy.ofEq (by
    ext i x
    rfl)).trans (rhoHomotopy V)

end HatcherSmall

section Relative

open CategoryTheory.Limits

lemma R_surj (P : TopPair) (n : ℕ) : Function.Surjective ((relativeChainsπ P).f n).hom := by
  have h := (pairShortComplex_shortExact P).epi_g
  have : Epi (relativeChainsπ P) := h
  have : Epi ((relativeChainsπ P).f n) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

lemma R_ker (P : TopPair) (n : ℕ) (z : (singularChains.obj P.right).X n)
    (hz : ((relativeChainsπ P).f n).hom z = 0) :
    ∃ w : (singularChains.obj P.left).X n, ((singularChains.map P.hom).f n).hom w = z := by
  have h := ((pairShortComplex_shortExact P).map_of_exact (HomologicalComplex.eval _ _ n)).exact
  exact (ShortComplex.moduleCat_exact_iff _).1 h z hz

lemma R_zero (P : TopPair) (n : ℕ) (w : (singularChains.obj P.left).X n) :
    ((relativeChainsπ P).f n).hom (((singularChains.map P.hom).f n).hom w) = 0 := by
  have := congr($(relativeChains_condition_f P n) w)
  simpa using this

end Relative

section Embedding

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

lemma range_map_eq {Y X : TopCat.{0}} (g : Y ⟶ X) (hg : Topology.IsEmbedding g.hom) (n : ℕ) :
    LinearMap.range ((singularChains.map g).f n).hom =
      SmallChains.smallSub X {Set.range g.hom} n := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    have hw : w ∈ Submodule.span F2 (Set.range (SmallChains.gen Y (n := n))) := by
      rw [SmallChains.span_gen_eq_top]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      show ((singularChains.map g).f n).hom (gen σ) ∈ _
      rw [map_gen]
      refine SmallChains.gen_mem_smallSub ⟨_, rfl, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨τ, ⟨A, hA, hsub⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hA
    subst hA
    have hτ : ∀ t, ∃ y, g.hom y = simpEquiv X n τ t := fun t => hsub ⟨t, rfl⟩
    choose s hs using hτ
    have hcont : Continuous s := by
      rw [hg.continuous_iff]
      have : g.hom ∘ s = simpEquiv X n τ := funext hs
      rw [this]
      exact (simpEquiv X n τ).continuous
    refine ⟨gen ((simpEquiv Y n).symm ⟨s, hcont⟩), ?_⟩
    show ((singularChains.map g).f n).hom (gen _) = gen τ
    rw [map_gen]
    congr 1
    apply (simpEquiv X n).injective
    rw [simpEquiv_map, Equiv.apply_symm_apply]
    ext t
    exact hs t

end Embedding

section Intersection

open DGPS.Topology.Subdivision DGPS.Topology.SubdivisionSingular Finsupp

open Classical in
/-- Projection onto the generators of `P`-small simplices. -/
noncomputable def proj {X : TopCat.{0}} (P : Set X) (n : ℕ) : SC X n ⟶ SC X n :=
  mkHom fun x => if SmallChains.IsSmall {P} x then gen x else 0

open Classical in
lemma proj_gen {X : TopCat.{0}} (P : Set X) {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    (proj P n).hom (gen x) = if SmallChains.IsSmall {P} x then gen x else 0 :=
  mkHom_gen _ x

lemma isSmall_inter_iff {X : TopCat.{0}} (A B : Set X) {n : ℕ} (x : (TopCat.toSSet.obj X) _⦋n⦌) :
    SmallChains.IsSmall {A ∩ B} x ↔ SmallChains.IsSmall {A} x ∧ SmallChains.IsSmall {B} x := by
  constructor
  · rintro ⟨C, hC, hsub⟩
    rw [Set.mem_singleton_iff] at hC
    subst hC
    exact ⟨⟨A, rfl, hsub.trans Set.inter_subset_left⟩, ⟨B, rfl, hsub.trans Set.inter_subset_right⟩⟩
  · rintro ⟨⟨C, hC, h1⟩, ⟨D, hD, h2⟩⟩
    rw [Set.mem_singleton_iff] at hC hD
    subst hC hD
    exact ⟨C ∩ D, rfl, Set.subset_inter h1 h2⟩

lemma proj_mem {X : TopCat.{0}} (P : Set X) (n : ℕ) (z : SC X n) :
    (proj P n).hom z ∈ SmallChains.smallSub X {P} n := by
  have hz : z ∈ Submodule.span F2 (Set.range (SmallChains.gen X (n := n))) := by
    rw [SmallChains.span_gen_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, rfl⟩ := hx
    show (proj P n).hom (gen σ) ∈ _
    rw [proj_gen]
    split_ifs with h
    · exact SmallChains.gen_mem_smallSub h
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

lemma proj_fix {X : TopCat.{0}} (P : Set X) (n : ℕ) (z : SC X n)
    (hz : z ∈ SmallChains.smallSub X {P} n) : (proj P n).hom z = z := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    show (proj P n).hom (gen σ) = gen σ
    rw [proj_gen]
    have hσ' : SmallChains.IsSmall {P} σ := hσ
    simp [hσ']
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

lemma proj_comp {X : TopCat.{0}} (A B : Set X) (n : ℕ) :
    proj B n ≫ proj A n = proj (A ∩ B) n := by
  apply hom_ext_gen
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [proj_gen B, proj_gen (A ∩ B), isSmall_inter_iff]
  by_cases hA : SmallChains.IsSmall {A} x <;> by_cases hB : SmallChains.IsSmall {B} x <;>
    simp [hA, hB, proj_gen]

lemma inter_smallSub {X : TopCat.{0}} (A B : Set X) (n : ℕ) (z : SC X n)
    (hA : z ∈ SmallChains.smallSub X {A} n) (hB : z ∈ SmallChains.smallSub X {B} n) :
    z ∈ SmallChains.smallSub X {A ∩ B} n := by
  have h := congr($(proj_comp A B n) z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [proj_fix B n z hB, proj_fix A n z hA] at h
  rw [h]
  exact proj_mem _ _ _

end Intersection

section Algebra

open DGPS.Topology.Subdivision

lemma cf_from {C D : ChainComplex F2Mod ℕ} (f : C ⟶ D) (n : ℕ) (z : C.X n) :
    (D.dFrom n).hom ((f.f n).hom z) = (f.f ((ComplexShape.down ℕ).next n)).hom ((C.dFrom n).hom z) := by
  have h := congr($(f.comm_from n) z)
  exact h

lemma cf_to {C D : ChainComplex F2Mod ℕ} (f : C ⟶ D) (n : ℕ) (z : C.X ((ComplexShape.down ℕ).prev n)) :
    (D.dTo n).hom ((f.f ((ComplexShape.down ℕ).prev n)).hom z) = (f.f n).hom ((C.dTo n).hom z) := by
  have h := congr($(f.comm_to n) z)
  exact h

lemma neg_eq_self'' {M : Type*} [AddCommGroup M] [Module F2 M] (a : M) : -a = a :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero' a)

lemma sub_eq_add'' {M : Type*} [AddCommGroup M] [Module F2 M] (a b : M) : a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_self'']

end Algebra

section ExAlgebra

open DGPS.Topology.Subdivision

/-- Algebraic data for the excision argument. -/
structure ExData (C D RP RQ : ChainComplex F2Mod ℕ) where
  SA : ∀ i, Submodule F2 (C.X i)
  SB : ∀ i, Submodule F2 (C.X i)
  hdA : ∀ i j (x : C.X i), x ∈ SA i → (C.d i j).hom x ∈ SA j
  ρ : C ⟶ C
  H : ∀ i j, C.X i ⟶ C.X j
  hE : ∀ (n : ℕ) (z : C.X n), (ρ.f n).hom z =
    (H ((ComplexShape.down ℕ).next n) n).hom ((C.dFrom n).hom z) +
      (C.dTo n).hom ((H n ((ComplexShape.down ℕ).prev n)).hom z) + z
  hρA : ∀ k z, z ∈ SA k → (ρ.f k).hom z ∈ SA k
  hHA : ∀ i j z, z ∈ SA i → (H i j).hom z ∈ SA j
  hHB : ∀ i j z, z ∈ SB i → (H i j).hom z ∈ SB j
  hρ : ∀ k z, (ρ.f k).hom z ∈ SA k ⊔ SB k
  πQ : C ⟶ RQ
  hπQs : ∀ n, Function.Surjective (πQ.f n).hom
  hπQk : ∀ n z, (πQ.f n).hom z = 0 ↔ z ∈ SA n
  πP : D ⟶ RP
  hπPs : ∀ n, Function.Surjective (πP.f n).hom
  j : D ⟶ C
  hjr : ∀ n, LinearMap.range (j.f n).hom = SB n
  hkP : ∀ n u, (πP.f n).hom u = 0 ↔ (j.f n).hom u ∈ SA n
  φ : RP ⟶ RQ
  hφ : ∀ n u, (φ.f n).hom ((πP.f n).hom u) = (πQ.f n).hom ((j.f n).hom u)

end ExAlgebra

end DGPS.Topology.Excision

namespace DGPS.Topology.Excision.ExData

open DGPS.Topology.Subdivision

variable {C D RP RQ : ChainComplex F2Mod ℕ} (E : ExData C D RP RQ)

lemma hdFromA (n : ℕ) (z : C.X n) (hz : z ∈ E.SA n) :
    (C.dFrom n).hom z ∈ E.SA ((ComplexShape.down ℕ).next n) := E.hdA _ _ z hz

lemma hdToA (n : ℕ) (z : C.X ((ComplexShape.down ℕ).prev n))
    (hz : z ∈ E.SA ((ComplexShape.down ℕ).prev n)) :
    (C.dTo n).hom z ∈ E.SA n := E.hdA _ _ z hz

lemma hπQeq (n : ℕ) (u v : C.X n) (h : u + v ∈ E.SA n) :
    (E.πQ.f n).hom u = (E.πQ.f n).hom v := by
  have h0 := (E.hπQk n _).2 h
  rw [map_add] at h0
  rw [add_eq_zero_iff_eq_neg, neg_eq_self''] at h0
  exact h0

lemma hπPeq (n : ℕ) (u v : D.X n) (h : (E.j.f n).hom u + (E.j.f n).hom v ∈ E.SA n) :
    (E.πP.f n).hom u = (E.πP.f n).hom v := by
  have h0 := (E.hkP n (u + v)).2 (by rw [map_add]; exact h)
  rw [map_add] at h0
  rw [add_eq_zero_iff_eq_neg, neg_eq_self''] at h0
  exact h0

lemma hsurj (n : ℕ) (y : RQ.X n) (hy : (RQ.dFrom n).hom y = 0) :
    ∃ x : RP.X n, (RP.dFrom n).hom x = 0 ∧ ∃ w : RQ.X ((ComplexShape.down ℕ).prev n),
      (RQ.dTo n).hom w = (E.φ.f n).hom x - y := by
  obtain ⟨z, rfl⟩ := E.hπQs n y
  have hz1 : (C.dFrom n).hom z ∈ E.SA ((ComplexShape.down ℕ).next n) := by
    rw [← E.hπQk, ← cf_from, hy]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (E.hρ n z)
  obtain ⟨bt, hbt⟩ : b ∈ LinearMap.range (E.j.f n).hom := by rw [E.hjr]; exact hb
  have hbz : b = (E.ρ.f n).hom z + a := by
    rw [← hab]
    generalize a = a'
    rw [add_comm a' b, add_assoc, add_self_eq_zero', add_zero]
  have hdb : (C.dFrom n).hom b ∈ E.SA ((ComplexShape.down ℕ).next n) := by
    rw [hbz, map_add, cf_from E.ρ]
    exact add_mem (E.hρA _ _ hz1) (E.hdFromA n a ha)
  refine ⟨(E.πP.f n).hom bt, ?_, (E.πQ.f _).hom ((E.H n _).hom z), ?_⟩
  · rw [cf_from E.πP]
    refine (E.hkP _ _).2 ?_
    rw [← cf_from E.j, hbt]
    exact hdb
  · rw [cf_to E.πQ, E.hφ, hbt, sub_eq_add'', ← map_add]
    have h1 : a + b = (E.H ((ComplexShape.down ℕ).next n) n).hom ((C.dFrom n).hom z) +
        (C.dTo n).hom ((E.H n ((ComplexShape.down ℕ).prev n)).hom z) + z := by
      rw [hab, E.hE]
    have he := E.hHA _ n _ hz1
    refine E.hπQeq n _ _ ?_
    generalize (E.H ((ComplexShape.down ℕ).next n) n).hom ((C.dFrom n).hom z) = e at h1 he
    generalize (C.dTo n).hom ((E.H n ((ComplexShape.down ℕ).prev n)).hom z) = t at h1 ⊢
    have ha' : a = (e + t + z) + b := by
      rw [← h1, add_assoc a b b, add_self_eq_zero', add_zero]
    have : t + (b + z) = a + e := by
      rw [ha']
      have e1 : (e + t + z + b) + e = t + (b + z) + (e + e) := by abel
      rw [e1, add_self_eq_zero', add_zero]
    rw [this]
    exact add_mem ha he

lemma hinj (n : ℕ) (x : RP.X n) (hx : (RP.dFrom n).hom x = 0)
    (h : ∃ w : RQ.X ((ComplexShape.down ℕ).prev n), (RQ.dTo n).hom w = (E.φ.f n).hom x) :
    ∃ w' : RP.X ((ComplexShape.down ℕ).prev n), (RP.dTo n).hom w' = x := by
  obtain ⟨u, rfl⟩ := E.hπPs n x
  obtain ⟨w, hw⟩ := h
  obtain ⟨c, rfl⟩ := E.hπQs _ w
  rw [cf_to E.πQ, E.hφ] at hw
  have ha : (C.dTo n).hom c + (E.j.f n).hom u ∈ E.SA n := by
    refine (E.hπQk n _).1 ?_
    rw [map_add, hw, add_self_eq_zero']
  have hdb : (C.dFrom n).hom ((E.j.f n).hom u) ∈ E.SA ((ComplexShape.down ℕ).next n) := by
    rw [cf_from E.j]
    refine (E.hkP _ _).1 ?_
    rw [← cf_from E.πP]
    exact hx
  have hb : (E.j.f n).hom u ∈ E.SB n := by
    rw [← E.hjr]; exact ⟨u, rfl⟩
  obtain ⟨cA, hcA, cB, hcB, hc⟩ := Submodule.mem_sup.1 (E.hρ _ c)
  have hc' : cB + (E.H n ((ComplexShape.down ℕ).prev n)).hom ((E.j.f n).hom u) ∈
      E.SB ((ComplexShape.down ℕ).prev n) := add_mem hcB (E.hHB _ _ _ hb)
  have hc'' : cB + (E.H n ((ComplexShape.down ℕ).prev n)).hom ((E.j.f n).hom u) ∈
      LinearMap.range (E.j.f ((ComplexShape.down ℕ).prev n)).hom := by
    rw [E.hjr]; exact hc'
  obtain ⟨ct, hct⟩ := hc''
  refine ⟨(E.πP.f _).hom ct, ?_⟩
  rw [cf_to E.πP]
  refine E.hπPeq n _ _ ?_
  rw [← cf_to E.j, hct, map_add]
  have hcB' : cB = (E.ρ.f _).hom c + cA := by
    rw [← hc, add_comm cA cB, add_assoc, add_self_eq_zero', add_zero]
  have hdt : (C.dTo n).hom cB = (E.ρ.f n).hom ((C.dTo n).hom c) + (C.dTo n).hom cA := by
    rw [hcB', map_add, cf_to E.ρ]
  have hH := E.hE n ((E.j.f n).hom u)
  have hmem : (E.ρ.f n).hom ((C.dTo n).hom c + (E.j.f n).hom u) + (C.dTo n).hom cA +
      (E.H ((ComplexShape.down ℕ).next n) n).hom ((C.dFrom n).hom ((E.j.f n).hom u)) ∈ E.SA n :=
    add_mem (add_mem (E.hρA _ _ ha) (E.hdToA n cA hcA)) (E.hHA _ _ _ hdb)
  rw [map_add] at hmem
  rw [hdt]
  generalize (E.ρ.f n).hom ((C.dTo n).hom c) = p at hmem ⊢
  generalize (E.ρ.f n).hom ((E.j.f n).hom u) = q at hmem hH
  generalize (C.dTo n).hom cA = s at hmem ⊢
  generalize (E.H ((ComplexShape.down ℕ).next n) n).hom ((C.dFrom n).hom ((E.j.f n).hom u)) = e
    at hmem hH
  generalize (C.dTo n).hom ((E.H n ((ComplexShape.down ℕ).prev n)).hom ((E.j.f n).hom u)) = t
    at hH ⊢
  generalize (E.j.f n).hom u = b at hmem hH ⊢
  subst hH
  have e1 : p + (e + t + b) + s + e = (p + s + t + b) + (e + e) := by abel
  rw [e1, add_self_eq_zero', add_zero] at hmem
  exact hmem

lemma isIso (n : ℕ) : IsIso (HomologicalComplex.homologyMap E.φ n) := by
  refine SmallChains.isIso_homologyMap_of_moduleCat
    ((HomologicalComplex.shortComplexFunctor _ _ n).map E.φ) ?_ ?_
  · intro y hy
    exact E.hsurj n y hy
  · intro x hx h
    exact E.hinj n x hx h

end DGPS.Topology.Excision.ExData

namespace DGPS.Topology.Excision

section Topological

open DGPS.Topology

lemma smallSub_mono {X : TopCat.{0}} {B A : Set X} (h : B ⊆ A) (n : ℕ) :
    SmallChains.smallSub X {B} n ≤ SmallChains.smallSub X {A} n := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro σ ⟨B', hB', hs⟩
  rw [Set.mem_singleton_iff] at hB'
  subst hB'
  exact ⟨A, rfl, hs.trans h⟩

lemma sc_map_comp_apply {X Y W : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (n : ℕ)
    (z : (singularChains.obj X).X n) :
    ((singularChains.map (f ≫ g)).f n).hom z =
      ((singularChains.map g).f n).hom (((singularChains.map f).f n).hom z) := by
  rw [Functor.map_comp]
  rfl

lemma rel_ker_iff (P : TopPair) (hP : Topology.IsEmbedding P.hom.hom) (n : ℕ)
    (z : (singularChains.obj P.right).X n) :
    ((relativeChainsπ P).f n).hom z = 0 ↔
      z ∈ SmallChains.smallSub P.right {Set.range P.hom.hom} n := by
  have hr : LinearMap.range ((singularChains.map P.hom).f n).hom =
      SmallChains.smallSub P.right {Set.range P.hom.hom} n := range_map_eq P.hom hP n
  rw [← hr]
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := R_ker P n z hz
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact R_zero P n w

/-- The complement subspace `X ∖ Z`. -/
abbrev exY (X : TopCat.{0}) (Z : Set X) : TopCat.{0} := TopCat.of ↥(Zᶜ)

/-- The inclusion `X ∖ Z ⟶ X`. -/
def exInc (X : TopCat.{0}) (Z : Set X) : exY X Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

lemma exInc_emb (X : TopCat.{0}) (Z : Set X) : Topology.IsEmbedding (exInc X Z).hom :=
  Topology.IsEmbedding.subtypeVal

lemma exInc_range (X : TopCat.{0}) (Z : Set X) : Set.range (exInc X Z).hom = Zᶜ :=
  Subtype.range_val

/-- `A ∖ Z` as a subset of `X ∖ Z`. -/
def exA (X : TopCat.{0}) (A Z : Set X) : Set (exY X Z) := {y | y.1 ∈ A}

/-- The pair `(X ∖ Z, A ∖ Z)`. -/
noncomputable abbrev pairP (X : TopCat.{0}) (A Z : Set X) : TopPair :=
  TopPair.ofSet (exY X Z) (exA X A Z)

/-- The pair `(X, A)`. -/
noncomputable abbrev pairQ (X : TopCat.{0}) (A : Set X) : TopPair := TopPair.ofSet X A

/-- The inclusion of pairs `(X ∖ Z, A ∖ Z) ⟶ (X, A)`. -/
noncomputable def excisionMap (X : TopCat.{0}) (A Z : Set X) : pairP X A Z ⟶ pairQ X A :=
  TopPair.homMk
    (TopCat.ofHom (X := TopCat.of (exA X A Z)) (Y := TopCat.of A)
      ⟨fun y => ⟨y.1.1, y.2⟩,
        Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩)
    (exInc X Z) rfl

lemma pairQ_emb (X : TopCat.{0}) (A : Set X) : Topology.IsEmbedding (pairQ X A).hom.hom :=
  Topology.IsEmbedding.subtypeVal

lemma pairP_emb (X : TopCat.{0}) (A Z : Set X) :
    Topology.IsEmbedding (pairP X A Z).hom.hom :=
  Topology.IsEmbedding.subtypeVal

lemma pairQ_range (X : TopCat.{0}) (A : Set X) : Set.range (pairQ X A).hom.hom = A :=
  Subtype.range_val

lemma comp_range (X : TopCat.{0}) (A Z : Set X) :
    Set.range ((pairP X A Z).hom ≫ exInc X Z).hom = A ∩ Zᶜ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.2, y.1.2⟩
  · rintro ⟨hA, hZ⟩
    exact ⟨⟨⟨x, hZ⟩, hA⟩, rfl⟩

lemma exInc_inj (X : TopCat.{0}) (Z : Set X) (n : ℕ) :
    Function.Injective ((singularChains.map (exInc X Z)).f n).hom := by
  have : Mono (exInc X Z) := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have h := relative_chain_quotient.1 (TopPair.of (exInc X Z)) n
  exact (ModuleCat.mono_iff_injective _).1 h

lemma smallSub_V_le (X : TopCat.{0}) (A Z : Set X) (n : ℕ) :
    SmallChains.smallSub X {interior A, (closure Z)ᶜ} n ≤
      SmallChains.smallSub X {A} n ⊔ SmallChains.smallSub X {Zᶜ} n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨σ, ⟨B, hB, hsub⟩, rfl⟩
  rcases hB with rfl | hB
  · exact Submodule.mem_sup_left
      (SmallChains.gen_mem_smallSub ⟨A, rfl, hsub.trans interior_subset⟩)
  · rw [Set.mem_singleton_iff] at hB
    subst hB
    exact Submodule.mem_sup_right (SmallChains.gen_mem_smallSub
      ⟨Zᶜ, rfl, hsub.trans (Set.compl_subset_compl.2 subset_closure)⟩)

/-- The algebraic excision data for `(X ∖ Z, A ∖ Z) ⟶ (X, A)`. -/
noncomputable def exData (X : TopCat.{0}) (A Z : Set X) (hZ : closure Z ⊆ interior A) :
    ExData (singularChains.obj X) (singularChains.obj (exY X Z))
      (relativeChains.obj (pairP X A Z)) (relativeChains.obj (pairQ X A)) where
  SA := SmallChains.smallSub X {A}
  SB := SmallChains.smallSub X {Zᶜ}
  hdA i j x hx := SmallChains.smallSub_d X {A} i j x hx
  ρ := rho ({interior A, (closure Z)ᶜ} : Set (Set X))
  H := Dhom ({interior A, (closure Z)ᶜ} : Set (Set X))
  hE n z := rho_eq_general _ n z
  hρA k z hz := rho_mem_W _ _ k z hz
  hHA i j z hz := Dhom_mem _ _ i j z hz
  hHB i j z hz := Dhom_mem _ _ i j z hz
  hρ k z := by
    refine smallSub_V_le X A Z k (rho_mem _ ?_ ?_ k z)
    · rintro B (rfl | hB)
      · exact isOpen_interior
      · rw [Set.mem_singleton_iff] at hB
        subst hB
        exact isClosed_closure.isOpen_compl
    · ext x
      simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
      by_cases hx : x ∈ closure Z
      · exact ⟨interior A, Or.inl rfl, hZ hx⟩
      · exact ⟨(closure Z)ᶜ, Or.inr rfl, hx⟩
  πQ := relativeChainsπ (pairQ X A)
  hπQs n := R_surj _ n
  hπQk n z := by
    have h := rel_ker_iff _ (pairQ_emb X A) n z
    rw [pairQ_range] at h
    exact h
  πP := relativeChainsπ (pairP X A Z)
  hπPs n := R_surj _ n
  j := singularChains.map (exInc X Z)
  hjr n := by
    rw [range_map_eq _ (exInc_emb X Z) n, exInc_range]
  hkP n u := by
    refine (rel_ker_iff _ (pairP_emb X A Z) n u).trans ?_
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := (show u ∈ LinearMap.range ((singularChains.map (pairP X A Z).hom).f n).hom
        from by rw [range_map_eq _ (pairP_emb X A Z) n]; exact hu)
      have hc : Topology.IsEmbedding ((pairP X A Z).hom ≫ exInc X Z).hom :=
        (exInc_emb X Z).comp (pairP_emb X A Z)
      have hmem : ((singularChains.map (exInc X Z)).f n).hom u ∈
          LinearMap.range ((singularChains.map ((pairP X A Z).hom ≫ exInc X Z)).f n).hom :=
        ⟨w, (sc_map_comp_apply (pairP X A Z).hom (exInc X Z) n w).trans
          (congrArg (((singularChains.map (exInc X Z)).f n).hom) hw)⟩
      rw [range_map_eq _ hc n, comp_range] at hmem
      exact smallSub_mono Set.inter_subset_left n hmem
    · intro hu
      have hb : ((singularChains.map (exInc X Z)).f n).hom u ∈
          SmallChains.smallSub X {Zᶜ} n := by
        rw [← exInc_range X Z, ← range_map_eq _ (exInc_emb X Z) n]
        exact ⟨u, rfl⟩
      have hi := inter_smallSub _ _ n _ hu hb
      have hc : Topology.IsEmbedding ((pairP X A Z).hom ≫ exInc X Z).hom :=
        (exInc_emb X Z).comp (pairP_emb X A Z)
      rw [← comp_range X A Z, ← range_map_eq _ hc n] at hi
      obtain ⟨w, hw⟩ := hi
      have hw' : ((singularChains.map (exInc X Z)).f n).hom
          (((singularChains.map (pairP X A Z).hom).f n).hom w) =
          ((singularChains.map (exInc X Z)).f n).hom u := by
        exact (sc_map_comp_apply (pairP X A Z).hom (exInc X Z) n w).symm.trans hw
      have := exInc_inj X Z n hw'
      rw [← this]
      have hr : LinearMap.range ((singularChains.map (pairP X A Z).hom).f n).hom =
          SmallChains.smallSub (pairP X A Z).right {Set.range (pairP X A Z).hom.hom} n :=
        range_map_eq _ (pairP_emb X A Z) n
      rw [← hr]
      exact ⟨w, rfl⟩
  φ := relativeChains.map (excisionMap X A Z)
  hφ n u := by
    have h := congr($(HomologicalComplex.congr_hom
      (relativeChainsπ_naturality (excisionMap X A Z)) n) u)
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp] at h
    exact h.symm

theorem excision_iso (X : TopCat.{0}) (A Z : Set X) (hZ : closure Z ⊆ interior A) (n : ℕ) :
    IsIso ((relativeHomology n).map (excisionMap X A Z)) :=
  (exData X A Z hZ).isIso n

end Topological

end DGPS.Topology.Excision

namespace DGPS.Topology

open CategoryTheory

/-- Subdivision and excision (Hatcher Prop. 2.21, Thm. 2.20): for an open cover `U` of `X` the
inclusion of `U`-small chains into singular chains is a chain homotopy equivalence; and if
`Z ⊆ A` with `closure Z ⊆ interior A`, the inclusion of pairs `(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces
isomorphisms on singular homology (with `F2` coefficients) in all degrees. -/
theorem subdivision_and_excision :
    (∀ (X : TopCat.{0}) (U : Set (Set X)), (∀ A ∈ U, IsOpen A) → ⋃₀ U = Set.univ →
      Nonempty (HomotopyEquiv (SmallChains.smallChains U) (singularChains.obj X))) ∧
    (∀ (X : TopCat.{0}) (A Z : Set X), Z ⊆ A → closure Z ⊆ interior A → ∀ n : ℕ,
      IsIso ((relativeHomology n).map (Excision.excisionMap X A Z))) :=
  ⟨fun _ U hU hcov => ⟨Excision.smallChainsHomotopyEquiv U hU hcov⟩,
    fun X A Z _ hZ n => Excision.excision_iso X A Z hZ n⟩

end DGPS.Topology
