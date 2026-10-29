import DGPS.Topology.Subdivision
import DGPS.Topology.SingularAdapter

/-!
# Barycentric subdivision on Mathlib singular chains (TOP004a, singular transfer)

Transfers the affine algebra of `DGPS.Topology.Subdivision` to `DGPS.Topology.singularChains`
(`F2` coefficients): a list of points of the standard simplex is realized as a singular simplex
(`σ ∘ realize l`), the chain-level operators `S` (subdivision) and `T` (homotopy) are defined on the
generators `ι σ` of the coproduct and shown to be a chain map and a chain homotopy `S ≃ 𝟙`,
natural in the space.
-/

open Convexity

namespace DGPS.Topology.SubdivisionSingular


abbrev Simp (n : ℕ) : Type := StdSimplex ℝ (Fin (n + 1))

noncomputable def p0 {n : ℕ} : Simp n := StdSimplex.single 0

noncomputable def vert (n : ℕ) : List (Simp n) := List.ofFn fun i : Fin (n + 1) => StdSimplex.single i

noncomputable def realize {n : ℕ} (l : List (Simp n)) (k : ℕ) (t : Simp k) : Simp n :=
  t.iConvexComb (fun j : Fin (k + 1) => l.getD j p0)

lemma getD_of_lt {α : Type*} (l : List α) (a : α) {j : ℕ} (hj : j < l.length) :
    l.getD j a = l[j] := by
  simp [List.getD_eq_getElem?_getD, hj]

lemma val_succAbove {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1)) :
    ((i.succAbove j : Fin (k + 2)) : ℕ) = if (j : ℕ) < i then (j : ℕ) else (j : ℕ) + 1 := by
  by_cases h : (j : ℕ) < i
  · rw [Fin.succAbove_of_castSucc_lt i j (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc i j (by simp [Fin.le_def]; omega)]
    simp [h]

/-- The barycenter of a list of points of a standard simplex (junk value on the empty list). -/
noncomputable def bary {n : ℕ} (l : List (Simp n)) : Simp n :=
  if h : l = [] then p0 else
    (StdSimplex.subBarycenter (K := ℝ) (Finset.range l.length)
      (by simpa [Finset.nonempty_range_iff] using h)).iConvexComb (fun i : ℕ => l.getD i p0)

lemma bary_map {n m : ℕ} (φ : Simp n → Simp m) (hφ : IsAffineMap ℝ φ) (l : List (Simp n))
    (hl : l ≠ []) : bary (l.map φ) = φ (bary l) := by
  have hl' : l.map φ ≠ [] := by simpa using hl
  simp only [bary, hl, hl', dite_false]
  rw [hφ.map_iConvexComb]
  simp only [List.length_map]
  refine iConvexComb_congr fun i hi => ?_
  have hi' : i < l.length := by
    by_contra hc
    exact hi (StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i (by simpa using hc))
  rw [Function.comp_apply, getD_of_lt _ _ hi', getD_of_lt _ _ (by simpa using hi')]
  simp

lemma weights_iConvexComb' {I J : Type*} (w : StdSimplex ℝ I) (f : I → StdSimplex ℝ J) :
    (w.iConvexComb f).weights = w.weights.sum (fun i r => r • (f i).weights) := by
  simp [iConvexComb, Finsupp.sum_mapDomain_index, add_smul]

lemma continuous_realize {n : ℕ} (l : List (Simp n)) (k : ℕ) : Continuous (realize l k) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff]
  rw [continuous_pi_iff]
  intro i
  have : ∀ t : Simp k, ((fun t : Simp n => t.weights) (realize l k t)) i =
      ∑ j : Fin (k + 1), t.weights j * (l.getD j p0).weights i := by
    intro t
    simp only [realize, weights_iConvexComb']
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [Finsupp.finsetSum_apply]
  simp only [Function.comp_def, this]
  refine continuous_finsetSum _ fun j _ => ?_
  exact (StdSimplex.continuous_weights_apply ℝ j).mul continuous_const


lemma getD_eraseIdx_succAbove {α : Type*} (l : List α) (a : α) {k : ℕ} (hl : l.length = k + 2)
    (i : Fin (k + 2)) (j : Fin (k + 1)) :
    (l.eraseIdx i).getD j a = l.getD (i.succAbove j) a := by
  have h1 : (j : ℕ) < (l.eraseIdx i).length := by
    rw [List.length_eraseIdx_of_lt (by omega)]; omega
  have h2 : ((i.succAbove j : Fin (k + 2)) : ℕ) < l.length := by
    have := (i.succAbove j).2; omega
  rw [getD_of_lt _ _ h1, getD_of_lt _ _ h2, List.getElem_eraseIdx]
  by_cases h : (j : ℕ) < i
  · simp [h, val_succAbove]
  · simp [h, val_succAbove]

lemma realize_face {n k : ℕ} (l : List (Simp n)) (hl : l.length = k + 2) (i : Fin (k + 2))
    (t : Simp k) :
    realize l (k + 1) (StdSimplex.map i.succAbove t) = realize (l.eraseIdx i) k t := by
  unfold realize
  rw [iConvexComb_map]
  congr 1
  funext j
  exact (getD_eraseIdx_succAbove l p0 hl i j).symm

lemma getD_irrel {α : Type*} (l : List α) (a b : α) {j : ℕ} (hj : j < l.length) :
    l.getD j a = l.getD j b := by
  rw [getD_of_lt _ _ hj, getD_of_lt _ _ hj]

lemma realize_map {n m k : ℕ} (φ : Simp n → Simp m) (hφ : IsAffineMap ℝ φ) (l : List (Simp n))
    (hl : l.length = k + 1) (t : Simp k) :
    φ (realize l k t) = realize (l.map φ) k t := by
  unfold realize
  rw [hφ.map_iConvexComb]
  congr 1
  funext j
  have hj : (j : ℕ) < l.length := by omega
  have hj' : (j : ℕ) < (l.map φ).length := by simpa using hj
  rw [Function.comp_apply, getD_of_lt _ _ hj, getD_of_lt _ _ hj']
  simp


lemma vert_length (n : ℕ) : (vert n).length = n + 1 := by simp [vert]

lemma vert_getD (n : ℕ) (j : Fin (n + 1)) : (vert n).getD j p0 = StdSimplex.single j := by
  rw [getD_of_lt _ _ (by rw [vert_length]; exact j.2)]
  simp only [vert, List.getElem_ofFn]

lemma realize_vert (n : ℕ) (t : Simp n) : realize (vert n) n t = t := by
  unfold realize
  simp only [vert_getD]
  exact StdSimplex.iConvexComb_single t

lemma vert_map_face (n : ℕ) (i : Fin (n + 2)) :
    (vert n).map (StdSimplex.map (R := ℝ) i.succAbove) = (vert (n + 1)).eraseIdx i := by
  refine List.ext_getElem (by rw [List.length_eraseIdx_of_lt (by simp [vert_length]; omega)]; simp [vert_length]) fun j h1 h2 => ?_
  have hj : j < n + 1 := by simpa [vert_length] using h1
  rw [List.getElem_map, List.getElem_eraseIdx]
  simp only [vert, List.getElem_ofFn, StdSimplex.map_single]
  by_cases h : j < (i : ℕ)
  · simp only [h, dite_true]
    congr 1
    apply Fin.ext
    simpa [h] using val_succAbove i ⟨j, hj⟩
  · simp only [h, dite_false]
    congr 1
    apply Fin.ext
    simpa [h] using val_succAbove i ⟨j, hj⟩


/-! ### Naturality of the homotopy operator on affine chains -/

section natural

open DGPS.Topology.Subdivision
open DGPS.Topology (F2)
open Finsupp

variable {P P' : Type*} (b : List P → P) (b' : List P' → P') (f : P → P')

lemma mapChain_homList (hf : ∀ l : List P, l ≠ [] → b' (l.map f) = f (b l)) (l : List P) :
    mapChain f (homList b l) = homList b' (l.map f) := by
  suffices h : ∀ n, ∀ l : List P, l.length = n →
      mapChain f (homList b l) = homList b' (l.map f) from h _ l rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn
  by_cases hl : l = []
  · subst hl; simp [homList]
  · have hl' : l.map f ≠ [] := by simpa using hl
    have key : mapChain f (homotopy b (bdList l)) = homotopy b' (bdList (l.map f)) := by
      rw [← mapChain_bdList]
      refine face_sum_congr l (mapChain f ∘ₗ homotopy b) (homotopy b' ∘ₗ mapChain f) fun i hi => ?_
      simp only [LinearMap.comp_apply, homotopy_single, one_smul, mapChain_single]
      rw [ih _ (hn ▸ bdList_length_lt l hi) _ rfl]
    rw [homList_of_ne_nil b hl, homList_of_ne_nil b' hl', mapChain_cone, map_add, mapChain_single,
      key, hf l hl]

end natural


/-! ### Transfer to Mathlib singular chains with `F2` coefficients -/

section singular

open CategoryTheory
open scoped Simplicial
open DGPS.Topology
open DGPS.Topology.Subdivision
open Finsupp

/-- The `k`-chains of the singular chain complex of `X`. -/
noncomputable abbrev SC (X : TopCat.{0}) (k : ℕ) : F2Mod := (singularChains.obj X).X k

noncomputable def gen {X : TopCat.{0}} {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) : SC X k :=
  ((TopCat.toSSet.obj X).ιChainComplex (R := coeffModule) x).hom (1 : F2)

noncomputable def mkHom {X : TopCat.{0}} {k : ℕ} {Y : F2Mod} (y : (TopCat.toSSet.obj X) _⦋k⦌ → Y) :
    SC X k ⟶ Y :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan coeffModule k).desc
    (Limits.Cofan.mk Y fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 Y (y x)))

lemma ι_mkHom {X : TopCat.{0}} {k : ℕ} {Y : F2Mod} (y : (TopCat.toSSet.obj X) _⦋k⦌ → Y)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := coeffModule) x ≫ mkHom y =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 Y (y x)) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan coeffModule k).fac
    (Limits.Cofan.mk Y fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton F2 Y (y x))) ⟨x⟩

lemma mkHom_gen {X : TopCat.{0}} {k : ℕ} {Y : F2Mod} (y : (TopCat.toSSet.obj X) _⦋k⦌ → Y)
    (x : (TopCat.toSSet.obj X) _⦋k⦌) : (mkHom y).hom (gen x) = y x := by
  have h : (mkHom y).hom (gen x) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := coeffModule) x ≫ mkHom y).hom (1 : F2) := rfl
  rw [h, ι_mkHom]
  simp

lemma hom_ext_gen {X : TopCat.{0}} {k : ℕ} {Y : F2Mod} {f g : SC X k ⟶ Y}
    (h : ∀ x : (TopCat.toSSet.obj X) _⦋k⦌, f.hom (gen x) = g.hom (gen x)) : f = g := by
  apply SSet.chainComplex_hom_ext
  intro x
  ext
  exact h x

lemma neg_one_pow_zsmul_F2 {M : Type*} [AddCommGroup M] [Module F2 M] (n : ℕ) (v : M) :
    ((-1 : ℤ) ^ n) • v = v := by
  have h1 : ∀ m : ℤ, m • v = (m : F2) • v := fun m => (Int.cast_smul_eq_zsmul F2 m v).symm
  rw [h1]
  have : (((-1 : ℤ) ^ n : ℤ) : F2) = 1 := by
    push_cast
    have : (-1 : F2) = 1 := by decide
    rw [this, one_pow]
  rw [this, one_smul]

lemma d_gen {X : TopCat.{0}} {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k + 1⦌) :
    ((singularChains.obj X).d (k + 1) k).hom (gen x) =
      ∑ i : Fin (k + 2), gen ((TopCat.toSSet.obj X).δ i x) := by
  have := (TopCat.toSSet.obj X).ιChainComplex_d (R := coeffModule) x
  have h : ((singularChains.obj X).d (k + 1) k).hom (gen x) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := coeffModule) x ≫
        ((TopCat.toSSet.obj X).chainComplex coeffModule).d (k + 1) k).hom (1 : F2) := rfl
  rw [h, this]
  simp [gen]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact neg_one_pow_zsmul_F2 _ _

noncomputable def simpEquiv (X : TopCat.{0}) (k : ℕ) : (TopCat.toSSet.obj X) _⦋k⦌ ≃ C(Simp k, X) :=
  X.toSSetObjEquiv (Opposite.op ⦋k⦌)

noncomputable def sim {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (l : List (Simp n)) (k : ℕ) :
    (TopCat.toSSet.obj X) _⦋k⦌ :=
  (simpEquiv X k).symm (σ.comp ⟨realize l k, continuous_realize l k⟩)

noncomputable def psi {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (k : ℕ) :
    LChain (Simp n) →ₗ[F2] SC X k :=
  Finsupp.lsum F2 fun l => if l.length = k + 1 then
    LinearMap.toSpanSingleton F2 (SC X k) (gen (sim σ l k)) else 0

lemma psi_single {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (k : ℕ) (l : List (Simp n)) :
    psi σ k (single l 1) = if l.length = k + 1 then gen (sim σ l k) else 0 := by
  simp only [psi, Finsupp.lsum_single]
  split_ifs <;> simp

lemma psi_nil {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (k : ℕ) :
    psi σ k (single [] 1) = 0 := by
  simp [psi_single]

lemma delta_sim {X : TopCat.{0}} {n k : ℕ} (σ : C(Simp n, X)) (l : List (Simp n))
    (hl : l.length = k + 2) (i : Fin (k + 2)) :
    (TopCat.toSSet.obj X).δ i (sim σ l (k + 1)) = sim σ (l.eraseIdx i) k := by
  apply (simpEquiv X k).injective
  ext t
  have h : (simpEquiv X k) ((TopCat.toSSet.obj X).δ i (sim σ l (k + 1))) t =
      σ (realize l (k + 1) (StdSimplex.map i.succAbove t)) := rfl
  rw [h, realize_face l hl i t]
  simp only [sim, Equiv.apply_symm_apply]
  rfl

lemma bdList_fin {α : Type*} (l : List α) (n : ℕ) (hl : l.length = n) :
    bdList l = ∑ i : Fin n, single (l.eraseIdx i) 1 := by
  subst hl
  unfold bdList
  exact (Fin.sum_univ_eq_sum_range (fun i => single (l.eraseIdx i) (1 : F2)) l.length).symm

lemma psi_d {X : TopCat.{0}} {n : ℕ} (σ : C(Simp n, X)) (k : ℕ) (y : LChain (Simp n)) :
    ((singularChains.obj X).d (k + 1) k).hom (psi σ (k + 1) y) = psi σ k (bd y) := by
  have : (((singularChains.obj X).d (k + 1) k).hom ∘ₗ psi σ (k + 1) : LChain (Simp n) →ₗ[F2] SC X k)
      = psi σ k ∘ₗ bd := by
    refine Finsupp.lhom_ext fun l c => ?_
    rw [← Finsupp.smul_single_one l c]
    simp only [map_smul, LinearMap.comp_apply]
    congr 1
    rw [bd_single, one_smul, psi_single]
    by_cases h : l.length = k + 2
    · simp only [h, show k + 2 = k + 1 + 1 from rfl, ↓reduceIte]
      rw [d_gen, bdList_fin l (k + 2) h, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [delta_sim σ l h i, psi_single]
      have : (l.eraseIdx i).length = k + 1 := by rw [List.length_eraseIdx_of_lt (by omega)]; omega
      simp [this]
    · have h' : ¬ l.length = k + 1 + 1 := h
      simp only [h', ↓reduceIte, map_zero]
      unfold bdList
      rw [map_sum]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      have hi' := Finset.mem_range.1 hi
      have : (l.eraseIdx i).length ≠ k + 1 := by
        rw [List.length_eraseIdx_of_lt hi']; omega
      simp [psi_single, this]
  exact congrArg (fun g => g y) this

lemma psi_comp {X : TopCat.{0}} {n m : ℕ} (σ : C(Simp n, X)) (ψ : C(Simp m, Simp n))
    (hψ : IsAffineMap ℝ ψ) (k : ℕ) (y : LChain (Simp m)) :
    psi (σ.comp ψ) k y = psi σ k (mapChain ψ y) := by
  have : (psi (σ.comp ψ) k : LChain (Simp m) →ₗ[F2] SC X k) = psi σ k ∘ₗ mapChain ψ := by
    refine Finsupp.lhom_ext fun l c => ?_
    rw [← Finsupp.smul_single_one l c]
    simp only [map_smul, LinearMap.comp_apply, mapChain_single, psi_single, List.length_map]
    congr 1
    by_cases h : l.length = k + 1
    · simp only [h, ↓reduceIte]
      congr 1
      apply (simpEquiv X k).injective
      simp only [sim, Equiv.apply_symm_apply]
      ext t
      exact congrArg σ (realize_map ψ hψ l h t)
    · have h' : ¬ l.length = k + 1 := h
      simp [h']
  exact congrArg (fun g => g y) this

lemma map_gen {X Y : TopCat.{0}} (f : X ⟶ Y) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    ((singularChains.map f).f k).hom (gen x) = gen ((TopCat.toSSet.map f).app _ x) := by
  have := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
    (f := TopCat.toSSet.map f) (R := coeffModule) x
  exact congrArg (fun g => ModuleCat.Hom.hom g (1 : F2)) this

lemma simpEquiv_map {X Y : TopCat.{0}} (f : X ⟶ Y) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    simpEquiv Y k ((TopCat.toSSet.map f).app _ x) = f.hom.comp (simpEquiv X k x) := rfl

lemma psi_nat {X Y : TopCat.{0}} (f : X ⟶ Y) {n : ℕ} (σ : C(Simp n, X)) (k : ℕ)
    (y : LChain (Simp n)) :
    psi (f.hom.comp σ) k y = ((singularChains.map f).f k).hom (psi σ k y) := by
  have : (psi (f.hom.comp σ) k : LChain (Simp n) →ₗ[F2] SC Y k) =
      ((singularChains.map f).f k).hom ∘ₗ psi σ k := by
    refine Finsupp.lhom_ext fun l c => ?_
    rw [← Finsupp.smul_single_one l c]
    simp only [map_smul, LinearMap.comp_apply, psi_single]
    congr 1
    by_cases h : l.length = k + 1
    · simp only [h, ↓reduceIte]
      rw [map_gen]
      congr 1
    · have h' : ¬ l.length = k + 1 := h
      simp [h']
  exact congrArg (fun g => g y) this

noncomputable def fm (k : ℕ) (i : Fin (k + 2)) : C(Simp k, Simp (k + 1)) :=
  ⟨StdSimplex.map i.succAbove, by fun_prop⟩

lemma fm_affine (k : ℕ) (i : Fin (k + 2)) : IsAffineMap ℝ (fm k i) :=
  StdSimplex.isAffineMap_map ℝ _

lemma bary_fm (k : ℕ) (i : Fin (k + 2)) :
    ∀ l : List (Simp k), l ≠ [] → bary (l.map (fm k i)) = fm k i (bary l) :=
  fun l hl => bary_map (fm k i) (fm_affine k i) l hl

lemma vert_map_fm (k : ℕ) (i : Fin (k + 2)) :
    (vert k).map (fm k i) = (vert (k + 1)).eraseIdx i := vert_map_face k i

noncomputable def sdHom (X : TopCat.{0}) (k : ℕ) : SC X k ⟶ SC X k :=
  mkHom fun x => psi (simpEquiv X k x) k (sdList bary (vert k))

noncomputable def hoHom (X : TopCat.{0}) (k : ℕ) : SC X k ⟶ SC X (k + 1) :=
  mkHom fun x => psi (simpEquiv X k x) (k + 1) (homList bary (vert k))

lemma sdHom_gen (X : TopCat.{0}) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    (sdHom X k).hom (gen x) = psi (simpEquiv X k x) k (sdList bary (vert k)) :=
  mkHom_gen _ x

lemma hoHom_gen (X : TopCat.{0}) {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    (hoHom X k).hom (gen x) = psi (simpEquiv X k x) (k + 1) (homList bary (vert k)) :=
  mkHom_gen _ x

lemma simpEquiv_δ {X : TopCat.{0}} {k : ℕ} (x : (TopCat.toSSet.obj X) _⦋k + 1⦌) (i : Fin (k + 2)) :
    simpEquiv X k ((TopCat.toSSet.obj X).δ i x) = (simpEquiv X (k + 1) x).comp (fm k i) := rfl

lemma sd_face {X : TopCat.{0}} {k : ℕ} (σ : C(Simp (k + 1), X)) (i : Fin (k + 2)) :
    psi (σ.comp (fm k i)) k (sdList bary (vert k)) =
      psi σ k (sdList bary ((vert (k + 1)).eraseIdx i)) := by
  rw [psi_comp σ (fm k i) (fm_affine k i), mapChain_sdList bary bary (fm k i) (bary_fm k i),
    vert_map_fm]

lemma ho_face {X : TopCat.{0}} {k : ℕ} (σ : C(Simp (k + 1), X)) (i : Fin (k + 2)) :
    psi (σ.comp (fm k i)) (k + 1) (homList bary (vert k)) =
      psi σ (k + 1) (homList bary ((vert (k + 1)).eraseIdx i)) := by
  rw [psi_comp σ (fm k i) (fm_affine k i), mapChain_homList bary bary (fm k i) (bary_fm k i),
    vert_map_fm]

lemma sdHom_comm (X : TopCat.{0}) (k : ℕ) :
    sdHom X (k + 1) ≫ (singularChains.obj X).d (k + 1) k =
      (singularChains.obj X).d (k + 1) k ≫ sdHom X k := by
  apply hom_ext_gen
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [sdHom_gen, psi_d, d_gen, map_sum, bd_sdList, bdList_fin _ (k + 2) (vert_length _), map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sdHom_gen, simpEquiv_δ, sd_face, sd_single, one_smul]

noncomputable def sdChainMap (X : TopCat.{0}) : singularChains.obj X ⟶ singularChains.obj X where
  f k := sdHom X k
  comm' i j hij := by
    have h : j + 1 = i := hij
    subst h
    exact sdHom_comm X j

lemma sdChainMap_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singularChains.map f ≫ sdChainMap Y = sdChainMap X ≫ singularChains.map f := by
  ext k : 1
  apply hom_ext_gen
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  show (sdHom Y k).hom (((singularChains.map f).f k).hom (gen x)) =
    ((singularChains.map f).f k).hom ((sdHom X k).hom (gen x))
  rw [map_gen, sdHom_gen, sdHom_gen, ← psi_nat]
  rfl

noncomputable def sdNat : singularChains ⟶ singularChains where
  app X := sdChainMap X
  naturality _ _ f := sdChainMap_natural f

lemma hoHom_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) :
    (singularChains.map f).f k ≫ hoHom Y k = hoHom X k ≫ (singularChains.map f).f (k + 1) := by
  apply hom_ext_gen
  intro x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [map_gen, hoHom_gen, hoHom_gen, ← psi_nat]
  rfl

lemma sim_vert {X : TopCat.{0}} (k : ℕ) (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    sim (simpEquiv X k x) (vert k) k = x := by
  apply (simpEquiv X k).injective
  simp only [sim, Equiv.apply_symm_apply]
  ext t
  exact congrArg (simpEquiv X k x) (realize_vert k t)

noncomputable def hhom (X : TopCat.{0}) (i j : ℕ) : SC X i ⟶ SC X j :=
  if h : i + 1 = j then hoHom X i ≫ eqToHom (by rw [h]) else 0

lemma hhom_succ (X : TopCat.{0}) (i : ℕ) : hhom X i (i + 1) = hoHom X i := by
  simp [hhom]

lemma psi_vert {X : TopCat.{0}} (k : ℕ) (x : (TopCat.toSSet.obj X) _⦋k⦌) :
    psi (simpEquiv X k x) k (single (vert k) 1) = gen x := by
  rw [psi_single, sim_vert]
  simp [vert_length]

lemma sd_eq_succ (X : TopCat.{0}) (k : ℕ) :
    sdHom X (k + 1) = (singularChains.obj X).d (k + 1) k ≫ hoHom X k +
      hoHom X (k + 1) ≫ (singularChains.obj X).d (k + 1 + 1) (k + 1) + 𝟙 _ := by
  apply hom_ext_gen
  intro x
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply]
  rw [sdHom_gen, d_gen, map_sum, hoHom_gen, psi_d]
  have h1 : ∑ i : Fin (k + 2), (hoHom X k).hom (gen ((TopCat.toSSet.obj X).δ i x)) =
      psi (simpEquiv X (k + 1) x) (k + 1) (homotopy bary (bdList (vert (k + 1)))) := by
    rw [bdList_fin _ (k + 2) (vert_length _), map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hoHom_gen, simpEquiv_δ, ho_face, homotopy_single, one_smul]
  rw [h1]
  have key := congrArg (psi (simpEquiv X (k + 1) x) (k + 1))
    (bd_homotopy_add bary (single (vert (k + 1)) (1 : F2)))
  rw [map_add, map_add, bd_single, one_smul, homotopy_single, one_smul, sd_single, one_smul,
    psi_vert] at key
  rw [add_comm (psi _ _ (bd _)) _] at key
  rw [key, add_right_comm (gen x) _ (gen x), add_self_eq_zero', zero_add]

lemma sd_eq_zero (X : TopCat.{0}) :
    sdHom X 0 = hoHom X 0 ≫ (singularChains.obj X).d 1 0 + 𝟙 _ := by
  apply hom_ext_gen
  intro x
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply]
  rw [sdHom_gen, hoHom_gen, psi_d]
  have h0 : homotopy bary (bdList (vert 0)) = 0 := by
    rw [bdList_fin _ 1 (vert_length 0), map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (vert 0).eraseIdx i = [] := List.eq_nil_of_length_eq_zero (by
      rw [List.length_eraseIdx_of_lt (by simp [vert_length])]; simp [vert_length])
    rw [this, homotopy_single, one_smul]
    simp [homList]
  have key := congrArg (psi (simpEquiv X 0 x) 0)
    (bd_homotopy_add bary (single (vert 0) (1 : F2)))
  rw [map_add, map_add, bd_single, one_smul, homotopy_single, one_smul, sd_single, one_smul,
    psi_vert, h0, map_zero, add_zero] at key
  rw [key, add_right_comm (gen x) _ (gen x), add_self_eq_zero']
  exact (zero_add _).symm

noncomputable def sdHomotopy (X : TopCat.{0}) :
    Homotopy (sdChainMap X) (𝟙 (singularChains.obj X)) where
  hom i j := hhom X i j
  zero i j hij := by
    have h : ¬ (i + 1 = j) := fun h => hij h
    simp [hhom, h]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, hhom_succ, zero_add]
      exact sd_eq_zero X
    | succ k =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex, hhom_succ, hhom_succ]
      exact sd_eq_succ X k

lemma sdHomotopy_natural {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ) :
    (singularChains.map f).f i ≫ (sdHomotopy Y).hom i j =
      (sdHomotopy X).hom i j ≫ (singularChains.map f).f j := by
  by_cases h : i + 1 = j
  · subst h
    show (singularChains.map f).f i ≫ hhom Y i (i + 1) = hhom X i (i + 1) ≫ _
    rw [hhom_succ, hhom_succ]
    exact hoHom_natural f i
  · show (singularChains.map f).f i ≫ hhom Y i j = hhom X i j ≫ _
    simp [hhom, h]

/-- Packet interface (TOP004a, singular transfer): barycentric subdivision `S` is a natural chain
map of the `F2` singular chain complex, and Mathlib `Homotopy`s `S_X ≃ 𝟙` exist for every space
`X`, natural in `X` componentwise. -/
theorem subdivision_singular_transfer :
    ∃ (S : singularChains ⟶ singularChains)
      (H : ∀ X : TopCat.{0}, Homotopy (S.app X) (𝟙 (singularChains.obj X))),
      ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (i j : ℕ),
        (singularChains.map f).f i ≫ (H Y).hom i j = (H X).hom i j ≫ (singularChains.map f).f j :=
  ⟨sdNat, sdHomotopy, fun f i j => sdHomotopy_natural f i j⟩

end singular

end DGPS.Topology.SubdivisionSingular
