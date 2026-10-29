import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Homotopy
import DGPS.Topology.SingularAdapter
import DGPS.Topology.Subdivision
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.StdSimplex

open CategoryTheory Simplicial

namespace DGPS.Topology.SmallChains

universe v u
variable {R : Type u} [Ring R]

theorem isIso_homologyMap_of_moduleCat {S₁ S₂ : ShortComplex (ModuleCat.{v} R)} (φ : S₁ ⟶ S₂)
    (hsurj : ∀ y : S₂.X₂, S₂.g y = 0 →
      ∃ x : S₁.X₂, S₁.g x = 0 ∧ ∃ w : S₂.X₁, S₂.f w = φ.τ₂ x - y)
    (hinj : ∀ x : S₁.X₂, S₁.g x = 0 → (∃ w : S₂.X₁, S₂.f w = φ.τ₂ x) →
      ∃ w' : S₁.X₁, S₁.f w' = x) :
    IsIso (ShortComplex.homologyMap φ) := by
  have c12 : ∀ w, φ.τ₂ (S₁.f w) = S₂.f (φ.τ₁ w) := fun w => by
    simpa using (congr($(φ.comm₁₂) w)).symm
  have c23 : ∀ x, S₂.g (φ.τ₂ x) = φ.τ₃ (S₁.g x) := fun x => by
    simpa using congr($(φ.comm₂₃) x)
  have hker : ∀ x ∈ LinearMap.ker S₁.g.hom, φ.τ₂.hom x ∈ LinearMap.ker S₂.g.hom := by
    intro x hx
    have h1 : S₁.g x = 0 := hx
    show S₂.g (φ.τ₂ x) = 0
    rw [c23, h1, map_zero]
  let φK : S₁.moduleCatLeftHomologyData.K ⟶ S₂.moduleCatLeftHomologyData.K :=
    ModuleCat.ofHom (φ.τ₂.hom.restrict hker)
  have hq : LinearMap.range S₁.moduleCatToCycles ≤
      (LinearMap.range S₂.moduleCatToCycles).comap φK.hom := by
    rintro _ ⟨w, rfl⟩
    refine ⟨φ.τ₁ w, ?_⟩
    apply Subtype.ext
    exact (c12 w).symm
  let γ : ShortComplex.LeftHomologyMapData φ S₁.moduleCatLeftHomologyData
      S₂.moduleCatLeftHomologyData :=
    { φK := φK
      φH := ModuleCat.ofHom (Submodule.mapQ _ _ φK.hom hq)
      commi := by ext x; rfl
      commf' := by
        ext x
        apply Subtype.ext
        exact (c12 x)
      commπ := by
        ext x
        rfl }
  have hH : IsIso γ.φH := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · rw [← LinearMap.ker_eq_bot (f := γ.φH.hom), Submodule.eq_bot_iff]
      intro q hq0
      obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hq1 : (Submodule.Quotient.mk (⟨φ.τ₂ x, hker x hx⟩ : LinearMap.ker S₂.g.hom) :
          S₂.moduleCatLeftHomologyData.H) = 0 := hq0
      rw [Submodule.Quotient.mk_eq_zero] at hq1
      obtain ⟨w, hw⟩ := hq1
      have hw' : S₂.f w = φ.τ₂ x := congr_arg Subtype.val hw
      obtain ⟨w', hw''⟩ := hinj x hx ⟨w, hw'⟩
      show (Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker S₁.g.hom) :
          S₁.moduleCatLeftHomologyData.H) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨w', Subtype.ext hw''⟩
    · intro q
      obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, hx, w, hw⟩ := hsurj y hy
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      show (Submodule.Quotient.mk (⟨φ.τ₂ x, hker x hx⟩ : LinearMap.ker S₂.g.hom) :
          S₂.moduleCatLeftHomologyData.H) = Submodule.Quotient.mk ⟨y, hy⟩
      rw [Submodule.Quotient.eq]
      exact ⟨w, Subtype.ext hw⟩
  rw [γ.homologyMap_eq]
  infer_instance

open HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}

/-- The subcomplex of a complex of modules cut out by d-stable submodules. -/
def subcomplex (C : HomologicalComplex (ModuleCat.{v} R) c) (P : ∀ i, Submodule R (C.X i))
    (hP : ∀ i j (x : C.X i), x ∈ P i → (C.d i j).hom x ∈ P j) :
    HomologicalComplex (ModuleCat.{v} R) c where
  X i := ModuleCat.of R (P i)
  d i j := ModuleCat.ofHom ((C.d i j).hom.restrict (fun x hx => hP i j x hx))
  shape i j h := by
    ext x
    simp [C.shape i j h]
  d_comp_d' i j k _ _ := by
    ext x
    have h := congrArg (fun f => f.hom x.1) (C.d_comp_d i j k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h
    exact h

/-- Inclusion of the subcomplex. -/
def subcomplexι (C : HomologicalComplex (ModuleCat.{v} R) c) (P : ∀ i, Submodule R (C.X i))
    (hP : ∀ i j (x : C.X i), x ∈ P i → (C.d i j).hom x ∈ P j) :
    subcomplex C P hP ⟶ C where
  f i := ModuleCat.ofHom (P i).subtype
  comm' i j _ := by
    ext x
    rfl

theorem homotopy_iter_step {C : HomologicalComplex (ModuleCat.{v} R) c} (S : C ⟶ C)
    (H : Homotopy S (𝟙 C)) (i : ι) (y : C.X i) (hy : C.dFrom i y = 0) :
    C.dTo i (H.hom i (c.prev i) y) = S.f i y - y := by
  have h := congr($(H.comm i) y)
  simp [dNext, prevD, hy] at h
  rw [h]
  simp

section Iter

variable {C : HomologicalComplex (ModuleCat.{v} R) c} (S : C ⟶ C)

theorem dFrom_iterate (i : ι) (m : ℕ) (z : C.X i) (hz : C.dFrom i z = 0) :
    C.dFrom i ((S.f i).hom^[m] z) = 0 := by
  induction m with
  | zero => simpa using hz
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h := congr($(S.comm_from i) ((S.f i).hom^[m] z))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    have h' : C.dFrom i ((S.f i).hom ((S.f i).hom^[m] z)) =
        (S.f (c.next i)).hom (C.dFrom i ((S.f i).hom^[m] z)) := h
    rw [h', ih, map_zero]

theorem dTo_iterate (i : ι) (m : ℕ) (w : C.X (c.prev i)) :
    C.dTo i ((S.f (c.prev i)).hom^[m] w) = (S.f i).hom^[m] (C.dTo i w) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h := congr($(S.comm_to i) ((S.f (c.prev i)).hom^[m] w))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    have h' : C.dTo i ((S.f (c.prev i)).hom ((S.f (c.prev i)).hom^[m] w)) =
        (S.f i).hom (C.dTo i ((S.f (c.prev i)).hom^[m] w)) := by
      have := h
      exact this.symm ▸ rfl
    rw [h', ih]

end Iter

section Main

variable (C : HomologicalComplex (ModuleCat.{v} R) c) (P : ∀ i, Submodule R (C.X i))
  (hP : ∀ i j (x : C.X i), x ∈ P i → (C.d i j).hom x ∈ P j)
  (S : C ⟶ C) (H : Homotopy S (𝟙 C))
  (hS : ∀ i (x : C.X i), x ∈ P i → (S.f i).hom x ∈ P i)
  (hH : ∀ i j (x : C.X i), x ∈ P i → (H.hom i j).hom x ∈ P j)

include hS hH in
theorem iter_exists (i : ι) (m : ℕ) (z : C.X i) (hz : C.dFrom i z = 0) :
    ∃ w : C.X (c.prev i), C.dTo i w = (S.f i).hom^[m] z - z ∧
      (z ∈ P i → w ∈ P (c.prev i)) := by
  induction m with
  | zero => exact ⟨0, by simp, fun _ => zero_mem _⟩
  | succ m ih =>
    obtain ⟨w, hw, hwP⟩ := ih
    have hcyc := dFrom_iterate S i m z hz
    refine ⟨H.hom i (c.prev i) ((S.f i).hom^[m] z) + w, ?_, ?_⟩
    · rw [map_add, homotopy_iter_step S H i _ hcyc, hw, Function.iterate_succ_apply']
      have : ∀ (a b d : C.X i), a - b + (b - d) = a - d := fun a b d => by abel
      exact this _ _ _
    · intro hz'
      refine add_mem (hH i _ _ ?_) (hwP hz')
      have : ∀ n, (S.f i).hom^[n] z ∈ P i := by
        intro n
        induction n with
        | zero => exact hz'
        | succ n ihn => rw [Function.iterate_succ_apply']; exact hS i _ ihn
      exact this m


include hS hH in
theorem isIso_homologyMap_subcomplexι
    (hm : ∀ i (x : C.X i), ∃ m, (S.f i).hom^[m] x ∈ P i) (i : ι) :
    IsIso (homologyMap (subcomplexι C P hP) i) := by
  have hiter : ∀ (j : ι) (n : ℕ) (z : C.X j), z ∈ P j → (S.f j).hom^[n] z ∈ P j := by
    intro j n z hz
    induction n with
    | zero => exact hz
    | succ n ihn => rw [Function.iterate_succ_apply']; exact hS j _ ihn
  refine isIso_homologyMap_of_moduleCat
    ((shortComplexFunctor _ c i).map (subcomplexι C P hP)) ?_ ?_
  · intro y hy
    have hy' : C.dFrom i y = 0 := hy
    obtain ⟨m, hmP⟩ := hm i y
    obtain ⟨w, hw, -⟩ := iter_exists C P S H hS hH i m y hy'
    refine ⟨⟨(S.f i).hom^[m] y, hmP⟩, ?_, w, hw⟩
    exact Subtype.ext (dFrom_iterate S i m y hy')
  · intro x hx ⟨w, hw⟩
    have hx' : C.dFrom i x.1 = 0 := congrArg Subtype.val hx
    have hw' : C.dTo i w = x.1 := hw
    obtain ⟨m, hmP⟩ := hm (c.prev i) w
    obtain ⟨u, hu, huP⟩ := iter_exists C P S H hS hH i m x.1 hx'
    refine ⟨⟨(S.f (c.prev i)).hom^[m] w - u, sub_mem hmP (huP x.2)⟩, ?_⟩
    apply Subtype.ext
    change C.dTo i ((S.f (c.prev i)).hom^[m] w - u) = x.1
    rw [map_sub, dTo_iterate S i m w, hu, hw']
    abel

end Main

open DGPS.Topology

/-- Generator of singular `n`-chains attached to a simplex. -/
noncomputable def gen (X : TopCat.{0}) {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (singularChains.obj X).X n :=
  (SSet.ιChainComplex (TopCat.toSSet.obj X) (R := coeffModule) σ).hom 1

theorem d_gen (X : TopCat.{0}) {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n + 1⦌) :
    ((singularChains.obj X).d (n + 1) n).hom (gen X σ) =
      ∑ i : Fin (n + 2), gen X ((TopCat.toSSet.obj X).δ i σ) := by
  have h := congr($(SSet.ιChainComplex_d (TopCat.toSSet.obj X) (R := coeffModule) σ) 1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, LinearMap.sum_apply] at h
  have hs : ∀ (k : ℕ) (f : coeffModule ⟶ (singularChains.obj X).X n),
      (ModuleCat.Hom.hom (((-1 : ℤ) ^ k) • f)) 1 = f.hom 1 := by
    intro k f
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_one_pow]; simp
    · rw [ho.neg_one_pow]
      simp only [Int.reduceNeg, neg_one_zsmul]
      simp only [ModuleCat.hom_neg, LinearMap.neg_apply]
      rw [neg_eq_iff_add_eq_zero, ← two_smul F2 (f.hom 1)]
      have h2 : (2 : F2) = 0 := by decide
      rw [h2, zero_smul]
  exact h.trans (Finset.sum_congr rfl fun i _ => hs i _)

theorem span_gen_eq_top (X : TopCat.{0}) (n : ℕ) :
    Submodule.span F2 (Set.range (gen X (n := n))) = ⊤ := by
  set N := Submodule.span F2 (Set.range (gen X (n := n))) with hN
  let q : (singularChains.obj X).X n ⟶ ModuleCat.of F2 (((singularChains.obj X).X n) ⧸ N) :=
    ModuleCat.ofHom N.mkQ
  have hq : q = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    ext
    show N.mkQ (gen X σ) = 0
    exact (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨σ, rfl⟩)
  rw [eq_top_iff]
  intro y _
  have h0 := congrArg (fun f => f.hom y) hq
  exact (Submodule.Quotient.mk_eq_zero N).mp h0

/-- A singular simplex is `U`-small when its image lies in a member of `U`. -/
def IsSmall {X : TopCat.{0}} (U : Set (Set X)) {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) : Prop :=
  ∃ A ∈ U, Set.range (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌) σ) ⊆ A

theorem isSmall_δ {X : TopCat.{0}} {U : Set (Set X)} {n : ℕ} {σ : TopCat.toSSet.obj X _⦋n + 1⦌}
    (h : IsSmall U σ) (i : Fin (n + 2)) : IsSmall U ((TopCat.toSSet.obj X).δ i σ) := by
  obtain ⟨A, hA, hsub⟩ := h
  refine ⟨A, hA, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hsub ⟨_, rfl⟩

/-- The span of the generators of `U`-small simplices, in degree `n`. -/
noncomputable def smallSub (X : TopCat.{0}) (U : Set (Set X)) (n : ℕ) :
    Submodule F2 ((singularChains.obj X).X n) :=
  Submodule.span F2 (gen X '' {σ | IsSmall U σ})

theorem gen_mem_smallSub {X : TopCat.{0}} {U : Set (Set X)} {n : ℕ}
    {σ : TopCat.toSSet.obj X _⦋n⦌} (h : IsSmall U σ) : gen X σ ∈ smallSub X U n :=
  Submodule.subset_span ⟨σ, h, rfl⟩

theorem smallSub_d (X : TopCat.{0}) (U : Set (Set X)) (i j : ℕ)
    (x : (singularChains.obj X).X i) (hx : x ∈ smallSub X U i) :
    ((singularChains.obj X).d i j).hom x ∈ smallSub X U j := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hi : j + 1 = i := hij
    subst hi
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, hσ, rfl⟩ := hx
      rw [d_gen]
      exact sum_mem fun k _ => gen_mem_smallSub (isSmall_δ hσ k)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [(singularChains.obj X).shape i j hij]
    simp

/-- The subcomplex of singular chains spanned by `U`-small simplices. -/
noncomputable def smallChains {X : TopCat.{0}} (U : Set (Set X)) : ChainComplex F2Mod ℕ :=
  subcomplex (singularChains.obj X) (smallSub X U) (smallSub_d X U)

/-- The inclusion of `U`-small chains into all singular chains. -/
noncomputable def smallChains_inclusion {X : TopCat.{0}} (U : Set (Set X)) :
    smallChains U ⟶ singularChains.obj X :=
  subcomplexι (singularChains.obj X) (smallSub X U) (smallSub_d X U)

theorem exists_iterate_mem_of_span {M : Type*} [AddCommGroup M] [Module F2 M] (f : M →ₗ[F2] M)
    (P : Submodule F2 M) (hf : ∀ x ∈ P, f x ∈ P) (G : Set M) (hG : Submodule.span F2 G = ⊤)
    (h : ∀ g ∈ G, ∃ m : ℕ, f^[m] g ∈ P) (x : M) : ∃ m : ℕ, f^[m] x ∈ P := by
  have hit : ∀ (k : ℕ) y, y ∈ P → f^[k] y ∈ P := by
    intro k
    induction k with
    | zero => intro y hy; exact hy
    | succ k ih => intro y hy; rw [Function.iterate_succ_apply]; exact ih _ (hf _ hy)
  have hadd : ∀ (k : ℕ) (y z : M), f^[k] (y + z) = f^[k] y + f^[k] z := by
    intro k
    induction k with
    | zero => intro y z; rfl
    | succ k ih => intro y z; rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_add]
  have hsmul : ∀ (k : ℕ) (r : F2) (y : M), f^[k] (r • y) = r • f^[k] y := by
    intro k
    induction k with
    | zero => intro r y; rfl
    | succ k ih => intro r y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, map_smul]
  have hx : x ∈ Submodule.span F2 G := by rw [hG]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [hadd]
    refine add_mem ?_ ?_
    · rw [Nat.add_comm, Function.iterate_add_apply]; exact hit b _ ha
    · rw [Function.iterate_add_apply]; exact hit a _ hb
  | smul r x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, ?_⟩
    rw [hsmul]
    exact Submodule.smul_mem _ _ ha

/-- Abstract hypothesis bundle for a barycentric subdivision operator `S` on singular chains with
chain homotopy `T` from `S` to the identity, relative to the cover `U`. -/
structure SubdivisionData (X : TopCat.{0}) (U : Set (Set X)) where
  /-- The subdivision chain map. -/
  S : singularChains.obj X ⟶ singularChains.obj X
  /-- The chain homotopy `∂T + T∂ = S - id`. -/
  T : Homotopy S (𝟙 (singularChains.obj X))
  /-- `S` preserves `U`-small simplices (as chains). -/
  S_small : ∀ (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌), IsSmall U σ →
    (S.f n).hom (gen X σ) ∈ smallSub X U n
  /-- `T` preserves `U`-small simplices (as chains). -/
  T_small : ∀ (n m : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌), IsSmall U σ →
    (T.hom n m).hom (gen X σ) ∈ smallSub X U m
  /-- Iterated subdivision eventually makes every simplex `U`-small. -/
  iter_small : ∀ (n : ℕ) (σ : TopCat.toSSet.obj X _⦋n⦌),
    ∃ m : ℕ, (S.f n).hom^[m] (gen X σ) ∈ smallSub X U n

/-- Abstract Hatcher argument: with a subdivision operator satisfying the hypotheses, the inclusion
of `U`-small chains induces isomorphisms on homology. -/
theorem smallChains_inclusion_isIso {X : TopCat.{0}} {U : Set (Set X)} (D : SubdivisionData X U)
    (n : ℕ) : IsIso (HomologicalComplex.homologyMap (smallChains_inclusion U) n) := by
  have hmap : ∀ {M N : Type} [AddCommGroup M] [Module F2 M] [AddCommGroup N] [Module F2 N]
      (g : M →ₗ[F2] N) (A : Submodule F2 M) (B : Submodule F2 N) (G : Set M),
      Submodule.span F2 G = A → (∀ x ∈ G, g x ∈ B) → ∀ x ∈ A, g x ∈ B := by
    intro M N _ _ _ _ g A B G hG hg x hx
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hg x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  refine isIso_homologyMap_subcomplexι (singularChains.obj X) (smallSub X U) (smallSub_d X U)
    D.S D.T ?_ ?_ ?_ n
  · intro i x hx
    exact hmap (D.S.f i).hom (smallSub X U i) (smallSub X U i) _ rfl
      (by rintro _ ⟨σ, hσ, rfl⟩; exact D.S_small i σ hσ) x hx
  · intro i j x hx
    exact hmap (D.T.hom i j).hom (smallSub X U i) (smallSub X U j) _ rfl
      (by rintro _ ⟨σ, hσ, rfl⟩; exact D.T_small i j σ hσ) x hx
  · intro i x
    refine exists_iterate_mem_of_span (D.S.f i).hom (smallSub X U i) ?_ (Set.range (gen X))
      (span_gen_eq_top X i) ?_ x
    · intro y hy
      exact hmap (D.S.f i).hom (smallSub X U i) (smallSub X U i) _ rfl
        (by rintro _ ⟨σ, hσ, rfl⟩; exact D.S_small i σ hσ) y hy
    · rintro _ ⟨σ, rfl⟩
      exact D.iter_small i σ

section MeshLebesgue

open DGPS.Topology.Subdivision DGPS.Topology Finsupp Convexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centroid of a list of points (the barycenter used for barycentric subdivision). -/
noncomputable def centroid (l : List E) : E := (l.length : ℝ)⁻¹ • l.sum

theorem list_sum_map_sub (l : List E) (v : E) :
    (l.map (fun x => x - v)).sum = l.sum - (l.length : ℝ) • v := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih, add_smul]; abel

theorem centroid_mem {C : Set E} (hC : Convex ℝ C) :
    ∀ (l : List E), l ≠ [] → (∀ x ∈ l, x ∈ C) → centroid l ∈ C := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
    intro _ hl
    by_cases ht : t = []
    · subst ht; simpa [centroid] using hl a (by simp)
    · have h1 := ih ht (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have hk : (0 : ℝ) < t.length := by
        exact_mod_cast List.length_pos_iff.mpr ht
      have := hC (hl a (by simp)) h1 (a := ((t.length : ℝ) + 1)⁻¹)
        (b := (t.length : ℝ) / ((t.length : ℝ) + 1)) (by positivity) (by positivity)
        (by field_simp; ring)
      convert this using 1
      simp only [centroid, List.length_cons, List.sum_cons, Nat.cast_add, Nat.cast_one, smul_add,
        smul_smul]
      congr 2
      field_simp

omit [NormedSpace ℝ E] in
theorem norm_list_sum_map_le (l : List E) (f : E → E) :
    ‖(l.map f).sum‖ ≤ (l.map (fun x => ‖f x‖)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (norm_add_le _ _).trans (by linarith)

theorem dist_centroid_vertex_le (l : List E) (hl : l ≠ []) (d : ℝ)
    (hd : ∀ x ∈ l, ∀ y ∈ l, dist x y ≤ d) (v : E) (hv : v ∈ l) :
    dist (centroid l) v ≤ (((l.length : ℝ) - 1) / l.length) * d := by
  classical
  have hL : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_iff.mpr hl
  have h1 : centroid l - v = (l.length : ℝ)⁻¹ • (l.map (fun x => x - v)).sum := by
    rw [list_sum_map_sub, smul_sub, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
    rfl
  have h2 : ‖(l.map (fun x => x - v)).sum‖ ≤ (l.map (fun x => ‖x - v‖)).sum := by
    exact norm_list_sum_map_le l (fun x => x - v)
  have hp : l.Perm (v :: l.erase v) := List.perm_cons_erase hv
  have h3 : (l.map (fun x => ‖x - v‖)).sum ≤ ((l.length : ℝ) - 1) * d := by
    rw [(hp.map (fun x => ‖x - v‖)).sum_eq]
    simp only [List.map_cons, List.sum_cons, sub_self, norm_zero, zero_add]
    have h4 := List.sum_le_length_nsmul ((l.erase v).map (fun x => ‖x - v‖)) d (by
      intro r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      rw [← dist_eq_norm]
      exact hd x (List.mem_of_mem_erase hx) v hv)
    rw [List.length_map, List.length_erase_of_mem hv, nsmul_eq_mul] at h4
    have : (((l.length - 1 : ℕ)) : ℝ) = (l.length : ℝ) - 1 := by
      rw [Nat.cast_sub (List.length_pos_iff.mpr hl)]; simp
    rw [this] at h4
    exact h4
  rw [dist_eq_norm, h1, norm_smul, norm_inv, Real.norm_natCast]
  calc (l.length : ℝ)⁻¹ * ‖(l.map (fun x => x - v)).sum‖
      ≤ (l.length : ℝ)⁻¹ * (((l.length : ℝ) - 1) * d) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = (((l.length : ℝ) - 1) / l.length) * d := by field_simp

theorem dist_centroid_hull_le (l : List E) (hl : l ≠ []) (d : ℝ)
    (hd : ∀ x ∈ l, ∀ y ∈ l, dist x y ≤ d) (y : E) (hy : y ∈ convexHull ℝ {x | x ∈ l}) :
    dist (centroid l) y ≤ (((l.length : ℝ) - 1) / l.length) * d := by
  have : convexHull ℝ {x | x ∈ l} ⊆ Metric.closedBall (centroid l)
      ((((l.length : ℝ) - 1) / l.length) * d) :=
    convexHull_min (fun v hv => by
      rw [Metric.mem_closedBall]
      rw [dist_comm]
      exact dist_centroid_vertex_le l hl d hd v hv) (convex_closedBall _ _)
  have := this hy
  rw [Metric.mem_closedBall, dist_comm] at this
  exact this

theorem sdList_eq_sum {P : Type*} (b : List P → P) {l : List P} (hl : l ≠ []) :
    sdList b l = ∑ i : Fin l.length, cone (b l) (sdList b (l.eraseIdx i)) := by
  rw [sdList]
  simp [hl]

theorem mem_support_sdList {P : Type*} (b : List P → P) {l : List P} (hl : l ≠ [])
    {l' : List P} (h : l' ∈ (sdList b l).support) :
    ∃ i : Fin l.length, ∃ l'' ∈ (sdList b (l.eraseIdx i)).support, l' = b l :: l'' := by
  classical
  rw [sdList_eq_sum b hl] at h
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  obtain ⟨l'', hl'', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hi)
  exact ⟨i, l'', hl'', rfl⟩

theorem mesh_sdList : ∀ (k : ℕ) (l : List E) (d : ℝ), l.length = k + 1 →
    (∀ x ∈ l, ∀ y ∈ l, dist x y ≤ d) → ∀ l' ∈ (sdList centroid l).support,
    l'.length = k + 1 ∧ (∀ v ∈ l', v ∈ convexHull ℝ {x | x ∈ l}) ∧
      ∀ x ∈ l', ∀ y ∈ l', dist x y ≤ ((k : ℝ) / (k + 1)) * d := by
  intro k
  induction k with
  | zero =>
    intro l d hlen hd l' hl'
    have hl : l ≠ [] := by intro h; subst h; simp at hlen
    obtain ⟨i, l'', hl'', rfl⟩ := mem_support_sdList centroid hl hl'
    have hf : (l.eraseIdx i) = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_eraseIdx_of_lt i.2, hlen]
    rw [hf, sdList_nil] at hl''
    have : l'' = [] := by simpa using Finsupp.support_single_subset hl''
    subst this
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    refine ⟨by simp [centroid], ?_, ?_⟩
    · intro v hv
      have : v = centroid [a] := by simpa using hv
      subst this
      simp [centroid]
    · intro x hx y hy
      have hx' : x = centroid [a] := by simpa using hx
      have hy' : y = centroid [a] := by simpa using hy
      subst hx' hy'
      simp
  | succ k ih =>
    intro l d hlen hd l' hl'
    have hl : l ≠ [] := by intro h; subst h; simp at hlen
    obtain ⟨i, l'', hl'', rfl⟩ := mem_support_sdList centroid hl hl'
    have hlenf : (l.eraseIdx i).length = k + 1 := by
      rw [List.length_eraseIdx_of_lt i.2, hlen]; rfl
    obtain ⟨h1, h2, h3⟩ := ih (l.eraseIdx i) d hlenf
      (fun x hx y hy => hd x (List.mem_of_mem_eraseIdx hx) y (List.mem_of_mem_eraseIdx hy)) l'' hl''
    have hsub : convexHull ℝ {x | x ∈ l.eraseIdx i} ⊆ convexHull ℝ {x | x ∈ l} :=
      convexHull_mono (fun x hx => List.mem_of_mem_eraseIdx hx)
    have hd0 : 0 ≤ d := by
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l hl
      exact (dist_nonneg).trans (hd a ha a ha)
    have hcm : centroid l ∈ convexHull ℝ {x | x ∈ l} :=
      centroid_mem (convex_convexHull ℝ _) l hl (fun x hx => subset_convexHull ℝ _ hx)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmono : ((k : ℝ) / (k + 1)) * d ≤ (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) * d := by
      apply mul_le_mul_of_nonneg_right _ hd0
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    refine ⟨by simp [h1], ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hcm
      · exact hsub (h2 v hv)
    · have hcd : ∀ v ∈ l'', dist (centroid l) v ≤ (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) * d := by
        intro v hv
        have := dist_centroid_hull_le l hl d hd v (hsub (h2 v hv))
        rw [hlen] at this
        push_cast at this ⊢
        convert this using 2
        ring
      have hcc : dist (centroid l) (centroid l) ≤ (((k + 1 : ℕ) : ℝ) / (((k + 1 : ℕ) : ℝ) + 1)) * d := by
        rw [dist_self]; positivity
      intro x hx y hy
      rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hy with rfl | hy
      · exact hcc
      · exact hcd y hy
      · rw [dist_comm]; exact hcd x hx
      · exact (h3 x hx y hy).trans hmono


theorem support_sd_subset {P : Type*} (b : List P → P) (y : LChain P) {l' : List P}
    (h : l' ∈ (sd b y).support) : ∃ l ∈ y.support, l' ∈ (sdList b l).support := by
  classical
  rw [sd, Finsupp.linearCombination_apply, Finsupp.sum] at h
  obtain ⟨l, hl, hl'⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum h)
  exact ⟨l, hl, Finsupp.support_smul hl'⟩

/-- Mesh lemma for iterated barycentric subdivision (centroid barycenter): every simplex of the
`m`-fold subdivision of a `k`-simplex `l₀` of diameter `≤ d` has `k + 1` vertices in the hull of
`l₀` and pairwise distances `≤ (k/(k+1))^m * d`. -/
theorem mesh_sd_iterate (k : ℕ) (l₀ : List E) (d : ℝ) (hlen : l₀.length = k + 1)
    (hd : ∀ x ∈ l₀, ∀ y ∈ l₀, dist x y ≤ d) : ∀ m : ℕ,
    ∀ l' ∈ ((sd centroid)^[m] (single l₀ (1 : F2))).support,
    l'.length = k + 1 ∧ (∀ v ∈ l', v ∈ convexHull ℝ {x | x ∈ l₀}) ∧
      ∀ x ∈ l', ∀ y ∈ l', dist x y ≤ ((k : ℝ) / (k + 1)) ^ m * d := by
  intro m
  induction m with
  | zero =>
    intro l' hl'
    have : l' = l₀ := by simpa using Finsupp.support_single_subset hl'
    subst this
    exact ⟨hlen, fun v hv => subset_convexHull ℝ _ hv, fun x hx y hy => by simpa using hd x hx y hy⟩
  | succ m ih =>
    intro l' hl'
    rw [Function.iterate_succ_apply'] at hl'
    obtain ⟨l, hl, hl''⟩ := support_sd_subset centroid _ hl'
    obtain ⟨h1, h2, h3⟩ := ih l hl
    obtain ⟨g1, g2, g3⟩ := mesh_sdList k l _ h1 h3 l' hl''
    refine ⟨g1, fun v hv => ?_, fun x hx y hy => ?_⟩
    · have : convexHull ℝ {x | x ∈ l} ⊆ convexHull ℝ {x | x ∈ l₀} :=
        convexHull_min (fun v hv => h2 v hv) (convex_convexHull ℝ _)
      exact this (g2 v hv)
    · have := g3 x hx y hy
      rw [pow_succ]
      calc dist x y ≤ _ := this
        _ = _ := by ring


/-- Metric-form corollary of the mesh lemma. -/
theorem diam_mesh_sd_iterate (k : ℕ) (l₀ : List E) (d : ℝ) (hlen : l₀.length = k + 1)
    (hd : ∀ x ∈ l₀, ∀ y ∈ l₀, dist x y ≤ d) (m : ℕ)
    (l' : List E) (hl' : l' ∈ ((sd centroid)^[m] (single l₀ (1 : F2))).support) :
    Metric.diam {x | x ∈ l'} ≤ ((k : ℝ) / (k + 1)) ^ m * d := by
  obtain ⟨-, -, h⟩ := mesh_sd_iterate k l₀ d hlen hd m l' hl'
  have hd0 : 0 ≤ d := by
    have hne : l₀ ≠ [] := by intro h; subst h; simp at hlen
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l₀ hne
    exact (dist_nonneg).trans (hd a ha a ha)
  exact Metric.diam_le_of_forall_dist_le (by positivity) (fun x hx y hy => h x hx y hy)

/-- The vertices of the standard `n`-simplex, inside `Fin (n+1) → ℝ`. -/
noncomputable def stdVertices (n : ℕ) : List (Fin (n + 1) → ℝ) :=
  List.ofFn (fun i : Fin (n + 1) => (Pi.single i 1 : Fin (n + 1) → ℝ))

theorem stdVertices_length (n : ℕ) : (stdVertices n).length = n + 1 := by
  simp [stdVertices]

theorem stdVertices_dist (n : ℕ) : ∀ x ∈ stdVertices n, ∀ y ∈ stdVertices n, dist x y ≤ 1 := by
  classical
  intro x hx y hy
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
  refine (dist_pi_le_iff zero_le_one).mpr fun k => ?_
  simp only [Pi.single_apply, Real.dist_eq]
  split_ifs <;> norm_num

/-- The image of the standard simplex in `Fin (n+1) → ℝ` under the weights map. -/
def simplexSet (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  Set.range (fun t : StdSimplex ℝ (Fin (n + 1)) => (t.weights : Fin (n + 1) → ℝ))

theorem convex_simplexSet (n : ℕ) : Convex ℝ (simplexSet n) := by
  rw [simplexSet, StdSimplex.range_toFun_comp_weights]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx hy ⊢
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.1 i, hy.1 i, mul_nonneg ha (hx.1 i), mul_nonneg hb (hy.1 i)]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2, hy.2]
    linarith

theorem stdVertices_mem (n : ℕ) : ∀ v ∈ stdVertices n, v ∈ simplexSet n := by
  classical
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact ⟨StdSimplex.single i, by ext j; simp [Pi.single_apply, Finsupp.single_apply, eq_comm]⟩

theorem hull_stdVertices_subset (n : ℕ) :
    convexHull ℝ {x | x ∈ stdVertices n} ⊆ simplexSet n :=
  convexHull_min (fun v hv => stdVertices_mem n v hv) (convex_simplexSet n)


theorem isCompact_simplexSet (n : ℕ) : IsCompact (simplexSet n) :=
  isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous

/-- Lebesgue-number lemma for the standard simplex in the affine model: for a singular simplex
`σ` and an open cover `U`, for large `m` every simplex of the `m`-fold barycentric subdivision of
the standard simplex lies (as a convex hull of its vertices, read through the weights map) in
`σ⁻¹ A` for some `A ∈ U`. -/
theorem lebesgue_subdivision {X : Type*} [TopologicalSpace X] (n : ℕ)
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (U : Set (Set X)) (hU : ∀ A ∈ U, IsOpen A)
    (hcov : ⋃₀ U = Set.univ) :
    ∃ m : ℕ, ∀ l' ∈ ((sd centroid)^[m] (single (stdVertices n) (1 : F2))).support,
      ∃ A ∈ U, ∀ s : StdSimplex ℝ (Fin (n + 1)),
        (s.weights : Fin (n + 1) → ℝ) ∈ convexHull ℝ {x | x ∈ l'} → σ s ∈ A := by
  have hemb := StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))
  have hV : ∀ A : U, ∃ V : Set (Fin (n + 1) → ℝ), IsOpen V ∧
      (fun t : StdSimplex ℝ (Fin (n + 1)) => (t.weights : Fin (n + 1) → ℝ)) ⁻¹' V = σ ⁻¹' A.1 :=
    fun A => hemb.isInducing.isOpen_iff.mp ((hU A.1 A.2).preimage σ.continuous)
  choose V hVo hVeq using hV
  have hK : simplexSet n ⊆ ⋃ A : U, V A := by
    rintro _ ⟨t, rfl⟩
    have : σ t ∈ ⋃₀ U := by rw [hcov]; trivial
    obtain ⟨A, hA, hσ⟩ := this
    refine Set.mem_iUnion.mpr ⟨⟨A, hA⟩, ?_⟩
    have : t ∈ σ ⁻¹' A := hσ
    rw [← hVeq ⟨A, hA⟩] at this
    exact this
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (isCompact_simplexSet n) hVo hK
  have hr : (n : ℝ) / (n + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hδ hr
  refine ⟨m, fun l' hl' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := mesh_sd_iterate n (stdVertices n) 1 (stdVertices_length n)
    (stdVertices_dist n) m l' hl'
  have hne : l' ≠ [] := by intro h; subst h; simp at h1
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil l' hne
  have hvK : v ∈ simplexSet n := hull_stdVertices_subset n (h2 v hv)
  obtain ⟨A, hA⟩ := hball v hvK
  refine ⟨A.1, A.2, fun s hs => ?_⟩
  have hsub : convexHull ℝ {x | x ∈ l'} ⊆ Metric.closedBall v (((n : ℝ) / (n + 1)) ^ m * 1) :=
    convexHull_min (fun x hx => by
      rw [Metric.mem_closedBall, dist_comm]; exact h3 v hv x hx) (convex_closedBall _ _)
  have hmem : (s.weights : Fin (n + 1) → ℝ) ∈ Metric.ball v δ := by
    rw [Metric.mem_ball]
    have := hsub hs
    rw [Metric.mem_closedBall, mul_one] at this
    exact lt_of_le_of_lt this hm
  have : s ∈ (fun t : StdSimplex ℝ (Fin (n + 1)) => (t.weights : Fin (n + 1) → ℝ)) ⁻¹' V A :=
    hA hmem
  rw [hVeq A] at this
  exact this

end MeshLebesgue

end DGPS.Topology.SmallChains
