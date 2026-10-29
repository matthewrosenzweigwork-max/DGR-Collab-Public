import DGPS.Topology.SingularAdapter
import DGPS.Topology.ContractibleHomology
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Relative chain quotient (TOP002)

For a subspace `A` of `X`, the singular chains on `A` inject into those on `X`, and the degreewise
quotient is the relative chain complex `C(X,A;F2)`, whose homology `H_n(X,A;F2)` is functorial for
maps of pairs.  A pair is a monomorphism `i : A ⟶ X` in `TopCat` (an injective continuous map;
subspace inclusions are the motivating case, see `TopPair.ofSet`); maps of pairs are commuting
squares.  The relative chain complex is Mathlib's `SSetPair.chainComplex` for the singular
simplicial sets, i.e. the cokernel of `singularChains.map i`, computed degreewise.

* `DGPS.Topology.TopPair`, `DGPS.Topology.TopPair.ofSet`, `DGPS.Topology.TopPair.empty`.
* `DGPS.Topology.relativeChains : TopPair ⥤ ChainComplex F2Mod ℕ`, with quotient map
  `relativeChainsπ`.
* `DGPS.Topology.relativeHomology n : TopPair ⥤ F2Mod`.
* `DGPS.Topology.relative_chain_quotient`: the packet interface.

The exact sequence of a pair (TOP003) is appended at the end: `connectingHomology`,
`reducedHomology`, `exact_sequence_of_a_pair`.
-/

open CategoryTheory CategoryTheory.Limits

namespace DGPS.Topology

/-- Pairs of spaces: monomorphisms `A ⟶ X` in `TopCat`, with commuting squares as morphisms. -/
abbrev TopPair : Type 1 := MorphismProperty.Arrow (MorphismProperty.monomorphisms TopCat.{0}) ⊤ ⊤

/-- The pair given by an injective continuous map `i : A ⟶ X`. -/
abbrev TopPair.of {A X : TopCat.{0}} (i : A ⟶ X) [Mono i] : TopPair :=
  MorphismProperty.Arrow.mk i (by assumption)

instance (P : TopPair) : Mono P.hom := P.prop

theorem mono_ofSetInclusion (X : TopCat.{0}) (A : Set X) :
    Mono (TopCat.ofHom (X := TopCat.of A) (Y := X) ⟨Subtype.val, continuous_subtype_val⟩) :=
  (TopCat.mono_iff_injective _).2 Subtype.val_injective

theorem mono_emptyInclusion (X : TopCat.{0}) :
    Mono (TopCat.ofHom (X := TopCat.of PEmpty.{1}) (Y := X)
      ⟨fun e => e.elim, continuous_of_discreteTopology⟩) :=
  (TopCat.mono_iff_injective _).2 (fun a => a.elim)

/-- The pair `(X, A)` for a subset `A` of `X` with the subspace topology. -/
noncomputable def TopPair.ofSet (X : TopCat.{0}) (A : Set X) : TopPair :=
  haveI := mono_ofSetInclusion X A
  TopPair.of (TopCat.ofHom (X := TopCat.of A) (Y := X) ⟨Subtype.val, continuous_subtype_val⟩)

/-- The pair `(X, ∅)`. -/
noncomputable def TopPair.empty (X : TopCat.{0}) : TopPair :=
  haveI := mono_emptyInclusion X
  TopPair.of (TopCat.ofHom (X := TopCat.of PEmpty.{1}) (Y := X)
    ⟨fun e => e.elim, continuous_of_discreteTopology⟩)

/-- Singular simplicial sets of a pair of spaces, as a pair of simplicial sets. -/
noncomputable def TopPair.toSSetPair : TopPair ⥤ SSetPair.{0} where
  obj P := haveI : Mono (TopCat.toSSet.map P.hom) := inferInstance
    SSetPair.of (TopCat.toSSet.map P.hom)
  map f := SSetPair.homMk (TopCat.toSSet.map f.left) (TopCat.toSSet.map f.right)
    (by
      show TopCat.toSSet.map f.left ≫ TopCat.toSSet.map _ = TopCat.toSSet.map _ ≫ TopCat.toSSet.map f.right
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ f.w)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The relative singular chain complex `C(X,A;F2)` as a functor on pairs: the degreewise
quotient of the chains on `X` by the subcomplex of chains on `A`. -/
noncomputable def relativeChains : TopPair ⥤ ChainComplex F2Mod ℕ :=
  TopPair.toSSetPair ⋙ (SSetPair.chainComplexFunctor.{0} F2Mod).obj coeffModule

/-- The quotient map `C(X;F2) ⟶ C(X,A;F2)`. -/
noncomputable def relativeChainsπ (P : TopPair) :
    singularChains.obj P.right ⟶ relativeChains.obj P :=
  SSetPair.chainComplexπ (TopPair.toSSetPair.obj P) coeffModule

/-- Relative singular homology `H_n(X,A;F2)`. -/
noncomputable def relativeHomology (n : ℕ) : TopPair ⥤ F2Mod :=
  relativeChains ⋙ HomologicalComplex.homologyFunctor F2Mod (ComplexShape.down ℕ) n

/-- Constructor for morphisms of pairs. -/
abbrev TopPair.homMk {P Q : TopPair} (left : P.left ⟶ Q.left) (right : P.right ⟶ Q.right)
    (w : left ≫ Q.hom = P.hom ≫ right) : P ⟶ Q :=
  MorphismProperty.Arrow.Hom.mk (Arrow.homMk left right w) (by simp) (by simp)

/-- The functor `X ↦ (X, ∅)`. -/
noncomputable def emptyPairFunctor : TopCat.{0} ⥤ TopPair where
  obj X := TopPair.empty X
  map f := TopPair.homMk (𝟙 _) f (by ext e; exact e.elim)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem relativeChainsπ_naturality {P Q : TopPair} (f : P ⟶ Q) :
    singularChains.map f.right ≫ relativeChainsπ Q = relativeChainsπ P ≫ relativeChains.map f :=
  (((SSetPair.chainComplexFunctorπ.{0} F2Mod).app coeffModule).naturality
    (TopPair.toSSetPair.map f)).symm.symm

theorem isIso_relativeChainsπ_of_isEmpty (P : TopPair) [IsEmpty P.left] :
    IsIso (relativeChainsπ P) := by
  have : (TopPair.toSSetPair.obj P).left.HasDimensionLT 0 := by
    rw [← SSet.notNonempty_iff_hasDimensionLT_zero]
    rintro ⟨x⟩
    have f := TopCat.toSSetObjEquiv P.left _ x
    obtain ⟨y⟩ : Nonempty (Convexity.StdSimplex ℝ (Fin (0 + 1))) := inferInstance
    exact IsEmpty.false (f y)
  exact SSetPair.isIso_chainComplexπ _ _

theorem relativeChains_condition (P : TopPair) :
    singularChains.map P.hom ≫ relativeChainsπ P = 0 :=
  SSetPair.chainComplex_condition (TopPair.toSSetPair.obj P) coeffModule

theorem relativeChains_condition_f (P : TopPair) (n : ℕ) :
    (singularChains.map P.hom).f n ≫ (relativeChainsπ P).f n = 0 :=
  SSetPair.chainComplex_condition_f (TopPair.toSSetPair.obj P) coeffModule n

/-- The natural isomorphism `C(X,∅;F2) ≅ C(X;F2)`. -/
noncomputable def relativeChainsEmptyIso :
    singularChains ≅ emptyPairFunctor ⋙ relativeChains :=
  NatIso.ofComponents
    (fun X =>
      haveI : IsEmpty (emptyPairFunctor.obj X).left := inferInstanceAs (IsEmpty PEmpty)
      @asIso _ _ _ _ (relativeChainsπ (emptyPairFunctor.obj X))
        (isIso_relativeChainsπ_of_isEmpty (emptyPairFunctor.obj X)))
    (fun g => relativeChainsπ_naturality (emptyPairFunctor.map g))

/-- The natural isomorphism `H_n(X,∅;F2) ≅ H_n(X;F2)`. -/
noncomputable def relativeHomologyEmptyIso (n : ℕ) :
    singularHomology n ≅ emptyPairFunctor ⋙ relativeHomology n :=
  Functor.isoWhiskerRight relativeChainsEmptyIso
    (HomologicalComplex.homologyFunctor F2Mod (ComplexShape.down ℕ) n)

/-- Packet interface. For a pair `i : A ⟶ X` (an injective map; e.g. a subspace inclusion):
the chains on `A` inject into those on `X` (degreewise and as a chain map); the relative chain
complex is the degreewise quotient by this subcomplex (short exact sequence, degreewise
cokernels); relative homology is the homology of this complex and is functorial for maps of
pairs, compatibly with the quotient maps; for empty `A` the quotient map is an isomorphism, and
`(X, ∅)` agrees naturally in `X` with absolute chains and homology. -/
theorem relative_chain_quotient :
    (∀ (P : TopPair) (n : ℕ), Mono ((singularChains.map P.hom).f n)) ∧
    (∀ P : TopPair, Mono (singularChains.map P.hom)) ∧
    (∀ P : TopPair, (ShortComplex.mk _ _ (relativeChains_condition P)).ShortExact) ∧
    (∀ (P : TopPair) (n : ℕ),
      Nonempty (IsColimit (CokernelCofork.ofπ ((relativeChainsπ P).f n)
        (relativeChains_condition_f P n)))) ∧
    (∀ (n : ℕ) (P : TopPair), (relativeHomology n).obj P =
      (relativeChains.obj P).homology n) ∧
    (∀ P : TopPair, relativeChains.map (𝟙 P) = 𝟙 (relativeChains.obj P)) ∧
    (∀ {P Q R : TopPair} (f : P ⟶ Q) (g : Q ⟶ R),
      relativeChains.map (f ≫ g) = relativeChains.map f ≫ relativeChains.map g) ∧
    (∀ (n : ℕ) (P : TopPair), (relativeHomology n).map (𝟙 P) = 𝟙 ((relativeHomology n).obj P)) ∧
    (∀ (n : ℕ) {P Q R : TopPair} (f : P ⟶ Q) (g : Q ⟶ R),
      (relativeHomology n).map (f ≫ g) = (relativeHomology n).map f ≫ (relativeHomology n).map g) ∧
    (∀ (n : ℕ) {P Q : TopPair} (f : P ⟶ Q),
      (relativeHomology n).map f = HomologicalComplex.homologyMap (relativeChains.map f) n) ∧
    (∀ {P Q : TopPair} (f : P ⟶ Q),
      singularChains.map f.right ≫ relativeChainsπ Q = relativeChainsπ P ≫ relativeChains.map f) ∧
    (∀ (P : TopPair), IsEmpty P.left → IsIso (relativeChainsπ P)) ∧
    (∀ (X : TopCat.{0}) (A : Set X), A = ∅ → IsIso (relativeChainsπ (TopPair.ofSet X A))) ∧
    Nonempty (singularChains ≅ emptyPairFunctor ⋙ relativeChains) ∧
    (∀ n : ℕ, Nonempty (singularHomology n ≅ emptyPairFunctor ⋙ relativeHomology n)) := by
  refine ⟨fun P n => ?_, fun P => ?_, fun P => ?_, fun P n => ?_, fun _ _ => rfl,
    fun P => relativeChains.map_id P, fun f g => relativeChains.map_comp f g,
    fun n P => (relativeHomology n).map_id P, fun n _ _ _ f g => (relativeHomology n).map_comp f g,
    fun n _ _ f => rfl, fun f => relativeChainsπ_naturality f,
    fun P _ => isIso_relativeChainsπ_of_isEmpty P, fun X A hA => ?_,
    ⟨relativeChainsEmptyIso⟩, fun n => ⟨relativeHomologyEmptyIso n⟩⟩
  · exact inferInstanceAs (Mono ((SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom
      coeffModule).f n))
  · exact inferInstanceAs (Mono (SSet.chainComplexMap (TopPair.toSSetPair.obj P).hom
      coeffModule))
  · exact SSetPair.shortExact_chainComplexShortComplex (TopPair.toSSetPair.obj P) coeffModule
  · exact ⟨SSetPair.isColimitCokernelCoforkChainComplexX (TopPair.toSSetPair.obj P) coeffModule n⟩
  · subst hA
    have : IsEmpty (TopPair.ofSet X ∅).left := inferInstanceAs (IsEmpty (∅ : Set X))
    exact isIso_relativeChainsπ_of_isEmpty _

/-! ## Exact sequence of a pair (TOP003) -/

section ExactSequence

open HomologicalComplex

/-- The short complex of chain complexes `C(A) ⟶ C(X) ⟶ C(X,A)` of a pair. -/
noncomputable def pairShortComplex (P : TopPair) : ShortComplex (ChainComplex F2Mod ℕ) :=
  ShortComplex.mk _ _ (relativeChains_condition P)

theorem pairShortComplex_shortExact (P : TopPair) : (pairShortComplex P).ShortExact :=
  SSetPair.shortExact_chainComplexShortComplex (TopPair.toSSetPair.obj P) coeffModule

/-- A map of pairs induces a morphism of the short exact sequences of chain complexes. -/
noncomputable def pairShortComplexMap {P Q : TopPair} (f : P ⟶ Q) :
    pairShortComplex P ⟶ pairShortComplex Q :=
  ShortComplex.homMk (singularChains.map f.left) (singularChains.map f.right)
    (relativeChains.map f)
    (by
      show singularChains.map f.left ≫ singularChains.map Q.hom =
        singularChains.map P.hom ≫ singularChains.map f.right
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ f.w)
    (relativeChainsπ_naturality f)

/-- The connecting homomorphism `∂ : H_{n+1}(X,A) ⟶ H_n(A)` of the pair `(X,A)`. -/
noncomputable def connectingHomology (n : ℕ) (P : TopPair) :
    (relativeHomology (n + 1)).obj P ⟶ (singularHomology n).obj P.left :=
  (pairShortComplex_shortExact P).δ (n + 1) n rfl

/-- The segment `H_n(A) ⟶ H_n(X) ⟶ H_n(X,A)` of the long exact sequence. -/
noncomputable def pairHomologyComplex₂ (n : ℕ) (P : TopPair) : ShortComplex F2Mod :=
  ShortComplex.mk (homologyMap (singularChains.map P.hom) n)
    (homologyMap (relativeChainsπ P) n)
    (by rw [← homologyMap_comp, relativeChains_condition, homologyMap_zero])

/-- The segment `H_{n+1}(X) ⟶ H_{n+1}(X,A) ⟶ H_n(A)` of the long exact sequence. -/
noncomputable def pairHomologyComplex₃ (n : ℕ) (P : TopPair) : ShortComplex F2Mod :=
  ShortComplex.mk (homologyMap (relativeChainsπ P) (n + 1)) (connectingHomology n P)
    ((pairShortComplex_shortExact P).comp_δ (n + 1) n rfl)

/-- The segment `H_{n+1}(X,A) ⟶ H_n(A) ⟶ H_n(X)` of the long exact sequence. -/
noncomputable def pairHomologyComplex₁ (n : ℕ) (P : TopPair) : ShortComplex F2Mod :=
  ShortComplex.mk (connectingHomology n P) (homologyMap (singularChains.map P.hom) n)
    ((pairShortComplex_shortExact P).δ_comp (n + 1) n rfl)

/-- Reduced singular homology with `F2` coefficients: in degree `0` the kernel of the map to the
homology of a point, in positive degree the ordinary homology. -/
noncomputable def reducedHomology : ℕ → TopCat.{0} → F2Mod
  | 0, A => kernel ((singularHomology 0).map
      (TopCat.ofHom (X := A) (Y := TopCat.of PUnit.{1}) ⟨fun _ => PUnit.unit, continuous_const⟩))
  | m + 1, A => (singularHomology (m + 1)).obj A

/-- The inclusion of reduced homology into ordinary homology. -/
noncomputable def reducedHomologyι : (m : ℕ) → (A : TopCat.{0}) →
    (reducedHomology m A ⟶ (singularHomology m).obj A)
  | 0, _ => kernel.ι _
  | _ + 1, _ => 𝟙 _

theorem isIso_homology_toPoint_of_contractible (X : TopCat.{0}) [ContractibleSpace X] :
    IsIso ((singularHomology 0).map
      (TopCat.ofHom (X := X) (Y := TopCat.of PUnit.{1}) ⟨fun _ => PUnit.unit, continuous_const⟩)) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic X
  let c : X ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let p : TopCat.of PUnit.{1} ⟶ X := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  have hid : (singularHomology 0).map (𝟙 X) = (singularHomology 0).map (c ≫ p) :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      (f := 𝟙 X) (g := c ≫ p) H coeffModule 0
  refine ⟨(singularHomology 0).map p, ?_, ?_⟩
  · rw [← (singularHomology 0).map_comp, ← hid, (singularHomology 0).map_id]
  · rw [← (singularHomology 0).map_comp]
    have : p ≫ c = 𝟙 _ := by ext x
    rw [this, (singularHomology 0).map_id]

theorem cycle_aux {S : ShortComplex (ChainComplex F2Mod ℕ)} (hS : Mono S.f) {M : F2Mod} {n : ℕ}
    (x₁ : M ⟶ S.X₁.X n) (x₂ : M ⟶ S.X₂.X (n + 1))
    (hx₁ : x₁ ≫ S.f.f n = x₂ ≫ S.X₂.d (n + 1) n) (k : ℕ) : x₁ ≫ S.X₁.d n k = 0 := by
  rw [← cancel_mono (S.f.f k), Category.assoc, ← S.f.comm, reassoc_of% hx₁, d_comp_d,
    comp_zero, zero_comp]

/-- Elements of the description of the connecting map: if `x₃` is a relative cycle with lift
`x₂` to `C_{n+1}(X)` and `∂ x₂` comes from `x₁ ∈ C_n(A)`, then the connecting map sends the class
of `x₃` to the class of `x₁`. -/
theorem connectingHomology_eq (n : ℕ) (P : TopPair) {M : F2Mod}
    (x₃ : M ⟶ (relativeChains.obj P).X (n + 1)) (hx₃ : x₃ ≫ (relativeChains.obj P).d (n + 1) n = 0)
    (x₂ : M ⟶ (singularChains.obj P.right).X (n + 1))
    (hx₂ : x₂ ≫ (relativeChainsπ P).f (n + 1) = x₃)
    (x₁ : M ⟶ (singularChains.obj P.left).X n)
    (hx₁ : x₁ ≫ (singularChains.map P.hom).f n = x₂ ≫ (singularChains.obj P.right).d (n + 1) n)
    (k : ℕ) (hk : (ComplexShape.down ℕ).next n = k) :
    (relativeChains.obj P).liftCycles x₃ n (by simp) hx₃ ≫ (relativeChains.obj P).homologyπ (n + 1) ≫
        connectingHomology n P =
      (singularChains.obj P.left).liftCycles x₁ k hk
        (cycle_aux (pairShortComplex_shortExact P).mono_f x₁ x₂ hx₁ k)
        ≫ (singularChains.obj P.left).homologyπ n := by
  exact (pairShortComplex_shortExact P).δ_eq (n + 1) n rfl x₃ hx₃ x₂ hx₂ x₁ hx₁ k hk


theorem pairHomologyComplex₁_exact (n : ℕ) (P : TopPair) : (pairHomologyComplex₁ n P).Exact :=
  (pairShortComplex_shortExact P).homology_exact₁ (n + 1) n rfl

theorem pairHomologyComplex₂_exact (n : ℕ) (P : TopPair) : (pairHomologyComplex₂ n P).Exact :=
  (pairShortComplex_shortExact P).homology_exact₂ n

theorem pairHomologyComplex₃_exact (n : ℕ) (P : TopPair) : (pairHomologyComplex₃ n P).Exact :=
  (pairShortComplex_shortExact P).homology_exact₃ (n + 1) n rfl

theorem connectingHomology_naturality (n : ℕ) {P Q : TopPair} (f : P ⟶ Q) :
    connectingHomology n P ≫ (singularHomology n).map f.left =
      (relativeHomology (n + 1)).map f ≫ connectingHomology n Q :=
  HomologicalComplex.HomologySequence.δ_naturality (pairShortComplexMap f) (pairShortComplex_shortExact P)
    (pairShortComplex_shortExact Q) (n + 1) n rfl

theorem kernel_comp_mono_aux {A B C : F2Mod} (g : A ⟶ B) (m : B ⟶ C) [Mono m] (t : A ⟶ C)
    (hc : t = g ≫ m) : ∃ e : kernel t ≅ kernel g, e.inv ≫ kernel.ι t = kernel.ι g := by
  refine ⟨kernelIsoOfEq hc ≪≫ kernelCompMono g m, ?_⟩
  simp [kernelCompMono]

theorem contractible_relative_homology (P : TopPair) [ContractibleSpace P.right] (m : ℕ) :
    ∃ e : (relativeHomology (m + 1)).obj P ≅ reducedHomology m P.left,
      e.hom ≫ reducedHomologyι m P.left = connectingHomology m P := by
  have hS := pairShortComplex_shortExact P
  have h1 : ∀ k, 0 < k → IsZero ((singularHomology k).obj P.right) := fun k hk =>
    contractible_positive_degree_homology P.right k hk
  cases m with
  | zero =>
    have hmono : Mono (connectingHomology 0 P) := hS.mono_δ 1 0 rfl (h1 1 one_pos)
    have : Mono (pairHomologyComplex₁ 0 P).f := hmono
    have hk : IsLimit (KernelFork.ofι (connectingHomology 0 P)
        (pairHomologyComplex₁ 0 P).zero) := (pairHomologyComplex₁_exact 0 P).fIsKernel
    let cX : P.right ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    have : IsIso ((singularHomology 0).map cX) := isIso_homology_toPoint_of_contractible P.right
    have hm : Mono ((singularHomology 0).map cX) := inferInstance
    let cA : P.left ⟶ TopCat.of PUnit.{1} := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
    have hc : (singularHomology 0).map cA =
        (singularHomology 0).map P.hom ≫ (singularHomology 0).map cX :=
      (congrArg _ (rfl : cA = P.hom ≫ cX)).trans ((singularHomology 0).map_comp P.hom cX)
    obtain ⟨e₂, h₂⟩ := kernel_comp_mono_aux ((singularHomology 0).map P.hom)
      ((singularHomology 0).map cX) ((singularHomology 0).map cA) hc
    let e₁ : (relativeHomology 1).obj P ≅ kernel ((singularHomology 0).map P.hom) :=
      IsLimit.conePointUniqueUpToIso hk (limit.isLimit _)
    have h₁ : e₁.hom ≫ kernel.ι ((singularHomology 0).map P.hom) = connectingHomology 0 P :=
      IsLimit.conePointUniqueUpToIso_hom_comp hk (limit.isLimit _) WalkingParallelPair.zero
    refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
    exact (Category.assoc _ _ _).trans ((congrArg (e₁.hom ≫ ·) h₂).trans h₁)
  | succ k =>
    have : IsIso (connectingHomology (k + 1) P) := hS.isIso_δ (k + 2) (k + 1) rfl (h1 (k + 2) (by omega)) (h1 (k + 1) (by omega))
    exact ⟨@asIso _ _ _ _ (connectingHomology (k + 1) P) this, by simp only [reducedHomologyι]; rfl⟩

theorem homologyMap_incl_naturality (n : ℕ) {P Q : TopPair} (f : P ⟶ Q) :
    (singularHomology n).map f.left ≫ (singularHomology n).map Q.hom =
      (singularHomology n).map P.hom ≫ (singularHomology n).map f.right := by
  rw [← (singularHomology n).map_comp, ← (singularHomology n).map_comp]
  exact congrArg _ f.w

theorem homologyMap_quot_naturality (n : ℕ) {P Q : TopPair} (f : P ⟶ Q) :
    (singularHomology n).map f.right ≫ homologyMap (relativeChainsπ Q) n =
      homologyMap (relativeChainsπ P) n ≫ (relativeHomology n).map f := by
  show homologyMap (singularChains.map f.right) n ≫ _ = _ ≫ homologyMap (relativeChains.map f) n
  rw [← homologyMap_comp, ← homologyMap_comp, relativeChainsπ_naturality]

/-- Packet interface. For a pair `(X,A)` (`P.left = A`, `P.right = X`) the short exact sequence of
chain complexes `C(A) ⟶ C(X) ⟶ C(X,A)` induces the long exact homology sequence: exactness at
`H_n(X)`, at `H_{n+1}(X,A)` and at `H_n(A)`, with connecting map `connectingHomology`.  The
connecting map is natural for maps of pairs (and so are the other maps of the sequence), and sends
the class of a relative cycle `x₃` to the class of the boundary `x₁ ∈ C_n(A)` of any lift
`x₂ ∈ C_{n+1}(X)` (the description is given for generalized elements `M ⟶ -`, `M` any module).
If `X` is contractible then `H_{m+1}(X,A)` is isomorphic, via the connecting map, to reduced
homology `H̃_m(A)` (`reducedHomology`; in degree `0` the kernel of `H_0(A) ⟶ H_0(pt)`). -/
theorem exact_sequence_of_a_pair :
    (∀ (n : ℕ) (P : TopPair), (pairHomologyComplex₂ n P).Exact) ∧
    (∀ (n : ℕ) (P : TopPair), (pairHomologyComplex₃ n P).Exact) ∧
    (∀ (n : ℕ) (P : TopPair), (pairHomologyComplex₁ n P).Exact) ∧
    (∀ (n : ℕ) {P Q : TopPair} (f : P ⟶ Q),
      connectingHomology n P ≫ (singularHomology n).map f.left =
        (relativeHomology (n + 1)).map f ≫ connectingHomology n Q) ∧
    (∀ (n : ℕ) {P Q : TopPair} (f : P ⟶ Q),
      (singularHomology n).map f.left ≫ (singularHomology n).map Q.hom =
        (singularHomology n).map P.hom ≫ (singularHomology n).map f.right) ∧
    (∀ (n : ℕ) {P Q : TopPair} (f : P ⟶ Q),
      (singularHomology n).map f.right ≫ homologyMap (relativeChainsπ Q) n =
        homologyMap (relativeChainsπ P) n ≫ (relativeHomology n).map f) ∧
    (∀ (n : ℕ) (P : TopPair) {M : F2Mod}
      (x₃ : M ⟶ (relativeChains.obj P).X (n + 1))
      (hx₃ : x₃ ≫ (relativeChains.obj P).d (n + 1) n = 0)
      (x₂ : M ⟶ (singularChains.obj P.right).X (n + 1))
      (_hx₂ : x₂ ≫ (relativeChainsπ P).f (n + 1) = x₃)
      (x₁ : M ⟶ (singularChains.obj P.left).X n)
      (hx₁ : x₁ ≫ (singularChains.map P.hom).f n = x₂ ≫ (singularChains.obj P.right).d (n + 1) n)
      (k : ℕ) (hk : (ComplexShape.down ℕ).next n = k),
      (relativeChains.obj P).liftCycles x₃ n (by simp) hx₃ ≫
          (relativeChains.obj P).homologyπ (n + 1) ≫ connectingHomology n P =
        (singularChains.obj P.left).liftCycles x₁ k hk
          (cycle_aux (pairShortComplex_shortExact P).mono_f x₁ x₂ hx₁ k) ≫
          (singularChains.obj P.left).homologyπ n) ∧
    (∀ (P : TopPair) [ContractibleSpace P.right] (m : ℕ),
      ∃ e : (relativeHomology (m + 1)).obj P ≅ reducedHomology m P.left,
        e.hom ≫ reducedHomologyι m P.left = connectingHomology m P) :=
  ⟨fun n P => pairHomologyComplex₂_exact n P, fun n P => pairHomologyComplex₃_exact n P,
    fun n P => pairHomologyComplex₁_exact n P, fun n _ _ f => connectingHomology_naturality n f,
    fun n _ _ f => homologyMap_incl_naturality n f, fun n _ _ f => homologyMap_quot_naturality n f,
    fun n P _ x₃ hx₃ x₂ hx₂ x₁ hx₁ k hk => connectingHomology_eq n P x₃ hx₃ x₂ hx₂ x₁ hx₁ k hk,
    fun P _ m => contractible_relative_homology P m⟩

end ExactSequence

end DGPS.Topology
