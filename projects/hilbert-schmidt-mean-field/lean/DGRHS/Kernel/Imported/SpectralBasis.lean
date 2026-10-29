/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in SpectralBasis.LICENSE.
Authors: Adam Benenson

MODIFIED for DGRHS September30 2026: narrow Hilbert-basis assembly port from
abenenson/compact-spectral commit72cd62dbdd4c397d26fc0c5777d60fea2211e938,
CompactSpectral/Analysis/InnerProductSpace/CompactSelfAdjoint/SpectralTheorem.lean.
Removed upstream approximation closure: use pinned Mathlib's compact symmetric
spectral completeness theorem. Namespace/imports adapted; no spectral axiom.
-/
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

namespace DGRHS.Kernel.Spectral
open scoped Topology
open Filter Topology
noncomputable section
universe u v
variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem iSup_eigenspace_orthogonal_eq_bot_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    (⨆ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT)

theorem exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
    (T : E →L[𝕜] E) (hT : IsSelfAdjoint T) (hTc : IsCompactOperator (T : E → E)) :
    ∃ (ι : Type (max u v)) (μ : ι → 𝕜) (b : HilbertBasis ι 𝕜 E),
      (∀ i, Module.End.HasEigenvector (T : E →ₗ[𝕜] E) (μ i) (b i)) := by
  classical
  let t : Module.End 𝕜 E := (T : E →ₗ[𝕜] E)
  have hSymm : t.IsSymmetric :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric (A := T)).1 hT
  -- Each eigenspace is closed (as a kernel), hence complete.
  have complete_eigenspace : ∀ μ : 𝕜, CompleteSpace (t.eigenspace μ) := by
    intro μ
    have hClosed : IsClosed ((t.eigenspace μ : Submodule 𝕜 E) : Set E) := by
      have :
          ((t.eigenspace μ : Submodule 𝕜 E) : Set E) =
            (LinearMap.ker ((T - μ • ContinuousLinearMap.id 𝕜 E : E →L[𝕜] E) :
              E →ₗ[𝕜] E) : Set E) := by
        ext x
        simp [t, LinearMap.mem_ker, sub_eq_zero]
      simpa [this] using
        (ContinuousLinearMap.isClosed_ker (f := (T - μ • ContinuousLinearMap.id 𝕜 E)))
    have : CompleteSpace ((t.eigenspace μ : Submodule 𝕜 E) : Set E) := hClosed.completeSpace_coe
    simpa using (inferInstance : CompleteSpace (t.eigenspace μ))
  -- Choose a Hilbert basis for each eigenspace, indexed by a set of vectors.
  classical
  choose w b hb using (fun μ : 𝕜 =>
    @exists_hilbertBasis 𝕜 _ (t.eigenspace μ) _ _ (complete_eigenspace μ))
  let ι : Type _ := Σ μ : 𝕜, w μ
  let μ' : ι → 𝕜 := fun i => i.1
  let v : ι → E := fun i => ((b i.1 i.2 : t.eigenspace i.1) : E)
  have hv_orthonormal : Orthonormal 𝕜 v := by
    refine ⟨?_, ?_⟩
    · intro i
      rcases i with ⟨μi, vi⟩
      -- `b μi` is orthonormal in the eigenspace.
      have h' : ‖(b μi vi : t.eigenspace μi)‖ = 1 := by
        have : Orthonormal 𝕜 (b μi) := (b μi).orthonormal
        exact this.norm_eq_one vi
      -- Coercion to `E` does not change the norm.
      simpa [v] using h'
    · intro i j hij
      rcases i with ⟨μi, vi⟩
      rcases j with ⟨μj, vj⟩
      by_cases hμ : μi = μj
      · subst hμ
        have hv' : Orthonormal 𝕜 (b μi) := (b μi).orthonormal
        have hij' : vi ≠ vj := by
          intro h
          exact hij (by simp [h])
        -- Orthonormality within one eigenspace.
        have : inner 𝕜 (b μi vi : t.eigenspace μi) (b μi vj : t.eigenspace μi) = 0 :=
          hv'.2 hij'
        simpa [v] using this
      · -- Distinct eigenspaces are orthogonal for symmetric operators.
        have hOrtho : t.eigenspace μi ⟂ t.eigenspace μj :=
          (hSymm.orthogonalFamily_eigenspaces).isOrtho hμ
        have : inner 𝕜 (b μi vi : E) (b μj vj : E) = 0 := by
          have hmem : (b μi vi : E) ∈ (t.eigenspace μj)ᗮ :=
            hOrtho (b μi vi).property
          have : inner 𝕜 (b μj vj : E) (b μi vi : E) = 0 :=
            (Submodule.mem_orthogonal (K := t.eigenspace μj) (v := (b μi vi : E))).1 hmem
              (b μj vj : E) (b μj vj).property
          simpa using (inner_eq_zero_symm.mp this)
        simpa [v] using this
  have hv_span_orth : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    -- If `x` is orthogonal to the span of all basis vectors in all eigenspaces,
    -- then `x` is orthogonal to every eigenspace, hence zero by compactness.
    ext x
    constructor
    · intro hx
      have hxv : ∀ i : ι, inner 𝕜 (v i) x = 0 := by
        have hx' : ∀ y, y ∈ Submodule.span 𝕜 (Set.range v) → inner 𝕜 y x = 0 :=
          (Submodule.mem_orthogonal (K := Submodule.span 𝕜 (Set.range v)) (v := x)).1 hx
        intro i
        exact hx' (v i) (Submodule.subset_span ⟨i, rfl⟩)
      have hx_eigs : x ∈ (⨆ μ : 𝕜, t.eigenspace μ)ᗮ := by
        -- Use `iInf_orthogonal` to show orthogonality to each eigenspace.
        have hx_each : ∀ μ : 𝕜, x ∈ (t.eigenspace μ)ᗮ := by
          intro μ
          -- Let `f : t.eigenspace μ →L[𝕜] 𝕜` be `y ↦ ⟪x, y⟫`.
          let f : (t.eigenspace μ) →L[𝕜] 𝕜 := (innerSL 𝕜 x).comp (t.eigenspace μ).subtypeL
          have hspan_le : Submodule.span 𝕜 (Set.range (b μ)) ≤ LinearMap.ker f.toLinearMap := by
            refine Submodule.span_le.2 ?_
            rintro _ ⟨i, rfl⟩
            change f (b μ i) = 0
            -- `x` is orthogonal to `b μ i`, since it appears among the `v`'s.
            have : inner 𝕜 x (b μ i : E) = 0 := by
              have : inner 𝕜 (b μ i : E) x = 0 := by
                -- This is `hxv` at index `⟨μ, i⟩`.
                simpa [v] using hxv ⟨μ, i⟩
              simpa using (inner_eq_zero_symm.mp this)
            simpa [f, ContinuousLinearMap.comp_apply] using this
          have hker_closed : IsClosed ((LinearMap.ker f.toLinearMap : Set (t.eigenspace μ))) := by
            simpa using (ContinuousLinearMap.isClosed_ker (f := f))
          have htop :
              (Submodule.span 𝕜 (Set.range (b μ))).topologicalClosure = ⊤ :=
            HilbertBasis.dense_span (b μ)
          have htop_le :
              (⊤ : Submodule 𝕜 (t.eigenspace μ)) ≤ LinearMap.ker f.toLinearMap := by
            -- The kernel is closed and contains a dense submodule, hence is `⊤`.
            have :
                (Submodule.span 𝕜 (Set.range (b μ))).topologicalClosure ≤
                  LinearMap.ker f.toLinearMap :=
              Submodule.topologicalClosure_minimal
                (Submodule.span 𝕜 (Set.range (b μ))) hspan_le hker_closed
            simpa [htop] using this
          have hf0 : ∀ y, f y = 0 := by
            intro y
            have : y ∈ LinearMap.ker f.toLinearMap := htop_le (by simp)
            simpa [LinearMap.mem_ker] using this
          -- Conclude `x` is orthogonal to the whole eigenspace.
          refine (Submodule.mem_orthogonal (K := t.eigenspace μ) (v := x)).2 ?_
          intro y hy
          have : inner 𝕜 x y = 0 := by
            -- `y` is a vector in the eigenspace, viewed as a subtype element.
            have : f ⟨y, hy⟩ = 0 := hf0 ⟨y, hy⟩
            simpa [f, ContinuousLinearMap.comp_apply] using this
          simpa using (inner_eq_zero_symm.mp this)
        -- Now package the pointwise orthogonality.
        have hx_inf : x ∈ ⨅ μ : 𝕜, (t.eigenspace μ)ᗮ := by
          refine (Submodule.mem_iInf (p := fun μ : 𝕜 => (t.eigenspace μ)ᗮ) (x := x)).2 ?_
          intro μ
          exact hx_each μ
        simpa [Submodule.iInf_orthogonal] using hx_inf
      have hx0 : x = 0 := by
        have hxbot : x ∈ (⊥ : Submodule 𝕜 E) := by
          have :
              (⨆ μ : 𝕜, t.eigenspace μ)ᗮ = (⊥ : Submodule 𝕜 E) :=
            iSup_eigenspace_orthogonal_eq_bot_of_isCompactOperator_of_isSelfAdjoint
              (𝕜 := 𝕜) (E := E) T hT hTc
          simpa [this] using hx_eigs
        simpa using hxbot
      simp [hx0]
    · intro hx0
      subst hx0
      simp
  refine ⟨ι, μ', HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth, ?_⟩
  intro i
  rcases i with ⟨μi, vi⟩
  -- Show each basis vector is a nonzero vector in the `μi`-eigenspace.
  have hmem : (v ⟨μi, vi⟩) ∈ t.eigenspace μi := by
    -- `b μi vi` is an element of the eigenspace subtype.
    simp [v]
  have hne0 : v ⟨μi, vi⟩ ≠ 0 := by
    have hv' : Orthonormal 𝕜 v := hv_orthonormal
    have hv_norm : ‖v ⟨μi, vi⟩‖ = 1 := hv'.1 ⟨μi, vi⟩
    have hv_norm_ne : ‖v ⟨μi, vi⟩‖ ≠ 0 := by
      simp [hv_norm]
    exact (norm_ne_zero_iff.1 hv_norm_ne)
  -- Identify `b`'s coerced family with `v`.
  have hb' :
      (HilbertBasis.mkOfOrthogonalEqBot hv_orthonormal hv_span_orth) ⟨μi, vi⟩ = v ⟨μi, vi⟩ := by
    exact congrArg (fun f : ι → E => f ⟨μi, vi⟩)
      (HilbertBasis.coe_mkOfOrthogonalEqBot hv_orthonormal hv_span_orth)
  -- Conclude.
  refine (Module.End.hasEigenvector_iff.mpr ?_)
  refine ⟨?_, ?_⟩
  · simpa [μ', hb', t] using hmem
  · simpa [hb'] using hne0
end
end DGRHS.Kernel.Spectral
#print axioms DGRHS.Kernel.Spectral.exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
#check DGRHS.Kernel.Spectral.exists_hilbertBasis_hasEigenvector_of_isCompactOperator_of_isSelfAdjoint
