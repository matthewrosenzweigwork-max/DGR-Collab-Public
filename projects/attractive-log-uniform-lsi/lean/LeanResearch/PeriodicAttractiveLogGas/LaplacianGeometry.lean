/-
The invariance and locality proofs below are adapted from the Tau Ceti contributors,
TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean and Harmonic/Isometry.lean,
immutable commit d969ec21da00439b0479ee3923df9008da718365 (Apache 2.0).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The exact sources, hashes, and retained license are recorded in
research/discovery/laplacian-geometry-reuse.json. No TauCeti module is imported.
-/
import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Affine.Isometry

/-! Geometric changes of variables and support locality for the ordinary
Euclidean Laplacian. These results do not assert Weyl regularity. -/

noncomputable section

open InnerProductSpace Laplacian Filter Topology

namespace PeriodicAttractiveLogGas

section EuclideanGeometry

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem iteratedFDeriv_comp_isometry_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m =
      iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- The Laplacian commutes with a linear isometry of its domain. -/
theorem laplacian_comp_linearIsometryEquiv_right (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_isometry_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- The Laplacian commutes with translation of its domain. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- Reflection about a translated origin introduces two cancelling derivative signs. -/
theorem laplacian_comp_const_sub (f : E → F) (a : E) :
    Δ (fun y ↦ f (a - y)) = fun y ↦ (Δ f) (a - y) := by
  have h := laplacian_comp_linearIsometryEquiv_right
    (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E) (fun y ↦ f (y + a))
  rw [laplacian_comp_add_right] at h
  simpa only [Function.comp_def, LinearIsometryEquiv.coe_neg,
    sub_eq_add_neg, add_comm] using h

/-- The topological support of the Laplacian lies in that of the function. -/
theorem tsupport_laplacian_subset (f : E → F) : tsupport (Δ f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx ↦ ?_) (isClosed_tsupport f)
  by_contra hxf
  have h0 : Δ f =ᶠ[𝓝 x] Δ (fun _ : E ↦ (0 : F)) :=
    laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hxf)
  exact hx (by simpa using h0.eq_of_nhds)

/-- Harmonicity transports across a linear isometry of the domain. -/
theorem harmonicAt_comp_linearIsometryEquiv_right_iff (l : E ≃ₗᵢ[ℝ] E') {f : E' → F}
    {x : E} : HarmonicAt (f ∘ l) x ↔ HarmonicAt f (l x) := by
  have hcd : ContDiffAt ℝ 2 (f ∘ l) x ↔ ContDiffAt ℝ 2 f (l x) := by
    have := l.toContinuousLinearEquiv.contDiffAt_comp_iff (f := f) (n := 2) (x := l x)
    simpa using this
  have hlap : (Δ (f ∘ l) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (l x)] 0) := by
    rw [laplacian_comp_linearIsometryEquiv_right l f]
    change (Δ f ∘ l.toHomeomorph =ᶠ[𝓝 x] 0) ↔
      (Δ f =ᶠ[𝓝 (l.toHomeomorph x)] 0)
    rw [← l.toHomeomorph.map_nhds_eq x]
    change (Δ f ∘ l.toHomeomorph =ᶠ[𝓝 x] (0 : E' → F) ∘ l.toHomeomorph) ↔
      (Δ f =ᶠ[Filter.map l.toHomeomorph (𝓝 x)] (0 : E' → F))
    exact (Filter.eventuallyEq_map (f := 𝓝 x) (m := l.toHomeomorph) (f₁ := Δ f)
      (f₂ := (0 : E' → F))).symm
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩,
    fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- Harmonicity on a neighborhood transports to the preimage of the set. -/
theorem harmonicOnNhd_comp_linearIsometryEquiv_right_iff (l : E ≃ₗᵢ[ℝ] E')
    {f : E' → F} {s : Set E'} :
    HarmonicOnNhd (f ∘ l) (l ⁻¹' s) ↔ HarmonicOnNhd f s := by
  constructor
  · intro hf y hy
    have hpre : l (l.symm y) ∈ s := by simpa using hy
    have h := hf (l.symm y) hpre
    simpa using (harmonicAt_comp_linearIsometryEquiv_right_iff l).1 h
  · intro hf x hx
    exact (harmonicAt_comp_linearIsometryEquiv_right_iff l).2 (hf (l x) hx)

end EuclideanGeometry

end PeriodicAttractiveLogGas
