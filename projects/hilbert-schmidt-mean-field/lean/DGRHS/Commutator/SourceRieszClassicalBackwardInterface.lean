import DGRHS.Commutator.SourceRieszMeanFieldTestEvolution
import DGRHS.Commutator.SourceRieszDynamicJointCLT

/-! UNCOMPILED exact source888--902 backward-solution interface. The time
derivative is an actual derivative on the open interval and has a bounded,
jointly continuous extension to the closed interval. No differentiability
of a global extension at the two endpoints is imposed. The AE backward
identity needed by the checked consumer is derived using the null terminal
singleton, rather than treating totalized `deriv` as a classical PDE.
The source assumes existence and uniqueness; this module selects that solution
and records uniqueness only on its original time interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceRieszClassicalBackwardSolution
    (s β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ) : Prop where
  terminal : f (t:ℝ)=φ
  spatial_contdiff : ∀ r∈Icc 0 (t:ℝ),ContDiff ℝ 2 (f r)
  value_continuous : ContinuousOn (fun p:ℝ×E=>f p.1 p.2) (Icc 0 (t:ℝ) ×ˢ univ)
  gradient_continuous : ContinuousOn (fun p:ℝ×E=>gradient (f p.1) p.2) (Icc 0 (t:ℝ) ×ˢ univ)
  hessian_continuous : ContinuousOn (fun p:ℝ×E=>iteratedFDeriv ℝ 2 (f p.1) p.2)
    (Icc 0 (t:ℝ) ×ˢ univ)
  bounded : ∃ C:ℝ,0≤C ∧ ∀ r∈Icc 0 (t:ℝ),∀ z,
    |f r z|≤C ∧ ‖gradient (f r) z‖≤C ∧ ‖iteratedFDeriv ℝ 2 (f r) z‖≤C
  time_equation : ∃ δ:ℝ→E→ℝ,
    ContinuousOn (fun p:ℝ×E=>δ p.1 p.2) (Icc 0 (t:ℝ) ×ˢ univ) ∧
    (∃ C:ℝ,∀ r∈Icc 0 (t:ℝ),∀ z,|δ r z|≤C) ∧
    (∀ r∈Ioo 0 (t:ℝ),∀ z,HasDerivAt (fun u=>f u z) (δ r z) r) ∧
    ∀ r∈Icc 0 (t:ℝ),∀ z,δ r z+β⁻¹*laplacian (f r) z=
      ∫ y,⟪sourceRieszForce s (z-y),gradient (f r) z-gradient (f r) y⟫
        ∂gaussianRieszDensityMeasure (ρ r)

/-- Literal existence and uniqueness assumption for the source real linear
test space. The solution's off-horizon values are irrelevant to uniqueness. -/
def SourceRieszBackwardClassicalWellPosed
    (T : ℝ≥0) (s β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ)) : Prop :=
  ∀ t:ℝ≥0,t≤T → ∀ φ:E→ℝ,φ∈D → ∃ f:ℝ→E→ℝ,
    SourceRieszClassicalBackwardSolution s β ρ t φ f ∧
    ∀ g:ℝ→E→ℝ,SourceRieszClassicalBackwardSolution s β ρ t φ g →
      ∀ r∈Icc 0 (t:ℝ),f r=g r

/-- The source propagator U^{r,t}phi, selected once from the assumed unique
classical backward solution. Every later covariance uses this same choice. -/
def sourceRieszUprop
    (T : ℝ≥0) (s β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceRieszBackwardClassicalWellPosed T s β ρ D)
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφ : φ∈D) : ℝ→E→ℝ :=
  Classical.choose (h t ht φ hφ)

lemma sourceRieszUprop_spec
    (T : ℝ≥0) (s β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceRieszBackwardClassicalWellPosed T s β ρ D)
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφ : φ∈D) :
    SourceRieszClassicalBackwardSolution s β ρ t φ (sourceRieszUprop T s β ρ D h t ht φ hφ) ∧
    ∀ g:ℝ→E→ℝ,SourceRieszClassicalBackwardSolution s β ρ t φ g →
      ∀ r∈Icc 0 (t:ℝ),sourceRieszUprop T s β ρ D h t ht φ hφ r=g r :=
  Classical.choose_spec (h t ht φ hφ)

lemma SourceRieszClassicalBackwardSolution.backward_ae
    (s β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceRieszClassicalBackwardSolution s β ρ t φ f) :
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),∀ z,
      deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (f r) z-gradient (f r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r) := by
  obtain ⟨δ,hδc,hδb,hδ,hEq⟩ := h.time_equation
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (t:ℝ))] with r hr hrt
  intro z
  rw [(hδ r ⟨hr.1,lt_of_le_of_ne hr.2 hrt⟩ z).deriv]
  exact hEq r ⟨hr.1.le,hr.2⟩ z

lemma sourceRieszBackwardTestSpace_Cb2
    (T : ℝ≥0) (s β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceRieszBackwardClassicalWellPosed T s β ρ D)
    (φ : E→ℝ) (hφ : φ∈D) :
    ContDiff ℝ 2 φ ∧ ∃ C:ℝ,0≤C ∧ ∀ z,
      |φ z|≤C ∧ ‖gradient φ z‖≤C ∧ ‖iteratedFDeriv ℝ 2 φ z‖≤C := by
  have hu := (sourceRieszUprop_spec T s β ρ D h 0 zero_le φ hφ).1
  have ht := hu.terminal
  change sourceRieszUprop T s β ρ D h 0 zero_le φ hφ (0:ℝ)=φ at ht
  have hs := hu.spatial_contdiff 0 ⟨le_rfl,le_rfl⟩
  obtain ⟨C,hC,hb⟩ := hu.bounded
  refine ⟨?_,C,hC,?_⟩
  · simpa only [ht] using hs
  · intro z
    simpa only [ht] using hb 0 ⟨le_rfl,le_rfl⟩ z

/-- The source's fixed finite-family uniform bounds are obtained by taking a
finite sum of the selected nonnegative individual solution bounds. -/
lemma sourceRieszClassicalBackwardSolution_finite_bounds
    (s β : ℝ) (ρ : ℝ→E→ℝ) (k : ℕ) (t : Fin k→ℝ≥0)
    (φ : Fin k→E→ℝ) (f : Fin k→ℝ→E→ℝ)
    (h : ∀ a,SourceRieszClassicalBackwardSolution s β ρ (t a) (φ a) (f a)) :
    ∃ C:ℝ,0≤C ∧ ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,
      |f a r z|≤C ∧ ‖gradient (f a r) z‖≤C ∧ ‖iteratedFDeriv ℝ 2 (f a r) z‖≤C := by
  classical
  choose C hC hb using fun a=>(h a).bounded
  refine ⟨∑ a,C a,Finset.sum_nonneg (fun a _=>hC a),?_⟩
  intro a r hr z
  have hle : C a≤∑ b,C b := Finset.single_le_sum (fun b _=>hC b) (Finset.mem_univ a)
  exact ⟨((hb a r hr z).1).trans hle,((hb a r hr z).2.1).trans hle,
    ((hb a r hr z).2.2).trans hle⟩

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszClassicalBackwardSolution
#print axioms DGRHS.Commutator.SourceRieszClassicalBackwardSolution
#check @DGRHS.Commutator.SourceRieszBackwardClassicalWellPosed
#print axioms DGRHS.Commutator.SourceRieszBackwardClassicalWellPosed
#check @DGRHS.Commutator.sourceRieszUprop
#print axioms DGRHS.Commutator.sourceRieszUprop
#check @DGRHS.Commutator.sourceRieszUprop_spec
#print axioms DGRHS.Commutator.sourceRieszUprop_spec
#check @DGRHS.Commutator.SourceRieszClassicalBackwardSolution.backward_ae
#print axioms DGRHS.Commutator.SourceRieszClassicalBackwardSolution.backward_ae
#check @DGRHS.Commutator.sourceRieszBackwardTestSpace_Cb2
#print axioms DGRHS.Commutator.sourceRieszBackwardTestSpace_Cb2
#check @DGRHS.Commutator.sourceRieszClassicalBackwardSolution_finite_bounds
#print axioms DGRHS.Commutator.sourceRieszClassicalBackwardSolution_finite_bounds
