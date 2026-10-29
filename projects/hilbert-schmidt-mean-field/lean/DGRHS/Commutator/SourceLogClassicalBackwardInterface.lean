import DGRHS.Commutator.SourceLogPrimitiveForceBridge

/-! Records-only actual LOG classical interface. The time derivative is an
actual interior derivative with a continuous bounded closed-horizon extension.
The source supplies well-posedness; one named propagator is selected once. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Dynamics
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceLogClassicalBackwardSolution
    (β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ) : Prop where
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
      ∫ y,sourceLogTransportKernel 1 (gradient (f r)) (z,y)
        ∂gaussianRieszDensityMeasure (ρ r)

/-- Literal existence and uniqueness assumption for the source real linear
test space. The solution's off-horizon values are irrelevant to uniqueness. -/
def SourceLogBackwardClassicalWellPosed
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ)) : Prop :=
  ∀ t:ℝ≥0,t≤T → ∀ φ:E→ℝ,φ∈D → ∃ f:ℝ→E→ℝ,
    SourceLogClassicalBackwardSolution β ρ t φ f ∧
    ∀ g:ℝ→E→ℝ,SourceLogClassicalBackwardSolution β ρ t φ g →
      ∀ r∈Icc 0 (t:ℝ),f r=g r

/-- The source propagator U^{r,t}phi, selected once from the assumed unique
classical backward solution. Every later covariance uses this same choice. -/
def sourceLogUprop
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceLogBackwardClassicalWellPosed T β ρ D)
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφ : φ∈D) : ℝ→E→ℝ :=
  Classical.choose (h t ht φ hφ)

lemma sourceLogUprop_spec
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceLogBackwardClassicalWellPosed T β ρ D)
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφ : φ∈D) :
    SourceLogClassicalBackwardSolution β ρ t φ (sourceLogUprop T β ρ D h t ht φ hφ) ∧
    ∀ g:ℝ→E→ℝ,SourceLogClassicalBackwardSolution β ρ t φ g →
      ∀ r∈Icc 0 (t:ℝ),sourceLogUprop T β ρ D h t ht φ hφ r=g r :=
  Classical.choose_spec (h t ht φ hφ)

lemma SourceLogClassicalBackwardSolution.backward_ae
    (β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceLogClassicalBackwardSolution β ρ t φ f) :
    ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),∀ z,
      deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z=
        ∫ y,sourceLogTransportKernel 1 (gradient (f r)) (z,y)
          ∂gaussianRieszDensityMeasure (ρ r) := by
  obtain ⟨δ,hδc,hδb,hδ,hEq⟩ := h.time_equation
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (t:ℝ))] with r hr hrt
  intro z
  rw [(hδ r ⟨hr.1,lt_of_le_of_ne hr.2 hrt⟩ z).deriv]
  exact hEq r ⟨hr.1.le,hr.2⟩ z

lemma sourceLogBackwardTestSpace_Cb2
    (T : ℝ≥0) (β : ℝ) (ρ : ℝ→E→ℝ) (D : Submodule ℝ (E→ℝ))
    (h : SourceLogBackwardClassicalWellPosed T β ρ D)
    (φ : E→ℝ) (hφ : φ∈D) :
    ContDiff ℝ 2 φ ∧ ∃ C:ℝ,0≤C ∧ ∀ z,
      |φ z|≤C ∧ ‖gradient φ z‖≤C ∧ ‖iteratedFDeriv ℝ 2 φ z‖≤C := by
  have hu := (sourceLogUprop_spec T β ρ D h 0 zero_le φ hφ).1
  have ht := hu.terminal
  change sourceLogUprop T β ρ D h 0 zero_le φ hφ (0:ℝ)=φ at ht
  have hs := hu.spatial_contdiff 0 ⟨le_rfl,le_rfl⟩
  obtain ⟨C,hC,hb⟩ := hu.bounded
  refine ⟨?_,C,hC,?_⟩
  · simpa only [ht] using hs
  · intro z
    simpa only [ht] using hb 0 ⟨le_rfl,le_rfl⟩ z

/-- The source's fixed finite-family uniform bounds are obtained by taking a
finite sum of the selected nonnegative individual solution bounds. -/
lemma sourceLogClassicalBackwardSolution_finite_bounds
    (β : ℝ) (ρ : ℝ→E→ℝ) (k : ℕ) (t : Fin k→ℝ≥0)
    (φ : Fin k→E→ℝ) (f : Fin k→ℝ→E→ℝ)
    (h : ∀ a,SourceLogClassicalBackwardSolution β ρ (t a) (φ a) (f a)) :
    ∃ C:ℝ,0≤C ∧ ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,
      |f a r z|≤C ∧ ‖gradient (f a r) z‖≤C ∧ ‖iteratedFDeriv ℝ 2 (f a r) z‖≤C := by
  classical
  choose C hC hb using fun a=>(h a).bounded
  refine ⟨∑ a,C a,Finset.sum_nonneg (fun a _=>hC a),?_⟩
  intro a r hr z
  have hle : C a≤∑ b,C b := Finset.single_le_sum (fun b _=>hC b) (Finset.mem_univ a)
  exact ⟨((hb a r hr z).1).trans hle,((hb a r hr z).2.1).trans hle,
    ((hb a r hr z).2.2).trans hle⟩


/-- The native logarithmic canceled backward equation is the technical
force-zero equation, independently of any Riesz potential at zero. -/
lemma SourceLogClassicalBackwardSolution.to_zero
    (β : ℝ) (ρ : ℝ→E→ℝ) (t : ℝ≥0) (φ : E→ℝ) (f : ℝ→E→ℝ)
    (h : SourceLogClassicalBackwardSolution β ρ t φ f) :
    SourceRieszClassicalBackwardSolution 0 β ρ t φ f := by
  refine ⟨h.terminal,h.spatial_contdiff,h.value_continuous,h.gradient_continuous,
    h.hessian_continuous,h.bounded,?_⟩
  obtain ⟨δ,hδc,hδb,hδ,hEq⟩ := h.time_equation
  refine ⟨δ,hδc,hδb,hδ,?_⟩
  intro r hr z
  simpa only [sourceRieszForce_zero_eq_logForce,←sourceLogTransportKernel_force] using hEq r hr z

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceLogClassicalBackwardSolution
#print axioms DGRHS.Commutator.SourceLogClassicalBackwardSolution
#check @DGRHS.Commutator.SourceLogBackwardClassicalWellPosed
#print axioms DGRHS.Commutator.SourceLogBackwardClassicalWellPosed
#check @DGRHS.Commutator.sourceLogUprop
#print axioms DGRHS.Commutator.sourceLogUprop
#check @DGRHS.Commutator.sourceLogUprop_spec
#print axioms DGRHS.Commutator.sourceLogUprop_spec
#check @DGRHS.Commutator.SourceLogClassicalBackwardSolution.backward_ae
#print axioms DGRHS.Commutator.SourceLogClassicalBackwardSolution.backward_ae
#check @DGRHS.Commutator.sourceLogBackwardTestSpace_Cb2
#print axioms DGRHS.Commutator.sourceLogBackwardTestSpace_Cb2
#check @DGRHS.Commutator.sourceLogClassicalBackwardSolution_finite_bounds
#print axioms DGRHS.Commutator.sourceLogClassicalBackwardSolution_finite_bounds
#check @DGRHS.Commutator.SourceLogClassicalBackwardSolution.to_zero
#print axioms DGRHS.Commutator.SourceLogClassicalBackwardSolution.to_zero
