import DGRHS.Commutator.SourceRieszStaticWeakForm

/-! UNCOMPILED actual narrow-continuity consequence of the integrated static
source PDE. Endpoint clamping supplies a probability path at every real time.
Continuity is derived through the admissible Fourier tests, not assumed.
Only the original closed-horizon densities need be probability densities. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma SourceRieszStaticWeakMeanField.exists_continuous_probability_path
    (s β T : ℝ) (hT : 0≤T) (ρ : ℝ→E→ℝ)
    (h : SourceRieszStaticWeakMeanField s β T ρ)
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) :
    ∃ μ:ℝ→ProbabilityMeasure E,Continuous μ ∧
      ∀ r,(μ r:Measure E)=gaussianRieszDensityMeasure (ρ (max 0 (min T r))) := by
  let c : ℝ→ℝ := fun r=>max 0 (min T r)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (r : ℝ) : c r∈Icc 0 T :=
    ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (r : ℝ) (hr : r∈Icc 0 T) : c r=r := by
    dsimp only [c]
    rw [min_eq_right hr.2,max_eq_right hr.1]
  let μ : ℝ→ProbabilityMeasure E :=
    fun r=>⟨gaussianRieszDensityMeasure (ρ (c r)),hprob (c r) (hcm r)⟩
  have hAC : ∀ φ:E→ℝ,SourceBoundedC2Test φ →
      AbsolutelyContinuousOnInterval (fun r=>∫ x,φ x ∂(μ r:Measure E)) 0 T := by
    intro φ hφ
    apply (h.static_pairing_ac s β T hT ρ φ hφ).congr
    intro r hr
    have hr' : r∈Icc 0 T := by simpa only [uIcc_of_le hT] using hr
    simp only [μ,hce r hr']
    rfl
  have hμ : ContinuousOn μ (Icc 0 T) :=
    continuousOn_probability_of_ac_boundedC2_tests μ 0 T hT hAC
  have hcont : Continuous (μ∘c) := hμ.comp_continuous hc hcm
  have he : μ∘c=μ := by
    funext r
    apply Subtype.ext
    change gaussianRieszDensityMeasure (ρ (c (c r)))=gaussianRieszDensityMeasure (ρ (c r))
    rw [hce (c r) (hcm r)]
  refine ⟨μ,?_,fun _=>rfl⟩
  rwa [he] at hcont

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszStaticWeakMeanField.exists_continuous_probability_path
#print axioms DGRHS.Commutator.SourceRieszStaticWeakMeanField.exists_continuous_probability_path
