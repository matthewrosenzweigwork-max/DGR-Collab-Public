/- Original arbitrary L2 observable fluctuation under the actual normalized
Gibbs tilt. Legitimate product AE equality is pulled through finite iid laws
and then through absolute continuity of the actual tilt. -/
import DGRHS.Kernel.L2Centering
import DGRHS.CLT.SourceKernelGibbsGaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators
namespace DGRHS.CLT
variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {μ : Measure S} [IsProbabilityMeasure μ]
    {P : Measure Ω} [IsProbabilityMeasure P]

def sourceObservableFluctuation {m : ℕ} (φ : Fin m → Lp ℝ 2 μ)
    (N : ℕ) (x : Fin N → S) (k : Fin m) : ℝ :=
  Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N, φ k (x i) - ∫ y, φ k y ∂μ)

theorem sourceObservableFluctuation_tendsto {m : ℕ} (φ : Fin m → Lp ℝ 2 μ)
    (Y : ∀ N, (Fin N → S) → ℝ)
    [∀ N, IsProbabilityMeasure ((Measure.pi (fun _ : Fin N => μ)).tilted (Y N))]
    (Z : Ω → (Fin m → ℝ))
    (h : TendstoInDistribution
      (fun N (x : Fin N → S) k => (Real.sqrt N)⁻¹*
        ∑ i : Fin N, DGRHS.Kernel.centeredL2 (φ k) (x i)) atTop Z
      (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted (Y N)) P) :
    TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
      (fun N => (Measure.pi (fun _ : Fin N => μ)).tilted (Y N)) P := by
  apply TendstoInDistribution.congr _ (Filter.EventuallyEq.rfl) h
  intro N
  have hk := fun k : Fin m => DGRHS.Kernel.particle_centeredL2_fluctuation (φ k) N
  have he :
      (fun x : Fin N → S => fun k : Fin m => (Real.sqrt N)⁻¹*
        ∑ i : Fin N, DGRHS.Kernel.centeredL2 (φ k) (x i))
        =ᵐ[Measure.pi (fun _ : Fin N => μ)] sourceObservableFluctuation φ N := by
    filter_upwards [ae_all_iff.mpr hk] with x hx
    funext k
    exact hx k
  exact (tilted_absolutelyContinuous (Measure.pi (fun _ : Fin N => μ)) (Y N)).ae_le he
end DGRHS.CLT
#print axioms DGRHS.CLT.sourceObservableFluctuation_tendsto
#check @DGRHS.CLT.sourceObservableFluctuation_tendsto
