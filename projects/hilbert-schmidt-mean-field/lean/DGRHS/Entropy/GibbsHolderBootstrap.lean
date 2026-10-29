/- Source all-temperature Holder bootstrap, using actual local numerator and
the actual remaining partition. Both exponential factors are proper before
their square-root product and literal Gibbs normalization are used. -/
import DGRHS.Entropy.GibbsExponentialNormalization
import DGRHS.CLT.BoundedLinearWeightMoments
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

theorem exponential_half_sum_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (u v : S→ℝ)
    (hu : Integrable (fun x=>Real.exp (u x)) μ)
    (hv : Integrable (fun x=>Real.exp (v x)) μ)
    (B C : ℝ) (hB : (∫ x,Real.exp (u x) ∂μ)≤B)
    (hC : (∫ x,Real.exp (v x) ∂μ)≤C) :
    Integrable (fun x=>Real.exp ((u x+v x)/2)) μ ∧
      (∫ x,Real.exp ((u x+v x)/2) ∂μ)≤Real.sqrt B*Real.sqrt C := by
  have hmu : AEMeasurable u μ := by
    simpa only [Function.comp_def,Real.log_exp] using
      Real.measurable_log.comp_aemeasurable hu.aestronglyMeasurable.aemeasurable
  have hmv : AEMeasurable v μ := by
    simpa only [Function.comp_def,Real.log_exp] using
      Real.measurable_log.comp_aemeasurable hv.aestronglyMeasurable.aemeasurable
  have hu2 : Integrable (fun x=>Real.exp (2*(u x/2))) μ := by
    convert hu using 1
    funext x
    congr 1
    ring
  have hv2 : Integrable (fun x=>Real.exp (2*(v x/2))) μ := by
    convert hv using 1
    funext x
    congr 1
    ring
  obtain ⟨hi,hb⟩ := DGRHS.CLT.exponential_sum_integral_cs
    (fun x=>u x/2) (fun x=>v x/2) (hmu.div_const 2) (hmv.div_const 2) hu2 hv2
  have he : (fun x=>Real.exp ((u x+v x)/2))=(fun x=>Real.exp (u x/2+v x/2)) := by
    funext x
    congr 1
    ring
  refine ⟨by rw [he]; exact hi,?_⟩
  rw [he]
  apply hb.trans
  apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · apply Real.sqrt_le_sqrt
    convert hB using 1
    congr 1
    funext x
    congr 1
    ring
  · apply Real.sqrt_le_sqrt
    convert hC using 1
    congr 1
    funext x
    congr 1
    ring

open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLog_gibbs_holder_bound (β γ : ℝ≥0) (hγβ : (γ:ℝ)≤(β:ℝ))
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (a : (Fin N→EuclideanSpace ℝ ι)→ℝ)
    (ε B Cub : ℝ) :
    let θ : ℝ≥0 := ⟨2*(β:ℝ)-(γ:ℝ),by linarith [β.coe_nonneg]⟩
    let μ := gaussianRieszDensityMeasure ρ
    let P := Measure.pi (fun _ : Fin N=>μ)
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    Integrable (fun x=>Real.exp (-(γ:ℝ)*(N:ℝ)*E x+ε*a x)) P →
    (∫ x,Real.exp (-(γ:ℝ)*(N:ℝ)*E x+ε*a x) ∂P)≤B →
    (sourceLogSingularPartition θ ρ N).toReal≤Cub →
      Integrable (fun x=>Real.exp ((ε/2)*a x)) (sourceLogSingularGibbs β ρ N) ∧
      (∫ x,Real.exp ((ε/2)*a x) ∂sourceLogSingularGibbs β ρ N)≤
        Real.exp (-(β:ℝ)*DGRHS.interactionEnergy μ W)*Real.sqrt B*Real.sqrt Cub := by
  dsimp only
  intro hlocal hB hCub
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  let u := fun x=>-(γ:ℝ)*(N:ℝ)*E x+ε*a x
  let v := fun x=>-(2*(β:ℝ)-(γ:ℝ))*(N:ℝ)*E x
  have hv := sourceLogEnergyWeight_integrable (2*(β:ℝ)-(γ:ℝ))
    (by linarith [β.coe_nonneg]) hd ρ M hM hρ hpair N
  have hV : (∫ x,Real.exp (v x) ∂P)≤Cub := by
    rw [sourceLogSingularPartition_eq_integral
      (⟨2*(β:ℝ)-(γ:ℝ),by linarith [β.coe_nonneg]⟩ : ℝ≥0) hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)] at hCub
    exact hCub
  obtain ⟨hi,hb⟩ := exponential_half_sum_bound P u v hlocal hv B Cub hB hV
  have he : (fun x=>Real.exp (-(β:ℝ)*(N:ℝ)*E x+(ε/2)*a x))=
      (fun x=>Real.exp ((u x+v x)/2)) := by
    funext x
    congr 1
    dsimp only [u,v]
    ring
  rw [←he] at hi hb
  obtain ⟨hproper,hbound⟩ := sourceLog_gibbs_exponential_bound β hd ρ M hM hρ hpair N hN
    (fun x=>(ε/2)*a x) (Real.sqrt B*Real.sqrt Cub) hi hb
  refine ⟨hproper,?_⟩
  convert hbound using 1
  rw [div_eq_mul_inv,←Real.exp_neg]
  ring

end DGRHS.Entropy
#check @DGRHS.Entropy.exponential_half_sum_bound
#check @DGRHS.Entropy.sourceLog_gibbs_holder_bound
#print axioms DGRHS.Entropy.exponential_half_sum_bound
#print axioms DGRHS.Entropy.sourceLog_gibbs_holder_bound
