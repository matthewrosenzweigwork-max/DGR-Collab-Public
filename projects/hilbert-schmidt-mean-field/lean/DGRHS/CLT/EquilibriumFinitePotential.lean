import DGRHS.CLT.MacroscopicFreeEnergy
import DGRHS.Entropy.BoundedDensityLogMoment

/-! The native thermal RN identity yields proper V once genuine entropy and
pair interaction are proper. For LOG, bounded density and pair-log integrability
derive that entropy. No potential-energy or entropy premise is added to the
LOG source assumptions. The Riesz-only thermal domain is not asserted here. -/
noncomputable section
open MeasureTheory
namespace DGRHS.CLT
open DGRHS.Gaussian

theorem equilibrium_integrable_potential_of_entropy {S : Type*} [MeasurableSpace S]
    (ν₀ μ : Measure S) [SigmaFinite ν₀] [IsProbabilityMeasure μ]
    (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hW : Integrable (Function.uncurry W) (μ.prod μ))
    (hLLR : Integrable (llr μ ν₀) μ)
    (hEL : ν₀.tilted (fun x => -β * (V x + DGRHS.potential μ W x)) = μ) :
    Integrable V μ := by
  let f := fun x => -β * (V x + DGRHS.potential μ W x)
  have hf := integrable_exp_of_tilted_probability f hEL
  have hμν : μ ≪ ν₀ := by rw [← hEL]; exact tilted_absolutelyContinuous ν₀ f
  have he : llr μ ν₀ =ᵐ[μ] (fun x => f x - Real.log (∫ y, Real.exp (f y) ∂ν₀)) := by
    have h := hμν.ae_le (log_rnDeriv_tilted_left_self hf)
    rw [hEL] at h
    exact h
  have hfi : Integrable f μ := by
    apply (hLLR.add (integrable_const (Real.log (∫ y, Real.exp (f y) ∂ν₀)))).congr
    filter_upwards [he] with x hx
    dsimp only [Pi.add_apply]
    rw [hx]
    ring
  have hsum : Integrable (fun x => V x + DGRHS.potential μ W x) μ := by
    convert hfi.const_mul (-β)⁻¹ using 1
    funext x
    dsimp only [f]
    field_simp
  have hF := DGRHS.integrable_potential μ W hW
  convert hsum.sub hF using 1
  funext x
  simp

theorem sourceLog_equilibrium_finite_potential {ι : Type*} [Fintype ι]
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)))
    (V : EuclideanSpace ℝ ι → ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β *
      (V x + DGRHS.potential (gaussianRieszDensityMeasure ρ)
        (fun a b => logPhysicalPair (a,b)) x)) = gaussianRieszDensityMeasure ρ) :
    Integrable V (gaussianRieszDensityMeasure ρ) ∧
    Integrable (llr (gaussianRieszDensityMeasure ρ) volume) (gaussianRieszDensityMeasure ρ) := by
  have hlog := integrable_log_one_add_norm_of_pair_log (gaussianRieszDensityMeasure ρ) hpair
  have hLLR := DGRHS.Entropy.integrable_llr_densityMeasure_of_log_moment ρ M hM hρ hlog
  exact ⟨equilibrium_integrable_potential_of_entropy volume (gaussianRieszDensityMeasure ρ)
    (fun a b => logPhysicalPair (a,b)) V β hβ hpair hLLR hEL, hLLR⟩

end DGRHS.CLT
#check @DGRHS.CLT.equilibrium_integrable_potential_of_entropy
#print axioms DGRHS.CLT.equilibrium_integrable_potential_of_entropy
#check @DGRHS.CLT.sourceLog_equilibrium_finite_potential
#print axioms DGRHS.CLT.sourceLog_equilibrium_finite_potential
