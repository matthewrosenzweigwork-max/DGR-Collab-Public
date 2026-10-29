import DGRHS.Commutator.SourceRieszLocalDecomposition

/-! UNCOMPILED draft, outside the first moving-law check. The already checked
full/short/long split and short-row estimate give a uniform error for the
actual first-order cancelled transport integral. This is the singular
analysis input to the static weak-PDE moving-test adapter. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRiesz_integral_full_sub_long_bound
    (s η : ℝ) (hs : 0<s) (hη : 0<η) (hd : s<(Fintype.card ι:ℝ))
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    |(∫ p,sourceRieszTransportKernel 1 s v p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))-
      (∫ p,sourceRieszLongTransportKernel 1 s η v p
        ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))| ≤
      localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) 1 s η K M := by
  let μ := gaussianRieszDensityMeasure ρ
  let B := localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) 1 s η K M
  have hS := localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair
    1 s η hs hη hd hv ρ M hM hρ
  have hL := integrable_sourceRieszLocalLongKernel μ s η 1 hs hη hv
  have he : (∫ p,sourceRieszTransportKernel 1 s v p ∂μ.prod μ) =
      (∫ p,sourceRieszShortTransportKernel 1 s η v p ∂μ.prod μ)+
        (∫ p,sourceRieszLongTransportKernel 1 s η v p ∂μ.prod μ) := by
    simp_rw [sourceRieszTransportKernel_full_short_long 1 s η hs hη v]
    exact integral_add hS hL
  change |(∫ p,sourceRieszTransportKernel 1 s v p ∂μ.prod μ)-
    (∫ p,sourceRieszLongTransportKernel 1 s η v p ∂μ.prod μ)| ≤ B
  rw [he,add_sub_cancel_right]
  calc
    _ ≤ ∫ p,|sourceRieszShortTransportKernel 1 s η v p| ∂μ.prod μ := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ:=μ.prod μ) (sourceRieszShortTransportKernel 1 s η v)
    _ = ∫ x,∫ y,|sourceRieszShortTransportKernel 1 s η v (x,y)| ∂μ ∂μ :=
      integral_prod _ hS.abs
    _ ≤ ∫ _ : E,B ∂μ := integral_mono_ae hS.abs.integral_prod_left (integrable_const B)
      (Filter.Eventually.of_forall (fun x =>
        localCompatible_sourceRieszShortTransportKernel_all_order_row_bound
          1 s η hs hη hd hv ρ M hM hρ x))
    _ = B := by simp

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceRiesz_integral_full_sub_long_bound
#print axioms DGRHS.Commutator.sourceRiesz_integral_full_sub_long_bound
