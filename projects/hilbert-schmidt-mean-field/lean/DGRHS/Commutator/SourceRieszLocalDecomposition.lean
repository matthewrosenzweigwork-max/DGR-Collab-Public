import DGRHS.Commutator.SourceRieszLocalAbsorption
import DGRHS.Commutator.SourceRieszLocalCenteredCap
import DGRHS.Commutator.SourceRieszTruncatedTransportKernelSplit

/-! Actual proper full/short/long centering identities. The physical energy
identity is product-AE off collision; the derivative kernel split is genuine
pointwise collision-zero. No diagonal slice of an AE statement is used. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian

lemma sourceRieszLocal_centered_const_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W : X×X→ℝ) (c : ℝ) (p : X×X) :
    hoeffdingCentered μ (fun q=>c*W q) p=c*hoeffdingCentered μ W p := by
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp only [integral_const_mul]
  ring

lemma sourceRieszLocal_centered_add {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (W V : X×X→ℝ)
    (hW : Integrable W (μ.prod μ)) (hV : Integrable V (μ.prod μ)) :
    hoeffdingCentered μ (W+V)=ᵐ[μ.prod μ] hoeffdingCentered μ W+hoeffdingCentered μ V := by
  filter_upwards [
    (measurePreserving_fst (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hW.prod_right_ae,
    (measurePreserving_fst (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hV.prod_right_ae,
    (measurePreserving_snd (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hW.prod_left_ae,
    (measurePreserving_snd (μ:=μ) (ν:=μ)).quasiMeasurePreserving.ae hV.prod_left_ae] with p hWx hVx hWy hVy
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  simp only [Pi.add_apply]
  rw [integral_add hWx hVx,integral_add hWy hVy,integral_add hW hV]
  ring

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma integrable_sourceRieszLocalLongKernel (μ : Measure E) [IsProbabilityMeasure μ]
    (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) :
    Integrable (sourceRieszLongTransportKernel n s η v) (μ.prod μ) := by
  let A := (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n
  have hA : 0≤A := by have hc:=sourceRieszGaussianDerivativeConstant_pos n;dsimp[A];positivity
  have hc := (gaussianRieszSourceCoefficient_pos s hs).le
  apply sourceRieszLocal_bounded_integrable (μ.prod μ) _
    (measurable_sourceRieszLongTransportKernel_all_order s η n hs hη hv).stronglyMeasurable
    (A*(gaussianRieszSourceCoefficient s/s*η^(-s))) (by positivity)
  intro p
  apply (sourceRieszLongTransportKernel_all_order_bound n s η hs hη hv p).trans
  apply mul_le_mul_of_nonneg_left _ hA
  have hg := gaussianRieszEuclideanTruncation_nonneg s η hs hη (p.1-p.2)
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using gaussianRieszEuclideanTruncation_le_diagonal s η hs hη (p.1-p.2))

lemma ae_sourceRieszLocalCenteredTransport_split (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszTransportKernel n s v)=ᵐ[
      (gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v)+
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszLongTransportKernel n s η v) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hS := localCompatible_integrable_sourceRieszShortTransportKernel_all_order_pair n s η hs hη hd hv ρ M hM hρ
  have hL := integrable_sourceRieszLocalLongKernel μ s η n hs hη hv
  have he : sourceRieszTransportKernel n s v=ᵐ[μ.prod μ]
      sourceRieszShortTransportKernel n s η v+sourceRieszLongTransportKernel n s η v :=
    Filter.Eventually.of_forall (fun p=>sourceRieszTransportKernel_full_short_long n s η hs hη v p)
  exact (ae_hoeffdingCentered_congr μ _ _ he).trans (sourceRieszLocal_centered_add μ _ _ hS hL)

lemma ae_sourceRieszLocalCenteredEnergy_split (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : 2*s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)=ᵐ[
      (gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)]
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszShortPair s η)+
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η) := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0<Fintype.card ι := by exact_mod_cast (show (0:ℝ)<(Fintype.card ι:ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have he : gaussianRieszPhysicalPair s=ᵐ[μ.prod μ] gaussianRieszShortPair s η+gaussianRieszTruncatedPair s η := by
    filter_upwards [ae_gaussianRieszDensity_pair_ne ρ] with p hp
    exact gaussianRieszEuclidean_full_short_long_split s η hs hη _ (sub_ne_zero.mpr hp)
  have hF := (memLp_gaussianRieszPhysicalPair s hs (by linarith) ρ M hM hρ).integrable (by norm_num)
  have hL := (memLp_gaussianRieszTruncatedPair s η hs hη μ).integrable (by norm_num)
  have hS : Integrable (gaussianRieszShortPair s η) (μ.prod μ) := by
    apply (hF.sub hL).congr
    filter_upwards [he] with p hp
    change gaussianRieszPhysicalPair s p-gaussianRieszTruncatedPair s η p=gaussianRieszShortPair s η p
    change gaussianRieszPhysicalPair s p=gaussianRieszShortPair s η p+gaussianRieszTruncatedPair s η p at hp
    linarith
  exact (ae_hoeffdingCentered_congr μ _ _ he).trans (sourceRieszLocal_centered_add μ _ _ hS hL)

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocal_centered_const_mul
#print axioms DGRHS.Commutator.sourceRieszLocal_centered_const_mul

#check DGRHS.Commutator.sourceRieszLocal_centered_add
#print axioms DGRHS.Commutator.sourceRieszLocal_centered_add

#check DGRHS.Commutator.integrable_sourceRieszLocalLongKernel
#print axioms DGRHS.Commutator.integrable_sourceRieszLocalLongKernel

#check DGRHS.Commutator.ae_sourceRieszLocalCenteredTransport_split
#print axioms DGRHS.Commutator.ae_sourceRieszLocalCenteredTransport_split

#check DGRHS.Commutator.ae_sourceRieszLocalCenteredEnergy_split
#print axioms DGRHS.Commutator.ae_sourceRieszLocalCenteredEnergy_split
