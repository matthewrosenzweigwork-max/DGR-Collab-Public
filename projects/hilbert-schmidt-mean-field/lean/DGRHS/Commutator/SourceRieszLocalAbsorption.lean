import DGRHS.Commutator.SourceRieszLocalCutoff
import DGRHS.Commutator.SourceRieszLocalShortConvolution

/-! Actual short-profile cancellation for the source local commutator numerator.
The same widened Gaussian short profile is used in both terms. -/
noncomputable section
open MeasureTheory
open scoped NNReal BigOperators
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceRieszLocalShortPotential (s η M : ℝ) : ℝ :=
  M*(gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι:ℝ)/2)/
    ((Fintype.card ι:ℝ)-s)*(2:ℝ)^((Fintype.card ι:ℝ)-s))*η^((Fintype.card ι:ℝ)-s)

lemma sourceRieszLocalShortPotential_nonneg (s η M : ℝ) (hs : 0<s) (hη : 0<η)
    (hM : 0≤M) (hd : s<(Fintype.card ι:ℝ)) : 0≤sourceRieszLocalShortPotential (ι:=ι) s η M := by
  have hc := gaussianRieszSourceCoefficient_pos s hs
  unfold sourceRieszLocalShortPotential
  positivity

lemma sourceRieszLocalShortCentered_lower (s η : ℝ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M) (p : E×E) :
    gaussianRieszEuclideanShortRange s (2*η) (p.1-p.2)-2*sourceRieszLocalShortPotential (ι:=ι) s η M ≤
      hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (fun q : E×E=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)) p := by
  let μ := gaussianRieszDensityMeasure ρ
  let f : E×E→ℝ := fun q=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)
  let P := sourceRieszLocalShortPotential (ι:=ι) s η M
  have hr (x : E) : (∫ y,f (x,y) ∂μ)≤P := by
    have h := gaussianRieszShortRange_convolution_le s (2*η) hs (by positivity) (by linarith) ρ M hM hρ x
    dsimp [f,P,sourceRieszLocalShortPotential]
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hη.le] at h
    convert h using 1 <;> ring
  have hswap : (fun x=>f (x,p.2))=(fun x=>f (p.2,x)) := by
    funext x
    exact gaussianRieszShortRange_symmetric s (2*η) x p.2
  have hmean : 0≤∫ q,f q ∂μ.prod μ := integral_nonneg (fun q=>gaussianRieszEuclideanShortRange_nonneg s (2*η) hs _)
  have h1 := hr p.1
  have h2 := hr p.2
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
  change f p-2*P≤f p-(∫ y,f (p.1,y) ∂μ)-(∫ x,f (x,p.2) ∂μ)+(∫ q,f q ∂μ.prod μ)
  rw [hswap]
  linarith

lemma sourceRieszLocalShortAbsorption_pointwise (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (p : E×E) :
    σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
      hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) p-
      γ/2*hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (fun q : E×E=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)) p ≤
      (7/4:ℝ)*γ*sourceRieszLocalShortPotential (ι:=ι) s η M := by
  let μ := gaussianRieszDensityMeasure ρ
  let ε := sourceRieszLocalCoefficient (ι:=ι) s n K γ
  let A := (sourceRieszGaussianDerivativeConstant n*(2:ℝ)^s)*(K:ℝ)^n
  let P := sourceRieszLocalShortPotential (ι:=ι) s η M
  let f := gaussianRieszEuclideanShortRange s (2*η) (p.1-p.2)
  let q := hoeffdingCentered μ (sourceRieszShortTransportKernel n s η v) p
  let F := hoeffdingCentered μ (fun q : E×E=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)) p
  have hε : 0≤ε := sourceRieszLocalCoefficient_nonneg (ι:=ι) s n K γ K.coe_nonneg hγ
  have hP : 0≤P := sourceRieszLocalShortPotential_nonneg s η M hs hη hM hd
  have hf : 0≤f := gaussianRieszEuclideanShortRange_nonneg s (2*η) hs _
  have hA : 0≤A := by have h:=sourceRieszGaussianDerivativeConstant_pos n;dsimp[A];positivity
  have hdom : A≤sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n :=
    mul_le_mul_of_nonneg_right (sourceRieszLocalProfileConstant_properties (ι:=ι) s n).2.2 (by positivity)
  have hcoeff : ε*A≤γ/4 := by
    have h1 := mul_le_mul_of_nonneg_left hdom hε
    have h2 := sourceRieszLocalCoefficient_mul_le (ι:=ι) s n K γ K.coe_nonneg hγ
    change 4*ε*(sourceRieszLocalProfileConstant (ι:=ι) s n*(K:ℝ)^n)≤γ at h2
    nlinarith
  have hB : localCompatible_sourceRieszShortTransportAllOrderPotentialBound (ι:=ι) n s η K M=A*P := by
    dsimp [A,P,localCompatible_sourceRieszShortTransportAllOrderPotentialBound,sourceRieszLocalShortPotential]
    ring
  have hκ : |q|≤A*f+3*A*P := by
    have h:=localCompatible_sourceRieszShortTransportKernel_all_order_centered_bound n s η hs hη hd hv ρ M hM hρ p
    rw [hB] at h
    simpa only [A,f,q,μ,mul_assoc] using h
  have hsign : σ*ε*q≤ε*|q| := by
    calc
      _ ≤ |σ*ε*q| := le_abs_self _
      _ = |σ| * ε * |q| := by rw [abs_mul,abs_mul,abs_of_nonneg hε]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hσ (mul_nonneg hε (abs_nonneg q))]
  have hscaled := mul_le_mul_of_nonneg_left hκ hε
  have hcf := mul_le_mul_of_nonneg_right hcoeff hf
  have hcp := mul_le_mul_of_nonneg_right hcoeff hP
  have hlower := sourceRieszLocalShortCentered_lower s η hs hη hd ρ M hM hρ p
  change f-2*P≤F at hlower
  have hnegative := mul_le_mul_of_nonneg_left hlower (by positivity : 0≤γ/2)
  change σ*ε*q-γ/2*F≤(7/4:ℝ)*γ*P
  nlinarith [mul_nonneg hγ hf]

lemma sourceRieszLocalShortAbsorption_sum (s η : ℝ) (n : ℕ) (hs : 0<s) (hη : 0<η)
    (hd : s<(Fintype.card ι:ℝ)) (γ σ : ℝ) (hγ : 0≤γ) (hσ : |σ|≤1)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N) (ω : Fin N→E) :
    (1/(N:ℝ))*(∑ i : Fin N,∑ j : Fin N,if i=j then 0 else
      σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) (ω i,ω j)-
        γ/2*hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (fun q : E×E=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)) (ω i,ω j)) ≤
      (7/4:ℝ)*γ*(N:ℝ)*sourceRieszLocalShortPotential (ι:=ι) s η M := by
  classical
  let B := (7/4:ℝ)*γ*sourceRieszLocalShortPotential (ι:=ι) s η M
  have hP := sourceRieszLocalShortPotential_nonneg s η M hs hη hM hd
  have hB : 0≤B := by dsimp[B];positivity
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin N) _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun (j : Fin N) _=>show
      (if i=j then 0 else σ*sourceRieszLocalCoefficient (ι:=ι) s n K γ*
        hoeffdingCentered (gaussianRieszDensityMeasure ρ) (sourceRieszShortTransportKernel n s η v) (ω i,ω j)-
        γ/2*hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (fun q : E×E=>gaussianRieszEuclideanShortRange s (2*η) (q.1-q.2)) (ω i,ω j))≤B from by
      split_ifs
      · exact hB
      · exact sourceRieszLocalShortAbsorption_pointwise s η n hs hη hd γ σ hγ hσ hv ρ M hM hρ (ω i,ω j)))
  have hn : 0<(N:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hN)
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0≤1/(N:ℝ))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  convert hh using 1 <;> dsimp[B] <;> field_simp [hn.ne'] <;> ring

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalShortPotential
#print axioms DGRHS.Commutator.sourceRieszLocalShortPotential

#check DGRHS.Commutator.sourceRieszLocalShortPotential_nonneg
#print axioms DGRHS.Commutator.sourceRieszLocalShortPotential_nonneg

#check DGRHS.Commutator.sourceRieszLocalShortCentered_lower
#print axioms DGRHS.Commutator.sourceRieszLocalShortCentered_lower

#check DGRHS.Commutator.sourceRieszLocalShortAbsorption_pointwise
#print axioms DGRHS.Commutator.sourceRieszLocalShortAbsorption_pointwise

#check DGRHS.Commutator.sourceRieszLocalShortAbsorption_sum
#print axioms DGRHS.Commutator.sourceRieszLocalShortAbsorption_sum
