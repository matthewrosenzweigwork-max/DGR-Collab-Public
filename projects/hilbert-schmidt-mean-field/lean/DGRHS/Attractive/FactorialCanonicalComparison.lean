/- Actual positive-sign particle exponential comparison from source row moments.
An endpoint CS argument replaces differentiation of the interpolation.
No desired particle exponential estimate is supplied as a hypothesis. -/
import DGRHS.Attractive.CanonicalExponential
import DGRHS.Attractive.SourceOperatorBound
import DGRHS.CLT.IidCanonicalNormalization
import DGRHS.CLT.CanonicalPartitionComparison
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma attractiveStatistic_eq_neg_normalized (h : S×S→ℝ) (N : ℕ) (x : Fin N→S) :
    attractiveNormalizedStatistic N h x =
      -DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  rw [←DGRHS.CLT.sourceStatistic_eq_normalized]
  unfold attractiveNormalizedStatistic DGRHS.Gaussian.sourceKernelParticleStatistic
    DGRHS.Decoupling.offDiagonalSum
  simp only [ne_eq,ite_not]
  ring

lemma factorialCanonical_positive_uniform (h : S×S→ℝ) (hh : Measurable h)
    (C β : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y,h (x,y)=h (y,x))
    (hc : ∀ᵐ y ∂μ,∫ x,h (x,y) ∂μ=0)
    (hβ : 0≤β) (hsmall : β*(attractiveMomentConstant*C)<1) :
    ∀ N : ℕ,Integrable (fun x : Fin N→S => Real.exp
      (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N=>μ)) ∧
      (∫ x : Fin N→S,Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N=>μ)) ≤2/(1-(β*(attractiveMomentConstant*C))^2) := by
  intro N
  have ht : |-β| * (attractiveMomentConstant*C)<1 := by
    simpa only [abs_neg,abs_of_nonneg hβ] using hsmall
  have he : (fun x : Fin N→S => Real.exp ((-β)*attractiveNormalizedStatistic N h x))=
      (fun x => Real.exp (β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [attractiveStatistic_eq_neg_normalized]
    congr 1
    ring
  have hu := attractiveCanonical_uniform_exponential μ h hh C hC hs hc (-β) ht N
  rw [he] at hu
  simpa only [neg_mul,neg_sq] using hu

lemma factorialCanonical_positive_comparison (h k : S×S→ℝ)
    (hh : Measurable h) (hk : Measurable k) (C D β : ℝ)
    (hC : RowFactorialMoments μ h C) (hD : RowFactorialMoments μ k D)
    (hs : ∀ x y,h (x,y)=h (y,x)) (ks : ∀ x y,k (x,y)=k (y,x))
    (hc : ∀ᵐ y ∂μ,∫ x,h (x,y) ∂μ=0) (kc : ∀ᵐ y ∂μ,∫ x,k (x,y) ∂μ=0)
    (hβ : 0≤β) (hsmallC : β*(attractiveMomentConstant*C)<1)
    (hsmallD : β*(attractiveMomentConstant*D)<1) (N : ℕ) :
    let h2 := joint_memLp μ h hh C hC 2 (by omega)
    let k2 := joint_memLp μ k hk D hD 2 (by omega)
    |(∫ x : Fin N→S,Real.exp (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N=>μ))-
     (∫ x : Fin N→S,Real.exp (β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x)
      ∂Measure.pi (fun _ : Fin N=>μ))| ≤
      (β/2*Real.sqrt 2)*‖(h2.sub k2).toLp (fun z=>h z-k z)‖*
        (Real.sqrt (2/(1-(β*(attractiveMomentConstant*C))^2))+
         Real.sqrt (2/(1-(β*(attractiveMomentConstant*D))^2))) := by
  dsimp only
  let h2 := joint_memLp μ h hh C hC 2 (by omega)
  let k2 := joint_memLp μ k hk D hD 2 (by omega)
  have hcr : ∀ᵐ x ∂μ,∫ y,h (x,y) ∂μ=0 := by
    filter_upwards [hc] with x hx
    simpa only [hs] using hx
  have kcr : ∀ᵐ x ∂μ,∫ y,k (x,y) ∂μ=0 := by
    filter_upwards [kc] with x hx
    simpa only [ks] using hx
  have hU := factorialCanonical_positive_uniform h hh C β hC hs hc hβ hsmallC N
  have kU := factorialCanonical_positive_uniform k hk D β hD ks kc hβ hsmallD N
  have hiH : Integrable (fun x : Fin N→S => Real.exp
      (-(-β)*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N=>μ)) := by simpa only [neg_neg] using hU.1
  have hiK : Integrable (fun x : Fin N→S => Real.exp
      (-(-β)*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x))
      (Measure.pi (fun _ : Fin N=>μ)) := by simpa only [neg_neg] using kU.1
  have hb := DGRHS.CLT.canonical_partition_difference_le h k hh hk h2 k2
    (Filter.Eventually.of_forall fun z => hs z.2 z.1)
    (Filter.Eventually.of_forall fun z => ks z.2 z.1) hcr kcr (-β) hiH hiK
  simp only [neg_neg,abs_neg,abs_of_nonneg hβ] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (Real.sqrt_le_sqrt hU.2) (Real.sqrt_le_sqrt kU.2)) (by positivity)

end DGRHS.Attractive
#check @DGRHS.Attractive.factorialCanonical_positive_uniform
#check @DGRHS.Attractive.factorialCanonical_positive_comparison
#print axioms DGRHS.Attractive.attractiveStatistic_eq_neg_normalized
#print axioms DGRHS.Attractive.factorialCanonical_positive_uniform
#print axioms DGRHS.Attractive.factorialCanonical_positive_comparison
