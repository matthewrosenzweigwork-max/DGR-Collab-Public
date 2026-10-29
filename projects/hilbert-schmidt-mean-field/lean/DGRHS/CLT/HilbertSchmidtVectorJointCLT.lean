/- Actual finitely many L2 readouts and HS quadratic limit on one Gaussian field. -/
import DGRHS.CLT.HilbertSchmidtJointCLT
import DGRHS.CLT.ChangingProjectionCriterion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S j : Type*} [MeasurableSpace S] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

def jointReadoutVector (r : j → ℝ) (q : ℝ) : EuclideanSpace ℝ (j ⊕ Unit) :=
  WithLp.toLp 2 (Sum.elim r (fun _ => q))

lemma jointReadoutVector_inner (r : j → ℝ) (q : ℝ) (t : EuclideanSpace ℝ (j ⊕ Unit)) :
    inner ℝ (jointReadoutVector r q) t =
      (∑ l : j, r l * t (Sum.inl l)) + q * t (Sum.inr ()) := by
  classical
  rw [PiLp.inner_apply,Fintype.sum_sum_type]
  simp [jointReadoutVector,mul_comm]

theorem hilbertSchmidtParticleVectorJointCLT {ι : Type*} [Countable ι]
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
    (hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i)
    (f : ι → ℕ) (hf : Function.Injective f)
    (v : j → Lp ℝ 2 μ) (hv : ∀ l, (∫ x, v l x ∂μ) = 0) :
    TendstoInDistribution
      (fun N (x : Fin N → S) => jointReadoutVector
        (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
        (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) atTop
      (fun ω => jointReadoutVector
        (fun l => DGRHS.Gaussian.indexedGaussianIsometry b f hf (v l) ω)
        (DGRHS.Gaussian.centeredGaussianChaos eig f ω))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  let W := DGRHS.Gaussian.indexedGaussianIsometry b f hf
  let Q := DGRHS.Gaussian.centeredGaussianChaos eig f
  let X := fun N (x : Fin N → S) => jointReadoutVector
    (fun l => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i))
    (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
  let Y := fun ω => jointReadoutVector (fun l => W (v l) ω) (Q ω)
  have hX : ∀ N, AEMeasurable (X N) (Measure.pi (fun _ : Fin N => μ)) := by
    intro N
    have hA : ∀ l : j, Measurable (fun x : Fin N → S => (Real.sqrt N)⁻¹*∑ i : Fin N, v l (x i)) := by
      intro l
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro i _
      exact (Lp.stronglyMeasurable (v l)).measurable.comp (measurable_pi_apply i)
    have hq := (memLp_normalizedOffDiagonalSum (ι := Fin N) h hh).aemeasurable
    dsimp [X,jointReadoutVector]
    apply (PiLp.continuous_toLp 2 (fun _ : j ⊕ Unit => ℝ)).measurable.comp_aemeasurable
    apply aemeasurable_pi_lambda
    intro l
    cases l with
    | inl l => exact (hA l).aemeasurable
    | inr l => exact hq
  have hY : AEMeasurable Y IsonormalProcess.iidStdGaussian := by
    dsimp [Y,jointReadoutVector]
    apply (PiLp.continuous_toLp 2 (fun _ : j ⊕ Unit => ℝ)).measurable.comp_aemeasurable
    apply aemeasurable_pi_lambda
    intro l
    cases l with
    | inl l => exact (Lp.memLp (W (v l))).aemeasurable
    | inr l => exact (Lp.memLp Q).aemeasurable
  apply tendstoInDistribution_changing_inner_projections _ X Y hX hY
  intro t
  let c := fun l : j => t (Sum.inl l)
  let vt : Lp ℝ 2 μ := ∑ l : j, c l • v l
  have hvt := coeFn_finiteLpCombination c v
  have hmean : (∫ x, vt x ∂μ) = 0 := by
    rw [integral_congr_ae hvt,integral_finsetSum]
    · simp_rw [integral_const_mul,hv,mul_zero]
      exact Finset.sum_const_zero
    · intro l _
      exact ((Lp.memLp (v l)).integrable (by norm_num)).const_mul (c l)
  let P := fun z : ℝ × ℝ => z.1 + t (Sum.inr ()) * z.2
  have hlimit := (hilbertSchmidtParticleJointCLT h hhm hh hs hc eig b hb f hf vt hmean).continuous_comp
    (g := P) (by fun_prop)
  refine hlimit.congr (fun N => ?_) ?_
  · have hp : ∀ᵐ x : Fin N → S ∂Measure.pi (fun _ : Fin N => μ),
        ∀ i : Fin N, vt (x i) = ∑ l : j, c l * v l (x i) :=
      ae_all_iff.mpr fun i => (measurePreserving_eval
        (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hvt
    filter_upwards [hp] with x hx
    change (Real.sqrt N)⁻¹*∑ i : Fin N, vt (x i) + t (Sum.inr ()) *
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x = inner ℝ (X N x) t
    rw [jointReadoutVector_inner]
    simp_rw [hx,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [c]
      ring
    · ring
  · have hw : W vt = ∑ l : j, c l • W (v l) := by simp only [vt,map_sum,map_smul]
    have he := coeFn_finiteLpCombination c (fun l => W (v l))
    rw [← hw] at he
    filter_upwards [he] with ω hω
    change W vt ω + t (Sum.inr ()) * Q ω = inner ℝ (Y ω) t
    rw [jointReadoutVector_inner,hω]
    dsimp [c]
    congr 1
    · apply Finset.sum_congr rfl
      intro l _
      ring
    · ring
end DGRHS.CLT
#print axioms DGRHS.CLT.jointReadoutVector_inner
#print axioms DGRHS.CLT.hilbertSchmidtParticleVectorJointCLT
#check @DGRHS.CLT.hilbertSchmidtParticleVectorJointCLT
