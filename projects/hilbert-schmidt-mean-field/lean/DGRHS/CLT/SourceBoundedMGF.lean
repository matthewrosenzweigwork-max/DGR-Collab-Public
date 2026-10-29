/- The bounded source MGF clause: mixed UI is derived from native Hoeffding
and actual doubled weight moments. The SAME basis/process determines the
Gaussian transform and the particle joint CLT. Physical weight moments are
explicit remaining inputs, never the desired mixed limit. -/
import DGRHS.CLT.SourcePartitionFactory
import DGRHS.CLT.BoundedLinearWeightMoments
import DGRHS.Gaussian.HilbertTiltedResolvent
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

theorem exists_sourceBoundedMGF [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ z ∂μ.prod μ, h z.swap = h z)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (hpos : ∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : ι → ℕ) (hf : Function.Injective f),
      Countable ι ∧ (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
    ∀ β : ℝ, 0 ≤ β → ∃ R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
      (∀ v, R v + β • DGRHS.Kernel.integralOperator h hh (R v) = v) ∧
      (∀ v, R (v + β • DGRHS.Kernel.integralOperator h hh v) = v) ∧
    ∀ (v : Lp ℝ 2 μ), (∫ x,v x ∂μ) = 0 →
      ∀ K : ℝ, (∀ᵐ x ∂μ, |v x| ≤ K) →
      ∀ (F : S → ℝ), Integrable F μ → ∀ (I p C : ℝ), 1 < p →
      (∀ N, Integrable (fun x : Fin N → S => Real.exp ((2*p)*sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ))) →
      (∀ N, (∫ x : Fin N → S, Real.exp ((2*p)*sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C) →
      (∀ N, Integrable (fun x : Fin N → S => Real.exp ((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)))
        ((Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N))) ∧
      Tendsto (fun N => ∫ x : Fin N → S,Real.exp ((Real.sqrt N)⁻¹*∑ i : Fin N,v (x i))
        ∂(Measure.pi (fun _ : Fin N => μ)).tilted (sourceParticleExponent h F I β N)) atTop
        (𝓝 (Real.exp (inner ℝ v (R v)/2))) := by
  obtain ⟨ι,eig,b,f,hf,hcount,hb,hjoint⟩ :=
    exists_originalKernelSourceExponentCLT (j := Fin 1) h hh hs hc
  letI := hcount
  have hsum := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq h hh eig b hb
  have heig : ∀ i, 0 ≤ eig i := by
    intro i
    have hi := hpos (b i)
    rw [hb,real_inner_smul_right,real_inner_self_eq_norm_sq,b.orthonormal.1 i,one_pow,mul_one] at hi
    exact hi
  refine ⟨ι,eig,b,f,hf,hcount,hb,fun β hβ => ?_⟩
  have hmargin : ∀ i, 0 < 1+β*eig i := fun i => by nlinarith [mul_nonneg hβ (heig i)]
  obtain ⟨R,hR1,hR2,hRc,htransform⟩ := DGRHS.Gaussian.exists_hilbert_tilt_resolvent
    (DGRHS.Kernel.integralOperator h hh) (DGRHS.Kernel.integralOperator_isSymmetric h hh hs)
    b eig hb β hsum hmargin f hf
  refine ⟨R,hR1,hR2,fun v hv K hK F hF I p C hp hm hC => ?_⟩
  let Y := fun N => sourceParticleExponent h F I β N
  let A := fun N (x : Fin N → S) => (Real.sqrt N)⁻¹*∑ i : Fin N,v (x i)
  let G := fun ω => -(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω
  let W := DGRHS.Gaussian.indexedGaussianIsometry b f hf v
  let c := β*(∫ x,F x ∂μ)-β*I
  let D := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹
  have hj := hjoint (fun _ : Fin 1 => v) (fun _ => hv) F hF β I
  have hYweak : TendstoInDistribution Y atTop (fun ω => G ω+c)
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
    convert hj.continuous_comp (g := Prod.snd) continuous_snd using 1
    · rfl
    · funext ω; dsimp [G,c]; ring
  have hMixweak : TendstoInDistribution (fun N x => A N x+Y N x) atTop
      (fun ω => (W ω-(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)+c)
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
    have hcont : Continuous (fun z : EuclideanSpace ℝ (Fin 1 ⊕ Unit) × ℝ =>
        z.1 (Sum.inl 0)+z.2) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 1 ⊕ Unit => ℝ) (Sum.inl 0)).comp continuous_fst).add continuous_snd
    convert hj.continuous_comp (g := fun z => z.1 (Sum.inl 0)+z.2) hcont using 1
    · rfl
    · funext ω; dsimp [W,c,jointReadoutVector]; ring
  have hMixed := bounded_linear_weight_exponential_bound v hv K hK Y
    hYweak.forall_aemeasurable p C hm hC
  have hG := DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_weak_margin
    β eig hmargin hsum f hf
  have hDenProper := integrable_exp_add_const G hG.1 c
  have hNumProper := integrable_exp_add_const
    (fun ω => W ω-(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω) (htransform v).1 c
  have htNum := exponential_integral_tendsto_of_distribution_moment _ _ hMixweak hNumProper p _ hp
    (fun N => (hMixed N).1) (fun N => (hMixed N).2)
  have htDen := exponential_integral_tendsto_of_distribution_moment _ _ hYweak hDenProper
    (2*p) C (by linarith) hm hC
  have hvDen : (∫ ω,Real.exp (G ω+c) ∂IsonormalProcess.iidStdGaussian) = Real.exp c*D := by
    rw [integral_exp_add_const]
    exact congrArg (fun z => Real.exp c*z) hG.2
  have hvNum : (∫ ω,Real.exp ((W ω-(β/2)*DGRHS.Gaussian.centeredGaussianChaos eig f ω)+c)
      ∂IsonormalProcess.iidStdGaussian) = Real.exp c*D*Real.exp (inner ℝ v (R v)/2) := by
    rw [integral_exp_add_const,(htransform v).2,mul_assoc]
  have hDenNe : Real.exp c*D ≠ 0 := by
    rw [←hvDen]
    exact (integral_exp_pos hDenProper).ne'
  rw [hvDen] at htDen
  rw [hvNum] at htNum
  refine ⟨fun N => ?_,?_⟩
  · have hiY := integrable_exp_of_higher_exp (hYweak.forall_aemeasurable N)
      (show 1 ≤ 2*p by linarith) (hm N)
    have hiMix := integrable_exp_of_higher_exp (hMixweak.forall_aemeasurable N) hp.le (hMixed N).1
    apply (integrable_tilted_iff hiY _).mpr
    apply hiMix.congr
    exact ae_of_all _ fun x => by
      change Real.exp (A N x+Y N x) = Real.exp (Y N x)*Real.exp (A N x)
      rw [Real.exp_add,mul_comm]
  · have ht := htNum.div htDen hDenNe
    have he : (Real.exp c*D*Real.exp (inner ℝ v (R v)/2))/(Real.exp c*D) =
        Real.exp (inner ℝ v (R v)/2) := by exact mul_div_cancel_left₀ _ hDenNe
    rw [he] at ht
    convert ht using 1
    funext N
    rw [integral_exp_tilted]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change Real.exp (Y N x+A N x) = Real.exp (A N x+Y N x)
      rw [add_comm]
end DGRHS.CLT
#print axioms DGRHS.CLT.exists_sourceBoundedMGF
#check @DGRHS.CLT.exists_sourceBoundedMGF
