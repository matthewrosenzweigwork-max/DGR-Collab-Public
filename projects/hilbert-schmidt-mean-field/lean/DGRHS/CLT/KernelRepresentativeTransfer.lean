/- UNCHECKED outside frozen proof. Close the representative gap for original
L2 kernels. Only unequal particle labels pull product-AE identities back; no
spatial diagonal or atom assumption is introduced. -/
import DGRHS.CLT.HilbertSchmidtChaosCLT
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
universe u
variable {S : Type u} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma normalizedOffDiagonalSum_congr_ae {J : Type*} [Fintype J]
    {h k : S × S → ℝ} (he : h =ᵐ[μ.prod μ] k) :
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := J) h =ᵐ[Measure.pi (fun _ : J => μ)]
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum k := by
  classical
  have hp : ∀ p : (Finset.univ : Finset J).offDiag,
      (fun x : J → S => h (x p.val.1, x p.val.2)) =ᵐ[Measure.pi (fun _ : J => μ)]
      (fun x => k (x p.val.1, x p.val.2)) := by
    intro p
    exact (DGRHS.Decoupling.pair_eval_measurePreserving μ p.val.1 p.val.2
      (Finset.mem_offDiag.mp p.property).2.2).quasiMeasurePreserving.ae he
  filter_upwards [ae_all_iff.mpr hp] with x hx
  unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
  congr 1
  exact Finset.sum_congr rfl (fun p hp => hx ⟨p,hp⟩)

lemma integralOperator_Lp_representative (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    DGRHS.Kernel.integralOperator (hh.toLp h) (Lp.memLp (hh.toLp h)) =
      DGRHS.Kernel.integralOperator h hh := by
  simp only [DGRHS.Kernel.integralOperator, Lp.toLp_coeFn]

/-- The original HS kernel endpoint, with actual spectrum and chaos constructed
from its L2 equivalence class. Measurability of a preferred representative is
not an extra source hypothesis. This is convergence of changing particle laws. -/
theorem exists_originalKernelChaosCLT [MeasurableSpace.CountablyGenerated S]
    (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0) :
    ∃ (ι : Type u) (eig : ι → ℝ) (b : HilbertBasis ι ℝ (Lp ℝ 2 μ))
      (f : {i // eig i ≠ 0} → ℕ),
      Countable ι ∧ Function.Injective f ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      TendstoInDistribution
        (fun N => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) h)
        atTop (DGRHS.Gaussian.centeredGaussianChaos (fun i : {i // eig i ≠ 0} => eig i.val) f)
        (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  let κ := hh.toLp h
  have he : (κ : S × S → ℝ) =ᵐ[μ.prod μ] h := hh.coeFn_toLp
  have hswap : ∀ᵐ p ∂μ.prod μ, κ p.swap = κ p := by
    filter_upwards [he, (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae he,
      hs] with p h1 h2 h3
    exact h2.trans (h3.trans h1.symm)
  have hcan : ∀ᵐ x ∂μ, (∫ y, κ (x,y) ∂μ) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod he, hc] with x hx hc
    exact (integral_congr_ae hx).trans hc
  obtain ⟨ι,eig,b,f,hcount,hf,hb,hlimit⟩ := exists_hilbertSchmidtParticleChaosCLT
    (κ : S × S → ℝ) (Lp.stronglyMeasurable κ).measurable (Lp.memLp κ) hswap hcan
  letI := hcount
  have hOp := integralOperator_Lp_representative h hh
  have hb' : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i := by
    intro i
    rw [← hOp]
    exact hb i
  refine ⟨ι,eig,b,f,hcount,hf,hb', ?_⟩
  refine ⟨fun N => (memLp_normalizedOffDiagonalSum (ι := Fin N) h hh).aemeasurable,
    hlimit.aemeasurable_limit, ?_⟩
  have hm : ∀ N, (Measure.pi (fun _ : Fin N => μ)).map
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) h) =
      (Measure.pi (fun _ : Fin N => μ)).map
        (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) (κ : S × S → ℝ)) :=
    fun N => Measure.map_congr (normalizedOffDiagonalSum_congr_ae (J := Fin N) he.symm)
  have hlaws : (fun N => (⟨(Measure.pi (fun _ : Fin N => μ)).map
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) h),
        (Measure.isProbabilityMeasure_map_iff
          (memLp_normalizedOffDiagonalSum (ι := Fin N) h hh).aemeasurable).mpr inferInstance⟩ :
      ProbabilityMeasure ℝ)) = (fun N => (⟨(Measure.pi (fun _ : Fin N => μ)).map
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := Fin N) (κ : S × S → ℝ)),
        (Measure.isProbabilityMeasure_map_iff (hlimit.forall_aemeasurable N)).mpr inferInstance⟩ :
      ProbabilityMeasure ℝ)) := by
    funext N
    exact Subtype.ext (hm N)
  rw [hlaws]
  exact hlimit.tendsto

end DGRHS.CLT
#print axioms DGRHS.CLT.normalizedOffDiagonalSum_congr_ae
#print axioms DGRHS.CLT.integralOperator_Lp_representative
#print axioms DGRHS.CLT.exists_originalKernelChaosCLT
