import DGRHS.Gaussian.SourceRepulsiveLogRateCanonical
import DGRHS.Gaussian.SourceRepulsiveLogRateOneBody
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Original REPULSIVE logarithmic quantitative source partition, all beta>=0.
Source504-529 and1939-2158; source SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
The basis/determinant is the same actual full centered mean-zero operator used
by the canonical rate. The literal source energy is restored via its proper
one-body potential, not a supplied affine convergence or rate premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology InnerProductSpace
namespace DGRHS.SourceRepulsiveLogRate
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι]

lemma half_power_le_shifted_power (n c : ℝ) (hn : 1≤n) (hc : 0≤c) (hc1 : c≤1/2) :
    1/Real.sqrt n≤(Real.exp 1+1)^c*(Real.exp 1+n)^(-c) := by
  have hp : 0<n := lt_of_lt_of_le zero_lt_one hn
  have h1 : n^(-(1/2:ℝ))≤n^(-c) := Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have h2 := inverse_rpow_comparison (Real.exp 1+n) n (Real.exp 1+1) c
    (by positivity) hp (by positivity) hc
    (by nlinarith [mul_nonneg (Real.exp_pos (1:ℝ)).le (sub_nonneg.mpr hn)])
  rw [Real.sqrt_eq_rpow,one_div,←Real.rpow_neg hp.le]
  exact h1.trans h2

lemma partition_tendsto_of_power_error (Z : ℕ→ℝ) (z C c : ℝ) (hc : 0<c)
    (h : ∀ N,1≤N → |Z N-z|≤C*(Real.exp 1+(N:ℝ))^(-c)) :
    Tendsto Z atTop (𝓝 z) := by
  have hbase : Tendsto (fun N : ℕ=>Real.exp 1+(N:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N=>le_add_of_nonneg_left (Real.exp_pos _).le) tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_neg_atTop hc).comp hbase
  have hc' := tendsto_const_nhds.mul ht (a:=C)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun N=>norm_nonneg (Z N-z))
    ((eventually_ge_atTop 1).mono fun N hN=>?_) (by simpa using hc')
  simpa only [Real.norm_eq_abs] using h N hN

/-- Exact original logarithmic branch with all physical inputs constructed.
Only the original quantitative potential tail is assumed; no beta upper bound,
feature, spectral matching, Gaussian field, rate or uniform moment hypothesis.
The explicit positive-N convention retains N=1 and beta=0. -/
theorem exists_source_partition_rate (β : ℝ) (hβ : 0≤β)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x=>Real.exp (-4*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
    let h := hoeffdingCentered μ logPhysicalPair
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ,h p.swap=h p) (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧ (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i)=eig i • e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i=>β*eig i) ∧
      HasProd (fun i=>(1+β*eig i)*Real.exp (-(β*eig i))) (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)) ∧
      Tendsto (fun N=>∫ x : Fin N→EuclideanSpace ℝ ι,
        Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
        ∂Measure.pi (fun _ : Fin N=>μ)) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹)) ∧
      ∃ c C : ℝ,0<c ∧ c≤1/2 ∧ 0≤C ∧ ∀ N : ℕ,1≤N →
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
        |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
            (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x) ∂Measure.pi (fun _ : Fin N=>μ))-
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹|≤
          C*(Real.exp 1+(N:ℝ))^(-c) := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun (x y : EuclideanSpace ℝ ι)=>logPhysicalPair (x,y)
  let h := hoeffdingCentered μ logPhysicalPair
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  obtain ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,hT,c,CR,hc0,hc1,hCR,hRate⟩ :=
    exists_canonical_partition_rate β hβ hd ρ M hM hρ hpair htail
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i=>β*eig i)))⁻¹
  by_cases hzero : β=0
  · subst β
    have hz : z=1 := by simp [z,DGRHS.Kernel.regularizedDet]
    refine ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,?_,c,0,hc0,hc1,le_rfl,?_⟩
    · simpa [DGRHS.Kernel.regularizedDet] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(1:ℝ)) atTop (𝓝 1))
    · intro N hN
      constructor
      · simpa only [neg_zero,zero_mul,Real.exp_zero] using
          (integrable_const (1:ℝ) : Integrable (fun _ : Fin N→EuclideanSpace ℝ ι=>(1:ℝ)) (Measure.pi (fun _ : Fin N=>μ)))
      · simp [z,DGRHS.Kernel.regularizedDet]
  have hβp : 0<β := lt_of_le_of_ne hβ (Ne.symm hzero)
  obtain ⟨D,hD0,hComp⟩ := exists_affine_comparison_constant β hβp hd ρ M hM hρ hpair htail
  let C := D*(Real.exp 1+1)^c+Real.exp (β*I)*CR
  have hC0 : 0≤C := by dsimp [C];positivity
  have hMain (N : ℕ) (hN : 1≤N) :
      |sourceAffinePartition μ β I h F N-Real.exp (β*I)*z|≤C*(Real.exp 1+(N:ℝ))^(-c) := by
    have hn : (1:ℝ)≤N := by exact_mod_cast hN
    have hAff : |sourceAffinePartition μ β I h F N-Real.exp (β*I)*canonicalPartition μ β h N|≤
        D*(Real.exp 1+1)^c*(Real.exp 1+(N:ℝ))^(-c) := by
      calc
        _ ≤ D/Real.sqrt (N:ℝ) := (hComp N hN).2
        _ = D*(1/Real.sqrt (N:ℝ)) := by ring
        _ ≤ _ := by simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_left (half_power_le_shifted_power (N:ℝ) c hn hc0.le hc1) hD0
    have hCan : |Real.exp (β*I)*canonicalPartition μ β h N-Real.exp (β*I)*z|≤
        Real.exp (β*I)*CR*(Real.exp 1+(N:ℝ))^(-c) := by
      rw [←mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc,z] using mul_le_mul_of_nonneg_left (hRate N hN).2 (Real.exp_pos (β*I)).le
    calc
      _ ≤ |sourceAffinePartition μ β I h F N-Real.exp (β*I)*canonicalPartition μ β h N|+
          |Real.exp (β*I)*canonicalPartition μ β h N-Real.exp (β*I)*z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hAff hCan
      _ = _ := by dsimp [C];ring
  have hLiteral (N : ℕ) (hN : 1≤N) :
      Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
        (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)) (Measure.pi (fun _ : Fin N=>μ)) ∧
      |(∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp
        (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x) ∂Measure.pi (fun _ : Fin N=>μ))-
        Real.exp (β*I)*z|≤C*(Real.exp 1+(N:ℝ))^(-c) := by
    constructor
    · have hE : (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))=
          (fun x=>Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)) := by
        funext x
        congr 1
        exact DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent h F I β (by omega) x
      rw [hE]
      exact (hComp N hN).1
    · rw [sourceEnergy_partition_eq_affine μ β I h F N hN]
      exact hMain N hN
  exact ⟨hs,hc,κ,eig,e,hκ,he,hD,hProd,
    partition_tendsto_of_power_error _ (Real.exp (β*I)*z) C c hc0 (fun N hN=>(hLiteral N hN).2),
    c,C,hc0,hc1,hC0,hLiteral⟩
end DGRHS.SourceRepulsiveLogRate
#check @DGRHS.SourceRepulsiveLogRate.half_power_le_shifted_power
#print axioms DGRHS.SourceRepulsiveLogRate.half_power_le_shifted_power
#check @DGRHS.SourceRepulsiveLogRate.partition_tendsto_of_power_error
#print axioms DGRHS.SourceRepulsiveLogRate.partition_tendsto_of_power_error
#check @DGRHS.SourceRepulsiveLogRate.exists_source_partition_rate
#print axioms DGRHS.SourceRepulsiveLogRate.exists_source_partition_rate
