/- Original source Jensen lower bound eq:KlowerJensen and the common
literal logarithmic partition cap. Proper exponent mean is constructed from
the SAME canonical kernel and actual potential; no lower bound is assumed. -/
import DGRHS.CLT.SourceLogSingularIdentification
import DGRHS.Gaussian.LogPhysicalCenteredL2
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Entropy

lemma exponential_integral_ge_mean {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (u : S→ℝ) (hi : Integrable u μ)
    (he : Integrable (fun x=>Real.exp (u x)) μ) :
    Real.exp (∫ x,u x ∂μ)≤∫ x,Real.exp (u x) ∂μ := by
  let m := ∫ x,u x ∂μ
  let g := fun x=>Real.exp m*(1+u x-m)
  have hg : Integrable g μ :=
    (((integrable_const (1:ℝ)).add hi).sub (integrable_const m)).const_mul _
  have hb (x : S) : g x≤Real.exp (u x) := by
    calc
      _ ≤ Real.exp m*Real.exp (u x-m) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (u x-m)]) (Real.exp_pos m).le
      _ = _ := by rw [←Real.exp_add];congr 1;ring
  have hm : (∫ x,g x ∂μ)=Real.exp m := by
    dsimp only [g]
    rw [integral_const_mul,
      integral_sub (f:=fun x=>1+u x) (g:=fun _=>m)
        ((integrable_const (1:ℝ)).add hi) (integrable_const m),
      integral_add (f:=fun _=>(1:ℝ)) (g:=u) (integrable_const (1:ℝ)) hi]
    simp only [integral_const,probReal_univ,one_smul]
    dsimp only [m]
    ring
  exact hm.symm.le.trans (integral_mono hg he hb)

open DGRHS.CLT DGRHS.Gaussian

lemma sourceParticleExponent_proper_mean {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (h : S×S→ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hc : ∀ᵐ x ∂μ,∫ y,h (x,y) ∂μ=0)
    (F : S→ℝ) (hF : Integrable F μ) (I β : ℝ)
    (hMean : (∫ x,F x ∂μ)=2*I) (N : ℕ) (hN : 1≤N) :
    Integrable (sourceParticleExponent h F I β N) (Measure.pi (fun _ : Fin N=>μ)) ∧
      (∫ x,sourceParticleExponent h F I β N x ∂Measure.pi (fun _ : Fin N=>μ))=β*I := by
  classical
  let P := Measure.pi (fun _ : Fin N=>μ)
  have ho : Integrable (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι:=Fin N) h) P :=
    (DGRHS.CanonicalVariance.integrable_offDiagonalSum μ h hh).const_mul _
  have hsum : Integrable (fun x : Fin N→S=>∑ i : Fin N,F (x i)) P :=
    integrable_finsetSum _ (fun i _=>integrable_comp_eval (μ:=fun _ : Fin N=>μ) (i:=i) hF)
  have havg := hsum.const_mul (N:ℝ)⁻¹
  have hproper := ((ho.const_mul (-β/2)).add (havg.const_mul β)).sub (integrable_const (β*I))
  refine ⟨hproper,?_⟩
  have hzero : (∫ x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x ∂P)=0 := by
    unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum
    rw [integral_const_mul,
      DGRHS.CanonicalVariance.integral_offDiagonalSum_eq_zero μ h hh hc,mul_zero]
  have hs : (∫ x : Fin N→S,(∑ i : Fin N,F (x i)) ∂P)=(N:ℝ)*(2*I) := by
    rw [integral_finsetSum _ (fun i _=>integrable_comp_eval (μ:=fun _ : Fin N=>μ) (i:=i) hF)]
    simp_rw [integral_comp_eval (μ:=fun _ : Fin N=>μ) (i:=_) hF.aestronglyMeasurable]
    simp only [hMean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold sourceParticleExponent
  change (∫ x : Fin N→S,-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x+
    β*((N:ℝ)⁻¹*∑ i : Fin N,F (x i))-β*I ∂P)=β*I
  rw [integral_sub
      (f:=fun x=>-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x+
        β*((N:ℝ)⁻¹*∑ i : Fin N,F (x i))) (g:=fun _=>β*I)
      ((ho.const_mul (-β/2)).add (havg.const_mul β)) (integrable_const (β*I)),
    integral_add (f:=fun x=>-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      (g:=fun x=>β*((N:ℝ)⁻¹*∑ i : Fin N,F (x i)))
      (ho.const_mul (-β/2)) (havg.const_mul β),integral_const_mul,
    integral_const_mul,integral_const_mul,hzero,hs]
  simp only [integral_const,probReal_univ,one_smul]
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  <;> ring

variable {ι : Type*} [Fintype ι]

theorem sourceLogPartition_original_bounds (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ Cpf : ℝ,0<Cpf ∧ ∀ N : ℕ,1≤N →
      Real.exp ((β:ℝ)*DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
        (fun a b=>logPhysicalPair (a,b)))≤(sourceLogSingularPartition β ρ N).toReal ∧
      (sourceLogSingularPartition β ρ N).toReal≤Cpf := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let q := hoeffdingCentered μ logPhysicalPair
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  have hh : MemLp q 2 (μ.prod μ) := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
  have hc : ∀ᵐ x ∂μ,∫ y,q (x,y) ∂μ=0 := DGRHS.integral_centeredKernel_right μ W hpair
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hpair
  have hMean : (∫ x,F x ∂μ)=2*I := DGRHS.integral_potential μ W hpair
  obtain ⟨Cpf,hCpf,hUniform⟩ := sourceLogPartition_uniform (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair
  refine ⟨Cpf,hCpf,fun N hN=>?_⟩
  have hKe : (sourceLogSingularPartition β ρ N).toReal=
      ∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (-(β:ℝ)*(N:ℝ)*
        sourceCanonicalModulatedEnergy q F I N x) ∂Measure.pi (fun _ : Fin N=>μ) := by
    rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
      ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)]
  obtain ⟨hi,hU⟩ := hUniform N hN
  have hKa : (sourceLogSingularPartition β ρ N).toReal=
      ∫ x : Fin N→EuclideanSpace ℝ ι,Real.exp (sourceParticleExponent q F I (β:ℝ) N x)
        ∂Measure.pi (fun _ : Fin N=>μ) := by
    rw [hKe]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x=>congrArg Real.exp
      (sourceCanonicalModulatedEnergy_exponent (N:=N) q F I (β:ℝ) (by omega) x)
  change Integrable (fun x : Fin N→EuclideanSpace ℝ ι=>Real.exp
    (-(β:ℝ)*(N:ℝ)*sourceCanonicalModulatedEnergy q F I N x))
    (Measure.pi (fun _ : Fin N=>μ)) at hi
  simp_rw [sourceCanonicalModulatedEnergy_exponent (N:=N) q F I (β:ℝ) (by omega)] at hi
  obtain ⟨hproper,hm⟩ := sourceParticleExponent_proper_mean μ q hh hc F hF I (β:ℝ) hMean N hN
  have hJ := exponential_integral_ge_mean (Measure.pi (fun _ : Fin N=>μ))
    (sourceParticleExponent q F I (β:ℝ) N) hproper hi
  rw [hm] at hJ
  refine ⟨?_,?_⟩
  · rw [hKa]
    exact hJ
  · rw [hKe]
    exact hU

end DGRHS.Entropy
#check @DGRHS.Entropy.exponential_integral_ge_mean
#check @DGRHS.Entropy.sourceParticleExponent_proper_mean
#print axioms DGRHS.Entropy.exponential_integral_ge_mean
#print axioms DGRHS.Entropy.sourceParticleExponent_proper_mean
#check @DGRHS.Entropy.sourceLogPartition_original_bounds
#print axioms DGRHS.Entropy.sourceLogPartition_original_bounds
