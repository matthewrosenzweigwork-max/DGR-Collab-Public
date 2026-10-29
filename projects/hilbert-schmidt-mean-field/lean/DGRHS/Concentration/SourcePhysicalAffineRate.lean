/- Full positive-Riesz affine source rate. Proper doubled source moments
are derived from the actual canonical factory and an AE bounded potential.
No rate, variance, normalizer limit or determinant-continuity premise. -/
import DGRHS.Concentration.SourcePhysicalRate
import DGRHS.Concentration.SourceRieszOneBodyInputs
import DGRHS.Concentration.SourceAffineLog
import DGRHS.CLT.SourceWeightCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.Concentration
universe u
open DGRHS.Gaussian

lemma partition_tendsto_of_log_error (Z : ℕ→ℝ) (z C q : ℝ) (hq : 0<q)
    (h : ∀ N,1≤N→|Z N-z|≤C*(Real.log (Real.exp 1+(N:ℝ)))^(-q)) :
    Tendsto Z atTop (𝓝 z) := by
  have hbase : Tendsto (fun N : ℕ ↦ Real.exp 1+(N:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun N ↦ le_add_of_nonneg_left (Real.exp_pos _).le) tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_neg_atTop hq).comp (Real.tendsto_log_atTop.comp hbase)
  have hc := tendsto_const_nhds.mul ht (a := C)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun N ↦ norm_nonneg (Z N-z))
    ((eventually_ge_atTop 1).mono fun N hN ↦ ?_) (by simpa using hc)
  simpa only [Real.norm_eq_abs] using h N hN

/-- The one-body potential is a true L2 function with an actual AE upper bound.
The physical potential instance is supplied separately by its source factory. -/
theorem gaussianRieszPhysical_affine_partition_rate {ι : Type u} [Fintype ι]
    (s β : ℝ) (hs : 0<s) (hβ : 0≤β) (ha : 0<(Fintype.card ι:ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (F : EuclideanSpace ℝ ι→ℝ) (hF : MemLp F 2 (gaussianRieszDensityMeasure ρ))
    (K I : ℝ) (hK : ∀ᵐ x ∂gaussianRieszDensityMeasure ρ,F x≤K) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
    let c := β*(∫ y,F y ∂μ)-β*I
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (κ : Type u) (eig : κ→ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i,DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i)=eig i•e i) ∧
      0<DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      Tendsto (sourceAffinePartition μ β I h F) atTop
        (𝓝 (Real.exp c*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N ↦ Real.log (sourceAffinePartition μ β I h F N)) atTop
        (𝓝 (c+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∃ C : ℝ,0≤C ∧ ∀ N,1≤N→
        Integrable (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
          (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N ↦ μ)) ∧
        Real.exp c≤sourceAffinePartition μ β I h F N ∧
        |sourceAffinePartition μ β I h F N-
          Real.exp c*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) ∧
        |Real.log (sourceAffinePartition μ β I h F N)-
          (c+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))|≤
          C*(Real.log (Real.exp 1+(N:ℝ)))^(-(((Fintype.card ι:ℝ)-2*s)/(2*s))) := by
  let μ := gaussianRieszDensityMeasure ρ
  let h := hoeffdingCentered μ (gaussianRieszPhysicalPair (ι := ι) s)
  let c := β*(∫ y,F y ∂μ)-β*I
  let q := ((Fintype.card ι:ℝ)-2*s)/(2*s)
  have hq : 0<q := by dsimp [q];apply div_pos _ (by positivity);linarith
  obtain ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,hT,hLog,CR,hCR,hRate⟩ :=
    gaussianRieszPhysical_log_partition_rate s β hs hβ ha ρ M hM hρ
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹
  obtain ⟨hhInputs, MS, MC, hS', hC⟩ :=
    gaussianRieszPhysical_oneBodyComparison_inputs s β hs hβ ha ρ M hM hρ
      F hF K I hK
  let L := |β| * Real.sqrt (variance F μ)*(Real.sqrt MS+Real.exp c*Real.sqrt MC)
  have hL : 0≤L := by dsimp [L];positivity
  have hComp (N : ℕ) (hN : 1 ≤ N) :=
    sourceAffinePartition_comparison μ β I h hhInputs F hF N hN MS MC
      (hS' N hN).1 (hC N hN).1 (hS' N hN).2 (hC N hN).2
  have hOne (N : ℕ) (hN : 1≤N) : 1≤canonicalPartition μ β h N := by
    have hb := sourceAffinePartition_lower μ β 0 h hh hCan (fun _ ↦ 0) (memLp_const 0) N hN
      (by simpa [DGRHS.CLT.sourceParticleExponent] using (hRate N hN).1)
    simpa [sourceAffinePartition,DGRHS.CLT.sourceParticleExponent,canonicalPartition] using hb
  have hz : 1≤z := ge_of_tendsto hT ((eventually_ge_atTop 1).mono fun N hN ↦ hOne N hN)
  let H := (Real.log (Real.exp 1+1)+2*q)^q
  let D := L*H+Real.exp c*CR
  have hH : 0≤H := by
    apply Real.rpow_nonneg
    have hb : 0<Real.log (Real.exp 1+1) := Real.log_pos (by linarith [Real.exp_pos (1:ℝ)])
    linarith
  have hD0 : 0≤D := add_nonneg (mul_nonneg hL hH) (mul_nonneg (Real.exp_pos c).le hCR)
  let C := (1+Real.exp (-c))*D
  have hC0 : 0≤C := by dsimp [C];positivity
  have hMain (N : ℕ) (hN : 1≤N) :
      |sourceAffinePartition μ β I h F N-Real.exp c*z|≤D*(Real.log (Real.exp 1+(N:ℝ)))^(-q) := by
    have hn : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
    have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
    have hab := half_power_le_log_rate (N:ℝ) q hn1 hq
    have he : L/Real.sqrt (N:ℝ)=L*(N:ℝ)^(-(1/2:ℝ)) := by
      rw [Real.sqrt_eq_rpow,Real.rpow_neg hn.le]
      ring
    have hcmp : |sourceAffinePartition μ β I h F N-Real.exp c*canonicalPartition μ β h N|≤
        L*H*(Real.log (Real.exp 1+(N:ℝ)))^(-q) := by
      have hb := (hComp N hN).2.2
      change _≤L/Real.sqrt (N:ℝ) at hb
      rw [he] at hb
      exact hb.trans (by simpa only [H,mul_assoc] using mul_le_mul_of_nonneg_left hab hL)
    have hcan : |Real.exp c*canonicalPartition μ β h N-Real.exp c*z|≤
        Real.exp c*CR*(Real.log (Real.exp 1+(N:ℝ)))^(-q) := by
      rw [←mul_sub,abs_mul,abs_of_pos (Real.exp_pos _)]
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left (hRate N hN).2.1 (Real.exp_pos c).le)
    calc
      _ ≤ |sourceAffinePartition μ β I h F N-Real.exp c*canonicalPartition μ β h N|+
          |Real.exp c*canonicalPartition μ β h N-Real.exp c*z| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hcmp hcan
      _ = _ := by dsimp [D];ring
  have hLow (N : ℕ) (hN : 1≤N) : Real.exp c≤sourceAffinePartition μ β I h F N :=
    sourceAffinePartition_lower μ β I h hh hCan F hF N hN (hComp N hN).1
  have hLogRate (N : ℕ) (hN : 1≤N) :
      |Real.log (sourceAffinePartition μ β I h F N)-(c+Real.log z)|≤
        (Real.exp (-c)*D)*(Real.log (Real.exp 1+(N:ℝ)))^(-q) := by
    calc
      _ ≤ Real.exp (-c)*|sourceAffinePartition μ β I h F N-Real.exp c*z| :=
        affine_log_difference_le c _ z (hLow N hN) hz
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hMain N hN) (Real.exp_pos (-c)).le
  refine ⟨hh,hSym,hCan,κ,eig,e,hκ,he,hD,
    partition_tendsto_of_log_error _ (Real.exp c*z) D q hq hMain,
    partition_tendsto_of_log_error _ (c+Real.log z) (Real.exp (-c)*D) q hq hLogRate,C,hC0,?_⟩
  intro N hN
  have hE : (fun x : Fin N→EuclideanSpace ℝ ι ↦ Real.exp
      (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)) =
      (fun x ↦ Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)) := by
    funext x
    congr 1
    exact congrFun (DGRHS.CLT.sourceEnergyExponent_eq (N := N) h F I β (by omega)) x
  have hw : 0≤(Real.log (Real.exp 1+(N:ℝ)))^(-q) := by
    apply Real.rpow_nonneg
    apply Real.log_nonneg
    have hn : (1:ℝ)≤N := by exact_mod_cast hN
    linarith [Real.exp_pos (1:ℝ)]
  refine ⟨by rw [hE];exact (hComp N hN).1,hLow N hN,?_,?_⟩
  · exact (hMain N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C];nlinarith [Real.exp_pos (-c)]) hw)
  · exact (hLogRate N hN).trans (mul_le_mul_of_nonneg_right
      (by dsimp [C];nlinarith [Real.exp_pos (-c)]) hw)

end DGRHS.Concentration
#print axioms DGRHS.Concentration.partition_tendsto_of_log_error
#print axioms DGRHS.Concentration.gaussianRieszPhysical_affine_partition_rate
#check @DGRHS.Concentration.gaussianRieszPhysical_affine_partition_rate
