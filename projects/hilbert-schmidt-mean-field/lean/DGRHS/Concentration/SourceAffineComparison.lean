/- Quantitative affine source correction. The variance is proved from the
actual iid law, and both exponentials are proved proper before comparison. -/
import DGRHS.Concentration.EmpiricalVariance
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def sourceAffinePartition (β I : ℝ) (h : Ω×Ω→ℝ) (F : Ω→ℝ) (N : ℕ) : ℝ :=
  ∫ x : Fin N→Ω,Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x)
    ∂Measure.pi (fun _ : Fin N ↦ μ)

lemma sqrt_scaled_empirical_variance (β v : ℝ) (_hv : 0≤v) (N : ℕ) :
    Real.sqrt (β^2*((N:ℝ)⁻¹*v)) = |β| *Real.sqrt v/Real.sqrt (N:ℝ) := by
  rw [Real.sqrt_mul (sq_nonneg β),Real.sqrt_sq_eq_abs,
    Real.sqrt_mul (inv_nonneg.mpr (Nat.cast_nonneg N)),Real.sqrt_inv]
  ring

/-- A genuine finite-N comparison with explicit constants and no independence,
variance, partition comparison, or integrability conclusion as a premise. -/
theorem sourceAffinePartition_comparison (β I : ℝ) (h : Ω×Ω→ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (F : Ω→ℝ) (hF : MemLp F 2 μ)
    (N : ℕ) (hN : 1≤N) (MS MC : ℝ)
    (hS : Integrable (fun x : Fin N→Ω ↦ Real.exp
      (2*DGRHS.CLT.sourceParticleExponent h F I β N x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (hC : Integrable (fun x : Fin N→Ω ↦ Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N ↦ μ)))
    (bS : (∫ x : Fin N→Ω,Real.exp (2*DGRHS.CLT.sourceParticleExponent h F I β N x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MS)
    (bC : (∫ x : Fin N→Ω,Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : Fin N ↦ μ))≤MC) :
    Integrable (fun x : Fin N→Ω ↦ Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x))
      (Measure.pi (fun _ : Fin N ↦ μ)) ∧
    Integrable (fun x : Fin N→Ω ↦ Real.exp (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N ↦ μ)) ∧
    |sourceAffinePartition μ β I h F N-
      Real.exp (β*(∫ y,F y ∂μ)-β*I)*canonicalPartition μ β h N| ≤
      (|β| *Real.sqrt (variance F μ)*
        (Real.sqrt MS+Real.exp (β*(∫ y,F y ∂μ)-β*I)*Real.sqrt MC))/Real.sqrt (N:ℝ) := by
  let P := Measure.pi (fun _ : Fin N ↦ μ)
  let A := fun x : Fin N→Ω ↦ -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x
  let X := DGRHS.CLT.sourceParticleExponent h F I β N
  let c := β*(∫ y,F y ∂μ)-β*I
  let Y := fun x : Fin N→Ω ↦ A x+c
  have hu := DGRHS.CLT.memLp_normalizedOffDiagonalSum (ι := Fin N) h hh
  have ha : MemLp A 2 P := hu.const_mul _
  have hm := memLp_empiricalMean μ F hF N
  have hxMeas : AEMeasurable X P :=
    ((ha.aemeasurable.add (hm.aemeasurable.const_mul β)).sub aemeasurable_const)
  have hx : MemLp (fun x ↦ Real.exp (X x)) 2 P :=
    DGRHS.CLT.memLp_exp_of_integrable_double X hxMeas hS
  have hA2 : Integrable (fun x ↦ Real.exp (2*A x)) P := by
    convert hC using 1
    funext x
    dsimp [A]
    congr 1
    ring
  have hAe : MemLp (fun x ↦ Real.exp (A x)) 2 P :=
    DGRHS.CLT.memLp_exp_of_integrable_double A ha.aemeasurable hA2
  have heY : (fun x ↦ Real.exp (Y x)) = (fun x ↦ Real.exp c*Real.exp (A x)) := by
    funext x
    dsimp [Y]
    rw [Real.exp_add]
    ring
  have hy : MemLp (fun x ↦ Real.exp (Y x)) 2 P := by
    rw [heY]
    exact hAe.const_mul _
  have heDiff : (fun x ↦ X x-Y x) = (fun x ↦ β*(empiricalMean F N x-(∫ y,F y ∂μ))) := by
    funext x
    dsimp [X,Y,A,c,DGRHS.CLT.sourceParticleExponent,empiricalMean]
    ring
  have hd : MemLp (fun x ↦ X x-Y x) 2 P := by
    rw [heDiff]
    exact (hm.sub (memLp_const _)).const_mul _
  have hDiff : (∫ x,(X x-Y x)^2 ∂P) = β^2*((N:ℝ)⁻¹*variance F μ) := by
    simp_rw [show ∀ x,X x-Y x=β*(empiricalMean F N x-(∫ y,F y ∂μ)) from fun x ↦ congrFun heDiff x,mul_pow]
    rw [integral_const_mul,empiricalMean_centered_second_moment μ F hF N hN]
  have hY2 : (∫ x,Real.exp (2*Y x) ∂P) = Real.exp c^2*(∫ x,Real.exp (2*A x) ∂P) := by
    have he : (fun x ↦ Real.exp (2*Y x)) = (fun x ↦ Real.exp c^2*Real.exp (2*A x)) := by
      funext x
      dsimp [Y]
      rw [mul_add,Real.exp_add]
      rw [show Real.exp (2*c)=Real.exp c^2 by rw [← Real.exp_nat_mul];norm_num]
      ring
    rw [he,integral_const_mul]
  have hsC : Real.sqrt (∫ x,Real.exp (2*Y x) ∂P) ≤ Real.exp c*Real.sqrt MC := by
    rw [hY2,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.exp_pos _).le]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt _) (Real.exp_pos _).le
    convert bC using 1
    congr 1
    funext x
    dsimp [A]
    congr 1
    ring
  have hsS : Real.sqrt (∫ x,Real.exp (2*X x) ∂P) ≤ Real.sqrt MS := Real.sqrt_le_sqrt bS
  have hb := DGRHS.CLT.partition_exp_difference_le_second_moments X Y hd hx hy
  have hiY : (∫ x,Real.exp (Y x) ∂P) = Real.exp c*canonicalPartition μ β h N := by
    rw [heY,integral_const_mul]
    rfl
  rw [hiY,hDiff,sqrt_scaled_empirical_variance β (variance F μ) (variance_nonneg _ _) N] at hb
  refine ⟨hx.integrable (by norm_num),hAe.integrable (by norm_num),?_⟩
  change |(∫ x,Real.exp (X x) ∂P)-Real.exp c*canonicalPartition μ β h N|≤_
  calc
    _ ≤ (|β| *Real.sqrt (variance F μ)/Real.sqrt (N:ℝ))*
      (Real.sqrt MS+Real.exp c*Real.sqrt MC) :=
      hb.trans (mul_le_mul_of_nonneg_left (add_le_add hsS hsC) (by positivity))
    _ = _ := by dsimp [c];ring


/-- The literal source modulated-energy normalizer agrees for every positive N.
The empty-array convention is deliberately excluded from this identity. -/
lemma sourceEnergy_partition_eq_affine (β I : ℝ) (h : Ω×Ω→ℝ) (F : Ω→ℝ)
    (N : ℕ) (hN : 1≤N) :
    (∫ x : Fin N→Ω,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
      ∂Measure.pi (fun _ : Fin N ↦ μ)) = sourceAffinePartition μ β I h F N := by
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  exact DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent h F I β
    (lt_of_lt_of_le Nat.zero_lt_one hN) x

end DGRHS.Concentration
#print axioms DGRHS.Concentration.sourceAffinePartition_comparison
#check @DGRHS.Concentration.sourceAffinePartition_comparison

#print axioms DGRHS.Concentration.sourceEnergy_partition_eq_affine
#check @DGRHS.Concentration.sourceEnergy_partition_eq_affine
