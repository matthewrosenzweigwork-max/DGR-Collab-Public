/- Proper canonical source exponents have a derived positive lower bound.
This yields an actual logarithm comparison without a normalizer premise. -/
import DGRHS.Concentration.SourceAffineComparison
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Concentration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

lemma sourceAffinePartition_lower (β I : ℝ) (h : Ω×Ω→ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0) (F : Ω→ℝ) (hF : MemLp F 2 μ)
    (N : ℕ) (hN : 1≤N)
    (hX : Integrable (fun x : Fin N→Ω ↦ Real.exp (DGRHS.CLT.sourceParticleExponent h F I β N x))
      (Measure.pi (fun _ : Fin N ↦ μ))) :
    Real.exp (β*(∫ y,F y ∂μ)-β*I) ≤ sourceAffinePartition μ β I h F N := by
  let P := Measure.pi (fun _ : Fin N ↦ μ)
  let X := DGRHS.CLT.sourceParticleExponent h F I β N
  let c := β*(∫ y,F y ∂μ)-β*I
  have hu := DGRHS.CLT.memLp_normalizedOffDiagonalSum (ι := Fin N) h hh
  have hm := memLp_empiricalMean μ F hF N
  have hXm : MemLp X 2 P := ((hu.const_mul (-β/2)).add (hm.const_mul β)).sub (memLp_const (β*I))
  have hiX := hXm.integrable (by norm_num)
  have hu0 : (∫ x : Fin N→Ω,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x ∂P)=0 := by
    unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum
    rw [integral_const_mul,DGRHS.CanonicalVariance.integral_offDiagonalSum_eq_zero μ h hh hc]
    simp
  have hi : (∫ x,X x ∂P)=c := by
    change (∫ x,(-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x+
      β*empiricalMean F N x)-β*I ∂P)=c
    rw [integral_sub (f := fun x ↦ -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x+β*empiricalMean F N x) (g := fun _ ↦ β*I) (((hu.const_mul (-β/2)).integrable (by norm_num)).add
      ((hm.const_mul β).integrable (by norm_num))) (integrable_const _),
      integral_add (f := fun x ↦ -β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) (g := fun x ↦ β*empiricalMean F N x) ((hu.const_mul (-β/2)).integrable (by norm_num))
        ((hm.const_mul β).integrable (by norm_num)),integral_const_mul,integral_const_mul,
      hu0,integral_empiricalMean μ F hF N hN,integral_const]
    simp [c]
  have he : (fun x ↦ Real.exp (X x-c)) = (fun x ↦ Real.exp (-c)*Real.exp (X x)) := by
    funext x
    rw [sub_eq_add_neg,Real.exp_add]
    ring
  have hProper : Integrable (fun x ↦ Real.exp (X x-c)) P := by
    rw [he]
    exact hX.const_mul _
  have hZero : (∫ x,X x-c ∂P)=0 := by rw [integral_sub hiX (integrable_const _),hi,integral_const];simp
  have hb := canonical_exponential_integral_one_le P (fun x ↦ X x-c)
    (hiX.sub (integrable_const c)) hProper hZero
  rw [he,integral_const_mul] at hb
  have ht := mul_le_mul_of_nonneg_left hb (Real.exp_pos c).le
  have hec : Real.exp c*Real.exp (-c)=1 := by rw [←Real.exp_add];simp
  simpa only [←mul_assoc,hec,one_mul,mul_one,c,X,P,sourceAffinePartition] using ht

lemma affine_log_difference_le (c Z z : ℝ) (hZ : Real.exp c≤Z) (hz : 1≤z) :
    |Real.log Z-(c+Real.log z)|≤Real.exp (-c)*|Z-Real.exp c*z| := by
  have hZp : 0<Z := (Real.exp_pos c).trans_le hZ
  have hScaled : 1≤Real.exp (-c)*Z := by
    have hb := mul_le_mul_of_nonneg_left hZ (Real.exp_pos (-c)).le
    have he : Real.exp (-c)*Real.exp c=1 := by rw [←Real.exp_add];simp
    simpa only [he] using hb
  have hb := abs_log_sub_le_abs_sub_of_one_le (Real.exp (-c)*Z) z hScaled hz
  rw [Real.log_mul (Real.exp_ne_zero _) hZp.ne',Real.log_exp] at hb
  have he : |Real.exp (-c)*Z-z|=Real.exp (-c)*|Z-Real.exp c*z| := by
    rw [←abs_of_pos (Real.exp_pos (-c)),←abs_mul]
    congr 1
    rw [mul_sub,←mul_assoc,←Real.exp_add]
    simp
  rw [he] at hb
  convert hb using 1
  congr 1
  ring

end DGRHS.Concentration
#print axioms DGRHS.Concentration.sourceAffinePartition_lower
#check @DGRHS.Concentration.sourceAffinePartition_lower
#print axioms DGRHS.Concentration.affine_log_difference_le
#check @DGRHS.Concentration.affine_log_difference_le
