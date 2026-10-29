/- Actual finite-particle endpoint comparison. The two proper exponential
second moments remain physical obligations, to be discharged independently.
Canonical residual cancellation supplies the cutoff error uniformly in N. -/
import DGRHS.CLT.PartitionComparison
import DGRHS.CLT.SpectralResidual
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DGRHS.CLT
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    {μ : Measure S} [IsProbabilityMeasure μ]

lemma canonical_kernel_sub (h k : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) (hk : MemLp k 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (kc : ∀ᵐ x ∂μ, (∫ y, k (x,y) ∂μ) = 0) :
    ∀ᵐ x ∂μ, (∫ y, h (x,y)-k (x,y) ∂μ) = 0 := by
  filter_upwards [hc,kc,(hh.integrable (by norm_num)).prod_right_ae,
    (hk.integrable (by norm_num)).prod_right_ae] with x hx kx hi ki
  rw [integral_sub hi ki,hx,kx,sub_self]

lemma memLp_exp_of_integrable_double {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} (X : Ω → ℝ) (hX : AEMeasurable X ν)
    (hi : Integrable (fun x => Real.exp (2*X x)) ν) :
    MemLp (fun x => Real.exp (X x)) 2 ν := by
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_exp.measurable.comp_aemeasurable hX).aestronglyMeasurable).mpr
  change Integrable (fun x => Real.exp (X x)^2) ν
  simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hi

theorem canonical_partition_difference_le (h k : S × S → ℝ)
    (hhm : Measurable h) (hkm : Measurable k)
    (hh : MemLp h 2 (μ.prod μ)) (hk : MemLp k 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (ks : ∀ᵐ p ∂μ.prod μ, k p.swap = k p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (kc : ∀ᵐ x ∂μ, (∫ y, k (x,y) ∂μ) = 0)
    (β : ℝ)
    (hiH : Integrable (fun x : ι → S => Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
        (Measure.pi (fun _ : ι => μ)))
    (hiK : Integrable (fun x : ι → S => Real.exp
      (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x))
        (Measure.pi (fun _ : ι => μ))) :
    |(∫ x : ι → S, Real.exp (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : ι => μ))-
      (∫ x : ι → S, Real.exp (-β/2*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x)
        ∂Measure.pi (fun _ : ι => μ))| ≤
      (|β|/2*Real.sqrt 2)*‖(hh.sub hk).toLp (fun p => h p-k p)‖ *
        (Real.sqrt (∫ x : ι → S, Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
            ∂Measure.pi (fun _ : ι => μ))+
         Real.sqrt (∫ x : ι → S, Real.exp (-β*DGRHS.CanonicalVariance.normalizedOffDiagonalSum k x)
            ∂Measure.pi (fun _ : ι => μ))) := by
  let U := fun g : S × S → ℝ => DGRHS.CanonicalVariance.normalizedOffDiagonalSum (ι := ι) g
  let X := fun x : ι → S => -β/2*U h x
  let Y := fun x : ι → S => -β/2*U k x
  have H := memLp_normalizedOffDiagonalSum (ι := ι) h hh
  have K := memLp_normalizedOffDiagonalSum (ι := ι) k hk
  have R := memLp_normalizedOffDiagonalSum (ι := ι) (fun p => h p-k p) (hh.sub hk)
  have hdEq : (fun x => X x-Y x) = fun x => (-β/2)*U (fun p => h p-k p) x := by
    funext x
    dsimp [X,Y,U]
    rw [normalizedOffDiagonalSum_sub]
    ring
  have hd : MemLp (fun x => X x-Y x) 2 (Measure.pi (fun _ : ι => μ)) := by
    rw [hdEq]
    exact R.const_mul (-β/2)
  have hxDouble : Integrable (fun x => Real.exp (2*X x)) (Measure.pi (fun _ : ι => μ)) := by
    convert hiH using 1 <;> funext x <;> congr 1 <;> dsimp [X,U] <;> ring
  have hyDouble : Integrable (fun x => Real.exp (2*Y x)) (Measure.pi (fun _ : ι => μ)) := by
    convert hiK using 1 <;> funext x <;> congr 1 <;> dsimp [Y,U] <;> ring
  have hx := memLp_exp_of_integrable_double X (H.aemeasurable.const_mul _) hxDouble
  have hy := memLp_exp_of_integrable_double Y (K.aemeasurable.const_mul _) hyDouble
  have hrs : ∀ᵐ p ∂μ.prod μ, (h p.swap-k p.swap) = h p-k p := by
    filter_upwards [hs,ks] with p hp kp
    rw [hp,kp]
  have hrn := norm_particle_residual_le (ι := ι) (fun p => h p-k p)
    (hhm.sub hkm) (hh.sub hk) hrs (canonical_kernel_sub h k hh hk hc kc)
  have hmSq : (∫ x : ι → S, (X x-Y x)^2 ∂Measure.pi (fun _ : ι => μ)) =
      (-β/2)^2*‖R.toLp (U (fun p => h p-k p))‖^2 := by
    simp_rw [congrFun hdEq,mul_pow]
    rw [integral_const_mul,← DGRHS.Kernel.norm_toLp_sq R]
  have hsqrt : Real.sqrt (∫ x : ι → S, (X x-Y x)^2 ∂Measure.pi (fun _ : ι => μ)) ≤
      (|β|/2*Real.sqrt 2)*‖(hh.sub hk).toLp (fun p => h p-k p)‖ := by
    rw [hmSq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      Real.sqrt_sq (norm_nonneg _),abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
    calc
      _ ≤ (|β|/2)*(Real.sqrt 2*‖(hh.sub hk).toLp (fun p => h p-k p)‖) :=
        mul_le_mul_of_nonneg_left hrn (by positivity)
      _ = _ := by ring
  have bound := (partition_exp_difference_le_second_moments X Y hd hx hy).trans
    (mul_le_mul_of_nonneg_right hsqrt (by positivity))
  have heX : ∀ x, 2*X x = -β*U h x := by intro x; dsimp [X]; ring
  have heY : ∀ x, 2*Y x = -β*U k x := by intro x; dsimp [Y]; ring
  simpa only [heX,heY] using bound
end DGRHS.CLT
#print axioms DGRHS.CLT.canonical_kernel_sub
#print axioms DGRHS.CLT.memLp_exp_of_integrable_double
#print axioms DGRHS.CLT.canonical_partition_difference_le
#check @DGRHS.CLT.canonical_partition_difference_le
