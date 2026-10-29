/- Development: scalar canonical residual estimates lifted to the actual joint
linear/quadratic law while preserving the identical linear coordinate. -/
import DGRHS.CLT.SpectralApproximationBridge
import DGRHS.CLT.BoundedLipschitz
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace DGRHS.CLT
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma integrable_bounded_lipschitz_pair (F : ℝ × ℝ → ℝ) (L : ℝ≥0)
    (hF : LipschitzWith L F) (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    {X : S → ℝ × ℝ} (hX : AEMeasurable X μ) : Integrable (fun x => F (X x)) μ := by
  obtain ⟨C,hC⟩ := hb
  apply Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable
    (‖F (0,0)‖+C)
  exact ae_of_all _ fun x => by
    change ‖F (X x)‖ ≤ ‖F (0,0)‖+C
    have h := hC (X x) (0,0)
    have ht := norm_sub_norm_le (F (X x)) (F (0,0))
    rw [dist_eq_norm] at h
    linarith

lemma integral_bounded_lipschitz_joint_Lp_difference_le
    (F : ℝ × ℝ → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
    (A : S → ℝ) (hA : AEMeasurable A μ) (X Y : Lp ℝ 2 μ) :
    dist (∫ x, F (A x,X x) ∂μ) (∫ x, F (A x,Y x) ∂μ) ≤ L*‖X-Y‖ := by
  have hR : (X-Y : Lp ℝ 2 μ) =ᵐ[μ] (fun x => X x-Y x) := Lp.coeFn_sub X Y
  have hiR : Integrable (fun x => X x-Y x) μ :=
    ((Lp.memLp (X-Y)).integrable (by norm_num)).congr hR
  have hiX := integrable_bounded_lipschitz_pair F L hF hb (hA.prodMk (Lp.memLp X).aemeasurable)
  have hiY := integrable_bounded_lipschitz_pair F L hF hb (hA.prodMk (Lp.memLp Y).aemeasurable)
  rw [dist_eq_norm, ← integral_sub hiX hiY]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x, (L : ℝ)*‖X x-Y x‖ ∂μ := by
      apply integral_mono (hiX.sub hiY).norm (hiR.norm.const_mul _)
      intro x
      have hd : dist (A x,X x) (A x,Y x) = ‖X x-Y x‖ := by
        change max ‖A x-A x‖ ‖X x-Y x‖ = _
        simp only [sub_self,norm_zero,max_eq_right (norm_nonneg _)]
      have ht := hF.dist_le_mul (A x,X x) (A x,Y x)
      rw [hd,dist_eq_norm] at ht
      exact ht
    _ = (L : ℝ)*(∫ x, ‖X x-Y x‖ ∂μ) := integral_const_mul _ _
    _ ≤ (L : ℝ)*‖X-Y‖ := by
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      calc
        _ = ∫ x, ‖(X-Y : Lp ℝ 2 μ) x‖ ∂μ := integral_congr_ae (hR.symm.fun_comp norm)
        _ ≤ _ := DGRHS.Gaussian.integral_norm_Lp_two_le_norm (X-Y)

lemma tendstoInMeasure_fixed_pair {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    {ν : Measure Ω} {Z : ℕ → Ω → ℝ} {Q : Ω → ℝ}
    (A : Ω → E) (hZ : TendstoInMeasure ν Z atTop Q) :
    TendstoInMeasure ν (fun n ω => (A ω,Z n ω)) atTop (fun ω => (A ω,Q ω)) := by
  rw [tendstoInMeasure_iff_dist] at hZ ⊢
  intro ε hε
  simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hZ ε hε

variable {j ι : Type*} [Fintype j] [Fintype ι]

lemma finiteSpectral_particle_joint_test_error
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (a : j → ℝ) (e : j → Lp ℝ 2 μ)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0)
    (A : (ι → S) → ℝ) (hA : AEMeasurable A (Measure.pi (fun _ : ι => μ)))
    (F : ℝ × ℝ → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) :
    dist (∫ x : ι → S, F (A x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : ι => μ))
      (∫ x : ι → S, F (A x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (finiteSpectralKernel a e) x) ∂Measure.pi (fun _ : ι => μ)) ≤
      (L : ℝ) * Real.sqrt 2 *
        ‖hh.toLp h - ∑ i, a i • DGRHS.Kernel.separatedLp (e i) (e i)‖ := by
  let Hn := memLp_normalizedOffDiagonalSum (ι := ι) h hh
  let Kn := memLp_normalizedOffDiagonalSum (ι := ι) (finiteSpectralKernel a e)
    (memLp_finiteSpectralKernel a e)
  let R := fun p => h p - finiteSpectralKernel a e p
  have hR : MemLp R 2 (μ.prod μ) := hh.sub (memLp_finiteSpectralKernel a e)
  have hRs : ∀ᵐ p ∂μ.prod μ, R p.swap = R p := by
    filter_upwards [hs] with p hp
    dsimp only [R]
    rw [hp, symmetric_finiteSpectralKernel a e p]
  have hRc := canonical_finiteSpectralResidual h hh hc a e hm
  have hn := norm_particle_residual_le (ι := ι) R
    (hhm.sub (measurable_finiteSpectralKernel a e)) hR hRs hRc
  have hlp : (memLp_normalizedOffDiagonalSum (ι := ι) R hR).toLp
      (DGRHS.CanonicalVariance.normalizedOffDiagonalSum R) = Hn.toLp _ - Kn.toLp _ := by
    apply Lp.ext
    filter_upwards [(memLp_normalizedOffDiagonalSum (ι := ι) R hR).coeFn_toLp,
      Lp.coeFn_sub (Hn.toLp _) (Kn.toLp _), Hn.coeFn_toLp, Kn.coeFn_toLp]
        with x h1 h2 h3 h4
    rw [h1, h2, Pi.sub_apply, h3, h4]
    exact normalizedOffDiagonalSum_sub h (finiteSpectralKernel a e) x
  rw [hlp] at hn
  have he := integral_bounded_lipschitz_joint_Lp_difference_le F L hF hb A hA (Hn.toLp _) (Kn.toLp _)
  have hFH : (fun x => F (A x,(Hn.toLp _) x)) =ᵐ[Measure.pi (fun _ : ι => μ)]
      (fun x => F (A x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) :=
    by filter_upwards [Hn.coeFn_toLp] with x hx; rw [hx]
  have hFK : (fun x => F (A x,(Kn.toLp _) x)) =ᵐ[Measure.pi (fun _ : ι => μ)]
      (fun x => F (A x,DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x)) :=
    by filter_upwards [Kn.coeFn_toLp] with x hx; rw [hx]
  rw [integral_congr_ae hFH, integral_congr_ae hFK] at he
  have hrLp : hR.toLp R = hh.toLp h -
      (memLp_finiteSpectralKernel a e).toLp (finiteSpectralKernel a e) := hh.toLp_sub _
  rw [hrLp, toLp_finiteSpectralKernel] at hn
  exact he.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn L.coe_nonneg)

end DGRHS.CLT
#print axioms DGRHS.CLT.integral_bounded_lipschitz_joint_Lp_difference_le
#print axioms DGRHS.CLT.tendstoInMeasure_fixed_pair
#print axioms DGRHS.CLT.finiteSpectral_particle_joint_test_error
