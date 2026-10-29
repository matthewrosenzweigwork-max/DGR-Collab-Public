/- UNCHECKED outside frozen proof. Concrete residual estimates for the actual
finite spectral kernels; this does not assume uniform particle approximation. -/
import DGRHS.CLT.FiniteParticleChaosCLT
import DGRHS.CLT.NonzeroSpectralTruncations
import DGRHS.CLT.FiniteCovarianceCLT
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology InnerProductSpace NNReal
namespace DGRHS.CLT
variable {S j ι : Type*} [MeasurableSpace S] [Fintype j] [Fintype ι]
    {μ : Measure S} [IsProbabilityMeasure μ]

lemma toLp_finiteSpectralKernel (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    (memLp_finiteSpectralKernel a e).toLp (finiteSpectralKernel a e) =
      ∑ l, a l • DGRHS.Kernel.separatedLp (e l) (e l) := by
  classical
  apply Lp.ext
  have ht : ∀ l : j, (DGRHS.Kernel.separatedLp (e l) (e l) :
      Lp ℝ 2 (μ.prod μ)) =ᵐ[μ.prod μ]
      (fun p => e l p.1 * e l p.2) :=
    fun l => DGRHS.Kernel.separatedLp_coeFn (e l) (e l)
  filter_upwards [(memLp_finiteSpectralKernel a e).coeFn_toLp,
    coeFn_finiteLpCombination a (fun l => DGRHS.Kernel.separatedLp (e l) (e l)),
    ae_all_iff.mpr ht] with p h1 h2 h3
  rw [h1, h2]
  exact Finset.sum_congr rfl (fun l _ => by rw [h3 l]; ring)

lemma integrable_finiteSpectralKernel_row (a : j → ℝ) (e : j → Lp ℝ 2 μ) (x : S) :
    Integrable (fun y => finiteSpectralKernel a e (x,y)) μ := by
  classical
  unfold finiteSpectralKernel
  apply integrable_finsetSum
  intro i _
  exact ((Lp.memLp (e i)).integrable (by norm_num)).const_mul (a i * e i x)

lemma canonical_finiteSpectralResidual (h : S × S → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (a : j → ℝ) (e : j → Lp ℝ 2 μ)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0) :
    ∀ᵐ x ∂μ, (∫ y, h (x,y) - finiteSpectralKernel a e (x,y) ∂μ) = 0 := by
  filter_upwards [hc, (hh.integrable (by norm_num)).prod_right_ae] with x hx hi
  rw [integral_sub hi (integrable_finiteSpectralKernel_row a e x), hx,
    canonical_finiteSpectralKernel a e hm, sub_self]

lemma finiteSpectral_particle_test_error
    (h : S × S → ℝ) (hhm : Measurable h) (hh : MemLp h 2 (μ.prod μ))
    (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
    (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
    (a : j → ℝ) (e : j → Lp ℝ 2 μ)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0)
    (F : ℝ → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hb : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C) :
    dist (∫ x : ι → S, F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
      ∂Measure.pi (fun _ : ι => μ))
      (∫ x : ι → S, F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum
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
  have he := integral_bounded_lipschitz_Lp_difference_le F L hF hb (Hn.toLp _) (Kn.toLp _)
  have hFH : (fun x => F ((Hn.toLp _) x)) =ᵐ[Measure.pi (fun _ : ι => μ)]
      (fun x => F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) :=
    Hn.coeFn_toLp.fun_comp F
  have hFK : (fun x => F ((Kn.toLp _) x)) =ᵐ[Measure.pi (fun _ : ι => μ)]
      (fun x => F (DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x)) :=
    Kn.coeFn_toLp.fun_comp F
  rw [integral_congr_ae hFH, integral_congr_ae hFK] at he
  have hrLp : hR.toLp R = hh.toLp h -
      (memLp_finiteSpectralKernel a e).toLp (finiteSpectralKernel a e) := hh.toLp_sub _
  rw [hrLp, toLp_finiteSpectralKernel] at hn
  exact he.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn L.coe_nonneg)

end DGRHS.CLT
#print axioms DGRHS.CLT.toLp_finiteSpectralKernel
#print axioms DGRHS.CLT.canonical_finiteSpectralResidual
#print axioms DGRHS.CLT.finiteSpectral_particle_test_error
