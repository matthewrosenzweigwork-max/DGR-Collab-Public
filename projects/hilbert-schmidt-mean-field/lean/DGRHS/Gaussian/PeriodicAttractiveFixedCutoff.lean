import DGRHS.Gaussian.PeriodicLogTruncRows
import DGRHS.Gaussian.PeriodicLogOperatorPositive
import DGRHS.Attractive.SignedFeatureSourceRate
import DGRHS.Attractive.SignedFeaturePhysicalDiagonal
import DGRHS.Attractive.FactorialCanonicalComparison
import DGRHS.Attractive.SourceOperatorBound

/-!
Packet P11b, unit 2 (clause 2, step 3): the fixed-cutoff quantitative determinant rate for the
positive quadratic exponential `E exp(β/2 W_N(q_τ))` of the Hoeffding-centered heat-shifted periodic LOG
kernel `q_τ` on the torus (Proposition 6.1, TeX 2614-2632, applied to the centered Fourier feature
`periodicLogTruncFeature`), torus form of `DGRHS.Attractive.exists_gaussianLogPhysical_cutoff_feature_rate`.

Inputs: uniform factorial rows `R` of `q_τ` (`periodicLogTruncCentered_rows`) with
`β C_* R < 1`.  The feature diagonal is deterministic and logarithmic,
`‖k_τ(x)‖² ≤ 4 g_τ(0) ≤ 4 C_D (1 + log (1/τ))`, so the diagonal exponential moment is a power
`τ^{-q}` with `q = 8 β C_D`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

theorem exists_periodicLogTrunc_cutoff_feature_rate
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (β R : ℝ) (hβ : 0 < β) (hR : 0 ≤ R)
    (hrows : ∀ τ : ℝ, 0 < τ → RowFactorialMoments (periodicCappedDensityMeasure ρ)
      (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) R)
    (hsmall : β * (attractiveMomentConstant * R) < 1) :
    ∃ K q : ℝ, 0 ≤ K ∧ 0 ≤ q ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      let μ := periodicCappedDensityMeasure ρ
      let qτ := periodicLogTruncCentered μ τ
      ∃ (hh : MemLp qτ 2 (μ.prod μ)) (κ : Type u) (eig : κ → ℝ)
        (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)), Countable κ ∧
        (∀ i, DGRHS.Kernel.integralOperator qτ hh (b i) = eig i • b i) ∧
        ∀ N : ℕ, 1 ≤ N →
          Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
            (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum qτ x))
            (Measure.pi (fun _ : Fin N => μ)) ∧
          |(∫ x : Fin N → PeriodicTorus ι, Real.exp
            (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum qτ x)
            ∂Measure.pi (fun _ : Fin N => μ)) -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eig i)))⁻¹| ≤
            K * τ ^ (-q) / Real.sqrt (N : ℝ) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  obtain ⟨CD, hCD0, hCD⟩ := periodicLogTruncCoeff_tsum_le (ι := ι)
  let U := 2 / (1 - (β * (attractiveMomentConstant * R)) ^ 2)
  let L0 := Real.exp ((2 * β) ^ 2 * (2 * R ^ 2) / (2 * (1 - 2 * β * (2 * R))))
  let cb := positiveFeatureQuadraticFourthConstant β (2 * β)
  let cr := positiveFeatureCubicFourthConstant β (2 * β)
  let ce := positiveFeatureRemainderFourthConstant β (2 * β)
  let G := Real.sqrt (32 * β / (2 * β)) + 8 + 3 * cr + 3 * ce + 756 * (cb + cr + ce)
  have hcb : 0 ≤ cb := by
    dsimp [cb, positiveFeatureQuadraticFourthConstant, gaussianDiagonalMomentConstant]; positivity
  have hcr : 0 ≤ cr := by
    dsimp [cr, positiveFeatureCubicFourthConstant, gaussianDiagonalMomentConstant]; positivity
  have hce : 0 ≤ ce := by
    dsimp [ce, positiveFeatureRemainderFourthConstant, gaussianDiagonalMomentConstant]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hmarg : 2 * β * (2 * R) < 1 := by
    have hle := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right attractiveMomentConstant_four_le hR) hβ.le
    nlinarith
  have hU : 0 ≤ U := by
    have : 0 < 1 - (β * (attractiveMomentConstant * R)) ^ 2 := by
      have h0 : 0 ≤ β * (attractiveMomentConstant * R) :=
        mul_nonneg hβ.le (mul_nonneg attractiveMomentConstant_pos.le hR)
      nlinarith
    dsimp [U]; positivity
  refine ⟨G * Real.exp (8 * β * CD) * (Real.sqrt U + Real.sqrt L0), 8 * β * CD,
    by positivity, by positivity, fun τ hτ hτ1 => ?_⟩
  intro μ' qτ
  borelize ↥(PeriodicHeatFeatureSpace ι)
  have ha := periodicLogTruncCoeff_nonneg (ι := ι) τ
  have hsum := periodicLogTruncCoeff_summable (ι := ι) τ hτ
  have hr := periodicLogTruncCoeff_sqrt_summable (ι := ι) τ hτ
  have hrow := hrows τ hτ
  obtain ⟨hqm, hqs, hqc⟩ := periodicLogTruncCentered_data μ τ hτ
  have hsym : ∀ x y, qτ (x, y) = qτ (y, x) := by
    intro x y
    have he : qτ = featureKernel (periodicLogTruncFeature μ τ hτ) :=
      periodicLogTruncCentered_eq_featureKernel μ τ hτ
    rw [he]
    exact (featureKernel_symmetric (periodicLogTruncFeature μ τ hτ) (x, y)).symm
  have hWi : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogTruncKernel τ (p.1 - p.2)) (μ.prod μ) :=
    periodicPositiveFourierKernel_pair_integrable _ ha hsum μ
  have hc : ∀ᵐ y ∂μ, ∫ x, qτ (x, y) ∂μ = 0 :=
    DGRHS.integral_centeredKernel_left μ (fun a b => periodicLogTruncKernel τ (a - b)) hWi
  let hh := joint_memLp μ qτ hqm R hrow 2 (by omega)
  have hu := factorialCanonical_positive_uniform qτ hqm R β hrow hsym hc hβ.le hsmall
  have hp : ∀ N : ℕ, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
      (β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum qτ x)) (Measure.pi (fun _ : Fin N => μ)) :=
    fun N _ => (hu N).1
  have hU' : ∀ N : ℕ, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι, Real.exp
      (β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum qτ x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ U :=
    fun N _ => (hu N).2
  have hg : |2 * β| * ‖DGRHS.Kernel.integralOperator qτ hh‖ < 1 := by
    simpa only [abs_of_nonneg (by positivity : 0 ≤ 2 * β)] using
      rowMoment_actual_operator_doubled_margin qτ hqm R β hrow hβ.le hsmall
  -- the feature
  let k := periodicLogTruncFeature μ τ hτ
  have hk : StronglyMeasurable k := periodicLogTruncFeature_stronglyMeasurable μ τ hτ
  have hmean : (∫ x, k x ∂μ) = 0 := periodicLogTruncFeature_integral μ τ hτ
  have hGram : qτ =ᵐ[μ.prod μ] featureKernel k :=
    Filter.Eventually.of_forall (fun p => by
      have he := periodicLogTruncCentered_eq_featureKernel μ τ hτ
      exact congrFun he p)
  -- diagonal exponential moment
  have hnorm : ∀ x, ‖k x‖ ^ 2 ≤ 4 * ∑' j, periodicLogTruncCoeff (ι := ι) τ j := fun x =>
    periodicCenteredPositiveFourierFeature_norm_sq_le _ ha hsum hr μ x
  have hdiag := hCD τ hτ hτ1
  have hl : Real.exp (2 * β * (4 * (CD * (1 + Real.log (1 / τ))))) =
      Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)) := by
    rw [Real.rpow_def_of_pos hτ, ← Real.exp_add]
    congr 1
    rw [one_div, Real.log_inv]
    ring
  have hexp : ∀ x, Real.exp (2 * β * ‖k x‖ ^ 2) ≤ Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)) := by
    intro x
    rw [← hl]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (hnorm x) (by positivity : 0 ≤ 2 * β)
    have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiag (by norm_num : (0:ℝ) ≤ 4))
      (by positivity : 0 ≤ 2 * β)
    linarith
  have hMeas : AEStronglyMeasurable (fun x => Real.exp (2 * β * ‖k x‖ ^ 2)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable
      ((hk.norm.pow 2).aestronglyMeasurable.const_mul (2 * β))
  have hMi : Integrable (fun x => Real.exp (2 * β * ‖k x‖ ^ 2)) μ :=
    (integrable_const (Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)))).mono' hMeas
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexp x)
  have hMb : (∫ x, Real.exp (2 * β * ‖k x‖ ^ 2) ∂μ) ≤
      Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)) := by
    calc _ ≤ ∫ _ : PeriodicTorus ι, Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)) ∂μ :=
          integral_mono_ae hMi (integrable_const _) (Filter.Eventually.of_forall hexp)
      _ = _ := by simp
  obtain ⟨κ, eig, b, hκ, hb, hRate⟩ := exists_sourceKernel_positive_feature_rate
    β hβ.le qτ hh k hk (2 * β) (by positivity) hMi hmean hGram hp U hU' hg
  have hL := feature_HS_margin_exponential_uniform β
    (∫ z, qτ z ^ 2 ∂μ.prod μ) ‖DGRHS.Kernel.integralOperator qτ hh‖ (2 * R ^ 2) (2 * R)
    hβ.le (integral_nonneg (fun _ => sq_nonneg _))
    (rowMoment_actual_operator_norm_le qτ hqm R hrow)
    (rowMoment_joint_second_bound qτ hqm R hrow) hmarg
  simp only [abs_of_nonneg (by positivity : 0 ≤ 2 * β)] at hRate
  refine ⟨hh, κ, eig, b, hκ, hb, fun N hN => ?_⟩
  obtain ⟨hi, heRate⟩ := hRate N hN
  refine ⟨hi, heRate.trans ?_⟩
  have hprod := mul_le_mul hMb
    (add_le_add le_rfl (Real.sqrt_le_sqrt hL))
    (by positivity : 0 ≤ Real.sqrt U + Real.sqrt (Real.exp ((2 * β) ^ 2 *
      (∫ z, qτ z ^ 2 ∂μ.prod μ) / (2 * (1 - 2 * β * ‖DGRHS.Kernel.integralOperator qτ hh‖)))))
    (by positivity : 0 ≤ Real.exp (8 * β * CD) * τ ^ (-(8 * β * CD)))
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hG)
    (Real.sqrt_nonneg (N : ℝ))
  convert hscale using 1 <;> dsimp [G, cb, cr, ce, L0] <;> ring

end DGRHS.Periodic

#print axioms DGRHS.Periodic.exists_periodicLogTrunc_cutoff_feature_rate
