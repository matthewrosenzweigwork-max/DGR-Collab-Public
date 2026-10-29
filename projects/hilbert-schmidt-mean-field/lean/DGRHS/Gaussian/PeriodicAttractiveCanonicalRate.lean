import DGRHS.Gaussian.PeriodicAttractiveLogPartition
import DGRHS.Gaussian.PeriodicAttractiveFixedCutoff
import DGRHS.Gaussian.PeriodicLogTheorem211
import DGRHS.Gaussian.PeriodicLogTruncationRemainder
import DGRHS.Attractive.SignedCanonicalPartitionLimit
import DGRHS.Attractive.SignedFeatureRateAssembly
import DGRHS.Attractive.LogShortInterpolation

/-!
Packet P11b, unit 2 (clause 2, step 4): the canonical (centered, mean-zero) quantitative determinant
rate for the attractive torus LOG gas.  For the repulsive centered kernel `q = -h̃^att` the positive
quadratic exponential `Z_N = E exp(β/2 W_N(q))` converges to `det₂(Id - β T_q)^{-1/2}` with the
two-parameter bound `|Z_N - z| ≤ 2 A η^r + B η^{-q'}/√N` for every cutoff `η ∈ (0,1]` (heat shift
`τ = η²`).  Torus form of `DGRHS.Attractive.exists_gaussianLogPhysical_canonical_cutoff_rate` (TeX
2840-2905): the finite-particle comparison `|Z_N - Z_{N,τ}|` is the endpoint exponential-difference /
Cauchy-Schwarz argument (`factorialCanonical_positive_comparison`) with the centered `L²` residual
`‖q - q_τ‖ ≤ A τ^{θ/2}` of the torus heat shift (`periodicLogResidual_of_remainder`), and the fixed-cutoff
rate is Proposition 6.1 for the Fourier feature of `q_τ` (`exists_periodicLogTrunc_cutoff_feature_rate`).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The repulsive centered kernel is minus the centered attractive kernel (torus form of
`logPhysicalCentered_eq_neg_attractive`). -/
lemma periodicCentered_eq_neg_attractive (μ : Measure (PeriodicTorus ι)) :
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) =
      -(fun z => DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2) := by
  funext z
  unfold hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential
    periodicAttractiveInteraction
  simp only [Pi.neg_apply, integral_neg]
  ring

/-- Factorial rows of the attractive centered kernel give factorial rows of the repulsive one. -/
theorem periodic_rows_of_attractive (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel μ periodicAttractiveInteraction x y| ^ p) ∂μ) ≤
        ENNReal.ofReal (C ^ p * (p.factorial : ℝ))) :
    RowFactorialMoments μ (periodicLogCentered μ) C := by
  have hm : Measurable (fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2) := by
    have hw : StronglyMeasurable (Function.uncurry (periodicAttractiveInteraction (ι := ι))) := by
      rw [periodicAttractiveInteraction_uncurry]
      exact measurable_periodicLogKernelPair.neg.stronglyMeasurable
    exact (stronglyMeasurable_hoeffdingCentered μ _ hw).measurable
  have h := periodicCentered_eq_neg_attractive μ
  change RowFactorialMoments μ (hoeffdingCentered μ
    (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) C
  rw [h]
  exact (rowFactorialMoments_of_lintegral μ _ hm C hC hb).neg

theorem exists_periodicAttractive_canonical_cutoff_rate
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (C R β : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hβ : 0 < β)
    (hrows : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
        periodicAttractiveInteraction x y| ^ p) ∂periodicCappedDensityMeasure ρ) ≤
        ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hrowsτ : ∀ τ : ℝ, 0 < τ → RowFactorialMoments (periodicCappedDensityMeasure ρ)
      (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) R)
    (hbase : β * (attractiveMomentConstant * C) < 1)
    (hsmallR : β * (attractiveMomentConstant * R) < 1) :
    let μ := periodicCappedDensityMeasure ρ
    let q := periodicLogCentered μ
    ∃ (hh : MemLp q 2 (μ.prod μ)) (κ : Type u) (eig : κ → ℝ)
      (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)), Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperator q hh (b i) = eig i • b i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => -β * eig i) ∧
      Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι, Real.exp
        (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
        ∂Measure.pi (fun _ : Fin N => μ)) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eig i)))⁻¹)) ∧
      ∃ A B q' r : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ q' ∧ 0 < r ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x : Fin N → PeriodicTorus ι, Real.exp
          (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eig i)))⁻¹| ≤
          2 * A * η ^ r + B * η ^ (-q') / Real.sqrt (N : ℝ) := by
  intro μ q
  have hr : RowFactorialMoments μ q C := periodic_rows_of_attractive μ C hC hrows
  have hm : Measurable q := (periodicLogCentered_data ρ M hρ).1
  have hWsym : ∀ a b : PeriodicTorus ι, periodicLogKernel (a - b) = periodicLogKernel (b - a) := by
    intro a b
    rw [← neg_sub b a, periodicLogKernel_even]
  have hs : ∀ x y, q (x, y) = q (y, x) := DGRHS.centeredKernel_symmetric μ
    (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) hWsym
  have hWi : Integrable (Function.uncurry (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
      (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hc : ∀ᵐ y ∂μ, ∫ x, q (x, y) ∂μ = 0 :=
    DGRHS.integral_centeredKernel_left μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) hWi
  have hhalf : (β / 2) * (attractiveMomentConstant * C) < 1 := by
    nlinarith [mul_nonneg attractiveMomentConstant_pos.le hC]
  let hh := joint_memLp μ q hm C hr 2 (by omega)
  obtain ⟨κ, eig, b, f, hf, hκ, hb, ht⟩ :=
    exists_factorialCanonical_positive_partition_limit q hm C hr hs hc
  have hlim := ht β hβ.le hbase
  have hg := rowMoment_actual_operator_weak_margin q hm C β hr hβ.le hbase
  have hpdet (i : κ) : 0 < 1 + (-β * eig i) := by
    have hp := DGRHS.Kernel.attractive_eigenvalue_factor_pos q hh eig b hb hβ.le hg i
    linarith
  have hdet := DGRHS.Kernel.regularizedDet_pos
    (DGRHS.Kernel.summable_scaled_eigenvalue_sq eig
      (DGRHS.Kernel.summable_integralOperator_eigenvalue_sq q hh eig b hb) (-β)) hpdet
  obtain ⟨K, q', hK, hq', hCut⟩ := exists_periodicLogTrunc_cutoff_feature_rate ρ β R hβ hR hrowsτ hsmallR
  obtain ⟨θ, hθ, hrem⟩ := periodicLogRemainder_integral_sq_le_weak (ι := ι)
  obtain ⟨A0, hA0, hRes⟩ := periodicLogResidual_of_remainder θ
    (by obtain ⟨C', hC', h'⟩ := hrem; exact ⟨C', hC', h'⟩) ρ M hM hρ
  let c1 := Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2))
  let c2 := Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * R)) ^ 2))
  let A := (β / 2 * Real.sqrt 2) * A0 * (c1 + c2)
  have hA : 0 ≤ A := by dsimp [A, c1, c2]; positivity
  refine ⟨hh, κ, eig, b, hκ, hb, hdet, hlim, A, K, 2 * q', θ, hA, hK, by positivity, hθ, ?_⟩
  intro η hη hη1 N hN
  have hi := (factorialCanonical_positive_uniform q hm C (β / 2) hr hs hc
    (by positivity) hhalf N).1
  refine ⟨hi, ?_⟩
  have hτ : 0 < η ^ 2 := by positivity
  have hτ1 : η ^ 2 ≤ 1 := by nlinarith
  obtain ⟨hhτ, κη, eigη, bη, hκη, hbη, hRate⟩ := hCut (η ^ 2) hτ hτ1
  let qτ := periodicLogTruncCentered μ (η ^ 2)
  let Y := fun n : ℕ => ∫ x : Fin n → PeriodicTorus ι, Real.exp
    (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum qτ x)
    ∂Measure.pi (fun _ : Fin n => μ)
  let y := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eigη i)))⁻¹
  have hη2 : (η ^ 2) ^ (-q') = η ^ (-(2 * q')) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    congr 1
    push_cast
    ring
  have hY : ∀ n, 1 ≤ n → |Y n - y| ≤ K * η ^ (-(2 * q')) / Real.sqrt (n : ℝ) := by
    intro n hn
    have := (hRate n hn).2
    rw [hη2] at this
    exact this
  have hητ : (η ^ 2) ^ (θ / 2) = η ^ θ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
    congr 1
    push_cast
    ring
  -- comparison with the truncation
  obtain ⟨hqτm, hqτs, hqτc⟩ := periodicLogTruncCentered_data μ (η ^ 2) hτ
  have hqτsym : ∀ x y, qτ (x, y) = qτ (y, x) := by
    intro x y
    have he : qτ = featureKernel (periodicLogTruncFeature μ (η ^ 2) hτ) :=
      periodicLogTruncCentered_eq_featureKernel μ (η ^ 2) hτ
    rw [he]
    exact (featureKernel_symmetric (periodicLogTruncFeature μ (η ^ 2) hτ) (x, y)).symm
  have hWτ : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogTruncKernel (η ^ 2) (p.1 - p.2)) (μ.prod μ) :=
    periodicPositiveFourierKernel_pair_integrable _ (periodicLogTruncCoeff_nonneg (ι := ι) (η ^ 2))
      (periodicLogTruncCoeff_summable (ι := ι) (η ^ 2) hτ) μ
  have hqτc' : ∀ᵐ y ∂μ, ∫ x, qτ (x, y) ∂μ = 0 :=
    DGRHS.integral_centeredKernel_left μ (fun a b : PeriodicTorus ι => periodicLogTruncKernel (η ^ 2) (a - b)) hWτ
  have hcomp : ∀ n, 1 ≤ n → |(∫ x : Fin n → PeriodicTorus ι, Real.exp
      (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
      ∂Measure.pi (fun _ : Fin n => μ)) - Y n| ≤ A * η ^ θ := by
    intro n hn
    have hb := factorialCanonical_positive_comparison q qτ hm hqτm C R β hr (hrowsτ (η ^ 2) hτ) hs
      hqτsym hc hqτc' hβ.le hbase hsmallR n
    have hres := hRes (η ^ 2) hτ hτ1
    refine hb.trans ?_
    have hRes' := hres (joint_memLp μ q hm C hr 2 (by omega)) 
      (joint_memLp μ qτ hqτm R (hrowsτ (η ^ 2) hτ) 2 (by omega))
    rw [hητ] at hRes'
    have h1 : 0 ≤ β / 2 * Real.sqrt 2 := by positivity
    calc _ ≤ (β / 2 * Real.sqrt 2) * (A0 * η ^ θ) * (c1 + c2) := by
          apply mul_le_mul_of_nonneg_right _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          exact mul_le_mul_of_nonneg_left hRes' h1
      _ = A * η ^ θ := by dsimp [A]; ring
  have hZ : Tendsto (fun n => ∫ x : Fin n → PeriodicTorus ι, Real.exp
      (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum q x)
      ∂Measure.pi (fun _ : Fin n => μ)) atTop
      (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eig i)))⁻¹)) := hlim
  exact partition_error_of_sqrt_cutoff_rate _ Y _ y A K (2 * q') θ η hZ hY hcomp N hN

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicCentered_eq_neg_attractive
#print axioms DGRHS.Periodic.periodic_rows_of_attractive
#print axioms DGRHS.Periodic.exists_periodicAttractive_canonical_cutoff_rate
