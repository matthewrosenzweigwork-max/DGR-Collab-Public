import DGRHS.Gaussian.PeriodicLogTruncatedLaplace
import DGRHS.Gaussian.PeriodicRieszTruncationRemainder

/-!
Packet P9g, unit 2 (part 3): the `L²` remainder of the heat-shift truncation of the torus LOG
kernel, the periodic form of `eq:fetaL2Rate` / `eq:centeredFetaL2Rate` (TeX Step 2 of Proposition
5.5) at `s = 0`.  Spectrally `‖g - g_τ‖² = Σ_{k≠0} ĝ(k)² (1 - e^{-τ‖k‖²})²` with
`ĝ(k) ∝ ‖k‖^{-d}`.

RANGE (resolution of the packet caution): because the printed LOG rate is `(e+N)^{-c_log}` with an
UNSPECIFIED positive exponent, any positive power rate of the remainder suffices.  The heat shift
gives `‖g - g_τ‖² ≲ τ^θ` for every `0 < θ ≤ min 1 (d/4)` and every `d` (the `ℤ^d` sum
`Σ ‖k‖^{2θ-2d}` converges since `2θ - 2d < -d`); the saturation at `τ²` for `d > 4` (first lattice
shell) only limits the *largest* admissible `θ`, which is irrelevant for the LOG statement.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology lp
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration DGRHS.Periodic.RealifiedStrictCutoff
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLogTruncKernel_integrable (τ : ℝ) (hτ : 0 < τ) :
    Integrable (periodicLogTruncKernel (ι := ι) τ) (periodicHaar ι) :=
  ((periodicPositiveFourierKernel_continuous _ (periodicLogTruncCoeff_nonneg τ)
    (periodicLogTruncCoeff_summable τ hτ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

lemma periodicLogTruncKernel_memLp (τ : ℝ) (hτ : 0 < τ) :
    MemLp (periodicLogTruncKernel (ι := ι) τ) 2 (periodicHaar ι) :=
  (periodicPositiveFourierKernel_continuous _ (periodicLogTruncCoeff_nonneg τ)
    (periodicLogTruncCoeff_summable τ hτ)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma periodicLogMellinGreen_memLp_pos (τ : ℝ) (hτ : 0 < τ) :
    MemLp (periodicLogMellinGreen (ι := ι) τ) 2 (periodicHaar ι) :=
  (memLp_congr_ae (periodicLogMellinGreen_ae_truncKernel τ hτ)).2 (periodicLogTruncKernel_memLp τ hτ)

/-- Real kernel of the remainder `g - g_τ`. -/
def periodicLogRemainder (τ : ℝ) : PeriodicTorus ι → ℝ := fun x =>
  periodicLogKernel x - periodicLogMellinGreen τ x

lemma periodicLogRemainder_memLp (τ : ℝ) (hτ : 0 < τ) :
    MemLp (periodicLogRemainder (ι := ι) τ) 2 (periodicHaar ι) :=
  periodicLogKernel_memLp.sub (periodicLogMellinGreen_memLp_pos τ hτ)

lemma periodicLogRemainder_stronglyMeasurable (τ : ℝ) :
    StronglyMeasurable (periodicLogRemainder (ι := ι) τ) :=
  periodicLogKernel_measurable.stronglyMeasurable.sub
    (periodicLogMellinGreen_measurable (ι := ι) τ).stronglyMeasurable

/-- Parseval identity for the LOG remainder. -/
theorem periodicLogRemainder_integral_sq_eq (τ : ℝ) (hτ : 0 < τ) :
    ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι =
      ∑' k : PeriodicFrequency ι,
        ((1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) * periodicLogCoeffReal k) ^ 2 := by
  have hg := periodicLogRemainder_memLp (ι := ι) τ hτ
  have hMC : MemLp (fun x : PeriodicTorus ι => (periodicLogMellinGreen τ x : ℂ)) 2 (periodicHaar ι) :=
    (periodicLogMellinGreen_memLp_pos τ hτ).ofReal
  set M : Lp ℂ 2 (periodicHaar ι) := hMC.toLp _ with hM
  set F : Lp ℂ 2 (periodicHaar ι) := periodicLogL2 - M with hF
  set g : Lp ℝ 2 (periodicHaar ι) := hg.toLp (periodicLogRemainder τ) with hgdef
  have hc : realToComplexL2 g = F := by
    apply Lp.ext
    filter_upwards [realToComplexL2_coe_ae g, hg.coeFn_toLp, periodicLogKernel_coe_ae,
      hMC.coeFn_toLp, Lp.coeFn_sub (periodicLogL2 (ι := ι)) M] with x h1 h2 h3 h4 h5
    rw [h1]
    have : g x = periodicLogRemainder τ x := h2
    rw [this, hF, h5]
    simp only [Pi.sub_apply, periodicLogRemainder, Complex.ofReal_sub, h3]
    rw [← h4]
  calc ∫ x, periodicLogRemainder τ x ^ 2 ∂periodicHaar ι
      = ‖g‖ ^ 2 := (DGRHS.Kernel.norm_toLp_sq hg).symm
    _ = ‖F‖ ^ 2 := by rw [← hc, realToComplexL2_norm]
    _ = ∑' k : PeriodicFrequency ι, ‖UnitAddTorus.mFourierCoeff F k‖ ^ 2 :=
        norm_sq_eq_tsum_fourierCoeff _
    _ = _ := by
        apply tsum_congr
        intro k
        have hco : UnitAddTorus.mFourierCoeff F k =
            UnitAddTorus.mFourierCoeff (periodicLogL2 (ι := ι)) k -
              UnitAddTorus.mFourierCoeff M k := by
          rw [← periodicFourierBasis_repr, ← periodicFourierBasis_repr,
            ← periodicFourierBasis_repr, hF, map_sub]
          rfl
        have hMk : UnitAddTorus.mFourierCoeff M k = ((periodicLogTruncCoeff τ k : ℝ) : ℂ) := by
          rw [← periodicLogMellinGreen_fourier τ hτ.le k]
          exact periodic_mFourierCoeff_congr hMC.coeFn_toLp k
        rw [hco, periodicLogL2_fourierCoeff, hMk, periodicLogFourierCoeff_eq_ofReal]
        have : ((periodicLogCoeffReal k : ℝ) : ℂ) - ((periodicLogTruncCoeff τ k : ℝ) : ℂ) =
            (((1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) * periodicLogCoeffReal k : ℝ) : ℂ) := by
          unfold periodicLogTruncCoeff
          push_cast
          ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma periodicLog_one_sub_exp_neg_sq_le_rpow (x θ : ℝ) (hx : 0 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 - Real.exp (-x)) ^ 2 ≤ x ^ θ := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0
    simp [Real.zero_rpow hθ0.ne']
  · by_cases hx1 : x ≤ 1
    · calc (1 - Real.exp (-x)) ^ 2 ≤ x ^ 2 := one_sub_exp_neg_sq_le_sq x hx
        _ = x ^ (2 : ℝ) := by norm_num
        _ ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_ge hpos hx1 (by linarith)
    · calc (1 - Real.exp (-x)) ^ 2 ≤ 1 := one_sub_exp_neg_sq_le_one x hx
        _ ≤ x ^ θ := Real.one_le_rpow (by linarith) hθ0.le

lemma periodicLogCoeffReal_sq (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    periodicLogCoeffReal k ^ 2 =
      (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι)) ^ 2 *
        ‖periodicFrequencyVector k‖ ^ (-(2 * (Fintype.card ι : ℝ))) := by
  have hpos : 0 < ‖periodicFrequencyVector k‖ := periodicFrequency_norm_pos hk
  unfold periodicLogCoeffReal
  rw [ite_eq_right hk, mul_pow, ← pow_mul, Real.rpow_neg hpos.le,
    show (2 * (Fintype.card ι : ℝ)) = ((2 * Fintype.card ι : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, inv_pow, mul_comm (Fintype.card ι) 2]

/-- Power rate of the LOG heat-shift remainder: `‖g - g_τ‖²_{L²(Haar)} ≲ τ^θ` for
`θ = min 1 (d/4) > 0` and every dimension `d ≥ 1`. -/
theorem periodicLogRemainder_integral_sq_le_weak :
    ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos (α := ι)
  set θ : ℝ := min 1 (d / 4) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (by linarith)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ ≤ d / 4 := min_le_right _ _
  have hr : -(2 * d) + 2 * θ < -d := by linarith
  have hsum : Summable (fun k : PeriodicFrequency ι =>
      ‖periodicFrequencyVector k‖ ^ (-(2 * d) + 2 * θ)) := summable_periodicFrequency_rpow _ hr
  set A := periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) with hA
  refine ⟨θ, hθ0, A ^ 2 * ∑' k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (-(2 * d) + 2 * θ),
    mul_nonneg (sq_nonneg _) (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro τ hτ hτ1
  have hterm : ∀ k : PeriodicFrequency ι,
      ((1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) * periodicLogCoeffReal k) ^ 2 ≤
        A ^ 2 * (τ ^ θ * ‖periodicFrequencyVector k‖ ^ (-(2 * d) + 2 * θ)) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [periodicLogCoeffReal_zero]
      positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      have hx : 0 ≤ ‖periodicFrequencyVector k‖ ^ 2 * τ := by positivity
      have hb := periodicLog_one_sub_exp_neg_sq_le_rpow _ θ hx hθ0 hθ1
      have hmul : (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ θ =
          ‖periodicFrequencyVector k‖ ^ (2 * θ) * τ ^ θ := by
        rw [Real.mul_rpow (by positivity) hτ.le, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
        congr 2
      have hc2 := periodicLogCoeffReal_sq k hk
      rw [mul_pow, hc2]
      have hc2nn : 0 ≤ A ^ 2 * ‖periodicFrequencyVector k‖ ^ (-(2 * d)) := by positivity
      calc (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2 *
            (A ^ 2 * ‖periodicFrequencyVector k‖ ^ (-(2 * d)))
          ≤ (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ θ *
            (A ^ 2 * ‖periodicFrequencyVector k‖ ^ (-(2 * d))) :=
            mul_le_mul_of_nonneg_right hb hc2nn
        _ = _ := by
            rw [hmul, Real.rpow_add hpos]
            ring
  have hsumL : Summable (fun k : PeriodicFrequency ι =>
      ((1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) * periodicLogCoeffReal k) ^ 2) :=
    ((hsum.mul_left (τ ^ θ)).mul_left (A ^ 2)).of_nonneg_of_le (fun k => sq_nonneg _) hterm
  rw [periodicLogRemainder_integral_sq_eq τ hτ]
  calc _ ≤ ∑' k : PeriodicFrequency ι,
        A ^ 2 * (τ ^ θ * ‖periodicFrequencyVector k‖ ^ (-(2 * d) + 2 * θ)) :=
        hsumL.tsum_le_tsum hterm ((hsum.mul_left (τ ^ θ)).mul_left (A ^ 2))
    _ = _ := by rw [tsum_mul_left, tsum_mul_left]; ring

/-- Centered `L²(μ⊗μ)` residual `‖h̃ - h̃_τ‖` from the Haar remainder bound (torus form of
`eq:centeredFetaL2Rate`, first inequality, LOG kernel). -/
theorem periodicLogResidual_of_remainder (θ : ℝ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ (hh : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
        (hq : MemLp (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) 2
          ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))),
      ‖(hh.sub hq).toLp (fun p => hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) p -
          periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ p)‖ ≤ A * τ ^ (θ / 2) := by
  obtain ⟨C, hC0, hC⟩ := hrem
  refine ⟨4 * M * Real.sqrt C, by positivity, ?_⟩
  intro τ hτ hτ1 hh hq
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hg := periodicLogRemainder_memLp (ι := ι) τ hτ
  have hgm := periodicLogRemainder_stronglyMeasurable (ι := ι) τ
  have hWint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogKernel (p.1 - p.2)) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hVint : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogTruncKernel τ (p.1 - p.2)) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicLogTruncKernel_integrable τ hτ)
  have hsub := ae_hoeffdingCentered_sub μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2))
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogTruncKernel τ (p.1 - p.2))
    hWint hVint
  have hgreen := periodicDensity_pair_ae_of_haar ρ
    (fun x => periodicLogMellinGreen τ x = periodicLogTruncKernel τ x)
    (periodicLogMellinGreen_ae_truncKernel τ hτ)
  have hWV : ((fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2)) -
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogTruncKernel τ (p.1 - p.2)))
      =ᵐ[μ.prod μ] (fun p => periodicLogRemainder τ (p.1 - p.2)) := by
    filter_upwards [hgreen] with p hp
    simp only [Pi.sub_apply, periodicLogRemainder]
    rw [hp]
  have hcong := ae_hoeffdingCentered_congr μ _ _ hWV
  have hae : (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) p -
      periodicLogTruncCentered μ τ p) =ᵐ[μ.prod μ]
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicLogRemainder τ (x - y)) p.1 p.2) := by
    filter_upwards [hsub, hcong] with p h1 h2
    have h3 : hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicLogRemainder τ (q.1 - q.2)) p =
        DGRHS.centeredKernel μ (fun x y => periodicLogRemainder τ (x - y)) p.1 p.2 := rfl
    rw [← h3, ← h2, h1]
    rfl
  have hcM := periodicCenteredPair_memLp_of_density_cap ρ M hρ _ hgm hg
  have hnorm := periodicCenteredPair_norm_le_of_density_cap ρ M hM hρ _ hgm hg
  have key : (hh.sub hq).toLp (fun p => hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) p -
      periodicLogTruncCentered μ τ p) = hcM.toLp (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        DGRHS.centeredKernel μ (fun x y => periodicLogRemainder τ (x - y)) p.1 p.2) :=
    MemLp.toLp_congr _ _ hae
  rw [key]
  refine hnorm.trans ?_
  have hn2 : ‖hg.toLp (periodicLogRemainder τ)‖ ^ 2 ≤ C * τ ^ θ := by
    rw [DGRHS.Kernel.norm_toLp_sq hg]
    exact hC τ hτ hτ1
  have hb := norm_le_sqrt_mul_rpow _ C τ θ (norm_nonneg _) hC0 hτ hn2
  calc 4 * M * ‖hg.toLp (periodicLogRemainder τ)‖
      ≤ 4 * M * (Real.sqrt C * τ ^ (θ / 2)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogTruncKernel_integrable
#print axioms DGRHS.Periodic.periodicLogTruncKernel_memLp
#print axioms DGRHS.Periodic.periodicLogMellinGreen_memLp_pos
#print axioms DGRHS.Periodic.periodicLogRemainder
#print axioms DGRHS.Periodic.periodicLogRemainder_memLp
#print axioms DGRHS.Periodic.periodicLogRemainder_stronglyMeasurable
#print axioms DGRHS.Periodic.periodicLogRemainder_integral_sq_eq
#print axioms DGRHS.Periodic.periodicLog_one_sub_exp_neg_sq_le_rpow
#print axioms DGRHS.Periodic.periodicLogCoeffReal_sq
#print axioms DGRHS.Periodic.periodicLogRemainder_integral_sq_le_weak
#print axioms DGRHS.Periodic.periodicLogResidual_of_remainder
