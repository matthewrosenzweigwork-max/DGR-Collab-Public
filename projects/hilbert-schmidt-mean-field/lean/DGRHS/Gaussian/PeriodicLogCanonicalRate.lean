import DGRHS.Gaussian.PeriodicLogTheorem211
import DGRHS.Gaussian.PeriodicLogTruncationRemainder
import DGRHS.Concentration.SourceRateAssembly
import DGRHS.Concentration.SourceCutoffRate
import DGRHS.Gaussian.SourceRepulsiveLogRate

/-!
Packet P9g, unit 2 (part 5): the canonical (centered, mean-zero) torus LOG partition rate, the
periodic form of `DGRHS.SourceRepulsiveLogRate.exists_canonical_partition_rate`
(TeX Steps 1-4 of Proposition 5.5 at `s = 0`, 1941-2087): uniform moments for the exact and the
heat-shifted LOG kernels, the fixed-scale Laplace estimate (constant `L exp(L(1+log(1/τ)))`), the
finite-`N` comparison, and the polynomial cutoff `η(N) = N^{-p}` with `τ = η²`, which yields the
printed LOG rate `(e+N)^{-c}`, `0 < c ≤ 1/2`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLog_shift_rpow (n c : ℝ) (hn : 1 ≤ n) (hc : 0 ≤ c) :
    n ^ (-c) ≤ (Real.exp 1 + 1) ^ c * (Real.exp 1 + n) ^ (-c) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  refine inverse_rpow_comparison (Real.exp 1 + n) n (Real.exp 1 + 1) c
    (by positivity) hn0 (by positivity) hc ?_
  nlinarith [mul_nonneg (Real.exp_pos (1 : ℝ)).le (sub_nonneg.mpr hn)]

/-- Uniform exponential moments of the heat-shifted LOG truncations (continuous representative). -/
theorem periodicLogTrunc_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicLogMellinGreen_uniform_exponential β hβ ρ M hM hρ
  refine ⟨C, fun τ hτ n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC τ hτ.le n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicLogTruncKernel τ (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ (periodicLogMellinGreen_ae_truncKernel τ hτ)
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- The canonical periodic LOG partition `K_N^{can}` converges to `det₂^{-1/2}` with the
polynomial rate `(e+N)^{-c}`, `0 < c ≤ 1/2` (the printed LOG exponent `c_log`), for the heat-shift
truncation whose centered residual is `‖h̃ - h̃_τ‖ ≲ τ^{θ/2}`. -/
theorem exists_periodic_log_canonical_rate (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ) (hθ : 0 < θ)
    (hrem : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicLogRemainder (ι := ι) τ x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicLogCentered μ
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      Tendsto (canonicalPartition μ β h) atTop
        (𝓝 ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)) ∧
      Tendsto (fun N => Real.log (canonicalPartition μ β h N)) atTop
        (𝓝 (Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |canonicalPartition μ β h N -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) ∧
        |Real.log (canonicalPartition μ β h N) -
          Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹)| ≤
          C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
  intro μ h
  have hh : MemLp h 2 (μ.prod μ) := periodicLogCentered_memLp ρ M hρ
  obtain ⟨hhm, hSym, hCan⟩ := periodicLogCentered_data ρ M hρ
  have hPos := periodicLogOperator_positive θ hθ hrem ρ M hM hρ hh
  -- moments of the exact centered kernel
  obtain ⟨MF, hF⟩ := periodicLogKernel_uniform_exponential (2 * β) (by positivity) ρ M hM hρ
  have hEF (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp ((2 * β) * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
    congr 1; ring
  have hMF : 1 ≤ MF := by
    have hb := (hF 1 le_rfl).2
    simpa [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum] using hb
  have hDouble : ∀ N, Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
      (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) (Measure.pi (fun _ : Fin N => μ)) := by
    intro N
    by_cases hN : N = 0
    · subst N
      simpa [DGRHS.CanonicalVariance.normalizedOffDiagonalSum] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Fin 0 → PeriodicTorus ι => (1 : ℝ))
          (Measure.pi (fun _ : Fin 0 => μ)))
    · have hb := (hF N (by omega)).1
      rw [hEF N] at hb
      exact hb
  have bDouble : ∀ N, (∫ x : Fin N → PeriodicTorus ι, Real.exp
      (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ MF := by
    intro N
    by_cases hN : N = 0
    · subst N
      simpa [DGRHS.CanonicalVariance.normalizedOffDiagonalSum] using hMF
    · have hb := (hF N (by omega)).2
      rw [hEF N] at hb
      exact hb
  -- moments of the truncations
  obtain ⟨MK, hK⟩ := periodicLogTrunc_uniform_exponential (2 * β) (by positivity) ρ M hM hρ
  have hEK (τ : ℝ) (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp ((2 * β) *
      iidNegativeStatistic N (periodicLogTruncCentered μ τ) x)) =
      (fun x => Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (periodicLogTruncCentered μ τ) x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
    congr 1; ring
  have kDouble : ∀ τ : ℝ, 0 < τ → ∀ N : ℕ, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (periodicLogTruncCentered μ τ) x)) (Measure.pi (fun _ : Fin N => μ)) := by
    intro τ hτ N hN
    have hb := (hK τ hτ N hN).1
    rw [hEK τ N] at hb
    exact hb
  have bkDouble : ∀ τ : ℝ, 0 < τ → ∀ N : ℕ, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-β * DGRHS.CanonicalVariance.normalizedOffDiagonalSum
        (periodicLogTruncCentered μ τ) x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ MK := by
    intro τ hτ N hN
    have hb := (hK τ hτ N hN).2
    rw [hEK τ N] at hb
    exact hb
  obtain ⟨A, hA0, hRes⟩ := periodicLogResidual_of_remainder θ hrem ρ M hM hρ
  obtain ⟨κ, eig, e, hκ, he, hD, _, hT, hLog, hAll⟩ :=
    exists_canonicalMeanZero_log_partition_limit μ β hβ h hh hSym hCan hPos MF hDouble bDouble
  set z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ with hz
  obtain ⟨L0, hL0, hLap⟩ := periodicLogTruncatedLaplace (ι := ι) β hβ
  -- Euclidean-shaped Laplace constant in the scale `η = √τ`
  set L : ℝ := 2 * L0 with hLdef
  have hL : 0 < L := by positivity
  set B := (|β| / 2 * Real.sqrt 2) * (Real.sqrt MF + Real.sqrt MK) * A with hBdef
  have hB : 0 ≤ B := by
    dsimp [B]; positivity
  obtain ⟨ha, _, _⟩ := sourceLogRatePower_bounds L hL
  set c : ℝ := min (sourceLogRatePower L * θ) (1 / 2 : ℝ) with hcdef
  have hc0 : 0 < c := lt_min (mul_pos ha hθ) (by norm_num)
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  set C : ℝ := (2 * B + L * Real.exp L) * (Real.exp 1 + 1) ^ c with hCdef
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hRateAll : ∀ N : ℕ, 1 ≤ N → |canonicalPartition μ β h N - z| ≤
      C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
    intro N hN
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    set η := sourceLogRateCutoff L (N : ℝ) with hηdef
    obtain ⟨hη, hη1, hlogη, _, _⟩ := sourceLogRateCutoff_identities L (N : ℝ) θ hL hn
    have hτ : 0 < η ^ 2 := by positivity
    have hτ1 : η ^ 2 ≤ 1 := by nlinarith
    obtain ⟨hq, σ, cc, b, hσ, hb, hDc, hY, hRate⟩ := hLap (η ^ 2) hτ hτ1 μ
    obtain ⟨hqm, hqs, hqc⟩ := periodicLogTruncCentered_data μ (η ^ 2) hτ
    have hητ : (η ^ 2) ^ (θ / 2) = η ^ θ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη.le]
      congr 1; push_cast; ring
    have hresid := hRes (η ^ 2) hτ hτ1 hh hq
    rw [hητ] at hresid
    have hComp := canonicalPartition_comparison μ β h (periodicLogTruncCentered μ (η ^ 2)) hhm hqm hh hq
      hSym hqs hCan hqc (A * η ^ θ) MF MK hresid
      (fun n _ => hDouble n) (fun n hn => kDouble (η ^ 2) hτ n hn)
      (fun n _ => bDouble n) (fun n hn => bkDouble (η ^ 2) hτ n hn)
    have hComp' : ∀ n, 1 ≤ n → |canonicalPartition μ β h n -
        canonicalPartition μ β (periodicLogTruncCentered μ (η ^ 2)) n| ≤ B * η ^ θ := by
      intro n hn
      convert hComp n hn using 1 <;> dsimp [B] <;> ring
    have hError := partition_error_assembly (canonicalPartition μ β h)
      (canonicalPartition μ β (periodicLogTruncCentered μ (η ^ 2)))
      z ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * cc i)))⁻¹) (B * η ^ θ) hT hY hComp' N hN
    have hOpt := (sourceLogRateCutoff_bound B L θ (N : ℝ) hB hL hθ hn).2
    have hR := (hRate N hN).2
    have hl0 : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
    have hlogτ : Real.log (1 / η ^ 2) = 2 * Real.log (1 / η) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_pow]; push_cast; ring
    have hLap2 : L0 * Real.exp (L0 * (1 + Real.log (1 / η ^ 2))) / (N : ℝ) ≤
        L * Real.exp (L * (1 + Real.log (1 / η))) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
      rw [hlogτ]
      apply mul_le_mul (by dsimp [L]; linarith) _ (Real.exp_pos _).le hL.le
      apply Real.exp_le_exp.mpr
      dsimp [L]
      nlinarith [mul_nonneg hL0.le hl0]
    have hfin : |canonicalPartition μ β h N - z| ≤
        2 * B * η ^ θ + L * Real.exp (L * (1 + Real.log (1 / η))) / (N : ℝ) := by
      refine hError.trans ?_
      calc 2 * (B * η ^ θ) + |canonicalPartition μ β (periodicLogTruncCentered μ (η ^ 2)) N -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * cc i)))⁻¹|
          ≤ 2 * (B * η ^ θ) + L0 * Real.exp (L0 * (1 + Real.log (1 / η ^ 2))) / (N : ℝ) :=
            add_le_add le_rfl hR
        _ ≤ 2 * (B * η ^ θ) + L * Real.exp (L * (1 + Real.log (1 / η))) / (N : ℝ) :=
            add_le_add le_rfl hLap2
        _ = _ := by ring
    have hShift : (N : ℝ) ^ (-c) ≤ (Real.exp 1 + 1) ^ c * (Real.exp 1 + (N : ℝ)) ^ (-c) :=
      periodicLog_shift_rpow (N : ℝ) c hn hc0.le
    calc |canonicalPartition μ β h N - z|
        ≤ (2 * B + L * Real.exp L) * (N : ℝ) ^ (-c) := hfin.trans hOpt
      _ ≤ C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
        simpa only [C, mul_assoc] using
          mul_le_mul_of_nonneg_left hShift (show 0 ≤ 2 * B + L * Real.exp L by positivity)
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hT, hLog, c, C, hc0, hc1, hC, ?_⟩
  intro N hN
  exact ⟨(hAll N).1, hRateAll N hN, ((hAll N).2.2).trans (hRateAll N hN)⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLog_shift_rpow
#print axioms DGRHS.Periodic.periodicLogTrunc_uniform_exponential
#print axioms DGRHS.Periodic.exists_periodic_log_canonical_rate
