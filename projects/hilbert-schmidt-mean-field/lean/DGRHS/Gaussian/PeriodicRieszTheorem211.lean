import DGRHS.Gaussian.PeriodicRieszTheorem22ii
import DGRHS.CLT.SourceStaticCharacteristic
import DGRHS.CLT.SourceFiniteMGF
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.Kernel.MeanZeroResolventUnique

/-!
Packet P9d, unit 2: Proposition 2.11 (static linear-statistics CLT, TeX 805-831, proof 3617-3760)
for the periodic Riesz gas `0 < s < d/2` on the torus (Remark 2.1), mirroring
`DGRHS.CLT.exists_sourceRieszStatic` / `exists_sourceRieszSingularStatic`.  The generic CLT
machinery (`exists_sourceStaticCharacteristic`, `exists_sourceFiniteMGF`,
`meanZeroResolvent_unique`) is reused unchanged; the torus inputs are the kernel properties
(symmetry, canonicity, positivity of `T_μ`), the proper doubled moments of the modulated weights and
the literal singular Gibbs law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology InnerProductSpace
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma one_sub_exp_neg_sq_le_rpow (x θ : ℝ) (hx : 0 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
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

/-- A non-sharp power rate for the heat-shift remainder, valid for every `0 < s`, `2s < d`
(enough for positivity of `T_μ`). -/
theorem periodicRieszRemainder_integral_sq_le_weak (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∫ x, periodicRieszRemainder s τ hs2 x ^ 2 ∂periodicHaar ι ≤ C * τ ^ θ := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by rw [hd]; exact_mod_cast Fintype.card_pos (α := ι)
  set θ : ℝ := min 1 ((d - 2 * s) / 4) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (by linarith)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθ2 : θ ≤ (d - 2 * s) / 4 := min_le_right _ _
  have hr : 2 * (s - d) + 2 * θ < -d := by linarith
  have hsum : Summable (fun k : PeriodicFrequency ι =>
      ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 2 * θ)) := summable_periodicFrequency_rpow _ hr
  set A := periodicRieszFourierAmplitude ι s with hA
  refine ⟨θ, hθ0, A ^ 2 * ∑' k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 2 * θ),
    mul_nonneg (sq_nonneg _) (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _), ?_⟩
  intro τ hτ hτ1
  have hterm : ∀ k : PeriodicFrequency ι, ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2 ≤
      τ ^ θ * ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 2 * θ) := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp
      try positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      have hx : 0 ≤ ‖periodicFrequencyVector k‖ ^ 2 * τ := by positivity
      have hpn : 0 ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) := Real.rpow_nonneg hpos.le _
      have hb := one_sub_exp_neg_sq_le_rpow _ θ hx hθ0 hθ1
      have hmul : (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ θ =
          ‖periodicFrequencyVector k‖ ^ (2 * θ) * τ ^ θ := by
        rw [Real.mul_rpow (by positivity) hτ.le, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
        congr 2
      calc _ ≤ ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
            (‖periodicFrequencyVector k‖ ^ 2 * τ) ^ θ := mul_le_mul_of_nonneg_left hb hpn
        _ = _ := by
            rw [hmul, Real.rpow_add hpos]
            ring
  have hsumL : Summable (fun k : PeriodicFrequency ι => ‖periodicFrequencyVector k‖ ^ (2 * (s - d)) *
      (1 - Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ))) ^ 2) :=
    (hsum.mul_left (τ ^ θ)).of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)) hterm
  rw [periodicRieszRemainder_integral_sq_eq s τ hs2 hτ.le]
  calc _ ≤ A ^ 2 * ∑' k : PeriodicFrequency ι, τ ^ θ * ‖periodicFrequencyVector k‖ ^ (2 * (s - d) + 2 * θ) :=
        mul_le_mul_of_nonneg_left (hsumL.tsum_le_tsum hterm (hsum.mul_left _)) (sq_nonneg _)
    _ = _ := by rw [tsum_mul_left]; ring

/-- Unconditional positivity of the centered periodic Riesz operator `T_μ`. -/
theorem periodicRieszOperator_positive_all (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hh : MemLp (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ)) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))) :
    ∀ v : Lp ℝ 2 (periodicCappedDensityMeasure ρ), 0 ≤ inner ℝ v
      (DGRHS.Kernel.integralOperator (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ)) hh v) := by
  obtain ⟨θ, hθ, hrem⟩ := periodicRieszRemainder_integral_sq_le_weak s hs0 hs2
  exact periodicRieszOperator_positive s hs0 hs2 θ hθ hrem ρ M hM hρ hh


/-- Kernel properties used by the static CLT. -/
theorem periodicRieszKernel_properties (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := periodicRieszCentered s hs2 μ
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    (∀ᵐ p ∂μ.prod μ, h p.swap = h p) ∧ (∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0) ∧
    (∀ v : Lp ℝ 2 μ, 0 ≤ inner ℝ v (DGRHS.Kernel.integralOperator h hh v)) := by
  obtain ⟨_, hSym, hCan⟩ := periodicRieszCentered_data s hs2 ρ M hρ
  exact ⟨hSym, hCan, periodicRieszOperator_positive_all s hs0 hs2 ρ M hM hρ _⟩

/-- Proper modulated weights with uniform moments (torus form of `sourceRieszWeight_uniform`). -/
theorem periodicRieszWeight_uniform (s γ : ℝ) (hs0 : 0 < s) (hγ : 0 ≤ γ)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := periodicRieszCentered s hs2 μ
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ, ∀ N,
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (sourceParticleExponent h F I γ N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (sourceParticleExponent h F I γ N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  intro μ W h F I
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ (periodicRieszKernel_integrable s hs2)
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicRieszKernel_potential_abs_le s hs2 ρ M hM hρ x)
  obtain ⟨C, hC⟩ := periodicRieszKernel_uniform_exponential s γ hs0 hγ hs2 ρ M hM hρ
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (γ * iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-γ / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
    intro N hN
    have hb := (hC N hN).2
    rw [he N] at hb
    exact hb
  exact ⟨hF, max (Real.exp (γ * ((M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι) - I)) * C)
    (Real.exp (-γ * I)), sourceWeight_of_canonical_moments h F hF _ hK I γ hγ C hProper hBound⟩

theorem periodicRieszWeight_higher (s β p : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β) (hp : 0 ≤ p)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := periodicRieszCentered s hs2 μ
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    Integrable F μ ∧ ∃ C : ℝ, ∀ N,
      Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (p * sourceParticleExponent h F I β N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (p * sourceParticleExponent h F I β N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  simpa only [sourceParticleExponent_mul_parameter] using
    periodicRieszWeight_uniform s (p * β) hs0 (mul_nonneg hp hβ) hs2 ρ M hM hρ

/-- The literal singular Gibbs law `Q_{N,β}(μ)` on the torus, including `β = 0`, `N = 0` and the
collision-zero convention. -/
def periodicRieszSingularGibbs (s β : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : Measure (Fin N → PeriodicTorus ι) :=
  (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).withDensity
    (fun x => periodicRieszSingularWeight s β hs2 ρ N x / periodicRieszSingularPartition s β hs2 ρ N)

lemma periodicRieszSingularGibbs_eq (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    periodicRieszSingularGibbs s β hs2 ρ N = (Measure.pi (fun _ : Fin N => μ)).tilted
      (sourceParticleExponent (periodicRieszCentered s hs2 μ)
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) β N) := by
  dsimp only
  rw [← sourceEnergyTilt_eq _ _ _ β N]
  have hi := periodicRieszEnergyWeight_integrable s β hs0 hβ hs2 ρ M hM hρ N
  unfold periodicRieszSingularGibbs Measure.tilted
  apply withDensity_congr_ae
  filter_upwards [periodicRieszSingularWeight_ae s β hs2 ρ N] with x hx
  rw [hx, periodicRieszSingularPartition_eq_integral s β hs0 hβ hs2 ρ M hM hρ N]
  unfold periodicRieszSourcePartition
  exact (ENNReal.ofReal_div_of_pos (integral_exp_pos hi)).symm

lemma periodicRieszSingularGibbs_probability (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    IsProbabilityMeasure (periodicRieszSingularGibbs s β hs2 ρ N) := by
  rw [periodicRieszSingularGibbs_eq s β hs0 hβ hs2 ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  exact isProbabilityMeasure_tilted (periodicRieszEnergyWeight_integrable s β hs0 hβ hs2 ρ M hM hρ N)


/-- Proposition 2.11 on the torus (Riesz, `0 < s < d/2`), for the physical canonical tilt. -/
theorem exists_periodicRieszStatic
    (m : ℕ) (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R0 v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x)))),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => ((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x)))) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂((Measure.pi (fun _ : Fin N => μ)).tilted
          (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x))) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, hPos⟩ := periodicRieszKernel_properties s hs0 hs2 ρ M hM hρ
  obtain ⟨R0, hR1, hR2, hStat⟩ := exists_sourceStaticCharacteristic m h hh hSym hCan hPos β hβ
  obtain ⟨T0, hT1, hT2, hMGF⟩ := exists_sourceFiniteMGF h hh hSym hCan hPos β hβ
  have hRT : R0 = T0 := DGRHS.Kernel.meanZeroResolvent_unique h hh hSym hCan β R0 T0 hR1 hT2
  rw [← hRT] at hMGF
  obtain ⟨hF, C2, hC2⟩ := periodicRieszWeight_higher s β 2 hs0 hβ (by norm_num) hs2 ρ M hM hρ
  obtain ⟨_, C4, hC4⟩ := periodicRieszWeight_higher s β 4 hs0 hβ (by norm_num) hs2 ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, fun φ => ?_⟩
  obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF⟩ := hStat φ F hF I 2 C2 (by norm_num)
    (fun N => (hC2 N).1) (fun N => (hC2 N).2)
  refine ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, fun K θ hK => ?_⟩
  exact hMGF m φ K θ hK F hF I 2 C4 (by norm_num)
    (fun N => by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using (hC4 N).1)
    (fun N => by simpa only [show (2 : ℝ) * 2 = 4 by norm_num] using (hC4 N).2)

/-- Proposition 2.11 on the torus (Riesz, `0 < s < d/2`) under the literal singular Gibbs law
`Q_{N,β}(μ)` (collision weight `0` for `β > 0`, `1` for `β = 0`), with full `L²` tests, the
characteristic-function limit and the bounded-test MGF limit (TeX 805-831). -/
theorem exists_periodicRieszSingularStatic
    (m : ℕ) (s β : ℝ) (hs0 : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : DGRHS.Kernel.meanZeroL2 μ →L[ℝ] DGRHS.Kernel.meanZeroL2 μ),
      (∀ v, R0 v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      ∀ φ : Fin m → Lp ℝ 2 μ,
      ∃ (ν : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → (Fin m → ℝ))
        (hν : IsProbabilityMeasure ν)
        (hPN : ∀ N, IsProbabilityMeasure (periodicRieszSingularGibbs s β hs2 ρ N)),
      letI := hν
      letI := hPN
      TendstoInDistribution (sourceObservableFluctuation φ) atTop Z
        (fun N => periodicRieszSingularGibbs s β hs2 ρ N) ν ∧
      HasGaussianLaw Z ν ∧
      (∀ k, (∫ ω, Z ω k ∂ν) = 0) ∧
      (∀ k l, Integrable (fun ω => Z ω k * Z ω l) ν ∧
        (∫ ω, Z ω k * Z ω l ∂ν) = inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
          (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) ∧
      (∀ θ : Fin m → ℝ, Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
        Complex.exp ((∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k : ℝ) * Complex.I)
        ∂periodicRieszSingularGibbs s β hs2 ρ N) atTop
        (𝓝 (Complex.exp (-(∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
          inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
            (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l))) : ℝ) / 2)))) ∧
      ∀ (K θ : Fin m → ℝ), (∀ k, ∀ᵐ x ∂μ, |φ k x| ≤ K k) →
        (∀ N, Integrable (fun x : Fin N → PeriodicTorus ι =>
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k))
          (periodicRieszSingularGibbs s β hs2 ρ N)) ∧
        Tendsto (fun N => ∫ x : Fin N → PeriodicTorus ι,
          Real.exp (∑ k : Fin m, θ k * sourceObservableFluctuation φ N x k)
          ∂periodicRieszSingularGibbs s β hs2 ρ N) atTop
          (𝓝 (Real.exp ((∑ k : Fin m, ∑ l : Fin m, θ k * θ l *
            inner ℝ (DGRHS.Kernel.sourceCenteredL2 (φ k))
              (R0 (DGRHS.Kernel.sourceCenteredL2 (φ l)))) / 2))) := by
  intro μ W h F I hh
  obtain ⟨hSym, hCan, R0, hR1, hR2, hStat⟩ := exists_periodicRieszStatic m s β hs0 hβ hs2 ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, fun φ => ?_⟩
  obtain ⟨ν, Z, hν, hPN, hw, hG, hMean, hCov, hCF, hMGF⟩ := hStat φ
  have he (N : ℕ) : periodicRieszSingularGibbs s β hs2 ρ N =
      (Measure.pi (fun _ : Fin N => μ)).tilted
        (fun x => -β * (N : ℝ) * sourceCanonicalModulatedEnergy h F I N x) := by
    rw [periodicRieszSingularGibbs_eq s β hs0 hβ hs2 ρ M hM hρ N, ← sourceEnergyTilt_eq _ _ _ β N]
  have hPN' (N : ℕ) : IsProbabilityMeasure (periodicRieszSingularGibbs s β hs2 ρ N) :=
    periodicRieszSingularGibbs_probability s β hs0 hβ hs2 ρ M hM hρ N
  refine ⟨ν, Z, hν, hPN', ?_⟩
  simpa only [he] using ⟨hw, hG, hMean, hCov, hCF, hMGF⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.exists_periodicRieszStatic
#print axioms DGRHS.Periodic.exists_periodicRieszSingularStatic
