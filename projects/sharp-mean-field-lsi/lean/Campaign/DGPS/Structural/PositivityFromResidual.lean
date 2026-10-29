import DGPS.Structural.GlobalResidualEstimate
import DGPS.Structural.FrozenEnergyIdentity
import DGPS.Structural.HarmonicRateComparison
import DGPS.Foundations.RateArithmetic
import DGPS.Foundations.TotalVariation

/-!
# Constructive species positivity from the residual bound (STR009)

Let `μ` be a free-energy minimizer, `K` its centered kernel with `|K| ≤ Kb`, and suppose the
residual bound `‖ν - μ‖_TV ≤ C ‖ν - Pν‖_TV` (STR007).  For every finite positive-weight absolute
family `F` with barycenter `ν` and `E_fr = ∑ θ_s H(ν_s | Pν)`:

* `G_θ ≤ (1 + Kb C²) E_fr`  (convexity, Pinsker, STR007, STR008);
* `D_θ ≥ 2 ℓ₀ E_fr`, `ℓ₀ = 4π² e^{-M}`  (STR002 and the frozen LSI of STR001).

Hence `r_ms ≥ ℓ₀ / (1 + Kb C²) > 0`; no bound on the species number or on the weights is used.

Route (R5 note): `‖K‖∞` is represented by an arbitrary constant `Kb ≥ 0` bounding `|K|`
(so the estimate holds for the sup-norm itself, the best such constant).  The residual constant
`C` is produced by STR007 under its hypotheses, and the estimate is also proved for any `C`
satisfying the residual bound.
-/

open MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Structural

variable {d : ℕ}

/-- Species entropies relative to a bounded reference minus the barycenter entropy: the Jensen
defect, independent of the reference. -/
theorem sum_relativeEntropy_reference_sub (F : SpeciesFamily d) (P : BoundedPositiveReference d) :
    ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure).toReal -
      (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) P.measure).toReal =
    ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal -
      (relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal := by
  have hI : ∑ s, F.weight s * ∫ x, (F.density s).density x * Real.log (P.density x) ∂haar d =
      ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar d := by
    have hint : ∀ s, Integrable (fun x => F.weight s *
        ((F.density s).density x * Real.log (P.density x))) (haar d) :=
      fun s => (integrable_density_mul_log_reference P (F.density s)).const_mul _
    have h1 : ∑ s, F.weight s * ∫ x, (F.density s).density x * Real.log (P.density x) ∂haar d =
        ∫ x, ∑ s, F.weight s * ((F.density s).density x * Real.log (P.density x)) ∂haar d := by
      rw [integral_finsetSum _ fun s _ => hint s]
      exact Finset.sum_congr rfl fun s _ => (integral_const_mul _ _).symm
    rw [h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = (barycenter F).density x * Real.log (P.density x)
    calc ∑ s, F.weight s * ((F.density s).density x * Real.log (P.density x))
        = (∑ s, F.weight s * (F.density s).density x) * Real.log (P.density x) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
      _ = _ := by rw [← F.barycenter_density_eq_sum x]
  have hB : ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        (haar d)).toReal -
      ∫ x, (barycenter F).density x * Real.log (P.density x) ∂haar d := by
    rw [← hI, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [(relativeEntropy_reference P (F.density s)).2]; ring
  rw [hB, (relativeEntropy_reference P (barycenter F)).2]
  ring

/-- Convexity of relative entropy in the first argument: `H(ν | P) ≤ ∑ θ_s H(ν_s | P)`. -/
theorem relativeEntropy_barycenter_le_sum (F : SpeciesFamily d) (P : BoundedPositiveReference d) :
    (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d)) P.measure).toReal ≤
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
        P.measure).toReal := by
  have h := sum_relativeEntropy_reference_sub F P
  have h2 := barycenter_entropy_le F
  linarith

/-- `|Q| ≤ Kb ‖ν - μ‖_TV²` for the centered correction. -/
theorem abs_centeredCorrection_le (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d))
    {Kb : ℝ} (hKb : 0 ≤ Kb) (hK : ∀ x y, |centeredKernel A μ x y| ≤ Kb) :
    |centeredCorrection A μ ν| ≤
      Kb * fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ^ 2 := by
  set T := fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) with hT
  have hT0 : 0 ≤ T := fullVariation_nonneg _ _
  have hu : ∀ x, |kernelPotential A μ ν x| ≤ Kb * T := fun x => by
    let g : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun y => centeredKernel A μ x y, continuous_kernelSection A μ x⟩
    have hg : ‖g‖ ≤ Kb := (BoundedContinuousFunction.norm_le hKb).2 fun y => by
      simpa [g] using hK x y
    have h := abs_integral_sub_le_fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) g
    exact h.trans (mul_le_mul_of_nonneg_right hg hT0)
  let U : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨kernelPotential A μ ν, kernelPotential_continuous A μ ν⟩
  have hU : ‖U‖ ≤ Kb * T := (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => by
    simpa [U, Real.norm_eq_abs] using hu x
  have h := abs_integral_sub_le_fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) U
  unfold centeredCorrection
  calc _ ≤ ‖U‖ * T := h
    _ ≤ Kb * T * T := mul_le_mul_of_nonneg_right hU hT0
    _ = Kb * T ^ 2 := by ring

/-- The pointwise estimates of STR009 for one finite family. -/
theorem speciesGap_dissipation_bounds_of_residual (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) {C Kb : ℝ} (hKb : 0 ≤ Kb)
    (hK : ∀ x y, |centeredKernel A μ x y| ≤ Kb)
    (hC : ∀ ν : ProbabilityMeasure (Torus d),
      fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤
        C * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure)
    (F : SpeciesFamily d) :
    (speciesGap A F : ℝ) ≤ (1 + Kb * C ^ 2) * (frozenEntropy A F).toReal ∧
    ENNReal.ofReal (2 * (4 * Real.pi ^ 2 * Real.exp (-totalOscillation A)) *
        (frozenEntropy A F).toReal) ≤ speciesDissipation A b F := by
  set ν : ProbabilityMeasure (Torus d) := densityMeasure (barycenter F) with hν
  set P := frozenGibbs A ν with hP
  obtain ⟨hEne, -, -, hlog0, hG⟩ := speciesGap_eq_frozenEntropy_centeredCorrection A hLip b hμ F
  have hfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      P.measure ≠ ⊤ := fun s => (relativeEntropy_reference P (F.density s)).1
  have hE : (frozenEntropy A F).toReal = ∑ s, F.weight s *
      (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) P.measure).toReal := by
    unfold frozenEntropy
    rw [ENNReal.toReal_sum fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (F.weight_nonneg s)]
  set E := (frozenEntropy A F).toReal with hEdef
  have hνH := (relativeEntropy_reference P (barycenter F)).1
  have hHle : (relativeEntropy (ν : Measure (Torus d)) P.measure).toReal ≤ E := by
    rw [hE]; exact relativeEntropy_barycenter_le_sum F P
  have hpin := pinsker_fullVariation_real (ν : Measure (Torus d)) P.measure hνH
  have hT0 : 0 ≤ fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) :=
    fullVariation_nonneg _ _
  have hsq : fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ^ 2 ≤
      C ^ 2 * (2 * E) := by
    calc _ ≤ (C * fullVariation (ν : Measure (Torus d)) P.measure) ^ 2 :=
          pow_le_pow_left₀ hT0 (hC ν) 2
      _ = C ^ 2 * fullVariation (ν : Measure (Torus d)) P.measure ^ 2 := by ring
      _ ≤ C ^ 2 * (2 * E) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg C)
          linarith
  have hQ := abs_centeredCorrection_le A μ ν hKb hK
  have hQ2 : -(centeredCorrection A μ ν) / 2 ≤ Kb * C ^ 2 * E := by
    have h1 : -(centeredCorrection A μ ν) ≤ |centeredCorrection A μ ν| := neg_le_abs _
    have h2 : Kb * fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ^ 2 ≤
        Kb * (C ^ 2 * (2 * E)) := mul_le_mul_of_nonneg_left hsq hKb
    linarith
  refine ⟨?_, ?_⟩
  · rw [hG]
    linarith
  · set ℓ0 : ℝ := 4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) with hℓ0
    obtain ⟨hℓpos, hℓle, hℓtop⟩ := frozenLSRateInf_ge_lowerBound hd A
    have hterm : ∀ s, ENNReal.ofReal (F.weight s * (2 * ℓ0 *
        (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) P.measure).toReal)) =
        ENNReal.ofReal (F.weight s) * (2 * ENNReal.ofReal ℓ0 *
          relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) P.measure) := by
      intro s
      rw [ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_toReal (hfin s)]
    have hrw : 2 * ℓ0 * E = ∑ s, F.weight s * (2 * ℓ0 *
        (relativeEntropy (densityMeasure (F.density s) : Measure (Torus d)) P.measure).toReal) := by
      rw [hE, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hrw, ENNReal.ofReal_sum_of_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (mul_nonneg (by positivity) ENNReal.toReal_nonneg),
      speciesDissipation_eq_frozenInformation A hLip b F]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [hterm s]
    refine mul_le_mul' le_rfl (le_trans ?_
      (two_mul_frozenLSRateInf_mul_relativeEntropy_le A (densityMeasure (barycenter F))
        (F.density s)))
    exact mul_le_mul' (mul_le_mul' le_rfl hℓle) le_rfl

/-- The rate bound for a given residual constant `C` and kernel bound `Kb`. -/
theorem speciesRate_ge_of_residual_bound (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) {C Kb : ℝ} (hKb : 0 ≤ Kb)
    (hK : ∀ x y, |centeredKernel A μ x y| ≤ Kb)
    (hC : ∀ ν : ProbabilityMeasure (Torus d),
      fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤
        C * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure) :
    ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) / (1 + Kb * C ^ 2)) ≤
      speciesRate A b := by
  set ℓ0 : ℝ := 4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) with hℓ0
  have hℓpos : 0 < ℓ0 := by positivity
  have hden : 0 < 1 + Kb * C ^ 2 := by positivity
  refine le_iInf fun F => ?_
  obtain ⟨h1, h2⟩ := speciesGap_dissipation_bounds_of_residual hd A hLip b hμ hKb hK hC F.1
  have hG : 0 < speciesGap A F.1 := F.2
  unfold speciesQuotient
  have hne0 : (2 : ℝ≥0∞) * (speciesGap A F.1 : ℝ≥0∞) ≠ 0 := by
    simp [hG.ne']
  have hnetop : (2 : ℝ≥0∞) * (speciesGap A F.1 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnetop)]
  refine le_trans ?_ h2
  have hGnn : (0 : ℝ) ≤ (speciesGap A F.1 : ℝ) := NNReal.coe_nonneg _
  have hE0 : 0 ≤ (frozenEntropy A F.1).toReal := ENNReal.toReal_nonneg
  rw [show (2 : ℝ≥0∞) * (speciesGap A F.1 : ℝ≥0∞) =
      ENNReal.ofReal (2 * (speciesGap A F.1 : ℝ)) by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal],
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h3 : ℓ0 / (1 + Kb * C ^ 2) * (speciesGap A F.1 : ℝ) ≤ ℓ0 * (frozenEntropy A F.1).toReal := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left h1 hℓpos.le]
  nlinarith [h3]

/-- **STR009.** Constructive species positivity from the residual bound.  Let `μ` be a
free-energy minimizer, the unique probability fixed point of the frozen Gibbs map, with coercive
density Hessian.  Then there is `C_err ≥ 0` with the global residual bound
`‖ν - μ‖_TV ≤ C_err ‖ν - Pν‖_TV`, and for every bound `Kb ≥ ‖K‖∞` of the centered kernel:
every finite positive-weight absolute family `F` satisfies `G_θ ≤ (1 + Kb C_err²) E_fr` and
`D_θ ≥ 2 ℓ₀ E_fr` with `ℓ₀ = 4π² e^{-M}`, and `r_ms ≥ ℓ₀ / (1 + Kb C_err²) > 0`.  No bound on
the number of species or on their weights is used. -/
theorem speciesRate_ge_frozenResidual_bound (hd : 0 < d) (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (huniq : ∀ ν : ProbabilityMeasure (Torus d),
      (ν : Measure (Torus d)) = (frozenGibbs A ν).measure → ν = μ)
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ ν : ProbabilityMeasure (Torus d),
        fullVariation (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≤
          C * fullVariation (ν : Measure (Torus d)) (frozenGibbs A ν).measure) ∧
      ∀ Kb : ℝ, 0 ≤ Kb → (∀ x y, |centeredKernel A μ x y| ≤ Kb) →
        (∀ F : SpeciesFamily d,
          (speciesGap A F : ℝ) ≤ (1 + Kb * C ^ 2) * (frozenEntropy A F).toReal ∧
          ENNReal.ofReal (2 * (4 * Real.pi ^ 2 * Real.exp (-totalOscillation A)) *
            (frozenEntropy A F).toReal) ≤ speciesDissipation A b F) ∧
        0 < 4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) / (1 + Kb * C ^ 2) ∧
        ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-totalOscillation A) / (1 + Kb * C ^ 2)) ≤
          speciesRate A b := by
  obtain ⟨C, hC0, hC⟩ := frozenResidual_global_errorBound A μ
    (minimizer_eq_frozenGibbs A hμ).symm huniq hH
  refine ⟨C, hC0, hC, fun Kb hKb hK => ⟨fun F => ?_, ?_, ?_⟩⟩
  · exact speciesGap_dissipation_bounds_of_residual hd A hLip b hμ hKb hK hC F
  · positivity
  · exact speciesRate_ge_of_residual_bound hd A hLip b hμ hKb hK hC

end DGPS.Structural
