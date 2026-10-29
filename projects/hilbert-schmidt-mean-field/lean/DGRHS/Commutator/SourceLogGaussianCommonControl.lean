import DGRHS.Commutator.SourceLogGaussianLongDerivative
import DGRHS.Commutator.SourceLogGaussianShortCentering
import DGRHS.Commutator.SourceLogTransportGibbsMoments

/-! One dimensional coefficient for actual Gaussian LOG truncation and the
physical local numerator. Enlarging the coefficient retains the exact local
threshold by the checked two-sign interpolation, including the zero-temperature
endpoint separately. The large-temperature Gibbs proof is reused below.
This is not a uniformly positive threshold over a family of backgrounds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy
variable {ι : Type*} [Fintype ι]

lemma sourceLogTransportNumerator_enlarge_constant
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (n : ℕ) (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (γ Cold Csr K : ℝ) (hγ : 0 ≤ γ) (hCold : 0 < Cold)
    (hCsr : Cold ≤ Csr) (hK : 0 < K)
    (hold : ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (sourceLogTransportNumerator μ γ n v
        (σ * (γ / (4 * Cold * K ^ n))) N)
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x, sourceLogTransportNumerator μ γ n v
        (σ * (γ / (4 * Cold * K ^ n))) N x
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp 1) :
    ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (sourceLogTransportNumerator μ γ n v
        (σ * (γ / (4 * Csr * K ^ n))) N)
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x, sourceLogTransportNumerator μ γ n v
        (σ * (γ / (4 * Csr * K ^ n))) N x
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp 1 := by
  intro σ hσ N hN
  by_cases hz : γ = 0
  · have he : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
    constructor
    · unfold sourceLogTransportNumerator
      simpa [hz] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Fin N → EuclideanSpace ℝ ι => (1 : ℝ))
          (Measure.pi (fun _ : Fin N => μ)))
    · simpa [sourceLogTransportNumerator, hz] using he
  have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hz)
  have hCpos : 0 < Csr := hCold.trans_le hCsr
  have hp : 0 < K ^ n := pow_pos hK n
  let ε := γ / (4 * Cold * K ^ n)
  have hε : 0 < ε := div_pos hγpos (by positivity)
  let X := fun x : Fin N → EuclideanSpace ℝ ι =>
    -γ * (N : ℝ) * sourceCanonicalModulatedEnergy
      (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ (fun a b => logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))) N x
  let A := fun x : Fin N → EuclideanSpace ℝ ι =>
    (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  obtain ⟨hlo, blo⟩ := hold (-1) (by norm_num) N hN
  obtain ⟨hhi, bhi⟩ := hold 1 (by norm_num) N hN
  unfold sourceLogTransportNumerator at hlo hhi
  have hlo' : Integrable (fun x => Real.exp (X x - ε * A x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [X, A, ε, sourceLogTransportNumerator, neg_one_mul, one_mul,
      sub_eq_add_neg, neg_mul] using hlo
  have blo' : (∫ x, Real.exp (X x - ε * A x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp 1 := by
    simpa only [X, A, ε, sourceLogTransportNumerator, neg_one_mul, one_mul,
      sub_eq_add_neg, neg_mul] using blo
  have hhi' : Integrable (fun x => Real.exp (X x + ε * A x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    simpa only [X, A, ε, sourceLogTransportNumerator, one_mul] using hhi
  have bhi' : (∫ x, Real.exp (X x + ε * A x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ Real.exp 1 := by
    simpa only [X, A, ε, sourceLogTransportNumerator, one_mul] using bhi
  have ht : |σ * (γ / (4 * Csr * K ^ n))| ≤ ε := by
    rw [abs_mul, hσ, one_mul, abs_of_pos (div_pos hγpos (by positivity))]
    exact div_le_div_of_nonneg_left hγ (by positivity)
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hCsr (by norm_num : (0 : ℝ) ≤ 4)) hp.le)
  unfold sourceLogTransportNumerator
  simpa only [X, A] using
    smaller_parameter_numerator (Measure.pi (fun _ : Fin N => μ)) X A ε hε
      (Real.exp 1) hlo' hhi' blo' bhi' (σ * (γ / (4 * Csr * K ^ n))) ht

theorem exists_sourceLogGaussian_common_control (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧
      (∀ (η : ℝ), 0 < η → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v → ∀ p,
        |sourceLogGaussianShortTransportKernel n η v p| ≤
          Csr * (K : ℝ)^n * gaussianLogShortRange (2 * η) (p.1 - p.2)) ∧
      (∀ (η : ℝ), 0 < η → ∀ (K : ℝ≥0)
        (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι), LipschitzWith K v → ∀ p,
        |sourceLogGaussianLongTransportKernel n η v p| ≤ Csr * (K : ℝ)^n) ∧
      (∀ (η : ℝ), 0 < η → 0 < (Fintype.card ι : ℝ) → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
        ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
        ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ p,
        |hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (sourceLogGaussianShortTransportKernel n η v) p| ≤
          Csr * (K : ℝ)^n *
            (gaussianLogShortRange (2 * η) (p.1 - p.2) + M * η^(Fintype.card ι : ℝ))) ∧
      ∀ {K : ℝ≥0} {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι},
        LipschitzWith K v → 0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
        ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
        ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) →
        Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
          (gaussianRieszDensityMeasure ρ)) →
        ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
          ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
          Integrable (sourceLogTransportNumerator (gaussianRieszDensityMeasure ρ)
            γ n v (σ * (γ / (4 * Csr * (K : ℝ)^n))) N)
            (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ∧
          (∫ x, sourceLogTransportNumerator (gaussianRieszDensityMeasure ρ)
            γ n v (σ * (γ / (4 * Csr * (K : ℝ)^n))) N x
            ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ≤ Real.exp 1 := by
  obtain ⟨Cold, hCold, hlocal⟩ := exists_sourceLogTransport_local_numerator (ι := ι) n hn
  obtain ⟨Clong, hClong, hlong⟩ := exists_sourceLogGaussianLongTransportKernel_uniform_bound (ι := ι) n hn
  let Cn := sourceRieszGaussianDerivativeConstant n
  let D : ℝ := 3 * ((2 * Real.pi)^((Fintype.card ι : ℝ) / 2) /
    (Fintype.card ι : ℝ) * (2 : ℝ)^(Fintype.card ι : ℝ))
  have hCn : 0 < Cn := sourceRieszGaussianDerivativeConstant_pos n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let Csr := Cold + Clong + Cn * (1 + D) + 1
  have hC : 0 < Csr := by dsimp [Csr]; positivity
  have hColdC : Cold ≤ Csr := by
    have hterm : 0 ≤ Cn * (1 + D) := mul_nonneg hCn.le (by linarith)
    dsimp [Csr]; linarith
  have hLongC : Clong ≤ Csr := by
    have hterm : 0 ≤ Cn * (1 + D) := mul_nonneg hCn.le (by linarith)
    dsimp [Csr]; linarith
  have hCnC : Cn ≤ Csr := by
    have hCD : 0 ≤ Cn * D := mul_nonneg hCn.le hD
    dsimp [Csr]; nlinarith
  have hCenteredC : Cn * D ≤ Csr := by dsimp [Csr]; nlinarith
  refine ⟨Csr, hC, ?_, ?_, ?_, ?_⟩
  · intro η hη K v hv p
    exact (sourceLogGaussianShortTransportKernel_bound n η hη hv p).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCnC (by positivity))
        (gaussianLogShortRange_nonneg _ _))
  · intro η hη K v hv p
    exact (hlong η hη K v hv p).trans
      (mul_le_mul_of_nonneg_right hLongC (by positivity))
  · intro η hη hd K v hv ρ M hM hμ hρ p
    have h := sourceLogGaussianShortTransportKernel_centered_bound n η hη hd hv ρ M hM hρ p
    have h1 := mul_le_mul_of_nonneg_right hCnC
      (mul_nonneg (pow_nonneg K.coe_nonneg n) (gaussianLogShortRange_nonneg (2 * η) (p.1 - p.2)))
    have h2 := mul_le_mul_of_nonneg_right hCenteredC
      (mul_nonneg (mul_nonneg (pow_nonneg K.coe_nonneg n) hM) (Real.rpow_nonneg hη.le (Fintype.card ι : ℝ)))
    dsimp [sourceLogGaussianShortTransportPotentialBound] at h
    dsimp [Cn, D] at h1 h2
    nlinarith
  · intro K v hv hK hd ρ M hM hμ hρ hpair
    obtain ⟨βloc, hloc, hnum⟩ := hlocal hv hK hd ρ M hM hρ hpair
    refine ⟨βloc, hloc, ?_⟩
    intro γ hγ hγloc
    exact sourceLogTransportNumerator_enlarge_constant (gaussianRieszDensityMeasure ρ)
      n v γ Cold Csr K hγ hCold hColdC hK (hnum γ hγ hγloc)

/-- The same coefficient supplies the literal piecewise parameter and signed
normalization, with the actual remaining-temperature partition bound. -/
theorem exists_sourceLogGaussian_common_gibbs_moments (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧
      (∀ (η : ℝ), 0 < η → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v → ∀ p,
        |sourceLogGaussianShortTransportKernel n η v p| ≤
          Csr * (K : ℝ)^n * gaussianLogShortRange (2 * η) (p.1 - p.2)) ∧
      (∀ (η : ℝ), 0 < η → ∀ (K : ℝ≥0)
        (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι), LipschitzWith K v → ∀ p,
        |sourceLogGaussianLongTransportKernel n η v p| ≤ Csr * (K : ℝ)^n) ∧
      (∀ (η : ℝ), 0 < η → 0 < (Fintype.card ι : ℝ) → ∀ {K : ℝ≥0}
        {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
        ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
        ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
        (∀ᵐ x ∂volume, ρ x ≤ M) → ∀ p,
        |hoeffdingCentered (gaussianRieszDensityMeasure ρ)
          (sourceLogGaussianShortTransportKernel n η v) p| ≤
          Csr * (K : ℝ)^n *
            (gaussianLogShortRange (2 * η) (p.1 - p.2) + M * η^(Fintype.card ι : ℝ))) ∧
      ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub : ℝ, 1 ≤ Cub ∧
      (∀ N : ℕ, 1 ≤ N → ∀ hlarge : βloc < (β : ℝ),
        (sourceLogSingularPartition
          (⟨2 * (β : ℝ) - βloc, by linarith [hlarge, β.coe_nonneg]⟩ : ℝ≥0) ρ N).toReal ≤ Cub) ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
      let μ := gaussianRieszDensityMeasure ρ
      let a := fun x : Fin N → EuclideanSpace ℝ ι =>
        (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n)
      Integrable (fun x => Real.exp (σ * ε * a x)) (sourceLogSingularGibbs β ρ N) ∧
      (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤
        sourceLogTransportCem (β : ℝ) βloc
          (DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b)))
          DGRHS.Concentration.glzUniversalTailConstant Cub := by
  obtain ⟨Csr, hC, hshort, hlong, hcentered, hlocal⟩ :=
    exists_sourceLogGaussian_common_control (ι := ι) n hn
  refine ⟨Csr, hC, hshort, hlong, hcentered, ?_⟩
  intro K v hv hK hd ρ M hM hμ hρ hpair
  obtain ⟨βloc, hloc, hnum⟩ := hlocal hv hK hd ρ M hM hρ hpair
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  let μ := gaussianRieszDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b => logPhysicalPair (a,b))
  let L := DGRHS.Concentration.glzUniversalTailConstant
  have hL : 0 ≤ L := DGRHS.Concentration.glzUniversalTailConstant_pos.le
  by_cases hsmall : (β : ℝ) ≤ βloc
  · refine ⟨1, le_rfl, ?_, ?_⟩
    · intro N hN hlarge
      exact False.elim (not_lt_of_ge hsmall hlarge)
    intro σ hσ N hN
    let a := fun x : Fin N → EuclideanSpace ℝ ι =>
      (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
    let ε := (β : ℝ) / (4 * Csr * (K : ℝ)^n)
    obtain ⟨hi, hb⟩ := hnum (β : ℝ) β.coe_nonneg hsmall σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_exponential_bound β hd ρ M hM hρ hpair N hN
      (fun x => σ * ε * a x) (Real.exp 1) hi hb
    refine ⟨by simpa only [sourceLogTransportEpsilon, if_pos hsmall] using hq, ?_⟩
    have hr : Real.exp 1 / Real.exp ((β : ℝ)*I) = Real.exp (-(β : ℝ)*I)*Real.exp 1 := by
      rw [div_eq_mul_inv, ←Real.exp_neg]
      ring
    simp only [sourceLogTransportEpsilon, if_pos hsmall, sourceLogTransportCem, if_pos hsmall]
    change (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤ _
    change (∫ x, Real.exp (σ * ε * a x) ∂sourceLogSingularGibbs β ρ N) ≤
      Real.exp 1 / Real.exp ((β : ℝ)*I) at hqb
    rw [hr] at hqb
    simpa only [sourceLogTransportCem, if_pos hsmall] using
      hqb.trans (mul_le_mul_of_nonneg_left (by linarith : Real.exp 1 ≤ Real.exp 1 + L)
        (Real.exp_pos (-(β : ℝ)*I)).le)
  · have hlarge : βloc < (β : ℝ) := lt_of_not_ge hsmall
    let γ : ℝ≥0 := ⟨βloc, hloc.le⟩
    have hγβ : (γ : ℝ) ≤ (β : ℝ) := hlarge.le
    let θ : ℝ≥0 := ⟨2*(β : ℝ)-(γ : ℝ), by linarith [β.coe_nonneg]⟩
    obtain ⟨Cub, hCub, hcap⟩ := sourceLogPartition_original_bounds_one_le θ hd ρ M hM hρ hpair
    refine ⟨Cub, hCub, ?_, ?_⟩
    · intro N hN _
      exact (hcap N hN).2
    intro σ hσ N hN
    let a := fun x : Fin N → EuclideanSpace ℝ ι =>
      (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
    let t := σ * (βloc / (4 * Csr * (K : ℝ)^n))
    obtain ⟨hi, hb⟩ := hnum βloc hloc.le le_rfl σ hσ N (by omega)
    obtain ⟨hq, hqb⟩ := sourceLog_gibbs_holder_bound β γ hγβ hd ρ M hM hρ hpair
      N hN a t (Real.exp 1) Cub hi hb (hcap N hN).2
    have he : t / 2 = σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ)^n) := by
      dsimp [t, sourceLogTransportEpsilon]
      rw [if_neg hsmall]
      ring
    simp_rw [he] at hq hqb
    refine ⟨hq, ?_⟩
    simp only [sourceLogTransportCem, if_neg hsmall]
    change (∫ x, Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr
      ((K : ℝ)^n) * a x) ∂sourceLogSingularGibbs β ρ N) ≤
        Real.exp (-(β : ℝ)*I)*Real.sqrt (Real.exp 1+L)*Real.sqrt Cub
    exact hqb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : Real.exp 1 ≤ Real.exp 1 + L))
        (Real.exp_pos _).le) (Real.sqrt_nonneg _))


end DGRHS.Commutator
