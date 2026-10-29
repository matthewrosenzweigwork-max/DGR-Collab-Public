import DGRHS.Commutator.SourceLogTransportFamilyPartition

noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator

/-- Csr depends only on dimension/order. The local threshold is chosen BEFORE
all densities in the class and works for every globally Lipschitz transport
with the displayed common Lipschitz coefficient. No origin-tail or desired
family partition/moment bound is an input. -/
theorem exists_log_transport_family_local_numerator {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) →
      ∀ M : ℝ, 0 ≤ M → 0 < (Fintype.card ι : ℝ) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
      LipschitzWith K v →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ),
      ∀ [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable DGRHS.Gaussian.logPhysicalPair
        ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod
          (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (sourceLogTransportNumerator (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)
        γ n v (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) N)
        (Measure.pi (fun _ : Fin N => DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) ∧
      (∫ x, sourceLogTransportNumerator (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)
        γ n v (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) N x
        ∂Measure.pi (fun _ : Fin N => DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) ≤
          Real.exp 1 := by
  obtain ⟨C, hC, hmoment⟩ := exists_sourceLogTransport_energy_exponential
    (E := EuclideanSpace ℝ ι) n hn
  refine ⟨C + 1, by linarith, ?_⟩
  intro K hK M hM hd
  obtain ⟨Cp, hCp, hfamily⟩ := exists_log_family_source_cap (ι := ι) 1 (by norm_num) hd M hM
  let βloc := min (1 / 6 : ℝ) (min (1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (1 / (6 * (Cp + 1))))
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hloc : 0 < βloc := by
    dsimp [βloc]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨βloc, hloc, ?_⟩
  intro v hv ρ hμ hρ hpair γ hγ hγloc σ hσ N hN
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  have hrep := hfamily ρ hρ hpair
  have hγ6 : γ ≤ 1 / 6 := hγloc.trans (min_le_left _ _)
  have hγq : γ ≤ 1 / (16 * DGRHS.Attractive.attractiveMomentConstant) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγp : γ ≤ 1 / (6 * (Cp + 1)) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_right _ _))
  let t := σ * (γ / (4 * (C + 1) * (K : ℝ) ^ n))
  have hscalar := local_log_transport_scalar C ((K : ℝ) ^ n) γ σ hC (pow_pos hK n)
    hγ hγ6 hγq hσ
  obtain ⟨hc, hcb⟩ := hmoment hv μ (2 * t) (by simpa [t] using hscalar.1) N hN
  have hcBound : (∫ x : Fin N → EuclideanSpace ℝ ι,
      Real.exp ((2 * t) * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ (128 / 63 : ℝ) * Real.exp (1 / 4) :=
    hcb.trans (by simpa [t, mul_assoc] using hscalar.2)
  let E := fun x : Fin N → EuclideanSpace ℝ ι => (N : ℝ) *
    DGRHS.CLT.sourceCanonicalModulatedEnergy
      (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
      (DGRHS.potential μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b))) N x
  obtain ⟨hr, hrb⟩ := hrep N (by omega)
  have hr' : Integrable (fun x => Real.exp (-E x)) (Measure.pi (fun _ : Fin N => μ)) := by
    have hfun : sourceLogTransportNumerator μ 1 1 (fun _ => 0) 0 N = fun x => Real.exp (-E x) := by
      funext x
      simp [sourceLogTransportNumerator, E]
    change Integrable (sourceLogTransportNumerator μ 1 1 (fun _ => 0) 0 N)
      (Measure.pi (fun _ : Fin N => μ)) at hr
    rw [hfun] at hr
    exact hr
  have hrb' : (∫ x, Real.exp (-E x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    have hfun : sourceLogTransportNumerator μ 1 1 (fun _ => 0) 0 N = fun x => Real.exp (-E x) := by
      funext x
      simp [sourceLogTransportNumerator, E]
    change (∫ x, sourceLogTransportNumerator μ 1 1 (fun _ => 0) 0 N x
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp at hrb
    rw [hfun] at hrb
    exact hrb
  obtain ⟨hri, hrbi⟩ := local_repulsive_interpolation
    (Measure.pi (fun _ : Fin N => μ)) E Cp γ hCp hr' hrb' hγ hγ6 hγp
  let X := fun x => -γ * E x
  let Y := fun x : Fin N → EuclideanSpace ℝ ι =>
    t * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  have hx : Integrable (fun x => Real.exp (2 * X x)) (Measure.pi (fun _ : Fin N => μ)) := by
    convert hri using 1
    funext x
    congr 1
    dsimp [X]
    ring
  have hy : Integrable (fun x => Real.exp (2 * Y x)) (Measure.pi (fun _ : Fin N => μ)) := by
    convert hc using 1
    funext x
    congr 1
    dsimp [Y]
    ring
  obtain ⟨hi, hib⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hx)
    (aemeasurable_of_exp_double_integrable _ Y hy) hx hy
  have hxb : (∫ x, Real.exp (2 * X x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ 4 / 3 := by
    convert hrbi using 1
    congr 1
    funext x
    congr 1
    dsimp [X]
    ring
  have hyb : (∫ x, Real.exp (2 * Y x) ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (128 / 63 : ℝ) * Real.exp (1 / 4) := by
    convert hcBound using 1
    congr 1
    funext x
    congr 1
    dsimp [Y]
    ring
  have he : (fun x => Real.exp (X x + Y x)) =
      sourceLogTransportNumerator μ γ n v t N := by
    funext x
    congr 1
    dsimp [X, Y, E, sourceLogTransportNumerator]
    ring
  rw [he] at hi hib
  exact ⟨hi, hib.trans ((mul_le_mul (Real.sqrt_le_sqrt hxb) (Real.sqrt_le_sqrt hyb)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans local_log_transport_cs_constant)⟩

end DGRHS.Commutator
#print axioms DGRHS.Commutator.exists_log_transport_family_local_numerator
#check @DGRHS.Commutator.exists_log_transport_family_local_numerator
