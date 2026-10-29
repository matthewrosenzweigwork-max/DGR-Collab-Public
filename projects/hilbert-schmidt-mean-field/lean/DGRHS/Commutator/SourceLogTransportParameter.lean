import DGRHS.Commutator.SourceLogTransportNumerator
import DGRHS.Concentration.MasterInterpolation

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace DGRHS.Commutator

lemma aemeasurable_of_exp_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ) :
    AEMeasurable f μ := by
  simpa only [Function.comp_def, Real.log_exp] using
    Real.measurable_log.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable

/-- Reducing the signed parameter preserves the common numerator constant, without a factor two. -/
lemma smaller_parameter_numerator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X A : Ω → ℝ) (ε : ℝ) (hε : 0 < ε) (C : ℝ)
    (hlo : Integrable (fun x => Real.exp (X x - ε * A x)) μ)
    (hhi : Integrable (fun x => Real.exp (X x + ε * A x)) μ)
    (hloBound : (∫ x, Real.exp (X x - ε * A x) ∂μ) ≤ C)
    (hhiBound : (∫ x, Real.exp (X x + ε * A x) ∂μ) ≤ C)
    (t : ℝ) (ht : |t| ≤ ε) :
    Integrable (fun x => Real.exp (X x + t * A x)) μ ∧
      (∫ x, Real.exp (X x + t * A x) ∂μ) ≤ C := by
  let θ := (t + ε) / (2 * ε)
  have htlo : -ε ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ ε := (abs_le.mp ht).2
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by positivity)
  have hθ1 : θ ≤ 1 := (div_le_one (by positivity : 0 < 2 * ε)).mpr (by linarith)
  obtain ⟨hi, hb⟩ := DGRHS.Concentration.interpolated_exp_integral μ
    (fun x => X x - ε * A x) (fun x => X x + ε * A x)
    (aemeasurable_of_exp_integrable μ _ hlo) (aemeasurable_of_exp_integrable μ _ hhi)
    hlo hhi θ hθ0 hθ1
  have he (x : Ω) : (1 - θ) * (X x - ε * A x) + θ * (X x + ε * A x) =
      X x + t * A x := by
    dsimp [θ]
    field_simp
    ring
  simp_rw [he] at hi hb
  refine ⟨hi, hb.trans ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hloBound (by linarith : 0 ≤ 1 - θ)
  have h2 := mul_le_mul_of_nonneg_left hhiBound hθ0
  linarith

/-- A separate min-parameter adaptation; this is not the manuscript piecewise formula. -/
lemma log_min_parameter_admissible (ε Csr L β : ℝ) (hε : 0 < ε)
    (hCsr : 0 < Csr) (hL : 0 < L) (hβ : 0 < β) :
    let βloc := 8 * Csr * L * ε
    0 < min β βloc / (8 * Csr * L) ∧ min β βloc / (8 * Csr * L) ≤ ε := by
  have hd : 0 < 8 * Csr * L := by positivity
  dsimp only
  constructor
  · exact div_pos (lt_min hβ (by positivity)) hd
  · apply (div_le_iff₀ hd).mpr
    calc
      min β (8 * Csr * L * ε) ≤ 8 * Csr * L * ε := min_le_right _ _
      _ = ε * (8 * Csr * L) := by ring

def sourceLogTransportEpsilon (β βloc Csr L : ℝ) : ℝ :=
  if β ≤ βloc then β / (4 * Csr * L) else βloc / (8 * Csr * L)

lemma source_log_parameter_admissible (ε Csr L β : ℝ) (hε : 0 < ε)
    (hCsr : 0 < Csr) (hL : 0 < L) (hβ : 0 < β) :
    let βloc := 4 * Csr * L * ε
    0 < sourceLogTransportEpsilon β βloc Csr L ∧
      sourceLogTransportEpsilon β βloc Csr L ≤ ε := by
  have h4 : 0 < 4 * Csr * L := by positivity
  have h8 : 0 < 8 * Csr * L := by positivity
  dsimp only
  unfold sourceLogTransportEpsilon
  split_ifs with h
  · refine ⟨div_pos hβ h4, (div_le_iff₀ h4).mpr ?_⟩
    exact h.trans_eq (by ring)
  · refine ⟨div_pos (by positivity) h8, (div_le_iff₀ h8).mpr ?_⟩
    calc
      4 * Csr * L * ε = (ε / 2) * (8 * Csr * L) := by ring
      _ ≤ ε * (8 * Csr * L) := mul_le_mul_of_nonneg_right (by linarith) h8.le

def sourceLogTransportNumerator {ι : Type*} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) (β : ℝ) (n : ℕ)
    (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (t : ℝ) (N : ℕ)
    (x : Fin N → EuclideanSpace ℝ ι) : ℝ :=
  Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
    (DGRHS.potential μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b))) N x +
      t * ((N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x))

/-- The original displayed piecewise parameter, obtained from actual physical
moments by convex interpolation and an admissible choice of the local threshold. -/
theorem exists_sourceLogTransport_source_profile
    {ι : Type*} [Fintype ι] (n : ℕ) (hn : 0 < n)
    {K : ℝ≥0} {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (hK : 0 < (K : ℝ)) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable DGRHS.Gaussian.logPhysicalPair
      ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod
        (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ))) :
    ∃ Csr : ℝ, 0 < Csr ∧
      (∀ p, |sourceLogTransportKernel n v p| ≤ Csr * (K : ℝ) ^ n) ∧
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ, 0 < β → ∃ Cem : ℝ, 0 < Cem ∧
        ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
        Integrable (sourceLogTransportNumerator (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)
          β n v (σ * sourceLogTransportEpsilon β βloc Csr ((K : ℝ) ^ n)) N)
          (Measure.pi (fun _ : Fin N => DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) ∧
        (∫ x, sourceLogTransportNumerator (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)
          β n v (σ * sourceLogTransportEpsilon β βloc Csr ((K : ℝ) ^ n)) N x
          ∂Measure.pi (fun _ : Fin N => DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) ≤ Cem := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := EuclideanSpace ℝ ι) n hn
  let Csr := C + 1
  have hCs : 0 < Csr := by dsimp [Csr]; linarith
  obtain ⟨ε, hε, hnum⟩ := exists_sourceLogTransport_unnormalized_exponential
    n hn hv hd ρ M hM hρ hpair
  let βloc := 4 * Csr * (K : ℝ) ^ n * ε
  have hloc : 0 < βloc := by dsimp [βloc]; positivity
  refine ⟨Csr, hCs, ?_, βloc, hloc, ?_⟩
  · intro p
    exact (hb hv p).trans (mul_le_mul_of_nonneg_right (by change C ≤ C + 1; linarith)
      (pow_nonneg K.coe_nonneg n))
  intro β hβ
  obtain ⟨Cem, hCem, hmoment⟩ := hnum β hβ.le
  refine ⟨Cem, hCem, ?_⟩
  intro σ hσ N hN
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let X := fun x : Fin N → EuclideanSpace ℝ ι => -β * (N : ℝ) *
    DGRHS.CLT.sourceCanonicalModulatedEnergy
      (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
      (DGRHS.potential μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b)))
      (DGRHS.interactionEnergy μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b))) N x
  let A := fun x : Fin N → EuclideanSpace ℝ ι =>
    (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  have hlo := hmoment (-1) (by norm_num) N hN
  have hhi := hmoment 1 (by norm_num) N hN
  have hminus : (fun x : Fin N → EuclideanSpace ℝ ι =>
      Real.exp (X x - ε * A x)) = fun x => Real.exp
      (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
        (DGRHS.potential μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b))) N x +
          (-1) * ε * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x) := by
    funext x
    congr 1
    dsimp [X, A]
    ring
  have hplus : (fun x : Fin N → EuclideanSpace ℝ ι =>
      Real.exp (X x + ε * A x)) = fun x => Real.exp
      (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
        (DGRHS.potential μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy μ (fun a b => DGRHS.Gaussian.logPhysicalPair (a,b))) N x +
          1 * ε * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x) := by
    funext x
    congr 1
    dsimp [X, A]
    ring
  rw [← hminus] at hlo
  rw [← hplus] at hhi
  have hadm := source_log_parameter_admissible ε Csr ((K : ℝ) ^ n) β hε hCs (pow_pos hK n) hβ
  have ht : |σ * sourceLogTransportEpsilon β βloc Csr ((K : ℝ) ^ n)| ≤ ε := by
    rw [abs_mul, hσ, one_mul, abs_of_pos hadm.1]
    exact hadm.2
  exact smaller_parameter_numerator (Measure.pi (fun _ : Fin N => μ)) X A ε hε Cem
    hlo.1 hhi.1 hlo.2 hhi.2 _ ht

end DGRHS.Commutator
#print axioms DGRHS.Commutator.smaller_parameter_numerator
#print axioms DGRHS.Commutator.source_log_parameter_admissible
#check @DGRHS.Commutator.smaller_parameter_numerator

#print axioms DGRHS.Commutator.exists_sourceLogTransport_source_profile
#check @DGRHS.Commutator.exists_sourceLogTransport_source_profile
