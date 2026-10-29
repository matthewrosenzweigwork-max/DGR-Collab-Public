import DGRHS.Commutator.SourceLogTransportParameter

noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator

/-- Scalar bounds for the doubled manuscript small-temperature parameter. -/
lemma local_log_transport_scalar (C L γ σ : ℝ) (hC : 0 ≤ C) (hL : 0 < L)
    (hγ : 0 ≤ γ) (hγ6 : γ ≤ 1 / 6)
    (hγq : γ ≤ 1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (hσ : |σ| = 1) :
    let t := 2 * (σ * (γ / (4 * (C + 1) * L)))
    let Q := DGRHS.Attractive.attractiveMomentConstant * (4 * C * L)
    |t| * Q < 1 ∧
      Real.exp (3 * |t| * C * L) * (2 / (1 - (t * Q) ^ 2)) ≤
        (128 / 63 : ℝ) * Real.exp (1 / 4) := by
  let t := 2 * (σ * (γ / (4 * (C + 1) * L)))
  let Q := DGRHS.Attractive.attractiveMomentConstant * (4 * C * L)
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hCp : 0 < C + 1 := by linarith
  have hat : |t| = γ / (2 * (C + 1) * L) := by
    dsimp [t]
    rw [abs_mul, abs_mul, hσ, abs_of_nonneg (div_nonneg hγ (by positivity))]
    norm_num
    field_simp
    ring
  have hq0 : 0 ≤ |t| * Q := by dsimp [Q]; positivity
  have hqa : |t| * Q ≤ 2 * γ * DGRHS.Attractive.attractiveMomentConstant := by
    rw [hat]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (C + 1) * L)).mpr
    dsimp [Q]
    nlinarith [mul_nonneg hγ hA.le, mul_nonneg (mul_nonneg hγ hA.le) hL.le]
  have hγA : γ * (16 * DGRHS.Attractive.attractiveMomentConstant) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hγq
  have hq : |t| * Q ≤ 1 / 8 := by linarith
  have hc : 3 * |t| * C * L ≤ 1 / 4 := by
    rw [hat]
    have hr : 3 * (γ / (2 * (C + 1) * L)) * C * L ≤ 3 * γ / 2 := by
      have he : 3 * (γ / (2 * (C + 1) * L)) * C * L =
          (3 * γ * C * L) / (2 * (C + 1) * L) := by ring
      rw [he]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (C + 1) * L)).mpr
      nlinarith [mul_nonneg hγ hL.le]
    linarith
  have hs : (t * Q) ^ 2 = (|t| * Q) ^ 2 := by simp only [mul_pow, sq_abs]
  have hd : (63 / 64 : ℝ) ≤ 1 - (t * Q) ^ 2 := by rw [hs]; nlinarith
  have hf : 2 / (1 - (t * Q) ^ 2) ≤ (128 / 63 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - (t * Q) ^ 2)).mpr
    linarith
  exact ⟨by linarith, (mul_le_mul (Real.exp_le_exp.mpr hc) hf
    (by positivity) (Real.exp_pos _).le).trans_eq (by ring)⟩

/-- Interpolation of the actual beta-one repulsive partition, including gamma zero. -/
lemma local_repulsive_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω → ℝ) (Cp γ : ℝ)
    (hCp : 0 < Cp) (hE : Integrable (fun x => Real.exp (-E x)) μ)
    (hb : (∫ x, Real.exp (-E x) ∂μ) ≤ Cp)
    (hγ : 0 ≤ γ) (hγ6 : γ ≤ 1 / 6) (hγp : γ ≤ 1 / (6 * (Cp + 1))) :
    Integrable (fun x => Real.exp (-2 * γ * E x)) μ ∧
      (∫ x, Real.exp (-2 * γ * E x) ∂μ) ≤ (4 / 3 : ℝ) := by
  obtain ⟨hi, hbi⟩ := DGRHS.Concentration.interpolated_exp_integral μ
    (fun _ => 0) (fun x => -E x) aemeasurable_const
    (aemeasurable_of_exp_integrable μ _ hE)
    (by simp) hE (2 * γ) (by positivity) (by linarith)
  have he (x : Ω) : (1 - 2 * γ) * 0 + 2 * γ * (-E x) = -2 * γ * E x := by ring
  simp_rw [he] at hi hbi
  refine ⟨hi, hbi.trans ?_⟩
  have hg := (le_div_iff₀ (by positivity : 0 < 6 * (Cp + 1))).mp hγp
  have hp := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * γ)
  have hzero : (∫ x : Ω, Real.exp (0 : ℝ) ∂μ) = 1 := by simp
  rw [hzero]
  nlinarith

lemma local_log_transport_cs_constant :
    Real.sqrt (4 / 3 : ℝ) * Real.sqrt ((128 / 63 : ℝ) * Real.exp (1 / 4)) ≤
      Real.exp 1 := by
  have he := Real.add_one_le_exp (7 / 4 : ℝ)
  have hnum : (512 / 189 : ℝ) ≤ Real.exp (7 / 4) := by linarith
  have hp : (4 / 3 : ℝ) * ((128 / 63 : ℝ) * Real.exp (1 / 4)) ≤ Real.exp 1 ^ 2 := by
    calc
      _ = (512 / 189 : ℝ) * Real.exp (1 / 4) := by ring
      _ ≤ Real.exp (7 / 4) * Real.exp (1 / 4) :=
        mul_le_mul_of_nonneg_right hnum (Real.exp_pos _).le
      _ = Real.exp 1 ^ 2 := by rw [← Real.exp_add, pow_two, ← Real.exp_add]; norm_num
  have h1 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4 / 3)
  have h2 := Real.sq_sqrt (by positivity : 0 ≤ (128 / 63 : ℝ) * Real.exp (1 / 4))
  have h0 : 0 ≤ Real.sqrt (4 / 3 : ℝ) *
      Real.sqrt ((128 / 63 : ℝ) * Real.exp (1 / 4)) := by positivity
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- An actual local numerator bounded by e, with the exact small-beta source parameter.
The constant Csr is chosen before the density and velocity. This is a bounded-log
transport proof adaptation, not a use of a short-range derivative estimate. -/
theorem exists_sourceLogTransport_local_numerator {ι : Type*} [Fintype ι]
    (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0}
      {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}, LipschitzWith K v →
      0 < (K : ℝ) → 0 < (Fintype.card ι : ℝ) →
      ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume, ρ x ≤ M) →
      Integrable DGRHS.Gaussian.logPhysicalPair
        ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod
          (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc →
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
  intro K v hv hK hd ρ M hM hμ hρ hpair
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  obtain ⟨Cp, hCp, hrep⟩ := DGRHS.CLT.sourceLogPartition_uniform 1 (by norm_num)
    hd ρ M hM hρ hpair
  let βloc := min (1 / 6 : ℝ) (min (1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (1 / (6 * (Cp + 1))))
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hloc : 0 < βloc := by
    dsimp [βloc]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨βloc, hloc, ?_⟩
  intro γ hγ hγloc σ hσ N hN
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
    simpa [E, μ] using hr
  have hrb' : (∫ x, Real.exp (-E x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    simpa [E, μ] using hrb
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

/-- Constant velocity has zero actual contraction kernel, including collisions. -/
lemma sourceLogTransportKernel_zero_lipschitz {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (n : ℕ) (hn : 0 < n) {v : E → E} (hv : LipschitzWith 0 v) :
    sourceLogTransportKernel n v = fun _ => 0 := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  funext p
  have hp : |sourceLogTransportKernel n v p| ≤ 0 := by
    simpa [hn.ne'] using hb hv p
  exact abs_eq_zero.mp (le_antisymm hp (abs_nonneg _))

/-- The literal signed empirical energy is zero for constant velocity, for every N. -/
lemma sourceTransportEnergy_zero_lipschitz {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] (μ : Measure E) (n : ℕ) (hn : 0 < n)
    {v : E → E} (hv : LipschitzWith 0 v) (N : ℕ) (x : Fin N → E) :
    sourceTransportEnergy μ (sourceLogTransportKernel n v) N x = 0 := by
  rw [sourceLogTransportKernel_zero_lipschitz n hn hv]
  simp [sourceTransportEnergy, DGRHS.CLT.sourceCanonicalModulatedEnergy,
    DGRHS.Gaussian.hoeffdingCentered, DGRHS.centeredKernel, DGRHS.secondPotential,
    DGRHS.potential, DGRHS.interactionEnergy,
    DGRHS.CanonicalVariance.normalizedOffDiagonalSum, DGRHS.CanonicalVariance.offDiagonalSum]

end DGRHS.Commutator
#print axioms DGRHS.Commutator.local_log_transport_scalar
#print axioms DGRHS.Commutator.local_repulsive_interpolation
#print axioms DGRHS.Commutator.local_log_transport_cs_constant
#print axioms DGRHS.Commutator.exists_sourceLogTransport_local_numerator
#check @DGRHS.Commutator.exists_sourceLogTransport_local_numerator

#print axioms DGRHS.Commutator.sourceLogTransportKernel_zero_lipschitz
#print axioms DGRHS.Commutator.sourceTransportEnergy_zero_lipschitz
#check @DGRHS.Commutator.sourceTransportEnergy_zero_lipschitz
