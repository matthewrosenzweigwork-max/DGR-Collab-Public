import DGRHS.Gaussian.PeriodicRieszParticleLink

/-!
Packet P9h, unit 2 (part 27): the torus transport energy, its one-body correction and the local
numerator estimate (torus versions of `SourceRieszLocalEnergy` and `SourceRieszLocalNumerator`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The literal transport energy of Theorem 2.8 on the torus: twice the modulated energy of the
transport kernel. -/
def periodicRieszTransportEnergy (s : ℝ) (n : ℕ) (v : PeriodicTorus ι → E) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  2 * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszTransportKernel n s v))
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszTransportKernel n s v (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszTransportKernel n s v (a, b))) N ω

/-- The one-body correction of the scaled transport energy. -/
def periodicRieszTransportCorrection (s : ℝ) (n : ℕ) (v : PeriodicTorus ι → E)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  -2 * (N : ℝ)⁻¹ * (∑ i : Fin N, ∫ y, periodicRieszTransportKernel n s v (ω i, y)
      ∂periodicCappedDensityMeasure ρ) +
    ∫ p, periodicRieszTransportKernel n s v p
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)

lemma periodicRieszTransportEnergy_scaled (s : ℝ) (n : ℕ) (v : PeriodicTorus ι → E)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (hN : 0 < N) (ω : Fin N → PeriodicTorus ι) :
    (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω =
      -2 * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszTransportKernel n s v)) ω +
      periodicRieszTransportCorrection s n v ρ N ω := by
  have he := DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszTransportKernel n s v))
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszTransportKernel n s v (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b => periodicRieszTransportKernel n s v (a, b))) (-2) hN ω
  rw [← periodic_energy_normalization (-2)] at he
  dsimp [periodicRieszTransportEnergy, periodicRieszTransportCorrection, DGRHS.potential,
    DGRHS.interactionEnergy] at *
  nlinarith [he]

/-! ### Bounds for the one-body correction -/

/-- The transport potential constant. -/
def periodicRieszTransportBound (ι : Type u) [Fintype ι] [Nonempty ι] (s M : ℝ) (n : ℕ) (K : ℝ≥0) : ℝ :=
  (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
    (M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι + 1))

lemma periodicRieszTransport_section (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (x : PeriodicTorus ι) :
    Integrable (fun y => periodicRieszTransportKernel n s v (x, y)) (periodicCappedDensityMeasure ρ) ∧
    |∫ y, periodicRieszTransportKernel n s v (x, y) ∂periodicCappedDensityMeasure ρ| ≤
      periodicRieszTransportBound ι s M n K := by
  let μ := periodicCappedDensityMeasure ρ
  have hΨ := periodicRieszShortFun_integrable (ι := ι) s 1 hs hs2 one_pos
  have hrow := periodicDensityRow_integrable_of_haar ρ M hρ _ hΨ x
  have hC := (periodicRieszProfileC_ge (ι := ι) s hs n).2.2
  have hKn : 0 ≤ (K : ℝ) ^ n := by positivity
  have hg : Integrable (fun y => (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
      (periodicRieszMajorantFun s (x - y) + 1))) μ :=
    ((hrow.add (integrable_const (1 : ℝ))).const_mul _).const_mul _
  have hm : AEStronglyMeasurable (fun y => periodicRieszTransportKernel n s v (x, y)) μ :=
    ((periodicRieszTransportKernel_measurable n hn s hs hs2 hv).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hb : ∀ y, |periodicRieszTransportKernel n s v (x, y)| ≤ (K : ℝ) ^ n *
      (periodicRieszProfileC ι s n * (periodicRieszMajorantFun s (x - y) + 1)) := fun y =>
    periodicRieszTransportKernel_bound_fun n hn s hs hs2 hv (x, y)
  have hi : Integrable (fun y => periodicRieszTransportKernel n s v (x, y)) μ :=
    hg.mono' hm (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb y)
  refine ⟨hi, ?_⟩
  have hnn := periodicDensityRow_nonnegative_bound ρ M hM hρ (periodicRieszMajorantFun s) hΨ
    (fun z => periodicRieszShortFun_nonneg s 1 hs z) x
  calc |∫ y, periodicRieszTransportKernel n s v (x, y) ∂μ|
      ≤ ∫ y, |periodicRieszTransportKernel n s v (x, y)| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun y => periodicRieszTransportKernel n s v (x, y))
    _ ≤ ∫ y, (K : ℝ) ^ n * (periodicRieszProfileC ι s n * (periodicRieszMajorantFun s (x - y) + 1)) ∂μ :=
        integral_mono hi.abs hg hb
    _ = (K : ℝ) ^ n * (periodicRieszProfileC ι s n *
          ((∫ y, periodicRieszMajorantFun s (x - y) ∂μ) + 1)) := by
        rw [integral_const_mul, integral_const_mul, integral_add hrow (integrable_const _)]
        have h1 : ∫ _ : PeriodicTorus ι, (1 : ℝ) ∂μ = 1 := by simp
        rw [h1]
    _ ≤ periodicRieszTransportBound ι s M n K := by
        unfold periodicRieszTransportBound
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by linarith)) hKn
        linarith

lemma periodicRieszTransport_pair (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Integrable (periodicRieszTransportKernel n s v)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ∧
    |∫ p, periodicRieszTransportKernel n s v p
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)| ≤
      periodicRieszTransportBound ι s M n K := by
  let μ := periodicCappedDensityMeasure ρ
  have hi := integrable_periodicRieszTransportKernel ρ M hρ n hn s hs hs2 hv
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  calc |∫ x, ∫ y, periodicRieszTransportKernel n s v (x, y) ∂μ ∂μ|
      ≤ ∫ x, |∫ y, periodicRieszTransportKernel n s v (x, y) ∂μ| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => ∫ y, periodicRieszTransportKernel n s v (x, y) ∂μ)
    _ ≤ ∫ _ : PeriodicTorus ι, periodicRieszTransportBound ι s M n K ∂μ :=
        integral_mono hi.integral_prod_left.abs (integrable_const _) (fun x =>
          (periodicRieszTransport_section n hn s hs hs2 hv ρ M hM hρ x).2)
    _ = _ := by simp

lemma abs_periodicRieszTransportCorrection_le (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 0 < N) (ω : Fin N → PeriodicTorus ι) :
    |periodicRieszTransportCorrection s n v ρ N ω| ≤ 3 * periodicRieszTransportBound ι s M n K := by
  let μ := periodicCappedDensityMeasure ρ
  let B := periodicRieszTransportBound ι s M n K
  have hm := (periodicRieszTransport_pair n hn s hs hs2 hv ρ M hM hρ).2
  have hsum : |∑ i : Fin N, ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ| ≤ (N : ℝ) * B := by
    calc _ ≤ ∑ i : Fin N, |∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin N, B := Finset.sum_le_sum (fun i _ =>
          (periodicRieszTransport_section n hn s hs hs2 hv ρ M hM hρ (ω i)).2)
      _ = _ := by simp
  have hn' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha : |(N : ℝ)⁻¹ * (∑ i : Fin N, ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ)| ≤ B := by
    rw [abs_mul, abs_inv, abs_of_pos hn']
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn'.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul] using h
  unfold periodicRieszTransportCorrection
  rw [show -2 * (N : ℝ)⁻¹ * (∑ i : Fin N, ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ) =
    -2 * ((N : ℝ)⁻¹ * (∑ i : Fin N, ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ)) by ring]
  have ht := abs_add_le (-2 * ((N : ℝ)⁻¹ * (∑ i : Fin N,
    ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂μ)))
    (∫ p, periodicRieszTransportKernel n s v p ∂μ.prod μ)
  rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num] at ht
  linarith

lemma periodicRieszTransportCorrection_scaled_bound (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 0 < N) (ω : Fin N → PeriodicTorus ι) :
    σ * periodicRieszCoefficient ι s n K γ * periodicRieszTransportCorrection s n v ρ N ω ≤
      (3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M := by
  let ε := periodicRieszCoefficient ι s n K γ
  have hε : 0 ≤ ε := periodicRieszCoefficient_nonneg (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hb := abs_periodicRieszTransportCorrection_le n hn s hs hs2 hv ρ M hM hρ N hN ω
  have he := periodicRieszCoefficient_mul_le (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hΨ0 : 0 ≤ ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι :=
    integral_nonneg (fun z => periodicRieszShortFun_nonneg s 1 hs z)
  have hP := (periodicRieszPotConst_ge (ι := ι) s hs hs2 M hM).1
  have hP1 := (periodicRieszPotConst_ge (ι := ι) s hs hs2 M hM).2.2
  have hq : M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι + 1 ≤
      periodicRieszPotConst s hs2 M := by
    unfold periodicRieszPotConst
    have : 0 ≤ M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
      mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
    nlinarith
  have hr : σ * ε * periodicRieszTransportCorrection s n v ρ N ω ≤
      ε * |periodicRieszTransportCorrection s n v ρ N ω| := by
    calc _ ≤ |σ * ε * periodicRieszTransportCorrection s n v ρ N ω| := le_abs_self _
      _ = |σ| * ε * |periodicRieszTransportCorrection s n v ρ N ω| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hε]
      _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_right hσ (mul_nonneg hε (abs_nonneg (periodicRieszTransportCorrection s n v ρ N ω)))]
  have hb' := mul_le_mul_of_nonneg_left hb hε
  have hbd : ε * (3 * periodicRieszTransportBound ι s M n K) ≤ (3 / 4 : ℝ) * γ *
      (M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι + 1) := by
    unfold periodicRieszTransportBound
    have hq0 : 0 ≤ M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι + 1 := by
      have := mul_nonneg hM hΨ0
      linarith
    have := mul_le_mul_of_nonneg_right he hq0
    nlinarith [this]
  have hfin : (3 / 4 : ℝ) * γ * (M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι + 1) ≤
      (3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  linarith

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszTransportEnergy_scaled
#print axioms DGRHS.Periodic.periodicRieszTransport_pair
#print axioms DGRHS.Periodic.periodicRieszTransportCorrection_scaled_bound
