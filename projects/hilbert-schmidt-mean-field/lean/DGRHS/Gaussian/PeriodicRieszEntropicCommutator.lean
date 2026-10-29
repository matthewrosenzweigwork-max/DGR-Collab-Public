import DGRHS.Gaussian.PeriodicRieszEntropicTransfer

/-!
Packet P9h, unit 2 (part 30): Theorem 2.8 (`thm:entropicCommutator`, TeX 691-736) on the torus
(Remark 2.1) for the Riesz kernel `0 < s < d/2`, with the printed constants of Remark A.1
(`eq:CemLargeBetaDef`, TeX 4144-4156): `C_em = e + L` for `β ≤ β_loc` and
`C_em = e^{-β I_μ} (e + L)^{1/2} C_ub(2β - β_loc, μ)^{1/2}` for `β > β_loc`.

Torus version of `SourceRieszEntropicCommutator` and `SourceRieszEntropicCommutatorPrinted`.  The
partition constants `C_ub`, `C_pf` and `C_em` depend on the background `μ` (as in the printed
`C_pf(β,μ)`, `C_em(β,μ,v,n)`); `β_loc` and the transport parameter `ε_{β,n}` do not.
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Printed `C_em` of Remark A.1 without the Jensen factor (the numerator constant). -/
def periodicRieszTransportCem (β βloc L Cub : ℝ) : ℝ :=
  if β ≤ βloc then Real.exp 1 + L else Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub

lemma one_le_periodicRieszTransportCem (β βloc L Cub : ℝ) (hL : 0 ≤ L) (hCub : 1 ≤ Cub) :
    1 ≤ periodicRieszTransportCem β βloc L Cub := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  unfold periodicRieszTransportCem
  split_ifs with h
  · linarith
  · have h1 : (1 : ℝ) ≤ Real.sqrt (Real.exp 1 + L) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (Real.exp 1 + L) := Real.sqrt_le_sqrt (by linarith)
    have h2 : (1 : ℝ) ≤ Real.sqrt Cub := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt Cub := Real.sqrt_le_sqrt hCub
    nlinarith [h1, h2]

/-- Printed `C_em` of Remark A.1 including the Jensen factor `e^{-β I}` for `β > β_loc`. -/
def periodicRieszPrintedCem (β βloc L Cub I : ℝ) : ℝ :=
  if β ≤ βloc then Real.exp 1 + L
  else Real.exp (-(β * I)) * (Real.sqrt (Real.exp 1 + L) * Real.sqrt Cub)

lemma periodicRieszSingularPartition_toReal_eq (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    (periodicRieszSingularPartition s β hs2 ρ N).toReal =
      ∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  rw [periodicRieszSingularPartition_eq_integral s β hs hβ hs2 ρ M hM hρ N,
    ENNReal.toReal_ofReal (by
      unfold periodicRieszSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)]
  exact periodicRieszSourcePartition_eq_particle s β hs hs2 ρ M hρ N hN

/-- Jensen lower bound `e^{β I_μ} ≤ K_{N,β}` (TeX eq. KlowerJensen). -/
lemma periodicRieszJensen_lower_integral (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (β * DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) ≤
    ∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  have hrate := periodicRieszSingularPartition_original_rate_full s β hs hβ hs2 ρ M hM hρ
  obtain ⟨-, -, -, κ, eig, e, -, -, -, -, -, -, C', -, hr⟩ := hrate
  have hJ := (hr N hN).2.1
  rw [periodicRieszSingularPartition_toReal_eq s β hs hβ hs2 ρ M hM hρ N hN] at hJ
  exact hJ

/-- Unnormalized all-temperature numerator with the printed constant. -/
theorem periodicRieszTransport_numerator_explicit (s M : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β) (Cub : ℝ)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hpart : periodicRieszLocalBeta s hs2 M < β → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ
        (2 * β - periodicRieszLocalBeta s hs2 M) N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszParticleExponent s ρ (2 * β - periodicRieszLocalBeta s hs2 M) N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cub) :
    ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤
        periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M) glzUniversalTailConstant Cub := by
  have hloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  intro σ hσ N hN
  by_cases hsmall : β ≤ periodicRieszLocalBeta s hs2 M
  · have he : periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N =
        periodicRieszNumeratorExponent s n β σ K v ρ N := by
      funext ω
      simp only [periodicRieszTransportAllBetaExponent, periodicRieszTransportEpsilon, ite_eq_left hsmall]
      rfl
    have hc : periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M) glzUniversalTailConstant Cub =
        Real.exp 1 + glzUniversalTailConstant := by
      unfold periodicRieszTransportCem
      exact ite_eq_left hsmall
    rw [he, hc]
    exact periodicRieszLocal_numerator s n hn hs hs2 β σ hβ hσ hv ρ M hM hρ N hN hsmall
  · have hlarge := lt_of_not_ge hsmall
    obtain ⟨hyi0, hyb0⟩ := hpart hlarge N hN
    have hn' : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN
    let X := fun ω : Fin N → PeriodicTorus ι =>
      periodicRieszNumeratorExponent s n (periodicRieszLocalBeta s hs2 M) σ K v ρ N ω / 2
    let Y := periodicRieszParticleExponent s ρ (β - periodicRieszLocalBeta s hs2 M / 2) N
    have hX : Measurable X :=
      (measurable_periodicRieszNumeratorExponent s hs hs2 n hn _ σ hv ρ N hn').div_const 2
    have hY : Measurable Y := measurable_periodicRieszParticleExponent s hs hs2 ρ _ N hn'
    have hXX (ω : Fin N → PeriodicTorus ι) : 2 * X ω =
        periodicRieszNumeratorExponent s n (periodicRieszLocalBeta s hs2 M) σ K v ρ N ω := by
      dsimp [X]; ring
    have hYY (ω : Fin N → PeriodicTorus ι) : 2 * Y ω =
        periodicRieszParticleExponent s ρ (2 * β - periodicRieszLocalBeta s hs2 M) N ω := by
      unfold Y periodicRieszParticleExponent
      ring
    have hx := periodicRieszLocal_numerator s n hn hs hs2 (periodicRieszLocalBeta s hs2 M) σ hloc hσ hv
      ρ M hM hρ N hN le_rfl
    have hxi : Integrable (fun ω => Real.exp (2 * X ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
      simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω => Real.exp (2 * Y ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
      simpa only [hYY] using hyi0
    obtain ⟨hi, hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N → PeriodicTorus ι) : X ω + Y ω =
        periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω :=
      (periodicRieszTransportAllBetaExponent_large s hs2 M n β σ K v ρ N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX, hYY] at hb
    have hc : periodicRieszTransportCem β (periodicRieszLocalBeta s hs2 M) glzUniversalTailConstant Cub =
        Real.sqrt (Real.exp 1 + glzUniversalTailConstant) * Real.sqrt Cub := by
      unfold periodicRieszTransportCem
      exact ite_eq_right hsmall
    rw [hc]
    exact ⟨hi, hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2) (Real.sqrt_le_sqrt hyb0)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-- Gibbs moments, both signs, from a numerator bound `Cnum ≤ Cem * Zlow` and a partition lower
bound `Zlow ≤ K_{N,β}`; includes the zero Lipschitz constant. -/
theorem periodicRieszTransport_Gibbs_moment_of_numerator_lower (s M : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (Cnum Zlow Cem : ℝ) (hCem : 1 ≤ Cem) (hZpos : 0 < Zlow) (hdiv : Cnum ≤ Cem * Zlow)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hNum : ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cnum)
    (hZlow : ∀ N : ℕ, 1 ≤ N → Zlow ≤ (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) :
    ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (σ * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω)) (periodicRieszSingularGibbs s β hs2 ρ N) ∧
      (∫ ω, Real.exp (σ * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω) ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ Cem := by
  intro σ hσ N hN
  obtain ⟨Cp, hCp, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hp := hPart N hN
  by_cases hk : K = 0
  · have hv0 : LipschitzWith 0 v := by simpa only [hk] using hv
    haveI := periodicRieszSingularGibbs_probability s β hs hβ.le hs2 ρ M hM hρ N
    simp only [periodicRieszTransportEnergy_eq_zero s n hn hv0, mul_zero, Real.exp_zero]
    exact ⟨integrable_const 1, by simpa using hCem⟩
  · simp only [periodicRieszPositiveTransportParameter, ite_eq_right hk]
    have hi := hNum σ hσ N hN
    rw [periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN]
    let A := fun ω : Fin N → PeriodicTorus ι => σ * periodicRieszTransportEpsilon s hs2 M n K β * (N : ℝ) *
      periodicRieszTransportEnergy s n v ρ N ω
    have hSum (ω : Fin N → PeriodicTorus ι) :
        periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω =
          periodicRieszParticleExponent s ρ β N ω + A ω := by
      dsimp [periodicRieszTransportAllBetaExponent, A]
      ring
    have ht : Integrable (fun ω => Real.exp (A ω))
        ((Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
          (periodicRieszParticleExponent s ρ β N)) := by
      apply (integrable_tilted_iff hp.1 _).mpr
      apply hi.1.congr
      exact ae_of_all _ fun ω => by
        change Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω) =
          Real.exp (periodicRieszParticleExponent s ρ β N ω) * Real.exp (A ω)
        rw [hSum, Real.exp_add]
    refine ⟨ht, ?_⟩
    change (∫ ω, Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
      (periodicRieszParticleExponent s ρ β N)) ≤ Cem
    rw [integral_exp_tilted]
    change (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω + A ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) /
      (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cem
    simp_rw [← hSum]
    have hdpos : 0 < (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
      lt_of_lt_of_le hZpos (hZlow N hN)
    apply (div_le_iff₀ hdpos).mpr
    exact hi.2.trans (hdiv.trans (mul_le_mul_of_nonneg_left (hZlow N hN) (by linarith)))

/-- Finite-relative-entropy estimate (2.22) from the Gibbs exponential moments of both signs
(bounded by `Cem`) and a partition cap `Cpf`. -/
theorem periodicRieszTransport_finiteKL_entropic_of_moments (s M : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (Cpf Cem : ℝ) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hMom : ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (σ * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω)) (periodicRieszSingularGibbs s β hs2 ρ N) ∧
      (∫ ω, Real.exp (σ * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω) ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ Cem)
    (hZ : ∀ N : ℕ, 1 ≤ N → (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cpf)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞) :
    ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) ∧
    Integrable (periodicRieszTransportBackgroundEnergy s ρ N) ν ∧
    Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν ∧
    Integrable (fun ω => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω) ν ∧
    |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω ∂ν| ≤
      (β / periodicRieszPositiveTransportParameter s hs2 M n K β) * (N : ℝ) *
        periodicRieszTransportProperFreeEnergy s ρ β N ν +
      (periodicRieszPositiveTransportParameter s hs2 M n K β)⁻¹ * (Real.log Cpf + Real.log Cem) := by
  obtain ⟨Cp, hCp, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  let P := Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)
  let Ebg := periodicRieszTransportBackgroundEnergy s ρ N
  let a := fun ω : Fin N → PeriodicTorus ι => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω
  let ε := periodicRieszPositiveTransportParameter s hs2 M n K β
  have hε : 0 < ε := periodicRieszPositiveTransportParameter_pos s hs hs2 M hM n K β hβ
  have hQ : periodicRieszSingularGibbs s β hs2 ρ N = P.tilted (fun ω => -β * Ebg ω) := by
    rw [periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN]
    congr 1
    funext ω
    exact periodicRieszParticleExponent_background s ρ β N ω
  have hp := hMom 1 (by norm_num) N hN
  have hm := hMom (-1) (by norm_num) N hN
  rw [hQ] at hp hm hKL
  have heP (ω : Fin N → PeriodicTorus ι) :
      1 * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω = ε * a ω := by dsimp [ε, a]; ring
  have heM (ω : Fin N → PeriodicTorus ι) :
      (-1) * periodicRieszPositiveTransportParameter s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω = -(ε * a ω) := by dsimp [ε, a]; ring
  simp_rw [heP] at hp
  simp_rw [heM] at hm
  have hz : Integrable (fun ω => Real.exp (-β * Ebg ω)) P := by
    simpa only [periodicRieszParticleExponent_background] using (hPart N hN).1
  have hzb : (∫ ω, Real.exp (-β * Ebg ω) ∂P) ≤ Cpf := by
    simpa only [periodicRieszParticleExponent_background] using hZ N hN
  obtain ⟨hac, he, hllr, ha, hb⟩ := DGRHS.Entropy.gibbs_entropic_transfer P ν Ebg
    (-(N : ℝ) * periodicRieszBgConst s hs2 M) β hβ
    (periodicRieszTransportBackgroundEnergy_lower s hs hs2 M hM ρ hρ N hN) hz a
    (measurable_periodicRieszScaledTransportEnergy s n hn hs hs2 hv ρ N hN).stronglyMeasurable ε hε
    hp.1 hm.1 hKL Cpf Cem hzb hp.2 hm.2
  refine ⟨hac, he, hllr, ha, ?_⟩
  have hNreal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have halgebra : (β / ε) * (N : ℝ) * periodicRieszTransportProperFreeEnergy s ρ β N ν =
      ε⁻¹ * ((klDiv ν P).toReal + β * (∫ ω, Ebg ω ∂ν)) := by
    unfold periodicRieszTransportProperFreeEnergy
    dsimp only [P, Ebg]
    field_simp [hβ.ne', hε.ne', hNreal]
  rw [halgebra]
  exact hb

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszJensen_lower_integral
#print axioms DGRHS.Periodic.periodicRieszTransport_numerator_explicit
#print axioms DGRHS.Periodic.periodicRieszTransport_Gibbs_moment_of_numerator_lower
#print axioms DGRHS.Periodic.periodicRieszTransport_finiteKL_entropic_of_moments
