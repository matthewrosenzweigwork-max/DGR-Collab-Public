import DGRHS.Gaussian.PeriodicLogCommon

/-!
Packet P11a, unit 3 (LOG, part 2): the family (common-constant) form of the torus LOG entropic
commutator of Theorem 2.8, torus version of `exists_log_transport_family_local_numerator`,
`exists_log_transport_family_gibbs_moments` and `exists_log_transport_family_entropic_commutator`.

All constants (`C_sr`, `β_loc`, `C_ub`, `C_pf`, `C_em`) are chosen before the Lipschitz field, the
background density, the particle number and the competitor; they depend only on `(n, K, M, β)` and
the dimension.  The lower bound `I_μ ≥ -J₀` of the interaction energy is the universal torus constant
`J₀ = periodicLogPairLower / 2` (`periodicLogInteraction_lower`), so no control of `I_μ` is needed
(the Euclidean family carries it as the parameter `J`).
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Local numerator on the torus, LOG kernel, with `β_loc` chosen before the density. -/
theorem periodicLog_family_local_numerator (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) → ∀ M : ℝ, 0 ≤ M →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ βloc → ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
        Integrable (fun x => Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ x, Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Real.exp 1 := by
  obtain ⟨C, hC, hb⟩ := periodicLogTransportKernel_bound (ι := ι) n hn
  refine ⟨C + 1, by linarith, ?_⟩
  intro K hK M hM
  obtain ⟨Cp, hCp, hrep⟩ := periodicLogCommon_particle_cap (ι := ι) 1 zero_le_one M hM
  let βloc := min (1 / 6 : ℝ) (min (1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (1 / (6 * (Cp + 1))))
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hloc : 0 < βloc := by
    dsimp [βloc]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨βloc, hloc, ?_⟩
  intro v hv ρ hprob hρ γ hγ hγloc σ hσ N hN
  let μ := periodicCappedDensityMeasure ρ
  have hγ6 : γ ≤ 1 / 6 := hγloc.trans (min_le_left _ _)
  have hγq : γ ≤ 1 / (16 * DGRHS.Attractive.attractiveMomentConstant) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγp : γ ≤ 1 / (6 * (Cp + 1)) :=
    hγloc.trans ((min_le_right _ _).trans (min_le_right _ _))
  let t := σ * (γ / (4 * (C + 1) * (K : ℝ) ^ n))
  have hscalar := local_log_transport_scalar C ((K : ℝ) ^ n) γ σ hC.le (pow_pos hK n) hγ hγ6 hγq hσ
  have hL : 0 ≤ C * (K : ℝ) ^ n := by positivity
  have hkm := periodicLogTransportKernel_measurable (ι := ι) n hv
  have hks : ∀ a b, periodicLogTransportKernel n v (a, b) = periodicLogTransportKernel n v (b, a) :=
    fun a b => (periodicLogTransportKernel_symm n v (a, b)).symm
  have ht2 : |2 * t| * (DGRHS.Attractive.attractiveMomentConstant * (4 * (C * (K : ℝ) ^ n))) < 1 := by
    have := hscalar.1
    simpa [t, mul_assoc] using this
  obtain ⟨hc, hcb⟩ := boundedKernel_energy_exponential μ (periodicLogTransportKernel n v) hkm hks
    (C * (K : ℝ) ^ n) hL (hb hv) (2 * t) ht2 N hN
  have hcBound : (∫ x : Fin N → PeriodicTorus ι,
      Real.exp ((2 * t) * (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤ (128 / 63 : ℝ) * Real.exp (1 / 4) := by
    refine hcb.trans ?_
    have := hscalar.2
    simpa [t, mul_assoc] using this
  obtain ⟨hr, hrC⟩ := hrep ρ hρ N hN
  -- the repulsive exponent at temperature `2 γ` by interpolation
  let Eb := fun x : Fin N → PeriodicTorus ι => -periodicLogParticleExponent ρ 1 N x
  have hr' : Integrable (fun x => Real.exp (-Eb x)) (Measure.pi (fun _ : Fin N => μ)) := by
    simpa [Eb] using hr
  have hrb' : (∫ x, Real.exp (-Eb x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    simpa [Eb] using hrC
  obtain ⟨hri, hrbi⟩ := local_repulsive_interpolation
    (Measure.pi (fun _ : Fin N => μ)) Eb Cp γ hCp hr' hrb' hγ hγ6 hγp
  let X := fun x => periodicLogParticleExponent ρ γ N x
  let Y := fun x : Fin N → PeriodicTorus ι =>
    t * (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x
  have hx : Integrable (fun x => Real.exp (2 * X x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hri.congr (ae_of_all _ fun x => ?_)
    dsimp only [X, Eb]
    rw [periodicLog_u_eq ρ γ N x]
    congr 1; ring
  have hy : Integrable (fun x => Real.exp (2 * Y x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hc.congr (ae_of_all _ fun x => ?_)
    dsimp only [Y]
    congr 1; ring
  obtain ⟨hi, hib⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hx)
    (aemeasurable_of_exp_double_integrable _ Y hy) hx hy
  have hxb : (∫ x, Real.exp (2 * X x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ 4 / 3 := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hrbi
    dsimp only [X, Eb]
    rw [periodicLog_u_eq ρ γ N x]
    congr 1; ring
  have hyb : (∫ x, Real.exp (2 * Y x) ∂Measure.pi (fun _ : Fin N => μ)) ≤
      (128 / 63 : ℝ) * Real.exp (1 / 4) := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hcBound
    dsimp only [Y]
    congr 1; ring
  have he : (fun x => Real.exp (X x + Y x)) = fun x => Real.exp (periodicLogParticleExponent ρ γ N x +
      (σ * (γ / (4 * (C + 1) * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) := by
    funext x
    congr 1
    dsimp only [X, Y, t, periodicLogA]
    ring
  rw [he] at hi hib
  exact ⟨hi, hib.trans ((mul_le_mul (Real.sqrt_le_sqrt hxb) (Real.sqrt_le_sqrt hyb)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans local_log_transport_cs_constant)⟩



/-- Gibbs exponential moments on the torus, LOG kernel, with all constants chosen before the density. -/
theorem periodicLog_family_gibbs_moments (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) → ∀ M : ℝ, 0 ≤ M →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc (-(periodicLogPairLower ι / 2))
        glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
        (periodicLogSingularPartition (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition (β : ℝ) ρ N).toReal ≤ Cpf) ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x))) (periodicLogSingularGibbs (β : ℝ) ρ N) ∧
        (∫ x, Real.exp (σ * sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x)) ∂periodicLogSingularGibbs (β : ℝ) ρ N) ≤
          sourceLogTransportCem (β : ℝ) βloc (-(periodicLogPairLower ι / 2))
            glzUniversalTailConstant Cub := by
  obtain ⟨Csr, hC, hlocal⟩ := periodicLog_family_local_numerator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K hK M hM
  obtain ⟨βloc, hloc, hnum⟩ := hlocal K hK M hM
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  have hβ' : 0 < (β : ℝ) := hβ
  set J0 := periodicLogPairLower ι / 2 with hJ0
  have hJ0n : 0 ≤ J0 := by
    have := periodicLogPairLower_nonneg (ι := ι)
    rw [hJ0]; positivity
  let L := glzUniversalTailConstant
  have hL : 0 ≤ L := glzUniversalTailConstant_pos.le
  have hKn : 0 < (K : ℝ) ^ n := pow_pos hK n
  obtain ⟨C, hCpos, hcap⟩ := periodicLogCommon_particle_cap (ι := ι) (β : ℝ) β.coe_nonneg M hM
  obtain ⟨Cub, hCub, hCubfam⟩ : ∃ Cub : ℝ, 1 ≤ Cub ∧
      (βloc < (β : ℝ) → ∀ (ρ : PeriodicTorus ι → ℝ)
        [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
        (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ (2 * (β : ℝ) - βloc) N ω))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ ω, Real.exp (periodicLogParticleExponent ρ (2 * (β : ℝ) - βloc) N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cub) := by
    by_cases hlarge : βloc < (β : ℝ)
    · obtain ⟨Cp1, hCp1, hP1⟩ := periodicLogCommon_particle_cap (ι := ι) (2 * (β : ℝ) - βloc)
        (by linarith [β.coe_nonneg]) M hM
      refine ⟨max Cp1 1, le_max_right _ _, fun _ ρ hprob hρ N hN => ?_⟩
      have h := hP1 ρ hρ N hN
      exact ⟨h.1, h.2.trans (le_max_left _ _)⟩
    · exact ⟨1, le_rfl, fun h => absurd h hlarge⟩
  set Cpf := max (max C 1) (Real.exp (-(β : ℝ) * J0)) with hCpfdef
  have hCpf : 1 ≤ Cpf := (le_max_right C 1).trans (le_max_left _ _)
  have hforcingLower : Real.exp (-(β : ℝ) * J0) ≤ Cpf := le_max_right _ _
  have hε : 0 < sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) :=
    sourceLogTransportEpsilon_pos _ _ _ _ hβ' hloc hC hKn
  have hCem : 0 < sourceLogTransportCem (β : ℝ) βloc (-J0) L Cub :=
    sourceLogTransportCem_pos _ _ _ _ _ hL hCub
  have hforcing : 0 ≤ Real.log Cpf + Real.log (sourceLogTransportCem (β : ℝ) βloc (-J0) L Cub) := by
    dsimp only [sourceLogTransportCem]
    split_ifs
    · simpa only [neg_mul, mul_neg, neg_neg] using
        log_small_Cem_forcing_nonnegative (-(β : ℝ) * J0) Cpf L hforcingLower hL
    · simpa only [neg_mul, mul_neg, neg_neg] using
        log_large_Cem_forcing_nonnegative (-(β : ℝ) * J0) Cpf L Cub hforcingLower hL hCub
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, ?_⟩
  intro v hv ρ hprob hρ
  refine ⟨fun N hN hlarge => ?_, fun N hN => ?_, ?_⟩
  · rw [periodicLogSingularPartition_toReal_eq (2 * (β : ℝ) - βloc) (by linarith [β.coe_nonneg])
      ρ M hM hρ N hN]
    exact (hCubfam hlarge ρ hρ N hN).2
  · rw [periodicLogSingularPartition_toReal_eq (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    exact (hcap ρ hρ N hN).2.trans ((le_max_left C 1).trans (le_max_left _ _))
  intro σ hσ N hN
  let μ := periodicCappedDensityMeasure ρ
  let I := DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
  have hIlow : -J0 ≤ I := by
    have h1 := periodicLogInteraction_lower ρ
    have h2 := periodicLogInteraction_eq ρ M hρ
    change -J0 ≤ DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
    rw [h2]
    exact h1
  have hz0 : Real.exp (-(β : ℝ) * J0) ≤ Real.exp ((β : ℝ) * I) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hpre : Real.exp (-(β : ℝ) * I) ≤ Real.exp ((β : ℝ) * J0) :=
    Real.exp_le_exp.mpr (by nlinarith)
  by_cases hsmall : (β : ℝ) ≤ βloc
  · obtain ⟨Cp', -, hrep'⟩ := periodicLogParticleWeight_uniform (β : ℝ) β.coe_nonneg ρ M hM hρ
    obtain ⟨-, hz, -⟩ := hrep' N hN
    obtain ⟨hui, -⟩ := hcap ρ hρ N hN
    obtain ⟨hi, hb⟩ := hnum hv ρ hρ (β : ℝ) β.coe_nonneg hsmall σ hσ N (by omega)
    rw [periodicLogSingularGibbs_eq_particle (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    have hε' : sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) =
        (β : ℝ) / (4 * Csr * (K : ℝ) ^ n) := by
      unfold sourceLogTransportEpsilon
      rw [ite_eq_left hsmall]
    obtain ⟨hq, hqb⟩ := gibbs_moment_of_numerator
      (Measure.pi (fun _ : Fin N => μ)) (periodicLogParticleExponent ρ (β : ℝ) N)
      (fun x => (σ * ((β : ℝ) / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) hui
      (Real.exp (-(β : ℝ) * J0)) (Real.exp 1) (Real.exp_pos _) (hz0.trans hz) hi hb
    have hfun : (fun x : Fin N → PeriodicTorus ι => Real.exp (σ *
        sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x))) =
        fun x => Real.exp ((σ * ((β : ℝ) / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) := by
      funext x
      rw [hε']
    rw [hfun]
    refine ⟨hq, ?_⟩
    have hr : Real.exp 1 / Real.exp (-(β : ℝ) * J0) = Real.exp ((β : ℝ) * J0) * Real.exp 1 := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring_nf
    calc _ ≤ Real.exp 1 / Real.exp (-(β : ℝ) * J0) := hqb
      _ = Real.exp ((β : ℝ) * J0) * Real.exp 1 := hr
      _ ≤ Real.exp ((β : ℝ) * J0) * (Real.exp 1 + L) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = _ := by
        unfold sourceLogTransportCem
        rw [ite_eq_left hsmall]
        simp only [neg_mul, mul_neg, neg_neg]
        rfl
  · have hlarge : βloc < (β : ℝ) := lt_of_not_ge hsmall
    obtain ⟨hu2, hu2b⟩ := hCubfam hlarge ρ hρ N hN
    obtain ⟨hui, -⟩ := hcap ρ hρ N hN
    obtain ⟨Cp', -, hrep'⟩ := periodicLogParticleWeight_uniform (β : ℝ) β.coe_nonneg ρ M hM hρ
    obtain ⟨-, hz, -⟩ := hrep' N hN
    obtain ⟨hi, hb⟩ := hnum hv ρ hρ βloc hloc.le le_rfl σ hσ N (by omega)
    rw [periodicLogSingularGibbs_eq_particle (β : ℝ) β.coe_nonneg ρ M hM hρ N hN]
    have hε' : sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) =
        βloc / (8 * Csr * (K : ℝ) ^ n) := by
      unfold sourceLogTransportEpsilon
      rw [ite_eq_right hsmall]
    obtain ⟨hq, hqb⟩ := gibbs_moment_holder
      (Measure.pi (fun _ : Fin N => μ)) (periodicLogParticleExponent ρ (β : ℝ) N)
      (periodicLogParticleExponent ρ βloc N) (periodicLogParticleExponent ρ (2 * (β : ℝ) - βloc) N)
      (fun x => (σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
      (fun x => by unfold periodicLogParticleExponent; ring) hui hi (Real.exp 1) hb hu2
      Cub hu2b (Real.exp (-(β : ℝ) * J0)) (Real.exp_pos _) (hz0.trans hz)
    have hfun : (fun x : Fin N → PeriodicTorus ι => Real.exp (σ *
        sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) *
          ((N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x))) =
        fun x => Real.exp (((σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) / 2) := by
      funext x
      rw [hε']
      congr 1
      simp only [periodicLogA]
      ring
    rw [hfun]
    refine ⟨hq, ?_⟩
    refine hqb.trans ?_
    have hI : Real.sqrt (Real.exp 1) * Real.sqrt Cub / Real.exp (-(β : ℝ) * J0) =
        Real.exp ((β : ℝ) * J0) * Real.sqrt (Real.exp 1) * Real.sqrt Cub := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring_nf
    rw [hI]
    unfold sourceLogTransportCem
    rw [ite_eq_right hsmall]
    simp only [neg_mul, mul_neg, neg_neg]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.exp_pos _).le)
      (Real.sqrt_nonneg _)


/-- Theorem 2.8 on the torus, LOG kernel, family form: all constants before the Lipschitz field, the
density, the particle number and the competitor. -/
theorem exists_periodicLog_family_entropic_commutator (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ K : ℝ≥0, 0 < (K : ℝ) → ∀ M : ℝ, 0 ≤ M →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc (-(periodicLogPairLower ι / 2))
        glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicLogTransportKernel n v) N x ∂ν| : ℝ) : EReal) ≤
        (((β : ℝ) / ε * (N : ℝ) : ℝ) : EReal) *
            periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν +
          ((ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) : EReal) := by
  have hn1 : 1 ≤ n := hn
  obtain ⟨Csr, hC, hfactory⟩ := periodicLog_family_gibbs_moments (ι := ι) n hn1
  obtain ⟨CK, hCK, hbd⟩ := periodicLogTransportKernel_bound (ι := ι) n hn1
  refine ⟨Csr, hC, ?_⟩
  intro K hK M hM
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory K hK M hM
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  have hβ' : 0 < (β : ℝ) := hβ
  obtain ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, hfam⟩ := hβfactory β hβ
  refine ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, ?_⟩
  intro v hv ρ hprob hρ N hN ν hν
  obtain ⟨-, hcapPf, hmom⟩ := hfam hv ρ hρ
  have hn' : 0 < N := by omega
  let μ := periodicCappedDensityMeasure ρ
  have hm := periodicLogTransportKernel_measurable (ι := ι) n hv
  have hsa : StronglyMeasurable (fun x : Fin N → PeriodicTorus ι => (N : ℝ) *
      sourceTransportEnergy μ (periodicLogTransportKernel n v) N x) :=
    (stronglyMeasurable_sourceTransportEnergy μ _ hm N).const_mul (N : ℝ)
  let A := (N : ℝ) * (4 * (CK * (K : ℝ) ^ n))
  have hA : ∀ x : Fin N → PeriodicTorus ι, |(N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x| ≤ A := by
    intro x
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    exact abs_sourceTransportEnergy_le μ _ hm _ (hbd hv)
      (fun a b => (periodicLogTransportKernel_symm n v (a, b)).symm)
      (fun a => by simp [periodicLogTransportKernel]) N hn' x
  have hp := hmom 1 (by norm_num) N hN
  have hmn := hmom (-1) (by norm_num) N hN
  have hp' : Integrable (fun x => Real.exp (sourceLogTransportEpsilon (β : ℝ) βloc Csr
      ((K : ℝ) ^ n) * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x))) (periodicLogSingularGibbs (β : ℝ) ρ N) := by
    simpa only [one_mul] using hp.1
  have hm' : Integrable (fun x => Real.exp (-(sourceLogTransportEpsilon (β : ℝ) βloc Csr
      ((K : ℝ) ^ n) * ((N : ℝ) * sourceTransportEnergy μ
      (periodicLogTransportKernel n v) N x)))) (periodicLogSingularGibbs (β : ℝ) ρ N) := by
    simpa only [neg_one_mul, neg_mul, one_mul] using hmn.1
  exact periodicLog_entropic_all_laws M hM (β : ℝ) hβ' ρ hρ N hN ν
    (fun x => (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x) hsa A hA
    _ hε hp' hm' Cpf _ (hcapPf N hN)
    (by simpa only [one_mul] using hp.2)
    (by simpa only [neg_one_mul, neg_mul, one_mul] using hmn.2)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_family_local_numerator
#print axioms DGRHS.Periodic.periodicLog_family_gibbs_moments
#print axioms DGRHS.Periodic.exists_periodicLog_family_entropic_commutator
