import DGRHS.Gaussian.PeriodicDynamicBase
import DGRHS.Gaussian.PeriodicLogEntropicCommutator

/-!
Packet P11c, unit 2 (LOG, part 1): family-uniform Gibbs moments of the torus LOG transport energy.

The P9h export `exists_periodicLog_entropic_commutator` chooses its local threshold `β_loc` after the
background density `ρ` (through the particle-weight cap of `ρ`).  Lemma 8.1(ii) needs the constants for
the whole family `{μ^t}` simultaneously.  The printed Theorem 2.13(ii) supplies the uniform partition
bounds `K_{N,β}(μ^t) ≤ C_{β,T}` and `K_{N,2β}(μ^t) ≤ C_{2β,T}` (TeX 877-881); here the local numerator is
re-run with the cap `Cpart ≥ K_{N,β}(ρ)` as an explicit hypothesis, so that the threshold
`periodicLogFamilyBeta β Cpart` and the transport parameter depend only on `(β, Cpart, Csr, K, n)`,
and the Gibbs moments are bounded by a constant that depends only on `(β, C₂)` (`I_μ ≥ -J₀` is a
torus identity: the smooth LOG kernel is bounded below, `periodicLogInteraction_lower`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The family threshold of the local LOG numerator: independent of the density. -/
def periodicLogFamilyBeta (β Cp : ℝ) : ℝ :=
  min (β / 6) (min (1 / 6) (min (1 / (16 * DGRHS.Attractive.attractiveMomentConstant))
    (β / (6 * (Cp + 1)))))

lemma periodicLogFamilyBeta_pos {β Cp : ℝ} (hβ : 0 < β) (hCp : 0 < Cp) :
    0 < periodicLogFamilyBeta β Cp := by
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  unfold periodicLogFamilyBeta
  exact lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))

lemma periodicLogFamilyBeta_lt {β Cp : ℝ} (hβ : 0 < β) (hCp : 0 < Cp) :
    periodicLogFamilyBeta β Cp < β := by
  unfold periodicLogFamilyBeta
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- Local numerator bounded by `e` for `γ ≤ periodicLogFamilyBeta β0 Cp`, with the cap `Cp` for the
weight at temperature `β0` as an explicit hypothesis. -/
theorem periodicLog_capped_local_numerator (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v → 0 < (K : ℝ) →
      ∀ (β0 Cp : ℝ), 0 < β0 → 0 < Cp →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ β0 N ω))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ ω, Real.exp (periodicLogParticleExponent ρ β0 N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cp) →
      ∀ γ : ℝ, 0 ≤ γ → γ ≤ periodicLogFamilyBeta β0 Cp → ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
        Integrable (fun x => Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x))
          (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
        (∫ x, Real.exp (periodicLogParticleExponent ρ γ N x +
          (σ * (γ / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Real.exp 1 := by
  obtain ⟨C, hC, hb⟩ := periodicLogTransportKernel_bound (ι := ι) n hn
  refine ⟨C + 1, by linarith, ?_⟩
  intro K v hv hK β0 Cp hβ0 hCp ρ hprob hcap γ hγ hγloc σ hσ N hN
  let μ := periodicCappedDensityMeasure ρ
  have hA := DGRHS.Attractive.attractiveMomentConstant_pos
  have hγβ : γ ≤ β0 / 6 := hγloc.trans (min_le_left _ _)
  have hγ6 : γ ≤ 1 / 6 := hγloc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγq : γ ≤ 1 / (16 * DGRHS.Attractive.attractiveMomentConstant) :=
    hγloc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hγp : γ ≤ β0 / (6 * (Cp + 1)) :=
    hγloc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
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
  obtain ⟨hr, hrC⟩ := hcap N hN
  -- the repulsive exponent at temperature `2 γ` by interpolation from temperature `β0`
  let Eb := fun x : Fin N → PeriodicTorus ι => -periodicLogParticleExponent ρ β0 N x
  have hr' : Integrable (fun x => Real.exp (-Eb x)) (Measure.pi (fun _ : Fin N => μ)) := by
    simpa [Eb] using hr
  have hrb' : (∫ x, Real.exp (-Eb x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    simpa [Eb] using hrC
  have hγ'0 : 0 ≤ γ / β0 := div_nonneg hγ hβ0.le
  have hγ'6 : γ / β0 ≤ 1 / 6 := by
    rw [div_le_iff₀ hβ0]
    linarith
  have hγ'p : γ / β0 ≤ 1 / (6 * (Cp + 1)) := by
    rw [div_le_iff₀ hβ0]
    have h6 : 0 < 6 * (Cp + 1) := by positivity
    have := (le_div_iff₀ h6).mp hγp
    calc γ ≤ β0 / (6 * (Cp + 1)) := hγp
      _ = 1 / (6 * (Cp + 1)) * β0 := by field_simp
  obtain ⟨hri, hrbi⟩ := local_repulsive_interpolation
    (Measure.pi (fun _ : Fin N => μ)) Eb Cp (γ / β0) hCp hr' hrb' hγ'0 hγ'6 hγ'p
  let X := fun x => periodicLogParticleExponent ρ γ N x
  let Y := fun x : Fin N → PeriodicTorus ι =>
    t * (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x
  have hXE (x : Fin N → PeriodicTorus ι) : 2 * X x = -2 * (γ / β0) * Eb x := by
    dsimp only [X, Eb]
    rw [periodicLog_u_eq ρ γ N x, periodicLog_u_eq ρ β0 N x]
    field_simp
  have hx : Integrable (fun x => Real.exp (2 * X x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hri.congr (ae_of_all _ fun x => ?_)
    show Real.exp (-2 * (γ / β0) * Eb x) = Real.exp (2 * X x)
    rw [hXE x]
  have hy : Integrable (fun x => Real.exp (2 * Y x)) (Measure.pi (fun _ : Fin N => μ)) := by
    refine hc.congr (ae_of_all _ fun x => ?_)
    dsimp only [Y]
    congr 1; ring
  obtain ⟨hi, hib⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hx)
    (aemeasurable_of_exp_double_integrable _ Y hy) hx hy
  have hxb : (∫ x, Real.exp (2 * X x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ 4 / 3 := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun x => ?_))) hrbi
    show Real.exp (2 * X x) = Real.exp (-2 * (γ / β0) * Eb x)
    rw [hXE x]
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

/-- Family-uniform lower bound of the interaction energy of the torus LOG kernel. -/
lemma periodicLog_interaction_ge (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    -(periodicLogPairLower ι / 2) ≤ DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) := by
  rw [periodicLogInteraction_eq ρ M hρ]
  exact periodicLogInteraction_lower ρ

/-- The Gibbs partition of the torus LOG gas is bounded below by `e^{-β J₀}`, `J₀ = pairLower/2`. -/
lemma periodicLog_partition_ge (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    Real.exp (-(β * (periodicLogPairLower ι / 2))) ≤
      ∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  obtain ⟨_, _, hP⟩ := periodicLogParticleWeight_uniform β hβ ρ M hM hρ
  refine le_trans (Real.exp_le_exp.mpr ?_) (hP N hN).2.1
  have := periodicLog_interaction_ge ρ M hρ
  nlinarith

/-- The doubled-partition constant from the printed bound `K_{N,2β} ≤ C₂`: for `0 ≤ γ ≤ 2β` the
partition integral at temperature `γ` is at most `1 + max C₂ 0`. -/
lemma periodicLog_partition_interp (β γ C₂ : ℝ) (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2 * β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N)
    (hC₂ : (periodicLogSingularPartition (2 * β) ρ N).toReal ≤ C₂) :
    Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ γ N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
    (∫ ω, Real.exp (periodicLogParticleExponent ρ γ N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ 1 + max C₂ 0 := by
  have hn' : 0 < N := by omega
  obtain ⟨_, _, hP₂⟩ := periodicLogParticleWeight_uniform (2 * β) (by positivity) ρ M hM hρ
  have hpt (ω : Fin N → PeriodicTorus ι) :
      Real.exp (periodicLogParticleExponent ρ γ N ω) ≤
        1 + Real.exp (periodicLogParticleExponent ρ (2 * β) N ω) := by
    rw [periodicLogParticleExponent_background, periodicLogParticleExponent_background]
    have h := exp_mul_le_one_add_exp_mul (a := γ) (b := 2 * β) hγ0 hγ
      (-(periodicLogTransportBackgroundEnergy ρ N ω))
    simpa only [mul_neg, neg_mul] using h
  have hint : Integrable (fun ω => 1 + Real.exp (periodicLogParticleExponent ρ (2 * β) N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
    (integrable_const 1).add (hP₂ N hN).1
  have hmeas := measurable_periodicLogParticleExponent ρ γ N hn'
  have hi : Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ γ N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
    hint.mono' (Real.measurable_exp.comp hmeas).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpt ω)
  refine ⟨hi, ?_⟩
  have h2 : (∫ ω, Real.exp (periodicLogParticleExponent ρ (2 * β) N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C₂ := by
    rwa [periodicLogSingularPartition_toReal_eq (2 * β) (by positivity) ρ M hM hρ N hN] at hC₂
  calc _ ≤ ∫ ω, (1 + Real.exp (periodicLogParticleExponent ρ (2 * β) N ω))
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) :=
        integral_mono hi hint hpt
    _ = 1 + ∫ ω, Real.exp (periodicLogParticleExponent ρ (2 * β) N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
        rw [integral_add (integrable_const 1) (hP₂ N hN).1]
        simp
    _ ≤ 1 + max C₂ 0 := by linarith [le_max_left C₂ 0]

/-- Family-uniform Gibbs moments of the torus LOG transport energy. -/
theorem periodicLog_capped_gibbs_moments (n : ℕ) (hn : 1 ≤ n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v → 0 < (K : ℝ) →
      ∀ (β Cpart C₂ M : ℝ), 0 < β → 0 < Cpart → 0 ≤ M →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition β ρ N).toReal ≤ Cpart) →
      (∀ N : ℕ, 1 ≤ N → (periodicLogSingularPartition (2 * β) ρ N).toReal ≤ C₂) →
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (σ * (periodicLogFamilyBeta β Cpart / (8 * Csr * (K : ℝ) ^ n)) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x))) (periodicLogSingularGibbs β ρ N) ∧
        (∫ x, Real.exp (σ * (periodicLogFamilyBeta β Cpart / (8 * Csr * (K : ℝ) ^ n)) *
          ((N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
            (periodicLogTransportKernel n v) N x)) ∂periodicLogSingularGibbs β ρ N) ≤
          Real.exp (β * (periodicLogPairLower ι / 2)) *
            (Real.sqrt (Real.exp 1) * Real.sqrt (1 + max C₂ 0)) := by
  obtain ⟨Csr, hC, hlocal⟩ := periodicLog_capped_local_numerator (ι := ι) n hn
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK β Cpart C₂ M hβ hCpart hM ρ hprob hρ hcap hC₂ σ hσ N hN
  let μ := periodicCappedDensityMeasure ρ
  let βloc := periodicLogFamilyBeta β Cpart
  have hloc : 0 < βloc := periodicLogFamilyBeta_pos hβ hCpart
  have hlt : βloc < β := periodicLogFamilyBeta_lt hβ hCpart
  obtain ⟨Cp, hCp, hrep⟩ := periodicLogParticleWeight_uniform β hβ.le ρ M hM hρ
  have hcap' : ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ β N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ Cpart := by
    intro N' hN'
    refine ⟨(hrep N' hN').1, ?_⟩
    have := hcap N' hN'
    rwa [periodicLogSingularPartition_toReal_eq β hβ.le ρ M hM hρ N' hN'] at this
  have hnum := hlocal hv hK β Cpart hβ hCpart ρ hcap'
  obtain ⟨hi, hb⟩ := hnum βloc hloc.le le_rfl σ hσ N (by omega)
  obtain ⟨hui, -, -⟩ := hrep N hN
  obtain ⟨hu2, hu2b⟩ := periodicLog_partition_interp β (2 * β - βloc) C₂ hβ (by linarith)
    (by linarith) ρ M hM hρ N hN (hC₂ N hN)
  have hz := periodicLog_partition_ge β hβ.le ρ M hM hρ N hN
  rw [periodicLogSingularGibbs_eq_particle β hβ.le ρ M hM hρ N hN]
  have hε : periodicLogFamilyBeta β Cpart / (8 * Csr * (K : ℝ) ^ n) = βloc / (8 * Csr * (K : ℝ) ^ n) :=
    rfl
  obtain ⟨hq, hqb⟩ := gibbs_moment_holder
    (Measure.pi (fun _ : Fin N => μ)) (periodicLogParticleExponent ρ β N)
    (periodicLogParticleExponent ρ βloc N) (periodicLogParticleExponent ρ (2 * β - βloc) N)
    (fun x => (σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x)
    (fun x => by unfold periodicLogParticleExponent; ring) hui hi (Real.exp 1) hb hu2
    (1 + max C₂ 0) hu2b (Real.exp (-(β * (periodicLogPairLower ι / 2)))) (Real.exp_pos _) hz
  have hfun : (fun x : Fin N → PeriodicTorus ι => Real.exp (σ *
      (periodicLogFamilyBeta β Cpart / (8 * Csr * (K : ℝ) ^ n)) *
        ((N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x))) =
      fun x => Real.exp (((σ * (βloc / (4 * Csr * (K : ℝ) ^ n))) * periodicLogA ρ n v N x) / 2) := by
    funext x
    rw [hε]
    congr 1
    simp only [periodicLogA]
    ring
  rw [hfun]
  refine ⟨hq, hqb.trans (le_of_eq ?_)⟩
  rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_capped_local_numerator
#print axioms DGRHS.Periodic.periodicLog_partition_ge
#print axioms DGRHS.Periodic.periodicLog_partition_interp
#print axioms DGRHS.Periodic.periodicLog_capped_gibbs_moments
