import DGRHS.Gaussian.PeriodicRieszEntropicCommutatorPrinted
import DGRHS.Gaussian.PeriodicLocalNumeratorExport
import DGRHS.Gaussian.PeriodicPairUnbounded

/-!
Packet P11a, unit 2 (Riesz): Corollary 7.3 (`cor:entropicCommutatorTemperatureInterpolation`,
TeX 3547-3579) on the flat torus (Remark 2.1, TeX 492-496), positive Riesz kernel `0 < s < d/2`,
finite-relative-entropy class (owner convention 1.2, as the torus Theorem 2.8 export), with the
pointwise commutator premise `eq:pointwiseCommutatorBound` required only on COLLISION-FREE
configurations (as the Euclidean export `sourceRieszCommon_thermal_minimum_source_collisionFree`).

The printed `F_N` is `+∞` on collisions, so the printed premise is vacuous there (for `C_pw > 0`);
a competitor of finite relative entropy is absolutely continuous with respect to the iid law, which
is concentrated on collision-free configurations (`periodic_iid_collision_free`).  The sign
`0 ≤ C_pw` is derived (collision-free two-particle configurations of arbitrarily large energy).
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The torus modulated energy `F_N` of `eq:FNdef` with the smooth pair representative. -/
def periodicRieszEnergyF (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) : ℝ :=
  DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) N ω

lemma periodicRieszTransportBackgroundEnergy_eq_mul (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) :
    periodicRieszTransportBackgroundEnergy s ρ N ω = (N : ℝ) * periodicRieszEnergyF s ρ N ω := rfl

/-- Finite relative entropy to the Gibbs law gives the standing integrability data. -/
lemma periodicRiesz_finiteKL_data (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) ≠ ∞) :
    ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) ∧
    Integrable (periodicRieszTransportBackgroundEnergy s ρ N) ν ∧
    Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν := by
  obtain ⟨Cpf, hCpf, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hz := (hPart N hN).1
  have hcap := periodicRieszParticleExponent_cap s hs hs2 M hM ρ hρ β hβ N hN
  rw [periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN] at hKL
  obtain ⟨hac, hu, hllr⟩ := (DGRHS.Entropy.gibbsKL_finite_domain
    (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ν
    (periodicRieszParticleExponent s ρ β N) _ hcap hz).mp hKL
  refine ⟨hac, ?_, hllr⟩
  have he : Integrable (fun ω => (-β)⁻¹ * periodicRieszParticleExponent s ρ β N ω) ν :=
    hu.const_mul _
  refine he.congr (ae_of_all _ fun ω => ?_)
  change (-β)⁻¹ * periodicRieszParticleExponent s ρ β N ω = periodicRieszTransportBackgroundEnergy s ρ N ω
  rw [periodicRieszParticleExponent_background]
  field_simp

/-- The pointwise (second) branch of Corollary 7.3 for a competitor of finite free energy. -/
lemma periodicRiesz_pointwise_branch (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (n : ℕ) (β : ℝ) (hβ : 0 < β) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] {v : PeriodicTorus ι → E}
    (Cpw Cpt : ℝ) (hCpw : 0 ≤ Cpw)
    (hpoint : ∀ N : ℕ, 1 ≤ N → ∀ ω : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → ω i ≠ ω j) →
      |periodicRieszTransportEnergy s n v ρ N ω| ≤
        Cpw * (periodicRieszEnergyF s ρ N ω + Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ)) / (N : ℝ)))
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hac : ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))
    (hbg : Integrable (periodicRieszTransportBackgroundEnergy s ρ N) ν)
    (ha : Integrable (fun ω => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω) ν) :
    |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω ∂ν| ≤
      Cpw * (N : ℝ) * periodicRieszTransportProperFreeEnergy s ρ β N ν +
        Cpw * Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ)) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let a := fun ω : Fin N → PeriodicTorus ι => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω
  have hscaled (ω : Fin N → PeriodicTorus ι) (hω : ∀ i j : Fin N, i ≠ j → ω i ≠ ω j) :
      |a ω| ≤ Cpw * (periodicRieszTransportBackgroundEnergy s ρ N ω +
        Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) := by
    have hm := mul_le_mul_of_nonneg_left (hpoint N hN ω hω) (Nat.cast_nonneg N)
    dsimp only [a]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    rw [periodicRieszTransportBackgroundEnergy_eq_mul]
    convert hm using 1 <;> field_simp <;> ring
  have hscaledae : ∀ᵐ ω ∂ν, |a ω| ≤ Cpw * (periodicRieszTransportBackgroundEnergy s ρ N ω +
      Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) := by
    filter_upwards [hac.ae_le (periodic_iid_collision_free ρ N)] with ω hω
    exact hscaled ω hω
  have hi := integral_mono_ae ha.abs
    ((hbg.add (integrable_const (Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))))).const_mul Cpw)
    hscaledae
  have hbpoint : (∫ ω, |a ω| ∂ν) ≤ Cpw * ((∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν) +
      Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) := by
    rw [integral_const_mul] at hi
    simp only [Pi.add_apply] at hi
    rw [integral_add hbg (integrable_const _)] at hi
    simpa [a] using hi
  have hex : (N : ℝ) * periodicRieszTransportProperFreeEnergy s ρ β N ν =
      (klDiv ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))).toReal / β +
        (∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν) := by
    unfold periodicRieszTransportProperFreeEnergy
    field_simp [hNr, hβ.ne']
    <;> ring
  have henergy : (∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν) ≤
      (N : ℝ) * periodicRieszTransportProperFreeEnergy s ρ β N ν := by
    rw [hex]
    exact le_add_of_nonneg_left (div_nonneg ENNReal.toReal_nonneg hβ.le)
  calc |∫ ω, a ω ∂ν| ≤ ∫ ω, |a ω| ∂ν := abs_integral_le_integral_abs
    _ ≤ Cpw * ((∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν) +
          Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) := hbpoint
    _ ≤ Cpw * ((N : ℝ) * periodicRieszTransportProperFreeEnergy s ρ β N ν +
          Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add henergy le_rfl) hCpw
    _ = _ := by ring

/-! ### The sign of `C_pw` -/

/-- Collision-free two-particle configurations of arbitrarily large modulated energy. -/
lemma periodicRiesz_twoParticle_energy_unbounded (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (R : ℝ) :
    ∃ ω : Fin 2 → PeriodicTorus ι, (∀ i j : Fin 2, i ≠ j → ω i ≠ ω j) ∧
      R < periodicRieszEnergyF s ρ 2 ω := by
  set pk := M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι with hpk
  obtain ⟨x, y, hxy, hxy'⟩ := periodicRieszPair_unbounded s hs hs2 (4 * (R + pk))
  refine ⟨![x, y], periodicTwoParticle_collisionFree x y hxy, ?_⟩
  have hlow := periodic_twoParticle_energy_lower (periodicCappedDensityMeasure ρ) (periodicRieszPair s)
    (fun a b => by simpa using (periodicRieszPair_symm (ι := ι) s (a, b)).symm) pk 0
    (fun x => periodicRieszPair_potential_abs_le s hs hs2 ρ M hM hρ x)
    (periodicRieszInteraction_nonneg s hs hs2 ρ M hM hρ) x y
  unfold periodicRieszEnergyF
  linarith

theorem periodicRiesz_pointwise_constant_nonneg (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (n : ℕ) (v : PeriodicTorus ι → E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ, 1 ≤ N → ∀ ω : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → ω i ≠ ω j) →
      |periodicRieszTransportEnergy s n v ρ N ω| ≤
        Cpw * (periodicRieszEnergyF s ρ N ω + Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ)) / (N : ℝ))) :
    0 ≤ Cpw := by
  by_contra hc
  have hcneg : Cpw < 0 := lt_of_not_ge hc
  obtain ⟨ω, hcf, hω⟩ := periodicRiesz_twoParticle_energy_unbounded s hs hs2 M hM ρ hρ
    (-Cpt * (2 : ℝ) ^ (s / (Fintype.card ι : ℝ)) / 2)
  have hb := hpoint 2 (by norm_num) ω hcf
  have hpos : 0 < periodicRieszEnergyF s ρ 2 ω + Cpt * (2 : ℝ) ^ (s / (Fintype.card ι : ℝ)) / 2 := by
    linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

/-- Corollary 7.3 on the torus, positive Riesz kernel, finite-relative-entropy competitors: the better
of the entropic estimate of Theorem 2.8 (`n`, `v`) and the pointwise-commutator estimate. -/
theorem exists_periodicRiesz_thermal_minimum_collisionFree (n : ℕ) (hn : 0 < n)
    (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
        (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
          (periodicRieszSingularPartition s (2 * (β : ℝ) - βloc) hs2 ρ N).toReal ≤ Cub) ∧
      (∀ N : ℕ, 1 ≤ N →
          1 ≤ (periodicRieszSingularPartition s (β : ℝ) hs2 ρ N).toReal ∧
          (periodicRieszSingularPartition s (β : ℝ) hs2 ρ N).toReal ≤ Cpf) ∧
      ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      let ε := periodicRieszPositiveTransportParameter s hs2 M n K (β : ℝ)
      0 < ε ∧
      let Cem := periodicRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
      1 ≤ Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ, 1 ≤ N → ∀ ω : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → ω i ≠ ω j) →
        |periodicRieszTransportEnergy s n v ρ N ω| ≤ Cpw *
          (DGRHS.CLT.sourceCanonicalModulatedEnergy
            (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
            (DGRHS.potential (periodicCappedDensityMeasure ρ)
              (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
            (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
              (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) N ω +
            Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ)) / (N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
        klDiv ν (periodicRieszSingularGibbs s (β : ℝ) hs2 ρ N) ≠ ∞ →
        ∃ e : ℝ, periodicRieszTransportExtendedFreeEnergy s hs2 ρ M (β : ℝ) N ν = (e : EReal) ∧
        Integrable (fun x => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N x) ν ∧
        |∫ x, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N x ∂ν| ≤
          min (((β : ℝ) / ε) * (N : ℝ) * e + ε⁻¹ * (Real.log Cpf + Real.log Cem))
            (Cpw * (N : ℝ) * e + Cpw * Cpt * (N : ℝ) ^ (s / (Fintype.card ι : ℝ))) := by
  obtain ⟨βloc, hloc, hrest⟩ :=
    exists_periodicRiesz_entropic_commutator_printed_constants n hn s hs hs2 M hM
  refine ⟨βloc, hloc, fun β hβ ρ hprob hρ => ?_⟩
  have hβ' : 0 < (β : ℝ) := hβ
  obtain ⟨Cub, Cpf, hCub, hCpf, hc1, hc2, hK⟩ := hrest β hβ ρ hρ
  refine ⟨Cub, Cpf, hCub, hCpf, hc1, hc2, fun {K v} hv => ?_⟩
  have h := hK hv
  dsimp only at h ⊢
  obtain ⟨hε, hCem, hlog, -, hent⟩ := h
  refine ⟨hε, hCem, hlog, ?_⟩
  intro Cpw Cpt hpoint N hN ν hν hKL
  have hCpw := periodicRiesz_pointwise_constant_nonneg s hs hs2 M hM ρ hρ n v Cpw Cpt hpoint
  obtain ⟨hac, hbg, hllr⟩ := periodicRiesz_finiteKL_data s hs hs2 M hM (β : ℝ) hβ' ρ hρ N hN ν hKL
  obtain ⟨⟨e, he⟩, ha, hb⟩ := hent N hN ν hKL
  have hext := periodicRieszTransportExtendedFreeEnergy_eq_proper s hs hs2 M hM (β : ℝ) hβ' ρ hρ
    N hN ν hac hbg hllr
  have hpe : periodicRieszTransportProperFreeEnergy s ρ (β : ℝ) N ν = e := by
    apply EReal.coe_injective
    exact hext.symm.trans he
  have hbd1 : |∫ x, (N : ℝ) * periodicRieszTransportEnergy s n v ρ N x ∂ν| ≤
      ((β : ℝ) / periodicRieszPositiveTransportParameter s hs2 M n K (β : ℝ)) * (N : ℝ) * e +
        (periodicRieszPositiveTransportParameter s hs2 M n K (β : ℝ))⁻¹ *
          (Real.log Cpf + Real.log (periodicRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
            (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
              (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))))) := by
    rw [he, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hb
    exact hb
  have hbd2 := periodicRiesz_pointwise_branch s hs hs2 n (β : ℝ) hβ' ρ Cpw Cpt hCpw hpoint N hN ν
    hac hbg ha
  rw [hpe] at hbd2
  exact ⟨e, he, ha, le_min hbd1 hbd2⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRiesz_finiteKL_data
#print axioms DGRHS.Periodic.periodicRiesz_pointwise_branch
#print axioms DGRHS.Periodic.periodicRiesz_twoParticle_energy_unbounded
#print axioms DGRHS.Periodic.periodicRiesz_pointwise_constant_nonneg
#print axioms DGRHS.Periodic.exists_periodicRiesz_thermal_minimum_collisionFree
