import DGRHS.Gaussian.PeriodicLogEntropicCommutator
import DGRHS.Gaussian.PeriodicPairUnbounded
import DGRHS.Commutator.SourceLogThermalSourceCollisionFree

/-!
Packet P11a, unit 2 (LOG): Corollary 7.3 (`cor:entropicCommutatorTemperatureInterpolation`,
TeX 3547-3579) on the flat torus (Remark 2.1, TeX 492-496), logarithmic kernel, for every
probability competitor `ν` (extended free energy, as the torus Theorem 2.8 LOG export), with the
pointwise commutator premise `eq:pointwiseCommutatorBound` required only on COLLISION-FREE
configurations (as the Euclidean export `exists_sourceLog_thermal_minimum_source_collisionFree`).

As in that export, the single degenerate case `C_pw = 0` with `ν` charging collisions
(`0 · (+∞)` in the print) is excluded by the explicit hypothesis `C_pw = 0 → ν ≪ μ^{⊗N}`.  The sign
`0 ≤ C_pw` is derived (`periodicLogPair_unbounded`).  The pointwise branch reuses the kernel-generic
`DGRHS.Entropy.bounded_observable_pointwise_freeEnergy_ae`.
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration DGRHS.Entropy
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The torus modulated energy `F_N` of `eq:FNdef` for the LOG kernel (smooth pair representative). -/
def periodicLogEnergyF (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) : ℝ :=
  DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair)
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) N ω

lemma periodicLogTransportBackgroundEnergy_eq_mul (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) :
    periodicLogTransportBackgroundEnergy ρ N ω = (N : ℝ) * periodicLogEnergyF ρ N ω := rfl

/-- The torus LOG extended free energy is the bounded-energy free energy of `F_N`. -/
lemma periodicLogTransportExtendedFreeEnergy_eq_bounded (M β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) :
    periodicLogTransportExtendedFreeEnergy ρ M β N ν =
      boundedEnergyFreeEnergy (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ν
        (periodicLogEnergyF ρ N) (-periodicLogBgConst ι M) (β * (N : ℝ)) := by
  have hb : 0 < β * (N : ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0 < N))
  rw [boundedEnergyFreeEnergy_eq_scaledGibbs _ ν _ _ _ hb]
  unfold periodicLogTransportExtendedFreeEnergy
  congr 2
  · funext x
    unfold periodicLogParticleExponent periodicLogEnergyF
    ring
  · ring

/-- The pointwise (second) branch of Corollary 7.3, LOG. -/
lemma periodicLog_pointwise_branch (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (a : (Fin N → PeriodicTorus ι) → ℝ) (ha : StronglyMeasurable a) (A : ℝ) (hA : ∀ x, |a x| ≤ A)
    (Cpw Cpt scale : ℝ) (hCpw : 0 ≤ Cpw)
    (hν0 : Cpw = 0 → ∀ᵐ x ∂ν, |a x| ≤ 0)
    (hscaled : ∀ x : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → x i ≠ x j) →
      |a x| ≤ Cpw * ((N : ℝ) * periodicLogEnergyF ρ N x + Cpt * scale)) :
    Integrable a ν ∧ ((|∫ x, a x ∂ν| : ℝ) : EReal) ≤
      ((Cpw * (N : ℝ) : ℝ) : EReal) * periodicLogTransportExtendedFreeEnergy ρ M β N ν +
        ((Cpw * Cpt * scale : ℝ) : EReal) := by
  let P := Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hF : StronglyMeasurable (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) :=
    measurable_periodicLogPair.stronglyMeasurable.integral_prod_right'
  have hE : StronglyMeasurable (periodicLogEnergyF ρ N) :=
    DGRHS.CLT.stronglyMeasurable_sourceCanonicalModulatedEnergy _ _ _
      (stronglyMeasurable_hoeffdingCentered _ _ measurable_periodicLogPair.stronglyMeasurable) hF N
  have hfloor : ∀ x, -periodicLogBgConst ι M ≤ periodicLogEnergyF ρ N x := by
    intro x
    have h := periodicLogTransportBackgroundEnergy_lower M hM ρ hρ N hN x
    rw [periodicLogTransportBackgroundEnergy_eq_mul] at h
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hn]
  have hae : ∀ᵐ x ∂P, |a x| ≤ Cpw * (N : ℝ) * periodicLogEnergyF ρ N x + Cpw * Cpt * scale := by
    filter_upwards [periodic_iid_collision_free ρ N] with x hx
    calc |a x| ≤ Cpw * ((N : ℝ) * periodicLogEnergyF ρ N x + Cpt * scale) := hscaled x hx
      _ = Cpw * (N : ℝ) * periodicLogEnergyF ρ N x + Cpw * Cpt * scale := by ring
  have hmain := bounded_observable_pointwise_freeEnergy_ae P ν a (periodicLogEnergyF ρ N) ha hE A
    (-periodicLogBgConst ι M) (β * (N : ℝ)) (Cpw * (N : ℝ)) (Cpw * Cpt * scale) hA hfloor
    (mul_pos hβ hn) (mul_nonneg hCpw hn.le) ?_ hae
  · rw [periodicLogTransportExtendedFreeEnergy_eq_bounded M β hβ ρ N hN ν]
    exact hmain
  · intro hk
    have hc : Cpw = 0 := (mul_eq_zero.mp hk).resolve_right hn.ne'
    filter_upwards [hν0 hc] with x hx
    rw [hc]
    simpa using hx

/-! ### The sign of `C_pw` -/

lemma periodicLog_twoParticle_energy_unbounded (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (R : ℝ) :
    ∃ ω : Fin 2 → PeriodicTorus ι, (∀ i j : Fin 2, i ≠ j → ω i ≠ ω j) ∧
      R < periodicLogEnergyF ρ 2 ω := by
  set pk := M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι with hpk
  set I0 := -(periodicLogPairLower ι / 2) with hI0
  obtain ⟨x, y, hxy, hxy'⟩ := periodicLogPair_unbounded (ι := ι) (4 * (R + pk - I0))
  refine ⟨![x, y], periodicTwoParticle_collisionFree x y hxy, ?_⟩
  have hlow := periodic_twoParticle_energy_lower (periodicCappedDensityMeasure ρ) periodicLogPair
    (fun a b => by simpa using (periodicLogPair_symm (ι := ι) (a, b)).symm) pk I0
    (fun x => periodicLogPair_potential_abs_le ρ M hM hρ x)
    (periodicLogInteraction_lower ρ) x y
  unfold periodicLogEnergyF
  linarith

theorem periodicLog_pointwise_constant_nonneg (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (n : ℕ) (v : PeriodicTorus ι → E) (Cpw Cpt : ℝ)
    (hpoint : ∀ N : ℕ, 1 ≤ N → ∀ ω : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → ω i ≠ ω j) →
      |sourceTransportEnergy (periodicCappedDensityMeasure ρ) (periodicLogTransportKernel n v) N ω| ≤
        Cpw * (periodicLogEnergyF ρ N ω + Cpt * Real.log (Real.exp 1 + (N : ℝ)) / (N : ℝ))) :
    0 ≤ Cpw := by
  by_contra hc
  have hcneg : Cpw < 0 := lt_of_not_ge hc
  obtain ⟨ω, hcf, hω⟩ := periodicLog_twoParticle_energy_unbounded M hM ρ hρ
    (-Cpt * Real.log (Real.exp 1 + (2 : ℝ)) / 2)
  have hb := hpoint 2 (by norm_num) ω hcf
  have hpos : 0 < periodicLogEnergyF ρ 2 ω + Cpt * Real.log (Real.exp 1 + (2 : ℝ)) / 2 := by
    linarith
  have hneg := mul_neg_of_neg_of_pos hcneg hpos
  norm_num only [Nat.cast_ofNat] at hb
  exact (not_lt_of_ge ((abs_nonneg _).trans hb)) hneg

/-- Corollary 7.3 on the torus, LOG kernel. -/
theorem exists_periodicLog_thermal_minimum_collisionFree (n : ℕ) (hn : 0 < n) :
    ∃ Csr : ℝ, 0 < Csr ∧ ∀ {K : ℝ≥0} {v : PeriodicTorus ι → E}, LipschitzWith K v →
      0 < (K : ℝ) →
      ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ), 0 ≤ M →
      ∀ [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
      (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
      ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ Cub Cpf : ℝ, 1 ≤ Cub ∧ 1 ≤ Cpf ∧
      (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
        (periodicLogSingularPartition (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
      let μ := periodicCappedDensityMeasure ρ
      let I := DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))
      let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n)
      let Cem := sourceLogTransportCem (β : ℝ) βloc I glzUniversalTailConstant Cub
      0 < ε ∧ 0 < Cem ∧
      (∀ N : ℕ, 1 ≤ N → Real.exp ((β : ℝ) * I) ≤ (periodicLogSingularPartition (β : ℝ) ρ N).toReal ∧
        (periodicLogSingularPartition (β : ℝ) ρ N).toReal ≤ Cpf) ∧
      ∀ Cpw Cpt : ℝ,
      (∀ N : ℕ, 1 ≤ N → ∀ x : Fin N → PeriodicTorus ι, (∀ i j : Fin N, i ≠ j → x i ≠ x j) →
        |sourceTransportEnergy μ (periodicLogTransportKernel n v) N x| ≤
          Cpw * (DGRHS.CLT.sourceCanonicalModulatedEnergy (hoeffdingCentered μ periodicLogPair)
            (DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
            (DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) N x +
            Cpt * Real.log (Real.exp 1 + (N : ℝ)) / (N : ℝ))) →
      ∀ N : ℕ, 1 ≤ N → ∀ (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν],
      (Cpw = 0 → ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) →
      Integrable (fun x => (N : ℝ) * sourceTransportEnergy μ
        (periodicLogTransportKernel n v) N x) ν ∧
      ((|∫ x, (N : ℝ) * sourceTransportEnergy μ (periodicLogTransportKernel n v) N x ∂ν| : ℝ) :
        EReal) ≤
        min ((((β : ℝ) / ε) * (N : ℝ) : ℝ) * periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν +
            (ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ))
          ((Cpw * (N : ℝ) : ℝ) * periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν +
            (Cpw * Cpt * Real.log (Real.exp 1 + (N : ℝ)) : ℝ)) := by
  have hn1 : 1 ≤ n := hn
  obtain ⟨Csr, hC, hfactory⟩ := exists_periodicLog_entropic_commutator (ι := ι) n hn
  obtain ⟨CK, hCK, hbd⟩ := periodicLogTransportKernel_bound (ι := ι) n hn1
  refine ⟨Csr, hC, ?_⟩
  intro K v hv hK ρ M hM hprob hρ
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory hv hK ρ M hM hρ
  refine ⟨βloc, hloc, ?_⟩
  intro β hβ
  obtain ⟨Cub, Cpf, hCub, hCpf, hremaining, hrest⟩ := hβfactory β hβ
  have hβ' : 0 < (β : ℝ) := hβ
  refine ⟨Cub, Cpf, hCub, hCpf, hremaining, ?_⟩
  dsimp only at hrest ⊢
  obtain ⟨hε, hCem, hcap, -, -, hent⟩ := hrest
  refine ⟨hε, hCem, hcap, ?_⟩
  intro Cpw Cpt hpoint N hN ν hν hν0
  have hn' : 0 < N := by omega
  have hCpw := periodicLog_pointwise_constant_nonneg M hM ρ hρ n v Cpw Cpt hpoint
  have hm := periodicLogTransportKernel_measurable (ι := ι) n hv
  have hsa : StronglyMeasurable (fun x : Fin N → PeriodicTorus ι => (N : ℝ) *
      sourceTransportEnergy (periodicCappedDensityMeasure ρ) (periodicLogTransportKernel n v) N x) :=
    (stronglyMeasurable_sourceTransportEnergy _ _ hm N).const_mul (N : ℝ)
  let A := (N : ℝ) * (4 * (CK * (K : ℝ) ^ n))
  have hA : ∀ x : Fin N → PeriodicTorus ι, |(N : ℝ) * sourceTransportEnergy
      (periodicCappedDensityMeasure ρ) (periodicLogTransportKernel n v) N x| ≤ A := by
    intro x
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
    exact abs_sourceTransportEnergy_le _ _ hm _ (hbd hv)
      (fun a b => (periodicLogTransportKernel_symm n v (a, b)).symm)
      (fun a => by simp [periodicLogTransportKernel]) N hn' x
  obtain ⟨hi, hb1⟩ := hent N hN ν
  have hnr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hscaled (x : Fin N → PeriodicTorus ι) (hx : ∀ i j : Fin N, i ≠ j → x i ≠ x j) :
      |(N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
        (periodicLogTransportKernel n v) N x| ≤
      Cpw * ((N : ℝ) * periodicLogEnergyF ρ N x + Cpt * Real.log (Real.exp 1 + (N : ℝ))) := by
    have hm' := mul_le_mul_of_nonneg_left (hpoint N hN x hx) (Nat.cast_nonneg N)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    unfold periodicLogEnergyF
    convert hm' using 1 <;> field_simp <;> ring
  have hν0' : Cpw = 0 → ∀ᵐ x ∂ν, |(N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
      (periodicLogTransportKernel n v) N x| ≤ 0 := by
    intro hc
    filter_upwards [(hν0 hc).ae_le (periodic_iid_collision_free ρ N)] with x hx
    have h := hscaled x hx
    rw [hc, zero_mul] at h
    exact h
  obtain ⟨-, hb2⟩ := periodicLog_pointwise_branch M hM (β : ℝ) hβ' ρ hρ N hN ν
    (fun x => (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
      (periodicLogTransportKernel n v) N x) hsa A hA Cpw Cpt (Real.log (Real.exp 1 + (N : ℝ)))
    hCpw hν0' hscaled
  exact ⟨hi, le_min hb1 hb2⟩

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogTransportExtendedFreeEnergy_eq_bounded
#print axioms DGRHS.Periodic.periodicLog_pointwise_branch
#print axioms DGRHS.Periodic.periodicLog_twoParticle_energy_unbounded
#print axioms DGRHS.Periodic.periodicLog_pointwise_constant_nonneg
#print axioms DGRHS.Periodic.exists_periodicLog_thermal_minimum_collisionFree
