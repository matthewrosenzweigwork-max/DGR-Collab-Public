import DGRHS.Gaussian.PeriodicD1ParticleVariational
import DGRHS.Gaussian.PeriodicD1PhysicalLimit

/-! UNCOMPILED CANDIDATE (Claude complete physical d1 return, 2026-10-03).
Sharp subcritical entropy-energy comparison on the circle for EVERY probability
law, in the campaign's extended formulation (source eq:periodicAttractiveFreeEnergy,
eq:betaGmDef, lines 2986-3003, specialized to d = 1 as asserted at line 3087).

Route (an alternative to density approximation, see PROOF_PLAN.md):
1. infinite KL: the EReal comparison is trivial (right side is ⊤);
2. β = 0: the left side is `0 * E = 0` in EReal;
3. finite KL, 0 < β < 2: proper pair energy is derived at N = 2
   (`periodicGreen_pair_integrable_of_finite_klDiv`); for every N ≥ 1 the exact
   iid bound `β (N-1)/2 · E ≤ N · KL + log Z_N` holds
   (`periodicParticle_pair_energy_bound`); after division by N the coefficient
   is `(β/2)(1 - 1/N)`; the actual physical partition has a finite positive
   limit, so `log Z_N / N → 0` (`periodicD1_log_partition_div_tendsto`).

No absolute continuity, density bound, L2, finite entropy, finite energy or
minimizer hypothesis appears in the exported comparison. (Absolute continuity
is not even needed: infinite KL covers every non-AC law.) -/
noncomputable section
open MeasureTheory InformationTheory Filter
open scoped Topology ENNReal
namespace DGRHS.Periodic

/-- Elementary division step, stated on free reals to avoid any coercion or
local-definition matching. -/
lemma periodicD1_scaled_bound_algebra (β E K L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (h : β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*E) ≤ (N:ℝ)*K + L) :
    β/2*E - β/2*E/(N:ℝ) ≤ K + L/(N:ℝ) := by
  have hNpos : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hN0 : (N:ℝ) ≠ 0 := hNpos.ne'
  have h1 : β/(2*(N:ℝ))*((N:ℝ)*((N:ℝ)-1)*E) = (N:ℝ)*(β/2*E - β/2*E/(N:ℝ)) := by
    first
    | (field_simp; ring)
    | field_simp
    | (rw [mul_sub, mul_div_cancel₀ _ hN0]; field_simp; ring)
  have h2 : (N:ℝ)*K + L = (N:ℝ)*(K + L/(N:ℝ)) := by
    rw [mul_add, mul_div_cancel₀ L hN0]
  rw [h1, h2] at h
  exact le_of_mul_le_mul_left h hNpos

/-- Finite-KL case: proper pair energy and the sharp real comparison. -/
theorem periodicD1_entropy_energy_of_finite_klDiv (β : ℝ) (hβ : 0 < β) (hβ2 : β < 2)
    (ν : Measure (PeriodicTorus (Fin 1))) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar (Fin 1)) ≠ ∞) :
    Integrable (fun p : PeriodicTorus (Fin 1) × PeriodicTorus (Fin 1) =>
        periodicLogKernel (p.1 - p.2)) (ν.prod ν) ∧
      β/2 * (∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν) ≤
        (klDiv ν (periodicHaar (Fin 1))).toReal := by
  have hβd := periodicD1_beta_lt_card hβ2
  refine ⟨periodicGreen_pair_integrable_of_finite_klDiv β hβ hβd ν hKL, ?_⟩
  have hf : Tendsto (fun N : ℕ => β/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν) -
      β/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν)/(N:ℝ)) atTop
      (𝓝 (β/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν))) := by
    have h := (tendsto_const_nhds
        (x := β/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν))).sub
      ((tendsto_const_nhds
        (x := β/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν))).div_atTop
          tendsto_natCast_atTop_atTop)
    simpa only [sub_zero] using h
  have hg : Tendsto (fun N : ℕ => (klDiv ν (periodicHaar (Fin 1))).toReal +
      Real.log (∫ x : Fin N → PeriodicTorus (Fin 1), Real.exp (periodicParticleExponent β N x)
        ∂Measure.pi fun _ : Fin N => periodicHaar (Fin 1))/(N:ℝ)) atTop
      (𝓝 ((klDiv ν (periodicHaar (Fin 1))).toReal)) := by
    have h := (tendsto_const_nhds (x := (klDiv ν (periodicHaar (Fin 1))).toReal)).add
      (periodicD1_log_partition_div_tendsto β hβ.le hβ2)
    simpa only [add_zero] using h
  apply le_of_tendsto_of_tendsto hf hg
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact periodicD1_scaled_bound_algebra β _ _ _ N hN
    (periodicParticle_pair_energy_bound β hβ hβd N hN ν hKL)

/-- **All-law extended entropy-energy comparison, d = 1, 0 ≤ β < 2.**
`(β/2) · E_ext(ν) ≤ KL(ν | Haar)` in `EReal`, for EVERY probability law `ν`
on the circle. When the energy is proper this is the literal real comparison;
for L2 densities it is the source centered operator pairing
(`periodicGreenEnergyExtended_eq_source_L2_pairing`). -/
theorem periodicD1_entropy_energy_extended (β : ℝ) (hβ0 : 0 ≤ β) (hβ2 : β < 2)
    (ν : Measure (PeriodicTorus (Fin 1))) [IsProbabilityMeasure ν] :
    ((β/2:ℝ):EReal) * periodicGreenEnergyExtended ν ≤
      (klDiv ν (periodicHaar (Fin 1)) : EReal) := by
  by_cases hKL : klDiv ν (periodicHaar (Fin 1)) = ∞
  · rw [hKL, EReal.coe_ennreal_top]
    exact le_top
  rcases hβ0.eq_or_lt with h0 | hpos
  · subst h0
    rw [zero_div, EReal.coe_zero, zero_mul]
    exact EReal.coe_ennreal_nonneg _
  · obtain ⟨hint, hle⟩ := periodicD1_entropy_energy_of_finite_klDiv β hpos hβ2 ν hKL
    rw [signedGreen_extended_eq_integral ν hint, ← EReal.coe_ennreal_toReal hKL,
      ← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr hle

/-- In the finite-entropy case the extended energy is a real number: the
comparison at any fixed positive subcritical temperature excludes `+∞` energy.
This records the extended-value case analysis explicitly. -/
theorem periodicD1_energy_proper_of_finite_klDiv
    (ν : Measure (PeriodicTorus (Fin 1))) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar (Fin 1)) ≠ ∞) :
    periodicGreenEnergyExtended ν =
      (((∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν):ℝ):EReal) :=
  signedGreen_extended_eq_integral ν
    (periodicD1_entropy_energy_of_finite_klDiv 1 one_pos (by norm_num) ν hKL).1

/-- Endpoint form (the supremum statement does not need it): the energy is at
most the entropy, `E(ν) ≤ KL(ν)`, obtained by letting β ↑ 2 in the finite case. -/
theorem periodicD1_energy_le_entropy_of_finite_klDiv
    (ν : Measure (PeriodicTorus (Fin 1))) [IsProbabilityMeasure ν]
    (hKL : klDiv ν (periodicHaar (Fin 1)) ≠ ∞) :
    (∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν) ≤
      (klDiv ν (periodicHaar (Fin 1))).toReal := by
  have hseq : Tendsto (fun n : ℕ => (2:ℝ) - 1/((n:ℝ)+1)) atTop (𝓝 2) := by
    have h := (tendsto_const_nhds (x := (2:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [sub_zero] using h
  have hlo (n : ℕ) : 0 < (2:ℝ) - 1/((n:ℝ)+1) := by
    have h1 : 1/((n:ℝ)+1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    linarith
  have hhi (n : ℕ) : (2:ℝ) - 1/((n:ℝ)+1) < 2 := by
    have : 0 < 1/((n:ℝ)+1) := one_div_pos.mpr (by positivity)
    linarith
  have hf := (hseq.div_const 2).mul_const (∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν)
  have hE : (2:ℝ)/2*(∫ p, periodicLogKernel (p.1 - p.2) ∂ν.prod ν) ≤
      (klDiv ν (periodicHaar (Fin 1))).toReal :=
    le_of_tendsto_of_tendsto' hf tendsto_const_nhds fun n =>
      (periodicD1_entropy_energy_of_finite_klDiv _ (hlo n) (hhi n) ν hKL).2
  simpa only [div_self (two_ne_zero : (2:ℝ) ≠ 0), one_mul] using hE

end DGRHS.Periodic
