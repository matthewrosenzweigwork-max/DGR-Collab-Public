import DGRHS.Gaussian.PeriodicD1DysonSourceBridge
import DGRHS.Gaussian.PeriodicD1GammaQuotient
import DGRHS.Gaussian.PeriodicPartitionFinite

/-! UNCOMPILED CANDIDATE (Claude complete physical d1 return, 2026-10-03).
Scalar thermodynamic limit of the ACTUAL one-dimensional source partition.

The first three declarations are moved verbatim (same names, same statements)
from the supplied `PeriodicD1SourceConsequences` draft, so that the scalar limit
no longer imports the operator branch. `PeriodicD1SourceConsequences` (repaired
copy in this return) imports this file and keeps only the determinant
identification; every one of its four public names still resolves for its
consumers.

Dependencies: the exact finite-N partition `periodicD1_attractive_partition_exact`
(DysonSourceBridge, which imports A's CircleMellin, UNCOMPILED) and the checked
scalar `periodicD1_Gamma_quotient_tendsto`. The determinant is NOT used here,
so the all-AC entropy-energy branch cannot circularly depend on it. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace DGRHS.Periodic

/-- The source range `β < 2 = 2·d` in the generic campaign form. -/
lemma periodicD1_beta_lt_card {β : ℝ} (hβ : β < 2) :
    β < 2*(Fintype.card (Fin 1):ℝ) := by
  rw [Fintype.card_fin, Nat.cast_one, mul_one]
  exact hβ

/-- The physical limit constant `exp(-γ β/2) Γ(1-β/2)`. -/
lemma periodicD1_partition_limit_pos {β : ℝ} (hβ : β < 2) :
    0 < Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2) :=
  mul_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos (by linarith))

lemma periodicD1_attractive_partition_toReal (β : ℝ) (hβ0 : 0≤β) (hβ : β<2)
    (N : ℕ) (hN : 0<N) :
    (periodicAttractivePartition (ι := Fin 1) β N).toReal=
      Real.Gamma (1-β/2)/(Real.Gamma (1-β/(2*(N:ℝ))))^N := by
  rw [periodicD1_attractive_partition_exact β hβ0 hβ N hN,
    ENNReal.toReal_ofReal]
  exact div_nonneg (Real.Gamma_pos_of_pos (by linarith : 0<1-β/2)).le
    (pow_nonneg (Real.Gamma_pos_of_pos
      (periodicD1_Gamma_argument_pos hβ (by omega : 1≤N))).le _)

theorem periodicD1_attractive_partition_toReal_tendsto (β : ℝ) (hβ0 : 0≤β)
    (hβ : β<2) :
    Tendsto (fun N : ℕ => (periodicAttractivePartition (ι := Fin 1) β N).toReal)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2))) := by
  apply (periodicD1_Gamma_quotient_tendsto β hβ0 hβ).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (periodicD1_attractive_partition_toReal β hβ0 hβ N hN).symm

theorem periodicD1_attractive_partition_tendsto (β : ℝ) (hβ0 : 0≤β) (hβ : β<2) :
    Tendsto (periodicAttractivePartition (ι := Fin 1) β) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2)))) := by
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (periodicD1_Gamma_quotient_tendsto β hβ0 hβ)
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (periodicD1_attractive_partition_exact β hβ0 hβ N hN).symm

/-- The real Gibbs integral is the actual extended partition, for every `N ≥ 1`. -/
lemma periodicD1_partition_integral_eq_toReal (β : ℝ) (hβ0 : 0≤β) (hβ : β<2)
    (N : ℕ) (hN : 1≤N) :
    (∫ x : Fin N → PeriodicTorus (Fin 1), Real.exp (periodicParticleExponent β N x)
        ∂Measure.pi fun _ : Fin N => periodicHaar (Fin 1)) =
      (periodicAttractivePartition (ι := Fin 1) β N).toReal := by
  rw [periodicAttractivePartition_eq_ofReal β hβ0 (periodicD1_beta_lt_card hβ) N hN,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- Limit of the literal real Gibbs integrals. -/
theorem periodicD1_partition_integral_tendsto (β : ℝ) (hβ0 : 0≤β) (hβ : β<2) :
    Tendsto (fun N : ℕ => ∫ x : Fin N → PeriodicTorus (Fin 1),
        Real.exp (periodicParticleExponent β N x) ∂Measure.pi fun _ : Fin N => periodicHaar (Fin 1))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2))) := by
  apply (periodicD1_attractive_partition_toReal_tendsto β hβ0 hβ).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (periodicD1_partition_integral_eq_toReal β hβ0 hβ N hN).symm

/-- Normalized free energy of the physical partition tends to zero. This is the
only thermodynamic input of the all-AC entropy-energy argument. -/
theorem periodicD1_log_partition_div_tendsto (β : ℝ) (hβ0 : 0≤β) (hβ : β<2) :
    Tendsto (fun N : ℕ => Real.log (∫ x : Fin N → PeriodicTorus (Fin 1),
        Real.exp (periodicParticleExponent β N x) ∂Measure.pi fun _ : Fin N => periodicHaar (Fin 1))
          / (N:ℝ)) atTop (𝓝 0) := by
  have hlog := ((Real.continuousAt_log (periodicD1_partition_limit_pos hβ).ne').tendsto).comp
    (periodicD1_partition_integral_tendsto β hβ0 hβ)
  exact hlog.div_atTop tendsto_natCast_atTop_atTop

end DGRHS.Periodic
