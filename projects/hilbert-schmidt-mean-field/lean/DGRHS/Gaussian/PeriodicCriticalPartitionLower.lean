import DGRHS.Gaussian.PeriodicFirstShellFullLower
import DGRHS.Gaussian.PeriodicCriticalGaussianFactor
import Mathlib.Order.LiminfLimsup

/-! Original periodic critical lower bound, for the full actual extended
partition. The every-N bound is stronger than the source asymptotic one.
This direct bounded-tilt proof replaces heat regularization; no unproved
physical pointwise Green bound or partition finiteness is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_critical_full_sqrt_lower (N : ℕ) (hN : 1≤N) :
    ENNReal.ofReal (Real.exp (-(Fintype.card ι:ℝ))*
      (Real.sqrt Real.pi*Real.sqrt (N:ℝ))^(Fintype.card ι)) ≤
      periodicAttractivePartition (ι := ι) (periodicStabilityThreshold ι) N := by
  have h := periodic_firstShell_full_partition_lower (ι := ι)
    (periodicStabilityThreshold ι) periodicStabilityThreshold_pos.le N hN
  have he : -(periodicStabilityThreshold ι)*(periodicStabilityThreshold ι)⁻¹*(Fintype.card ι:ℝ)=
      -(Fintype.card ι:ℝ) := by
    rw [neg_mul,mul_inv_cancel₀ periodicStabilityThreshold_pos.ne',neg_one_mul]
  rw [he,periodic_critical_gaussian_normalizer_factor N hN,
    ←ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  apply le_trans _ h
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact pow_le_pow_left₀ (by positivity) (periodic_halfGaussian_Bessel_sqrt_lower N hN) _

lemma periodic_critical_normalizing_identity (N : ℕ) (hN : 1≤N) :
    (N:ℝ)^(-(Fintype.card ι:ℝ)/2)*
      (Real.exp (-(Fintype.card ι:ℝ))*(Real.sqrt Real.pi*Real.sqrt (N:ℝ))^(Fintype.card ι)) =
      (Real.sqrt Real.pi/Real.exp 1)^(Fintype.card ι) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hs : (Real.sqrt (N:ℝ))^(Fintype.card ι) = (N:ℝ)^((Fintype.card ι:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul hn.le]
    congr 1
    ring
  rw [mul_pow,hs,show -(Fintype.card ι:ℝ)/2= -((Fintype.card ι:ℝ)/2) by ring,
    Real.rpow_neg hn.le,Real.exp_neg,div_pow,Real.exp_one_pow]
  have hz : (N:ℝ)^((Fintype.card ι:ℝ)/2)≠0 := (Real.rpow_pos_of_pos hn _).ne'
  field_simp
  <;> ring

/-- Source-normalized every-N lower bound, with exact critical constant. -/
theorem periodic_critical_normalized_lower (N : ℕ) (hN : 1≤N) :
    ENNReal.ofReal ((Real.sqrt Real.pi/Real.exp 1)^(Fintype.card ι)) ≤
      ENNReal.ofReal ((N:ℝ)^(-(Fintype.card ι:ℝ)/2))*
        periodicAttractivePartition (ι := ι) (periodicStabilityThreshold ι) N := by
  have h := mul_le_mul_of_nonneg_left (periodic_critical_full_sqrt_lower (ι := ι) N hN)
    (show (0:ℝ≥0∞)≤ENNReal.ofReal ((N:ℝ)^(-(Fintype.card ι:ℝ)/2)) from zero_le)
  rw [←ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg N) _),
    periodic_critical_normalizing_identity N hN] at h
  exact h

/-- Actual full-partition version of source periodicCriticalLowerBound. -/
theorem periodic_critical_partition_liminf :
    ENNReal.ofReal ((Real.sqrt Real.pi/Real.exp 1)^(Fintype.card ι)) ≤
      Filter.liminf (fun N : ℕ => ENNReal.ofReal ((N:ℝ)^(-(Fintype.card ι:ℝ)/2))*
        periodicAttractivePartition (ι := ι) (periodicStabilityThreshold ι) N) atTop := by
  exact le_liminf_of_le (by isBoundedDefault)
    (eventually_atTop.2 ⟨1,fun N hN => periodic_critical_normalized_lower (ι := ι) N hN⟩)

/-- Exact source dimension range; the proof also gives lower-dimensional
extended lower bounds, without asserting their finiteness. -/
theorem periodic_critical_partition_source (d : ℕ) (hd : 11≤d) :
    letI : NeZero d := ⟨by omega⟩
    ENNReal.ofReal ((Real.sqrt Real.pi/Real.exp 1)^d) ≤
      Filter.liminf (fun N : ℕ => ENNReal.ofReal ((N:ℝ)^(-(d:ℝ)/2))*
        periodicAttractivePartition (ι := Fin d) (periodicStabilityThreshold (Fin d)) N) atTop := by
  letI : NeZero d := ⟨by omega⟩
  simpa only [Fintype.card_fin] using periodic_critical_partition_liminf (ι := Fin d)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_critical_full_sqrt_lower
#print axioms DGRHS.Periodic.periodic_critical_normalizing_identity
#print axioms DGRHS.Periodic.periodic_critical_normalized_lower
#print axioms DGRHS.Periodic.periodic_critical_partition_liminf
#print axioms DGRHS.Periodic.periodic_critical_partition_source
#check @DGRHS.Periodic.periodic_critical_partition_source
