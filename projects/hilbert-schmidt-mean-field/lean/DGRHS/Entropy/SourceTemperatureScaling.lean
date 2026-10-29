/- Original growing-temperature specialization (eq:growingTemperatureSpecialization).
Constants precede gamma, beta_star and N. Positive literal partition values are
proved before taking their logarithm. Native real powers supply all scaling identities. -/
import DGRHS.Entropy.SourceRieszTemperatureGrowth
import DGRHS.CLT.SourceRieszSingularIdentification
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

lemma temperature_scaling_log_small (C B a b q K : ℝ) (hC : 1 ≤ C)
    (hB : 0 ≤ B) (hb : 0 ≤ b) (hbB : b ≤ B) (hq : q ≤ 1)
    (hK : 0 < K) (hcap : K ≤ C*Real.exp (C*max (b*q-B) 0*a)) :
    Real.log K ≤ C*(1+B) := by
  have hsmall : b*q ≤ B := (mul_le_mul_of_nonneg_left hq hb).trans (by simpa using hbB)
  rw [max_eq_right (sub_nonpos.mpr hsmall), mul_zero, zero_mul, Real.exp_zero, mul_one] at hcap
  have hl := (Real.log_le_log hK hcap).trans (Real.log_le_sub_one_of_pos (by linarith : 0 < C))
  nlinarith

lemma temperature_scaling_log_large (C B a b q K : ℝ) (hC : 1 ≤ C)
    (hB : 0 ≤ B) (ha : 1 ≤ a) (hb : 0 ≤ b) (hbB : b ≤ B) (hq : 1 ≤ q)
    (hK : 0 < K) (hcap : K ≤ C*Real.exp (C*max (b*q-B) 0*a)) :
    Real.log K ≤ C*(1+B)*q*a := by
  have hCp : 0 < C := by linarith
  have hq0 : 0 ≤ q := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hmax : max (b*q-B) 0 ≤ B*q := max_le
    (by nlinarith [mul_le_mul_of_nonneg_right hbB hq0]) (mul_nonneg hB hq0)
  have hl := Real.log_le_log hK hcap
  rw [Real.log_mul hCp.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  have hcLog := Real.log_le_sub_one_of_pos hCp
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax ha0) hCp.le
  have hqa : 1 ≤ q*a := by nlinarith
  have hcqa := mul_le_mul_of_nonneg_left hqa hCp.le
  nlinarith

open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

def scaledLogTemperature (b : ℝ≥0) (N : ℕ) (γ : ℝ) : ℝ≥0 :=
  ⟨(b : ℝ)*(N : ℝ)^γ, mul_nonneg b.coe_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) γ)⟩

theorem sourceLogPartition_temperature_scaling (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ γ : ℝ, ∀ b : ℝ≥0, b ≤ B → ∀ N : ℕ, 1 ≤ N →
      (γ ≤ 0 → Real.log (sourceLogSingularPartition (scaledLogTemperature b N γ) ρ N).toReal ≤ D) ∧
      (0 < γ → Real.log (sourceLogSingularPartition (scaledLogTemperature b N γ) ρ N).toReal ≤
        D*(N : ℝ)^γ*Real.log (Real.exp 1+(N : ℝ))) := by
  obtain ⟨C, hC, hcap⟩ := sourceLogPartition_all_temperature_growth B hB hd ρ M hM hρ hpair
  refine ⟨C*(1+(B : ℝ)), by nlinarith [B.coe_nonneg], ?_⟩
  intro γ b hb N hN
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < (sourceLogSingularPartition (scaledLogTemperature b N γ) ρ N).toReal := by
    obtain ⟨_, _, hJ⟩ := sourceLogPartition_original_bounds (scaledLogTemperature b N γ)
      hd ρ M hM hρ hpair
    exact (Real.exp_pos _).trans_le (hJ N hN).1
  have hc := hcap (scaledLogTemperature b N γ) N hN
  change _ ≤ C*Real.exp (C*max ((b : ℝ)*(N : ℝ)^γ-(B : ℝ)) 0*
    Real.log (Real.exp 1+(N : ℝ))) at hc
  have hb' : (b : ℝ) ≤ (B : ℝ) := by exact_mod_cast hb
  refine ⟨fun hγ => temperature_scaling_log_small C (B : ℝ) _ (b : ℝ) _ _ hC B.coe_nonneg
    b.coe_nonneg hb' (Real.rpow_le_one_of_one_le_of_nonpos hn hγ) hp hc, ?_⟩
  intro hγ
  have ha : 1 ≤ Real.log (Real.exp 1+(N : ℝ)) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  exact temperature_scaling_log_large C (B : ℝ) _ (b : ℝ) _ _ hC B.coe_nonneg ha
    b.coe_nonneg hb' (Real.one_le_rpow hn hγ.le) hp hc

theorem sourceRieszPartition_temperature_scaling (s B : ℝ) (hs : 0 < s) (hB : 0 < B)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ γ b : ℝ, 0 ≤ b → b ≤ B → ∀ N : ℕ, 1 ≤ N →
      (γ ≤ 0 → Real.log (sourceRieszSingularPartition s (b*(N : ℝ)^γ) ρ N).toReal ≤ D) ∧
      (0 < γ → Real.log (sourceRieszSingularPartition s (b*(N : ℝ)^γ) ρ N).toReal ≤
        D*(N : ℝ)^(γ+s/(Fintype.card ι : ℝ))) := by
  obtain ⟨C, hC, hcap⟩ := sourceRieszPartition_all_temperature_growth s B hs hB ha ρ M hM hρ
  refine ⟨C*(1+B), by nlinarith [hB.le], ?_⟩
  intro γ b hb hbB N hN
  have hn : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hnp : 0 < (N : ℝ) := by linarith
  have hβ : 0 ≤ b*(N : ℝ)^γ := mul_nonneg hb (Real.rpow_nonneg hnp.le γ)
  have hp : 0 < (sourceRieszSingularPartition s (b*(N : ℝ)^γ) ρ N).toReal := by
    rw [sourceRieszSingularPartition_eq_integral s _ hs hβ ha ρ M hM hρ N]
    unfold DGRHS.Concentration.physicalRieszSourcePartition
    rw [ENNReal.toReal_ofReal (integral_nonneg fun x => (Real.exp_pos _).le)]
    exact integral_exp_pos (sourceRieszEnergyWeight_integrable s _ hs hβ ha ρ M hM hρ N)
  have hc := hcap _ hβ N hN
  refine ⟨fun hγ => temperature_scaling_log_small C B _ b _ _ hC hB.le hb hbB
    (Real.rpow_le_one_of_one_le_of_nonpos hn hγ) hp hc, ?_⟩
  intro hγ
  have hd : 0 < (Fintype.card ι : ℝ) := by linarith
  have hap : 1 ≤ (N : ℝ)^(s/(Fintype.card ι : ℝ)) :=
    Real.one_le_rpow hn (div_nonneg hs.le hd.le)
  have hh := temperature_scaling_log_large C B _ b _ _ hC hB.le hap hb hbB
    (Real.one_le_rpow hn hγ.le) hp hc
  rw [Real.rpow_add hnp]
  nlinarith [hh]

end DGRHS.Entropy
#check @DGRHS.Entropy.temperature_scaling_log_small
#check @DGRHS.Entropy.temperature_scaling_log_large
#check @DGRHS.Entropy.sourceLogPartition_temperature_scaling
#check @DGRHS.Entropy.sourceRieszPartition_temperature_scaling
#print axioms DGRHS.Entropy.temperature_scaling_log_small
#print axioms DGRHS.Entropy.temperature_scaling_log_large
#print axioms DGRHS.Entropy.sourceLogPartition_temperature_scaling
#print axioms DGRHS.Entropy.sourceRieszPartition_temperature_scaling
