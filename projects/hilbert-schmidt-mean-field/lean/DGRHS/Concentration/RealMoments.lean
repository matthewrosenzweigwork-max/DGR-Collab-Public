import DGRHS.Concentration.TailRate
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Concentration

lemma real_absolute_lp_root {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (p : ℝ) (hp : 0 < p)
    (hX : MemLp X (ENNReal.ofReal p) μ) :
    (eLpNorm X (ENNReal.ofReal p) μ).toReal = (∫ x, |X x|^p ∂μ)^(1/p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp [hp]
  rw [MemLp.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top hX]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofReal hp.le,Real.norm_eq_abs,one_div]

lemma real_absolute_moment_root_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q)
    (hXp : MemLp X (ENNReal.ofReal p) μ) (hXq : MemLp X (ENNReal.ofReal q) μ) :
    (∫ x, |X x|^p ∂μ)^(1/p) ≤ (∫ x, |X x|^q ∂μ)^(1/q) := by
  rw [← real_absolute_lp_root μ X p hp hXp,← real_absolute_lp_root μ X q hq hXq]
  exact ENNReal.toReal_mono hXq.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq))

lemma kernel_decoupled_absolute_memLp {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) (p : ℝ≥0∞) :
    MemLp (fun ω ↦ |kernelDecoupledSum h ω|) p ((Measure.pi μ).prod (Measure.pi ν)) := by
  have hAbs : AEStronglyMeasurable (fun ω ↦ |kernelDecoupledSum h ω|)
      ((Measure.pi μ).prod (Measure.pi ν)) := by
    simpa using (kernel_decoupled_moment_integrable μ ν h A hAES hBound 1).aestronglyMeasurable
  have hMP : ∀ j, MeasurePreserving (fun ω : (Fin n → Ω) × (Fin q → Ψ) ↦ (ω.1,ω.2 j))
      ((Measure.pi μ).prod (Measure.pi ν)) ((Measure.pi μ).prod (ν j)) := fun j ↦
    (MeasurePreserving.id (Measure.pi μ)).prod (measurePreserving_pi_coordinate ν j)
  have hc : ∀ᵐ ω ∂(Measure.pi μ).prod (Measure.pi ν), ∀ j,
      |kernelColumnSum h ω.1 j (ω.2 j)| ≤ (n : ℝ)*A :=
    ae_all_iff.mpr fun j ↦ (hMP j).quasiMeasurePreserving.ae
      (kernel_column_joint_bounded μ ν h A hAES hBound j).2
  apply bounded_real_memLp hAbs (p := p)
  filter_upwards [hc] with ω hω
  rw [abs_abs]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hω j))

lemma kernel_decoupled_real_moment_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) (p : ℝ) (hp : 0 ≤ p) :
    Integrable (fun ω ↦ |kernelDecoupledSum h ω|^p) ((Measure.pi μ).prod (Measure.pi ν)) := by
  have hm := kernel_decoupled_absolute_memLp μ ν h A hAES hBound (ENNReal.ofReal p)
  simpa only [ENNReal.toReal_ofReal hp,Real.norm_eq_abs,abs_abs] using hm.integrable_norm_rpow'

/-- Every real moment exponent p>=1, with actual probability-law monotonicity. -/
theorem kernel_real_four_scale {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hRow : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (hTest : ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
      (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))), ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ D)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ ω, |kernelDecoupledSum h ω|^p ∂(Measure.pi μ).prod (Measure.pi ν))^(1/p) ≤
      13824*glzRealScale p A B C D := by
  have hp0 : 0 < p := by linarith
  let m := 2*Nat.ceil p
  have hm : p ≤ (m : ℝ) := by
    have hh := Nat.le_ceil p
    dsimp [m]
    push_cast
    linarith [show (0 : ℝ) ≤ (Nat.ceil p : ℝ) from Nat.cast_nonneg _]
  have hm0 : 0 < (m : ℝ) := hp0.trans_le hm
  have hk : 1 ≤ Nat.ceil p := Nat.one_le_ceil_iff.mpr hp0
  have hmono := real_absolute_moment_root_mono ((Measure.pi μ).prod (Measure.pi ν))
    (fun ω ↦ |kernelDecoupledSum h ω|) p (m : ℝ) hp0 hm0 hm
    (kernel_decoupled_absolute_memLp μ ν h A hAES hBound (ENNReal.ofReal p))
    (kernel_decoupled_absolute_memLp μ ν h A hAES hBound (ENNReal.ofReal (m : ℝ)))
  simp only [abs_abs,Real.rpow_natCast] at hmono
  have he := kernel_even_four_scale μ ν h A B C D hA hB hC hD hAES hBound
    hMeanRight hMeanLeft hRow hColumn hTrace hTest (Nat.ceil p) hk
  have hscale := glz_scale_even_ceil_le p A B C D hp hA hB hC hD
  have hs := mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 864)
  have ht := hmono.trans he
  exact ht.trans (by nlinarith [hs])

#print axioms DGRHS.Concentration.real_absolute_moment_root_mono
#print axioms DGRHS.Concentration.kernel_decoupled_real_moment_integrable
#print axioms DGRHS.Concentration.kernel_real_four_scale
#check @DGRHS.Concentration.kernel_real_four_scale
end DGRHS.Concentration
