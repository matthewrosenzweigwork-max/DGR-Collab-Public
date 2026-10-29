import DGRHS.Concentration.ConditionalRosenthal

noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Concentration

lemma kernel_column_joint_bounded {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n r : ℕ} (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) (j : Fin r) :
    AEStronglyMeasurable (fun p : (Fin n → Ω) × Ψ ↦ kernelColumnSum h p.1 j p.2)
      ((Measure.pi μ).prod (ν j)) ∧
    (∀ᵐ p ∂(Measure.pi μ).prod (ν j), |kernelColumnSum h p.1 j p.2| ≤ (n : ℝ)*A) := by
  classical
  have hp : ∀ i, MeasurePreserving (fun p : (Fin n → Ω) × Ψ ↦ (p.1 i,p.2))
      ((Measure.pi μ).prod (ν j)) ((μ i).prod (ν j)) := fun i ↦
    (measurePreserving_pi_coordinate μ i).prod (MeasurePreserving.id (ν j))
  have hm : ∀ i, AEStronglyMeasurable (fun p : (Fin n → Ω) × Ψ ↦ h i j (p.1 i,p.2))
      ((Measure.pi μ).prod (ν j)) := fun i ↦
    (hAES i j).comp_quasiMeasurePreserving (hp i).quasiMeasurePreserving
  have hb : ∀ᵐ p ∂(Measure.pi μ).prod (ν j), ∀ i, |h i j (p.1 i,p.2)| ≤ A :=
    ae_all_iff.mpr fun i ↦ (hp i).quasiMeasurePreserving.ae (hBound i j)
  have hi : ∀ i, Integrable (fun p : (Fin n → Ω) × Ψ ↦ h i j (p.1 i,p.2))
      ((Measure.pi μ).prod (ν j)) := fun i ↦ integrable_of_ae_abs_le (hm i)
        (hb.mono fun p h ↦ h i)
  constructor
  · change AEStronglyMeasurable (fun p : (Fin n → Ω) × Ψ ↦ ∑ i, h i j (p.1 i,p.2)) _
    simpa only [Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).aestronglyMeasurable
  · filter_upwards [hb] with p hpb
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hpb i)))

lemma kernel_column_joint_moment_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) (j : Fin r) (m : ℕ) :
    Integrable (fun p : (Fin n → Ω) × Ψ ↦ |kernelColumnSum h p.1 j p.2|^m)
      ((Measure.pi μ).prod (ν j)) := by
  obtain ⟨hm,hb⟩ := kernel_column_joint_bounded μ ν h A hAES hBound j
  have ha : AEStronglyMeasurable (fun p : (Fin n → Ω) × Ψ ↦
      |kernelColumnSum h p.1 j p.2|) ((Measure.pi μ).prod (ν j)) := by
    simpa only [Real.norm_eq_abs] using hm.norm
  apply integrable_of_ae_abs_le (ha.fun_pow m)
  filter_upwards [hb] with p hp
  rw [abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hp m

lemma nonnegative_add_power_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    (a+b)^m ≤ (2*a)^m+(2*b)^m := by
  rcases le_total a b with hab | hba
  · have ht : a+b ≤ 2*b := by linarith
    exact (pow_le_pow_left₀ (by positivity) ht m).trans
      (le_add_of_nonneg_left (by positivity))
  · have ht : a+b ≤ 2*a := by linarith
    exact (pow_le_pow_left₀ (by positivity) ht m).trans
      (le_add_of_nonneg_right (by positivity))

lemma rosenthal_root_to_power {Q v M : ℝ} (hQ : 0 ≤ Q) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (k : ℕ) (hk : 1 ≤ k)
    (ht : Q^(1/((2*k : ℕ) : ℝ)) ≤
      3*(Real.sqrt ((2*k : ℕ) : ℝ)*Real.sqrt v+
        ((2*k : ℕ) : ℝ)*M^(1/((2*k : ℕ) : ℝ)))) :
    Q ≤ (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k)*v^k+
      (6*((2*k : ℕ) : ℝ))^(2*k)*M := by
  let m := 2*k
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by dsimp [m]; omega)
  have hmne : m ≠ 0 := by dsimp [m]; omega
  let a := Real.sqrt (m : ℝ)*Real.sqrt v
  let b := (m : ℝ)*M^(1/(m : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpower : Q ≤ (3*(a+b))^m := by
    have hq := (Real.rpow_inv_le_iff_of_pos hQ (by positivity : 0 ≤ 3*(a+b)) hmpos).mp
      (by simpa only [m,a,b,one_div] using ht)
    simpa only [Real.rpow_natCast] using hq
  have hadd := nonnegative_add_power_le a b ha hb m
  have he : (Real.sqrt v)^m = v^k := by
    dsimp [m]
    rw [pow_mul, Real.sq_sqrt hv]
  have hMpow : (M^(1/(m : ℝ)))^m = M := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hM hmne
  change Q ≤ (6*Real.sqrt (m : ℝ))^m*v^k+(6*(m : ℝ))^m*M
  calc
    Q ≤ (3*(a+b))^m := hpower
    _ ≤ (3:ℝ)^m*((2*a)^m+(2*b)^m) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = _ := by
      dsimp [a,b]
      rw [mul_add, ← mul_pow, ← mul_pow]
      rw [show (6 : ℝ) = 3*2 by norm_num]
      simp only [mul_assoc, mul_pow, he, hMpow]

def kernelColumnVariance {Ω Ψ : Type*} [MeasurableSpace Ψ] {n r : ℕ}
    (ν : Fin r → Measure Ψ) (h : Fin n → Fin r → Ω × Ψ → ℝ) (ω : Fin n → Ω) : ℝ :=
  ∑ j, ∫ y, (kernelColumnSum h ω j y)^2 ∂ν j

def kernelDecoupledSum {Ω Ψ : Type*} {n r : ℕ}
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (p : (Fin n → Ω) × (Fin r → Ψ)) : ℝ :=
  ∑ j, kernelColumnSum h p.1 j (p.2 j)

lemma kernel_column_variance_power_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMean : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0) (k : ℕ) :
    Integrable (fun ω ↦ (kernelColumnVariance ν h ω)^k) (Measure.pi μ) := by
  classical
  have hj : ∀ j, Integrable (fun p : (Fin n → Ω) × Ψ ↦
      (kernelColumnSum h p.1 j p.2)^2) ((Measure.pi μ).prod (ν j)) := fun j ↦ by
    simpa only [sq_abs] using kernel_column_joint_moment_integrable μ ν h A hAES hBound j 2
  have hm : AEStronglyMeasurable (kernelColumnVariance ν h) (Measure.pi μ) := by
    change AEStronglyMeasurable (fun ω ↦ ∑ j, ∫ y, (kernelColumnSum h ω j y)^2 ∂ν j) _
    simpa only [Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun j _ ↦ (hj j).integral_prod_left)).aestronglyMeasurable
  have hb : ∀ᵐ ω ∂Measure.pi μ,
      |kernelColumnVariance ν h ω| ≤ (r : ℝ)*((n : ℝ)*A)^2 := by
    filter_upwards [kernel_column_sections μ ν h A hAES hBound hMean] with ω hω
    have hOne : ∀ j, (∫ y, (kernelColumnSum h ω j y)^2 ∂ν j) ≤ ((n : ℝ)*A)^2 := by
      intro j
      have hi : Integrable (fun y ↦ (kernelColumnSum h ω j y)^2) (ν j) := by
        apply integrable_of_ae_abs_le ((hω j).1.fun_pow 2)
        filter_upwards [(hω j).2.1] with y hy
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      simpa using integral_mono_ae hi (integrable_const (((n : ℝ)*A)^2))
        ((hω j).2.1.mono fun y hy ↦ by simpa only [sq_abs] using
          (pow_le_pow_left₀ (abs_nonneg _) hy 2))
    have hn : 0 ≤ kernelColumnVariance ν h ω := Finset.sum_nonneg fun j _ ↦
      integral_nonneg fun y ↦ sq_nonneg _
    rw [abs_of_nonneg hn]
    simpa [kernelColumnVariance] using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hOne j)
  apply integrable_of_ae_abs_le (hm.fun_pow k)
  filter_upwards [hb] with ω hω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω k

lemma kernel_decoupled_moment_integrable {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) (m : ℕ) :
    Integrable (fun p : (Fin n → Ω) × (Fin r → Ψ) ↦ |kernelDecoupledSum h p|^m)
      ((Measure.pi μ).prod (Measure.pi ν)) := by
  classical
  have hp : ∀ j, MeasurePreserving (fun p : (Fin n → Ω) × (Fin r → Ψ) ↦ (p.1,p.2 j))
      ((Measure.pi μ).prod (Measure.pi ν)) ((Measure.pi μ).prod (ν j)) := fun j ↦
    (MeasurePreserving.id (Measure.pi μ)).prod (measurePreserving_pi_coordinate ν j)
  have hj := fun j ↦ kernel_column_joint_bounded μ ν h A hAES hBound j
  have hm : ∀ j, AEStronglyMeasurable
      (fun p : (Fin n → Ω) × (Fin r → Ψ) ↦ kernelColumnSum h p.1 j (p.2 j))
      ((Measure.pi μ).prod (Measure.pi ν)) := fun j ↦
    (hj j).1.comp_quasiMeasurePreserving (hp j).quasiMeasurePreserving
  have hb : ∀ᵐ p ∂(Measure.pi μ).prod (Measure.pi ν), ∀ j,
      |kernelColumnSum h p.1 j (p.2 j)| ≤ (n : ℝ)*A :=
    ae_all_iff.mpr fun j ↦ (hp j).quasiMeasurePreserving.ae (hj j).2
  have hi : ∀ j, Integrable
      (fun p : (Fin n → Ω) × (Fin r → Ψ) ↦ kernelColumnSum h p.1 j (p.2 j))
      ((Measure.pi μ).prod (Measure.pi ν)) := fun j ↦
    integrable_of_ae_abs_le (hm j) (hb.mono fun p h ↦ h j)
  have hs : AEStronglyMeasurable (kernelDecoupledSum h) ((Measure.pi μ).prod (Measure.pi ν)) := by
    change AEStronglyMeasurable (fun p : (Fin n → Ω) × (Fin r → Ψ) ↦
      ∑ j, kernelColumnSum h p.1 j (p.2 j)) _
    simpa only [Finset.sum_apply] using
      (integrable_finsetSum Finset.univ (fun j _ ↦ hi j)).aestronglyMeasurable
  have hsb : ∀ᵐ p ∂(Measure.pi μ).prod (Measure.pi ν),
      |kernelDecoupledSum h p| ≤ (r : ℝ)*((n : ℝ)*A) := by
    filter_upwards [hb] with p hpb
    exact (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hpb j))
  have ha : AEStronglyMeasurable (fun p ↦ |kernelDecoupledSum h p|)
      ((Measure.pi μ).prod (Measure.pi ν)) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  apply integrable_of_ae_abs_le (ha.fun_pow m)
  filter_upwards [hsb] with p hp
  rw [abs_pow,abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hp m

/-- First conditional Rosenthal step integrated under the actual two-product law.
All joint moments and the variance-power integral are proved integrable before Fubini.
The factor6 is the elementary power-splitting adaptation, avoiding a Minkowski premise. -/
theorem integrated_kernel_rosenthal {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] {n r : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin r → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin r → Ω × Ψ → ℝ) (A : ℝ)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMean : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ p, |kernelDecoupledSum h p|^(2*k) ∂(Measure.pi μ).prod (Measure.pi ν)) ≤
      (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k)*
        (∫ ω, (kernelColumnVariance ν h ω)^k ∂Measure.pi μ) +
      (6*((2*k : ℕ) : ℝ))^(2*k)*
        (∑ j, ∫ p : (Fin n → Ω) × Ψ, |kernelColumnSum h p.1 j p.2|^(2*k)
          ∂(Measure.pi μ).prod (ν j)) := by
  classical
  have hFull := kernel_decoupled_moment_integrable μ ν h A hAES hBound (2*k)
  have hVar := kernel_column_variance_power_integrable μ ν h A hAES hBound hMean k
  have hCols := fun j ↦ kernel_column_joint_moment_integrable μ ν h A hAES hBound j (2*k)
  have hOuter := integrable_finsetSum Finset.univ (fun j _ ↦ (hCols j).integral_prod_left)
  have hp : ∀ᵐ ω ∂Measure.pi μ,
      (∫ ξ, |kernelDecoupledSum h (ω,ξ)|^(2*k) ∂Measure.pi ν) ≤
      (6*Real.sqrt ((2*k : ℕ) : ℝ))^(2*k)*(kernelColumnVariance ν h ω)^k +
      (6*((2*k : ℕ) : ℝ))^(2*k)*
        (∑ j, ∫ y, |kernelColumnSum h ω j y|^(2*k) ∂ν j) := by
    filter_upwards [conditional_kernel_rosenthal μ ν h A hAES hBound hMean k hk] with ω hω
    exact rosenthal_root_to_power
      (integral_nonneg fun ξ ↦ pow_nonneg (abs_nonneg _) _)
      (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ sq_nonneg _)
      (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ pow_nonneg (abs_nonneg _) _)
      k hk hω
  have hb := integral_mono_ae hFull.integral_prod_left
    ((hVar.const_mul _).add (hOuter.const_mul _)) hp
  rw [← integral_prod _ hFull] at hb
  simp only [Pi.add_apply] at hb
  rw [integral_add (hVar.const_mul _) (hOuter.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ ↦ (hCols j).integral_prod_left)] at hb
  simpa only [integral_prod _ (hCols _)] using hb

#print axioms DGRHS.Concentration.integrated_kernel_rosenthal
#print axioms DGRHS.Concentration.kernel_column_variance_power_integrable
#print axioms DGRHS.Concentration.kernel_decoupled_moment_integrable
#print axioms DGRHS.Concentration.kernel_column_joint_bounded
#print axioms DGRHS.Concentration.kernel_column_joint_moment_integrable
#print axioms DGRHS.Concentration.rosenthal_root_to_power
end DGRHS.Concentration
