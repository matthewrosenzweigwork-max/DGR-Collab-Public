/- Genuine mean-centering of every original L2 observable. The particle
readout is the source sqrt(N) empirical fluctuation, with all-N conventions. -/
import DGRHS.Kernel.MeanZeroSpace
import Mathlib.MeasureTheory.Integral.Pi
noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators
namespace DGRHS.Kernel
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

def centeredL2 (v : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  v - (∫ x, v x ∂μ) • oneL2

lemma inner_oneL2_oneL2 : inner ℝ (oneL2 (μ := μ)) oneL2 = 1 := by
  rw [inner_oneL2_eq_integral]
  calc
    _ = ∫ _x, (1 : ℝ) ∂μ := integral_congr_ae oneL2_coeFn
    _ = 1 := by simp

lemma centeredL2_mem_meanZero (v : Lp ℝ 2 μ) : centeredL2 v ∈ meanZeroL2 μ := by
  change inner ℝ (oneL2 (μ := μ)) (centeredL2 v) = 0
  simp only [centeredL2,inner_sub_right,real_inner_smul_right,
    inner_oneL2_eq_integral,show (∫ x, (oneL2 (μ := μ)) x ∂μ) = 1 by
      rw [←inner_oneL2_eq_integral,inner_oneL2_oneL2],mul_one,sub_self]

def sourceCenteredL2 (v : Lp ℝ 2 μ) : meanZeroL2 μ :=
  ⟨centeredL2 v, centeredL2_mem_meanZero v⟩

lemma centeredL2_coeFn (v : Lp ℝ 2 μ) :
    (centeredL2 v : S → ℝ) =ᵐ[μ] fun x => v x - ∫ y, v y ∂μ := by
  filter_upwards [Lp.coeFn_sub v ((∫ y, v y ∂μ) • oneL2),
    Lp.coeFn_smul (∫ y, v y ∂μ) (oneL2 (μ := μ)),oneL2_coeFn (μ := μ)] with x hsub hsmul hone
  change (v - (∫ y, v y ∂μ) • oneL2 : Lp ℝ 2 μ) x = _
  simp only [hsub,Pi.sub_apply,hsmul,Pi.smul_apply,smul_eq_mul,hone,mul_one]

lemma centeredL2_integral_zero (v : Lp ℝ 2 μ) : (∫ x, centeredL2 v x ∂μ) = 0 :=
  (mem_meanZeroL2_iff _).mp (centeredL2_mem_meanZero v)

lemma fluctuation_normalization (N : ℕ) (z m : ℝ) :
    (Real.sqrt N)⁻¹*(z-(N : ℝ)*m) = Real.sqrt N*((N : ℝ)⁻¹*z-m) := by
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hs : Real.sqrt N ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hN))
    have hsq := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hsq' : (N : ℝ) = Real.sqrt N*Real.sqrt N := by nlinarith only [hsq]
    have hscale : (Real.sqrt N)⁻¹*(N : ℝ) = Real.sqrt N := by
      calc
        _ = (Real.sqrt N)⁻¹*(Real.sqrt N*Real.sqrt N) :=
          congrArg (fun t => (Real.sqrt N)⁻¹*t) hsq'
        _ = _ := by rw [←mul_assoc,inv_mul_cancel₀ hs,one_mul]
    have hcoef : (Real.sqrt N)⁻¹ = Real.sqrt N*(N : ℝ)⁻¹ := by
      calc
        _ = ((Real.sqrt N)⁻¹*(N : ℝ))*(N : ℝ)⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ hn,mul_one]
        _ = _ := by rw [hscale]
    calc
      _ = (Real.sqrt N)⁻¹*z-((Real.sqrt N)⁻¹*(N : ℝ))*m := by ring
      _ = _ := by rw [hscale,hcoef]; ring

theorem particle_centeredL2_fluctuation (v : Lp ℝ 2 μ) (N : ℕ) :
    (fun x : Fin N → S => (Real.sqrt N)⁻¹*∑ i : Fin N, centeredL2 v (x i))
      =ᵐ[Measure.pi (fun _ : Fin N => μ)]
    fun x => Real.sqrt N*((N : ℝ)⁻¹*∑ i : Fin N, v (x i) - ∫ y, v y ∂μ) := by
  have he : ∀ i : Fin N, ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      centeredL2 v (x i) = v (x i) - ∫ y, v y ∂μ :=
    fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae
      (centeredL2_coeFn v)
  filter_upwards [ae_all_iff.mpr he] with x hx
  simp_rw [hx]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact fluctuation_normalization N _ _
end DGRHS.Kernel
#print axioms DGRHS.Kernel.centeredL2_mem_meanZero
#print axioms DGRHS.Kernel.centeredL2_coeFn
#print axioms DGRHS.Kernel.centeredL2_integral_zero
#print axioms DGRHS.Kernel.fluctuation_normalization
#print axioms DGRHS.Kernel.particle_centeredL2_fluctuation
#check @DGRHS.Kernel.particle_centeredL2_fluctuation
