/- Original final entropic-commutator reduction, source3533-3540.
Finite Gibbs entropy derives the proper energy/base-entropy domain when the
physical energy is bounded below. Actual physical exponential moments remain
upstream obligations; no desired commutator or free-energy bound is assumed. -/
import DGRHS.Entropy.GibbsFiniteDomain
import DGRHS.Entropy.ExponentialTransfer
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

theorem gibbs_entropic_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (E : Ω→ℝ) (L b : ℝ) (hb : 0<b) (hL : ∀ x,L≤E x)
    (hZ : Integrable (fun x=>Real.exp (-b*E x)) μ)
    (a : Ω→ℝ) (ha : StronglyMeasurable a) (ε : ℝ) (hε : 0<ε)
    (hp : Integrable (fun x=>Real.exp (ε*a x)) (μ.tilted (fun x=>-b*E x)))
    (hm : Integrable (fun x=>Real.exp (-(ε*a x))) (μ.tilted (fun x=>-b*E x)))
    (hKL : klDiv ν (μ.tilted (fun x=>-b*E x))≠∞)
    (Cpf Cem : ℝ) (hCpf : (∫ x,Real.exp (-b*E x) ∂μ)≤Cpf)
    (hCp : (∫ x,Real.exp (ε*a x) ∂μ.tilted (fun x=>-b*E x))≤Cem)
    (hCm : (∫ x,Real.exp (-(ε*a x)) ∂μ.tilted (fun x=>-b*E x))≤Cem) :
    ν ≪ μ ∧ Integrable E ν ∧ Integrable (llr ν μ) ν ∧ Integrable a ν ∧
      |∫ x,a x ∂ν|≤ε⁻¹*((klDiv ν μ).toReal+b*(∫ x,E x ∂ν))+
        ε⁻¹*(Real.log Cpf+Real.log Cem) := by
  let u := fun x=>-b*E x
  letI := isProbabilityMeasure_tilted hZ
  have hcap : ∀ x,u x≤-b*L :=
    fun x=>mul_le_mul_of_nonpos_left (hL x) (by linarith)
  obtain ⟨hac,hu,hllr⟩ := (gibbsKL_finite_domain μ ν u (-b*L) hcap hZ).mp hKL
  have hE : Integrable E ν := by
    have h := hu.const_mul (-b)⁻¹
    convert h using 1
    funext x
    dsimp only [u]
    field_simp [hb.ne']
  have he := (gibbsEntropy_rewrite μ ν u hac hu hZ hllr).2
  have hi : (∫ x,u x ∂ν)=-b*(∫ x,E x ∂ν) := integral_const_mul _ _
  rw [hi] at he
  obtain ⟨hai,hbound⟩ := entropy_abs_scaled_of_two_exponential_bounds
    (μ.tilted u) ν a ha ε hε hp hm hKL Cem hCp hCm
  have hlog := Real.log_le_log (integral_exp_pos hZ) hCpf
  rw [he] at hbound
  refine ⟨hac,hE,hllr,hai,?_⟩
  calc
    |∫ x,a x ∂ν|≤ε⁻¹*((klDiv ν μ).toReal-(∫ x,u x ∂ν)+
        Real.log (∫ x,Real.exp (u x) ∂μ)+Real.log Cem) := by
      rw [hi]
      exact hbound
    _ ≤ ε⁻¹*((klDiv ν μ).toReal+b*(∫ x,E x ∂ν))+
        ε⁻¹*(Real.log Cpf+Real.log Cem) := by
      rw [hi]
      have hm := mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hε.le)
      nlinarith

end DGRHS.Entropy
#check @DGRHS.Entropy.gibbs_entropic_transfer
#print axioms DGRHS.Entropy.gibbs_entropic_transfer
