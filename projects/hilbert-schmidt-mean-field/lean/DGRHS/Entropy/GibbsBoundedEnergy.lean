/- Proper extended expectation for an energy bounded below: infinite KL and
infinite shifted energy are preserved. Positive temperature is indispensable. -/
import DGRHS.Entropy.GibbsExtendedVariational
import Mathlib.Data.EReal.Inv
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DGRHS.Entropy

def boundedEnergyFreeEnergy {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (E : Ω→ℝ) (L b : ℝ) : EReal :=
  (klDiv ν μ : EReal)*(b⁻¹ : ℝ)+( (∫⁻ x,ENNReal.ofReal (E x-L) ∂ν : ℝ≥0∞):EReal)+(L : EReal)

theorem boundedEnergyFreeEnergy_eq_scaledGibbs {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (E : Ω→ℝ) (L b : ℝ) (hb : 0<b) :
    boundedEnergyFreeEnergy μ ν E L b=
      gibbsExtendedFreeEnergy μ ν (fun x=>-b*E x) (-b*L)*(b⁻¹ : ℝ) := by
  have hi : (∫⁻ x,ENNReal.ofReal (-b*L-(-b*E x)) ∂ν)=
      ENNReal.ofReal b*(∫⁻ x,ENNReal.ofReal (E x-L) ∂ν) := by
    have he (x : Ω) : -b*L-(-b*E x)=b*(E x-L) := by ring
    simp_rw [he,ENNReal.ofReal_mul hb.le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hc : ((-b*L)*b⁻¹ : ℝ)=-L := by field_simp [hb.ne'] <;> ring
  have hcoeff : ((b : EReal)*( (∫⁻ x,ENNReal.ofReal (E x-L) ∂ν : ℝ≥0∞):EReal))*(b⁻¹ : ℝ)=
      ((∫⁻ x,ENNReal.ofReal (E x-L) ∂ν : ℝ≥0∞):EReal) := by
    calc
      _ = ((∫⁻ x,ENNReal.ofReal (E x-L) ∂ν : ℝ≥0∞):EReal)*((b:EReal)*(b⁻¹ : ℝ)) := by ac_rfl
      _ = _ := by rw [←EReal.coe_mul,mul_inv_cancel₀ hb.ne'];simp
  unfold boundedEnergyFreeEnergy gibbsExtendedFreeEnergy
  rw [hi,EReal.sub_mul_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (inv_nonneg.mpr hb.le)) (EReal.coe_ne_top _),
    EReal.coe_ennreal_add,EReal.coe_ennreal_mul,EReal.coe_ennreal_ofReal,max_eq_left hb.le,
    EReal.right_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr (inv_nonneg.mpr hb.le)) (EReal.coe_ne_top _),
    hcoeff,←EReal.coe_mul,hc,EReal.coe_neg]
  simp only [sub_eq_add_neg,neg_neg]

theorem boundedEnergyFreeEnergy_eq_proper {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure ν] (E : Ω→ℝ) (L b : ℝ)
    (hL : ∀ x,L≤E x) (hE : Integrable E ν) (hK : klDiv ν μ≠∞) :
    boundedEnergyFreeEnergy μ ν E L b=
      (((klDiv ν μ).toReal/b+∫ x,E x ∂ν : ℝ):EReal) := by
  have ht : Integrable (fun x=>E x-L) ν := hE.sub (integrable_const L)
  have hp : ∀ᵐ x ∂ν,0≤E x-L := Filter.Eventually.of_forall fun x=>sub_nonneg.mpr (hL x)
  have hi : (∫⁻ x,ENNReal.ofReal (E x-L) ∂ν)=ENNReal.ofReal ((∫ x,E x ∂ν)-L) := by
    rw [←ofReal_integral_eq_lintegral_ofReal ht hp,integral_sub hE (integrable_const L)]
    simp
  have hv : 0≤(∫ x,E x ∂ν)-L := by
    have h := integral_nonneg_of_ae hp
    rw [integral_sub hE (integrable_const L)] at h
    simpa using h
  unfold boundedEnergyFreeEnergy
  rw [hi,←EReal.coe_ennreal_toReal hK,EReal.coe_ennreal_ofReal,max_eq_left hv,
    ←EReal.coe_mul,←EReal.coe_add,←EReal.coe_add]
  congr 1
  simp only [div_eq_mul_inv]
  ring

def boundedEnergyValues {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Ω→ℝ) (L b : ℝ) : Set EReal :=
  {r | ∃ ν : Measure Ω, IsProbabilityMeasure ν ∧ r=boundedEnergyFreeEnergy μ ν E L b}

theorem boundedEnergyFreeEnergy_isLeast {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω→ℝ) (L b : ℝ)
    (hb : 0<b) (hL : ∀ x,L≤E x)
    (hexp : Integrable (fun x=>Real.exp (-b*E x)) μ) :
    IsLeast (boundedEnergyValues μ E L b)
      ((-Real.log (∫ x,Real.exp (-b*E x) ∂μ)/b : ℝ):EReal) := by
  let u := fun x=>-b*E x
  have hcap : ∀ x,u x≤-b*L := fun x=>mul_le_mul_of_nonpos_left (hL x) (by linarith)
  have hopt := gibbsExtended_isLeast μ u (-b*L) hcap hexp
  letI := isProbabilityMeasure_tilted hexp
  have hf : (-Real.log (∫ x,Real.exp (-b*E x) ∂μ)/b : ℝ)=
      (-Real.log (∫ x,Real.exp (-b*E x) ∂μ))*b⁻¹ := div_eq_mul_inv _ _
  refine ⟨?_,?_⟩
  · refine ⟨μ.tilted u,inferInstance,?_⟩
    rw [boundedEnergyFreeEnergy_eq_scaledGibbs μ (μ.tilted u) E L b hb,
      gibbsExtendedFreeEnergy_rewrite μ (μ.tilted u) u (-b*L) hcap hexp,klDiv_self]
    simp only [EReal.coe_ennreal_zero,zero_sub,←EReal.coe_neg,←EReal.coe_mul]
    rw [hf]
  · intro r hr
    obtain ⟨ν,hν,hr⟩ := hr
    rw [hr,boundedEnergyFreeEnergy_eq_scaledGibbs μ ν E L b hb,hf,EReal.coe_mul]
    exact mul_le_mul_of_nonneg_right (hopt.2 ⟨ν,hν,rfl⟩)
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr hb.le))

theorem boundedEnergyFreeEnergy_inf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Ω→ℝ) (L b : ℝ)
    (hb : 0<b) (hL : ∀ x,L≤E x)
    (hexp : Integrable (fun x=>Real.exp (-b*E x)) μ) :
    sInf (boundedEnergyValues μ E L b)=
      ((-Real.log (∫ x,Real.exp (-b*E x) ∂μ)/b : ℝ):EReal) :=
  (boundedEnergyFreeEnergy_isLeast μ E L b hb hL hexp).csInf_eq
end DGRHS.Entropy
#check @DGRHS.Entropy.boundedEnergyFreeEnergy_eq_scaledGibbs
#print axioms DGRHS.Entropy.boundedEnergyFreeEnergy_eq_scaledGibbs
#check @DGRHS.Entropy.boundedEnergyFreeEnergy_isLeast
#print axioms DGRHS.Entropy.boundedEnergyFreeEnergy_isLeast
#check @DGRHS.Entropy.boundedEnergyFreeEnergy_inf
#print axioms DGRHS.Entropy.boundedEnergyFreeEnergy_inf

#check @DGRHS.Entropy.boundedEnergyFreeEnergy_eq_proper
#print axioms DGRHS.Entropy.boundedEnergyFreeEnergy_eq_proper
