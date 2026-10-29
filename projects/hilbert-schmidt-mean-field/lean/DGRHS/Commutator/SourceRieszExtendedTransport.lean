import DGRHS.Commutator.SourceRieszEntropicTransport
import Mathlib.Data.EReal.Operations

/-! Extended all-law absolute transport expectation. The nonnegative Lebesgue
integral retains infinity and is controlled by the actual literal Gibbs KL.
Finite KL gives proper transport expectation; infinite KL gives the genuine
extended bound, never a totalized signed Bochner expectation. The sharper
finite-KL signed source estimate remains in SourceRieszEntropicTransport. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sourceRieszTransport_allLaw_absolute (s M : ℝ) (n : ℕ) (hn : 1≤n)
    (hs : 0<s) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (β : ℝ) (hβ : 0<β)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    0<sourceRieszPositiveTransportParameter (ι:=ι) s M n K β ∧
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,1≤N→
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],
      ((∫⁻ ω,ENNReal.ofReal |(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω| ∂ν):EReal)≤
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹:ℝ)*
          (klDiv ν (DGRHS.CLT.sourceRieszSingularGibbs s β ρ N):EReal)+
        ((sourceRieszPositiveTransportParameter (ι:=ι) s M n K β)⁻¹*Real.log (2*C):ℝ) := by
  obtain ⟨hε,C,hC,hMom⟩ := sourceRieszTransport_positive_Gibbs_moment s M n hn hs hd hM β hβ hv ρ hρ
  refine ⟨hε,max C 1,le_max_right _ _,?_⟩
  intro N hN ν hν
  let ε := sourceRieszPositiveTransportParameter (ι:=ι) s M n K β
  have hεlocal : 0<ε := hε
  let Q := DGRHS.CLT.sourceRieszSingularGibbs s β ρ N
  let a := fun ω : Fin N→E=>(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω
  let u := fun ω=>ε*a ω
  change ((∫⁻ ω,ENNReal.ofReal |a ω| ∂ν):EReal)≤
    (ε⁻¹:ℝ)*(klDiv ν Q:EReal)+(ε⁻¹*Real.log (2*max C 1):ℝ)
  by_cases hfinite : klDiv ν Q≠∞
  · letI := DGRHS.CLT.sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
    have hu : StronglyMeasurable u :=
      (measurable_sourceRieszScaledTransportEnergy ρ s n hv N hN).stronglyMeasurable.const_mul ε
    have hp := hMom 1 (by norm_num) N hN
    have hm := hMom (-1) (by norm_num) N hN
    have heP (ω : Fin N→E) :
        1*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω=u ω := by dsimp [u,a,ε];ring
    have heM (ω : Fin N→E) :
        (-1)*sourceRieszPositiveTransportParameter (ι:=ι) s M n K β*(N:ℝ)*sourceRieszLocalTransportEnergy ρ s n v N ω= -u ω := by dsimp [u,a,ε];ring
    simp_rw [heP] at hp
    simp_rw [heM] at hm
    have hx := DGRHS.Entropy.integrable_exp_abs_of_two_signs Q u hu hp.1 hm.1
    have hpoint (ω : Fin N→E) : Real.exp |u ω|≤Real.exp (u ω)+Real.exp (-u ω) := by
      by_cases h : 0≤u ω
      · rw [abs_of_nonneg h]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge h)]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    have hb : (∫ ω,Real.exp |u ω| ∂Q)≤2*max C 1 := by
      calc
        _ ≤ ∫ ω,Real.exp (u ω)+Real.exp (-u ω) ∂Q := integral_mono hx (hp.1.add hm.1) hpoint
        _ = (∫ ω,Real.exp (u ω) ∂Q)+(∫ ω,Real.exp (-u ω) ∂Q) := integral_add hp.1 hm.1
        _ ≤ 2*max C 1 := by linarith [hp.2,hm.2,le_max_left C 1]
    obtain ⟨hi,hbound⟩ := DGRHS.Entropy.entropy_integrable_abs_of_exponential Q ν u hu hx hfinite
    have hia : Integrable a ν := by
      have h := hi.const_mul ε⁻¹
      simpa only [u,←mul_assoc,inv_mul_cancel₀ hεlocal.ne',one_mul] using h
    have huabs (ω : Fin N→E) : |u ω|=ε*|a ω| := by
      dsimp only [u]
      rw [abs_mul,abs_of_pos hε]
    have hInt : (∫ ω,|u ω| ∂ν)=ε*(∫ ω,|a ω| ∂ν) := by
      simp_rw [huabs]
      exact integral_const_mul _ _
    rw [hInt] at hbound
    have hlog := Real.log_le_log (integral_exp_pos hx) hb
    have hbound' : (∫ ω,|a ω| ∂ν)≤ε⁻¹*((klDiv ν Q).toReal+Real.log (2*max C 1)) := by
      have ht := hbound.trans (add_le_add le_rfl hlog)
      have h : (∫ ω,|a ω| ∂ν)≤((klDiv ν Q).toReal+Real.log (2*max C 1))/ε :=
        (le_div_iff₀ hεlocal).mpr (by simpa only [mul_comm] using ht)
      simpa only [div_eq_mul_inv,mul_comm] using h
    rw [←ofReal_integral_eq_lintegral_ofReal hia.abs (ae_of_all _ fun ω=>abs_nonneg _),
      EReal.coe_ennreal_ofReal,max_eq_left (integral_nonneg (fun ω=>abs_nonneg _)),
      ←EReal.coe_ennreal_toReal hfinite,←EReal.coe_mul,←EReal.coe_add]
    apply EReal.coe_le_coe_iff.mpr
    simpa only [mul_add] using hbound'
  · have htop : klDiv ν Q=∞ := not_ne_iff.mp hfinite
    rw [htop,EReal.coe_ennreal_top,EReal.coe_mul_top_of_pos (inv_pos.mpr hε),EReal.top_add_coe]
    exact le_top

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszTransport_allLaw_absolute
#print axioms DGRHS.Commutator.sourceRieszTransport_allLaw_absolute
