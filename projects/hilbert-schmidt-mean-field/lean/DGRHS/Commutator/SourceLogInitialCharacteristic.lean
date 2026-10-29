import DGRHS.Commutator.SourceLogPhysicalFiniteCF
import DGRHS.CLT.SourceLogLiteralStatic

/-! Logarithmic adaptation of proof-b SourceRieszInitialCharacteristic.
Source4003--4007 on the ACTUAL initial sample with the literal Gibbs
law. Native L2 representatives are identified almost everywhere under iid,
then under the absolutely continuous physical Gibbs law. The same initial
sample map carries this identity back to the particle probability space.
No initial characteristic-function convergence premise is supplied. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators RealInnerProductSpace NNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_sourceLog_empirical_fluctuation (ρ q : E→ℝ)
    (hq : Measurable q) (N : ℕ) :
    Measurable (fun x : Fin N→E=>Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ q N x) := by
  change Measurable (fun x : Fin N→E=>Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ q N x)
  unfold sourceRieszDynamicEmpiricalDifference
  simp_rw [integral_sourceRieszLocalEmpiricalLaw]
  exact (((Finset.measurable_sum _ fun i _=>hq.comp (measurable_pi_apply i)).const_mul _).sub
    measurable_const).const_mul _

theorem sourceLog_L2_raw_fluctuation_ae (β : ℝ≥0) (ρ : E→ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (k : ℕ) (φ : Fin k→E→ℝ) (hφ : ∀ a,MemLp (φ a) 2 (gaussianRieszDensityMeasure ρ))
    (N : ℕ) :
    (fun x : Fin N→E=>sourceObservableFluctuation (fun a=>(hφ a).toLp (φ a)) N x)
      =ᵐ[sourceLogSingularGibbs β ρ N]
    (fun x a=>Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ (φ a) N x) := by
  let μ := gaussianRieszDensityMeasure ρ
  have he (a : Fin k) (i : Fin N) : ∀ᵐ x ∂Measure.pi (fun _ : Fin N=>μ),
      (hφ a).toLp (φ a) (x i)=φ a (x i) :=
    (measurePreserving_eval (fun _ : Fin N=>μ) i).quasiMeasurePreserving.ae (hφ a).coeFn_toLp
  have hm (a : Fin k) : (∫ z,(hφ a).toLp (φ a) z ∂μ)=∫ z,φ a z ∂μ :=
    integral_congr_ae (hφ a).coeFn_toLp
  have hid : (fun x : Fin N→E=>sourceObservableFluctuation (fun a=>(hφ a).toLp (φ a)) N x)
      =ᵐ[Measure.pi (fun _ : Fin N=>μ)]
      (fun x a=>Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ (φ a) N x) := by
    filter_upwards [ae_all_iff.mpr (fun a=>ae_all_iff.mpr (he a))] with x hx
    funext a
    unfold sourceObservableFluctuation sourceLogDynamicEmpiricalDifference
    rw [show transportEmpiricalLaw N x=sourceRieszLocalEmpiricalLaw N x from rfl]
    rw [integral_sourceRieszLocalEmpiricalLaw,hm a]
    simp_rw [hx a]
    rfl
  exact (withDensity_absolutelyContinuous _ _).ae_le hid

theorem exists_sourceLog_raw_initial_characteristic
    (k : ℕ) (β : ℝ≥0) (hd : 0<(Fintype.card ι:ℝ)) (ρ : E→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ z ∂volume,ρ z≤M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let h := hoeffdingCentered μ logPhysicalPair
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+(β:ℝ) • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ (φ : Fin k→E→ℝ),(∀ a,Measurable (φ a)) →
      ∀ (hφ : ∀ a,MemLp (φ a) 2 μ),
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (X₀ : ∀ N,Ω N→Fin N→E),(∀ N,Measurable (X₀ N)) →
      (∀ N,1≤N → (ν N).map (X₀ N)=sourceLogSingularGibbs β ρ N) →
      ∀ θ : Fin k→ℝ,Tendsto (fun N=>∫ ω,sourceRieszFinitePhase
        (∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ (φ a) N (X₀ N ω))) ∂ν N)
        atTop (𝓝 (Complex.exp (-(∑ a,∑ b,θ a*θ b*
          ⟪sourceCenteredL2 ((hφ a).toLp (φ a)),R0 (sourceCenteredL2 ((hφ b).toLp (φ b)))⟫ : ℝ)/2))) := by
  obtain ⟨hSym,hCan,R0,hR1,hR2,hfactory⟩ := exists_sourceLogSingularStatic
    k β hd ρ M hM hρ hpair
  refine ⟨hSym,hCan,R0,hR1,hR2,?_⟩
  intro φ hφm hφ Ω _ ν _ X₀ hX₀ hLaw θ
  obtain ⟨P,Z,hP,hPN,_,_,_,_,hCF,_⟩ := hfactory (fun a=>(hφ a).toLp (φ a))
  apply (hCF θ).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  let V := fun x : Fin N→E=>sourceRieszFinitePhase
    (∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ (φ a) N x))
  have hV : Measurable V := measurable_sourceRieszFinitePhase.comp
    (Finset.measurable_sum _ fun a _=>(measurable_sourceLog_empirical_fluctuation ρ (φ a) (hφm a) N).const_mul _)
  calc
    _ = ∫ x,V x ∂sourceLogSingularGibbs β ρ N := by
      apply integral_congr_ae
      filter_upwards [sourceLog_L2_raw_fluctuation_ae β ρ k φ hφ N] with x hx
      change Complex.exp ((∑ a,θ a*sourceObservableFluctuation (fun a=>(hφ a).toLp (φ a)) N x a : ℝ)*Complex.I)=_
      have hh := congrFun hx
      simp_rw [hh]
      simp only [V,sourceRieszFinitePhase,mul_comm]
    _ = ∫ ω,V (X₀ N ω) ∂ν N := by
      rw [←hLaw N hN,integral_map (hX₀ N).aemeasurable hV.aestronglyMeasurable]

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.measurable_sourceLog_empirical_fluctuation
#print axioms DGRHS.Commutator.measurable_sourceLog_empirical_fluctuation
#check @DGRHS.Commutator.sourceLog_L2_raw_fluctuation_ae
#print axioms DGRHS.Commutator.sourceLog_L2_raw_fluctuation_ae
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceLog_raw_initial_characteristic
#print axioms DGRHS.Commutator.exists_sourceLog_raw_initial_characteristic
