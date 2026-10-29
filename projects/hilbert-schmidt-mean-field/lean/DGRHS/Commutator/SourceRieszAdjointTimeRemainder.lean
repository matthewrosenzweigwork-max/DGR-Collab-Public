import DGRHS.Commutator.SourceRieszAdjointMeanDrift
import DGRHS.Commutator.SourceRieszTimeRemainder

/-! The actual classical backward-test remainder is proper in time and
sample under the original physical free-energy estimate and literal initial
Gibbs law. The measurable zero extension agrees with the native gradient at
every point of the closed horizon. No every-path singular drift bound is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_adjoint_time_remainder
    (s β M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K : ℝ≥0) :
    ∃ D : ℝ,0≤D ∧ ∀ (T : ℝ),0≤T → ∀ (N : ℕ),1≤N →
      ∀ (Ω : Type u),∀ [MeasurableSpace Ω],∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
      ∀ (ρ : ℝ→E→ℝ),Measurable (Function.uncurry ρ) →
      (∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r))) →
      (∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M) →
      ∀ (q : ℝ→E→ℝ),(∀ r∈Icc 0 T,ContDiff ℝ 2 (q r)) →
      (∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ)) →
      ContinuousOn (fun p : ℝ×E=>gradient (q p.1) p.2) (Icc 0 T ×ˢ univ) →
      ∀ (X : ℝ→Ω→Fin N→E),Measurable (Function.uncurry X) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ r∈Icc 0 T,sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      let A := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (q r)) N (X r ω)
      let R := fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 T,A r ω))
      Integrable (Function.uncurry A) ((volume.restrict (Ioc 0 T)).prod ν) ∧
      (∀ᵐ ω ∂ν,Integrable (fun r=>A r ω) (volume.restrict (Ioc 0 T))) ∧
      Measurable R ∧ Integrable R ν ∧ (∫ ω,|R ω| ∂ν)≤T*D/(2*Real.sqrt N) := by
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_time_commutator_remainder
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K
  refine ⟨D,hD,?_⟩
  intro T hT N hN Ω _ ν _ ρ hρm hprob hρ q hq hK hgrad X hXm G B hG hB hE
  let v := sourceRieszStoppedGradient T q
  have hvm : Measurable (Function.uncurry v) := measurable_sourceRieszStoppedGradient T q hgrad
  have hvr (r : ℝ) (hr : r∈Icc 0 T) : v r=gradient (q r) := by
    funext z
    simp [v,sourceRieszStoppedGradient,hr]
  have hv (r : ℝ) (hr : r∈Icc 0 T) : LipschitzWith K (v r) := by
    rw [hvr r hr]
    exact sourceAdjoint_gradient_lipschitz_of_hessian_bound (q r) (hq r hr) K (hK r hr)
  obtain ⟨hAm,hi,_,hRi,hRb⟩ := hfactory T hT N hN Ω ν ρ hρm hprob hρ
    v hvm hv X hXm G B hG hB hE
  let η := volume.restrict (Ioc 0 T)
  let Ae := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (v r) N (X r ω)
  let A := fun r ω=>sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (q r)) N (X r ω)
  have htime : ∀ᵐ p : ℝ×Ω ∂η.prod ν,p.1∈Ioc 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Filter.Eventually.of_forall fun _=>hr
  have heq : Function.uncurry Ae=ᵐ[η.prod ν]Function.uncurry A := by
    filter_upwards [htime] with p hp
    change sourceRieszLocalTransportEnergy (ρ p.1) s 1 (v p.1) N (X p.1 p.2)=
      sourceRieszLocalTransportEnergy (ρ p.1) s 1 (gradient (q p.1)) N (X p.1 p.2)
    rw [hvr p.1 ⟨hp.1.le,hp.2⟩]
  have hint (ω : Ω) : (∫ r,Ae r ω ∂η)=∫ r,A r ω ∂η := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp only [Ae,A]
    rw [hvr r ⟨hr.1.le,hr.2⟩]
  have hiA : Integrable (Function.uncurry A) (η.prod ν) := hi.congr heq
  have hRm : Measurable (fun ω=>-((Real.sqrt N/2)*(∫ r,A r ω ∂η))) := by
    have hh : Measurable (fun ω=>-((Real.sqrt N/2)*(∫ r,Ae r ω ∂η))) :=
      ((hAm.stronglyMeasurable.integral_prod_left' (μ:=η)).measurable.const_mul _).neg
    simpa only [hint] using hh
  change Integrable (fun ω=>(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)) ν at hRi
  change (∫ ω,|(Real.sqrt N/2)*(∫ r,Ae r ω ∂η)| ∂ν)≤T*D/(2*Real.sqrt N) at hRb
  simp_rw [hint] at hRi hRb
  exact ⟨hiA,hiA.prod_left_ae,hRm,hRi.neg,by simpa only [abs_neg] using hRb⟩

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_adjoint_time_remainder
#print axioms DGRHS.Commutator.exists_sourceRiesz_adjoint_time_remainder
