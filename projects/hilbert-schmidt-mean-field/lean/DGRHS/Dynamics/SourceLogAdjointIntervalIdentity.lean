import DGRHS.Dynamics.SourceLogAdjointAETimeIdentity
import DGRHS.Dynamics.SourceDensityKernel
import DGRHS.Gaussian.GaussianShortRangeSourceL2

/-! Native logarithmic terminal duality on the original closed horizon.
Only the density and path are extended outside the horizon. The native test,
gradient, Laplacian and time derivative are unchanged. The backward equation
is used only almost everywhere in the interior, and all properness follows
from the classical test bounds. Only the primitive particle/mean identities
are premises; the desired terminal decomposition is a conclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set
open scoped NNReal ENNReal
namespace DGRHS.Dynamics
open DGRHS.Commutator DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

set_option maxHeartbeats 1000000 in
theorem sourceLog_adjoint_interval_time_identity (β T : ℝ) (hT : 0≤T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p : Icc (0:ℝ) T×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (q : ℝ→E→ℝ) (K : ℝ≥0) (L : ℝ)
    (hq : ∀ r∈Icc 0 T,ContDiff ℝ 2 (q r))
    (hK : ∀ r∈Icc 0 T,∀ z,‖iteratedFDeriv ℝ 2 (q r) z‖≤(K:ℝ))
    (hqbound : ∀ r∈Icc 0 T,∀ z,|q r z|≤L)
    (hgrad : Continuous (fun p : Icc (0:ℝ) T×E=>gradient (q p.1) p.2))
    (hback : ∀ᵐ r ∂volume.restrict (Ioc 0 T),∀ z,
      deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
        ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y)
          ∂gaussianRieszDensityMeasure (ρ r))
    (N : ℕ) (hN : 0<N) (X : ℝ→Fin N→E)
    (hX : Measurable (fun r : Icc (0:ℝ) T=>X r)) (M : ℝ)
    (hIto : (∫ z,q T z ∂transportEmpiricalLaw N (X T))-
      (∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))=
      (∫ r in Ioc 0 T,sourceLogEmpiricalTestDrift β q N r (X r))+M)
    (hweak : (∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T))-
      (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
      ∫ r in Ioc 0 T,sourceLogMeanTestDrift β q r (gaussianRieszDensityMeasure (ρ r))) :
    (∀ r∈Icc 0 T,Integrable (q r) (gaussianRieszDensityMeasure (ρ r)) ∧
      ∀ x : Fin N→E,Integrable (q r) (transportEmpiricalLaw N x)) ∧
    Integrable (fun r=>sourceLogEmpiricalTestDrift β q N r (X r)) (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceLogMeanTestDrift β q r (gaussianRieszDensityMeasure (ρ r)))
      (volume.restrict (Ioc 0 T)) ∧
    Integrable (fun r=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
      (sourceLogTransportKernel 1 (gradient (q r))) N (X r)) (volume.restrict (Ioc 0 T)) ∧
    Real.sqrt N*((∫ z,q T z ∂transportEmpiricalLaw N (X T))-
      (∫ z,q T z ∂gaussianRieszDensityMeasure (ρ T)))=
      Real.sqrt N*((∫ z,q 0 z ∂transportEmpiricalLaw N (X 0))-
        (∫ z,q 0 z ∂gaussianRieszDensityMeasure (ρ 0)))+
      Real.sqrt N*M-(Real.sqrt N/2)*(∫ r in Ioc 0 T,
        sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
          (sourceLogTransportKernel 1 (gradient (q r))) N (X r)) := by
  let ρe := fun r=>ρ (projIcc 0 T hT r)
  let Xe := fun r=>X (projIcc 0 T hT r)
  have hρeq (r : ℝ) (hr : r∈Icc 0 T) : ρe r=ρ r := by
    dsimp only [ρe];rw [projIcc_of_mem hT hr]
  have hXeq (r : ℝ) (hr : r∈Icc 0 T) : Xe r=X r := by
    dsimp only [Xe];rw [projIcc_of_mem hT hr]
  have hρem : Measurable (Function.uncurry ρe) := hρm.comp
    (((continuous_projIcc : Continuous (projIcc 0 T hT)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hXem : Measurable Xe := hX.comp
    (continuous_projIcc : Continuous (projIcc 0 T hT)).measurable
  let κ := sourceDensityKernel volume ρe
  letI := sourceDensityKernel_sfinite volume ρe
  have hκeq (r : ℝ) (hr : r∈Icc 0 T) : κ r=gaussianRieszDensityMeasure (ρ r) := by
    rw [show κ r=gaussianRieszDensityMeasure (ρe r) from sourceDensityKernel_apply volume ρe hρem r,
      hρeq r hr]
  have hz : (0:ℝ)∈Icc 0 T := ⟨le_rfl,hT⟩
  have ht : T∈Icc 0 T := ⟨hT,le_rfl⟩
  let η := volume.restrict (Ioc 0 T)
  have he : (fun r=>sourceLogEmpiricalTestDrift β q N r (Xe r))=ᵐ[η]
      (fun r=>sourceLogEmpiricalTestDrift β q N r (X r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hXeq r ⟨hr.1.le,hr.2⟩]
  have hm : (fun r=>sourceLogMeanTestDrift β q r (κ r))=ᵐ[η]
      (fun r=>sourceLogMeanTestDrift β q r (gaussianRieszDensityMeasure (ρ r))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hκeq r ⟨hr.1.le,hr.2⟩]
  have ha : (fun r=>sourceTransportEnergy (κ r) (sourceLogTransportKernel 1 (gradient (q r))) N (Xe r))=ᵐ[η]
      (fun r=>sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
        (sourceLogTransportKernel 1 (gradient (q r))) N (X r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [hκeq r ⟨hr.1.le,hr.2⟩,hXeq r ⟨hr.1.le,hr.2⟩]
  have hb : ∀ᵐ r ∂η,∀ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z=
      ∫ y,sourceLogTransportKernel 1 (gradient (q r)) (z,y) ∂κ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hback] with r hr hb
    simpa only [hκeq r ⟨hr.1.le,hr.2⟩] using hb
  have heI := integral_congr_ae he
  have hmI := integral_congr_ae hm
  have haI := integral_congr_ae ha
  dsimp only [η] at heI hmI haI
  obtain ⟨hproper,hie,him,hia,hidentity⟩ := sourceLog_adjoint_regular_ae_time_identity
    β T hT q K L hq hK hqbound hgrad κ
    (fun r hr=>by rw [hκeq r hr];exact hprob r hr) hb N hN Xe hXem M
    (by simpa only [hXeq T ht,hXeq 0 hz,heI] using hIto)
    (by simpa only [hκeq T ht,hκeq 0 hz,hmI] using hweak)
  refine ⟨?_,hie.congr he,him.congr hm,hia.congr ha,?_⟩
  · intro r hr
    simpa only [hκeq r hr] using hproper r hr
  · simpa only [hXeq T ht,hXeq 0 hz,hκeq T ht,hκeq 0 hz,haI] using hidentity

end DGRHS.Dynamics
set_option pp.deepTerms true in
#check @DGRHS.Dynamics.sourceLog_adjoint_interval_time_identity
#print axioms DGRHS.Dynamics.sourceLog_adjoint_interval_time_identity
