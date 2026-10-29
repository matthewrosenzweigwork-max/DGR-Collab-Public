import DGRHS.Commutator.SourceRieszOriginalFiniteNAdjointDuality
import DGRHS.Commutator.SourceLogOriginalExtendedEnergyCLT
import DGRHS.Commutator.SourceLogLiteralEmpiricalIto
import DGRHS.Commutator.SourceLogNamedUpropDynamicCLT
import DGRHS.Dynamics.SourceLogPhysicalAdjointIdentity

/-! Packet P12a, unit B2.  Proposition 8.2 (`prop:finiteNAdjointDuality`, TeX 3859-3877), logarithmic
case `s = 0`, **as printed** in the class of Theorem 2.13 with the extended-energy hypothesis
(TeX 871-874; owner convention 1.2), with the same shape as the Riesz export
`exists_sourceRiesz_original_class_finiteN_adjoint_duality`: class hypotheses in, identity (8.2) with the
Lean Ito-integral martingale, the martingale properties and the `L^1` rate `t D/(2 sqrt N)` out.

Hypotheses not used and therefore omitted (a strengthening): the initial Gibbs law, the partition bound
at `2 beta`, and the trigonometric Ito field; the lower partition bound `c` is needed only at time `0`
and `N` (as in the Lemma 8.1 chain), the upper bound `K_{N,beta}(mu^r) <= Cpart` for `r ∈ [0,T]`. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel DGRHS.Entropy
universe u
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The empirical field of `SourceLogLiteralPhysicalItoAdmissibility`: the time-dependent Ito formula
`eq:dynamicItoEmpirical` (TeX 3880-3889) for the stopped tests with the literal off-diagonal logarithmic
gradient drift, valid for every predictable version of the physical coefficient. -/
def SourceLogLiteralEmpiricalItoAdmissibility
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop :=
  ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceLogPrimitiveLiteralEmpiricalIto P F T β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))

omit [Nonempty ι] in
/-- The empirical field of the literal physical admissibility is exactly this predicate. -/
theorem SourceLogLiteralPhysicalItoAdmissibility.toEmpirical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogLiteralPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B) :
    SourceLogLiteralEmpiricalItoAdmissibility P F T β N k t f G X B :=
  h.empirical

omit [Nonempty ι] in
/-- The literal logarithmic empirical predicate gives the force-zero Riesz physical one on a.e.-time
collision-free slices. -/
theorem SourceLogLiteralEmpiricalItoAdmissibility.to_physical_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogLiteralEmpiricalItoAdmissibility P F T β N k t f G X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceRieszPhysicalEmpiricalItoAdmissibility P F T 0 β N k t f G X B := by
  intro V hV hVb he
  rw [← sourceLogPrimitiveEmpiricalIto_iff_zero P F T β N k t f X B]
  intro a r hr
  filter_upwards [h V hV hVb he a r hr,hc] with ω hI hcol
  have hd : (fun u=>DGRHS.Dynamics.sourceLogEmpiricalTestDrift β (f a) N u (X u ω))=ᵐ[volume.restrict (Ioc 0 (r:ℝ))]
      (fun u=>sourceLogLiteralEmpiricalTestDrift β (f a) N u (X u ω)) := by
    change ∀ᵐ u ∂volume.restrict (Ioc 0 (r:ℝ)),
      DGRHS.Dynamics.sourceLogEmpiricalTestDrift β (f a) N u (X u ω)=
        sourceLogLiteralEmpiricalTestDrift β (f a) N u (X u ω)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp hcol] with u hu hur
    exact sourceLogEmpiricalTestDrift_eq_literal β (f a) N u (X u ω)
      (hu ⟨hur.1,hur.2.trans (hr.trans (ht a))⟩)
  rw [integral_congr_ae hd]
  exact hI

/-- **Proposition 8.2 as printed, logarithmic case, in the class of Theorem 2.13**
(`prop:finiteNAdjointDuality`, TeX 3859-3877; hypotheses as in
`exists_sourceLog_original_class_extended_energy_dynamic_joint_CLT`).  For `t ∈ [0,T]`, `φ ∈ 𝒟_T`,
`f^r = U^{r,t} φ`: there are constants `K, D` (depending on the class data only) such that for every
`N ≥ 1` and every particle system in the class, `M_N` (the normalised Ito integral of the physical
coefficient) is a continuous square-integrable martingale started at `0`, and almost surely
`S_N^t(φ) = S_N^0(f^0) + sqrt N M_N^t[f] - (sqrt N / 2) ∫_0^t A_1(∇f^r, X^r, μ^r) dr`
with the last term integrable of `L^1` norm at most `t D / (2 sqrt N)`. -/
theorem exists_sourceLog_original_class_finiteN_adjoint_duality
    (β : ℝ≥0) (hβ : 0<(β:ℝ)) (T : ℝ≥0)
    (M J c Cpart Amax Bmax : ℝ) (hM : 0≤M) (hc : 0<c) (hAmax : 0≤Amax) (hBmax : 0≤Bmax)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (hIext : ∀ r∈Icc 0 (T:ℝ),((-J : ℝ) : EReal) ≤
      sourceLogExtendedInteractionEnergy (gaussianRieszDensityMeasure (ρ r)))
    (hdist : SourceLogPVDistributionalWeakMeanField (β:ℝ) (T:ℝ) ρ)
    (μpath : ℝ → ProbabilityMeasure E)
    (hμpath : ContinuousOn μpath (Icc 0 (T:ℝ)))
    (hρμ : ∀ r∈Icc 0 (T:ℝ),(μpath r : Measure E)=gaussianRieszDensityMeasure (ρ r))
    (Dtest : Submodule ℝ (E→ℝ))
    (hwp : SourceLogBackwardClassicalWellPosed T (β:ℝ) ρ Dtest)
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφD : φ∈Dtest) :
    let f := sourceLogUprop T (β:ℝ) ρ Dtest hwp t ht φ hφD
    ∃ (K : ℝ≥0) (D : ℝ),0≤D ∧ (∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(K:ℝ)) ∧
    ∀ (Ω : Type u),∀ [mΩ : MeasurableSpace Ω],
    ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
    ∀ (F : Filtration ℝ≥0 mΩ),∀ (N : ℕ),1≤N →
    ∀ (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ),
    SourceLogFiniteHorizonWeakSDE ν F T (β:ℝ) N X B →
    ∀ (G Dg : ℝ→ℝ),(∀ r∈Icc 0 (T:ℝ),0≤G r) →
    (∀ r∈Icc 0 (T:ℝ),G r≤Amax) → (∀ r∈Icc 0 (T:ℝ),Dg r≤Bmax) →
    c≤(sourceLogSingularPartition β (ρ 0) N).toReal →
    (∀ r∈Icc 0 (T:ℝ),(sourceLogSingularPartition β (ρ r) N).toReal≤Cpart) →
    (∀ r∈Icc 0 (T:ℝ),
      sourceLogCollisionFreeEnergy β (ρ r) M N (ν.map (X r))≤
        (G r:EReal)*sourceLogCollisionFreeEnergy β (ρ 0) M N
          (sourceLogSingularGibbs β (ρ 0) N)+(Dg r/(N:ℝ):ℝ)) →
    (∀ Gmax:ℝ≥0,(∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(Gmax:ℝ)) →
      SourceLogLiteralEmpiricalItoAdmissibility ν F T (β:ℝ) N 1 (fun _=>t) (fun _=>f) Gmax X B) →
    ∃ (V : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hV : ∀ b,IsStronglyPredictable F (V b))
      (hVb : ∀ b r ω,‖V b r ω‖≤|Real.sqrt (2/(β:ℝ))/Real.sqrt N| * (K:ℝ)),
    (∀ᵐ ω ∂ν,∀ b r,V b r ω=(Real.sqrt (2/(β:ℝ))/Real.sqrt N)*
      (sourceRieszStoppedGradient (t:ℝ) f (r:ℝ) (X r ω b.1)) b.2) ∧
    ∃ m : ℝ→Ω→ℝ,
      Measurable (Function.uncurry m) ∧ (∀ ω,m 0 ω=0) ∧
      (∀ᵐ ω ∂ν,Continuous (fun r:ℝ=>m r ω)) ∧
      Martingale (fun r:ℝ≥0=>m (r:ℝ)) F ν ∧ (∀ r:ℝ≥0,MemLp (m (r:ℝ)) 2 ν) ∧
      (∀ᵐ ω ∂ν,∀ r:ℝ≥0,Real.sqrt N*m r ω=
        sourceRieszBrownianFamilyProcess ν F B T
          (fun b=>sourceRieszPredictableBoundedL2 ν F T (V b) (hV b)
            (|Real.sqrt (2/(β:ℝ))/Real.sqrt N| * (K:ℝ)) (hVb b)) r ω) ∧
      Integrable (fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
          (sourceLogTransportKernel 1 (gradient (f r))) N (X r ω)))) ν ∧
      (∫ ω,|-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
          (sourceLogTransportKernel 1 (gradient (f r))) N (X r ω)))| ∂ν)≤
        t*D/(2*Real.sqrt N) ∧
      ∀ᵐ ω ∂ν,
        Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ t) φ N (X t ω)=
          Real.sqrt N*sourceLogDynamicEmpiricalDifference (ρ 0) (f 0) N (X 0 ω)+
            Real.sqrt N*m t ω+
          -((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
            sourceTransportEnergy (gaussianRieszDensityMeasure (ρ r))
              (sourceLogTransportKernel 1 (gradient (f r))) N (X r ω))) := by
  classical
  intro f
  have hd : 0<(Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hsol : SourceLogClassicalBackwardSolution (β:ℝ) ρ t φ f :=
    (sourceLogUprop_spec T (β:ℝ) ρ Dtest hwp t ht φ hφD).1
  obtain ⟨C,hC,hb⟩ := hsol.bounded
  let K : ℝ≥0 := ⟨C,hC⟩
  have hgradK : ∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(K:ℝ) :=
    fun r hr z=>(hb r hr z).2.1
  obtain ⟨D,hD,hfactory⟩ := exists_sourceLog_physical_adjoint_interval_identity
    (ι:=ι) β hβ hd K M hM J c Cpart Amax Bmax hc hAmax hBmax
  refine ⟨K,D,hD,hgradK,?_⟩
  intro Ω _ ν _ F N hN X B hSDE G Dg hG hGA hDg hlow hcap hE hIto
  have hT0 : (0:ℝ)≤T := T.coe_nonneg
  have htT : (t:ℝ)≤T := by exact_mod_cast ht
  have hsub (r:ℝ) (hr:r∈Icc 0 (t:ℝ)) : r∈Icc 0 (T:ℝ) := ⟨hr.1,hr.2.trans htT⟩
  have hN0 : 0<N := hN
  -- extended energy lower bound gives pair integrability and the real lower bound
  have hpairI (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) :=
    letI := hprob r hr
    sourceLog_pair_integrable_of_extended_energy_lower_bound hd (ρ r) M J hM (hρ r hr) (hIext r hr)
  have hpair : ∀ r∈Icc 0 (T:ℝ),Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure (ρ r)).prod (gaussianRieszDensityMeasure (ρ r))) :=
    fun r hr=>(hpairI r hr).1
  have hIbg : ∀ r∈Icc 0 (T:ℝ),-J≤DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ r))
      (fun x y=>logPhysicalPair (x,y)) := fun r hr=>(hpairI r hr).2
  -- collision occupation, zero-force SDE
  have hcollision := sourceLog_gronwall_particle_collision_time ν T β M hβ hd hM N hN
    ρ X hSDE.measurable_on_horizon hprob hρ hpair G Dg hE
  have hSDE0 : SourceRieszFiniteHorizonWeakSDE ν F T 0 (β:ℝ) N X B :=
    hSDE.to_zero ν F T (β:ℝ) N X B hcollision
  -- weak mean-field class gives the time-tested identity for the backward solution
  have hstatic := SourceLogPVDistributionalWeakMeanField.to_static (β:ℝ) (T:ℝ) hT0 ρ hprob hdist
    (sourceCompactTestContinuousTrace_of_narrow (T:ℝ) ρ μpath hμpath hρμ)
  have hevol := hstatic.classical_test_evolution (β:ℝ) (T:ℝ) hT0 ρ hprob M hM hρ
    t htT φ f hsol
  have hweakId := (SourceLogMeanFieldTestEvolution.time_test_identity (β:ℝ) (t:ℝ) t.coe_nonneg ρ f
    hevol).2
  -- Ito integral martingale
  have hgrad1 : ∀ a:Fin 1,ContinuousOn (fun p:ℝ×E=>gradient ((fun _:Fin 1=>f) a p.1) p.2)
      (Icc 0 (((fun _:Fin 1=>t) a:ℝ≥0):ℝ) ×ˢ univ) := fun _=>hsol.gradient_continuous
  obtain ⟨V,hV,hVb,hVe,m,hmm,hm0,hmc,hMart,hLp,hme,hEmp⟩ :=
    exists_sourceRiesz_empirical_ito_fixed_martingales_of_physical ν F T 0 (β:ℝ) N 1 hN0
      (fun _=>t) (fun _=>ht) (fun _=>f) hgrad1 K (fun _ r hr z=>hgradK r hr z) X B hSDE0
      ((hIto K hgradK).to_physical_zero ν F T (β:ℝ) N 1 (fun _=>t) (fun _=>ht) (fun _=>f) K X B
        hcollision)
  -- restriction of the data to `[0,t]`
  let inc : Icc (0:ℝ) (t:ℝ)→Icc (0:ℝ) (T:ℝ) := fun r=>⟨r,hsub r r.property⟩
  have him : Measurable inc := measurable_subtype_coe.subtype_mk
  have hρm' : Measurable (fun p:Icc (0:ℝ) (t:ℝ)×E=>ρ p.1 p.2) :=
    hρm.comp (((him).comp measurable_fst).prodMk measurable_snd)
  have hXm' : Measurable (fun p:Icc (0:ℝ) (t:ℝ)×Ω=>X p.1 p.2) :=
    hSDE.measurable_on_horizon.comp (((him).comp measurable_fst).prodMk measurable_snd)
  have hgradC : Continuous (fun p:Icc (0:ℝ) (t:ℝ)×E=>gradient (f p.1) p.2) :=
    hsol.gradient_continuous.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p=>⟨p.1.property,mem_univ _⟩)
  have hIe : ∀ᵐ ω ∂ν,
      (∫ z,f (t:ℝ) z ∂transportEmpiricalLaw N (X (t:ℝ) ω))-
        (∫ z,f 0 z ∂transportEmpiricalLaw N (X 0 ω))=
        (∫ r in Ioc 0 (t:ℝ),sourceLogEmpiricalTestDrift (β:ℝ) f N r (X r ω))+m 0 (t:ℝ) ω := by
    filter_upwards [hEmp 0] with ω hω
    simpa only [sourceRieszLocalEmpiricalLaw_eq_transport,sourceRieszEmpiricalTestDrift_zero_eq_log]
      using hω
  obtain ⟨-,hid,-,hRi,hRb⟩ := hfactory (t:ℝ) t.coe_nonneg N hN Ω ν ρ hρm'
    (fun r hr=>hprob r (hsub r hr)) (fun r hr=>hρ r (hsub r hr))
    (fun r hr=>hpair r (hsub r hr)) (fun r hr=>hIbg r (hsub r hr)) f hsol.spatial_contdiff
    (fun r hr z=>(hb r hr z).2.2) hgradC C (fun r hr z=>(hb r hr z).1)
    (hsol.backward_ae (β:ℝ) ρ t φ f) X hXm' G Dg (fun r hr=>hG r (hsub r hr))
    (fun r hr=>hGA r (hsub r hr)) (fun r hr=>hDg r (hsub r hr)) hlow
    (fun r hr=>hcap r (hsub r hr)) (fun r hr=>hE r (hsub r hr)) (m 0 (t:ℝ)) hIe hweakId
  refine ⟨V 0,fun b=>hV 0 b,fun b r ω=>hVb 0 b r ω,?_,m 0,hmm 0,hm0 0,hmc 0,hMart 0,hLp 0,?_,hRi,
    ?_,?_⟩
  · filter_upwards [hVe] with ω hω b r
    exact hω 0 b r
  · filter_upwards [hme] with ω hω r
    exact hω 0 r
  · simpa only [abs_neg] using hRb
  · filter_upwards [hid] with ω hω
    obtain ⟨-,-,hω⟩ := hω
    have hts : f (t:ℝ)=φ := hsol.terminal
    rw [hts] at hω
    exact hω

end DGRHS.Commutator
#check @DGRHS.Commutator.SourceLogLiteralEmpiricalItoAdmissibility
#print axioms DGRHS.Commutator.SourceLogLiteralEmpiricalItoAdmissibility
#check @DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility.toEmpirical
#print axioms DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility.toEmpirical
#check @DGRHS.Commutator.SourceLogLiteralEmpiricalItoAdmissibility.to_physical_zero
#print axioms DGRHS.Commutator.SourceLogLiteralEmpiricalItoAdmissibility.to_physical_zero
#check @DGRHS.Commutator.exists_sourceLog_original_class_finiteN_adjoint_duality
#print axioms DGRHS.Commutator.exists_sourceLog_original_class_finiteN_adjoint_duality
