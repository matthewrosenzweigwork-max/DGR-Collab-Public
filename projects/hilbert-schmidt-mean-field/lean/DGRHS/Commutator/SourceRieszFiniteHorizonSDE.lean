import DGRHS.Commutator.SourceRieszPrimitiveDynamics

/-! UNCOMPILED finite-horizon source interface. Only restricted joint
measurability and adaptedness up to T are assumed. A constant extension at both
ends supplies the global-time technical data used by the checked constructor.
The actual SDE is preserved only on its original horizon. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

structure SourceRieszFiniteHorizonWeakSDE
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P F B
  measurable_on_horizon : Measurable (fun p : Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2)
  adapted_on_horizon : ∀ i,∀ r:ℝ≥0,r≤T → StronglyMeasurable[F r] (fun ω=>X (r:ℝ) ω i)
  continuous_on_horizon : ∀ i,∀ᵐ ω ∂P,
    ContinuousOn (fun r:ℝ≥0=>X (r:ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P,∀ i,
    IntegrableOn (fun r:ℝ=>sourceRieszParticleSDEDrift s N (X r ω) i) (Ioc 0 (T:ℝ))
  equation : ∀ᵐ ω ∂P,∀ r:ℝ≥0,r≤T → ∀ i,
    X (r:ℝ) ω i=X 0 ω i+
      (∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift s N (X u ω) i)+
      Real.sqrt (2/β) • (sourceRieszParticleBrownianVector N B i r ω-
        sourceRieszParticleBrownianVector N B i 0 ω)

def sourceRieszParticleRealHorizonExtension (T : ℝ≥0) (N : ℕ)
    (X : ℝ→Ω→Fin N→E) (r : ℝ) (ω : Ω) : Fin N→E :=
  X ((min (Real.toNNReal r) T:ℝ≥0):ℝ) ω

lemma sourceRieszParticleRealHorizonExtension_eq
    (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E) (r : ℝ) (hr : r∈Icc 0 (T:ℝ)) :
    sourceRieszParticleRealHorizonExtension T N X r=X r := by
  have ht : Real.toNNReal r≤T := by
    change ((Real.toNNReal r:ℝ≥0):ℝ)≤(T:ℝ)
    rw [Real.coe_toNNReal _ hr.1]
    exact hr.2
  funext ω
  change X ((min (Real.toNNReal r) T:ℝ≥0):ℝ) ω=X r ω
  rw [min_eq_left ht,Real.coe_toNNReal _ hr.1]

lemma sourceRieszParticleRealHorizonExtension_measurable
    (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (hX : Measurable (fun p : Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2)) :
    Measurable (Function.uncurry (sourceRieszParticleRealHorizonExtension T N X)) := by
  let c : ℝ→Icc (0:ℝ) (T:ℝ) := fun r=>
    ⟨((min (Real.toNNReal r) T:ℝ≥0):ℝ),⟨(min (Real.toNNReal r) T).coe_nonneg,min_le_right _ _⟩⟩
  have hc : Measurable c := by
    dsimp only [c]
    fun_prop
  exact hX.comp ((hc.comp measurable_fst).prodMk measurable_snd)

lemma sourceRieszParticleRealHorizonExtension_adapted
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (hX : ∀ i,∀ r:ℝ≥0,r≤T → StronglyMeasurable[F r] (fun ω=>X (r:ℝ) ω i)) :
    ∀ i,StronglyAdapted F (fun r ω=>sourceRieszParticleRealHorizonExtension T N X (r:ℝ) ω i) := by
  intro i r
  have hr : Real.toNNReal (r:ℝ)=r := Subtype.ext (Real.coe_toNNReal _ r.coe_nonneg)
  simpa only [sourceRieszParticleRealHorizonExtension,hr] using
    (hX i (min r T) (min_le_right _ _)).mono (F.mono (min_le_left _ _))

lemma sourceRieszParticleRealHorizonExtension_continuous
    (P : Measure Ω) (T : ℝ≥0) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (hX : ∀ i,∀ᵐ ω ∂P,ContinuousOn (fun r:ℝ≥0=>X (r:ℝ) ω i) (Icc 0 T)) :
    ∀ i,∀ᵐ ω ∂P,Continuous (fun r:ℝ≥0=>sourceRieszParticleRealHorizonExtension T N X (r:ℝ) ω i) := by
  intro i
  have hn (r:ℝ≥0) : Real.toNNReal (r:ℝ)=r := Subtype.ext (Real.coe_toNNReal _ r.coe_nonneg)
  filter_upwards [sourceRieszParticleHorizonExtension_continuous P T N X hX i] with ω hω
  simpa only [sourceRieszParticleRealHorizonExtension,hn,sourceRieszParticleHorizonExtension] using hω

lemma SourceRieszFiniteHorizonWeakSDE.extended
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszFiniteHorizonWeakSDE P F T s β N X B) :
    SourceRieszAdditiveWeakSDE P F T s β N (sourceRieszParticleRealHorizonExtension T N X) B := by
  let Xe := sourceRieszParticleRealHorizonExtension T N X
  have he (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : Xe r=X r :=
    sourceRieszParticleRealHorizonExtension_eq T N X r hr
  refine ⟨h.brownian,sourceRieszParticleRealHorizonExtension_measurable T N X h.measurable_on_horizon,
    sourceRieszParticleRealHorizonExtension_adapted F T N X h.adapted_on_horizon,?_,?_,?_⟩
  · intro i
    exact (sourceRieszParticleRealHorizonExtension_continuous P T N X h.continuous_on_horizon i).mono
      (fun ω hω=>hω.continuousOn)
  · filter_upwards [h.drift_integrable] with ω hω
    intro i
    apply (hω i).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change sourceRieszParticleSDEDrift s N (X r ω) i=
      sourceRieszParticleSDEDrift s N (Xe r ω) i
    rw [he r ⟨hr.1.le,hr.2⟩]
  · filter_upwards [h.equation] with ω hω
    intro r hr i
    have hi : (∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift s N (Xe u ω) i)=
        ∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift s N (X u ω) i := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      change sourceRieszParticleSDEDrift s N (Xe u ω) i=
        sourceRieszParticleSDEDrift s N (X u ω) i
      rw [he u ⟨hu.1.le,hu.2.trans hr⟩]
    change Xe r ω i=Xe 0 ω i+
      (∫ u in Ioc 0 (r:ℝ),sourceRieszParticleSDEDrift s N (Xe u ω) i)+_
    rw [he r ⟨r.coe_nonneg,hr⟩,he 0 ⟨le_rfl,T.coe_nonneg⟩,hi]
    exact hω r hr i

lemma SourceRieszInitialGibbsBrownianData.horizon_extension
    (P : Measure Ω) (T : ℝ≥0) (s β : ℝ) (ρ : E→ℝ) (N : ℕ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszInitialGibbsBrownianData P s β ρ N (X 0) B) :
    SourceRieszInitialGibbsBrownianData P s β ρ N
      (sourceRieszParticleRealHorizonExtension T N X 0) B := by
  rw [sourceRieszParticleRealHorizonExtension_eq T N X 0 ⟨le_rfl,T.coe_nonneg⟩]
  exact h


lemma sourceRieszParticleRealHorizonExtension_stopped_gradient
    (T a : ℝ≥0) (ha : a≤T) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (f : ℝ→E→ℝ) (r : ℝ) (ω : Ω) (i : Fin N) :
    sourceRieszStoppedGradient (a:ℝ) f r (sourceRieszParticleRealHorizonExtension T N X r ω i)=
      sourceRieszStoppedGradient (a:ℝ) f r (X r ω i) := by
  by_cases hr : r∈Icc 0 (a:ℝ)
  · rw [sourceRieszParticleRealHorizonExtension_eq T N X r ⟨hr.1,hr.2.trans ha⟩]
  · simp only [sourceRieszStoppedGradient,if_neg hr]

lemma SourceRieszPrimitiveEmpiricalIto.horizon_extension
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (f : Fin k→ℝ→E→ℝ) (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T))
    (h : SourceRieszPrimitiveEmpiricalIto P F T s β N k t f X B g) :
    SourceRieszPrimitiveEmpiricalIto P F T s β N k t f
      (sourceRieszParticleRealHorizonExtension T N X) B g := by
  intro a r hr
  have he (u:ℝ) (hu:u∈Icc 0 (T:ℝ)) :
      sourceRieszParticleRealHorizonExtension T N X u=X u :=
    sourceRieszParticleRealHorizonExtension_eq T N X u hu
  have hi (ω:Ω) : (∫ u in Ioc 0 (r:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N u
      (sourceRieszParticleRealHorizonExtension T N X u ω))=
      ∫ u in Ioc 0 (r:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N u (X u ω) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    change sourceRieszEmpiricalTestDrift s β (f a) N u
      (sourceRieszParticleRealHorizonExtension T N X u ω)=_
    rw [he u ⟨hu.1.le,hu.2.trans (hr.trans (ht a))⟩]
  simpa only [he r ⟨r.coe_nonneg,hr.trans (ht a)⟩,he 0 ⟨le_rfl,T.coe_nonneg⟩,hi]
    using h a r hr

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE
#print axioms DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE
#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension
#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_eq
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_eq
#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_measurable
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_measurable
#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_adapted
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_adapted
#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_continuous
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_continuous
#check @DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE.extended
#print axioms DGRHS.Commutator.SourceRieszFiniteHorizonWeakSDE.extended
#check @DGRHS.Commutator.SourceRieszInitialGibbsBrownianData.horizon_extension
#print axioms DGRHS.Commutator.SourceRieszInitialGibbsBrownianData.horizon_extension

#check @DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_stopped_gradient
#print axioms DGRHS.Commutator.sourceRieszParticleRealHorizonExtension_stopped_gradient

#check @DGRHS.Commutator.SourceRieszPrimitiveEmpiricalIto.horizon_extension
#print axioms DGRHS.Commutator.SourceRieszPrimitiveEmpiricalIto.horizon_extension
