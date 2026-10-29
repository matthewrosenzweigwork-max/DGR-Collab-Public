import DGRHS.Commutator.SourceRieszPhysicalSDE
import DGRHS.Commutator.SourceRieszSourceMartingaleAssembly

/-! UNCOMPILED literal source-input adapters. The actual singular-potential
SDE and its primitive empirical Ito drift are inputs. Zero collision-time
occupation, derived independently from the original free-energy bound, then
converts them to the checked zero-extension convention. Given drift
integrability is transported; it is never inferred from noncollision. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

structure SourceRieszLiteralFiniteHorizonSDE
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  brownian : SourceRieszFilteredBrownianFamily P F B
  measurable_on_horizon : Measurable (fun p : Icc (0:ℝ) (T:ℝ)×Ω=>X p.1 p.2)
  adapted_on_horizon : ∀ i,∀ r:ℝ≥0,r≤T → StronglyMeasurable[F r] (fun ω=>X (r:ℝ) ω i)
  continuous_on_horizon : ∀ i,∀ᵐ ω ∂P,
    ContinuousOn (fun r:ℝ≥0=>X (r:ℝ) ω i) (Icc 0 T)
  drift_integrable : ∀ᵐ ω ∂P,∀ i,
    IntegrableOn (fun r:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,gradient (sourceRieszPotential s) (X r ω i-X r ω j)) (Ioc 0 (T:ℝ))
  equation : ∀ᵐ ω ∂P,∀ r:ℝ≥0,r≤T → ∀ i,
    X (r:ℝ) ω i=X 0 ω i+
      (∫ u in Ioc 0 (r:ℝ),-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,gradient (sourceRieszPotential s) (X u ω i-X u ω j))+
      Real.sqrt (2/β) • (sourceRieszParticleBrownianVector N B i r ω-
        sourceRieszParticleBrownianVector N B i 0 ω)

/-- Correct input direction: an actual literal-gradient SDE supplies the
technical zero-force SDE once zero collision-time occupation is known. -/
theorem SourceRieszLiteralFiniteHorizonSDE.to_weak
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hs : 0<s) (N : ℕ) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszLiteralFiniteHorizonSDE P F T s β N X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceRieszFiniteHorizonWeakSDE P F T s β N X B := by
  classical
  have he : ∀ᵐ ω ∂P,∀ i:Fin N,
      (fun r:ℝ=>sourceRieszParticleSDEDrift s N (X r ω) i)=ᵐ[volume.restrict (Ioc 0 (T:ℝ))]
        (fun r:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
          gradient (sourceRieszPotential s) (X r ω i-X r ω j)) := by
    filter_upwards [hc] with ω hω
    intro i
    filter_upwards [hω] with r hr
    exact sourceRieszParticleSDEDrift_eq_physical s hs N (X r ω) hr i
  refine ⟨h.brownian,h.measurable_on_horizon,h.adapted_on_horizon,h.continuous_on_horizon,?_,?_⟩
  · filter_upwards [he,h.drift_integrable] with ω heq hI
    exact fun i=>(hI i).congr (heq i).symm
  · filter_upwards [he,h.equation] with ω heq hE
    intro r hr i
    have her :
        (fun u:ℝ=>sourceRieszParticleSDEDrift s N (X u ω) i)=ᵐ[volume.restrict (Ioc 0 (r:ℝ))]
          (fun u:ℝ=>-((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
            gradient (sourceRieszPotential s) (X u ω i-X u ω j)) := by
      change ∀ᵐ u ∂volume.restrict (Ioc 0 (r:ℝ)),
        sourceRieszParticleSDEDrift s N (X u ω) i=
          -((N:ℝ)⁻¹) • ∑ j ∈ Finset.univ.erase i,
            gradient (sourceRieszPotential s) (X u ω i-X u ω j)
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (heq i)] with u hu hur
      exact hu ⟨hur.1,hur.2.trans hr⟩
    rw [integral_congr_ae her]
    exact hE r hr i

/-- The literal source empirical Ito drift uses only distinct particle
indices and the native gradient of the physical potential. -/
def sourceRieszLiteralEmpiricalTestDrift (s β : ℝ) (q : ℝ→E→ℝ)
    (N : ℕ) (r : ℝ) (x : Fin N→E) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z ∂sourceRieszLocalEmpiricalLaw N x)-
    ((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
      (fun p:E×E=>⟪gradient (sourceRieszPotential s) (p.1-p.2),gradient (q r) p.1⟫) x

lemma sourceRieszEmpiricalTestDrift_eq_literal
    (s β : ℝ) (hs : 0<s) (q : ℝ→E→ℝ) (N : ℕ) (r : ℝ) (x : Fin N→E)
    (hx : ∀ i j:Fin N,i≠j → x i≠x j) :
    sourceRieszEmpiricalTestDrift s β q N r x=sourceRieszLiteralEmpiricalTestDrift s β q N r x := by
  classical
  unfold sourceRieszEmpiricalTestDrift sourceRieszLiteralEmpiricalTestDrift
  rw [←sourceRiesz_force_offDiagonalSum]
  congr 2
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [sourceRieszForce_eq_gradient s hs
    (sub_ne_zero.mpr (hx p.1 p.2 (Finset.mem_offDiag.mp hp).2.2))]

def SourceRieszPrimitiveLiteralEmpiricalIto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) : Prop :=
  ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
    (∫ z,f a r z ∂sourceRieszLocalEmpiricalLaw N (X r ω))-
      (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω)) =
      (∫ u in Ioc 0 (r:ℝ),sourceRieszLiteralEmpiricalTestDrift s β (f a) N u (X u ω))+
        sourceRieszBrownianFamilyProcess P F B T (g a) r ω/Real.sqrt N

structure SourceRieszLiteralPhysicalItoAdmissibility
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  empirical : ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceRieszPrimitiveLiteralEmpiricalIto P F T s β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))
  trigonometric : ∀ (θ : Fin k→ℝ) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hU : ∀ b,IsStronglyPredictable F (U b))
      (hUb : ∀ b r ω,‖U b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))),
      (∀ᵐ ω ∂P,∀ r b,U b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) →
      SourceRieszPrimitiveActualTrigIto P F T N B U hU
        (|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))) hUb
        (fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω)))


/-- Convert the literal empirical primitive formula using only the already
derived AE-time collision freedom. The trigonometric primitive formula and
its actual physical stochastic integrals are exactly unchanged. -/
theorem SourceRieszLiteralPhysicalItoAdmissibility.to_physical
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hs : 0<s) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszLiteralPhysicalItoAdmissibility P F T s β N k t ρ₀ f G X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceRieszPhysicalItoAdmissibility P F T s β N k t ρ₀ f G X B := by
  refine ⟨?_,h.trigonometric⟩
  intro V hV hVb he a r hr
  filter_upwards [h.empirical V hV hVb he a r hr,hc] with ω hI hcol
  have hd : (fun u=>sourceRieszEmpiricalTestDrift s β (f a) N u (X u ω))=ᵐ[volume.restrict (Ioc 0 (r:ℝ))]
      (fun u=>sourceRieszLiteralEmpiricalTestDrift s β (f a) N u (X u ω)) := by
    change ∀ᵐ u ∂volume.restrict (Ioc 0 (r:ℝ)),
      sourceRieszEmpiricalTestDrift s β (f a) N u (X u ω)=
        sourceRieszLiteralEmpiricalTestDrift s β (f a) N u (X u ω)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp hcol] with u hu hur
    exact sourceRieszEmpiricalTestDrift_eq_literal s β hs (f a) N u (X u ω)
      (hu ⟨hur.1,hur.2.trans (hr.trans (ht a))⟩)
  rw [integral_congr_ae hd]
  exact hI

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.SourceRieszLiteralFiniteHorizonSDE
#print axioms DGRHS.Commutator.SourceRieszLiteralFiniteHorizonSDE
#check @DGRHS.Commutator.SourceRieszLiteralFiniteHorizonSDE.to_weak
#print axioms DGRHS.Commutator.SourceRieszLiteralFiniteHorizonSDE.to_weak
#check @DGRHS.Commutator.sourceRieszLiteralEmpiricalTestDrift
#print axioms DGRHS.Commutator.sourceRieszLiteralEmpiricalTestDrift
#check @DGRHS.Commutator.sourceRieszEmpiricalTestDrift_eq_literal
#print axioms DGRHS.Commutator.sourceRieszEmpiricalTestDrift_eq_literal
#check @DGRHS.Commutator.SourceRieszPrimitiveLiteralEmpiricalIto
#print axioms DGRHS.Commutator.SourceRieszPrimitiveLiteralEmpiricalIto
#check @DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility
#print axioms DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility
#check @DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility.to_physical
#print axioms DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility.to_physical
