import DGRHS.Commutator.SourceLogSourceMartingaleAssembly
import DGRHS.Commutator.SourceRieszDynamicForceEmpirical

/-! Literal logarithmic primitive Itô input. The off-diagonal native gradient
of the physical logarithmic potential supplies the technical empirical drift
only on independently established collision-free time slices. No integrability
is inferred from noncollision. New body awaits actual restricted diagnostics. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι Ω : Type*} [Fintype ι] [mΩ : MeasurableSpace Ω]
local notation "E" => EuclideanSpace ℝ ι

/-- The literal source empirical Ito drift uses only distinct particle
indices and the native gradient of the physical potential. -/
def sourceLogLiteralEmpiricalTestDrift (β : ℝ) (q : ℝ→E→ℝ)
    (N : ℕ) (r : ℝ) (x : Fin N→E) : ℝ :=
  (∫ z,deriv (fun t=>q t z) r+β⁻¹*laplacian (q r) z ∂transportEmpiricalLaw N x)-
    ((N:ℝ)^2)⁻¹*DGRHS.CanonicalVariance.offDiagonalSum
      (fun p:E×E=>⟪gradient sourceLogPotential (p.1-p.2),gradient (q r) p.1⟫) x

lemma sourceLogEmpiricalTestDrift_eq_literal
    (β : ℝ) (q : ℝ→E→ℝ) (N : ℕ) (r : ℝ) (x : Fin N→E)
    (hx : ∀ i j:Fin N,i≠j → x i≠x j) :
    DGRHS.Dynamics.sourceLogEmpiricalTestDrift β q N r x=sourceLogLiteralEmpiricalTestDrift β q N r x := by
  classical
  rw [←sourceRieszEmpiricalTestDrift_zero_eq_log]
  unfold sourceRieszEmpiricalTestDrift sourceLogLiteralEmpiricalTestDrift
  rw [sourceRieszLocalEmpiricalLaw_eq_transport,←sourceRiesz_force_offDiagonalSum]
  congr 2
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only
  rw [sourceRieszForce_zero_eq_logForce,sourceLogForce_eq_gradient
    (sub_ne_zero.mpr (hx p.1 p.2 (Finset.mem_offDiag.mp hp).2.2))]

def SourceLogPrimitiveLiteralEmpiricalIto
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (f : Fin k→ℝ→E→ℝ)
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) : Prop :=
  ∀ a,∀ r : ℝ≥0,r≤t a → ∀ᵐ ω ∂P,
    (∫ z,f a r z ∂transportEmpiricalLaw N (X r ω))-
      (∫ z,f a 0 z ∂transportEmpiricalLaw N (X 0 ω)) =
      (∫ u in Ioc 0 (r:ℝ),sourceLogLiteralEmpiricalTestDrift β (f a) N u (X u ω))+
        sourceRieszBrownianFamilyProcess P F B T (g a) r ω/Real.sqrt N

structure SourceLogLiteralPhysicalItoAdmissibility
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop where
  empirical : ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceLogPrimitiveLiteralEmpiricalIto P F T β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))
  trigonometric : ∀ (θ : Fin k→ℝ) (U : (Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hU : ∀ b,IsStronglyPredictable F (U b))
      (hUb : ∀ b r ω,‖U b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))),
      (∀ᵐ ω ∂P,∀ r b,U b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        ((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2)) →
      SourceRieszPrimitiveActualTrigIto P F T N B U hU
        (|Real.sqrt (2/β)/Real.sqrt N| *((G:ℝ)*(∑ a,|θ a|))) hUb
        (fun ω=>∑ a,θ a*(Real.sqrt N*sourceLogDynamicEmpiricalDifference ρ₀ (f a 0) N (X 0 ω)))


/-- Convert the literal empirical primitive formula using only the already
derived AE-time collision freedom. The trigonometric primitive formula and
its actual physical stochastic integrals are exactly unchanged. -/
theorem SourceLogLiteralPhysicalItoAdmissibility.to_physical
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceLogLiteralPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceLogPhysicalItoAdmissibility P F T β N k t ρ₀ f G X B := by
  refine ⟨?_,h.trigonometric⟩
  intro V hV hVb he a r hr
  filter_upwards [h.empirical V hV hVb he a r hr,hc] with ω hI hcol
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

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLogLiteralEmpiricalTestDrift
#print axioms DGRHS.Commutator.sourceLogLiteralEmpiricalTestDrift
#check @DGRHS.Commutator.sourceLogEmpiricalTestDrift_eq_literal
#print axioms DGRHS.Commutator.sourceLogEmpiricalTestDrift_eq_literal
#check @DGRHS.Commutator.SourceLogPrimitiveLiteralEmpiricalIto
#print axioms DGRHS.Commutator.SourceLogPrimitiveLiteralEmpiricalIto
#check @DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility
#print axioms DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility
#check @DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility.to_physical
#print axioms DGRHS.Commutator.SourceLogLiteralPhysicalItoAdmissibility.to_physical
