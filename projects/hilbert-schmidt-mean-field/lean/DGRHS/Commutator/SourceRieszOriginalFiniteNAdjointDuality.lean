import DGRHS.Commutator.SourceRieszOriginalDynamicCLTNarrow
import DGRHS.Commutator.SourceRieszAdjointTimeIdentity

/-! Packet P12a, unit B1.  Proposition 8.2 (`prop:finiteNAdjointDuality`, TeX 3859-3877, proof
3879-3930), positive Riesz case `0 < s < d/2`, **as printed** in the class of Theorem 2.13.

The existing finite-`N` exports (`exists_sourceRiesz_finite_terminal_representation` and its CF form)
take an abstract random variable `m`, the integrated empirical Ito identity for that `m`, and the
time-tested mean-field identity as hypotheses.  Here the hypotheses are those of the Theorem 2.13
Euclidean export `exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT` (PV-distributional weak
mean-field class with a narrowly continuous path, classical backward well-posedness, the literal SDE, the
free-energy Gronwall estimate, and the empirical Ito formula of hypothesis (i) as a predicate), and the
conclusion contains all three printed claims: the identity (8.2) with `M_N^tau[f]` the Lean Ito integral of
the physical coefficient, `M_N` a continuous square-integrable martingale started at `0`, and the
`L^1` bound `t D / (2 sqrt N)` for the commutator remainder with `D` chosen before the particle data.

Hypotheses not used and therefore omitted (a strengthening): the initial Gibbs law (it enters only through
the right-hand side `Q_{N,beta}(mu^0)` of the Gronwall estimate), the `A^t` bound, and the
trigonometric (exponential) Ito field, which is used only later for the characteristic function. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The empirical field of `SourceRieszLiteralPhysicalItoAdmissibility`: the time-dependent Ito formula
`eq:dynamicItoEmpirical` (TeX 3880-3889) for the stopped tests, with the literal off-diagonal gradient
drift, valid for every predictable version of the physical coefficient. -/
def SourceRieszLiteralEmpiricalItoAdmissibility
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop :=
  ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceRieszPrimitiveLiteralEmpiricalIto P F T s β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))

/-- The empirical field of the literal physical admissibility is exactly this predicate. -/
theorem SourceRieszLiteralPhysicalItoAdmissibility.toEmpirical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0) (ρ₀ : E→ℝ)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszLiteralPhysicalItoAdmissibility P F T s β N k t ρ₀ f G X B) :
    SourceRieszLiteralEmpiricalItoAdmissibility P F T s β N k t f G X B :=
  h.empirical

/-- The empirical field of `SourceRieszPhysicalItoAdmissibility`: the same predicate with the
technical zero-extended force. -/
def SourceRieszPhysicalEmpiricalItoAdmissibility
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (t : Fin k→ℝ≥0)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) : Prop :=
  ∀ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ)
      (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) →
      SourceRieszPrimitiveEmpiricalIto P F T s β N k t f X B
        (fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
          (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b))

/-- The literal empirical predicate gives the physical one on a.e.-time collision-free slices. -/
theorem SourceRieszLiteralEmpiricalItoAdmissibility.to_physical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hs : 0<s) (N k : ℕ) (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (f : Fin k→ℝ→E→ℝ) (G : ℝ≥0) (X : ℝ→Ω→Fin N→E)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (h : SourceRieszLiteralEmpiricalItoAdmissibility P F T s β N k t f G X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    SourceRieszPhysicalEmpiricalItoAdmissibility P F T s β N k t f G X B := by
  intro V hV hVb he a r hr
  filter_upwards [h V hV hVb he a r hr,hc] with ω hI hcol
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

/-- Fixed Ito-integral martingales for the empirical test families, from the physical empirical Ito
predicate.  The coefficient `V` is the predictable physical coefficient, `m a` is the (continuous version
of the) normalised Ito integral `sqrt N * m a = sum_b ∫ V_b dB_b`, a continuous square-integrable
martingale started at `0`, and the empirical Ito identity holds at the terminal time `t a` with
`m a (t a)` as the stochastic term. -/
theorem exists_sourceRiesz_empirical_ito_fixed_martingales_of_physical
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (hSDE : SourceRieszFiniteHorizonWeakSDE P F T s β N X B)
    (hEmp : SourceRieszPhysicalEmpiricalItoAdmissibility P F T s β N k t f G X B) :
    ∃ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ) (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) ∧
      ∃ m : Fin k→ℝ→Ω→ℝ,
        (∀ a,Measurable (Function.uncurry (m a))) ∧
        (∀ a ω,m a 0 ω=0) ∧
        (∀ a,∀ᵐ ω ∂P,Continuous (fun r:ℝ=>m a r ω)) ∧
        (∀ a,Martingale (fun r:ℝ≥0=>m a (r:ℝ)) F P) ∧
        (∀ a (r:ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
        (∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),Real.sqrt N*m a r ω=
          sourceRieszBrownianFamilyProcess P F B T
            (fun b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
              (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b)) r ω) ∧
        ∀ a,∀ᵐ ω ∂P,
          (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
            (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
            (∫ r in Ioc 0 (t a:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N r (X r ω))+
              m a (t a:ℝ) ω := by
  classical
  let c := Real.sqrt (2/β)/Real.sqrt N
  let Xr := sourceRieszParticleRealHorizonExtension T N X
  have hXrSDE : SourceRieszAdditiveWeakSDE P F T s β N Xr B :=
    SourceRieszFiniteHorizonWeakSDE.extended P F T s β N X B hSDE
  let Xe := sourceRieszParticleHorizonExtension T N Xr
  have hXea := sourceRieszParticleHorizonExtension_adapted F T N Xr hXrSDE.adapted
  have hXec := sourceRieszParticleHorizonExtension_continuous P T N Xr hXrSDE.continuous_on_horizon
  have hext (a:Fin k) (r:ℝ≥0) (ω:Ω) (i:Fin N) :
      sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (Xe r ω i)=
        sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω i) :=
    (sourceRieszParticleHorizonExtension_stopped_gradient T (t a) (ht a) N Xr (f a) r ω i).trans
      (sourceRieszParticleRealHorizonExtension_stopped_gradient T (t a) (ht a) N X (f a) r ω i)
  obtain ⟨V,hV,hVb,hVz,hVe,hVm⟩ := exists_sourceRiesz_physical_fixed_martingales
    P F T N k hN t c f hgrad G hb Xe hXea hXec B hSDE.brownian
  have hVe' : ∀ᵐ ω ∂P,∀ a b r,V a b r ω=
      c*(sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 := by
    filter_upwards [hVe] with ω hω
    intro a b r
    rw [hω a b r,hext]
  let gV := fun a b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
    (|c| * (G:ℝ)) (hVb a b)
  obtain ⟨m,hmm,hm0,hmc,hMart,hLp,hme,-⟩ := hVm
  refine ⟨V,hV,hVb,hVe',m,hmm,hm0,hmc,hMart,hLp,hme,?_⟩
  intro a
  exact sourceRiesz_primitive_empirical_Ito_normalized_version P F T s β N k hN t f X B
    gV (hEmp V hV hVb hVe') m hme a (t a) le_rfl

/-- The same, from the literal empirical Ito predicate and the Riesz SDE. -/
theorem exists_sourceRiesz_empirical_ito_fixed_martingales
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (s β : ℝ) (hs : 0<s) (N k : ℕ) (hN : 0<N)
    (t : Fin k→ℝ≥0) (ht : ∀ a,t a≤T)
    (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ)
    (hSDE : SourceRieszFiniteHorizonWeakSDE P F T s β N X B)
    (hIto : SourceRieszLiteralEmpiricalItoAdmissibility P F T s β N k t f G X B)
    (hc : ∀ᵐ ω ∂P,∀ᵐ r ∂volume.restrict (Ioc 0 (T:ℝ)),
      ∀ i j:Fin N,i≠j → X r ω i≠X r ω j) :
    ∃ (V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ) (hV : ∀ a b,IsStronglyPredictable F (V a b))
      (hVb : ∀ a b r ω,‖V a b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)),
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
        (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) ∧
      ∃ m : Fin k→ℝ→Ω→ℝ,
        (∀ a,Measurable (Function.uncurry (m a))) ∧
        (∀ a ω,m a 0 ω=0) ∧
        (∀ a,∀ᵐ ω ∂P,Continuous (fun r:ℝ=>m a r ω)) ∧
        (∀ a,Martingale (fun r:ℝ≥0=>m a (r:ℝ)) F P) ∧
        (∀ a (r:ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
        (∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),Real.sqrt N*m a r ω=
          sourceRieszBrownianFamilyProcess P F B T
            (fun b=>sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
              (|Real.sqrt (2/β)/Real.sqrt N| * (G:ℝ)) (hVb a b)) r ω) ∧
        ∀ a,∀ᵐ ω ∂P,
          (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X (t a) ω))-
            (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X 0 ω))=
            (∫ r in Ioc 0 (t a:ℝ),sourceRieszEmpiricalTestDrift s β (f a) N r (X r ω))+
              m a (t a:ℝ) ω :=
  exists_sourceRiesz_empirical_ito_fixed_martingales_of_physical P F T s β N k hN t ht f hgrad G hb
    X B hSDE (hIto.to_physical P F T s β hs N k t ht f G X B hc)

/-- **Proposition 8.2 as printed, positive Riesz case, in the class of Theorem 2.13**
(`prop:finiteNAdjointDuality`, TeX 3859-3877; hypotheses as in
`exists_sourceRiesz_original_class_narrow_dynamic_joint_CLT`).

For `t ∈ [0,T]`, `φ ∈ 𝒟_T` and `f^r = U^{r,t} φ` there are constants `K, D` (depending on the class data
only, not on `N`, the probability space or the process) such that, for every `N ≥ 1` and every particle
system in the class, with `M_N^τ[f]` the normalised Ito integral of `∇f^r(x_i^r)` against the driving
Brownian motions (`sqrt N * M_N = sum_b ∫ V_b dB_b`, `V` the predictable physical coefficient), `M_N` is a
continuous square-integrable martingale started at `0` and almost surely
`S_N^t(φ) = S_N^0(f^0) + sqrt N M_N^t[f] - (sqrt N / 2) ∫_0^t A_1(∇f^r, X^r, μ^r) dr`,
with the last term integrable and of `L^1` norm at most `t D / (2 sqrt N)`. -/
theorem exists_sourceRiesz_original_class_finiteN_adjoint_duality
    (s β : ℝ) (T : ℝ≥0) (M Bmax : ℝ) (hs : 0<s) (hβ : 0<β)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (fun p:Icc (0:ℝ) (T:ℝ)×E=>ρ p.1 p.2))
    (hprob : ∀ r∈Icc 0 (T:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 (T:ℝ),∀ᵐ z ∂volume,ρ r z≤M)
    (Dtest : Submodule ℝ (E→ℝ))
    (hwp : SourceRieszBackwardClassicalWellPosed T s β ρ Dtest)
    (hdist : SourceRieszPVDistributionalWeakMeanField s β (T:ℝ) ρ)
    (μpath : ℝ → ProbabilityMeasure E)
    (hμpath : ContinuousOn μpath (Icc 0 (T:ℝ)))
    (hρμ : ∀ r∈Icc 0 (T:ℝ),(μpath r : Measure E)=gaussianRieszDensityMeasure (ρ r))
    (t : ℝ≥0) (ht : t≤T) (φ : E→ℝ) (hφD : φ∈Dtest) :
    let f := sourceRieszUprop T s β ρ Dtest hwp t ht φ hφD
    ∃ (K : ℝ≥0) (D : ℝ),0≤D ∧ (∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(K:ℝ)) ∧
    ∀ (Ω : Type u),∀ [mΩ : MeasurableSpace Ω],
    ∀ (ν : Measure Ω),∀ [IsProbabilityMeasure ν],
    ∀ (F : Filtration ℝ≥0 mΩ),∀ (N : ℕ),1≤N →
    ∀ (X : ℝ→Ω→Fin N→E) (B : (Fin N×ι)→ℝ≥0→Ω→ℝ),
    SourceRieszLiteralFiniteHorizonSDE ν F T s β N X B →
    ∀ (G Dg : ℝ→ℝ),(∀ r∈Icc 0 (T:ℝ),0≤G r) → (∀ r∈Icc 0 (T:ℝ),Dg r≤Bmax) →
    (∀ r∈Icc 0 (T:ℝ),
      sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N (ν.map (X r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
          (sourceRieszSingularGibbs s β (ρ 0) N)+(Dg r/(N:ℝ):ℝ)) →
    (∀ Gmax:ℝ≥0,(∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(Gmax:ℝ)) →
      SourceRieszLiteralEmpiricalItoAdmissibility ν F T s β N 1 (fun _=>t) (fun _=>f) Gmax X B) →
    ∃ (V : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hV : ∀ b,IsStronglyPredictable F (V b))
      (hVb : ∀ b r ω,‖V b r ω‖≤|Real.sqrt (2/β)/Real.sqrt N| * (K:ℝ)),
    (∀ᵐ ω ∂ν,∀ b r,V b r ω=(Real.sqrt (2/β)/Real.sqrt N)*
      (sourceRieszStoppedGradient (t:ℝ) f (r:ℝ) (X r ω b.1)) b.2) ∧
    ∃ m : ℝ→Ω→ℝ,
      Measurable (Function.uncurry m) ∧ (∀ ω,m 0 ω=0) ∧
      (∀ᵐ ω ∂ν,Continuous (fun r:ℝ=>m r ω)) ∧
      Martingale (fun r:ℝ≥0=>m (r:ℝ)) F ν ∧ (∀ r:ℝ≥0,MemLp (m (r:ℝ)) 2 ν) ∧
      (∀ᵐ ω ∂ν,∀ r:ℝ≥0,Real.sqrt N*m r ω=
        sourceRieszBrownianFamilyProcess ν F B T
          (fun b=>sourceRieszPredictableBoundedL2 ν F T (V b) (hV b)
            (|Real.sqrt (2/β)/Real.sqrt N| * (K:ℝ)) (hVb b)) r ω) ∧
      Integrable (fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω)))) ν ∧
      (∫ ω,|-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω)))| ∂ν)≤
        t*D/(2*Real.sqrt N) ∧
      ∀ᵐ ω ∂ν,
        Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ t) φ N (X t ω)=
          Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f 0) N (X 0 ω)+
            Real.sqrt N*m t ω+
          -((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
            sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω))) := by
  classical
  intro f
  have hsol : SourceRieszClassicalBackwardSolution s β ρ t φ f :=
    (sourceRieszUprop_spec T s β ρ Dtest hwp t ht φ hφD).1
  obtain ⟨C,hC,hb⟩ := hsol.bounded
  let K : ℝ≥0 := ⟨C,hC⟩
  have hgradK : ∀ r∈Icc 0 (t:ℝ),∀ z,‖gradient (f r) z‖≤(K:ℝ) :=
    fun r hr z=>(hb r hr z).2.1
  obtain ⟨D,hD,hfactory⟩ := exists_sourceRiesz_physical_adjoint_time_identity
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K
  refine ⟨K,D,hD,hgradK,?_⟩
  intro Ω _ ν _ F N hN X B hSDE G Dg hG hDg hE hIto
  have hT0 : (0:ℝ)≤T := T.coe_nonneg
  have htT : (t:ℝ)≤T := by exact_mod_cast ht
  have hsub (r:ℝ) (hr:r∈Icc 0 (t:ℝ)) : r∈Icc 0 (T:ℝ) := ⟨hr.1,hr.2.trans htT⟩
  have hN0 : 0<N := hN
  -- collision occupation and conversion of the literal SDE
  have hcollision := sourceRiesz_gronwall_particle_collision_time ν T s β M hs hβ hd hM N hN
    ρ X hSDE.measurable_on_horizon hprob hρ G Dg hE
  have hweakSDE : SourceRieszFiniteHorizonWeakSDE ν F T s β N X B :=
    SourceRieszLiteralFiniteHorizonSDE.to_weak ν F T s β hs N X B hSDE hcollision
  -- the weak mean-field class gives the time-tested identity for the backward solution
  have hstatic := SourceRieszPVDistributionalWeakMeanField.to_static s β (T:ℝ) hs hd hT0 ρ hprob M hM
    hρ hdist (sourceCompactTestContinuousTrace_of_narrow (T:ℝ) ρ μpath hμpath hρμ)
  have hevol := hstatic.classical_test_evolution s β (T:ℝ) hs hd hT0 ρ hprob M hM hρ
    t (by exact_mod_cast ht) φ f hsol
  have hweakId := (SourceRieszMeanFieldTestEvolution.time_test_identity s β (t:ℝ) t.coe_nonneg ρ f
    hevol).2
  -- Ito integral martingale
  have hgrad1 : ∀ a:Fin 1,ContinuousOn (fun p:ℝ×E=>gradient ((fun _:Fin 1=>f) a p.1) p.2)
      (Icc 0 (((fun _:Fin 1=>t) a:ℝ≥0):ℝ) ×ˢ univ) := fun _=>hsol.gradient_continuous
  obtain ⟨V,hV,hVb,hVe,m,hmm,hm0,hmc,hMart,hLp,hme,hEmp⟩ :=
    exists_sourceRiesz_empirical_ito_fixed_martingales ν F T s β hs N 1 hN0 (fun _=>t) (fun _=>ht)
      (fun _=>f) hgrad1 K (fun _ r hr z=>hgradK r hr z) X B hweakSDE
      (hIto K hgradK) hcollision
  -- clamp the density path so that it is jointly measurable on the whole line
  let ρe : ℝ→E→ℝ := fun r=>ρ (projIcc 0 (T:ℝ) hT0 r)
  have hρe : Measurable (Function.uncurry ρe) :=
    hρm.comp (((continuous_projIcc : Continuous (projIcc 0 (T:ℝ) hT0)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have heq (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : ρe r=ρ r := by
    dsimp only [ρe]; rw [projIcc_of_mem hT0 hr]
  have he0 : ρe 0=ρ 0 := heq 0 ⟨le_rfl,hT0⟩
  have het : ρe (t:ℝ)=ρ (t:ℝ) := heq _ (hsub _ ⟨t.coe_nonneg,le_rfl⟩)
  have heae : ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),ρe r=ρ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact heq r ⟨hr.1.le,hr.2.trans htT⟩
  have hpe : ∀ r∈Icc 0 (t:ℝ),IsProbabilityMeasure (gaussianRieszDensityMeasure (ρe r)) := by
    intro r hr; rw [heq r (hsub r hr)]; exact hprob r (hsub r hr)
  have hbe : ∀ r∈Icc 0 (t:ℝ),∀ᵐ z ∂volume,ρe r z≤M := by
    intro r hr; rw [heq r (hsub r hr)]; exact hρ r (hsub r hr)
  have hbacke : ∀ᵐ r ∂volume.restrict (Ioc 0 (t:ℝ)),∀ z,
      deriv (fun u=>f u z) r+β⁻¹*laplacian (f r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (f r) z-gradient (f r) y⟫
          ∂gaussianRieszDensityMeasure (ρe r) := by
    filter_upwards [SourceRieszClassicalBackwardSolution.backward_ae s β ρ t φ f hsol,heae]
      with r hr hrr
    simpa only [hrr] using hr
  have hweake : (∫ z,f (t:ℝ) z ∂gaussianRieszDensityMeasure (ρe (t:ℝ)))-
      (∫ z,f 0 z ∂gaussianRieszDensityMeasure (ρe 0))=
        ∫ r in Ioc 0 (t:ℝ),sourceRieszMeanTestDrift s β (ρe r) f r := by
    rw [het,he0,hweakId]
    apply integral_congr_ae
    filter_upwards [heae] with r hr
    rw [hr]
  -- horizon extension of the particle process, jointly measurable on the whole line
  let Xr := sourceRieszParticleRealHorizonExtension T N X
  have hXrm : Measurable (Function.uncurry Xr) :=
    sourceRieszParticleRealHorizonExtension_measurable T N X hSDE.measurable_on_horizon
  have hXr (r:ℝ) (hr:r∈Icc 0 (T:ℝ)) : Xr r=X r :=
    sourceRieszParticleRealHorizonExtension_eq T N X r hr
  have hEe : ∀ r∈Icc 0 (t:ℝ),
      sourceRieszTransportExtendedFreeEnergy (ρe r) s M β N (ν.map (Xr r))≤
        (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρe 0) s M β N
          (sourceRieszSingularGibbs s β (ρe 0) N)+(Dg r/(N:ℝ):ℝ) := by
    intro r hr
    rw [heq r (hsub r hr),he0,hXr r (hsub r hr)]
    exact hE r (hsub r hr)
  have hIe : ∀ᵐ ω ∂ν,
      (∫ z,f (t:ℝ) z ∂sourceRieszLocalEmpiricalLaw N (Xr (t:ℝ) ω))-
        (∫ z,f 0 z ∂sourceRieszLocalEmpiricalLaw N (Xr 0 ω))=
        (∫ r in Ioc 0 (t:ℝ),sourceRieszEmpiricalTestDrift s β f N r (Xr r ω))+m 0 (t:ℝ) ω := by
    filter_upwards [hEmp 0] with ω hω
    have hi : (∫ r in Ioc 0 (t:ℝ),sourceRieszEmpiricalTestDrift s β f N r (Xr r ω))=
        ∫ r in Ioc 0 (t:ℝ),sourceRieszEmpiricalTestDrift s β f N r (X r ω) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      change sourceRieszEmpiricalTestDrift s β f N r (Xr r ω)=_
      rw [hXr r (hsub r ⟨hr.1.le,hr.2⟩)]
    rw [hi,hXr (t:ℝ) (hsub _ ⟨t.coe_nonneg,le_rfl⟩),hXr 0 ⟨le_rfl,hT0⟩]
    exact hω
  obtain ⟨-,-,hid,-,hRi,hRb⟩ := hfactory (t:ℝ) t.coe_nonneg N hN Ω ν ρe hρe hpe hbe f
    hsol.spatial_contdiff (fun r hr z=>(hb r hr z).2.2) hsol.gradient_continuous C
    (fun r hr z=>(hb r hr z).1) hbacke Xr hXrm G Dg (fun r hr=>hG r (hsub r hr))
    (fun r hr=>hDg r (hsub r hr)) hEe (m 0 (t:ℝ)) hIe hweake
  -- return to the original density path and process on `[0,t]`
  have hRe : (fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
      sourceRieszLocalTransportEnergy (ρe r) s 1 (gradient (f r)) N (Xr r ω))))=
      (fun ω=>-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω)))) := by
    funext ω
    have hi : (∫ r in Ioc 0 (t:ℝ),sourceRieszLocalTransportEnergy (ρe r) s 1 (gradient (f r)) N (Xr r ω))=
        ∫ r in Ioc 0 (t:ℝ),sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro r hr
      change sourceRieszLocalTransportEnergy (ρe r) s 1 (gradient (f r)) N (Xr r ω)=_
      rw [heq r (hsub r ⟨hr.1.le,hr.2⟩),hXr r (hsub r ⟨hr.1.le,hr.2⟩)]
    rw [hi]
  rw [hRe] at hRi
  refine ⟨V 0,fun b=>hV 0 b,fun b r ω=>hVb 0 b r ω,?_,m 0,hmm 0,hm0 0,hmc 0,hMart 0,hLp 0,?_,hRi,?_,?_⟩
  · filter_upwards [hVe] with ω hω b r
    exact hω 0 b r
  · filter_upwards [hme] with ω hω r
    exact hω 0 r
  · have hh : (∫ ω,|-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
        sourceRieszLocalTransportEnergy (ρe r) s 1 (gradient (f r)) N (Xr r ω)))| ∂ν)=
        ∫ ω,|-((Real.sqrt N/2)*(∫ r in Ioc 0 (t:ℝ),
          sourceRieszLocalTransportEnergy (ρ r) s 1 (gradient (f r)) N (X r ω)))| ∂ν :=
      congrArg (fun g : Ω→ℝ=>∫ ω,|g ω| ∂ν) hRe
    rw [← hh]
    exact hRb
  · filter_upwards [hid] with ω hω
    obtain ⟨-,-,hω⟩ := hω
    have hts : f (t:ℝ)=φ := hsol.terminal
    have hRω := congrFun hRe ω
    rw [het,he0,hXr (t:ℝ) (hsub _ ⟨t.coe_nonneg,le_rfl⟩),hXr 0 ⟨le_rfl,hT0⟩,hts] at hω
    rw [← hRω]
    exact hω

end DGRHS.Commutator
#check @DGRHS.Commutator.SourceRieszLiteralEmpiricalItoAdmissibility
#print axioms DGRHS.Commutator.SourceRieszLiteralEmpiricalItoAdmissibility
#check @DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility.toEmpirical
#print axioms DGRHS.Commutator.SourceRieszLiteralPhysicalItoAdmissibility.toEmpirical
#check @DGRHS.Commutator.SourceRieszPhysicalEmpiricalItoAdmissibility
#print axioms DGRHS.Commutator.SourceRieszPhysicalEmpiricalItoAdmissibility
#check @DGRHS.Commutator.SourceRieszLiteralEmpiricalItoAdmissibility.to_physical
#print axioms DGRHS.Commutator.SourceRieszLiteralEmpiricalItoAdmissibility.to_physical
#check @DGRHS.Commutator.exists_sourceRiesz_empirical_ito_fixed_martingales_of_physical
#print axioms DGRHS.Commutator.exists_sourceRiesz_empirical_ito_fixed_martingales_of_physical
#check @DGRHS.Commutator.exists_sourceRiesz_empirical_ito_fixed_martingales
#print axioms DGRHS.Commutator.exists_sourceRiesz_empirical_ito_fixed_martingales
#check @DGRHS.Commutator.exists_sourceRiesz_original_class_finiteN_adjoint_duality
#print axioms DGRHS.Commutator.exists_sourceRiesz_original_class_finiteN_adjoint_duality
