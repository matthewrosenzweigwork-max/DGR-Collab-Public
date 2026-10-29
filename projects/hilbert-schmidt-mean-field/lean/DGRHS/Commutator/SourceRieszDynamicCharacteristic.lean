import DGRHS.Commutator.SourceRieszCharacteristicLimit

/-! Original positive-Riesz source4015--4024 characteristic limit on the
actual particle probability spaces. The initial law is the literal Gibbs
law, the initial covariance uses its actual mean-zero resolvent, and every
finite-N comparison is derived from original physical Gr, native backward
PDE and primitive time/phase Ito admissibility. No CF limit, factorization,
terminal representation or bracket replacement is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_dynamic_characteristic
    (s β T M Bmax : ℝ) (hs : 0<s) (hβ : 0<β) (hT : 0≤T)
    (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) (K Gmax : ℝ≥0)
    (k : ℕ) (t : Fin k→ℝ) (ht : ∀ a,t a∈Icc 0 T)
    (ρ : ℝ→E→ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r∈Icc 0 T,IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ r)))
    (hρ : ∀ r∈Icc 0 T,∀ᵐ z ∂volume,ρ r z≤M)
    (f : Fin k→ℝ→E→ℝ) (hf : ∀ a,∀ r∈Icc 0 (t a),ContDiff ℝ 2 (f a r))
    (hK : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖iteratedFDeriv ℝ 2 (f a r) z‖≤(K:ℝ))
    (hgrad : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2) (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a,∀ r∈Icc 0 (t a),∀ z,‖gradient (f a r) z‖≤(Gmax:ℝ))
    (L : ℝ) (hL : ∀ a,∀ r∈Icc 0 (t a),∀ z,|f a r z|≤L)
    (hback : ∀ a,∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),∀ z,
      deriv (fun u=>f a u z) r+β⁻¹*laplacian (f a r) z=
        ∫ y,⟪sourceRieszForce s (z-y),gradient (f a r) z-gradient (f a r) y⟫
          ∂gaussianRieszDensityMeasure (ρ r)) :
    let μ := gaussianRieszDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl,hT⟩
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let hh := memLp_gaussianRieszCenteredPhysicalPair s hs (by linarith) (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩)
    ∃ (hφ : ∀ a,MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ,h p.swap=h p)
      (hCan : ∀ᵐ x ∂μ,(∫ y,h (x,y) ∂μ)=0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v,R0 v+β • integralOperatorOnMeanZero h hh hSym hCan (R0 v)=v) ∧
      (∀ v,R0 (v+β • integralOperatorOnMeanZero h hh hSym hCan v)=v) ∧
      ∀ (Ω : ℕ→Type u),∀ [∀ N,MeasurableSpace (Ω N)],
      ∀ (ν : ∀ N,Measure (Ω N)),∀ [∀ N,IsProbabilityMeasure (ν N)],
      ∀ (X : ∀ N,ℝ→Ω N→Fin N→E),(∀ N,Measurable (Function.uncurry (X N))) →
      (∀ N,1≤N → (ν N).map (X N 0)=sourceRieszSingularGibbs s β (ρ 0) N) →
      ∀ (G B : ℝ→ℝ),(∀ r∈Icc 0 T,0≤G r) → (∀ r∈Icc 0 T,B r≤Bmax) →
      (∀ N,1≤N → ∀ r∈Icc 0 T,
        sourceRieszTransportExtendedFreeEnergy (ρ r) s M β N ((ν N).map (X N r))≤
          (G r:EReal)*sourceRieszTransportExtendedFreeEnergy (ρ 0) s M β N
            (sourceRieszSingularGibbs s β (ρ 0) N)+(B r/(N:ℝ):ℝ)) →
      ∀ (m : ∀ N,Fin k→ℝ→Ω N→ℝ),
      (∀ N,1≤N → ∀ a,Measurable (Function.uncurry (m N a))) →
      (∀ N,1≤N → ∀ a,∀ ω,m N a 0 ω=0) →
      (∀ N,1≤N → ∀ a,∀ᵐ ω ∂ν N,
        (∫ z,f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X N (t a) ω))-
          (∫ z,f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X N 0 ω))=
          (∫ r in Ioc 0 (t a),sourceRieszEmpiricalTestDrift s β (f a) N r (X N r ω))+m N a (t a) ω) →
      (∀ a,(∫ z,f a (t a) z ∂gaussianRieszDensityMeasure (ρ (t a)))-
        (∫ z,f a 0 z ∂gaussianRieszDensityMeasure (ρ 0))=
        ∫ r in Ioc 0 (t a),sourceRieszMeanTestDrift s β (ρ r) (f a) r) →
      (∀ (θ : Fin k→ℝ) (N : ℕ),1≤N →
        let A₀ := fun ω=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X N 0 ω))
        let W := fun r ω=>∑ a,θ a*(Real.sqrt N*m N a (min r (t a)) ω)
        let S := fun r z=>‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
        let Φ := fun r ω=>sourceRieszFinitePhase (A₀ ω+W r ω)
        let chi := fun r=>∫ ω,Φ r ω ∂ν N
        ∀ r∈Icc 0 T,chi r=chi 0-(1/β:ℝ) •
          (∫ u in 0..r,∫ ω,Φ u ω*((∫ z,S u z ∂sourceRieszLocalEmpiricalLaw N (X N u ω) : ℝ):ℂ) ∂ν N)) →
      ∀ θ : Fin k→ℝ,Tendsto (fun N=>∫ ω,sourceRieszFinitePhase
        (∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω))) ∂ν N)
        atTop (𝓝 (Complex.exp (-(∑ a,∑ b,θ a*θ b*
          ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2-
            ((1/β)*(∫ r in 0..T,∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
              ∂gaussianRieszDensityMeasure (ρ r)) : ℝ)))) := by
  let μ := gaussianRieszDensityMeasure (ρ 0)
  letI := hprob 0 ⟨le_rfl,hT⟩
  have hφm (a : Fin k) : Measurable (f a 0) := (hf a 0 ⟨le_rfl,(ht a).1⟩).continuous.measurable
  have hφ (a : Fin k) : MemLp (f a 0) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall fun z=>abs_le.mp (hL a 0 ⟨le_rfl,(ht a).1⟩ z))
      (hφm a).aestronglyMeasurable 2
  obtain ⟨hSym,hCan,R0,hR1,hR2,hinit⟩ := exists_sourceRiesz_raw_initial_characteristic
    k s β hs hβ.le (by linarith) (ρ 0) M hM (hρ 0 ⟨le_rfl,hT⟩)
  refine ⟨hφ,hSym,hCan,R0,hR1,hR2,?_⟩
  intro Ω _ ν _ X hXm hLaw G B hG hB hE m hmm hm0 hIto hweak hphase θ
  obtain ⟨Dc,Dl,hDc,hDl,hcompare⟩ := exists_sourceRiesz_finite_terminal_CF_comparison
    (ι:=ι) s β M Bmax hs hβ hd hM hBmax K Gmax
  let C := T*Dc*(∑ a,|θ a|)/2+
    Real.exp ((((Gmax:ℝ)*(∑ a,|θ a|))^2/β)*T)*T*Dl*(∑ a,|θ a|)^2
  let A := fun (N : ℕ) (ω : Ω N)=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ 0) (f a 0) N (X N 0 ω))
  let Z := fun (N : ℕ) (ω : Ω N)=>∑ a,θ a*(Real.sqrt N*sourceRieszDynamicEmpiricalDifference (ρ (t a)) (f a (t a)) N (X N (t a) ω))
  let V := (1/β)*(∫ r in 0..T,∫ z,‖∑ a,θ a • sourceRieszStoppedGradient (t a) (f a) r z‖^2
    ∂gaussianRieszDensityMeasure (ρ r))
  have hI := hinit (fun a=>f a 0) hφm hφ Ω ν (fun N=>X N 0)
    (fun N=>(hXm N).comp (measurable_const.prodMk measurable_id)) hLaw θ
  have hh := sourceRiesz_sqrt_rate_CF_limit
    (fun N=>∫ ω,sourceRieszFinitePhase (Z N ω) ∂ν N)
    (fun N=>∫ ω,sourceRieszFinitePhase (A N ω) ∂ν N)
    (Complex.exp (-(∑ a,∑ b,θ a*θ b*
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2))
    (Real.exp (-V):ℂ) C hI (fun N hN=>by
      have hc := hcompare T hT k t θ ht N hN (Ω N) (ν N) ρ hρm hprob hρ f hf hK hgrad hfB
        L hL hback (X N) (hXm N) G B hG hB (hE N hN) (m N) (hmm N hN)
        (hm0 N hN) (hIto N hN) hweak (hphase θ N hN)
      calc
        _ ≤ T*Dc*(∑ a,|θ a|)/(2*Real.sqrt N)+
            Real.exp ((((Gmax:ℝ)*(∑ a,|θ a|))^2/β)*T)*
              (T*Dl*(∑ a,|θ a|)^2/Real.sqrt N) := by
                simpa only [V,Z,A,neg_mul] using hc
        _ = C/Real.sqrt N := by dsimp only [C];ring)
  have he : Complex.exp (-(∑ a,∑ b,θ a*θ b*
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2)*
      (Real.exp (-V):ℂ)=
    Complex.exp (-(∑ a,∑ b,θ a*θ b*
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)),R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ)/2-(V:ℝ)) := by
    rw [Complex.ofReal_exp,←Complex.exp_add,Complex.ofReal_neg]
    rfl
  rw [he] at hh
  exact hh

end DGRHS.Commutator
set_option pp.deepTerms true in
#check @DGRHS.Commutator.exists_sourceRiesz_dynamic_characteristic
#print axioms DGRHS.Commutator.exists_sourceRiesz_dynamic_characteristic
