import DGRHS.Gaussian.PeriodicBackwardInterface
import DGRHS.Gaussian.PeriodicDynamicSDE
import DGRHS.Gaussian.PeriodicRieszDynamicJointCLT

/-!
Packet P11c, unit 4 (Riesz, part 3): Theorem 2.13 (`thm:dynamicLinearStatisticsCLT`, TeX 862-914) on the
flat torus (Remark 2.1), positive Riesz case `0 < s < d/2`, with the selected unique classical backward
solutions `U^{r,t} φ`, in the lifted particle formulation of `PeriodicDynamicSDE`.

Torus form of `exists_sourceRiesz_named_Uprop_dynamic_joint_CLT`.  Hypotheses transposed from the printed
statement: (i) the SDE with the periodic force, independence of the drivers from the initial
configuration, `f_N^0 = Q_{N,β}(μ^0)`, the free-energy Gronwall estimate in the extended convention, the
uniform controls `‖μ^t‖_∞ ≤ M`, `B^t ≤ Bmax`; (ii) the partition bounds
`K_{N,β}(μ^t) ≤ Cpart`, `K_{N,2β}(μ^t) ≤ C₂` (the lower bound `K ≥ 1` is derived for Riesz, Jensen);
(iii) the real linear test space `𝒟_T` with its unique classical backward solutions.  The Itô formulas
"used below" are the predicates of `PeriodicItoAdmissibility`; the mean-field class enters in its
time-tested form `PeriodicMeanFieldTimeTested` (TeX 3897-3904), see the return packet.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The mean-field solution class in the form used by the proof: the weak formulation of the
McKean-Vlasov equation tested against each classical backward solution `f^r` (TeX 3897-3904). -/
def PeriodicMeanFieldTimeTested (T : ℝ≥0) (F : PeriodicTorus ι → E) (β : ℝ)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (D : Submodule ℝ (PeriodicTorus ι → ℝ)) : Prop :=
  ∀ t : ℝ≥0, t ≤ T → ∀ φ : PeriodicTorus ι → ℝ, φ ∈ D → ∀ f : ℝ → PeriodicTorus ι → ℝ,
    PeriodicClassicalBackwardSolution F β ρ t φ f →
      (∫ z, f (t : ℝ) z ∂periodicCappedDensityMeasure (ρ (t : ℝ))) -
        (∫ z, f 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t : ℝ), periodicMeanTestDrift F β (ρ r) f r

/-- Theorem 2.13 (`thm:dynamicLinearStatisticsCLT`, TeX 862-914) on the flat torus, positive Riesz case
`0 < s < d/2`, named propagator `U^{r,t} φ`, lifted particle formulation; the mean-field class enters in its
time-tested form `PeriodicMeanFieldTimeTested` (conditional form: the printed-class export, which derives that
form, is `exists_periodicRiesz_original_class_dynamic_joint_CLT`). -/
theorem exists_periodicRiesz_named_Uprop_dynamic_joint_CLT
    (s β : ℝ) (T : ℝ≥0) (M Bmax Cpart C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax)
    (k : ℕ) (t : Fin k → ℝ≥0) (ht : ∀ a, t a ≤ T)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 (T : ℝ), IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (hCp : ∀ r ∈ Icc 0 (T : ℝ), ∀ N' : ℕ, 1 ≤ N' →
      (periodicRieszSingularPartition s β hs2 (ρ r) N').toReal ≤ Cpart)
    (hC₂ : ∀ r ∈ Icc 0 (T : ℝ), ∀ N' : ℕ, 1 ≤ N' →
      (periodicRieszSingularPartition s (2 * β) hs2 (ρ r) N').toReal ≤ C₂)
    (Dtest : Submodule ℝ (PeriodicTorus ι → ℝ))
    (hwp : PeriodicBackwardClassicalWellPosed T (periodicRieszForceData s hs hs2).F β ρ Dtest)
    (hmean : PeriodicMeanFieldTimeTested T (periodicRieszForceData s hs hs2).F β ρ Dtest)
    (φ : Fin k → PeriodicTorus ι → ℝ) (hφD : ∀ a, φ a ∈ Dtest) :
    let f := fun a => periodicUprop T (periodicRieszForceData s hs hs2).F β ρ Dtest hwp (t a) (ht a)
      (φ a) (hφD a)
    ((∀ a, ∀ r ∈ Icc 0 (t a : ℝ),
      Integrable (f a r) (periodicCappedDensityMeasure (ρ r)) ∧
      (∀ z, Integrable (fun y => ⟪(periodicRieszForceData s hs hs2).F (z - y),
        periodicGrad (f a r) z - periodicGrad (f a r) y⟫) (periodicCappedDensityMeasure (ρ r))) ∧
      Integrable (periodicForcePair (periodicRieszForceData s hs hs2).F (periodicGrad (f a r)))
        ((periodicCappedDensityMeasure (ρ r)).prod (periodicCappedDensityMeasure (ρ r)))) ∧
    (∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a : ℝ)),
      Integrable (fun z => deriv (fun u => f a u z) r + β⁻¹ * periodicLap (f a r) z)
        (periodicCappedDensityMeasure (ρ r)))) ∧
    let μ := periodicCappedDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let hh := periodicRieszCentered_memLp s hs2 (ρ 0) M (hρ 0 ⟨le_rfl, T.coe_nonneg⟩)
    ∃ (hφ : ∀ a, MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R0 v + β • integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b =>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ +
          (2 / β) * (∫ r in Ioc 0 (min (t a : ℝ) (t b : ℝ)),
            ∫ z, ⟪periodicGrad (f a r) z, periodicGrad (f b r) z⟫ ∂periodicCappedDensityMeasure (ρ r))
      let P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k, (∫ z, z a ∂P) = 0) ∧
      (∀ a b : Fin k, Integrable (fun z => z a * z b) P ∧ (∫ z, z a * z b ∂P) = C a b) ∧
      ∀ (Ω : ℕ → Type v) [∀ N, MeasurableSpace (Ω N)] (ν : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (ν N)]
        (Fil : ∀ N, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω N)))
        (X : ∀ N, ℝ → Ω N → Fin N → E) (B : ∀ N, (Fin N × ι) → ℝ≥0 → Ω N → ℝ),
      (∀ N, 1 ≤ N → PeriodicFiniteHorizonWeakSDE (periodicRieszForceData s hs hs2).F (ν N) (Fil N) T β N
        (X N) (B N)) →
      (∀ N, 1 ≤ N → PeriodicInitialGibbsBrownianData (ν N) (periodicRieszSingularGibbs s β hs2 (ρ 0) N)
        (X N 0) (B N)) →
      ∀ (G D : ℝ → ℝ), (∀ r ∈ Icc 0 (T : ℝ), 0 ≤ G r) → (∀ r ∈ Icc 0 (T : ℝ), D r ≤ Bmax) →
      (∀ N, 1 ≤ N → ∀ r (hr : r ∈ Icc 0 (T : ℝ)), haveI := hprob r hr;
        haveI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩;
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N
          ((ν N).map (fun ω => periodicProj N (X N r ω))) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (D r / (N : ℝ) : ℝ)) →
      (∀ Gmax : ℝ≥0, (∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ)) →
        ∀ N, 1 ≤ N → PeriodicItoAdmissibility (periodicRieszForceData s hs hs2).F (ν N) (Fil N) T β N k t
          μ f Gmax (X N) (B N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
          Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (φ a) N
            (periodicProj N (X N (t a) ω))))
        atTop id ν P := by
  classical
  intro f
  have hsol (a : Fin k) : PeriodicClassicalBackwardSolution (periodicRieszForceData s hs hs2).F β ρ (t a)
      (φ a) (f a) :=
    (periodicUprop_spec T (periodicRieszForceData s hs hs2).F β ρ Dtest hwp (t a) (ht a) (φ a) (hφD a)).1
  have hproper (a : Fin k) := PeriodicClassicalBackwardSolution.spatial_properness
    (periodicRieszForceData s hs hs2) β (t a) ρ M hM
      (fun r hr => hprob r ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.mpr (ht a))⟩)
      (fun r hr => hρ r ⟨hr.1, hr.2.trans (NNReal.coe_le_coe.mpr (ht a))⟩) (φ a) (f a) (hsol a)
  refine ⟨⟨fun a => (hproper a).1, fun a => (hproper a).2⟩, ?_⟩
  obtain ⟨C, hC, hbound⟩ := periodicClassicalBackwardSolution_finite_bounds
    (periodicRieszForceData s hs hs2).F β ρ k t φ f hsol
  let K : ℝ≥0 := ⟨C, hC⟩
  have hgradBound : ∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (K : ℝ) :=
    fun a r hr z => (hbound a r hr (periodicCenteredLift z)).2.1
  have hLbound : ∀ a, ∀ r ∈ Icc 0 (t a : ℝ), ∀ z, |f a r z| ≤ C := by
    intro a r hr z
    have := (hbound a r hr (periodicCenteredLift z)).1
    simpa only [periodicLiftFn, periodicLift_centeredLift] using this
  letI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩
  obtain ⟨hφ, hSym, hCan, R0, hR1, hR2, hPSD, hP, hGauss, hMean, hCov, huse⟩ :=
    exists_periodicRiesz_dynamic_joint_CLT s β (T : ℝ) M Bmax Cpart C₂ hs hβ T.coe_nonneg hs2 hM hBmax
      K K k (fun a => (t a : ℝ)) (fun a => ⟨(t a).coe_nonneg, ht a⟩) ρ hρm hprob hρ hCp hC₂ f
      (fun a => (hsol a).spatial_contdiff) (fun a r hr z => (hbound a r hr z).2.2)
      (fun a => (hsol a).gradient_continuous) hgradBound C hLbound
      (fun a => PeriodicClassicalBackwardSolution.backward_ae _ β ρ (t a) (φ a) (f a) (hsol a))
  refine ⟨hφ, hSym, hCan, R0, hR1, hR2, hPSD, hP, hGauss, hMean, hCov, ?_⟩
  intro Ω _ ν _ Fil X B hSDE hInitial G D hG hD hE hIto
  let Xe := fun N => sourceRieszParticleRealHorizonExtension T N (X N)
  have he (N : ℕ) (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : Xe N r = X N r :=
    sourceRieszParticleRealHorizonExtension_eq T N (X N) r hr
  let Xτ := fun (N : ℕ) (r : ℝ) (ω : Ω N) => periodicProj N (Xe N r ω)
  have hXτm (N : ℕ) : Measurable (Function.uncurry (Xτ N)) := by
    by_cases hN : 1 ≤ N
    · exact (measurable_periodicProj N).comp
        (sourceRieszParticleRealHorizonExtension_measurable T N (X N) (hSDE N hN).measurable_on_horizon)
    · have hN0 : N = 0 := by omega
      subst N
      apply Measurable.of_eval
      intro i
      exact Fin.elim0 i
  have hLaw (N : ℕ) (hN : 1 ≤ N) :
      (ν N).map (Xτ N 0) = periodicRieszSingularGibbs s β hs2 (ρ 0) N := by
    have h0 : Xτ N 0 = fun ω => periodicProj N (X N 0 ω) := by
      funext ω
      change periodicProj N (Xe N 0 ω) = _
      rw [he N 0 ⟨le_rfl, T.coe_nonneg⟩]
    rw [h0]
    exact (hInitial N hN).initial_gibbs
  have hEe (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      haveI := hprob r hr; haveI := hprob 0 ⟨le_rfl, T.coe_nonneg⟩;
      periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N ((ν N).map (Xτ N r)) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (D r / (N : ℝ) : ℝ) := by
    have h := hE N hN r hr
    have h1 : Xτ N r = fun ω => periodicProj N (X N r ω) := by
      funext ω
      change periodicProj N (Xe N r ω) = _
      rw [he N r hr]
    rw [h1]
    exact h
  have hf0 (a : Fin k) : Measurable (f a 0) :=
    measurable_of_contDiff_lift (((hsol a).spatial_contdiff 0 ⟨le_rfl, (t a).coe_nonneg⟩).of_le (by norm_num))
  have hex (n : {N : ℕ // 1 ≤ N}) := exists_periodic_fixed_martingale_inputs
    (periodicRieszForceData s hs hs2).F (ν n.1) (Fil n.1) T β hβ n.1 k (Nat.succ_le_iff.mp n.2) t ht
    (periodicCappedDensityMeasure (ρ 0)) f hf0 (fun a => (hsol a).gradient_continuous) K hgradBound
    (Xe n.1) (B n.1)
    (PeriodicFiniteHorizonWeakSDE.extended _ (ν n.1) (Fil n.1) T β n.1 (X n.1) (B n.1) (hSDE n.1 n.2))
    (PeriodicItoAdmissibility.horizon_extension _ (ν n.1) (Fil n.1) T β n.1 k t ht _ f K (X n.1) (B n.1)
      (hIto K hgradBound n.1 n.2))
  choose m hmm hm0 hmc hMart hLp hEmp hPhase using hex
  let mAll := fun (N : ℕ) => if hN : 1 ≤ N then m ⟨N, hN⟩ else fun (_ : Fin k) (_ : ℝ) (_ : Ω N) => (0 : ℝ)
  have hweak (a : Fin k) := hmean (t a) (ht a) (φ a) (hφD a) (f a) (hsol a)
  have hlim := huse Ω ν Xτ hXτm hLaw G D hG hD hEe mAll
    (fun N hN a => by simpa only [mAll, dite_eq_left hN] using hmm ⟨N, hN⟩ a)
    (fun N hN a ω => by simpa only [mAll, dite_eq_left hN] using hm0 ⟨N, hN⟩ a ω)
    (fun N hN a => by simpa only [mAll, dite_eq_left hN] using hEmp ⟨N, hN⟩ a)
    hweak
    (fun θ N hN => by simpa only [mAll, dite_eq_left hN] using hPhase ⟨N, hN⟩ θ)
  have hobs : (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
      Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N
        (Xτ N (t a) ω))) =
      (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
        Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (φ a) N
          (periodicProj N (X N (t a) ω)))) := by
    funext N ω
    congr 1
    funext a
    have h1 : Xτ N (t a) ω = periodicProj N (X N (t a) ω) := by
      change periodicProj N (Xe N (t a) ω) = _
      rw [he N (t a) ⟨(t a).coe_nonneg, NNReal.coe_le_coe.mpr (ht a)⟩]
    rw [h1, (hsol a).terminal]
  rw [hobs] at hlim
  exact hlim

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_periodicRiesz_named_Uprop_dynamic_joint_CLT
