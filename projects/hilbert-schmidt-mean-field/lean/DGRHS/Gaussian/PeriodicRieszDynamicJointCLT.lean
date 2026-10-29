import DGRHS.Gaussian.PeriodicDynamicCovariance
import DGRHS.Gaussian.PeriodicProp82CF
import DGRHS.Gaussian.PeriodicRieszCanonicalRate
import DGRHS.Gaussian.PeriodicRieszTheorem211
import DGRHS.Commutator.SourceRieszCharacteristicLimit
import DGRHS.Dynamics.SourceDynamicCovarianceTypes
import DGRHS.Kernel.MeanZeroResolventUnique

/-!
Packet P11c, unit 4 (Riesz, part 2): the joint dynamical CLT of Theorem 2.13 (TeX 862-914) on the torus
from the primitive finite-`N` inputs: the characteristic-function limit
(TeX 4003-4024: static initial limit `periodicRieszSingularStatic` + Proposition 8.2 comparison with the
`N^{-1/2}` rate), the Gaussian target with covariance (2.42), and Lévy continuity.  Torus form of
`exists_sourceRiesz_dynamic_joint_CLT`; the density path is measurable on `ℝ × 𝕋^d` (the path outside
`[0,T]` plays no role).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Laplacian Set Filter
open scoped NNReal ENNReal RealInnerProductSpace BigOperators Topology Classical Interval
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.CLT DGRHS.Dynamics DGRHS.Kernel
universe u v
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The `L²` representative of a bounded test gives a.e. the raw fluctuation under any law that is
absolutely continuous with respect to the product law. -/
theorem periodic_L2_raw_fluctuation_ae (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : Measure (Fin N → PeriodicTorus ι)) (hQ : Q ≪ Measure.pi (fun _ : Fin N => μ))
    (k : ℕ) (φ : Fin k → PeriodicTorus ι → ℝ) (hφ : ∀ a, MemLp (φ a) 2 μ) :
    (fun x : Fin N → PeriodicTorus ι => sourceObservableFluctuation (fun a => (hφ a).toLp (φ a)) N x)
      =ᵐ[Q] (fun x a => Real.sqrt N * dynEmpiricalDifference μ (φ a) N x) := by
  have he (a : Fin k) (i : Fin N) : ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (hφ a).toLp (φ a) (x i) = φ a (x i) :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae (hφ a).coeFn_toLp
  have hm (a : Fin k) : (∫ z, (hφ a).toLp (φ a) z ∂μ) = ∫ z, φ a z ∂μ :=
    integral_congr_ae (hφ a).coeFn_toLp
  have hid : (fun x : Fin N → PeriodicTorus ι => sourceObservableFluctuation (fun a => (hφ a).toLp (φ a)) N x)
      =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x a => Real.sqrt N * dynEmpiricalDifference μ (φ a) N x) := by
    filter_upwards [ae_all_iff.mpr (fun a => ae_all_iff.mpr (he a))] with x hx
    funext a
    unfold sourceObservableFluctuation dynEmpiricalDifference
    rw [integral_sourceRieszLocalEmpiricalLaw, hm a]
    simp_rw [hx a]
  exact hQ.ae_le hid

/-- Static initial data (Proposition 2.11 on the torus, Riesz): the mean-zero resolvent and the raw
initial characteristic limit, together with the Gaussian witness for the initial covariance. -/
theorem periodicRiesz_static_initial (k : ℕ) (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let hh := periodicRieszCentered_memLp s hs2 ρ M hρ
    ∃ (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R0 v + β • integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      (∀ (φ : Fin k → PeriodicTorus ι → ℝ), (∀ a, Measurable (φ a)) →
        ∀ (hφ : ∀ a, MemLp (φ a) 2 μ),
        ∀ (Ω : ℕ → Type v) [∀ N, MeasurableSpace (Ω N)] (ν : ∀ N, Measure (Ω N))
          [∀ N, IsProbabilityMeasure (ν N)] (X₀ : ∀ N, Ω N → Fin N → PeriodicTorus ι),
        (∀ N, Measurable (X₀ N)) →
        (∀ N, 1 ≤ N → (ν N).map (X₀ N) = periodicRieszSingularGibbs s β hs2 ρ N) →
        ∀ θ : Fin k → ℝ, Tendsto (fun N => ∫ ω, sourceRieszFinitePhase
          (∑ a, θ a * (Real.sqrt N * dynEmpiricalDifference μ (φ a) N (X₀ N ω))) ∂ν N)
          atTop (𝓝 (Complex.exp (-(∑ a, ∑ b, θ a * θ b *
            ⟪sourceCenteredL2 ((hφ a).toLp (φ a)), R0 (sourceCenteredL2 ((hφ b).toLp (φ b)))⟫ : ℝ) / 2)))) ∧
      (∀ φ : Fin k → Lp ℝ 2 μ, ∃ (P : Measure (ℕ → ℝ)) (Z : (ℕ → ℝ) → Fin k → ℝ)
        (_ : IsProbabilityMeasure P), HasGaussianLaw Z P ∧ (∀ a, MemLp (fun ω => Z ω a) 2 P) ∧
        (∀ a, (∫ ω, Z ω a ∂P) = 0) ∧
        (∀ a b, Integrable (fun ω => Z ω a * Z ω b) P ∧
          (∫ ω, Z ω a * Z ω b ∂P) = ⟪sourceCenteredL2 (φ a), R0 (sourceCenteredL2 (φ b))⟫)) := by
  intro μ h hh
  obtain ⟨hSym, hCan, R0, hR1, hR2, hfactory⟩ := exists_periodicRieszSingularStatic k s β hs hβ hs2 ρ M hM hρ
  refine ⟨hSym, hCan, R0, hR1, hR2, ?_, ?_⟩
  · intro φ hφm hφ Ω _ ν _ X₀ hX₀ hLaw θ
    obtain ⟨P, Z, hP, hPN, -, -, -, -, hCF, -⟩ := hfactory (fun a => (hφ a).toLp (φ a))
    apply (hCF θ).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    let V := fun x : Fin N → PeriodicTorus ι => sourceRieszFinitePhase
      (∑ a, θ a * (Real.sqrt N * dynEmpiricalDifference μ (φ a) N x))
    have hV : Measurable V := measurable_sourceRieszFinitePhase.comp
      (Finset.measurable_sum _ fun a _ => (((measurable_dynEmpiricalDifference μ (φ a) (hφm a) N hN).const_mul _).const_mul _))
    have hQac : periodicRieszSingularGibbs s β hs2 ρ N ≪ Measure.pi (fun _ : Fin N => μ) :=
      withDensity_absolutelyContinuous _ _
    calc
      _ = ∫ x, V x ∂periodicRieszSingularGibbs s β hs2 ρ N := by
        apply integral_congr_ae
        filter_upwards [periodic_L2_raw_fluctuation_ae μ N _ hQac k φ hφ] with x hx
        change Complex.exp ((∑ a, θ a * sourceObservableFluctuation (fun a => (hφ a).toLp (φ a)) N x a : ℝ) *
          Complex.I) = _
        have hh := congrFun hx
        simp_rw [hh]
        simp only [V, sourceRieszFinitePhase, mul_comm]
      _ = ∫ ω, V (X₀ N ω) ∂ν N := by
        rw [← hLaw N hN, integral_map (hX₀ N).aemeasurable hV.aestronglyMeasurable]
  · intro φ
    obtain ⟨P, Z, hP, hPN, -, hZ, hMean, hCov, -, -⟩ := hfactory φ
    exact ⟨P, Z, hP, hZ, fun a => (hZ.map_fun (ContinuousLinearMap.proj a)).memLp_two, hMean, hCov⟩

/-- Theorem 2.13, joint CLT from the primitive finite-`N` inputs, torus Riesz. -/
theorem exists_periodicRiesz_dynamic_joint_CLT
    (s β T M Bmax Cpart C₂ : ℝ) (hs : 0 < s) (hβ : 0 < β) (hT : 0 ≤ T)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) (hBmax : 0 ≤ Bmax) (K Gmax : ℝ≥0)
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ a, t a ∈ Icc 0 T)
    (ρ : ℝ → PeriodicTorus ι → ℝ) (hρm : Measurable (Function.uncurry ρ))
    (hprob : ∀ r ∈ Icc 0 T, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ r)))
    (hρ : ∀ r ∈ Icc 0 T, ∀ᵐ z ∂periodicHaar ι, ρ r z ≤ M)
    (hCp : ∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' → (periodicRieszSingularPartition s β hs2 (ρ r) N').toReal ≤ Cpart)
    (hC₂ : ∀ r ∈ Icc 0 T, ∀ N' : ℕ, 1 ≤ N' →
      (periodicRieszSingularPartition s (2 * β) hs2 (ρ r) N').toReal ≤ C₂)
    (f : Fin k → ℝ → PeriodicTorus ι → ℝ)
    (hf : ∀ a, ∀ r ∈ Icc 0 (t a), ContDiff ℝ 2 (periodicLiftFn (f a r)))
    (hK : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖iteratedFDeriv ℝ 2 (periodicLiftFn (f a r)) z‖ ≤ (K : ℝ))
    (hgrad : ∀ a, ContinuousOn (fun p : ℝ × E => gradient (periodicLiftFn (f a p.1)) p.2)
      (Icc 0 (t a) ×ˢ univ))
    (hfB : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, ‖periodicGrad (f a r) z‖ ≤ (Gmax : ℝ))
    (L : ℝ) (hL : ∀ a, ∀ r ∈ Icc 0 (t a), ∀ z, |f a r z| ≤ L)
    (hback : ∀ a, ∀ᵐ r ∂volume.restrict (Ioc 0 (t a)),
      PeriodicBackwardEq (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) :
    let μ := periodicCappedDensityMeasure (ρ 0)
    letI := hprob 0 ⟨le_rfl, hT⟩
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    let hh := periodicRieszCentered_memLp s hs2 (ρ 0) M (hρ 0 ⟨le_rfl, hT⟩)
    ∃ (hφ : ∀ a, MemLp (f a 0) 2 μ)
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (R0 : meanZeroL2 μ →L[ℝ] meanZeroL2 μ),
      (∀ v, R0 v + β • integralOperatorOnMeanZero h hh hSym hCan (R0 v) = v) ∧
      (∀ v, R0 (v + β • integralOperatorOnMeanZero h hh hSym hCan v) = v) ∧
      let C : Matrix (Fin k) (Fin k) ℝ := fun a b =>
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ +
          periodicDynamicTimeCovariance β ρ k t f a b
      let P := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) C
      C.PosSemidef ∧ IsProbabilityMeasure P ∧ HasGaussianLaw id P ∧
      (∀ a : Fin k, (∫ z, z a ∂P) = 0) ∧
      (∀ a b : Fin k, Integrable (fun z => z a * z b) P ∧ (∫ z, z a * z b ∂P) = C a b) ∧
      ∀ (Ω : ℕ → Type v) [∀ N, MeasurableSpace (Ω N)] (ν : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (ν N)] (X : ∀ N, ℝ → Ω N → Fin N → PeriodicTorus ι),
      (∀ N, Measurable (Function.uncurry (X N))) →
      (∀ N, 1 ≤ N → (ν N).map (X N 0) = periodicRieszSingularGibbs s β hs2 (ρ 0) N) →
      ∀ (G B : ℝ → ℝ), (∀ r ∈ Icc 0 T, 0 ≤ G r) → (∀ r ∈ Icc 0 T, B r ≤ Bmax) →
      (∀ N, 1 ≤ N → ∀ r (hr : r ∈ Icc 0 T), haveI := hprob r hr; haveI := hprob 0 ⟨le_rfl, hT⟩;
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ r) M β N ((ν N).map (X N r)) ≤
        (G r : EReal) * periodicRieszTransportExtendedFreeEnergy s hs2 (ρ 0) M β N
          (periodicRieszSingularGibbs s β hs2 (ρ 0) N) + (B r / (N : ℝ) : ℝ)) →
      ∀ (m : ∀ N, Fin k → ℝ → Ω N → ℝ),
      (∀ N, 1 ≤ N → ∀ a, Measurable (Function.uncurry (m N a))) →
      (∀ N, 1 ≤ N → ∀ a ω, m N a 0 ω = 0) →
      (∀ N, 1 ≤ N → ∀ a, ∀ᵐ ω ∂ν N,
        (∫ z, f a (t a) z ∂sourceRieszLocalEmpiricalLaw N (X N (t a) ω)) -
          (∫ z, f a 0 z ∂sourceRieszLocalEmpiricalLaw N (X N 0 ω)) =
          (∫ r in Ioc 0 (t a), periodicEmpiricalTestDrift (periodicRieszForceData s hs hs2).F β (f a) N r
            (X N r ω)) + m N a (t a) ω) →
      (∀ a, (∫ z, f a (t a) z ∂periodicCappedDensityMeasure (ρ (t a))) -
        (∫ z, f a 0 z ∂periodicCappedDensityMeasure (ρ 0)) =
        ∫ r in Ioc 0 (t a), periodicMeanTestDrift (periodicRieszForceData s hs hs2).F β (ρ r) (f a) r) →
      (∀ (θ : Fin k → ℝ) (N : ℕ), 1 ≤ N →
        let A₀ := fun ω => ∑ a, θ a * (Real.sqrt N *
          dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X N 0 ω))
        let W := fun r ω => ∑ a, θ a * (Real.sqrt N * m N a (min r (t a)) ω)
        let S := fun r z => ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
        let Φ := fun r ω => sourceRieszFinitePhase (A₀ ω + W r ω)
        let chi := fun r => ∫ ω, Φ r ω ∂ν N
        ∀ r ∈ Icc 0 T, chi r = chi 0 - (1 / β : ℝ) •
          (∫ u in 0..r, ∫ ω, Φ u ω * ((∫ z, S u z ∂sourceRieszLocalEmpiricalLaw N (X N u ω) : ℝ) : ℂ)
            ∂ν N)) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
          Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N
            (X N (t a) ω)))
        atTop id ν P := by
  intro μ h hh
  haveI := hprob 0 ⟨le_rfl, hT⟩
  have hφm (a : Fin k) : Measurable (f a 0) :=
    measurable_of_contDiff_lift ((hf a 0 ⟨le_rfl, (ht a).1⟩).of_le (by norm_num))
  have hφ (a : Fin k) : MemLp (f a 0) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall fun z => abs_le.mp (hL a 0 ⟨le_rfl, (ht a).1⟩ z))
      (hφm a).aestronglyMeasurable 2
  obtain ⟨hSym, hCan, R0, hR1, hR2, hinit, hcovw⟩ := periodicRiesz_static_initial k s β hs hβ.le hs2
    (ρ 0) M hM (hρ 0 ⟨le_rfl, hT⟩)
  refine ⟨hφ, hSym, hCan, R0, hR1, hR2, ?_⟩
  let C : Matrix (Fin k) (Fin k) ℝ := fun a b =>
    ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ +
      periodicDynamicTimeCovariance β ρ k t f a b
  obtain ⟨P0, Z0, hP0, hGauss0, hZ0, hMean0, hCov0⟩ := hcovw (fun a => (hφ a).toLp (f a 0))
  have hC : C.PosSemidef := by
    haveI := hP0
    have hp : Matrix.PosSemidef (fun a b => (∫ ω, Z0 ω a * Z0 ω b ∂P0) +
        periodicDynamicTimeCovariance β ρ k t f a b) :=
      (sourceDynamic_initial_secondMoment_posSemidef P0 k Z0 hZ0).add
      (periodic_time_covariance_posSemidef T β hβ.le ρ hρm hprob k t (fun a => (ht a).2) f Gmax
        hgrad hfB)
    simpa only [C, fun a b => (hCov0 a b).2] using hp
  obtain ⟨hP, hG, hMean, hCov, hchar⟩ := sourceDynamic_gaussian_target k C hC
  refine ⟨hC, hP, hG, hMean, hCov, ?_⟩
  intro Ω _ ν _ X hXm hLaw G B hGctrl hB hE m hmm hm0 hIto hweak hphase
  let V := fun (N : ℕ) (ω : Ω N) => WithLp.toLp 2 (fun a : Fin k =>
    Real.sqrt N * dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N
      (X N (t a) ω))
  have hV (N : ℕ) : Measurable (V N) := by
    apply (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp
    apply Measurable.of_eval
    intro a
    exact ((measurable_dynEmpiricalDifference_all (periodicCappedDensityMeasure (ρ (t a))) _
      (measurable_of_contDiff_lift ((hf a (t a) ⟨(ht a).1, le_rfl⟩).of_le (by norm_num))) N).const_mul _).comp
        ((hXm N).comp (measurable_const.prodMk measurable_id))
  apply sourceDynamic_scalar_characteristic_clt ν k V (fun N => (hV N).aemeasurable) C hC
  intro θ
  obtain ⟨Dc, Dl, hDc, hDl, hcompare⟩ := exists_periodicRiesz_finite_terminal_CF_comparison (ι := ι) s β M
    Bmax Cpart C₂ hs hβ hs2 hM hBmax K Gmax
  let Cc := T * Dc * (∑ a, |θ a|) / 2 +
    Real.exp ((((Gmax : ℝ) * (∑ a, |θ a|)) ^ 2 / β) * T) * T * Dl * (∑ a, |θ a|) ^ 2
  let A := fun (N : ℕ) (ω : Ω N) => ∑ a, θ a * (Real.sqrt N *
    dynEmpiricalDifference (periodicCappedDensityMeasure (ρ 0)) (f a 0) N (X N 0 ω))
  let Z := fun (N : ℕ) (ω : Ω N) => ∑ a, θ a * (Real.sqrt N *
    dynEmpiricalDifference (periodicCappedDensityMeasure (ρ (t a))) (f a (t a)) N (X N (t a) ω))
  let Vq := (1 / β) * (∫ r in 0..T, ∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
    ∂periodicCappedDensityMeasure (ρ r))
  have hI := hinit (fun a => f a 0) hφm hφ Ω ν (fun N => X N 0)
    (fun N => (hXm N).comp (measurable_const.prodMk measurable_id)) hLaw θ
  have hh := sourceRiesz_sqrt_rate_CF_limit
    (fun N => ∫ ω, sourceRieszFinitePhase (Z N ω) ∂ν N)
    (fun N => ∫ ω, sourceRieszFinitePhase (A N ω) ∂ν N)
    (Complex.exp (-(∑ a, ∑ b, θ a * θ b *
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ) / 2))
    (Real.exp (-Vq) : ℂ) Cc hI (fun N hN => by
      have hc := hcompare T hT k t θ ht N hN (Ω N) (ν N) ρ hρm hprob hρ hCp hC₂ f hf hK hgrad hfB
        L hL hback (X N) (hXm N) G B hGctrl hB (hE N hN) (m N) (hmm N hN)
        (hm0 N hN) (hIto N hN) hweak (hphase θ N hN)
      calc
        _ ≤ T * Dc * (∑ a, |θ a|) / (2 * Real.sqrt N) +
            Real.exp ((((Gmax : ℝ) * (∑ a, |θ a|)) ^ 2 / β) * T) *
              (T * Dl * (∑ a, |θ a|) ^ 2 / Real.sqrt N) := by
                simpa only [Vq, Z, A, neg_mul] using hc
        _ = Cc / Real.sqrt N := by dsimp only [Cc]; ring)
  have hquad := periodic_time_covariance_quadratic T β ρ hρm hprob k t θ (fun a => (ht a).2) f Gmax
    hgrad hfB
  have hsum : (∑ a, ∑ b, θ a * θ b * C a b) =
      (∑ a, ∑ b, θ a * θ b *
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫) +
      (2 / β) * (∫ r in Ioc 0 T, ∫ z,
        ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2 ∂periodicCappedDensityMeasure (ρ r)) := by
    dsimp only [C]
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hquad]
  have he : Complex.exp (-(∑ a, ∑ b, θ a * θ b *
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ) / 2) *
      (Real.exp (-Vq) : ℂ) =
    Complex.exp (-(∑ a, ∑ b, θ a * θ b *
      ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ) / 2 - (Vq : ℝ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_neg]
    rfl
  rw [he] at hh
  have hexp : Complex.exp (-(∑ a, ∑ b, θ a * θ b * C a b : ℝ) / 2) =
      Complex.exp (-(∑ a, ∑ b, θ a * θ b *
        ⟪sourceCenteredL2 ((hφ a).toLp (f a 0)), R0 (sourceCenteredL2 ((hφ b).toLp (f b 0)))⟫ : ℝ) / 2 -
        ((1 / β) * (∫ r in 0..T, ∫ z, ‖∑ a, θ a • periodicStoppedGrad (t a) (f a) r z‖ ^ 2
          ∂periodicCappedDensityMeasure (ρ r)) : ℝ)) := by
    congr 1
    rw [hsum, intervalIntegral.integral_of_le hT]
    push_cast
    ring
  rw [hexp]
  simpa only [V, WithLp.ofLp_toLp, sourceRieszFinitePhase, mul_comm] using hh

end DGRHS.Periodic
