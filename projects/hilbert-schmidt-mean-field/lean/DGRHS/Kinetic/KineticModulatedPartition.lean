import DGRHS.Kinetic.SpatialTensorization
import DGRHS.Kinetic.ParticleMaxwellian
import DGRHS.CLT.SourceRieszUniform
import DGRHS.CLT.SourceLogUniform
import DGRHS.CLT.SourceEnergyTilt
import DGRHS.CLT.SourceLogSingularIdentification
import DGRHS.CLT.SourceRieszSingularGibbs
import DGRHS.Gaussian.SourceRepulsiveRieszRate
import DGRHS.Gaussian.SourceRepulsiveLogRate

/-! Packet P14b, kinetic half of Remark 2.1 (`rem:torus-kinetic-variants`, TeX 495):
"If the starting Hamiltonian `H_N` is augmented by the standard quadratic kinetic
energy, then the velocity variables tensorize as an independent Maxwellian factor.
Consequently, the spatial modulated partition-function ... estimates carry over
verbatim for spatial observables."

The kinetic modulated partition function is the expectation of `exp(-β N F_N(x))`
(a spatial observable) under the kinetic reference `μ^{⊗N} ⊗ η`, where `η` is any
probability measure on any velocity space (the normalized `N d`-dimensional Maxwellian
is the instance `η = maxwellian (Fin N × ι) β`).  Theorem 2.2 (`thm:partitionFunctionBound`)
(i) and (ii) are restated for it, with constants independent of `η`, and are derived from
the existing spatial exports through the tensorization identity
`DGRHS.Kinetic.spatial_partition_tensor`. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
universe w u
namespace DGRHS.Kinetic
open DGRHS.Gaussian DGRHS.CLT DGRHS.Concentration

section generic
variable {X : Type*} {V : Type w} [MeasurableSpace X] [MeasurableSpace V]

/-- The kinetic modulated partition function `E_{P ⊗ η}[exp(-β N F_N(x))]` (a spatial
observable `F_N` of the phase-space point `(x, v)`), `P = μ^{⊗N}`, `η` a velocity reference. -/
def kineticModulatedPartition (P : Measure X) (η : Measure V) (FN : X → ℝ)
    (β N : ℝ) : ℝ :=
  ∫ z, Real.exp (-β*N*FN z.1) ∂P.prod η

/-- The Maxwellian (any normalized velocity factor) normalizes: the kinetic modulated
partition function equals the spatial one. -/
theorem kineticModulatedPartition_eq (P : Measure X) (η : Measure V)
    [IsProbabilityMeasure P] [IsProbabilityMeasure η] (FN : X → ℝ) (β N : ℝ) :
    kineticModulatedPartition P η FN β N = ∫ x, Real.exp (-β*N*FN x) ∂P :=
  spatial_partition_tensor P η (fun x => -β*N*FN x)

theorem kineticModulatedPartition_integrable (P : Measure X) (η : Measure V)
    [IsProbabilityMeasure P] [IsProbabilityMeasure η] (FN : X → ℝ) (β N : ℝ)
    (h : Integrable (fun x => Real.exp (-β*N*FN x)) P) :
    Integrable (fun z : X × V => Real.exp (-β*N*FN z.1)) (P.prod η) :=
  h.comp_fst η

end generic

section pi
variable {ι : Type u} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Theorem 2.2(i), Riesz branch `0 < s < d/2`, kinetic modulated partition function:
`sup_N K^kin_{N,β}(μ) ≤ C_ub`, with `C_ub` independent of the velocity reference. -/
theorem kinetic_sourceRieszPartition_uniform
    (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : E) => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      ∀ (V : Type w) [MeasurableSpace V] (η : Measure V) [IsProbabilityMeasure η],
      Integrable (fun z : (Fin N → E) × V =>
        Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N z.1))
          ((Measure.pi (fun _ : Fin N => μ)).prod η) ∧
      kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) η
        (sourceCanonicalModulatedEnergy h F I N) β (N : ℝ) ≤ C := by
  dsimp only
  obtain ⟨C, hC, hU⟩ := sourceRieszPartition_uniform s β hs hβ ha ρ M hM hρ
  refine ⟨C, hC, fun N hN V _ η _ => ?_⟩
  obtain ⟨hi, hb⟩ := hU N hN
  refine ⟨kineticModulatedPartition_integrable _ η _ _ _ hi, ?_⟩
  rw [kineticModulatedPartition_eq]
  exact hb

/-- Theorem 2.2(i), logarithmic branch `s = 0`, kinetic modulated partition function. -/
theorem kinetic_sourceLogPartition_uniform (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : E → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b : E => logPhysicalPair (a,b)
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      ∀ (V : Type w) [MeasurableSpace V] (η : Measure V) [IsProbabilityMeasure η],
      Integrable (fun z : (Fin N → E) × V => Real.exp
        (-β*(N : ℝ)*sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N z.1))
        ((Measure.pi (fun _ : Fin N => μ)).prod η) ∧
      kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) η
        (sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
          (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N) β (N : ℝ) ≤ C := by
  dsimp only
  obtain ⟨C, hC, hU⟩ := sourceLogPartition_uniform β hβ hd ρ M hM hρ hpair
  refine ⟨C, hC, fun N hN V _ η _ => ?_⟩
  obtain ⟨hi, hb⟩ := hU N hN
  refine ⟨kineticModulatedPartition_integrable _ η _ _ _ hi, ?_⟩
  rw [kineticModulatedPartition_eq]
  exact hb

/-- Theorem 2.2(ii), Riesz branch `0 < s < d/2`: the regularized-determinant limit and the
`(log (e+N))^{-(d-2s)/(2s)}` rate for the kinetic modulated partition function, along any
sequence of velocity references `η_N` (e.g. the `N`-particle Maxwellians), with the same
constants and spectral data as the spatial statement. -/
theorem kinetic_source_riesz_partition_rate
    (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : E => gaussianRieszPhysicalPair s (x,y)
    let h := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
    let I := DGRHS.interactionEnergy μ W
    ∃ (hh : MemLp h 2 (μ.prod μ))
      (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i) ∧
      HasProd (fun i => (1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β*eig i)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : ℕ → Type w) [∀ N, MeasurableSpace (V N)] (η : ∀ N, Measure (V N))
        [∀ N, IsProbabilityMeasure (η N)],
      Tendsto (fun N : ℕ => kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
          (sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N) β (N : ℝ)) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹)) ∧
      Tendsto (fun N : ℕ => Real.log (kineticModulatedPartition
          (Measure.pi (fun _ : Fin N => μ)) (η N)
          (sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N) β (N : ℝ))) atTop
        (𝓝 (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))) ∧
      ∀ N, 1 ≤ N →
        Integrable (fun z : (Fin N → E) × V N => Real.exp
          (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N z.1))
          ((Measure.pi (fun _ : Fin N => μ)).prod (η N)) ∧
        Real.exp (β*I) ≤ kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
          (sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N) β (N : ℝ) ∧
        |kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
            (sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N) β (N : ℝ) -
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹| ≤
          C*(Real.log (Real.exp 1+(N : ℝ)))^(-(((Fintype.card ι : ℝ)-2*s)/(2*s))) ∧
        |Real.log (kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
            (sourceCanonicalModulatedEnergy h (DGRHS.potential μ W) I N) β (N : ℝ)) -
          (β*I+Real.log ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i ↦ β*eig i)))⁻¹))| ≤
          C*(Real.log (Real.exp 1+(N : ℝ)))^(-(((Fintype.card ι : ℝ)-2*s)/(2*s))) := by
  dsimp only
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hP, hT, hLog, C, hC, hRate⟩ :=
    SourceRepulsiveRieszRate.exists_source_partition_rate s β hs hβ ha ρ M hM hρ
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hP, C, hC, ?_⟩
  intro V _ η _
  have hK : ∀ N : ℕ, kineticModulatedPartition (Measure.pi (fun _ : Fin N =>
      gaussianRieszDensityMeasure ρ)) (η N)
      (sourceCanonicalModulatedEnergy (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianRieszPhysicalPair s))
        (DGRHS.potential (gaussianRieszDensityMeasure ρ)
          (fun x y : E => gaussianRieszPhysicalPair s (x,y)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
          (fun x y : E => gaussianRieszPhysicalPair s (x,y))) N) β (N : ℝ) =
      physicalRieszSourcePartition s β ρ N := fun N =>
    kineticModulatedPartition_eq _ _ _ _ _
  refine ⟨hT.congr fun N => (hK N).symm, hLog.congr fun N => by rw [hK N], ?_⟩
  intro N hN
  obtain ⟨hi, hlow, hr1, hr2⟩ := hRate N hN
  refine ⟨kineticModulatedPartition_integrable _ (η N) _ _ _ hi, ?_, ?_, ?_⟩
  · rw [hK N]; exact hlow
  · rw [hK N]; exact hr1
  · rw [hK N]; exact hr2

/-- Theorem 2.2(ii), logarithmic branch `s = 0`: the regularized-determinant limit and the
power rate for the kinetic modulated partition function. -/
theorem kinetic_source_log_partition_rate (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : E → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-4*β*logPhysicalPotential
      (gaussianRieszDensityMeasure ρ) x)) (gaussianRieszDensityMeasure ρ)) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun (x y : E) => logPhysicalPair (x,y)
    let h := hoeffdingCentered μ logPhysicalPair
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    let hh := memLp_logPhysicalCenteredPair_source hd ρ M hM hρ hpair
    ∃ (hs : ∀ᵐ p ∂μ.prod μ, h p.swap = h p) (hc : ∀ᵐ x ∂μ, (∫ y, h (x,y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hs hc (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β*eig i) ∧
      HasProd (fun i => (1+β*eig i)*Real.exp (-(β*eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β*eig i)) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1/2 ∧ 0 ≤ C ∧
      ∀ (V : ℕ → Type w) [∀ N, MeasurableSpace (V N)] (η : ∀ N, Measure (V N))
        [∀ N, IsProbabilityMeasure (η N)],
      Tendsto (fun N : ℕ => kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
          (sourceCanonicalModulatedEnergy h F I N) β (N : ℝ)) atTop
        (𝓝 (Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹)) ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun z : (Fin N → E) × V N => Real.exp
          (-β*(N : ℝ)*sourceCanonicalModulatedEnergy h F I N z.1))
          ((Measure.pi (fun _ : Fin N => μ)).prod (η N)) ∧
        |kineticModulatedPartition (Measure.pi (fun _ : Fin N => μ)) (η N)
            (sourceCanonicalModulatedEnergy h F I N) β (N : ℝ) -
          Real.exp (β*I)*(Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹| ≤
          C*(Real.exp 1+(N : ℝ))^(-c) := by
  dsimp only
  obtain ⟨hs, hc, κ, eig, e, hκ, he, hD, hProd, hT, c, C, hc0, hc1, hC, hRate⟩ :=
    SourceRepulsiveLogRate.exists_source_partition_rate β hβ hd ρ M hM hρ hpair htail
  refine ⟨hs, hc, κ, eig, e, hκ, he, hD, hProd, c, C, hc0, hc1, hC, ?_⟩
  intro V _ η _
  have hK : ∀ N : ℕ, kineticModulatedPartition (Measure.pi (fun _ : Fin N =>
      gaussianRieszDensityMeasure ρ)) (η N)
      (sourceCanonicalModulatedEnergy (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ)
          (fun x y : E => logPhysicalPair (x,y)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
          (fun x y : E => logPhysicalPair (x,y))) N) β (N : ℝ) =
      ∫ x : Fin N → E, Real.exp (-β*(N : ℝ)*sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ)
          (fun x y : E => logPhysicalPair (x,y)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
          (fun x y : E => logPhysicalPair (x,y))) N x)
        ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ) := fun N =>
    kineticModulatedPartition_eq _ _ _ _ _
  refine ⟨hT.congr fun N => (hK N).symm, ?_⟩
  intro N hN
  obtain ⟨hi, hr⟩ := hRate N hN
  refine ⟨kineticModulatedPartition_integrable _ (η N) _ _ _ hi, ?_⟩
  rw [hK N]; exact hr

end pi

section maxwellian
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

/-- With the `N`-particle Maxwellian at inverse temperature `βv > 0` as velocity reference
the kinetic modulated partition function is the spatial one. -/
theorem kineticModulatedPartition_maxwellian (P : Measure X) [IsProbabilityMeasure P]
    (FN : X → ℝ) (β N : ℝ) (βv : ℝ) (hβv : 0 < βv) (n : ℕ) :
    kineticModulatedPartition P (maxwellian (Fin n × ι) βv) FN β N =
      ∫ x, Real.exp (-β*N*FN x) ∂P := by
  haveI := particle_maxwellian_probability (ι := ι) βv hβv n
  exact kineticModulatedPartition_eq P _ FN β N

/-- The literal kinetic Hamiltonian `N F_N + Σ|v_i|²/2` (Lebesgue velocity measure) has
partition function `K_{N,β}(μ) (2π/β)^{Nd/2}`; dividing by the Gaussian normalization
recovers the modulated partition function, i.e. the Maxwellian factor normalizes. -/
theorem kineticModulatedPartition_full_hamiltonian (P : Measure X) [SFinite P]
    (FN : X → ℝ) (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    (∫ z : X × ((Fin n × ι) → ℝ),
      Real.exp (-β * ((n : ℝ) * FN z.1 + particleKineticEnergy n z.2)) ∂P.prod volume) /
        (Real.sqrt (2*Real.pi/β))^(n * Fintype.card ι) =
      ∫ x, Real.exp (-β * ((n : ℝ) * FN x)) ∂P := by
  rw [particle_kinetic_full_partition P (fun x => (n : ℝ) * FN x) β hβ n]
  have : (Real.sqrt (2*Real.pi/β))^(n * Fintype.card ι) ≠ 0 := by
    have : 0 < Real.sqrt (2*Real.pi/β) := Real.sqrt_pos.mpr (by positivity)
    positivity
  field_simp

end maxwellian

end DGRHS.Kinetic
#check @DGRHS.Kinetic.kineticModulatedPartition_eq
#print axioms DGRHS.Kinetic.kineticModulatedPartition_eq
#check @DGRHS.Kinetic.kinetic_sourceRieszPartition_uniform
#print axioms DGRHS.Kinetic.kinetic_sourceRieszPartition_uniform
#check @DGRHS.Kinetic.kinetic_sourceLogPartition_uniform
#print axioms DGRHS.Kinetic.kinetic_sourceLogPartition_uniform
#check @DGRHS.Kinetic.kinetic_source_riesz_partition_rate
#print axioms DGRHS.Kinetic.kinetic_source_riesz_partition_rate
#check @DGRHS.Kinetic.kinetic_source_log_partition_rate
#print axioms DGRHS.Kinetic.kinetic_source_log_partition_rate
#print axioms DGRHS.Kinetic.kineticModulatedPartition_maxwellian
#print axioms DGRHS.Kinetic.kineticModulatedPartition_full_hamiltonian
