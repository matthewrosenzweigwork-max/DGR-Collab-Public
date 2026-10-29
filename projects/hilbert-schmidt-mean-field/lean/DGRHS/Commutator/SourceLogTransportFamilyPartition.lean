import DGRHS.Commutator.SourceLogTransportLocal

noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

/-- The physical finite-IR master constant is chosen BEFORE the density.
All actual master fields and the eventual particle threshold are derived. -/
theorem exists_log_family_finiteIR_cap (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ))
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : EuclideanSpace ℝ ι → ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x ≤ M) → ∀ T : ℝ,1 ≤ T → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β T n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨δ,hδ,hδ1,hrow,hop⟩ := exists_gaussianLogMaster_scale (ι := ι) β M hM hd
  let A := 1+8*gaussianLogShortConstant M ι
  let u₀ := 1+4*gaussianLogSourceLowConstant δ β M ι
  have hc := gaussianLogShortConstant_nonneg (ι := ι) M hM hd
  have hA : 0 < A := by dsimp [A];positivity
  have hAC : 8*gaussianLogShortConstant M ι ≤ A := by dsimp [A];linarith
  have hclow : 0 ≤ gaussianLogSourceLowConstant δ β M ι := by
    have hlog := Real.log_nonpos hδ.le hδ1.le
    have hterm : 0 ≤ -Real.log δ+1/4 := by linarith
    unfold gaussianLogSourceLowConstant
    positivity
  have hu₀ : 1 ≤ u₀ := by dsimp [u₀];linarith
  have hlow : 4*gaussianLogSourceLowConstant δ β M ι ≤ u₀ := by dsimp [u₀];linarith
  let K := (2+gaussianLogAdaptiveSizeConstant A β (Fintype.card ι : ℝ))^2
  obtain ⟨N₀,hN₀⟩ := sublinear_power_envelope_growth (2*glzUniversalTailConstant^2)
    0 K (2/3 : ℝ) (by norm_num)
  let C := masterEnvelopeConstant u₀ N₀ (fun n => 0+K*(n : ℝ)^(2/3 : ℝ))
  refine ⟨max C 1, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _), ?_⟩
  intro ρ hμ hρ
  let μ := gaussianRieszDensityMeasure ρ
  let I := {T : ℝ // 1 ≤ T}
  let X := fun (θ : I) (n : ℕ) => gaussianLogSourceApproxExponent μ β θ.val n
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) : AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_gaussianLogSourceApproxExponent μ β θ.val n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => gaussianLogSourceMasterData δ θ.val β A u₀
    hδ hδ1.le θ.property hβ hd ρ M hM hρ n hn hA hAC hu₀ hlow hrow.le hop.le
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤ 0+K*(n : ℝ)^(2/3 : ℝ) := by
    have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hz := (gaussianLogAdaptive_actual_size_bound δ A β (n : ℝ) u₀ hδ hδ1.le hA hβ hn' hu₀ hd μ).2
    simpa only [data,gaussianLogSourceMasterData,K,zero_add] using hz
  have hbound := master_uniform_exponential_envelope μ X hX u₀ hu₀ N₀ data
    (fun n => 0+K*(n : ℝ)^(2/3 : ℝ)) hsize hN₀
  intro T hT n hn
  have hz := hbound ⟨T,hT⟩ n hn
  exact ⟨hz.1, hz.2.trans (le_max_left _ _)⟩

/-- Genuine singular Fatou passage retains the SAME cap for every density in the class. -/
theorem exists_log_family_physical_cap (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : EuclideanSpace ℝ ι → ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_log_family_finiteIR_cap (ι := ι) β hβ hd M hM
  refine ⟨C,hC,?_⟩
  intro ρ hμ hρ hpair n hn
  let T := fun j : ℕ => ((j+1 : ℕ) : ℝ)
  have hT : Tendsto T atTop atTop := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hT1 (j : ℕ) : 1 ≤ T j := by dsimp [T];exact_mod_cast (Nat.le_add_left 1 j)
  exact exponential_integrable_of_ae_tendsto (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ))
    (fun j => gaussianLogSourceApproxExponent (gaussianRieszDensityMeasure ρ) β (T j) n)
    (logPhysicalMomentExponent (gaussianRieszDensityMeasure ρ) β n)
    (fun j => (hbound ρ hρ (T j) (hT1 j) n hn).1) C
    (fun j => (hbound ρ hρ (T j) (hT1 j) n hn).2)
    (ae_tendsto_gaussianLogSourceApproxExponent T hT hd ρ M hM hρ hpair β n)

/-- A common genuine literal source partition cap, with no origin-tail dependence. -/
theorem exists_log_family_source_cap (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : EuclideanSpace ℝ ι → ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ x ≤ M) →
      Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
        (gaussianRieszDensityMeasure ρ)) → ∀ N : ℕ, 1 ≤ N →
      Integrable (sourceLogTransportNumerator (gaussianRieszDensityMeasure ρ) β 1 (fun _ => 0) 0 N)
        (Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ∧
      (∫ x, sourceLogTransportNumerator (gaussianRieszDensityMeasure ρ) β 1 (fun _ => 0) 0 N x
        ∂Measure.pi (fun _ : Fin N => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_log_family_physical_cap (ι := ι) β hβ hd M hM
  refine ⟨C,hC,?_⟩
  intro ρ hμ hρ hpair N hN
  have he := hbound ρ hρ hpair N hN
  simp_rw [DGRHS.CLT.sourceLogMomentExponent_eq] at he
  have heq (x : Fin N → EuclideanSpace ℝ ι) :
      DGRHS.CLT.sourceParticleExponent
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) β N x =
      -β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x := by
    rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ (by omega : 0 < N)]
    unfold DGRHS.CLT.sourceParticleExponent
    ring
  simp_rw [heq] at he
  have hfun : sourceLogTransportNumerator (gaussianRieszDensityMeasure ρ) β 1 (fun _ => 0) 0 N =
      fun x => Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair)
        (DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)))
        (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b))) N x) := by
    funext x
    simp [sourceLogTransportNumerator]
  rw [hfun]
  exact he

end DGRHS.Commutator
#print axioms DGRHS.Commutator.exists_log_family_finiteIR_cap
#print axioms DGRHS.Commutator.exists_log_family_physical_cap
#print axioms DGRHS.Commutator.exists_log_family_source_cap
#check @DGRHS.Commutator.exists_log_family_source_cap
