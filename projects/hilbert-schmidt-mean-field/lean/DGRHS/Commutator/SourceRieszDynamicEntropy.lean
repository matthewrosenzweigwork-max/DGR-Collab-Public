import DGRHS.Commutator.SourceRieszCommonFiniteEnergy

/-! Original positive-Riesz dynamicEntropyTransfers(i). Literal initial Gibbs
and actual extended physical free-energy Gronwall imply finite actual Gibbs KL.
The common partition constant is constructed from the physical density envelope;
no desired entropy or normalizer bound is supplied. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma sourceRieszDynamic_initial_Gibbs_objective (s β M : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (N : ℕ) (hN : 1≤N) :
    sourceRieszTransportExtendedFreeEnergy ρ s M β N (sourceRieszSingularGibbs s β ρ N)=
      (-Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ))/(β*(N:ℝ)):ℝ) := by
  letI := sourceRieszSingularGibbs_probability s β hs hβ.le (by linarith) ρ M hM hρ N
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN]
  simp [div_eq_mul_inv]

theorem sourceRieszDynamic_entropy_from_gronwall (s β M : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M)
    (ρ₀ ρ : E→ℝ) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ₀ : ∀ᵐ x ∂volume,ρ₀ x≤M) (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (N : ℕ) (hN : 1≤N) (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν]
    (A B : ℝ)
    (hE : sourceRieszTransportExtendedFreeEnergy ρ s M β N ν≤
      (A:EReal)*sourceRieszTransportExtendedFreeEnergy ρ₀ s M β N (sourceRieszSingularGibbs s β ρ₀ N)+
        (B/(N:ℝ):ℝ)) :
    klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ ∧
    (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤
      -A*Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ₀ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ₀))+β*B+
        Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
          ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by
  rw [sourceRieszDynamic_initial_Gibbs_objective s β M hs hβ hd hM ρ₀ hρ₀ N hN,
    ←EReal.coe_mul,←EReal.coe_add] at hE
  have hbr : 0<β*(N:ℝ) := mul_pos hβ (by exact_mod_cast (by omega : 0<N))
  have hKL : klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ := by
    intro ht
    rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
      ht,EReal.coe_ennreal_top,EReal.top_sub_coe,EReal.top_mul_coe_of_pos (inv_pos.mpr hbr)] at hE
    exact EReal.coe_ne_top _ (top_le_iff.mp hE)
  rw [sourceRieszTransportExtendedFreeEnergy_rewrite s M hs hd hM β hβ ρ hρ N hN ν,
    ←EReal.coe_ennreal_toReal hKL,←EReal.coe_sub,←EReal.coe_mul,EReal.coe_le_coe_iff] at hE
  have hn : 0<(N:ℝ) := by exact_mod_cast (by omega : 0<N)
  have hh := mul_le_mul_of_nonneg_right hE hbr.le
  have hl : (((klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal-
      Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)))*(β*(N:ℝ))⁻¹)*(β*(N:ℝ))=
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal-
      Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by field_simp [hbr.ne']
  have hr : (A*(-Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ₀ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ₀))/(β*(N:ℝ)))+B/(N:ℝ))*(β*(N:ℝ))=
      -A*Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ₀ s β N ω)
        ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ₀))+β*B := by
    field_simp [hβ.ne',hn.ne'] <;> ring
  rw [hl,hr] at hh
  exact ⟨hKL,by linarith⟩

/-- The positive Riesz lower normalizer >=1 eliminates any dependence on Amax;
A is required only nonnegative, with genuine physical Gronwall as premise. -/
theorem sourceRieszDynamic_common_entropy (s β M Bmax : ℝ) (hs : 0<s)
    (hβ : 0<β) (hd : 2*s<(Fintype.card ι:ℝ)) (hM : 0≤M) (hBmax : 0≤Bmax) :
    ∃ H : ℝ,0≤H ∧ ∀ N : ℕ,1≤N → ∀ (ρ₀ ρ : E→ℝ),
      ∀ [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ₀)]
        [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)],
      (∀ᵐ x ∂volume,ρ₀ x≤M) → (∀ᵐ x ∂volume,ρ x≤M) →
      ∀ (ν : Measure (Fin N→E)) [IsProbabilityMeasure ν],∀ A B : ℝ,0≤A → B≤Bmax →
      sourceRieszTransportExtendedFreeEnergy ρ s M β N ν≤
        (A:EReal)*sourceRieszTransportExtendedFreeEnergy ρ₀ s M β N (sourceRieszSingularGibbs s β ρ₀ N)+
          (B/(N:ℝ):ℝ) →
      klDiv ν (sourceRieszSingularGibbs s β ρ N)≠∞ ∧
      (klDiv ν (sourceRieszSingularGibbs s β ρ N)).toReal≤H := by
  obtain ⟨C,hC,hpart⟩ := sourceRieszCommon_particle_moment (ι:=ι) s β M hs hβ.le hM hd
  refine ⟨β*Bmax+|Real.log C|,add_nonneg (mul_nonneg hβ.le hBmax) (abs_nonneg _),?_⟩
  intro N hN ρ₀ ρ hμ₀ hμ hρ₀ hρ ν hν A B hA hB hE
  obtain ⟨hKL,hb⟩ := sourceRieszDynamic_entropy_from_gronwall s β M hs hβ hd hM ρ₀ ρ hρ₀ hρ N hN ν A B hE
  have hlower := (hpart ρ₀ hμ₀ hρ₀ N hN).2.1
  have hlog₀ : 0≤Real.log (∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ₀ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ₀)) := Real.log_nonneg hlower
  have hpc := hpart ρ hμ hρ N hN
  have hp : 0<(∫ ω,Real.exp (sourceRieszLocalParticleExponent ρ s β N ω)
      ∂Measure.pi (fun _ : Fin N=>gaussianRieszDensityMeasure ρ)) := by linarith [hpc.2.1]
  have hlog := Real.log_le_log hp hpc.2.2
  have hB' := mul_le_mul_of_nonneg_left hB hβ.le
  exact ⟨hKL,by nlinarith [mul_nonneg hA hlog₀,le_abs_self (Real.log C)]⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszDynamic_initial_Gibbs_objective
#print axioms DGRHS.Commutator.sourceRieszDynamic_initial_Gibbs_objective
#check @DGRHS.Commutator.sourceRieszDynamic_entropy_from_gronwall
#print axioms DGRHS.Commutator.sourceRieszDynamic_entropy_from_gronwall
#check @DGRHS.Commutator.sourceRieszDynamic_common_entropy
#print axioms DGRHS.Commutator.sourceRieszDynamic_common_entropy
