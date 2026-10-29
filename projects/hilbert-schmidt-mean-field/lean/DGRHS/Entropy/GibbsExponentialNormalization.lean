/- Exact proper exponential normalization. Reuses the pinned native tilted
integrability equivalence and exponential integral formula, preserving the
actual normalizer before taking any ratio. -/
import DGRHS.Entropy.SourceLogPartitionBounds
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.Entropy

theorem gibbs_exponential_normalization {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (u a : S→ℝ)
    (hZ : Integrable (fun x=>Real.exp (u x)) μ)
    (hnum : Integrable (fun x=>Real.exp (u x+a x)) μ) :
    Integrable (fun x=>Real.exp (a x)) (μ.tilted u) ∧
      (∫ x,Real.exp (a x) ∂μ.tilted u)=
        (∫ x,Real.exp (u x+a x) ∂μ)/(∫ x,Real.exp (u x) ∂μ) := by
  refine ⟨(integrable_tilted_iff hZ _).mpr ?_,?_⟩
  · convert hnum using 1
    funext x
    simp only [smul_eq_mul,Real.exp_add]
  · simpa only [Pi.add_apply] using integral_exp_tilted u a

theorem gibbs_exponential_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (u a : S→ℝ)
    (hZ : Integrable (fun x=>Real.exp (u x)) μ)
    (hnum : Integrable (fun x=>Real.exp (u x+a x)) μ)
    (B k : ℝ) (hk : 0<k) (hLower : k≤∫ x,Real.exp (u x) ∂μ)
    (hB : (∫ x,Real.exp (u x+a x) ∂μ)≤B) :
    Integrable (fun x=>Real.exp (a x)) (μ.tilted u) ∧
      (∫ x,Real.exp (a x) ∂μ.tilted u)≤B/k := by
  obtain ⟨hi,he⟩ := gibbs_exponential_normalization μ u a hZ hnum
  have hBn : 0≤B := (integral_nonneg fun x=>(Real.exp_pos _).le).trans hB
  refine ⟨hi,?_⟩
  rw [he]
  exact (div_le_div_of_nonneg_right hB (integral_exp_pos hZ).le).trans
    (div_le_div_of_nonneg_left hBn hk hLower)

open DGRHS.Gaussian DGRHS.CLT
variable {ι : Type*} [Fintype ι]

theorem sourceLog_gibbs_exponential_bound (β : ℝ≥0)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1≤N) (a : (Fin N→EuclideanSpace ℝ ι)→ℝ) (B : ℝ) :
    let μ := gaussianRieszDensityMeasure ρ
    let P := Measure.pi (fun _ : Fin N=>μ)
    let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
    let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
    Integrable (fun x=>Real.exp (-(β:ℝ)*(N:ℝ)*E x+a x)) P →
    (∫ x,Real.exp (-(β:ℝ)*(N:ℝ)*E x+a x) ∂P)≤B →
      Integrable (fun x=>Real.exp (a x)) (sourceLogSingularGibbs β ρ N) ∧
      (∫ x,Real.exp (a x) ∂sourceLogSingularGibbs β ρ N)≤
        B/Real.exp ((β:ℝ)*DGRHS.interactionEnergy μ W) := by
  dsimp only
  intro hnum hB
  let μ := gaussianRieszDensityMeasure ρ
  let P := Measure.pi (fun _ : Fin N=>μ)
  let W := fun a b : EuclideanSpace ℝ ι=>logPhysicalPair (a,b)
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ logPhysicalPair)
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N
  let u := fun x=>-(β:ℝ)*(N:ℝ)*E x
  have hZ := sourceLogEnergyWeight_integrable (β:ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  have hQ : sourceLogSingularGibbs β ρ N=P.tilted u := by
    rw [sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N,←sourceEnergyTilt_eq _ _ _ (β:ℝ) N]
  obtain ⟨_,_,hBounds⟩ := sourceLogPartition_original_bounds β hd ρ M hM hρ hpair
  have hLower := (hBounds N hN).1
  rw [sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N,
    ENNReal.toReal_ofReal (integral_nonneg fun x=>(Real.exp_pos _).le)] at hLower
  rw [hQ]
  exact gibbs_exponential_bound P u a hZ hnum B _ (Real.exp_pos _) hLower hB

end DGRHS.Entropy
#check @DGRHS.Entropy.gibbs_exponential_normalization
#check @DGRHS.Entropy.gibbs_exponential_bound
#check @DGRHS.Entropy.sourceLog_gibbs_exponential_bound
#print axioms DGRHS.Entropy.gibbs_exponential_normalization
#print axioms DGRHS.Entropy.gibbs_exponential_bound
#print axioms DGRHS.Entropy.sourceLog_gibbs_exponential_bound
