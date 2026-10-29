import DGRHS.Gaussian.SharpnessCriticalQuantitative
import DGRHS.Gaussian.SharpnessSupercriticalQuantitative
import DGRHS.CLT.SourceRieszRawWeight

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical Topology
namespace DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι]

/-- Unchanged source singular-weight definition, with its actual AE collision
bridge valid throughout 0<s<d. The old root theorem's HS-subcritical binder is
not used; positive dimension is proved directly from the genuine range. -/
lemma sharpness_riesz_singular_weight_ae (s β : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι:ℝ)-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
    DGRHS.CLT.sourceRieszSingularWeight s β ρ N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x))) := by
  have hd : 0 < Fintype.card ι := by exact_mod_cast (show (0:ℝ) < Fintype.card ι by linarith)
  let : Nonempty ι := Fintype.card_pos_iff.mp hd
  filter_upwards [DGRHS.CLT.density_iid_collision_free ρ N] with x hx
  by_cases hb : β = 0
  · simp [DGRHS.CLT.sourceRieszSingularWeight,hb]
  · simp only [DGRHS.CLT.sourceRieszSingularWeight,ite_eq_right hb,ite_eq_left hx]

/-- Genuine finite literal singular partition equals the proper real source
integral even at and above the HS threshold. -/
lemma sharpness_riesz_literal_partition_eq (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι:ℝ)-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
    DGRHS.CLT.sourceRieszSingularPartition s β ρ N = ENNReal.ofReal
      (∫ x,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ (gaussianRieszPhysicalPair s)) (DGRHS.potential μ W)
        (DGRHS.interactionEnergy μ W) N x) ∂Measure.pi (fun _ => μ)) := by
  have hi := (sharpness_riesz_source_partition_lower s hs ha ρ M hM hρ β hβ N hN).1
  unfold DGRHS.CLT.sourceRieszSingularPartition
  rw [lintegral_congr_ae (sharpness_riesz_singular_weight_ae s β hs ha ρ N)]
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => (Real.exp_pos _).le))).symm

/-- Source quantitativeDyadicCompression -> partition-function-sharpness,
including the exact critical logarithmic-power and supercritical exponent
2-d/s, with proper literal singular partitions and original range. -/
theorem sharpness_riesz_literal_partition_rate (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι:ℝ)-s) (hsharp : (Fintype.card ι:ℝ) ≤ 2*s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (hρm : Measurable ρ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) :
    (∀ N : ℕ,1 ≤ N → 0 < DGRHS.CLT.sourceRieszSingularPartition s β ρ N ∧
      DGRHS.CLT.sourceRieszSingularPartition s β ρ N < ⊤) ∧
    Tendsto (fun N : ℕ => (DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal) atTop atTop ∧
    ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧ ∃ N0 : ℕ,3 ≤ N0 ∧ ∀ N : ℕ,N0 ≤ N →
      C⁻¹*(if 2*s = (Fintype.card ι:ℝ) then (Real.log (N:ℝ))^c
        else Real.exp (c*(Real.log (N:ℝ))^(2-(Fintype.card ι:ℝ)/s))) ≤
        (DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun x y : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (x,y)
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let Z := fun N : ℕ => ∫ x,Real.exp (-β*(N:ℝ)*DGRHS.CLT.sourceCanonicalModulatedEnergy
    H (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x) ∂Measure.pi (fun _ => μ)
  have he (N : ℕ) (hN : 1 ≤ N) :
      DGRHS.CLT.sourceRieszSingularPartition s β ρ N = ENNReal.ofReal (Z N) :=
    sharpness_riesz_literal_partition_eq s β hs hβ.le ha ρ M hM hρ N hN
  have hz (N : ℕ) (hN : 1 ≤ N) : 0 < Z N :=
    integral_exp_pos (sharpness_riesz_source_partition_lower s hs ha ρ M hM hρ β hβ.le N hN).1
  have heR (N : ℕ) (hN : 1 ≤ N) : (DGRHS.CLT.sourceRieszSingularPartition s β ρ N).toReal = Z N := by
    rw [he N hN,ENNReal.toReal_ofReal (hz N hN).le]
  have ht := (sharpness_riesz_source_partition_diverges s hs ha hsharp ρ hρm M hM hρ β hβ).2
  refine ⟨fun N hN => ?_,?_,?_⟩
  · rw [he N hN]
    exact ⟨ENNReal.ofReal_pos.mpr (hz N hN),ENNReal.ofReal_lt_top⟩
  · apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (heR N hN).symm
  · have hRate : ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
        C*(if 2*s = (Fintype.card ι:ℝ) then (Real.log (N:ℝ))^c
          else Real.exp (c*(Real.log (N:ℝ))^(2-(Fintype.card ι:ℝ)/s))) ≤ Z N := by
      by_cases hc : 2*s = (Fintype.card ι:ℝ)
      · simpa only [hc,ite_true] using sharpness_critical_source_partition_rate s hs hc ρ hρm M hM hρ β hβ
      · have hsup : (Fintype.card ι:ℝ) < 2*s := lt_of_le_of_ne hsharp (Ne.symm hc)
        simpa only [hc,ite_false] using sharpness_supercritical_source_partition_rate s hs ha hsup ρ hρm M hM hρ β hβ
    obtain ⟨c,hc,C,hC,hRateC⟩ := hRate
    obtain ⟨N0,hN0⟩ := eventually_atTop.mp hRateC
    refine ⟨c,hc,C⁻¹,by positivity,max 3 N0,le_max_left _ _,?_⟩
    intro N hN
    have hn : 1 ≤ N := (by omega : 1 ≤ max 3 N0).trans hN
    rw [inv_inv,heR N hn]
    exact hN0 N ((le_max_right 3 N0).trans hN)

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_riesz_literal_partition_rate
#check @DGRHS.Gaussian.sharpness_riesz_literal_partition_rate
