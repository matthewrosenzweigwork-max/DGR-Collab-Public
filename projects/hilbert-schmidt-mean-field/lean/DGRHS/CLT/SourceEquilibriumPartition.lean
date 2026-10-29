/- Exact source canonical versus literal singular modulated partition factor.
No integrability, collision-nullness or desired normalizer identity is an input
of either physical endpoint; all are derived from original physical data and EL. -/
import DGRHS.CLT.EquilibriumPartition
import DGRHS.CLT.SourceEquilibriumPhysical
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]
lemma canonicalSingularPartition_eq_ofReal {S : Type*} [MeasurableSpace S]
    (ν₀ : Measure S) (W : S → S → ℝ) (V : S → ℝ) (β : ℝ) (N : ℕ)
    (hi : Integrable (fun x : Fin N → S => Real.exp (-β*sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => ν₀)))
    (hc : ∀ᵐ x : Fin N → S ∂Measure.pi (fun _ : Fin N => ν₀),
      ∀ i j : Fin N,i≠j → x i≠x j) :
    canonicalSingularPartition ν₀ W V β N=ENNReal.ofReal
      (∫ x : Fin N → S,Real.exp (-β*sourceHamiltonian W V N x)
        ∂Measure.pi (fun _ : Fin N => ν₀)) := by
  have he : canonicalSingularWeight W V β N =ᵐ[Measure.pi (fun _ : Fin N => ν₀)]
      (fun x => ENNReal.ofReal (Real.exp (-β*sourceHamiltonian W V N x))) := by
    filter_upwards [hc] with x hx
    simp only [canonicalSingularWeight,if_pos hx]
  unfold canonicalSingularPartition
  rw [lintegral_congr_ae he]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

theorem sourceLog_equilibrium_partition (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod
      (gaussianRieszDensityMeasure ρ)))
    (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -(β : ℝ)*
      (V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => logPhysicalPair (a,b)) x))=
      gaussianRieszDensityMeasure ρ) (N : ℕ) (hN : 1 ≤ N) :
    let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
    (canonicalSingularPartition volume W V (β : ℝ) N).toReal=
      (∫ x,Real.exp (-(β : ℝ)*(V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) W x)) ∂volume)^N *
      Real.exp ((β : ℝ)*(N : ℝ)*DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) W) *
      (sourceLogSingularPartition β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
  have hW : ∀ x y,W x y=W y x := by
    intro x y
    simp only [W,logPhysicalPair,norm_sub_rev]
  have hi := sourceLog_equilibrium_canonical β hβ hd ρ M hM hρ hpair V hEL N hN
  have hm := sourceLogEnergyWeight_integrable (β : ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  have href := equilibrium_product_reference volume μ
    (fun x => -(β : ℝ)*(V x+DGRHS.potential μ W x)) hEL N
  have hdim : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hdim
  have hc := href.1.ae_le (density_iid_collision_free ρ N)
  rw [canonicalSingularPartition_eq_ofReal volume W V (β : ℝ) N hi.1 hc,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le)),
    sourceLogSingularPartition_eq_integral β hd ρ M hM hρ hpair N]
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le))]
  exact equilibrium_partition_factor (μ := μ) W hW V (β : ℝ) N (by omega) hEL hm

theorem sourceRiesz_equilibrium_partition (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β*
      (V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b)) x))=
      gaussianRieszDensityMeasure ρ) (N : ℕ) (hN : 1 ≤ N) :
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    (canonicalSingularPartition volume W V β N).toReal=
      (∫ x,Real.exp (-β*(V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) W x)) ∂volume)^N *
      Real.exp (β*(N : ℝ)*DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ) W) *
      (sourceRieszSingularPartition s β ρ N).toReal := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  have hW : ∀ x y,W x y=W y x := by
    intro x y
    simp only [W,gaussianRieszPhysicalPair,norm_sub_rev]
  have hi := sourceRiesz_equilibrium_canonical s β hs hβ ha ρ M hM hρ V hEL N hN
  have hm := sourceRieszEnergyWeight_integrable s β hs hβ.le ha ρ M hM hρ N
  have href := equilibrium_product_reference volume μ
    (fun x => -β*(V x+DGRHS.potential μ W x)) hEL N
  have hdim : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hdim
  have hc := href.1.ae_le (density_iid_collision_free ρ N)
  rw [canonicalSingularPartition_eq_ofReal volume W V β N hi.1 hc,
    ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le)),
    sourceRieszSingularPartition_eq_integral s β hs hβ.le ha ρ M hM hρ N]
  unfold DGRHS.Concentration.physicalRieszSourcePartition
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le))]
  exact equilibrium_partition_factor (μ := μ) W hW V β N (by omega) hEL hm

end DGRHS.CLT

#check @DGRHS.CLT.canonicalSingularPartition_eq_ofReal
#print axioms DGRHS.CLT.canonicalSingularPartition_eq_ofReal

#check @DGRHS.CLT.sourceLog_equilibrium_partition
#print axioms DGRHS.CLT.sourceLog_equilibrium_partition

#check @DGRHS.CLT.sourceRiesz_equilibrium_partition
#print axioms DGRHS.CLT.sourceRiesz_equilibrium_partition
