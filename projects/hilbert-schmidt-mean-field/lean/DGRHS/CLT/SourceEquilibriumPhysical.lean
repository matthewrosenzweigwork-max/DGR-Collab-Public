/- Source thermal Euler-Lagrange relation identifies BOTH literal modulated
log/Riesz Gibbs laws with the actual collision-zero canonical ensemble.
Canonical properness, positive finite normalizer and null collisions are
conclusions derived from original physical data and that relation. -/
import DGRHS.CLT.EquilibriumCollisionWeight
import DGRHS.CLT.SourceLogSingularIdentification
import DGRHS.CLT.SourceRieszSingularGibbs
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace DGRHS.CLT
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

theorem sourceLog_equilibrium_canonical (β : ℝ≥0) (hβ : 0 < (β : ℝ))
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
    Integrable (fun x => Real.exp (-(β : ℝ)*sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ ι)))) ∧
      0 < canonicalSingularPartition volume W V (β : ℝ) N ∧
      canonicalSingularPartition volume W V (β : ℝ) N < ∞ ∧
      sourceLogSingularGibbs β ρ N=canonicalSingularLaw volume W V (β : ℝ) N := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => logPhysicalPair (a,b)
  have hW : ∀ x y,W x y=W y x := by intro x y; simp only [W,logPhysicalPair,norm_sub_rev]
  have hc : 0 < Fintype.card ι := by exact_mod_cast hd
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hi := sourceLogEnergyWeight_integrable (β : ℝ) β.coe_nonneg hd ρ M hM hρ hpair N
  have hproper := equilibrium_modulated_eq_canonical (μ := μ) W hW V (β : ℝ) N
    (by omega) hEL hi
  have href := equilibrium_product_reference volume μ
    (fun x => -(β : ℝ)*(V x+DGRHS.potential μ W x)) hEL N
  letI : NeZero (Measure.pi (fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ ι)))) := ⟨href.2⟩
  have hcollision := href.1.ae_le (density_iid_collision_free ρ N)
  obtain ⟨hp,hfinite,hlaw⟩ := canonicalSingularLaw_eq_tilted volume W V (β : ℝ) N
    hproper.1 hcollision
  refine ⟨hproper.1,hp,hfinite,?_⟩
  rw [hlaw,←hproper.2,sourceEnergyTilt_eq _ _ _ (β : ℝ) N]
  exact sourceLogSingularGibbs_eq β hd ρ M hM hρ hpair N

theorem sourceRiesz_equilibrium_canonical (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x ≤ M) (V : EuclideanSpace ℝ ι → ℝ)
    (hEL : (volume : Measure (EuclideanSpace ℝ ι)).tilted (fun x => -β*
      (V x+DGRHS.potential (gaussianRieszDensityMeasure ρ) (fun a b => gaussianRieszPhysicalPair s (a,b)) x))=
      gaussianRieszDensityMeasure ρ) (N : ℕ) (hN : 1 ≤ N) :
    let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
    Integrable (fun x => Real.exp (-β*sourceHamiltonian W V N x))
      (Measure.pi (fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ ι)))) ∧
      0 < canonicalSingularPartition volume W V β N ∧
      canonicalSingularPartition volume W V β N < ∞ ∧
      sourceRieszSingularGibbs s β ρ N=canonicalSingularLaw volume W V β N := by
  dsimp only
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  have hW : ∀ x y,W x y=W y x := by intro x y; simp only [W,gaussianRieszPhysicalPair,norm_sub_rev]
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  have hi := sourceRieszEnergyWeight_integrable s β hs hβ.le ha ρ M hM hρ N
  have hproper := equilibrium_modulated_eq_canonical (μ := μ) W hW V β N (by omega) hEL hi
  have href := equilibrium_product_reference volume μ (fun x => -β*(V x+DGRHS.potential μ W x)) hEL N
  letI : NeZero (Measure.pi (fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ ι)))) := ⟨href.2⟩
  have hcollision := href.1.ae_le (density_iid_collision_free ρ N)
  obtain ⟨hp,hfinite,hlaw⟩ := canonicalSingularLaw_eq_tilted volume W V β N hproper.1 hcollision
  refine ⟨hproper.1,hp,hfinite,?_⟩
  rw [hlaw,←hproper.2,sourceEnergyTilt_eq _ _ _ β N]
  exact sourceRieszSingularGibbs_eq s β hs hβ.le ha ρ M hM hρ N
end DGRHS.CLT
#check @DGRHS.CLT.sourceLog_equilibrium_canonical
#check @DGRHS.CLT.sourceRiesz_equilibrium_canonical
#print axioms DGRHS.CLT.sourceLog_equilibrium_canonical
#print axioms DGRHS.CLT.sourceRiesz_equilibrium_canonical
