/- Original all-temperature positive Riesz partition growth, with the
sharp iid scale derived from the actual singular kernel and potential. -/
import DGRHS.Entropy.SourceLogTemperatureGrowth
import DGRHS.Entropy.SourceRieszSharpIidFloor
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace DGRHS.Entropy
open DGRHS.Gaussian DGRHS.CLT DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def rieszTemperatureFloorConstant (s M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  2*gaussianRieszSourceCoefficient s/s +
    M*gaussianRieszSourceCoefficient s*(2*Real.pi)^((Fintype.card ι : ℝ)/2)/
      ((Fintype.card ι : ℝ)-s) + gaussianRieszPhysicalPotentialConstant s M ι

theorem sourceRieszEnergy_sharp_iid_floor (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    let μ := gaussianRieszDensityMeasure ρ
    let W := fun a b => gaussianRieszPhysicalPair s (a,b)
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      -(N : ℝ)*sourceCanonicalModulatedEnergy (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x ≤
      rieszTemperatureFloorConstant s M ι*(N : ℝ)^(s/(Fintype.card ι : ℝ)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => gaussianRieszPhysicalPair s (a,b)
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let F := DGRHS.potential μ W
  let I := DGRHS.interactionEnergy μ W
  let Cp := gaussianRieszPhysicalPotentialConstant s M ι
  have hs0 := (gaussianRieszSourceCoefficient_pos s hs).le
  have hd : 0 < (Fintype.card ι : ℝ) := by linarith
  have hds : 0 < (Fintype.card ι : ℝ)-s := by linarith
  have hCp : 0 ≤ Cp := by dsimp [Cp, gaussianRieszPhysicalPotentialConstant]; positivity
  have hI : 0 ≤ I := by
    unfold I DGRHS.interactionEnergy
    apply mul_nonneg (by norm_num)
    apply integral_nonneg
    intro p
    dsimp [W, gaussianRieszPhysicalPair]
    positivity
  have hnp : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hnr : (N : ℝ) ≠ 0 := ne_of_gt hnp
  have hNpow : 1 ≤ (N : ℝ)^(s/(Fintype.card ι : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast hN) (div_nonneg hs.le hd.le)
  have havg (x : Fin N → EuclideanSpace ℝ ι) : (N : ℝ)⁻¹*(∑ i, F (x i)) ≤ Cp := by
    have hsum : (∑ i : Fin N, F (x i)) ≤ (N : ℝ)*Cp := by
      calc
        _ ≤ ∑ _ : Fin N, Cp := Finset.sum_le_sum (fun i _ =>
          (gaussianRieszPhysicalPotential_bound s hs ha ρ M hM hρ (x i)).2.2)
        _ = _ := by simp
    have hh := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnp.le)
    simpa only [←mul_assoc, inv_mul_cancel₀ hnr, one_mul] using hh
  have hCpN := mul_le_mul_of_nonneg_left hNpow hCp
  filter_upwards [rieszNegativeStatistic_sharp_Npower_ae s hs ha ρ M hM hρ N hN] with x hx
  have he := sourceCanonicalModulatedEnergy_exponent H F I 1 (by omega) x
  have hiid := iidCanonicalExponent_eq 1 H N x
  simp only [neg_one_mul, one_mul] at he hiid
  change -(N : ℝ)*sourceCanonicalModulatedEnergy H F I N x ≤ _
  dsimp [rieszTemperatureFloorConstant]
  change iidNegativeStatistic N H x ≤ _ at hx
  dsimp [Cp] at hCpN
  simp only [div_eq_mul_inv] at he hiid hx hCpN ⊢
  nlinarith [havg x]

theorem sourceRieszPartition_all_temperature_growth (s B : ℝ) (hs : 0 < s) (hB : 0 < B)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
      (sourceRieszSingularPartition s β ρ N).toReal ≤
        C*Real.exp (C*max (β-B) 0*(N : ℝ)^(s/(Fintype.card ι : ℝ))) := by
  obtain ⟨Cb, _, hcap⟩ := sourceRieszPartition_uniform s B hs hB.le ha ρ M hM hρ
  let C := max (max Cb 1) (rieszTemperatureFloorConstant s M ι)
  have hC : 1 ≤ C := (le_max_right Cb 1).trans (le_max_left _ _)
  have hCbC : Cb ≤ C := (le_max_left Cb 1).trans (le_max_left _ _)
  have hC0C : rieszTemperatureFloorConstant s M ι ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro β hβ N hN
  let μ := gaussianRieszDensityMeasure ρ
  let E := sourceCanonicalModulatedEnergy (hoeffdingCentered μ (gaussianRieszPhysicalPair s))
    (DGRHS.potential μ (fun a b => gaussianRieszPhysicalPair s (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => gaussianRieszPhysicalPair s (a,b))) N
  let X := fun x => -(N : ℝ)*E x
  let P := Measure.pi (fun _ : Fin N => μ)
  let a := (N : ℝ)^(s/(Fintype.card ι : ℝ))
  have ha0 : 0 ≤ a := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have he (b : ℝ) : (fun x => Real.exp (b*X x)) =
      (fun x => Real.exp (-b*(N : ℝ)*E x)) := by funext x; congr 1; dsimp [X]; ring
  obtain ⟨hiB, hb⟩ := hcap N hN
  obtain ⟨_, _, hiβ⟩ := sourceRieszPartition_uniform s β hs hβ ha ρ M hM hρ
  have hiB' : Integrable (fun x => Real.exp (B*X x)) P := by rw [he]; exact hiB
  have hiβ' : Integrable (fun x => Real.exp (β*X x)) P := by rw [he]; exact (hiβ N hN).1
  have hb' : (∫ x, Real.exp (B*X x) ∂P) ≤ C := by rw [he]; exact hb.trans hCbC
  have hout := exponential_temperature_growth P X B hB
    (rieszTemperatureFloorConstant s M ι*a) C β hC hβ
    (sourceRieszEnergy_sharp_iid_floor s hs ha ρ M hM hρ N hN) hiB' hiβ' hb'
  rw [he] at hout
  rw [sourceRieszSingularPartition_eq_integral s β hs hβ ha ρ M hM hρ N]
  have hp : 0 ≤ physicalRieszSourcePartition s β ρ N := by
    unfold physicalRieszSourcePartition
    exact integral_nonneg fun x => (Real.exp_pos _).le
  rw [ENNReal.toReal_ofReal hp]
  refine hout.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith : 0 ≤ C))
  have hh := mul_le_mul_of_nonneg_right hC0C (mul_nonneg (le_max_right (β-B) (0 : ℝ)) ha0)
  nlinarith [hh]

end DGRHS.Entropy
#check @DGRHS.Entropy.sourceRieszEnergy_sharp_iid_floor
#check @DGRHS.Entropy.sourceRieszPartition_all_temperature_growth
#print axioms DGRHS.Entropy.sourceRieszEnergy_sharp_iid_floor
#print axioms DGRHS.Entropy.sourceRieszPartition_all_temperature_growth
