import DGRHS.Gaussian.GaussianRieszPhysicalPotential

/-! Proper actual full Riesz row controls, using only the true integrability
range. In particular the square row requires 2s<d, never 4s<d. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma sourceRiesz_full_potential_bound (s : ℝ) (hs : 0 < s)
    (hd : s < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y => gaussianRieszPhysicalPair s (x,y)) (gaussianRieszDensityMeasure ρ) ∧
    0 ≤ (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ∧
    (∫ y,gaussianRieszPhysicalPair s (x,y) ∂gaussianRieszDensityMeasure ρ) ≤
      gaussianRieszPhysicalPotentialConstant s M ι := by
  let μ := gaussianRieszDensityMeasure ρ
  have hc : 0 < Fintype.card ι := by
    exact_mod_cast (show (0 : ℝ) < (Fintype.card ι : ℝ) by linarith)
  letI : Nonempty ι := Fintype.card_pos_iff.mp hc
  letI : NullSingletonClass μ := by unfold μ gaussianRieszDensityMeasure; infer_instance
  have ha1 : 0 < (Fintype.card ι : ℝ)-s := sub_pos.mpr hd
  have he : (fun y => gaussianRieszPhysicalPair s (x,y)) =ᵐ[μ]
      (fun y => gaussianRieszEuclideanShortRange s 1 (x-y)+gaussianRieszEuclideanTruncation s 1 (x-y)) := by
    filter_upwards [μ.ae_ne x] with y hy
    exact gaussianRieszEuclidean_full_short_long_split s 1 hs (by norm_num) _ (sub_ne_zero.mpr hy.symm)
  have hiS := integrable_gaussianRieszShortRange_convolution s 1 (by norm_num) ha1 ρ M hρ x
  have hiL := integrable_gaussianRieszTruncation_convolution s 1 hs (by norm_num) μ x
  refine ⟨(hiS.add hiL).congr he.symm, integral_nonneg (fun y => ?_), ?_⟩
  · unfold gaussianRieszPhysicalPair
    positivity
  · rw [integral_congr_ae he, integral_add hiS hiL]
    have hS := gaussianRieszShortRange_convolution_le s 1 hs (by norm_num) ha1 ρ M hM hρ x
    have hL : (∫ y,gaussianRieszEuclideanTruncation s 1 (x-y) ∂μ) ≤ gaussianRieszSourceCoefficient s/s := by
      calc
        _ ≤ ∫ _ : EuclideanSpace ℝ ι, gaussianRieszSourceCoefficient s/s ∂μ :=
          integral_mono_ae hiL (integrable_const _) (Filter.Eventually.of_forall (fun y =>
            (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, Real.one_rpow, mul_one] using
              gaussianRieszEuclideanTruncation_le_diagonal s 1 hs (by norm_num) (x-y))))
        _ = _ := by simp
    simp only [Real.one_rpow, mul_one] at hS
    unfold gaussianRieszPhysicalPotentialConstant
    convert add_le_add hS hL using 1 <;> ring

def sourceRieszFullSquareRowControl (s M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  (2/s)*gaussianRieszPhysicalPotentialConstant (2*s) M ι

lemma sourceRieszPhysicalPair_square (s : ℝ) (hs : 0<s)
    (p : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
    (gaussianRieszPhysicalPair s p)^2=(2/s)*gaussianRieszPhysicalPair (2*s) p := by
  unfold gaussianRieszPhysicalPair
  rw [div_pow,←Real.rpow_natCast,←Real.rpow_mul (norm_nonneg _)]
  simp only [Nat.cast_ofNat]
  rw [show (-s)*(2:ℝ)=-(2*s) by ring]
  field_simp [hs.ne']

lemma sourceRieszPhysicalPair_square_row (s : ℝ) (hs : 0<s)
    (hd : 2*s<(Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (x : EuclideanSpace ℝ ι) :
    Integrable (fun y=>(gaussianRieszPhysicalPair s (x,y))^2) (gaussianRieszDensityMeasure ρ) ∧
      (∫ y,(gaussianRieszPhysicalPair s (x,y))^2 ∂gaussianRieszDensityMeasure ρ) ≤
        sourceRieszFullSquareRowControl s M ι := by
  obtain ⟨hi,hn,hb⟩ := sourceRiesz_full_potential_bound (2*s) (by positivity) hd ρ M hM hρ x
  have he : (fun y=>(gaussianRieszPhysicalPair s (x,y))^2)=
      (fun y=>(2/s)*gaussianRieszPhysicalPair (2*s) (x,y)) := by
    funext y
    exact sourceRieszPhysicalPair_square s hs (x,y)
  rw [he]
  refine ⟨hi.const_mul _,?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end DGRHS.Commutator
#check DGRHS.Commutator.sourceRiesz_full_potential_bound
#print axioms DGRHS.Commutator.sourceRiesz_full_potential_bound
#check DGRHS.Commutator.sourceRieszFullSquareRowControl
#print axioms DGRHS.Commutator.sourceRieszFullSquareRowControl
#check DGRHS.Commutator.sourceRieszPhysicalPair_square
#print axioms DGRHS.Commutator.sourceRieszPhysicalPair_square
#check DGRHS.Commutator.sourceRieszPhysicalPair_square_row
#print axioms DGRHS.Commutator.sourceRieszPhysicalPair_square_row
