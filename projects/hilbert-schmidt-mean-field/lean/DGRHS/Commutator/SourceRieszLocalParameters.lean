import DGRHS.Commutator.SourceRieszLocalM1
import DGRHS.Commutator.SourceRieszLocalNorms

/-! One genuine positive source-local coupling threshold. Its constants are
built from actual Riesz row control, Gaussian profile and physical potential,
and discharge every smallness condition rather than assuming them. -/
noncomputable section
open MeasureTheory
namespace DGRHS.Commutator
open DGRHS.Gaussian DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

def sourceRieszLocalNormConstant (s M : ℝ) : ℝ :=
  1+144*|sourceRieszFullSquareRowControl s M ι|+12*Real.sqrt (sourceRieszFullSquareRowControl s M ι)

def sourceRieszLocalSizeConstant (s M : ℝ) : ℝ :=
  (4*sourceRieszLocalAbsorptionConstant (ι:=ι) s M+12*gaussianRieszSourceCoefficient s/s)*
    (1+2*(12*gaussianRieszSourceCoefficient s/s))

def sourceRieszLocalBeta (s M : ℝ) : ℝ :=
  1/(1+7*|gaussianRieszPhysicalPotentialConstant s M ι|+
    glzUniversalTailConstant*sourceRieszLocalNormConstant (ι:=ι) s M+
    2*glzUniversalTailConstant^2*sourceRieszLocalSizeConstant (ι:=ι) s M)

lemma sourceRieszLocalNormConstant_bounds (s M : ℝ) :
    0<sourceRieszLocalNormConstant (ι:=ι) s M ∧
    144*sourceRieszFullSquareRowControl s M ι≤sourceRieszLocalNormConstant (ι:=ι) s M ∧
    12*Real.sqrt (sourceRieszFullSquareRowControl s M ι)≤sourceRieszLocalNormConstant (ι:=ι) s M := by
  have ha := abs_nonneg (sourceRieszFullSquareRowControl s M ι)
  have hs := Real.sqrt_nonneg (sourceRieszFullSquareRowControl s M ι)
  have hb := le_abs_self (sourceRieszFullSquareRowControl s M ι)
  unfold sourceRieszLocalNormConstant
  constructor
  · linarith
  constructor <;> linarith

lemma sourceRieszLocalSizeConstant_pos (s M : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) : 0<sourceRieszLocalSizeConstant (ι:=ι) s M := by
  have hA := sourceRieszLocalAbsorptionConstant_pos (ι:=ι) s M hs hd hM
  have hc := gaussianRieszSourceCoefficient_pos s hs
  unfold sourceRieszLocalSizeConstant
  positivity

lemma sourceRieszLocalBeta_properties (s M : ℝ) (hs : 0<s)
    (hd : s<(Fintype.card ι:ℝ)) (hM : 0≤M) :
    0<sourceRieszLocalBeta (ι:=ι) s M ∧
    ∀ γ : ℝ,0<γ→γ≤sourceRieszLocalBeta (ι:=ι) s M→
      γ≤1 ∧ (7/4:ℝ)*γ*gaussianRieszPhysicalPotentialConstant s M ι≤1/4 ∧
      γ*sourceRieszLocalNormConstant (ι:=ι) s M≤1/glzUniversalTailConstant ∧
      2*glzUniversalTailConstant^2*sourceRieszLocalSizeConstant (ι:=ι) s M*γ≤1 := by
  let P := gaussianRieszPhysicalPotentialConstant s M ι
  let Cn := sourceRieszLocalNormConstant (ι:=ι) s M
  let Cs := sourceRieszLocalSizeConstant (ι:=ι) s M
  let L := glzUniversalTailConstant
  let D := 1+7*|P|+L*Cn+2*L^2*Cs
  have hL : 0<L := glzUniversalTailConstant_pos
  have hCn : 0<Cn := (sourceRieszLocalNormConstant_bounds (ι:=ι) s M).1
  have hCs : 0<Cs := sourceRieszLocalSizeConstant_pos s M hs hd hM
  have hD : 0<D := by dsimp[D];positivity
  have hD1 : 1≤D := by dsimp[D];nlinarith [mul_nonneg hL.le hCn.le,mul_nonneg (sq_nonneg L) hCs.le,abs_nonneg P]
  have hDP : 7*|P|≤D := by dsimp[D];nlinarith [mul_nonneg hL.le hCn.le,mul_nonneg (sq_nonneg L) hCs.le]
  have hDCn : L*Cn≤D := by dsimp[D];nlinarith [mul_nonneg (sq_nonneg L) hCs.le,abs_nonneg P]
  have hDCs : 2*L^2*Cs≤D := by dsimp[D];nlinarith [mul_nonneg hL.le hCn.le,abs_nonneg P]
  constructor
  · change 0<1/D
    positivity
  intro γ hγ hγb
  change γ≤1/D at hγb
  have hγD : γ*D≤1 := (le_div_iff₀ hD).mp hγb
  have h1 := mul_le_mul_of_nonneg_left hD1 hγ.le
  have hP := mul_le_mul_of_nonneg_left hDP hγ.le
  have hCn' := mul_le_mul_of_nonneg_left hDCn hγ.le
  have hCs' := mul_le_mul_of_nonneg_left hDCs hγ.le
  have hPabs := mul_le_mul_of_nonneg_left (le_abs_self P) hγ.le
  refine ⟨by nlinarith,by change (7/4:ℝ)*γ*P≤1/4;nlinarith,?_,?_⟩
  · change γ*Cn≤1/L
    apply (le_div_iff₀ hL).2
    nlinarith
  · change 2*L^2*Cs*γ≤1
    nlinarith

lemma sourceRieszLocal_small_square_bound (s M γ : ℝ) (hγ : 0≤γ) (hγ1 : γ≤1)
    (hC : 0≤sourceRieszFullSquareRowControl s M ι) :
    144*γ^2*sourceRieszFullSquareRowControl s M ι≤γ*sourceRieszLocalNormConstant (ι:=ι) s M := by
  have hsq : γ^2≤γ := by nlinarith
  have hb := mul_le_mul_of_nonneg_right hsq (mul_nonneg (by norm_num : 0≤(144:ℝ)) hC)
  have hc := mul_le_mul_of_nonneg_left (sourceRieszLocalNormConstant_bounds (ι:=ι) s M).2.1 hγ
  nlinarith

end DGRHS.Commutator

#check DGRHS.Commutator.sourceRieszLocalNormConstant
#print axioms DGRHS.Commutator.sourceRieszLocalNormConstant

#check DGRHS.Commutator.sourceRieszLocalSizeConstant
#print axioms DGRHS.Commutator.sourceRieszLocalSizeConstant

#check DGRHS.Commutator.sourceRieszLocalBeta
#print axioms DGRHS.Commutator.sourceRieszLocalBeta

#check DGRHS.Commutator.sourceRieszLocalNormConstant_bounds
#print axioms DGRHS.Commutator.sourceRieszLocalNormConstant_bounds

#check DGRHS.Commutator.sourceRieszLocalSizeConstant_pos
#print axioms DGRHS.Commutator.sourceRieszLocalSizeConstant_pos

#check DGRHS.Commutator.sourceRieszLocalBeta_properties
#print axioms DGRHS.Commutator.sourceRieszLocalBeta_properties

#check DGRHS.Commutator.sourceRieszLocal_small_square_bound
#print axioms DGRHS.Commutator.sourceRieszLocal_small_square_bound
