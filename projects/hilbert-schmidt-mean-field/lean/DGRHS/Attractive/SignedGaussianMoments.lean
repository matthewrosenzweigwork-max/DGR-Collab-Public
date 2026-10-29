import DGRHS.Attractive.SignedFeatureDiagonalMoment
import Mathlib.Probability.Moments.IntegrableExpMul

/-! Genuine absolute Gaussian MGF and exponentially weighted even moments.
These are derived from the actual law, including zero variance; they are not
assumed uniform remainder moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

lemma gaussian_exp_mgf (D : ℝ) (hD : 0 ≤ D)
    (hX : HasLaw X (gaussianReal 0 (Real.toNNReal D)) P) (s : ℝ) :
    Integrable (fun ω => Real.exp (s*X ω)) P ∧
    (∫ ω, Real.exp (s*X ω) ∂P) = Real.exp (D*s^2/2) := by
  have he : mgf X P s=Real.exp (D*s^2/2) := by
    rw [mgf_gaussianReal hX]
    simp only [zero_mul, zero_add, Real.toNNReal_of_nonneg hD, NNReal.coe_mk]
  exact ⟨mgf_pos_iff.mp (he.symm ▸ Real.exp_pos _), he⟩

lemma gaussian_abs_exponential (D : ℝ) (hD : 0 ≤ D)
    (hX : HasLaw X (gaussianReal 0 (Real.toNNReal D)) P) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => Real.exp (s*|X ω|)) P ∧
    (∫ ω, Real.exp (s*|X ω|) ∂P) ≤ 2*Real.exp (D*s^2/2) := by
  obtain ⟨hi, he⟩ := gaussian_exp_mgf D hD hX s
  obtain ⟨hn, hen⟩ := gaussian_exp_mgf D hD hX (-s)
  have ha := integrable_exp_mul_abs hi hn
  refine ⟨ha, ?_⟩
  calc
    _ ≤ ∫ ω, Real.exp (s*X ω)+Real.exp (-s*X ω) ∂P := by
      apply integral_mono ha (hi.add hn)
      intro ω
      change Real.exp (s*|X ω|) ≤ Real.exp (s*X ω)+Real.exp (-s*X ω)
      simpa only [abs_mul, abs_of_nonneg hs, neg_mul] using Real.exp_abs_le (s*X ω)
    _ = 2*Real.exp (D*s^2/2) := by
      have hsq : D*(-s)^2/2=D*s^2/2 := by ring
      rw [hsq] at hen
      rw [integral_add hi hn, he, hen]
      ring

lemma gaussian_weighted_even_moment (D : ℝ) (hD : 0 ≤ D)
    (hX : HasLaw X (gaussianReal 0 (Real.toNNReal D)) P)
    (s : ℝ) (hs : 0 ≤ s) (r : ℕ) :
    Integrable (fun ω => |X ω|^(2*r)*Real.exp (s*|X ω|)) P ∧
    (∫ ω, |X ω|^(2*r)*Real.exp (s*|X ω|) ∂P) ≤
      2*((2*r).factorial:ℝ)*D^r*Real.exp (D*s^2+1) := by
  by_cases hz : D=0
  · subst D
    have hx : X=ᵐ[P] fun _ => 0 := HasLaw.ae_eq_of_dirac (by simpa using hX)
    have he : (fun ω => |X ω|^(2*r)*Real.exp (s*|X ω|)) =ᵐ[P]
        fun _ => (0:ℝ)^(2*r) := by
      filter_upwards [hx] with ω hω
      simp [hω]
    refine ⟨(integrable_const ((0:ℝ)^(2*r))).congr he.symm, ?_⟩
    rw [integral_congr_ae he]
    cases r with
    | zero =>
      have h1 : (∫ ω,(1:ℝ) ∂P)=1 := by simp
      simp only [Nat.mul_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, zero_mul,
        zero_add, one_mul, mul_one,h1]
      linarith [Real.add_one_le_exp (1:ℝ)]
    | succ r => simp
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hz)
    let a := (Real.sqrt D)⁻¹
    have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hDp)
    have hcoef : ((2*r).factorial:ℝ)/a^(2*r)=((2*r).factorial:ℝ)*D^r := by
      dsimp [a]
      rw [inv_pow, div_inv_eq_mul, pow_mul, Real.sq_sqrt hD]
    have hbound (x : ℝ) : |x|^(2*r)*Real.exp (s*|x|) ≤
        (((2*r).factorial:ℝ)*D^r)*Real.exp ((s+a)*|x|) := by
      have h := mul_le_mul_of_nonneg_right
        (nonnegative_power_le_exponential a |x| ha (abs_nonneg x) (2*r))
        (Real.exp_pos (s*|x|)).le
      rw [hcoef] at h
      calc
        _ ≤ _ := h
        _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          rw [show a*|x|+s*|x|=(s+a)*|x| by ring]
    obtain ⟨hi, he⟩ := gaussian_abs_exponential D hD hX (s+a) (add_nonneg hs ha.le)
    have hm : AEStronglyMeasurable (fun ω => |X ω|^(2*r)*Real.exp (s*|X ω|)) P := by
      have hXm := hX.aemeasurable.aestronglyMeasurable
      exact (hXm.norm.pow (2*r)).mul
        (Real.continuous_exp.comp_aestronglyMeasurable (hXm.norm.const_mul s))
    have hproper : Integrable (fun ω => |X ω|^(2*r)*Real.exp (s*|X ω|)) P := by
      apply (hi.const_mul (((2*r).factorial:ℝ)*D^r)).mono' hm
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound _
    have hq : D*(s+a)^2/2 ≤ D*s^2+1 := by
      have hsq := Real.sq_sqrt hD
      have hsp : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDp
      dsimp [a]
      have hh := sq_nonneg (s*Real.sqrt D-1)
      field_simp [hsp.ne']
      nlinarith
    refine ⟨hproper, ?_⟩
    calc
      _ ≤ ∫ ω, (((2*r).factorial:ℝ)*D^r)*Real.exp ((s+a)*|X ω|) ∂P :=
        integral_mono hproper (hi.const_mul _) (fun ω => hbound (X ω))
      _ = (((2*r).factorial:ℝ)*D^r)*(∫ ω, Real.exp ((s+a)*|X ω|) ∂P) :=
        integral_const_mul _ _
      _ ≤ (((2*r).factorial:ℝ)*D^r)*(2*Real.exp (D*(s+a)^2/2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = 2*((2*r).factorial:ℝ)*D^r*Real.exp (D*(s+a)^2/2) := by ring
      _ ≤ 2*((2*r).factorial:ℝ)*D^r*Real.exp (D*s^2+1) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hq) (by positivity)

end DGRHS.Attractive
#check DGRHS.Attractive.gaussian_abs_exponential
#print axioms DGRHS.Attractive.gaussian_abs_exponential
#check DGRHS.Attractive.gaussian_weighted_even_moment
#print axioms DGRHS.Attractive.gaussian_weighted_even_moment
