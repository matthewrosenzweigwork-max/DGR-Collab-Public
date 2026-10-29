/- Derived proper every-row factorial moments of the actual Gaussian
logarithmic short kernel. Uniform in 0<eta<=1, p>=1 and every fixed row.
The allowed physical bounded density supplies the only measure comparison. -/
import DGRHS.Gaussian.GaussianLogShortRangeMoments
import DGRHS.Attractive.RowMoments
import Mathlib.Analysis.Complex.Exponential
noncomputable section
open MeasureTheory Real
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogShortFactorialConstant (M d : ℝ) : ℝ :=
  (1+M*(2*Real.pi)^(d/2))*Real.exp 1/d

lemma gaussianLogShortMoment_arithmetic (p : ℕ) (hp : 1≤p)
    (η M d : ℝ) (hη : 0<η) (hη1 : η≤1) (hM : 0≤M) (hd : 0<d) :
    M*(η^(d/(p:ℝ))/(d/(p:ℝ)))^p*(2*Real.pi/(p:ℝ))^(d/2) ≤
      (gaussianLogShortFactorialConstant M d)^p*(p.factorial:ℝ) := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
  have hp1 : 1≤(p:ℝ) := by exact_mod_cast hp
  have he : (η^(d/(p:ℝ))/(d/(p:ℝ)))^p=η^d*((p:ℝ)/d)^p := by
    rw [div_pow,←Real.rpow_natCast (η^(d/(p:ℝ))),←Real.rpow_mul hη.le]
    have hex : (d/(p:ℝ))*(p:ℝ)=d := by field_simp
    rw [hex]
    have hrec : (d/(p:ℝ))⁻¹=(p:ℝ)/d := by field_simp
    rw [div_eq_mul_inv,←inv_pow,hrec]
  rw [he]
  have hηpow : η^d≤1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hη.le hη1 hd.le
  have hπ : (2*Real.pi/(p:ℝ))^(d/2)≤(2*Real.pi)^(d/2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact (div_le_iff₀ hp0).mpr (by nlinarith [Real.pi_pos])
  let K := (2*Real.pi)^(d/2)
  let D := 1+M*K
  have hK : 0≤K := by unfold K;positivity
  have hD : 1≤D := by unfold D;nlinarith
  have hDp : M*K≤D^p := by
    have h := pow_le_pow_right₀ hD hp
    simp only [pow_one] at h
    exact (show M*K≤D by unfold D;linarith).trans h
  have hfac : 0<(p.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hpower := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (p:ℝ) (by positivity) p)
  have hexp : Real.exp (p:ℝ)=(Real.exp 1)^p := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hpower
  calc
    M*(η^d*((p:ℝ)/d)^p)*(2*Real.pi/(p:ℝ))^(d/2) ≤
      M*(1*((p:ℝ)/d)^p)*K := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hηpow (by positivity)) hM) hπ
          (by positivity) (by positivity)
    _ = (M*K)*((p:ℝ)/d)^p := by ring
    _ ≤ D^p*((p:ℝ)/d)^p := mul_le_mul_of_nonneg_right hDp (by positivity)
    _ ≤ D^p*((Real.exp 1)^p*(p.factorial:ℝ)/d^p) := by
      rw [div_pow]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpower (by positivity)) (by positivity)
    _ = (gaussianLogShortFactorialConstant M d)^p*(p.factorial:ℝ) := by
      unfold gaussianLogShortFactorialConstant D K
      rw [div_pow,mul_pow]
      ring

lemma gaussianLogShortRange_row_pow (p : ℕ) (hp : 1≤p)
    (η : ℝ) (hη : 0<η) (hd : 0<(Fintype.card ι:ℝ))
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) (y : EuclideanSpace ℝ ι) :
    Integrable (fun x => |gaussianLogShortRange η (x-y)|^p) (gaussianRieszDensityMeasure ρ) ∧
    (∫ x,|gaussianLogShortRange η (x-y)|^p ∂gaussianRieszDensityMeasure ρ) ≤
      M*(η^((Fintype.card ι:ℝ)/(p:ℝ))/((Fintype.card ι:ℝ)/(p:ℝ)))^p *
      (2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2) := by
  have hv := integral_gaussianLogShortRange_pow_le (ι:=ι) p hp η hη hd
  have hi := hv.1.comp_sub_right y
  have his : Integrable (fun x => gaussianLogShortRange η (x-y)^p)
      (ENNReal.ofReal M • volume) := hi.smul_measure ENNReal.ofReal_ne_top
  have hid := his.mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
  simp_rw [abs_of_nonneg (gaussianLogShortRange_nonneg η _)]
  refine ⟨hid,?_⟩
  calc
    _ ≤ ∫ x,gaussianLogShortRange η (x-y)^p ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure (gaussianRieszDensityMeasure_le ρ M hρ)
        (Filter.Eventually.of_forall fun x => pow_nonneg (gaussianLogShortRange_nonneg η _) p) his
    _ = M*(∫ x : EuclideanSpace ℝ ι,gaussianLogShortRange η x^p) := by
      rw [integral_smul_measure,ENNReal.toReal_ofReal hM,
        integral_sub_right_eq_self (fun x => gaussianLogShortRange η x^p) y,
        smul_eq_mul]
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left hv.2 hM using 1 <;> ring

theorem gaussianLogShortRange_factorial_rows (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    DGRHS.Attractive.RowFactorialMoments (gaussianRieszDensityMeasure ρ)
      (fun z => gaussianLogShortRange η (z.1-z.2))
      (gaussianLogShortFactorialConstant M (Fintype.card ι:ℝ)) := by
  refine ⟨?_,?_,?_⟩
  · unfold gaussianLogShortFactorialConstant
    positivity
  · intro p hp y
    exact (gaussianLogShortRange_row_pow p hp η hη hd ρ M hM hρ y).1
  · intro p hp y
    have h := (gaussianLogShortRange_row_pow p hp η hη hd ρ M hM hρ y).2
    have hb := gaussianLogShortMoment_arithmetic p hp η M (Fintype.card ι:ℝ) hη hη1 hM hd
    exact h.trans (by simpa only [mul_assoc] using hb)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogShortRange_factorial_rows
#print axioms DGRHS.Gaussian.gaussianLogShortMoment_arithmetic
#print axioms DGRHS.Gaussian.gaussianLogShortRange_row_pow
#print axioms DGRHS.Gaussian.gaussianLogShortRange_factorial_rows
