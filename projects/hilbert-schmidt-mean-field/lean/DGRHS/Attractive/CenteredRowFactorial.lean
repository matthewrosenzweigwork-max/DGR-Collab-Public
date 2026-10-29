/- Proper every-row centering of a nonnegative symmetric kernel.
All potentials/means are genuine proper integrals from the actual raw moments. -/
import DGRHS.Attractive.RowMomentAlgebra
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω]

lemma nonneg_centered_rowFactorial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω×Ω→ℝ) (hW : Measurable W) (hn : ∀ z,0≤W z)
    (hs : ∀ x y,W (x,y)=W (y,x)) (C : ℝ) (hC : RowFactorialMoments μ W C) :
    RowFactorialMoments μ (DGRHS.Gaussian.hoeffdingCentered μ W) (12*C) := by
  classical
  let P := fun y => ∫ x,W (x,y) ∂μ
  let K := ∫ z,W z ∂μ.prod μ
  have hrow (y : Ω) : Integrable (fun x => W (x,y)) μ := by
    simpa only [pow_one,abs_of_nonneg (hn _)] using hC.proper 1 (by omega) y
  have hP (y : Ω) : 0≤P y ∧ P y≤C := by
    constructor
    · exact integral_nonneg (fun x => hn (x,y))
    · simpa only [P,pow_one,abs_of_nonneg (hn _),Nat.factorial_one,Nat.cast_one,mul_one]
        using hC.bound 1 (by omega) y
  have hi : Integrable W (μ.prod μ) := by
    simpa only [pow_one,abs_of_nonneg (hn _)] using joint_abs_power_integrable μ W hW C hC 1 (by omega)
  have hK : 0≤K ∧ K≤C := by
    constructor
    · exact integral_nonneg hn
    · change (∫ z,W z ∂μ.prod μ)≤C
      rw [integral_prod_symm _ hi]
      calc
        _ ≤ ∫ _ : Ω,C ∂μ := integral_mono_ae hi.integral_prod_right (integrable_const C)
          (Filter.Eventually.of_forall fun y => (hP y).2)
        _ = _ := by simp
  have he (x y : Ω) : DGRHS.Gaussian.hoeffdingCentered μ W (x,y)=W (x,y)-P x-P y+K := by
    unfold DGRHS.Gaussian.hoeffdingCentered DGRHS.centeredKernel DGRHS.potential DGRHS.secondPotential P K
    have hswap : (∫ z, W (x,z) ∂μ) = ∫ z, W (z,x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => hs x z)
    change W (x,y) - (∫ z,W (x,z) ∂μ) - (∫ z,W (z,y) ∂μ) +
      (∫ z,W z ∂μ.prod μ) = W (x,y) - (∫ z,W (z,x) ∂μ) -
      (∫ z,W (z,y) ∂μ) + (∫ z,W z ∂μ.prod μ)
    rw [hswap]
  have hpoint (p : ℕ) (x y : Ω) :
      |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)|^p ≤
        2^p*(|W (x,y)|^p+(3*C)^p) := by
    have ha : |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)|≤W (x,y)+3*C := by
      rw [he]
      apply abs_le.mpr
      constructor <;> linarith [(hP x).1,(hP x).2,(hP y).1,(hP y).2,hK.1,hK.2,hn (x,y),hC.nonneg]
    have hb := (pow_le_pow_left₀ (abs_nonneg _) ha p).trans
      (nonneg_sum_pow_le _ _ (hn (x,y)) (by linarith [hC.nonneg]) p)
    simpa only [abs_of_nonneg (hn _)] using hb
  have hpint (p : ℕ) (hp : 1≤p) (y : Ω) :
      Integrable (fun x => |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)|^p) μ := by
    apply (((hC.proper p hp y).add (integrable_const ((3*C)^p))).const_mul (2^p)).mono'
      (by
        have hm := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ W hW.stronglyMeasurable).measurable
        exact ((continuous_pow p).measurable.comp (continuous_abs.measurable.comp
          (hm.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖|DGRHS.Gaussian.hoeffdingCentered μ W (x,y)|^p‖ ≤
        2^p*(|W (x,y)|^p+(3*C)^p)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
      exact hpoint p x y
  refine ⟨by linarith [hC.nonneg],hpint,?_⟩
  intro p hp y
  have hb := integral_mono_ae (hpint p hp y)
    (((hC.proper p hp y).add (integrable_const ((3*C)^p))).const_mul (2^p))
    (Filter.Eventually.of_forall fun x => hpoint p x y)
  change (∫ x,|DGRHS.Gaussian.hoeffdingCentered μ W (x,y)|^p ∂μ) ≤
    ∫ x,2^p*(|W (x,y)|^p+(3*C)^p) ∂μ at hb
  rw [integral_const_mul,integral_add (hC.proper p hp y) (integrable_const ((3*C)^p))] at hb
  simp only [integral_const,probReal_univ,one_smul] at hb
  have hfac : (1:ℝ)≤(p.factorial:ℝ) := by exact_mod_cast (show 1≤p.factorial by have h:=Nat.factorial_pos p;omega)
  have hCp : C^p≤(3*C)^p := pow_le_pow_left₀ hC.nonneg (by linarith [hC.nonneg]) p
  have h2 : (2:ℝ)≤2^p := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hp
  calc
    _ ≤ 2^p*((∫ x,|W (x,y)|^p ∂μ)+(3*C)^p) := hb
    _ ≤ 2^p*(C^p*(p.factorial:ℝ)+(3*C)^p) :=
      mul_le_mul_of_nonneg_left (add_le_add (hC.bound p hp y) le_rfl) (by positivity)
    _ ≤ 2^p*(2*(3*C)^p*(p.factorial:ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right hCp (Nat.cast_nonneg (p.factorial))
      have h3 : (3*C)^p≤(3*C)^p*(p.factorial:ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
          (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hC.nonneg) p)
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ ≤ 2^p*(2^p*(3*C)^p*(p.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (pow_nonneg (mul_nonneg (by norm_num) hC.nonneg) p))
          (Nat.cast_nonneg p.factorial)) (by positivity)
    _ = _ := by
      rw [←mul_assoc,←mul_assoc,←mul_pow,←mul_pow]
      congr 1
      congr 1
      ring

end DGRHS.Attractive
#check @DGRHS.Attractive.nonneg_centered_rowFactorial
#print axioms DGRHS.Attractive.nonneg_centered_rowFactorial
