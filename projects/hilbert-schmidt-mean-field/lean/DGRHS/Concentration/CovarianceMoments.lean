import DGRHS.Concentration.HilbertEntropy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped InnerProductSpace
namespace DGRHS.Concentration

lemma bounded_real_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {B : ℝ}
    (hX : AEStronglyMeasurable X μ) (hB : ∀ᵐ x ∂μ, |X x| ≤ B) (p : ENNReal) :
    MemLp X p μ := memLp_of_bounded (hB.mono fun _ hx ↦ abs_le.mp hx) hX p

lemma centered_product_sum_bounded {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Fin n → Ω → ℝ) (B : ℝ)
    (hX : ∀ i, AEStronglyMeasurable (X i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, |X i x| ≤ B) :
    AEStronglyMeasurable (fun ω : Fin n → Ω ↦ ∑ i, (X i (ω i)-∫ x, X i x ∂μ i)) (Measure.pi μ) ∧
      ∀ᵐ ω ∂Measure.pi μ, |∑ i, (X i (ω i)-∫ x, X i x ∂μ i)| ≤
        ∑ i, (B+|∫ x, X i x ∂μ i|) := by
  have ha : ∀ i, AEStronglyMeasurable (fun ω : Fin n → Ω ↦ X i (ω i)) (Measure.pi μ) := fun i ↦
    (hX i).comp_quasiMeasurePreserving (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving
  have hi : ∀ i, Integrable (fun ω : Fin n → Ω ↦ X i (ω i)-∫ x, X i x ∂μ i) (Measure.pi μ) := fun i ↦
    (((bounded_real_memLp (hX i) (hB i) 2).comp_measurePreserving (measurePreserving_pi_coordinate μ i)).integrable (by norm_num)).sub (integrable_const _)
  refine ⟨(integrable_finsetSum _ (fun i _ ↦ hi i)).aestronglyMeasurable, ?_⟩
  have hj := ae_all_iff.mpr fun i ↦
    (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i)
  filter_upwards [hj] with ω hω
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
    (by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (X i (ω i)) (-(∫ x, X i x ∂μ i)) : |X i (ω i)-∫ x, X i x ∂μ i| ≤ |X i (ω i)|+|∫ x, X i x ∂μ i|).trans (add_le_add (hω i) le_rfl))

/-- Actual independent scalar coordinate variance, obtained from the product law. -/
lemma centered_product_sum_square_le {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : Fin n → Ω → ℝ) (B : ℝ)
    (hX : ∀ i, AEStronglyMeasurable (X i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, |X i x| ≤ B) :
    (∫ ω : Fin n → Ω, (∑ i, (X i (ω i)-∫ x, X i x ∂μ i))^2 ∂Measure.pi μ) ≤
      ∑ i, ∫ x, (X i x)^2 ∂μ i := by
  have hp : ∀ i, MemLp (X i) 2 (μ i) := fun i ↦ bounded_real_memLp (hX i) (hB i) 2
  have ha : ∀ i, AEStronglyMeasurable (fun ω : Fin n → Ω ↦ X i (ω i)) (Measure.pi μ) := fun i ↦
    (hX i).comp_quasiMeasurePreserving (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving
  have hi : ∀ i, Integrable (fun ω : Fin n → Ω ↦ X i (ω i)) (Measure.pi μ) := fun i ↦
    ((hp i).comp_measurePreserving (measurePreserving_pi_coordinate μ i)).integrable (by norm_num)
  have hm : (∫ ω : Fin n → Ω, (∑ i, X i (ω i)) ∂Measure.pi μ) = ∑ i, ∫ x, X i x ∂μ i := by
    rw [integral_finsetSum _ (fun i _ ↦ hi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_comp_eval (μ := μ) (X := fun _ : Fin n ↦ Ω) (i := i) (f := X i) (hX i)
  have hv : variance (fun ω : Fin n → Ω ↦ ∑ i, X i (ω i)) (Measure.pi μ) = ∑ i, variance (X i) (μ i) := by
    have he : (fun ω : Fin n → Ω ↦ ∑ i, X i (ω i)) = ∑ i, (fun ω : Fin n → Ω ↦ X i (ω i)) := by
      funext ω
      simp
    rw [he]
    exact variance_sum_pi hp
  rw [variance_eq_integral (integrable_finsetSum _ (fun i _ ↦ hi i)).aestronglyMeasurable.aemeasurable,hm] at hv
  have he : (fun ω : Fin n → Ω ↦ (∑ i, (X i (ω i)-∫ x, X i x ∂μ i))^2) =
      fun ω ↦ ((∑ i, X i (ω i))-(∑ i, ∫ x, X i x ∂μ i))^2 := by
    funext ω
    rw [Finset.sum_sub_distrib]
  rw [he]
  change _ ≤ _
  simpa only [Pi.pow_apply] using (hv.trans_le (Finset.sum_le_sum fun i _ ↦ by
    rw [variance_eq_sub (hp i)]
    exact sub_le_self _ (sq_nonneg _)))

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι]

lemma basis_inner_square (b : OrthonormalBasis ι ℝ H) (z u : H) :
    (inner ℝ z u)^2 = ∑ p : ι × ι,
      (inner ℝ (b p.1) z*inner ℝ (b p.2) z)*(inner ℝ (b p.1) u*inner ℝ (b p.2) u) := by
  rw [← b.sum_inner_mul_inner z u,pow_two,Finset.sum_mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [real_inner_comm z (b a),real_inner_comm z (b c)]
  ring

lemma basis_outer_square_sum (b : OrthonormalBasis ι ℝ H) (z : H) :
    (∑ p : ι × ι, (inner ℝ (b p.1) z*inner ℝ (b p.2) z)^2) = ‖z‖^4 := by
  simp_rw [Fintype.sum_prod_type,mul_pow]
  rw [← Finset.sum_mul_sum,b.sum_sq_inner_right]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

def covarianceRemainder (b : OrthonormalBasis ι ℝ H) (μ : Fin n → Measure Ω)
    (Z : Fin n → Ω → H) (ω : Fin n → Ω) (p : ι × ι) : ℝ :=
  ∑ i, (inner ℝ (b p.1) (Z i (ω i))*inner ℝ (b p.2) (Z i (ω i))-
    ∫ x, inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x) ∂μ i)

def covarianceRadius (b : OrthonormalBasis ι ℝ H) (μ : Fin n → Measure Ω)
    (Z : Fin n → Ω → H) (ω : Fin n → Ω) : ℝ :=
  Real.sqrt (∑ p, (covarianceRemainder b μ Z ω p)^2)

lemma covariance_remainder_bounded (b : OrthonormalBasis ι ℝ H)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) (p : ι × ι) :
    AEStronglyMeasurable (fun ω ↦ covarianceRemainder b μ Z ω p) (Measure.pi μ) ∧
      ∀ᵐ ω ∂Measure.pi μ, |covarianceRemainder b μ Z ω p| ≤
      ∑ i, (B^2+|∫ x, inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x) ∂μ i|) := by
  unfold covarianceRemainder
  apply centered_product_sum_bounded μ (fun i x ↦ inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x)) (B^2)
  · intro i
    exact ((by fun_prop : Continuous (fun z : H ↦ inner ℝ (b p.1) z)).comp_aestronglyMeasurable (hZ i)).mul
      ((by fun_prop : Continuous (fun z : H ↦ inner ℝ (b p.2) z)).comp_aestronglyMeasurable (hZ i))
  · intro i
    filter_upwards [hB i] with x hx
    have ha : |inner ℝ (b p.1) (Z i x)| ≤ B := (abs_real_inner_le_norm _ _).trans (by simpa using hx)
    have hc : |inner ℝ (b p.2) (Z i x)| ≤ B := (abs_real_inner_le_norm _ _).trans (by simpa using hx)
    rw [abs_mul,pow_two]
    exact mul_le_mul ha hc (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma covariance_radius_bounded (b : OrthonormalBasis ι ℝ H)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) :
    ∃ K : ℝ, AEStronglyMeasurable (covarianceRadius b μ Z) (Measure.pi μ) ∧
      ∀ᵐ ω ∂Measure.pi μ, |covarianceRadius b μ Z ω| ≤ K := by
  let K := fun p : ι × ι ↦ ∑ i, (B^2+|∫ x, inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x) ∂μ i|)
  have hh := fun p ↦ covariance_remainder_bounded b μ Z B hZ hB p
  refine ⟨Real.sqrt (∑ p, (K p)^2), Real.continuous_sqrt.comp_aestronglyMeasurable
    (integrable_finsetSum _ (fun p _ ↦ integrable_of_ae_abs_le (bounded_square (hh p).1 (hh p).2).1 (bounded_square (hh p).1 (hh p).2).2)).aestronglyMeasurable, ?_⟩
  filter_upwards [ae_all_iff.mpr fun p ↦ (hh p).2] with ω hω
  change |Real.sqrt (∑ p, (covarianceRemainder b μ Z ω p)^2)| ≤ _
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro p _
  nlinarith [hω p,abs_nonneg (covarianceRemainder b μ Z ω p),sq_abs (covarianceRemainder b μ Z ω p)]

#print axioms DGRHS.Concentration.centered_product_sum_square_le
#print axioms DGRHS.Concentration.basis_inner_square
#print axioms DGRHS.Concentration.basis_outer_square_sum
#print axioms DGRHS.Concentration.covariance_radius_bounded
lemma bounded_basis_outer (b : OrthonormalBasis ι ℝ H)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → H} {B : ℝ}
    (hY : AEStronglyMeasurable Y μ) (hB : ∀ᵐ x ∂μ, ‖Y x‖ ≤ B) (p : ι × ι) :
    AEStronglyMeasurable (fun x ↦ inner ℝ (b p.1) (Y x)*inner ℝ (b p.2) (Y x)) μ ∧
    ∀ᵐ x ∂μ, |inner ℝ (b p.1) (Y x)*inner ℝ (b p.2) (Y x)| ≤ B^2 := by
  refine ⟨((by fun_prop : Continuous (fun z : H ↦ inner ℝ (b p.1) z)).comp_aestronglyMeasurable hY).mul
    ((by fun_prop : Continuous (fun z : H ↦ inner ℝ (b p.2) z)).comp_aestronglyMeasurable hY), ?_⟩
  filter_upwards [hB] with x hx
  have ha : |inner ℝ (b p.1) (Y x)| ≤ B := (abs_real_inner_le_norm _ _).trans (by simpa using hx)
  have hc : |inner ℝ (b p.2) (Y x)| ≤ B := (abs_real_inner_le_norm _ _).trans (by simpa using hx)
  rw [abs_mul,pow_two]
  exact mul_le_mul ha hc (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma covariance_radius_square_integral_le (b : OrthonormalBasis ι ℝ H)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) :
    (∫ ω, (covarianceRadius b μ Z ω)^2 ∂Measure.pi μ) ≤
      B^2*(∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) := by
  let X := fun (i : Fin n) (p : ι × ι) (x : Ω) ↦ inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x)
  have hx := fun i p ↦ bounded_basis_outer b (hZ i) (hB i) p
  have hXI : ∀ i p, Integrable (fun x ↦ (X i p x)^2) (μ i) := fun i p ↦
    integrable_of_ae_abs_le (bounded_square (hx i p).1 (hx i p).2).1 (bounded_square (hx i p).1 (hx i p).2).2
  have hd := fun p ↦ covariance_remainder_bounded b μ Z B hZ hB p
  have hdI : ∀ p, Integrable (fun ω ↦ (covarianceRemainder b μ Z ω p)^2) (Measure.pi μ) := fun p ↦
    integrable_of_ae_abs_le (bounded_square (hd p).1 (hd p).2).1 (bounded_square (hd p).1 (hd p).2).2
  have hpowI : ∀ i, Integrable (fun x ↦ ‖Z i x‖^4) (μ i) := by
    intro i
    have hs := bounded_square (hZ i).norm ((hB i).mono fun x hx ↦ by simpa using hx)
    have hs' := bounded_square hs.1 hs.2
    simpa only [← pow_mul] using integrable_of_ae_abs_le hs'.1 hs'.2
  have htwoI : ∀ i, Integrable (fun x ↦ ‖Z i x‖^2) (μ i) := fun i ↦
    integrable_of_ae_abs_le (bounded_square (hZ i).norm ((hB i).mono fun x hx ↦ by simpa using hx)).1
      (bounded_square (hZ i).norm ((hB i).mono fun x hx ↦ by simpa using hx)).2
  calc
    _ = ∫ ω, ∑ p, (covarianceRemainder b μ Z ω p)^2 ∂Measure.pi μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ Real.sq_sqrt (Finset.sum_nonneg fun p _ ↦ sq_nonneg _)
    _ = ∑ p, ∫ ω, (covarianceRemainder b μ Z ω p)^2 ∂Measure.pi μ := integral_finsetSum _ (fun p _ ↦ hdI p)
    _ ≤ ∑ p : ι × ι, ∑ i, ∫ x, (X i p x)^2 ∂μ i := Finset.sum_le_sum fun p _ ↦
      centered_product_sum_square_le μ (fun i ↦ X i p) (B^2) (fun i ↦ (hx i p).1) (fun i ↦ (hx i p).2)
    _ = ∑ i, ∫ x, ‖Z i x‖^4 ∂μ i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_finsetSum _ (fun p _ ↦ hXI i p)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ basis_outer_square_sum b (Z i x)
    _ ≤ ∑ i, B^2*(∫ x, ‖Z i x‖^2 ∂μ i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← integral_const_mul]
      apply integral_mono_ae (hpowI i) ((htwoI i).const_mul _)
      filter_upwards [hB i] with x hx
      have hsq : ‖Z i x‖^2 ≤ B^2 := by nlinarith [norm_nonneg (Z i x)]
      have hp := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖Z i x‖)
      nlinarith
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma covariance_directional_identity (b : OrthonormalBasis ι ℝ H)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : Fin n → Ω → H) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) (ω : Fin n → Ω) (u : H) :
    empiricalDirectionalSquare (fun i ↦ Z i (ω i)) u =
      (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i)+
      ∑ p : ι × ι, covarianceRemainder b μ Z ω p*(inner ℝ (b p.1) u*inner ℝ (b p.2) u) := by
  let X := fun (i : Fin n) (p : ι × ι) (x : Ω) ↦ inner ℝ (b p.1) (Z i x)*inner ℝ (b p.2) (Z i x)
  let c := fun p : ι × ι ↦ inner ℝ (b p.1) u*inner ℝ (b p.2) u
  have hi : ∀ i p, Integrable (X i p) (μ i) := fun i p ↦
    integrable_of_ae_abs_le (bounded_basis_outer b (hZ i) (hB i) p).1 (bounded_basis_outer b (hZ i) (hB i) p).2
  have he : ∀ i, (∫ x, (inner ℝ u (Z i x))^2 ∂μ i) = ∑ p, (∫ x, X i p x ∂μ i)*c p := by
    intro i
    calc
      _ = ∫ x, ∑ p, X i p x*c p ∂μ i := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          dsimp only
          rw [real_inner_comm (Z i x) u]
          exact basis_inner_square b (Z i x) u
      _ = _ := by
        rw [integral_finsetSum _ (fun p _ ↦ (hi i p).mul_const (c p))]
        simp only [integral_mul_const]
  simp_rw [he]
  unfold empiricalDirectionalSquare
  simp_rw [basis_inner_square b]
  change (∑ i, ∑ p, X i p (ω i)*c p) =
    (∑ i, ∑ p, (∫ x, X i p x ∂μ i)*c p)+
    ∑ p, (∑ i, (X i p (ω i)-∫ x, X i p x ∂μ i))*c p
  simp_rw [Finset.sum_mul,sub_mul,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i p ↦ X i p (ω i)*c p),
    Finset.sum_comm (f := fun i p ↦ (∫ x, X i p x ∂μ i)*c p)]
  ring

lemma empirical_quadratic_le_covariance_radius (b : OrthonormalBasis ι ℝ H)
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (Z : Fin n → Ω → H) (B D : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (ω : Fin n → Ω) : empiricalQuadraticOnProduct Z ω ≤ D^2+covarianceRadius b μ Z ω := by
  apply csSup_le (empirical_quadratic_image_nonempty _)
  rintro _ ⟨u,hu,rfl⟩
  have hu' : ‖u‖ ≤ 1 := by simpa using hu
  rw [covariance_directional_identity b μ Z B hZ hB ω u]
  apply add_le_add (hWeak u hu')
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (covarianceRemainder b μ Z ω) (fun p : ι × ι ↦ inner ℝ (b p.1) u*inner ℝ (b p.2) u)
  rw [basis_outer_square_sum b u] at hh
  have hs : 0 ≤ ∑ p, (covarianceRemainder b μ Z ω p)^2 := Finset.sum_nonneg fun p _ ↦ sq_nonneg _
  have hnorm : ‖u‖^4 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ)^4 := by gcongr
      _ = 1 := by norm_num
  have hp := mul_le_mul_of_nonneg_left hnorm hs
  have hr := Real.sq_sqrt hs
  have hn := Real.sqrt_nonneg (∑ p, (covarianceRemainder b μ Z ω p)^2)
  unfold covarianceRadius
  nlinarith

omit [Fintype ι] in
/-- H6 from actual matrix-entry independence, with the Euclidean/Frobenius square sum. -/
theorem empirical_quadratic_expectation_le [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B C D : ℝ) (hBpos : 0 ≤ B) (hCpos : 0 ≤ C)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hTrace : (∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) ≤ C^2)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2) :
    (∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ) ≤ D^2+B*C := by
  let b := stdOrthonormalBasis ℝ H
  obtain ⟨K,hR,hRb⟩ := covariance_radius_bounded b μ Z B hZ hB
  have hRI := integrable_of_ae_abs_le hR hRb
  have hRI2 := bounded_real_memLp hR hRb 2
  have hsq := covariance_radius_square_integral_le b μ Z B hZ hB
  have hs := hsq.trans (mul_le_mul_of_nonneg_left hTrace (sq_nonneg B))
  have hv := variance_nonneg (covarianceRadius b μ Z) (Measure.pi μ)
  rw [variance_eq_sub hRI2] at hv
  simp only [Pi.pow_apply] at hv
  have hm : 0 ≤ ∫ ω, covarianceRadius b μ Z ω ∂Measure.pi μ := integral_nonneg fun _ ↦ Real.sqrt_nonneg _
  have hmean : (∫ ω, covarianceRadius b μ Z ω ∂Measure.pi μ) ≤ B*C := by
    have hb : 0 ≤ B*C := mul_nonneg hBpos hCpos
    nlinarith
  have hV := empirical_quadratic_product_aestronglyMeasurable μ Z hZ
  have hVb := empirical_quadratic_product_bounded μ Z B hB
  have he := integral_mono (integrable_of_ae_abs_le hV hVb)
    ((integrable_const (D^2)).add hRI) (fun ω ↦ empirical_quadratic_le_covariance_radius b μ Z B D hZ hB hWeak ω)
  change (∫ ω, empiricalQuadraticOnProduct Z ω ∂Measure.pi μ) ≤ (∫ ω, D^2+covarianceRadius b μ Z ω ∂Measure.pi μ) at he
  have hh : (∫ ω, D^2+covarianceRadius b μ Z ω ∂Measure.pi μ) = D^2+∫ ω, covarianceRadius b μ Z ω ∂Measure.pi μ := by
    simpa using integral_add (integrable_const (D^2)) hRI
  rw [hh] at he
  exact he.trans (add_le_add le_rfl hmean)

#print axioms DGRHS.Concentration.covariance_radius_square_integral_le
#print axioms DGRHS.Concentration.covariance_directional_identity
#print axioms DGRHS.Concentration.empirical_quadratic_expectation_le
#check @DGRHS.Concentration.empirical_quadratic_expectation_le

end DGRHS.Concentration
