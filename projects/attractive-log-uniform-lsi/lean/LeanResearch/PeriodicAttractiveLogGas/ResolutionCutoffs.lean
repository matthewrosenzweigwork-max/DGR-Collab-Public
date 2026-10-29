import LeanResearch.PeriodicAttractiveLogGas.OccupationMassCutoff
import LeanResearch.PeriodicAttractiveLogGas.SquaredLocalization

/-! The actual successive-resolution cutoffs in Theorem 7.5.
Support is proved from the sine/cosine factors, without monotonicity of the
smoothed occupations under refinement. All gradients are physical gradients. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.ResolutionCutoffs
open SmoothOccupations OccupationMassCutoff SquaredLocalization HeavyLocalization

def mesh (J m : ℕ) : ℕ := J ^ (m + 1)

theorem mesh_pos {J : ℕ} (hJ : 0 < J) (m : ℕ) : 0 < mesh J m := pow_pos hJ _
theorem base_le_mesh (J m : ℕ) : J ≤ mesh J m := Nat.le_pow (by omega)
theorem mesh_three {J : ℕ} (hJ : 3 ≤ J) (m : ℕ) : 3 ≤ mesh J m :=
  hJ.trans (base_le_mesh J m)
@[simp] theorem mesh_zero (J : ℕ) : mesh J 0 = J := by simp [mesh]
theorem mesh_succ (J m : ℕ) : mesh J (m + 1) = mesh J m * J := by
  simp only [mesh, pow_succ]

def angle (N J : ℕ) (hJ : 0 < J) (t : ℝ) : C(Configuration N, ℝ) :=
  (Real.pi / 2) • cutoffValue N J hJ (t / 4) (t / 2)

@[simp] theorem angle_apply (N J : ℕ) (hJ : 0 < J) (t : ℝ) (X : Configuration N) :
    angle N J hJ t X = Real.pi / 2 * cutoffValue N J hJ (t / 4) (t / 2) X := rfl

theorem scalar_lipschitz (c : ℝ) : LipschitzWith ‖c‖₊ (fun x : ℝ => c * x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |c * x - c * y| ≤ |c| * |x - y|
  rw [← mul_sub, abs_mul]

def angleLiftConstant (N J : ℕ) (t : ℝ) : ℝ≥0 :=
  ‖Real.pi / 2‖₊ * cutoffLiftConstant N J (t / 4) (t / 2)

theorem angle_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) :
    LipschitzWith (angleLiftConstant N J t)
      (fun y => angle N J (by omega) t (configurationQuotient N y)) :=
  (scalar_lipschitz (Real.pi / 2)).comp
    (cutoff_lift_lipschitz N J hN hJ (by linarith : t / 4 < t / 2))

theorem angle_eq_zero {N J : ℕ} (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    {X : Configuration N} (hX : maximumOccupation N J hJ X ≤ t / 4) :
    angle N J hJ t X = 0 := by
  rw [angle_apply, cutoff_eq_zero hJ (by linarith) hX, mul_zero]

theorem angle_eq_half_pi {N J : ℕ} (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    {X : Configuration N} (hX : t / 2 ≤ maximumOccupation N J hJ X) :
    angle N J hJ t X = Real.pi / 2 := by
  rw [angle_apply, cutoff_eq_one hJ (by linarith) hX, mul_one]

def angleConstant (t : ℝ) : ℝ := 288 * Real.pi ^ 2 / t ^ 2

theorem angleConstant_nonneg (t : ℝ) : 0 ≤ angleConstant t := by
  unfold angleConstant; positivity

theorem ae_angle_gradient (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      descendedLiftGradient (angle N J (by omega) t) X =
        (Real.pi / 2) • descendedLiftGradient (cutoffValue N J (by omega) (t / 4) (t / 2)) X := by
  have hh := ae_scalar_chain_rule (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
    (cutoffValue N J (by omega) (t / 4) (t / 2))
    (cutoff_lift_lipschitz N J hN hJ (by linarith : t / 4 < t / 2))
    (scalar_lipschitz (Real.pi / 2))
    (fun z => by simpa using (hasDerivAt_id z).const_mul (Real.pi / 2))
  exact hh

theorem ae_angle_gradient_sq_bound (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (β : ℝ) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      ‖descendedLiftGradient (angle N J (by omega) t) X‖ ^ 2 ≤
        (transitionRegion N J (by omega) (t / 4) (t / 2)).indicator
          (fun _ => angleConstant t * (J : ℝ) ^ 2 / N) X := by
  filter_upwards [ae_angle_gradient N J hN hJ ht β,
    ae_cutoff_gradient_sq_bound N J hN hJ (by linarith : t / 4 < t / 2) β] with X he hb
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  by_cases hX : X ∈ transitionRegion N J (by omega) (t / 4) (t / 2)
  · rw [Set.indicator_of_mem hX] at hb ⊢
    calc
      _ ≤ (Real.pi / 2) ^ 2 * (72 * (J : ℝ) ^ 2 / (N * (t / 2 - t / 4) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = _ := by
        unfold angleConstant
        have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp [ht.ne', hn]
        <;> ring
  · rw [Set.indicator_of_notMem hX] at hb ⊢
    simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb (sq_nonneg (Real.pi / 2))

def refinementAngle (N J : ℕ) (hJ : 0 < J) (t : ℝ) (m : ℕ) : C(Configuration N, ℝ) :=
  angle N (mesh J m) (mesh_pos hJ m) t

def remainder (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ)) :
    ℕ → C(Configuration N, ℝ)
  | 0 => f
  | m + 1 => sinMap (refinementAngle N J hJ t m) * remainder N J hJ t f m

def lightPiece (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ)) (m : ℕ) :
    C(Configuration N, ℝ) :=
  cosMap (refinementAngle N J hJ t m) * remainder N J hJ t f m

@[simp] theorem remainder_zero (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ)) :
    remainder N J hJ t f 0 = f := rfl

theorem remainder_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y => remainder N J (by omega) t f m (configurationQuotient N y)) := by
  induction m with
  | zero => exact ⟨K, hf⟩
  | succ m ih =>
    obtain ⟨L, hL⟩ := ih
    have ha := angle_lipschitz N (mesh J m) hN (mesh_three hJ m) ht
    have hs := sinMap_lipschitz (refinementAngle N J (by omega) t m) ha
    exact ⟨_, lipschitz_lift_mul _ _ hs hL⟩

theorem lightPiece_lipschitz (N J : ℕ) (hN : 0 < N) (hJ : 3 ≤ J)
    {t : ℝ} (ht : 0 < t) (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y => f (configurationQuotient N y))) (m : ℕ) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y => lightPiece N J (by omega) t f m (configurationQuotient N y)) := by
  obtain ⟨L, hL⟩ := remainder_lipschitz N J hN hJ ht f hf m
  have ha := angle_lipschitz N (mesh J m) hN (mesh_three hJ m) ht
  have hc := cosMap_lipschitz (refinementAngle N J (by omega) t m) ha
  exact ⟨_, lipschitz_lift_mul _ _ hc hL⟩

theorem square_split (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ))
    (m : ℕ) (X : Configuration N) :
    lightPiece N J hJ t f m X ^ 2 + remainder N J hJ t f (m + 1) X ^ 2 =
      remainder N J hJ t f m X ^ 2 :=
  square_partition (remainder N J hJ t f m) (refinementAngle N J hJ t m) X

theorem abs_remainder_le (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ))
    (m : ℕ) (X : Configuration N) : |remainder N J hJ t f m X| ≤ |f X| := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    change |Real.sin (refinementAngle N J hJ t m X) * remainder N J hJ t f m X| ≤ _
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (by simpa only [one_mul] using ih)

theorem abs_lightPiece_le (N J : ℕ) (hJ : 0 < J) (t : ℝ) (f : C(Configuration N, ℝ))
    (m : ℕ) (X : Configuration N) : |lightPiece N J hJ t f m X| ≤ |f X| := by
  change |Real.cos (refinementAngle N J hJ t m X) * remainder N J hJ t f m X| ≤ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using abs_remainder_le N J hJ t f m X)

theorem remainder_succ_zero_low (N J : ℕ) (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    (f : C(Configuration N, ℝ)) (m : ℕ) {X : Configuration N}
    (hX : maximumOccupation N (mesh J m) (mesh_pos hJ m) X ≤ t / 4) :
    remainder N J hJ t f (m + 1) X = 0 := by
  change Real.sin (angle N (mesh J m) (mesh_pos hJ m) t X) * _ = 0
  rw [angle_eq_zero (mesh_pos hJ m) ht hX, Real.sin_zero, zero_mul]

theorem lightPiece_zero_high (N J : ℕ) (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    (f : C(Configuration N, ℝ)) (m : ℕ) {X : Configuration N}
    (hX : t / 2 ≤ maximumOccupation N (mesh J m) (mesh_pos hJ m) X) :
    lightPiece N J hJ t f m X = 0 := by
  change Real.cos (angle N (mesh J m) (mesh_pos hJ m) t X) * _ = 0
  rw [angle_eq_half_pi (mesh_pos hJ m) ht hX, Real.cos_pi_div_two, zero_mul]

theorem lightPiece_succ_zero_low (N J : ℕ) (hJ : 0 < J) {t : ℝ} (ht : 0 < t)
    (f : C(Configuration N, ℝ)) (m : ℕ) {X : Configuration N}
    (hX : maximumOccupation N (mesh J m) (mesh_pos hJ m) X ≤ t / 4) :
    lightPiece N J hJ t f (m + 1) X = 0 := by
  change Real.cos _ * remainder N J hJ t f (m + 1) X = 0
  rw [remainder_succ_zero_low N J hJ ht f m hX, mul_zero]

theorem remainder_persistent_zero (N J : ℕ) (hJ : 0 < J) (t : ℝ)
    (f : C(Configuration N, ℝ)) {m : ℕ} {X : Configuration N}
    (hz : remainder N J hJ t f m X = 0) (k : ℕ) :
    remainder N J hJ t f (m + k) X = 0 := by
  induction k with
  | zero => simpa only [Nat.add_zero] using hz
  | succ k ih =>
    change Real.sin _ * remainder N J hJ t f (m + k) X = 0
    rw [ih, mul_zero]

theorem finite_square_decomposition (N J : ℕ) (hJ : 0 < J) (t : ℝ)
    (f : C(Configuration N, ℝ)) (M : ℕ) (X : Configuration N) :
    (∑ m ∈ Finset.range M, lightPiece N J hJ t f m X ^ 2) +
      remainder N J hJ t f M X ^ 2 = f X ^ 2 := by
  induction M with
  | zero => simp [remainder]
  | succ M ih => rw [Finset.sum_range_succ, add_assoc, square_split, ih]

end PeriodicAttractiveLogGas.ResolutionCutoffs
