import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering
import DGPS.Structural.CircleDensityRatio
import DGPS.Variational.PositiveRankOne

/-! Genuine square-root distances control finite-family moments. The assigned
laws are actual absolute densities, with no species-count bound, weight lower
bound, competitor smoothness, or deficit-distance estimate assumed. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual Haar square-root L2 distance squared. -/
def rootDistanceSq (ρ σ : AbsoluteDensity 1) : ℝ :=
  ∫ x, (ρ.sqrt x - σ.sqrt x) ^ 2 ∂haar 1

theorem rootDistanceSq_nonneg (ρ σ : AbsoluteDensity 1) : 0 ≤ rootDistanceSq ρ σ :=
  integral_nonneg fun x => sq_nonneg _

/-- Hellinger control of every bounded continuous observable on the full absolute domain. -/
theorem absolute_moment_error_le_root_distance (ρ σ : AbsoluteDensity 1)
    {f : Torus 1 → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ x, |f x| ≤ B) :
    |(∫ x, f x ∂(densityMeasure ρ : Measure (Torus 1))) -
      (∫ x, f x ∂(densityMeasure σ : Measure (Torus 1)))| ≤
      2 * B * Real.sqrt (rootDistanceSq ρ σ) := by
  let du : Torus 1 → ℝ := fun x => ρ.sqrt x - σ.sqrt x
  let su : Torus 1 → ℝ := fun x => ρ.sqrt x + σ.sqrt x
  have hd : MemLp du 2 (haar 1) := ρ.memLp_sqrt.sub σ.memLp_sqrt
  have hs : MemLp su 2 (haar 1) := ρ.memLp_sqrt.add σ.memLp_sqrt
  have hda : MemLp (fun x => |du x|) 2 (haar 1) := by
    simpa only [Real.norm_eq_abs] using hd.norm
  have hsa : MemLp (fun x => |su x|) 2 (haar 1) := by
    simpa only [Real.norm_eq_abs] using hs.norm
  have hiρ : Integrable (fun x => ρ.density x * f x) (haar 1) :=
    ρ.integrable_density.mul_bdd hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfB x)
  have hiσ : Integrable (fun x => σ.density x * f x) (haar 1) :=
    σ.integrable_density.mul_bdd hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hfB x)
  have hab : Integrable (fun x => |du x| * |su x|) (haar 1) := hda.integrable_mul hsa
  have hsum : ∫ x, su x ^ 2 ∂haar 1 ≤ 4 := by
    have hi2 : Integrable (fun x => 2 * ρ.sqrt x ^ 2 + 2 * σ.sqrt x ^ 2) (haar 1) :=
      (ρ.memLp_sqrt.integrable_sq.const_mul (2 : ℝ)).add
        (σ.memLp_sqrt.integrable_sq.const_mul (2 : ℝ))
    have hmono : (∫ x, su x ^ 2 ∂haar 1) ≤
        ∫ x, 2 * ρ.sqrt x ^ 2 + 2 * σ.sqrt x ^ 2 ∂haar 1 := by
      apply integral_mono hs.integrable_sq hi2
      intro x
      dsimp only [su]
      nlinarith [sq_nonneg (ρ.sqrt x - σ.sqrt x)]
    have hval : (∫ x, 2 * ρ.sqrt x ^ 2 + 2 * σ.sqrt x ^ 2 ∂haar 1) = 4 := by
      rw [integral_add (ρ.memLp_sqrt.integrable_sq.const_mul (2 : ℝ))
        (σ.memLp_sqrt.integrable_sq.const_mul (2 : ℝ)), integral_const_mul,
        integral_const_mul, ρ.mass_one, σ.mass_one]
      norm_num
    exact hmono.trans_eq hval
  have hsqrt : Real.sqrt (∫ x, su x ^ 2 ∂haar 1) ≤ 2 := by
    have hh := Real.sqrt_le_sqrt hsum
    norm_num at hh
    exact hh
  have hcs := Structural.integral_mul_le_sqrt_mul_sqrt
    (μ := haar 1) (f := fun x => |du x|) (h := fun x => |su x|)
    (fun x => abs_nonneg _) (fun x => abs_nonneg _) hda hsa
  simp only [sq_abs] at hcs
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
    ← integral_sub hiρ hiσ]
  have he : (fun x => ρ.density x * f x - σ.density x * f x) =
      fun x => du x * su x * f x := by
    funext x
    dsimp only [du, su, AbsoluteDensity.density]
    ring
  rw [he]
  calc _ ≤ ∫ x, |du x * su x * f x| ∂haar 1 := abs_integral_le_integral_abs
    _ ≤ ∫ x, B * (|du x| * |su x|) ∂haar 1 := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) (hab.const_mul B)
      exact Eventually.of_forall fun x => by
        change |du x * su x * f x| ≤ B * (|du x| * |su x|)
        rw [abs_mul, abs_mul]
        calc |du x| * |su x| * |f x| ≤ |du x| * |su x| * B :=
            mul_le_mul_of_nonneg_left (hfB x) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by ring
    _ = B * ∫ x, |du x| * |su x| ∂haar 1 := integral_const_mul _ _
    _ ≤ B * (Real.sqrt (∫ x, du x ^ 2 ∂haar 1) * Real.sqrt (∫ x, su x ^ 2 ∂haar 1)) :=
      mul_le_mul_of_nonneg_left hcs hB
    _ ≤ B * (Real.sqrt (∫ x, du x ^ 2 ∂haar 1) * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) hB
    _ = _ := by dsimp only [du, rootDistanceSq]; ring

/-- Replace each species by one of four actual assigned laws, retaining its weight. -/
def assignedRootFamily (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) : SpeciesFamily 1 where
  count := F.count
  weight := F.weight
  weight_pos := F.weight_pos
  weight_sum := F.weight_sum
  density := fun s => R (label s)

/-- The genuine averaged square-root distance, never a deficit surrogate. -/
def rootDistanceBudget (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) : ℝ :=
  ∑ s, F.weight s * rootDistanceSq (F.density s) (R (label s))

theorem rootDistanceBudget_nonneg (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) : 0 ≤ rootDistanceBudget F R label :=
  Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (rootDistanceSq_nonneg _ _)

private theorem weighted_root_distance (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) :
    (∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) ≤
      Real.sqrt (rootDistanceBudget F R label) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin F.count))
    (fun s => Real.sqrt (F.weight s))
    (fun s => Real.sqrt (F.weight s) * Real.sqrt (rootDistanceSq (F.density s) (R (label s))))
  have hleft : (∑ s, Real.sqrt (F.weight s) *
      (Real.sqrt (F.weight s) * Real.sqrt (rootDistanceSq (F.density s) (R (label s))))) =
      ∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s))) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [← mul_assoc, ← sq, Real.sq_sqrt (F.weight_nonneg s)]
  have h1 : (∑ s, Real.sqrt (F.weight s) ^ 2) = 1 := by
    calc _ = ∑ s, F.weight s := Finset.sum_congr rfl fun s _ => Real.sq_sqrt (F.weight_nonneg s)
      _ = 1 := F.weight_sum
  have h2 : (∑ s, (Real.sqrt (F.weight s) *
      Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) ^ 2) = rootDistanceBudget F R label := by
    unfold rootDistanceBudget
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (F.weight_nonneg s), Real.sq_sqrt (rootDistanceSq_nonneg _ _)]
  rw [hleft, h1, h2] at hcs
  simpa using hcs

/-- Uniform finite-family moment transfer from the genuine averaged distances. -/
theorem family_moment_error_le_root_budget (F : SpeciesFamily 1)
    (R : Fin 4 → AbsoluteDensity 1) (label : Fin F.count → Fin 4)
    {f : Torus 1 → ℝ} (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ x, |f x| ≤ B) :
    |(∫ x, f x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
      (∫ x, f x ∂(densityMeasure (barycenter (assignedRootFamily F R label)) : Measure (Torus 1)))| ≤
      2 * B * Real.sqrt (rootDistanceBudget F R label) := by
  rw [Structural.budget_integral_barycenter F hf,
    Structural.budget_integral_barycenter (assignedRootFamily F R label) hf]
  change |(∑ s, F.weight s * ∫ x, f x ∂(densityMeasure (F.density s) : Measure (Torus 1))) -
    (∑ s, F.weight s * ∫ x, f x ∂(densityMeasure (R (label s)) : Measure (Torus 1)))| ≤ _
  rw [← Finset.sum_sub_distrib]
  have hterm (s : Fin F.count) :
      |F.weight s * (∫ x, f x ∂(densityMeasure (F.density s) : Measure (Torus 1))) -
        F.weight s * (∫ x, f x ∂(densityMeasure (R (label s)) : Measure (Torus 1)))| ≤
      2 * B * (F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) := by
    rw [← mul_sub, abs_mul, abs_of_pos (F.weight_pos s)]
    have hh := mul_le_mul_of_nonneg_left
      (absolute_moment_error_le_root_distance (F.density s) (R (label s)) hf hB hfB) (F.weight_nonneg s)
    convert hh using 1 <;> ring
  calc _ ≤ ∑ s, |F.weight s * (∫ x, f x ∂(densityMeasure (F.density s) : Measure (Torus 1))) -
        F.weight s * (∫ x, f x ∂(densityMeasure (R (label s)) : Measure (Torus 1)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, 2 * B * (F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) :=
      Finset.sum_le_sum fun s _ => hterm s
    _ = 2 * B * ∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s))) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_root_distance F R label) (by positivity)


/-- Total weight assigned to the three nonreference laws. -/
def nonreferenceRootWeight (F : SpeciesFamily 1) (label : Fin F.count → Fin 4) : ℝ :=
  ∑ s, if label s = 0 then 0 else F.weight s

theorem nonreferenceRootWeight_nonneg (F : SpeciesFamily 1) (label : Fin F.count → Fin 4) :
    0 ≤ nonreferenceRootWeight F label := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs
  · exact le_rfl
  · exact F.weight_nonneg s

/-- A centered reference observable sees only the total assigned nonreference weight. -/
theorem assigned_root_moment_bound (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) {f : Torus 1 → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B)
    (hzero : ∫ x, f x ∂(densityMeasure (R 0) : Measure (Torus 1)) = 0) :
    |∫ x, f x ∂(densityMeasure (barycenter (assignedRootFamily F R label)) : Measure (Torus 1))| ≤
      B * nonreferenceRootWeight F label := by
  have hr (j : Fin 4) : |∫ x, f x ∂(densityMeasure (R j) : Measure (Torus 1))| ≤ B := by
    calc _ ≤ ∫ x, |f x| ∂(densityMeasure (R j) : Measure (Torus 1)) := abs_integral_le_integral_abs
      _ ≤ ∫ _x, B ∂(densityMeasure (R j) : Measure (Torus 1)) := by
        apply integral_mono (hf.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (integrable_const _)
        exact hfB
      _ = B := by simp
  rw [Structural.budget_integral_barycenter (assignedRootFamily F R label) hf]
  change |∑ s, F.weight s * ∫ x, f x ∂(densityMeasure (R (label s)) : Measure (Torus 1))| ≤ _
  calc _ ≤ ∑ s, |F.weight s * ∫ x, f x ∂(densityMeasure (R (label s)) : Measure (Torus 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, B * (if label s = 0 then 0 else F.weight s) := by
      apply Finset.sum_le_sum
      intro s hs
      by_cases he : label s = 0
      · rw [he, hzero]
        simp
      · rw [if_neg he, abs_mul, abs_of_pos (F.weight_pos s)]
        exact (mul_le_mul_of_nonneg_left (hr (label s)) (F.weight_nonneg s)).trans_eq (mul_comm _ _)
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Actual feature moments and actual generator-feature moments are kept separately. -/
def elementarySixObservable (h : ℝ) : Fin 6 → Torus 1 → ℝ :=
  ![featureC h, featureS h, featureB h,
    elementaryFeatureGenerator h (featureC h), elementaryFeatureGenerator h (featureS h),
    elementaryFeatureGenerator h (featureB h)]

theorem continuous_elementarySixObservable (h : ℝ) (i : Fin 6) :
    Continuous (elementarySixObservable h i) := by
  fin_cases i
  · exact featureC_continuous h
  · exact featureS_continuous h
  · exact featureB_continuous h
  · exact continuous_elementaryFeatureGenerator h _ (smooth_featureC h)
  · exact continuous_elementaryFeatureGenerator h _ (smooth_featureS h)
  · exact continuous_elementaryFeatureGenerator h _ (smooth_featureB h)

theorem elementarySixObservable_reference_zero {h : ℝ} (hh : 0 < h) (i : Fin 6) :
    (∫ x, elementarySixObservable h i x ∂threefoldReference h) = 0 := by
  obtain ⟨hc, hs, hb, -⟩ := elementaryFeatures_centered_independent hh
  fin_cases i
  · exact hc
  · exact hs
  · exact hb
  · exact elementaryFeatureGenerator_reference_mean_zero h _ (smooth_featureC h)
  · exact elementaryFeatureGenerator_reference_mean_zero h _ (smooth_featureS h)
  · exact elementaryFeatureGenerator_reference_mean_zero h _ (smooth_featureB h)

private def sixCorrection (a : ℝ) (v : Fin 6 → ℝ) : ℝ :=
  2 * kAlpha * (v 0 * v 3 + v 1 * v 4) - 2 * kBeta * v 2 * v 5 -
    a * (kAlpha * (v 0 ^ 2 + v 1 ^ 2) - kBeta * v 2 ^ 2)

private theorem correction_vector (h a : ℝ) (τ : AbsoluteDensity 1) :
    elementaryC h a τ = sixCorrection a
      (fun i => ∫ x, elementarySixObservable h i x ∂(densityMeasure τ : Measure (Torus 1))) := by
  rw [elementaryC_moments]
  rfl

private theorem product_error {x y u v m e : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (hx : |x - u| ≤ e) (hy : |y - v| ≤ e) (hu : |u| ≤ m) (hv : |v| ≤ m) :
    |x * y - u * v| ≤ 2 * m * e + e ^ 2 := by
  have hh : x * y - u * v = u * (y - v) + v * (x - u) + (x - u) * (y - v) := by ring
  rw [hh]
  calc _ ≤ |u * (y - v)| + |v * (x - u)| + |(x - u) * (y - v)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |u| * |y - v| + |v| * |x - u| + |x - u| * |y - v| := by simp only [abs_mul]
    _ ≤ m * e + m * e + e * e := by gcongr
    _ = _ := by ring

private theorem sixCorrection_error (a : ℝ) (v w : Fin 6 → ℝ) {m e : ℝ}
    (hm : 0 ≤ m) (he : 0 ≤ e) (hd : ∀ i, |v i - w i| ≤ e) (hw : ∀ i, |w i| ≤ m) :
    |sixCorrection a v - sixCorrection a w| ≤
      (4 * |kAlpha| + 2 * |kBeta| + |a| * (2 * |kAlpha| + |kBeta|)) * (2 * m * e + e ^ 2) := by
  let L := 2 * m * e + e ^ 2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hp (i j : Fin 6) : |v i * v j - w i * w j| ≤ L :=
    product_error hm he (hd i) (hd j) (hw i) (hw j)
  have hs (i : Fin 6) : |v i ^ 2 - w i ^ 2| ≤ L := by simpa only [sq] using hp i i
  have hexp : sixCorrection a v - sixCorrection a w =
      2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4)) -
      2 * kBeta * (v 2 * v 5 - w 2 * w 5) -
      a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) - kBeta * (v 2 ^ 2 - w 2 ^ 2)) := by
    unfold sixCorrection
    ring
  rw [hexp]
  have h1 : |2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4))| ≤
      2 * |kAlpha| * (2 * L) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
    exact (abs_add_le _ _).trans (by linarith [hp 0 3, hp 1 4])
  have h2 : |2 * kBeta * (v 2 * v 5 - w 2 * w 5)| ≤ 2 * |kBeta| * L := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
    exact hp 2 5
  have h3 : |a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) -
      kBeta * (v 2 ^ 2 - w 2 ^ 2))| ≤ |a| * (|kAlpha| * (2 * L) + |kBeta| * L) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    calc _ ≤ |kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2))| +
          |kBeta * (v 2 ^ 2 - w 2 ^ 2)| := abs_sub _ _
      _ ≤ _ := by
        simp only [abs_mul]
        gcongr
        · exact (abs_add_le _ _).trans (by linarith [hs 0, hs 1])
        · exact hs 2
  calc _ ≤ |2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4))| +
        |2 * kBeta * (v 2 * v 5 - w 2 * w 5)| +
        |a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) - kBeta * (v 2 ^ 2 - w 2 ^ 2))| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 * |kAlpha| * (2 * L) + 2 * |kBeta| * L + |a| * (|kAlpha| * (2 * L) + |kBeta| * L) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by dsimp only [L]; ring

/-- Actual quadratic interaction error from the genuine assigned-root distances.
The constant is fixed before every finite family, assignment and root laws.
No estimate of the distance budget by an ordinary deficit is assumed. -/
theorem elementaryC_nearest_root_error {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
      (label : Fin F.count → Fin 4),
      (densityMeasure (R 0) : Measure (Torus 1)) = threefoldReference h →
      |elementaryC h a (barycenter F) - elementaryC h a (barycenter (assignedRootFamily F R label))| ≤
        K * (nonreferenceRootWeight F label * Real.sqrt (rootDistanceBudget F R label) +
          rootDistanceBudget F R label) := by
  have hb (i : Fin 6) : ∃ B : ℝ, ∀ x, ‖elementarySixObservable h i x‖ ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_elementarySixObservable h i).continuousOn
    exact ⟨B, fun x => hB x (Set.mem_univ x)⟩
  choose B hB using hb
  let M := 1 + ∑ i : Fin 6, |B i|
  have hM : 0 < M := by dsimp only [M]; positivity
  have hbound (i : Fin 6) (x : Torus 1) : |elementarySixObservable h i x| ≤ M := by
    have hx : |elementarySixObservable h i x| ≤ B i := by simpa only [Real.norm_eq_abs] using hB i x
    have hs : |B i| ≤ ∑ j : Fin 6, |B j| :=
      Finset.single_le_sum (f := fun j : Fin 6 => |B j|)
        (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
    dsimp only [M]
    linarith [le_abs_self (B i)]
  let C := 4 * |kAlpha| + 2 * |kBeta| + |a| * (2 * |kAlpha| + |kBeta|)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨4 * M ^ 2 * (C + 1), by positivity, fun F R label hR => ?_⟩
  let d := rootDistanceBudget F R label
  let u0 := nonreferenceRootWeight F label
  let v : Fin 6 → ℝ := fun i => ∫ x, elementarySixObservable h i x
    ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let w : Fin 6 → ℝ := fun i => ∫ x, elementarySixObservable h i x
    ∂(densityMeasure (barycenter (assignedRootFamily F R label)) : Measure (Torus 1))
  have hd : 0 ≤ d := rootDistanceBudget_nonneg F R label
  have hu : 0 ≤ u0 := nonreferenceRootWeight_nonneg F label
  have herror (i : Fin 6) : |v i - w i| ≤ 2 * M * Real.sqrt d :=
    family_moment_error_le_root_budget F R label (continuous_elementarySixObservable h i) hM.le (hbound i)
  have hw (i : Fin 6) : |w i| ≤ M * u0 := by
    apply assigned_root_moment_bound F R label (continuous_elementarySixObservable h i) hM.le (hbound i)
    rw [hR]
    exact elementarySixObservable_reference_zero hh i
  have he := sixCorrection_error a v w (mul_nonneg hM.le hu) (by positivity) herror hw
  rw [correction_vector, correction_vector]
  change |sixCorrection a v - sixCorrection a w| ≤ _
  have hpoly : 2 * (M * u0) * (2 * M * Real.sqrt d) + (2 * M * Real.sqrt d) ^ 2 =
      4 * M ^ 2 * (u0 * Real.sqrt d + d) := by
    calc _ = 4 * M ^ 2 * (u0 * Real.sqrt d + (Real.sqrt d) ^ 2) := by ring
      _ = _ := by rw [Real.sq_sqrt hd]
  change |sixCorrection a v - sixCorrection a w| ≤ C *
    (2 * (M * u0) * (2 * M * Real.sqrt d) + (2 * M * Real.sqrt d) ^ 2) at he
  rw [hpoly] at he
  have hn : 0 ≤ u0 * Real.sqrt d + d := by positivity
  calc _ ≤ C * (4 * M ^ 2 * (u0 * Real.sqrt d + d)) := he
    _ ≤ 4 * M ^ 2 * (C + 1) * (u0 * Real.sqrt d + d) := by
      nlinarith [mul_nonneg (sq_nonneg M) hn]

end DGPS.Examples.ThreeSpeciesCircle
