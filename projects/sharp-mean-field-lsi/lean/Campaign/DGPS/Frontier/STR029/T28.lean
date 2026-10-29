import DGPS.Frontier.STR029.T24
import DGPS.Frontier.STR029.T27

/-!
# STR029.28: Even rate and entropy expansions

Task STR029.28. The rate and chart entropy of the three actual variational branches have
fourth-order errors on one symmetric field interval, with one constant for all branches.

## R5 notes

The angular rate is `1 + h^2 * Z j h 2`; entropy is `entropyChart_STR02949` at
`chartU_STR02924 ψ h (Z j h)`. The range graph is the variational graph of STR029.16.
The new main statement restates the STR029.23 data and gives explicit uniform inequalities,
including the zero field. These authored interfaces require correspondence review.

For entropy we differentiate the reduced functional in the rate coordinate. Its graph
derivative pairs to zero with the variational gradient because it lies in the complementary
space. Thus entropy is `h^2` times a smooth scalar function with value one at zero. The sign
symmetry of STR029.27 makes this scalar even, and a quadratic remainder gives the requested
fourth-order error. This alternative to the fourth derivative of entropy uses the actual chart
branch, not an explicit quadratic trial function. The finite minimum of radii and maximum of
bounds preserves uniformity over all three branches and both field signs.

Identification with the optimal physical rate requires the absolute-domain identity of
STR029.01 and the global classification of STR029.26; chart expansions alone do not assert
that identification. The physical multiplication is assembled by the closing theorem.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

/-- A derivative bound: if `s'(0) = 0` and `|s''| ≤ K` on `[-d, d]`, then `|s'(x)| ≤ K |x|`. -/
theorem deriv_abs_le_STR02928 {s1 s2 : ℝ → ℝ} {d K : ℝ} (hd : 0 < d)
    (hs1 : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s1 (s2 x) x)
    (hs2 : ∀ x ∈ Set.Icc (-d) d, |s2 x| ≤ K) (hs10 : s1 0 = 0) :
    ∀ x ∈ Set.Icc (-d) d, |s1 x| ≤ K * |x| := by
  intro x hx
  have h0 : (0 : ℝ) ∈ Set.Icc (-d) d := ⟨by linarith, hd.le⟩
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (-d) d) (f := s1) (C := K)
    (fun y hy => (hs1 y hy).differentiableAt)
    (fun y hy => by rw [(hs1 y hy).deriv, Real.norm_eq_abs]; exact hs2 y hy)
    (convex_Icc (-d) d) h0 hx
  simpa [hs10, Real.norm_eq_abs] using key

/-- The one-sided quadratic estimate on `[0, d]`: `s x - s 0 ≤ K x^2 / 2`. -/
theorem quad_half_STR02928 {s s1 s2 : ℝ → ℝ} {d K : ℝ} (hd : 0 < d)
    (hs : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s (s1 x) x)
    (hs1 : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s1 (s2 x) x)
    (hs2 : ∀ x ∈ Set.Icc (-d) d, |s2 x| ≤ K) (hs10 : s1 0 = 0) :
    ∀ x ∈ Set.Icc 0 d, s x - s 0 ≤ K * x ^ 2 / 2 := by
  have hsub : Set.Icc (0 : ℝ) d ⊆ Set.Icc (-d) d := Set.Icc_subset_Icc (by linarith) le_rfl
  have hb := deriv_abs_le_STR02928 hd hs1 hs2 hs10
  have hφ : ∀ y ∈ Set.Icc (-d) d, HasDerivAt (fun y => K * y ^ 2 / 2 - (s y - s 0))
      (K * y - s1 y) y := by
    intro y hy
    have h1 := ((hasDerivAt_pow 2 y).const_mul K).div_const 2
    have h2 : HasDerivAt (fun y => s y - s 0) (s1 y) y := (hs y hy).sub_const (s 0)
    exact (h1.sub h2).congr_deriv (by norm_num; ring)
  have hmono : MonotoneOn (fun y => K * y ^ 2 / 2 - (s y - s 0)) (Set.Icc 0 d) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 d) ?_ ?_ ?_
    · intro y hy
      exact (hφ y (hsub hy)).continuousAt.continuousWithinAt
    · intro y hy
      exact (hφ y (hsub (interior_subset hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' := interior_subset hy
      have hy0 : 0 ≤ y := hy'.1
      rw [(hφ y (hsub hy')).deriv]
      have hbY := hb y (hsub hy')
      rw [abs_of_nonneg hy0] at hbY
      linarith [le_abs_self (s1 y)]
  intro x hx
  have h0 : (0 : ℝ) ∈ Set.Icc 0 d := ⟨le_rfl, hd.le⟩
  have hm := hmono h0 hx hx.1
  have e0 : K * (0 : ℝ) ^ 2 / 2 - (s 0 - s 0) = 0 := by ring
  change K * (0 : ℝ) ^ 2 / 2 - (s 0 - s 0) ≤ K * x ^ 2 / 2 - (s x - s 0) at hm
  linarith

/-- The quadratic bound `|s x - s 0| ≤ K x^2 / 2` on `[-d, d]` for an even `s` with `s'(0) = 0`
and `|s''| ≤ K` there. -/
theorem quad_bound_of_even_STR02928 {s s1 s2 : ℝ → ℝ} {d K : ℝ} (hd : 0 < d)
    (hs : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s (s1 x) x)
    (hs1 : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s1 (s2 x) x)
    (hs2 : ∀ x ∈ Set.Icc (-d) d, |s2 x| ≤ K) (hs10 : s1 0 = 0)
    (heven : ∀ x ∈ Set.Icc (-d) d, s (-x) = s x) :
    ∀ x ∈ Set.Icc (-d) d, |s x - s 0| ≤ K * x ^ 2 / 2 := by
  have hup := quad_half_STR02928 hd hs hs1 hs2 hs10
  have hlo := quad_half_STR02928 (s := fun x => -s x) (s1 := fun x => -s1 x)
    (s2 := fun x => -s2 x) hd (fun x hx => (hs x hx).neg) (fun x hx => (hs1 x hx).neg)
    (fun x hx => by simpa using hs2 x hx) (by simp [hs10])
  intro x hx
  rcases le_total 0 x with h0 | h0
  · have hxI : x ∈ Set.Icc 0 d := ⟨h0, hx.2⟩
    have u : s x - s 0 ≤ K * x ^ 2 / 2 := hup x hxI
    have l : -s x - -s 0 ≤ K * x ^ 2 / 2 := hlo x hxI
    rw [abs_le]
    constructor <;> linarith
  · have hxI : -x ∈ Set.Icc 0 d := ⟨by linarith, by linarith [hx.1]⟩
    have u : s (-x) - s 0 ≤ K * (-x) ^ 2 / 2 := hup (-x) hxI
    have l : -s (-x) - -s 0 ≤ K * (-x) ^ 2 / 2 := hlo (-x) hxI
    rw [heven x hx] at u l
    rw [neg_sq] at u l
    rw [abs_le]
    constructor <;> linarith

/-- Scalar rate lemma. A function `s` smooth on `(-η, η)` and even on `(-δ, δ)` with `δ ≤ η`
satisfies `|s h - s 0| ≤ K h^2 / 2` on a symmetric interval `[-d, d]` with `0 < d < η`. -/
theorem quad_expansion_STR02928 {s : ℝ → ℝ} {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) (hδη : δ ≤ η)
    (hsC : ContDiffOn ℝ ∞ s (Set.Ioo (-η) η))
    (hseven : ∀ h ∈ Set.Ioo (-δ) δ, s (-h) = s h) :
    ∃ K d : ℝ, 0 < d ∧ d < η ∧ ∀ h ∈ Set.Icc (-d) d, |s h - s 0| ≤ K * h ^ 2 / 2 := by
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = min δ η / 2 := ⟨_, rfl⟩
  have hmin : 0 < min δ η := lt_min hδ hη
  have hd : 0 < d := by rw [hd_def]; exact half_pos hmin
  have hdδ : d < δ := by linarith [min_le_left δ η]
  have hdη : d < η := by linarith [min_le_right δ η]
  have hIη : Set.Icc (-d) d ⊆ Set.Ioo (-η) η :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hIδ : Set.Icc (-d) d ⊆ Set.Ioo (-δ) δ :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs2C : ContDiffOn ℝ 2 s (Set.Ioo (-η) η) := hsC.of_le (by norm_num)
  have hs1C : ContDiffOn ℝ 1 (deriv s) (Set.Ioo (-η) η) :=
    hs2C.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsd : ∀ x ∈ Set.Icc (-d) d, HasDerivAt s (deriv s x) x := fun x hx =>
    ((hs2C.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds (hIη hx))).hasDerivAt
  have hsd1 : ∀ x ∈ Set.Icc (-d) d, HasDerivAt (deriv s) (deriv (deriv s) x) x := fun x hx =>
    ((hs1C.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds (hIη hx))).hasDerivAt
  have hcont : ContinuousOn (deriv (deriv s)) (Set.Icc (-d) d) :=
    (hs1C.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hIη
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -d) (b := d)).exists_bound_of_continuousOn hcont
  have hs2 : ∀ x ∈ Set.Icc (-d) d, |deriv (deriv s) x| ≤ K := fun x hx => by
    rw [← Real.norm_eq_abs]; exact hK x hx
  have hs10 : deriv s 0 = 0 := by
    have hev : (fun x => s (-x)) =ᶠ[𝓝 0] s :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩) hseven
    have e1 : deriv (fun x => s (-x)) 0 = deriv s 0 := hev.deriv_eq
    have e2 : deriv (fun x => s (-x)) 0 = -deriv s (-0) := deriv_comp_neg s 0
    rw [neg_zero] at e2
    linarith
  refine ⟨K, d, hd, hdη, fun h hh => ?_⟩
  exact quad_bound_of_even_STR02928 hd hsd hsd1 hs2 hs10 (fun x hx => hseven x (hIδ hx)) h hh

/-- STR029.28, rate clause. Under the clauses of STR029.23 used here (the uniqueness clause on
`N j`, the neighbourhood `N 0` of `(2, 0, -16/15)`, the smoothness of `Z j`, the equality
`Z j h 2 = Z 0 h 2`) and the evenness `Z j (-h) = Z j h` of STR029.27 on some `(-δ, δ)` with
`δ ≤ η`, there are `C` and `δ' > 0` such that for `|h| < δ'` and every branch `j`,
`|(1 + h^2 Z j h 2) - (1 - 16 h^2/15)| ≤ C h^4`. -/
theorem str029_28_even_rate_entropy_expansions_rate
    {E : ℝ × (Fin 3 → ℝ) → ℝ} {η : ℝ} {N : Fin 3 → Set (Fin 3 → ℝ)}
    {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    (hzero : ∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (hη : 0 < η) (hn0 : N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ))
    (hZC : ∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η))
    (hKuniq : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
      Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h)
    (hZ2 : ∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2)
    (hEven : ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3, Z j (-h) = Z j h) :
    ∃ C : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
      |(1 + h ^ 2 * Z j h 2) - (1 - 16 * h ^ 2 / 15)| ≤ C * h ^ 4 := by
  obtain ⟨δ, hδ, hδη, hEv⟩ := hEven
  have hηmem : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hZ00 : Z 0 0 = ![2, 0, -16 / 15] := by
    have hK := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
    have hmem : (![2, 0, -16 / 15] : Fin 3 → ℝ) ∈ N 0 := mem_of_mem_nhds hn0
    exact ((hKuniq 0 0 hηmem _ hmem).mp hK).symm
  have hs0 : Z 0 0 2 = -16 / 15 := by simp [hZ00]
  have hsC : ContDiffOn ℝ ∞ (fun h => Z 0 h 2) (Set.Ioo (-η) η) :=
    contDiffOn_pi.mp (hZC 0) 2
  have hseven : ∀ h ∈ Set.Ioo (-δ) δ, (fun h => Z 0 h 2) (-h) = (fun h => Z 0 h 2) h :=
    fun h hh => congrFun (hEv h hh 0) 2
  obtain ⟨K, d, hd, hdη, hbd⟩ := quad_expansion_STR02928 hη hδ hδη hsC hseven
  refine ⟨K / 2, d, hd, fun h hh j => ?_⟩
  have hhI : h ∈ Set.Icc (-d) d := ⟨hh.1.le, hh.2.le⟩
  have hb : |Z 0 h 2 - Z 0 0 2| ≤ K * h ^ 2 / 2 := hbd h hhI
  rw [hs0] at hb
  have hZj : Z j h 2 = Z 0 h 2 :=
    hZ2 h ⟨by linarith [hh.1], by linarith [hh.2]⟩ j
  rw [hZj]
  have hexpr : 1 + h ^ 2 * Z 0 h 2 - (1 - 16 * h ^ 2 / 15) =
      h ^ 2 * (Z 0 h 2 - -16 / 15) := by ring
  rw [hexpr, abs_mul, abs_of_nonneg (sq_nonneg h)]
  calc h ^ 2 * |Z 0 h 2 - -16 / 15| ≤ h ^ 2 * (K * h ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg h)
    _ = K / 2 * h ^ 4 := by ring


/-- Entropy on the Banach carrier, obtained from the affine rate dependence of the deficit. -/
noncomputable def HC2_STR02928 (h : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  (JC2_STR02956 h 0 u - JC2_STR02956 h 1 u) / 2

theorem HC2_eq_STR02928 (h : ℝ) (u : PeriodicC2_STR02969) :
    HC2_STR02928 h u = entropyChart_STR02949 h u.val := by
  unfold HC2_STR02928
  rw [JC2_eq_STR02956, JC2_eq_STR02956]
  unfold Jchart_STR02950
  ring

theorem HC2_smooth_STR02928 (h : ℝ) : ContDiff ℝ ∞ (HC2_STR02928 h) :=
  ((JC2_smooth_STR02956 h 0).sub (JC2_smooth_STR02956 h 1)).div_const 2

/-- The envelope identity on the variational range graph. -/
theorem envelope_STR02928 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (a b h γ : ℝ) (hp : ((a, b, h, γ) : Par_STR02916) ∈ U) :
    HasDerivAt (fun x : ℝ => Fred_STR02956 ψ (a, b) (h, x))
      (-2 * entropyChart_STR02949 h
        (uT_STR02901 a b ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val)) γ := by
  let g : ℝ → E_STR02969 := fun x => ψ (a, b, h, x)
  have hg : DifferentiableAt ℝ g γ :=
    ((hψC.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).comp γ (by fun_prop)
  let D : E_STR02969 := deriv g γ
  let u : ℝ → PeriodicC2_STR02969 := fun x =>
    a • cosC2_STR02915 + b • sinC2_STR02915 + ((g x : E_STR02969) : PeriodicC2_STR02969)
  have hu : HasDerivAt u ((D : E_STR02969) : PeriodicC2_STR02969) γ := by
    exact (E_STR02969.subtypeL.hasFDerivAt.comp_hasDerivAt γ hg.hasDerivAt).const_add _
  have huval (x : ℝ) : (u x).val =
      uT_STR02901 a b ((ψ (a, b, h, x) : E_STR02969) : PeriodicC2_STR02969).val :=
    paramMap_val_STR02915 a b (g x)
  have hJ := (((JC2_smooth_STR02956 h γ).differentiable (by simp)) (u γ)).hasFDerivAt.comp_hasDerivAt γ hu
  have hJ0 : fderiv ℝ (JC2_STR02956 h γ) (u γ)
      ((D : E_STR02969) : PeriodicC2_STR02969) = 0 := by
    rw [fderiv_JC2_STR02924, huval]
    exact meanT_mul_inE_STR02924 (continuous_val_STR02924 _)
      (inE_of_mem_STR02924 D) (projP_gradG_zero_STR02924 hψV hR a b h γ hp)
  rw [hJ0] at hJ
  have hH := (((HC2_smooth_STR02928 h).differentiable (by simp)) (u γ)).hasFDerivAt.comp_hasDerivAt γ hu
  have hlin : HasDerivAt (fun x : ℝ => 2 * (x - γ)) 2 γ := by
    simpa using ((hasDerivAt_id γ).sub_const γ).const_mul 2
  have hd := hJ.sub (hlin.mul hH)
  have heq : (fun x : ℝ => JC2_STR02956 h γ (u x) - 2 * (x - γ) * HC2_STR02928 h (u x)) =
      (fun x : ℝ => Fred_STR02956 ψ (a, b) (h, x)) := by
    funext x
    rw [JC2_eq_STR02956, HC2_eq_STR02928, huval]
    unfold Fred_STR02956 Jchart_STR02950
    ring
  change HasDerivAt (fun x : ℝ => JC2_STR02956 h γ (u x) -
    2 * (x - γ) * HC2_STR02928 h (u x)) _ γ at hd
  rw [heq] at hd
  convert hd using 1
  simp only [Function.comp_apply, HC2_eq_STR02928, huval]
  ring

/-- The rate-coordinate slice of the scaled deficit determines the actual chart entropy. -/
theorem entropy_slice_STR02928 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} {O : Set (ℝ × (Fin 3 → ℝ))}
    {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U) (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h : ℝ) (hh : h ≠ 0) (z : Fin 3 → ℝ) (hz : (h, z) ∈ O)
    (hp : ((h * z 0, h * z 1, h, h ^ 2 * z 2) : Par_STR02916) ∈ U) :
    entropyChart_STR02949 h (chartU_STR02924 ψ h z) =
      h ^ 2 * (-1 / 2 * fderiv ℝ E (h, z) ((0 : ℝ), (Pi.single 2 1 : Fin 3 → ℝ))) := by
  let H := entropyChart_STR02949 h (chartU_STR02924 ψ h z)
  have hE : DifferentiableAt ℝ E (h, z) := diffAt_STR02923 hO hEC hz
  have hs : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) z :=
    hE.comp z (by fun_prop)
  have hF := envelope_STR02928 hU hψC hψV hR (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp
  have hl : HasDerivAt (fun s : ℝ => h ^ 2 * (z 2 + s)) (h ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (z 2)).const_mul (h ^ 2)
  have hd := (hF.comp_of_eq 0 hl (by ring)).div_const (h ^ 4)
  have hline : HasDerivAt
      (fun s : ℝ => E (h, z + s • (Pi.single 2 1 : Fin 3 → ℝ)))
      ((-2 * H) * h ^ 2 / h ^ 4) 0 := by
    refine hd.congr_of_eventuallyEq ?_
    have hc : Continuous (fun s : ℝ => (h, z + s • (Pi.single 2 1 : Fin 3 → ℝ))) := by fun_prop
    have hm : (fun s : ℝ => (h, z + s • (Pi.single 2 1 : Fin 3 → ℝ))) ⁻¹' O ∈ 𝓝 (0 : ℝ) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hz)
    filter_upwards [hm] with s hs'
    rw [hval h _ hs' hh]
    simp
  have he := fderiv_line_STR02922 _ z (Pi.single 2 1) _ hs hline
  rw [fderiv_slice_STR02923 E hE] at he
  change H = _
  rw [he]
  field_simp [hh]

/-- The entropy divided by the field squared, smoothly extended through zero. -/
noncomputable def entropyFactor_STR02928 (E : ℝ × (Fin 3 → ℝ) → ℝ)
    (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  -1 / 2 * fderiv ℝ E p ((0 : ℝ), (Pi.single 2 1 : Fin 3 → ℝ))

theorem entropyFactor_smooth_STR02928 {E : ℝ × (Fin 3 → ℝ) → ℝ}
    {O : Set (ℝ × (Fin 3 → ℝ))} (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O) :
    ContDiffOn ℝ ∞ (entropyFactor_STR02928 E) O :=
  contDiffOn_const.mul ((hEC.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const)

theorem entropyFactor_zero_STR02928 {E : ℝ × (Fin 3 → ℝ) → ℝ}
    {O : Set (ℝ × (Fin 3 → ℝ))} (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O)
    (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O)
    (hzero : ∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) (z : Fin 3 → ℝ) :
    entropyFactor_STR02928 E (0, z) = (z 0 ^ 2 + z 1 ^ 2) / 4 := by
  have hs : (fun w : Fin 3 → ℝ => E ((0 : ℝ), w)) = Vp_STR02922 :=
    funext fun w => (hzero w).trans (Vp_eq_STR02922 w)
  unfold entropyFactor_STR02928
  rw [← fderiv_slice_STR02923 E (diffAt_STR02923 hO hEC (hOmem z)), hs, fderiv_Vp_STR02922]
  simp
  ring

/-- A common quadratic bound for three smooth even scalar functions. -/
theorem quad_three_STR02928 {s : Fin 3 → ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hs : ∀ j, ContDiffOn ℝ ∞ (s j) (Set.Ioo (-η) η))
    (heven : ∀ h ∈ Set.Ioo (-η) η, ∀ j, s j (-h) = s j h) :
    ∃ C d : ℝ, 0 < d ∧ d ≤ η ∧
      ∀ h ∈ Set.Ioo (-d) d, ∀ j, |s j h - s j 0| ≤ C * h ^ 2 := by
  have hq : ∀ j : Fin 3, ∃ K d : ℝ, 0 < d ∧ d < η ∧
      ∀ h ∈ Set.Icc (-d) d, |s j h - s j 0| ≤ K * h ^ 2 / 2 :=
    fun j => quad_expansion_STR02928 hη hη le_rfl (hs j) (fun h hh => heven h hh j)
  choose K d hd hdη hb using hq
  let d' := min (d 0) (min (d 1) (d 2))
  let C := max (K 0 / 2) (max (K 1 / 2) (K 2 / 2))
  have hd' : 0 < d' := lt_min (hd 0) (lt_min (hd 1) (hd 2))
  have hdj : ∀ j : Fin 3, d' ≤ d j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hKj : ∀ j : Fin 3, K j / 2 ≤ C := by
    intro j
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, d', hd', (hdj 0).trans (hdη 0).le, ?_⟩
  intro h hh j
  have hm : h ∈ Set.Icc (-d j) (d j) :=
    ⟨by linarith [hh.1, hdj j], by linarith [hh.2, hdj j]⟩
  calc |s j h - s j 0| ≤ K j * h ^ 2 / 2 := hb j h hm
    _ = (K j / 2) * h ^ 2 := by ring
    _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_right (hKj j) (sq_nonneg h)

/-- The expansion for arbitrary data satisfying the clauses supplied by STR029.23. -/
theorem str029_28_even_rate_entropy_expansions_of_data
    {U : Set Par_STR02916} {V : Set E_STR02969} {ψ : Par_STR02916 → E_STR02969}
    {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ} {η : ℝ}
    {N : Fin 3 → Set (Fin 3 → ℝ)} {Z : Fin 3 → ℝ → (Fin 3 → ℝ)}
    (hUo : IsOpen U) (hU0 : (0 : Par_STR02916) ∈ U) (hVo : IsOpen V)
    (hV0 : (0 : E_STR02969) ∈ V) (hψC : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hOo : IsOpen O) (hOmem : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (hzero : ∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2))
    (hη : 0 < η) (hn0 : N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ))
    (hsym : ∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0)
    (hZC : ∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η))
    (hZN : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j)
    (hZrot : ∀ h ∈ Set.Ioo (-η) η,
      Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h))
    (hZ2 : ∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2)
    (hKuniq : ∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
      Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
        |(1 + h ^ 2 * Z j h 2) - (1 - 16 * h ^ 2 / 15)| ≤ C * h ^ 4 ∧
        |entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) - h ^ 2| ≤ C * h ^ 4 := by
  obtain ⟨δs, hδs, hδsη, hsymmetry⟩ :=
    str029_27_reflection_sign_symmetry_branches_of_data hUo hU0 hVo hV0 hR hOo hOmem hEC
      hval hzero hη hn0 hsym hZC hZN hKuniq
  have hEven : ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
      ∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3, Z j (-h) = Z j h :=
    ⟨δs, hδs, hδsη, fun h hh => (hsymmetry h hh).2.1⟩
  obtain ⟨Cr, dr, hdr, hr⟩ := str029_28_even_rate_entropy_expansions_rate
    hzero hη hn0 hZC hKuniq hZ2 hEven
  have hηmem : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hZcont : ∀ j, ContinuousAt (Z j) 0 :=
    fun j => (hZC j).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hηmem)
  have hZ00 : Z 0 0 = ![2, 0, -16 / 15] := by
    have hK := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
    exact ((hKuniq 0 0 hηmem _ (mem_of_mem_nhds hn0)).mp hK).symm
  have hrotsq : ∀ z : Fin 3 → ℝ,
      (rot_STR02923 z 0) ^ 2 + (rot_STR02923 z 1) ^ 2 = z 0 ^ 2 + z 1 ^ 2 :=
    fun z => sumsq_rot_STR02923 (z 0) (z 1)
  have hsq0 : ∀ j : Fin 3, (Z j 0 0) ^ 2 + (Z j 0 1) ^ 2 = 4 := by
    have h0 : (Z 0 0 0) ^ 2 + (Z 0 0 1) ^ 2 = 4 := by rw [hZ00]; norm_num
    have h1 : (Z 1 0 0) ^ 2 + (Z 1 0 1) ^ 2 = 4 := by
      rw [(hZrot 0 hηmem).1, hrotsq]; exact h0
    have h2 : (Z 2 0 0) ^ 2 + (Z 2 0 1) ^ 2 = 4 := by
      rw [(hZrot 0 hηmem).2, hrotsq]; exact h1
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ j : Fin 3,
      (h, Z j h) ∈ O ∧
      ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916) ∈ U := by
    rw [Filter.eventually_all]
    intro j
    have hz := hZcont j
    have hz0 : ContinuousAt (fun h => Z j h 0) 0 := (continuous_apply 0).continuousAt.comp hz
    have hz1 : ContinuousAt (fun h => Z j h 1) 0 := (continuous_apply 1).continuousAt.comp hz
    have hz2 : ContinuousAt (fun h => Z j h 2) 0 := (continuous_apply 2).continuousAt.comp hz
    refine Filter.Eventually.and ?_ ?_
    · exact (continuousAt_id.prodMk hz).preimage_mem_nhds (hOo.mem_nhds (hOmem (Z j 0)))
    · have hc : ContinuousAt (fun h : ℝ =>
          ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916)) 0 :=
        (continuousAt_id.mul hz0).prodMk ((continuousAt_id.mul hz1).prodMk
          (continuousAt_id.prodMk ((continuousAt_id.pow 2).mul hz2)))
      have hp0 : ((0 * Z j 0 0, 0 * Z j 0 1, (0 : ℝ), 0 ^ 2 * Z j 0 2) : Par_STR02916) ∈ U := by
        have hp0eq : ((0 * Z j 0 0, 0 * Z j 0 1, (0 : ℝ), 0 ^ 2 * Z j 0 2) : Par_STR02916) = 0 := by
          simp
        rw [hp0eq]
        exact hU0
      exact hc.preimage_mem_nhds (hUo.mem_nhds hp0)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  let e := min ε δs
  have he : 0 < e := lt_min hε hδs
  have heη : e ≤ η := (min_le_right ε δs).trans hδsη
  have hes : e ≤ δs := min_le_right ε δs
  have hsub : Set.Ioo (-e) e ⊆ Set.Ioo (-η) η :=
    fun h hh => ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hsubs : Set.Ioo (-e) e ⊆ Set.Ioo (-δs) δs :=
    fun h hh => ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hgood : ∀ h ∈ Set.Ioo (-e) e, ∀ j : Fin 3,
      (h, Z j h) ∈ O ∧
      ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916) ∈ U := by
    intro h hh
    apply hεP
    rw [Real.dist_eq, sub_zero, abs_lt]
    have heε : e ≤ ε := min_le_left ε δs
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  let G : Fin 3 → ℝ → ℝ := fun j h => entropyFactor_STR02928 E (h, Z j h)
  have hGC : ∀ j, ContDiffOn ℝ ∞ (G j) (Set.Ioo (-e) e) := by
    intro j
    exact (entropyFactor_smooth_STR02928 hOo hEC).comp
      (contDiffOn_id.prodMk ((hZC j).mono hsub)) (fun h hh => (hgood h hh j).1)
  have hG0 : ∀ j, G j 0 = 1 := by
    intro j
    change entropyFactor_STR02928 E (0, Z j 0) = 1
    rw [entropyFactor_zero_STR02928 hOo hEC hOmem hzero, hsq0 j]
    norm_num
  have hfactor : ∀ h ∈ Set.Ioo (-e) e, ∀ j : Fin 3,
      entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) = h ^ 2 * G j h := by
    intro h hh j
    by_cases h0 : h = 0
    · subst h
      rw [chart_zero_STR02924 hψ0]
      simp [entropyChart_STR02949, meanT_STR02901]
    · exact entropy_slice_STR02928 hUo hψC hψV hR hOo hEC hval h h0 (Z j h)
        (hgood h hh j).1 (hgood h hh j).2
  have hGeven : ∀ h ∈ Set.Ioo (-e) e, ∀ j : Fin 3, G j (-h) = G j h := by
    intro h hh j
    by_cases h0 : h = 0
    · simp [h0]
    have hnh : -h ∈ Set.Ioo (-e) e := ⟨by linarith [hh.2], by linarith [hh.1]⟩
    have hhH := (hsymmetry h (hsubs hh)).2.2.2 j
    change entropyChart_STR02949 (-h) (chartU_STR02924 ψ (-h) (Z j (-h))) =
      entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) at hhH
    rw [hfactor (-h) hnh j, hfactor h hh j, neg_sq] at hhH
    exact mul_left_cancel₀ (pow_ne_zero 2 h0) hhH
  obtain ⟨Ce, de, hde, hdee, hb⟩ := quad_three_STR02928 he hGC hGeven
  let d := min dr de
  have hd : 0 < d := lt_min hdr hde
  have hddr : d ≤ dr := min_le_left dr de
  have hdde : d ≤ de := min_le_right dr de
  have hdeη : d ≤ η := hdde.trans (hdee.trans heη)
  let C := max 0 (max Cr Ce)
  have hC0 : 0 ≤ C := le_max_left _ _
  have hCr : Cr ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCe : Ce ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨d, hd, hdeη, C, hC0, ?_⟩
  intro h hh j
  have hhr : h ∈ Set.Ioo (-dr) dr := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hhe : h ∈ Set.Ioo (-de) de := ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hhe' : h ∈ Set.Ioo (-e) e := ⟨by linarith [hhe.1], by linarith [hhe.2]⟩
  refine ⟨(hr h hhr j).trans (mul_le_mul_of_nonneg_right hCr (by positivity)), ?_⟩
  rw [hfactor h hhe' j]
  have hex : h ^ 2 * G j h - h ^ 2 = h ^ 2 * (G j h - G j 0) := by rw [hG0]; ring
  rw [hex, abs_mul, abs_of_nonneg (sq_nonneg h)]
  calc h ^ 2 * |G j h - G j 0| ≤ h ^ 2 * (Ce * h ^ 2) :=
        mul_le_mul_of_nonneg_left (hb h hhe j) (sq_nonneg h)
    _ = Ce * h ^ 4 := by ring
    _ ≤ C * h ^ 4 := mul_le_mul_of_nonneg_right hCe (by positivity)

/-- Uniform fourth-order rate and entropy expansions on the three variational branches. -/
theorem str029_28_even_rate_entropy_expansions :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧ ∃ C : ℝ, 0 ≤ C ∧
              ∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                |(1 + h ^ 2 * Z j h 2) - (1 - 16 * h ^ 2 / 15)| ≤ C * h ^ 4 ∧
                |entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) - h ^ 2| ≤ C * h ^ 4 := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq⟩ := str029_23_three_locally_unique_solution_branches
  exact ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, str029_28_even_rate_entropy_expansions_of_data hUo hU0 hVo hV0 hψC hψ0 hψV hR hOo
      hOmem hEC hval hzero hη hn0 hsym hZC hZN hZrot hZs hKuniq⟩

end DGPS.Frontier.STR029
