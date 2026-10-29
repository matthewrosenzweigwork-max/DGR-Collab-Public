import DGPS.Frontier.STR029.T23

/-!
# STR029.24: Lift the reduced branches to full critical densities

Task id: STR029.24. Title: Lift the reduced branches to full critical densities. Node STR029.
Prerequisites: STR029.12 (mean of `G`), STR029.16 (the range map `ψ` and `Rpar_STR02916`),
STR029.17 and STR029.20 (the reduced function `E` and its extension), STR029.23 (the three
branches `Z j`, with the neighbourhoods `N j` and the uniqueness clause).

Provides:
* `DGPS.Frontier.STR029.str029_24_lift_reduced_branches_full_critical_densities`: the data of
  STR029.23 (`U, V, ψ, O, E, η, N, Z`, all its clauses restated) together with a radius
  `0 < δ ≤ η` such that, for every `h` with `|h| < δ` and every branch `j`, with
  `u_j = h A_j cos t + h B_j sin t + ψ(h A_j, h B_j, h, h² s_j)` (`(A_j, B_j, s_j) = Z j h`) and
  `ρ_j = ρ(h, u_j)`: `ρ_j > 0` everywhere; `G(h, h² s_j, u_j) = 0` pointwise; and, for `h ≠ 0`,
  the entropy of `ρ_j` is positive and `I_h / (2 H_h) = 1 + h² s_j`; for `h ≠ 0` the three densities
  `ρ_0, ρ_1, ρ_2` are pairwise distinct; at `h = 0` each `ρ_j` equals `q_0` and `G(0, 0, u_j) = 0`.
* `DGPS.Frontier.STR029.chartU_STR02924`: the log-chart function `u_j` of the specification, for a
  point `z = (A, B, s)` of the reduced slice.
* `DGPS.Frontier.STR029.lift_STR02924`: for `h ≠ 0`, a point `z` with `K(h, z) = 0`, and `1 + h² z₂`
  and `z₀² + z₁²` positive: `G = 0`, positive entropy, and quotient `1 + h² z₂`.
* `DGPS.Frontier.STR029.distinct_STR02924`: two chart densities with equal third coordinate and
  different points are different for `h ≠ 0`.
* `DGPS.Frontier.STR029.kfun_STR02924`: for `h ≠ 0`, the components of `Kfun_STR02923` are
  `h⁻³` times the cosine and sine pairings of `G`, and `J / h⁴`.
* `DGPS.Frontier.STR029.fderiv_Fred_STR02924`, `DGPS.Frontier.STR029.fderiv_slice_STR02924`,
  `DGPS.Frontier.STR029.fderiv_JC2_STR02924`: the amplitude derivatives of `Fred_STR02956` are the
  first-harmonic pairings of `G`; the slice derivatives of `E` are `h⁻⁴` times them; the derivative
  of `JC2_STR02956` is the pairing with `G`.
* `DGPS.Frontier.STR029.projP_gradG_zero_STR02924`: the range equation gives `P G = 0` pointwise.
* `DGPS.Frontier.STR029.meanT_mul_inE_STR02924`, `DGPS.Frontier.STR029.meanT_comb3_STR02924`,
  `DGPS.Frontier.STR029.meanT_uT_STR02924`: a function with zero complementary projection pairs to
  zero with every element of `E`; linearity of the mean on three continuous functions; the mean and
  first-harmonic pairings of `u = a cos t + b sin t + w` with `w` in `E`.
* `DGPS.Frontier.STR029.continuous_gradG_STR02924`, `DGPS.Frontier.STR029.chart_isC2_STR02924`,
  `DGPS.Frontier.STR029.chartU_isC2_STR02924`, `DGPS.Frontier.STR029.inE_of_mem_STR02924`,
  `DGPS.Frontier.STR029.continuous_val_STR02924`, `DGPS.Frontier.STR029.inE_zero_STR02924`:
  regularity and membership facts for the chart.
* `DGPS.Frontier.STR029.rho_eq_const_STR02924`, `DGPS.Frontier.STR029.coeff_eq_STR02924`:
  equal densities differ by a constant in the log chart; then the first Fourier coefficients agree.
* `DGPS.Frontier.STR029.exists_deriv_ne_STR02924`, `DGPS.Frontier.STR029.deriv_periodic_STR02924`,
  `DGPS.Frontier.STR029.fisher_pos_STR02924`: a chart with nonzero amplitude has positive Fisher
  information.
* `DGPS.Frontier.STR029.chart_zero_STR02924`, `DGPS.Frontier.STR029.rho_chart_zero_STR02924`,
  `DGPS.Frontier.STR029.gradG_chart_zero_STR02924`: at `h = 0` the chart is the zero function, its
  density is `q_0`, and `G` vanishes.

R5 notes:
1. Restated data. STR029.23 gives an existential statement, so the objects `ψ`, `E`, `N`, `Z`
   have to be named again. The main statement restates every clause of the conclusion of
   `str029_23_three_locally_unique_solution_branches` verbatim, and only then adds the new block
   about `δ`. No hypothesis is added; the new block is a conjunction of conclusions.
2. Draft dependency. The theorem of STR029.23 currently in the tree is a draft whose proof is a
   placeholder, so this file inherits that gap. Its statement, as restated, was usable as is.
3. Gap in the draft statement. It does not say that `(h, Z j h) ∈ O` nor that
   `(h Z_0, h Z_1, h, h² Z_2) ∈ U`. Both are proved here from the continuity of `Z j` at `h = 0`
   (the clause `(0, z) ∈ O`, openness of `O` and `U`, and `0 ∈ U`), so they hold only for small
   `|h|`. That is one of the reasons for the radius `δ`.
4. "Sufficiently small". It is read as `∃ δ, 0 < δ ∧ δ ≤ η` and the conclusions hold on
   `Set.Ioo (-δ) δ`, which lies inside the interval of definition of `Z`. `δ` is also used to
   keep `1 + h² s_j > 0` and `(A_j, B_j) ≠ (0, 0)`; both are obtained at `h = 0` and extended by
   continuity. At `h = 0`, `(A_j, B_j)` has squared norm `4`: `Z 0 0 = (2, 0, -16/15)` by the
   uniqueness clause and `Kmap_STR02922 E (2, 0, -16/15) = 0` of STR029.22, and the rotation
   `rot_STR02923` preserves `A² + B²`.
5. The chart. `chartU_STR02924 ψ h z` is `uT_STR02901 (h z₀) (h z₁) (ψ (h z₀, h z₁, h, h² z₂))`,
   the specification's `u_j` with `(A_j, B_j, s_j) = Z j h`; `ρ_j` is `rhoT_STR02901 h u_j`, and
   `r_j = 1 + h² s_j` is written `1 + h ^ 2 * Z j h 2`. `G` is `gradG_STR02950 h (h ^ 2 * s_j) u_j`.
6. Entropy and quotient. `H_h` and `I_h` are read as the chart formulas `entropyChart_STR02949`
   and `fisherChart_STR02949` of STR029.49, the same ones that enter `Jchart_STR02950`. The quotient
   is `I_h / (2 * H_h) = 1 + h² s_j`, stated for `h ≠ 0` together with `0 < H_h`.
7. Proof route for the entropy. Positivity of the entropy is not obtained from the asymptotic
   expansion `h² (A² + B²)/4`. It follows from `J = 0` (`J = I - 2 r H`), `I > 0` (Fisher
   information of a non-constant chart) and `r > 0`; the quotient identity is the same equation.
   The expansion is not stated.
8. Positivity. "Positive" for `ρ_j` means `0 < rhoT_STR02901 h u_j t` for every real `t`; it holds
   for every `h` in the radius, including `h = 0`.
9. The gradient equation. It is stated for every `h` in the radius with `γ = h² s_j`, so it covers
   `h = 0` where `γ = 0`; the `h = 0` clause repeats it in the form `G(0, 0, u_j) = 0` next to the
   identification of the density.
10. The case `h = 0`. "Their common density is `q_0`" is read as `rhoT_STR02901 0 u_j = qT_STR02901 0`
   as functions, for each `j`. Here `u_j` is the zero function because `ψ 0 = 0`.
11. Distinctness. It is the inequality of the functions `ρ_i ≠ ρ_j` for `i ≠ j` and `h ≠ 0`. It holds
   on the whole radius (no further smallness) because the first coordinates are determined by the
   first harmonics of `log ρ`, the third coordinate `s_j` is common to the branches, and the
   neighbourhoods `N j` are pairwise disjoint; the approach of the normalised coefficients to
   distinct points is not used.
12. The mean of `G`. It is taken from `str029_50_integrate_variation_compute_mean_mean_zero`, which
   proves the mean-zero property of the gradient expression.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

noncomputable def chartU_STR02924 (ψ : Par_STR02916 → E_STR02969) (h : ℝ) (z : Fin 3 → ℝ) :
    ℝ → ℝ :=
  uT_STR02901 (h * z 0) (h * z 1)
    ((ψ (h * z 0, h * z 1, h, h ^ 2 * z 2) : E_STR02969) : PeriodicC2_STR02969).val

theorem meanT_comb3_STR02924 {f₁ f₂ f₃ : ℝ → ℝ} (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃) (c₁ c₂ c₃ : ℝ) :
    meanT_STR02901 (fun t => c₁ * f₁ t + c₂ * f₂ t + c₃ * f₃ t) =
      c₁ * meanT_STR02901 f₁ + c₂ * meanT_STR02901 f₂ + c₃ * meanT_STR02901 f₃ := by
  have e : (fun t => c₁ * f₁ t + c₂ * f₂ t + c₃ * f₃ t) = (c₁ • f₁ + c₂ • f₂) + c₃ • f₃ := by
    funext t; simp
  rw [e, meanT_add_STR02953 ((h₁.const_smul c₁).add (h₂.const_smul c₂)) (h₃.const_smul c₃),
    meanT_add_STR02953 (h₁.const_smul c₁) (h₂.const_smul c₂), meanT_smul_STR02953,
    meanT_smul_STR02953, meanT_smul_STR02953]

theorem meanT_uT_STR02924 {w : ℝ → ℝ} (a b : ℝ) (hw : Continuous w) (hE : InE_STR02901 w) :
    meanT_STR02901 (uT_STR02901 a b w) = 0 ∧
    meanT_STR02901 (fun t => uT_STR02901 a b w t * Real.cos t) = a / 2 ∧
    meanT_STR02901 (fun t => uT_STR02901 a b w t * Real.sin t) = b / 2 := by
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  refine ⟨?_, ?_, ?_⟩
  · have e : uT_STR02901 a b w = fun t => a * Real.cos t + b * Real.sin t + 1 * w t := by
      funext t; simp [uT_STR02901]
    rw [e, meanT_comb3_STR02924 hc hs hw, meanT_cos_STR02955, meanT_sin_STR02955, hE.1]; ring
  · have e : (fun t => uT_STR02901 a b w t * Real.cos t) = fun t =>
        a * (Real.cos t * Real.cos t) + b * (Real.sin t * Real.cos t) + 1 * (w t * Real.cos t) := by
      funext t; simp only [uT_STR02901]; ring
    rw [e, meanT_comb3_STR02924 (f₁ := fun t => Real.cos t * Real.cos t)
      (f₂ := fun t => Real.sin t * Real.cos t) (f₃ := fun t => w t * Real.cos t)
      (hc.mul hc) (hs.mul hc) (hw.mul hc), meanT_cc_STR02955,
      meanT_sc_STR02955, hE.2.1]; ring
  · have e : (fun t => uT_STR02901 a b w t * Real.sin t) = fun t =>
        a * (Real.sin t * Real.cos t) + b * (Real.sin t * Real.sin t) + 1 * (w t * Real.sin t) := by
      funext t; simp only [uT_STR02901]; ring
    rw [e, meanT_comb3_STR02924 (f₁ := fun t => Real.sin t * Real.cos t)
      (f₂ := fun t => Real.sin t * Real.sin t) (f₃ := fun t => w t * Real.sin t)
      (hs.mul hc) (hs.mul hs) (hw.mul hs), meanT_ss_STR02955,
      meanT_sc_STR02955, hE.2.2]; ring

theorem fderiv_JC2_STR02924 (h γ : ℝ) (u v : PeriodicC2_STR02969) :
    fderiv ℝ (JC2_STR02956 h γ) u v =
      meanT_STR02901 (fun t => gradG_STR02950 h γ u.val t * v.val t) := by
  have hd : DifferentiableAt ℝ (JC2_STR02956 h γ) u :=
    ((JC2_smooth_STR02956 h γ).differentiable (by simp)) u
  have hline : HasDerivAt (fun s : ℝ => u + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have h1 : HasDerivAt (fun s : ℝ => JC2_STR02956 h γ (u + s • v))
      (fderiv ℝ (JC2_STR02956 h γ) u v) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have h2 := str029_50_integrate_variation_compute_mean_variation h γ u.isC2 v.isC2
  have hfun : (fun s : ℝ => JC2_STR02956 h γ (u + s • v)) = fun s : ℝ =>
      Jchart_STR02950 h γ (fun t => u.val t + s * v.val t) := by
    funext s
    rw [JC2_eq_STR02956]
    rfl
  rw [hfun] at h1
  exact h1.unique h2

theorem continuous_gradG_STR02924 (h γ : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    Continuous (gradG_STR02950 h γ u) := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hu1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hu2 : Continuous (deriv (deriv u)) := hu.2.2.2.1
  have hρ := continuous_rho_STR02950 h hu0
  unfold gradG_STR02950
  fun_prop

theorem meanT_mul_inE_STR02924 {G w : ℝ → ℝ} (hw : Continuous w) (hwE : InE_STR02901 w)
    (hP : ∀ t, projP_STR02953 G t = 0) : meanT_STR02901 (fun t => G t * w t) = 0 := by
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  have e : (fun t => G t * w t) = fun t =>
      meanT_STR02901 G * w t + (2 * pair_STR02953 Real.cos G) * (w t * Real.cos t) +
        (2 * pair_STR02953 Real.sin G) * (w t * Real.sin t) := by
    funext t
    have := hP t
    simp only [projP_STR02953] at this
    linear_combination (w t) * this
  rw [e, meanT_comb3_STR02924 (f₁ := w) (f₂ := fun t => w t * Real.cos t)
      (f₃ := fun t => w t * Real.sin t) hw (hw.mul hc) (hw.mul hs), hwE.1, hwE.2.1, hwE.2.2]; ring

theorem projP_gradG_zero_STR02924 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969}
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (a b h γ : ℝ) (hp : ((a, b, h, γ) : Par_STR02916) ∈ U) (t : ℝ) :
    projP_STR02953 (gradG_STR02950 h γ
      (uT_STR02901 a b ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val)) t = 0 := by
  have h0 : Rpar_STR02916 (a, b, h, γ) (ψ (a, b, h, γ)) = 0 :=
    (hR _ hp _ (hψV _ hp)).mpr rfl
  have h1 := str029_15_smooth_variational_range_map_pointwise (a, b, h, γ, ψ (a, b, h, γ)) t
  have h2 : Rvar_STR02915 (a, b, h, γ, ψ (a, b, h, γ)) = 0 := h0
  rw [h2] at h1
  exact h1.symm

theorem chart_isC2_STR02924 (a b : ℝ) (w : E_STR02969) :
    IsC2Alpha_STR02901 (1 / 2)
      (uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val) := by
  rw [← paramMap_val_STR02915]
  exact PeriodicC2_STR02969.isC2 _

theorem inE_of_mem_STR02924 (w : E_STR02969) :
    InE_STR02901 ((w : E_STR02969) : PeriodicC2_STR02969).val :=
  (str029_69_completeness_closed_complements_range_spaces_E.1 _).mp w.2

theorem continuous_val_STR02924 (w : PeriodicC2_STR02969) : Continuous w.val :=
  w.isC2.2.1.continuous

theorem fderiv_Fred_STR02924 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (a b h γ : ℝ) (hp : ((a, b, h, γ) : Par_STR02916) ∈ U) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => Fred_STR02956 ψ y (h, γ)) (a, b) v =
      v.1 * meanT_STR02901 (fun t => gradG_STR02950 h γ (uT_STR02901 a b
        ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val) t * Real.cos t) +
      v.2 * meanT_STR02901 (fun t => gradG_STR02950 h γ (uT_STR02901 a b
        ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val) t * Real.sin t) := by
  have hW := isOpen_iota_preimage_STR02956 hU (h, γ)
  have hy : ((a, b) : ℝ × ℝ) ∈ iota_STR02956 (h, γ) ⁻¹' U := hp
  have hg : DifferentiableAt ℝ (fun y => ψ (iota_STR02956 (h, γ) y)) (a, b) :=
    ((hψC.comp (iota_contDiff_STR02956 (h, γ)).contDiffOn (fun y hy => hy)).contDiffAt
      (hW.mem_nhds hy)).differentiableAt (by simp)
  set g : ℝ × ℝ → E_STR02969 := fun y => ψ (iota_STR02956 (h, γ) y) with hgdef
  have hLf : HasFDerivAt (Lamp_STR02956 ψ (h, γ))
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915) +
        E_STR02969.subtypeL.comp (fderiv ℝ g (a, b))) (a, b) := by
    have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915) (a, b) :=
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.smul_const cosC2_STR02915).add
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.smul_const sinC2_STR02915)
    have h2 : HasFDerivAt (fun y => ((g y : E_STR02969) : PeriodicC2_STR02969))
        (E_STR02969.subtypeL.comp (fderiv ℝ g (a, b))) (a, b) :=
      E_STR02969.subtypeL.hasFDerivAt.comp (a, b) hg.hasFDerivAt
    exact h1.add h2
  have hJd : DifferentiableAt ℝ (JC2_STR02956 h γ) (Lamp_STR02956 ψ (h, γ) (a, b)) :=
    ((JC2_smooth_STR02956 h γ).differentiable (by simp)) _
  have hcomp := hJd.hasFDerivAt.comp (a, b) hLf
  have e : (fun y : ℝ × ℝ => Fred_STR02956 ψ y (h, γ)) =
      JC2_STR02956 h γ ∘ Lamp_STR02956 ψ (h, γ) := Fred_fun_eq_STR02956 ψ (h, γ)
  rw [e, hcomp.fderiv, ContinuousLinearMap.comp_apply, fderiv_JC2_STR02924]
  have hLv : (Lamp_STR02956 ψ (h, γ) (a, b)).val =
      uT_STR02901 a b ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val :=
    paramMap_val_STR02915 a b (ψ (a, b, h, γ))
  set D : E_STR02969 := fderiv ℝ g (a, b) v with hD
  have hLv2 : ((((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915) +
        E_STR02969.subtypeL.comp (fderiv ℝ g (a, b))) v : PeriodicC2_STR02969).val =
      fun t => v.1 * Real.cos t + v.2 * Real.sin t + ((D : E_STR02969) : PeriodicC2_STR02969).val t := by
    funext t
    rfl
  rw [hLv, hLv2]
  set G := gradG_STR02950 h γ (uT_STR02901 a b
    ((ψ (a, b, h, γ) : E_STR02969) : PeriodicC2_STR02969).val) with hG
  have hGc : Continuous G := continuous_gradG_STR02924 h γ (chart_isC2_STR02924 a b _)
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  have hDc := continuous_val_STR02924 ((D : E_STR02969) : PeriodicC2_STR02969)
  have e2 : (fun t => G t * (v.1 * Real.cos t + v.2 * Real.sin t +
      ((D : E_STR02969) : PeriodicC2_STR02969).val t)) = fun t =>
      v.1 * (G t * Real.cos t) + v.2 * (G t * Real.sin t) +
        1 * (G t * ((D : E_STR02969) : PeriodicC2_STR02969).val t) := by
    funext t; ring
  rw [e2, meanT_comb3_STR02924 (f₁ := fun t => G t * Real.cos t) (f₂ := fun t => G t * Real.sin t)
    (f₃ := fun t => G t * ((D : E_STR02969) : PeriodicC2_STR02969).val t)
    (hGc.mul hc) (hGc.mul hs) (hGc.mul hDc),
    meanT_mul_inE_STR02924 hDc (inE_of_mem_STR02924 D)
      (projP_gradG_zero_STR02924 hψV hR a b h γ hp)]
  ring

theorem fderiv_slice_STR02924 {U : Set Par_STR02916}
    {ψ : Par_STR02916 → E_STR02969} {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h : ℝ) (hh : h ≠ 0) (z v : Fin 3 → ℝ) (hz : (h, z) ∈ O) (hv2 : v 2 = 0)
    (hp : ((h * z 0, h * z 1, h, h ^ 2 * z 2) : Par_STR02916) ∈ U) :
    fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z v =
      fderiv ℝ (fun y : ℝ × ℝ => Fred_STR02956 ψ y (h, h ^ 2 * z 2)) (h * z 0, h * z 1)
        (h * v 0, h * v 1) / h ^ 4 := by
  have hW := isOpen_iota_preimage_STR02956 hU (h, h ^ 2 * z 2)
  have hy : ((h * z 0, h * z 1) : ℝ × ℝ) ∈ iota_STR02956 (h, h ^ 2 * z 2) ⁻¹' U := hp
  have hFd : DifferentiableAt ℝ (fun y : ℝ × ℝ => Fred_STR02956 ψ y (h, h ^ 2 * z 2))
      (h * z 0, h * z 1) :=
    ((Fred_contDiffOn_STR02956 hψC (h, h ^ 2 * z 2)).contDiffAt
      (hW.mem_nhds hy)).differentiableAt (by simp)
  have hEd : DifferentiableAt ℝ (fun w : Fin 3 → ℝ => E (h, w)) z := by
    have h1 : DifferentiableAt ℝ E (h, z) :=
      (hEC.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    exact h1.comp z (by fun_prop)
  refine fderiv_line_STR02922 _ z v _ hEd ?_
  have hline : HasDerivAt (fun s : ℝ => ((h * z 0, h * z 1) : ℝ × ℝ) +
      s • ((h * v 0, h * v 1) : ℝ × ℝ)) ((h * v 0, h * v 1) : ℝ × ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((h * v 0, h * v 1) : ℝ × ℝ)).const_add
      ((h * z 0, h * z 1) : ℝ × ℝ)
  have h1 := (hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).div_const (h ^ 4)
  refine h1.congr_of_eventuallyEq ?_
  have hc : Continuous (fun s : ℝ => ((h, z + s • v) : ℝ × (Fin 3 → ℝ))) := by fun_prop
  have hmem : (fun s : ℝ => ((h, z + s • v) : ℝ × (Fin 3 → ℝ))) ⁻¹' O ∈ 𝓝 (0 : ℝ) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hz)
  filter_upwards [hmem] with s hs
  rw [hval h _ hs hh]
  have e1 : ((h * (z + s • v) 0, h * (z + s • v) 1) : ℝ × ℝ) =
      ((h * z 0, h * z 1) : ℝ × ℝ) + s • ((h * v 0, h * v 1) : ℝ × ℝ) := by
    ext <;> simp <;> ring
  have e2 : (z + s • v) 2 = z 2 := by simp [hv2]
  simp only [Function.comp]
  rw [e1, e2]

theorem kfun_STR02924 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U) (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h : ℝ) (hh : h ≠ 0) (z : Fin 3 → ℝ) (hz : (h, z) ∈ O)
    (hp : ((h * z 0, h * z 1, h, h ^ 2 * z 2) : Par_STR02916) ∈ U) :
    Kfun_STR02923 E (h, z) 0 = (h ^ 3)⁻¹ * meanT_STR02901 (fun t =>
        gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t * Real.cos t) ∧
      Kfun_STR02923 E (h, z) 1 = (h ^ 3)⁻¹ * meanT_STR02901 (fun t =>
        gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t * Real.sin t) ∧
      Kfun_STR02923 E (h, z) 2 =
        Jchart_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) / h ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 := fderiv_slice_STR02924 hU hψC hO hEC hval h hh z (Pi.single 0 1) hz (by simp) hp
    have h2 := fderiv_Fred_STR02924 hU hψC hψV hR (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp
      (h * (Pi.single 0 1 : Fin 3 → ℝ) 0, h * (Pi.single 0 1 : Fin 3 → ℝ) 1)
    show fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 0 1) = _
    rw [h1, h2]
    simp only [chartU_STR02924]
    simp
    field_simp
  · have h1 := fderiv_slice_STR02924 hU hψC hO hEC hval h hh z (Pi.single 1 1) hz (by simp) hp
    have h2 := fderiv_Fred_STR02924 hU hψC hψV hR (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp
      (h * (Pi.single 1 1 : Fin 3 → ℝ) 0, h * (Pi.single 1 1 : Fin 3 → ℝ) 1)
    show fderiv ℝ (fun w : Fin 3 → ℝ => E (h, w)) z (Pi.single 1 1) = _
    rw [h1, h2]
    simp only [chartU_STR02924]
    simp
    field_simp
  · show E (h, z) = _
    rw [hval h z hz hh]
    rfl

theorem rho_eq_const_STR02924 (h : ℝ) {u₁ u₂ : ℝ → ℝ} (hu₁ : Continuous u₁)
    (hu₂ : Continuous u₂) (hρ : rhoT_STR02901 h u₁ = rhoT_STR02901 h u₂) :
    ∃ c : ℝ, ∀ t, u₁ t = u₂ t + c := by
  have hZ1 : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u₁ s)) :=
    meanT_pos_STR02901 (by fun_prop) (fun s => Real.exp_pos _)
  have hZ2 : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u₂ s)) :=
    meanT_pos_STR02901 (by fun_prop) (fun s => Real.exp_pos _)
  refine ⟨Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u₁ s))) -
    Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u₂ s))), fun t => ?_⟩
  have := congrArg Real.log (congrFun hρ t)
  unfold rhoT_STR02901 at this
  rw [Real.log_div (Real.exp_pos _).ne' hZ1.ne', Real.log_div (Real.exp_pos _).ne' hZ2.ne',
    Real.log_exp, Real.log_exp] at this
  linarith

theorem inE_zero_STR02924 : InE_STR02901 (fun _ => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact meanT_const_STR02955 0
  · simpa using meanT_const_STR02955 0
  · simpa using meanT_const_STR02955 0

theorem coeff_eq_STR02924 {a₁ b₁ a₂ b₂ c : ℝ} {w₁ w₂ : ℝ → ℝ} (hw₁ : Continuous w₁)
    (hw₂ : Continuous w₂) (hE₁ : InE_STR02901 w₁) (hE₂ : InE_STR02901 w₂)
    (h : ∀ t, uT_STR02901 a₁ b₁ w₁ t = uT_STR02901 a₂ b₂ w₂ t + c) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hc := Real.continuous_cos
  have hs := Real.continuous_sin
  have hu₂ : Continuous (uT_STR02901 a₂ b₂ w₂) := by unfold uT_STR02901; fun_prop
  have k1 := (meanT_uT_STR02924 a₁ b₁ hw₁ hE₁).2.1
  have k2 := (meanT_uT_STR02924 a₂ b₂ hw₂ hE₂).2.1
  have k3 := (meanT_uT_STR02924 a₁ b₁ hw₁ hE₁).2.2
  have k4 := (meanT_uT_STR02924 a₂ b₂ hw₂ hE₂).2.2
  have e1 : (fun t => uT_STR02901 a₁ b₁ w₁ t * Real.cos t) = fun t =>
      1 * (uT_STR02901 a₂ b₂ w₂ t * Real.cos t) + c * Real.cos t + 0 * Real.cos t := by
    funext t; rw [h t]; ring
  have e2 : (fun t => uT_STR02901 a₁ b₁ w₁ t * Real.sin t) = fun t =>
      1 * (uT_STR02901 a₂ b₂ w₂ t * Real.sin t) + c * Real.sin t + 0 * Real.sin t := by
    funext t; rw [h t]; ring
  rw [e1, meanT_comb3_STR02924 (f₁ := fun t => uT_STR02901 a₂ b₂ w₂ t * Real.cos t)
    (f₂ := Real.cos) (f₃ := Real.cos) (hu₂.mul hc) hc hc, k2, meanT_cos_STR02955] at k1
  rw [e2, meanT_comb3_STR02924 (f₁ := fun t => uT_STR02901 a₂ b₂ w₂ t * Real.sin t)
    (f₂ := Real.sin) (f₃ := Real.sin) (hu₂.mul hs) hs hs, k4, meanT_sin_STR02955] at k3
  constructor <;> linarith

theorem exists_deriv_ne_STR02924 (a b : ℝ) (w : E_STR02969) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ t, deriv (uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val) t ≠ 0 := by
  by_contra hcon0
  have hcon : ∀ t, deriv (uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val) t = 0 :=
    fun t => not_not.mp (fun hne => hcon0 ⟨t, hne⟩)
  have hu := chart_isC2_STR02924 a b w
  have hconst : ∀ t, uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val t =
      uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val 0 :=
    fun t => is_const_of_deriv_eq_zero hu.2.1 hcon t 0
  have key := coeff_eq_STR02924 (a₂ := 0) (b₂ := 0) (w₂ := fun _ => (0 : ℝ))
    (c := uT_STR02901 a b ((w : E_STR02969) : PeriodicC2_STR02969).val 0)
    (continuous_val_STR02924 _) continuous_const (inE_of_mem_STR02924 w) inE_zero_STR02924
    (fun t => by rw [hconst t]; simp [uT_STR02901])
  rcases hab with h | h
  · exact h key.1
  · exact h key.2

theorem deriv_periodic_STR02924 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    Function.Periodic (deriv u) (2 * Real.pi) := by
  intro x
  have h1 : (fun y => u (y + 2 * Real.pi)) = u := funext fun y => hu.1 y
  have h2 : deriv (fun y => u (y + 2 * Real.pi)) x = deriv u (x + 2 * Real.pi) :=
    deriv_comp_add_const _ _ x
  rw [h1] at h2
  exact h2.symm

theorem fisher_pos_STR02924 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hne : ∃ t, deriv u t ≠ 0) : 0 < fisherChart_STR02949 h u := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hu1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hρ := continuous_rho_STR02950 h hu0
  obtain ⟨t₁, ht₁⟩ := hne
  obtain ⟨t₀, ht₀, he⟩ := (deriv_periodic_STR02924 hu).exists_mem_Ico₀ (by positivity) t₁
  have hne0 : deriv u t₀ ≠ 0 := by rw [← he]; exact ht₁
  have hfc : Continuous (fun t => deriv u t ^ 2 * rhoT_STR02901 h u t) := (hu1.pow 2).mul hρ
  have hlt : ∫ _ in (0 : ℝ)..(2 * Real.pi), (0 : ℝ) <
      ∫ t in (0 : ℝ)..(2 * Real.pi), deriv u t ^ 2 * rhoT_STR02901 h u t := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by positivity) continuousOn_const hfc.continuousOn ?_ ?_
    · intro x _
      exact mul_nonneg (sq_nonneg _) (rhoT_pos_STR02901 h hu0 x).le
    · exact ⟨t₀, ⟨ht₀.1, ht₀.2.le⟩, mul_pos (by positivity) (rhoT_pos_STR02901 h hu0 t₀)⟩
  simp only [intervalIntegral.integral_zero] at hlt
  unfold fisherChart_STR02949 meanT_STR02901
  positivity

theorem chart_zero_STR02924 {ψ : Par_STR02916 → E_STR02969} (hψ0 : ψ 0 = 0) (z : Fin 3 → ℝ) :
    chartU_STR02924 ψ 0 z = fun _ => 0 := by
  have h0 : ((0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)) = (0 : Par_STR02916) := rfl
  funext t
  have hv : (0 : PeriodicC2_STR02969).val t = 0 := rfl
  simp [chartU_STR02924, uT_STR02901, h0, hψ0, hv]

theorem chartU_isC2_STR02924 (ψ : Par_STR02916 → E_STR02969) (h : ℝ) (z : Fin 3 → ℝ) :
    IsC2Alpha_STR02901 (1 / 2) (chartU_STR02924 ψ h z) :=
  chart_isC2_STR02924 _ _ _

theorem rho_chart_zero_STR02924 {ψ : Par_STR02916 → E_STR02969} (hψ0 : ψ 0 = 0)
    (z : Fin 3 → ℝ) : rhoT_STR02901 0 (chartU_STR02924 ψ 0 z) = qT_STR02901 0 := by
  funext t
  rw [chart_zero_STR02924 hψ0 z]
  simp [rhoT_STR02901, qT_STR02901]

theorem gradG_chart_zero_STR02924 {ψ : Par_STR02916 → E_STR02969} (hψ0 : ψ 0 = 0)
    (z : Fin 3 → ℝ) (γ t : ℝ) : gradG_STR02950 0 γ (chartU_STR02924 ψ 0 z) t = 0 := by
  rw [chart_zero_STR02924 hψ0 z]
  have h0 : meanT_STR02901 (fun _ : ℝ => (0 : ℝ)) = 0 := by simp [meanT_STR02901]
  simp [gradG_STR02950, h0]

theorem lift_STR02924 {U : Set Par_STR02916} {V : Set E_STR02969}
    {ψ : Par_STR02916 → E_STR02969} {O : Set (ℝ × (Fin 3 → ℝ))} {E : ℝ × (Fin 3 → ℝ) → ℝ}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U) (hψV : ∀ p ∈ U, ψ p ∈ V)
    (hR : ∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p)
    (hO : IsOpen O) (hEC : ContDiffOn ℝ ∞ E O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h : ℝ) (hh : h ≠ 0) (z : Fin 3 → ℝ) (hz : (h, z) ∈ O)
    (hp : ((h * z 0, h * z 1, h, h ^ 2 * z 2) : Par_STR02916) ∈ U)
    (hK : Kfun_STR02923 E (h, z) = 0) (hr : 0 < 1 + h ^ 2 * z 2)
    (hsq : 0 < z 0 ^ 2 + z 1 ^ 2) :
    (∀ t, gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t = 0) ∧
    0 < entropyChart_STR02949 h (chartU_STR02924 ψ h z) ∧
    fisherChart_STR02949 h (chartU_STR02924 ψ h z) /
      (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h z)) = 1 + h ^ 2 * z 2 := by
  obtain ⟨k0, k1, k2⟩ := kfun_STR02924 hU hψC hψV hR hO hEC hval h hh z hz hp
  have e0 : Kfun_STR02923 E (h, z) 0 = 0 := by rw [hK]; rfl
  have e1 : Kfun_STR02923 E (h, z) 1 = 0 := by rw [hK]; rfl
  have e2 : Kfun_STR02923 E (h, z) 2 = 0 := by rw [hK]; rfl
  have hh3 : (h ^ 3)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 3 hh)
  have hc : meanT_STR02901 (fun t =>
      gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t * Real.cos t) = 0 :=
    (mul_eq_zero.mp (k0.symm.trans e0)).resolve_left hh3
  have hs : meanT_STR02901 (fun t =>
      gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t * Real.sin t) = 0 :=
    (mul_eq_zero.mp (k1.symm.trans e1)).resolve_left hh3
  have hJ : Jchart_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) = 0 :=
    (div_eq_zero_iff.mp (k2.symm.trans e2)).resolve_right (pow_ne_zero 4 hh)
  have hGeq : ∀ t, gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z) t = 0 := by
    intro t
    have hP : projP_STR02953 (gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z)) t = 0 :=
      projP_gradG_zero_STR02924 hψV hR (h * z 0) (h * z 1) h (h ^ 2 * z 2) hp t
    have hm : meanT_STR02901 (gradG_STR02950 h (h ^ 2 * z 2) (chartU_STR02924 ψ h z)) = 0 :=
      str029_50_integrate_variation_compute_mean_mean_zero h (h ^ 2 * z 2)
        (chartU_isC2_STR02924 ψ h z)
    simp only [projP_STR02953, pair_STR02953] at hP
    rw [hm, hc, hs] at hP
    simpa using hP
  refine ⟨hGeq, ?_⟩
  have hne : ∃ t, deriv (chartU_STR02924 ψ h z) t ≠ 0 := by
    have hab : h * z 0 ≠ 0 ∨ h * z 1 ≠ 0 := by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      have h0 : z 0 = 0 := (mul_eq_zero.mp hcon.1).resolve_left hh
      have h1 : z 1 = 0 := (mul_eq_zero.mp hcon.2).resolve_left hh
      rw [h0, h1] at hsq
      norm_num at hsq
    exact exists_deriv_ne_STR02924 (h * z 0) (h * z 1) (ψ (h * z 0, h * z 1, h, h ^ 2 * z 2)) hab
  have hI := fisher_pos_STR02924 h (chartU_isC2_STR02924 ψ h z) hne
  have hJ' : fisherChart_STR02949 h (chartU_STR02924 ψ h z) -
      2 * (1 + h ^ 2 * z 2) * entropyChart_STR02949 h (chartU_STR02924 ψ h z) = 0 := hJ
  have hH : 0 < entropyChart_STR02949 h (chartU_STR02924 ψ h z) := by
    rcases lt_or_ge 0 (entropyChart_STR02949 h (chartU_STR02924 ψ h z)) with hH | hH
    · exact hH
    · exfalso
      nlinarith [mul_nonneg hr.le (neg_nonneg.mpr hH)]
  refine ⟨hH, ?_⟩
  rw [div_eq_iff (by positivity)]
  linear_combination hJ'

theorem distinct_STR02924 (ψ : Par_STR02916 → E_STR02969) (h : ℝ) (hh : h ≠ 0)
    (z₁ z₂ : Fin 3 → ℝ) (h3 : z₁ 2 = z₂ 2) (hne : z₁ ≠ z₂) :
    rhoT_STR02901 h (chartU_STR02924 ψ h z₁) ≠ rhoT_STR02901 h (chartU_STR02924 ψ h z₂) := by
  intro hρ
  obtain ⟨c, hc⟩ := rho_eq_const_STR02924 h (chartU_isC2_STR02924 ψ h z₁).2.1.continuous
    (chartU_isC2_STR02924 ψ h z₂).2.1.continuous hρ
  obtain ⟨ha, hb⟩ := coeff_eq_STR02924 (continuous_val_STR02924 _) (continuous_val_STR02924 _)
    (inE_of_mem_STR02924 _) (inE_of_mem_STR02924 _) hc
  apply hne
  have h0 : z₁ 0 = z₂ 0 := mul_left_cancel₀ hh ha
  have h1 : z₁ 1 = z₂ 1 := mul_left_cancel₀ hh hb
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h3

theorem str029_24_lift_reduced_branches_full_critical_densities :
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
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
                (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
                (h ≠ 0 →
                  0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
                  fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
                    (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
                    1 + h ^ 2 * Z j h 2)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
                rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
                  rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) ∧
              (∀ j : Fin 3, rhoT_STR02901 0 (chartU_STR02924 ψ 0 (Z j 0)) = qT_STR02901 0 ∧
                ∀ t, gradG_STR02950 0 0 (chartU_STR02924 ψ 0 (Z j 0)) t = 0) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq⟩ := str029_23_three_locally_unique_solution_branches
  refine ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, ?_⟩
  have hηmem : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, hη⟩
  have hIoo : ∀ᶠ h in 𝓝 (0 : ℝ), h ∈ Set.Ioo (-η) η := isOpen_Ioo.eventually_mem hηmem
  have hIoo' : Set.Ioo (-η) η ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds hηmem
  have hZcont : ∀ j, ContinuousAt (Z j) 0 := fun j => ((hZC j).continuousOn).continuousAt hIoo'
  have hZ00 : Z 0 0 = ![2, 0, -16 / 15] := by
    have hK := (str029_22_invertible_finite_dimensional_jacobian_of_slice E hzero).1
    have hmem : (![2, 0, -16 / 15] : Fin 3 → ℝ) ∈ N 0 := mem_of_mem_nhds hn0
    exact ((hKuniq 0 0 hηmem _ hmem).mp hK).symm
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
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), h ∈ Set.Ioo (-η) η ∧ ∀ j : Fin 3,
      (h, Z j h) ∈ O ∧
      ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916) ∈ U ∧
      0 < 1 + h ^ 2 * Z j h 2 ∧ 0 < (Z j h 0) ^ 2 + (Z j h 1) ^ 2 := by
    refine hIoo.and ?_
    rw [Filter.eventually_all]
    intro j
    have hz := hZcont j
    have hz0 : ContinuousAt (fun h => Z j h 0) 0 := (continuous_apply 0).continuousAt.comp hz
    have hz1 : ContinuousAt (fun h => Z j h 1) 0 := (continuous_apply 1).continuousAt.comp hz
    have hz2 : ContinuousAt (fun h => Z j h 2) 0 := (continuous_apply 2).continuousAt.comp hz
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ ?_))
    · have hc : ContinuousAt (fun h : ℝ => ((h, Z j h) : ℝ × (Fin 3 → ℝ))) 0 :=
        continuousAt_id.prodMk hz
      exact hc.preimage_mem_nhds (hOo.mem_nhds (hOmem (Z j 0)))
    · have hc : ContinuousAt (fun h : ℝ =>
          ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916)) 0 :=
        (continuousAt_id.mul hz0).prodMk ((continuousAt_id.mul hz1).prodMk
          (continuousAt_id.prodMk ((continuousAt_id.pow 2).mul hz2)))
      have h0 : ((0 * Z j 0 0, 0 * Z j 0 1, (0 : ℝ), 0 ^ 2 * Z j 0 2) : Par_STR02916) ∈ U := by
        have : ((0 * Z j 0 0, 0 * Z j 0 1, (0 : ℝ), 0 ^ 2 * Z j 0 2) : Par_STR02916) = 0 := by
          simp
        rw [this]; exact hU0
      exact hc.preimage_mem_nhds (hUo.mem_nhds h0)
    · have hc : ContinuousAt (fun h : ℝ => 1 + h ^ 2 * Z j h 2) 0 :=
        continuousAt_const.add ((continuousAt_id.pow 2).mul hz2)
      exact (continuousAt_const (y := (0 : ℝ))).eventually_lt hc (by simp)
    · have hc : ContinuousAt (fun h : ℝ => (Z j h 0) ^ 2 + (Z j h 1) ^ 2) 0 :=
        (hz0.pow 2).add (hz1.pow 2)
      exact (continuousAt_const (y := (0 : ℝ))).eventually_lt hc (by simp only [hsq0 j]; norm_num)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε η, lt_min hε hη, min_le_right _ _, ?_⟩
  have hgood : ∀ h ∈ Set.Ioo (-(min ε η)) (min ε η), h ∈ Set.Ioo (-η) η ∧ ∀ j : Fin 3,
      (h, Z j h) ∈ O ∧
      ((h * Z j h 0, h * Z j h 1, h, h ^ 2 * Z j h 2) : Par_STR02916) ∈ U ∧
      0 < 1 + h ^ 2 * Z j h 2 ∧ 0 < (Z j h 0) ^ 2 + (Z j h 1) ^ 2 := by
    intro h hh
    apply hεP
    have h1 := min_le_left ε η
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hmain : ∀ h ∈ Set.Ioo (-(min ε η)) (min ε η), ∀ j : Fin 3,
      (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
      (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
      (h ≠ 0 →
        0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
        fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
          (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) = 1 + h ^ 2 * Z j h 2) := by
    intro h hh j
    refine ⟨fun t => rhoT_pos_STR02901 h (chartU_isC2_STR02924 ψ h (Z j h)).2.1.continuous t,
      ?_⟩
    rcases eq_or_ne h 0 with rfl | hne
    · exact ⟨fun t => gradG_chart_zero_STR02924 hψ0 _ _ t, fun h0 => absurd rfl h0⟩
    · obtain ⟨hhη, hj⟩ := hgood h hh
      obtain ⟨hOz, hpU, hr, hsq⟩ := hj j
      have hK : Kfun_STR02923 E (h, Z j h) = 0 := (hKuniq j h hhη _ (hZN j h hhη)).mpr rfl
      obtain ⟨hG, hH, hq⟩ := lift_STR02924 hUo hψC hψV hR hOo hEC hval h hne (Z j h) hOz hpU hK
        hr hsq
      exact ⟨hG, fun _ => ⟨hH, hq⟩⟩
  refine ⟨hmain, ?_, ?_⟩
  · intro h hh hne i j hij
    obtain ⟨hhη, -⟩ := hgood h hh
    have hZne : Z i h ≠ Z j h := by
      intro heq
      exact Set.disjoint_left.mp (hdisj i j hij) (hZN i h hhη) (by rw [heq]; exact hZN j h hhη)
    exact distinct_STR02924 ψ h hne (Z i h) (Z j h) ((hZs h hhη i).trans (hZs h hhη j).symm) hZne
  · intro j
    exact ⟨rho_chart_zero_STR02924 hψ0 _, fun t => gradG_chart_zero_STR02924 hψ0 _ _ t⟩

end DGPS.Frontier.STR029
