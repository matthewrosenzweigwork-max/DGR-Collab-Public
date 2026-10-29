import DGPS.Lipschitz.MeanFieldLocalFlow

/-!
# The mean-field nonlinearity `𝒩(u) = u (∇V + B ∗ P(u))` (LIP025b)

Sub-packet b of LIP025: measurability of the nonlinearity, the pointwise and `Lᵖ` estimates

* `‖𝒩(u)‖ₚ ≤ B₀ ‖u‖ₚ`,
* `‖𝒩(u) − 𝒩(v)‖ₚ ≤ B₀ ‖u − v‖ₚ + 2 ‖B‖∞ ‖v‖ₚ ‖u − v‖₁`,

for every `1 ≤ p ≤ ∞` (in particular `p = 2` and `p = ⊤`), with `B₀ = g + b`, where `g` bounds
`∇V = G` and `b` bounds `B` (everywhere, on the Lipschitz representatives); and the induced map
`Nvec : L² → L²(ℝ^d)` with its bound `‖Nvec u‖₂ ≤ B₀ ‖u‖₂`, its Lipschitz estimate on a.e.-bounded
balls `{‖v‖∞ ≤ R}` with constant `B₀ + 2 b R`, and its continuity there.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The convolution term `x ↦ ∫ P(u)(y) • B x y dy`. -/
noncomputable def meanFieldConv (B : Torus d → Torus d → Tangent d) (u : Torus d → ℝ)
    (x : Torus d) : Tangent d :=
  ∫ y, normPos u y • B x y ∂haar d

theorem meanFieldN_eq (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (u : Torus d → ℝ) (x : Torus d) :
    meanFieldN G B u x = u x • (G x + meanFieldConv B u x) := rfl

/-- Hypotheses on `G = ∇V` and `B`: measurable, with everywhere bounds `‖G‖ ≤ g`, `‖B‖ ≤ b`. -/
structure MeanFieldData (G : Torus d → Tangent d) (B : Torus d → Torus d → Tangent d)
    (g b : ℝ) : Prop where
  g_nonneg : 0 ≤ g
  b_nonneg : 0 ≤ b
  measurable_G : Measurable G
  measurable_B : Measurable (Function.uncurry B)
  norm_G_le : ∀ x, ‖G x‖ ≤ g
  norm_B_le : ∀ x y, ‖B x y‖ ≤ b

section Estimates

variable {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

theorem MeanFieldData.measurable_B_right (h : MeanFieldData G B g b) (x : Torus d) :
    Measurable (B x) :=
  h.measurable_B.comp measurable_prodMk_left

theorem norm_normPos_smul_le (h : MeanFieldData G B g b) (u : Torus d → ℝ) (x y : Torus d) :
    ‖normPos u y • B x y‖ ≤ normPos u y * b := by
  rw [norm_smul, Real.norm_of_nonneg (normPos_nonneg u y)]
  exact mul_le_mul_of_nonneg_left (h.norm_B_le x y) (normPos_nonneg u y)

theorem integrable_normPos_smul (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : Integrable u (haar d)) (x : Torus d) :
    Integrable (fun y => normPos u y • B x y) (haar d) :=
  Integrable.mono' ((integrable_normPos hu).mul_const b)
    ((integrable_normPos hu).aestronglyMeasurable.smul
      (h.measurable_B_right x).aestronglyMeasurable)
    (Eventually.of_forall fun y => norm_normPos_smul_le h u x y)

theorem norm_meanFieldConv_le (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : Integrable u (haar d)) (x : Torus d) : ‖meanFieldConv B u x‖ ≤ b := by
  unfold meanFieldConv
  calc ‖∫ y, normPos u y • B x y ∂haar d‖ ≤ ∫ y, ‖normPos u y • B x y‖ ∂haar d :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, normPos u y * b ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          ((integrable_normPos hu).mul_const b)
          (Eventually.of_forall fun y => norm_normPos_smul_le h u x y)
    _ = (∫ y, normPos u y ∂haar d) * b := integral_mul_const _ _
    _ ≤ 1 * b := mul_le_mul_of_nonneg_right integral_normPos_le h.b_nonneg
    _ = b := one_mul b

theorem norm_meanFieldConv_sub_le (h : MeanFieldData G B g b) {u v : Torus d → ℝ}
    (hu : Integrable u (haar d)) (hv : Integrable v (haar d)) (x : Torus d) :
    ‖meanFieldConv B u x - meanFieldConv B v x‖ ≤ 2 * b * ∫ y, |u y - v y| ∂haar d := by
  unfold meanFieldConv
  rw [← integral_sub (integrable_normPos_smul h hu x) (integrable_normPos_smul h hv x)]
  have hP : Integrable (fun y => |normPos u y - normPos v y|) (haar d) :=
    ((integrable_normPos hu).sub (integrable_normPos hv)).abs
  calc ‖∫ y, (normPos u y • B x y - normPos v y • B x y) ∂haar d‖
      ≤ ∫ y, ‖normPos u y • B x y - normPos v y • B x y‖ ∂haar d :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, |normPos u y - normPos v y| * b ∂haar d := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hP.mul_const b) (Eventually.of_forall fun y => ?_)
        simp only []
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (h.norm_B_le x y) (abs_nonneg _)
    _ = (∫ y, |normPos u y - normPos v y| ∂haar d) * b := integral_mul_const _ _
    _ ≤ (2 * ∫ y, |u y - v y| ∂haar d) * b :=
        mul_le_mul_of_nonneg_right (integral_abs_normPos_sub_le hu hv) h.b_nonneg
    _ = 2 * b * ∫ y, |u y - v y| ∂haar d := by ring

theorem norm_meanFieldN_le (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : Integrable u (haar d)) (x : Torus d) :
    ‖meanFieldN G B u x‖ ≤ (g + b) * |u x| := by
  rw [meanFieldN_eq, norm_smul, Real.norm_eq_abs, mul_comm]
  refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (abs_nonneg _)
  exact add_le_add (h.norm_G_le x) (norm_meanFieldConv_le h hu x)

theorem norm_meanFieldN_sub_le (h : MeanFieldData G B g b) {u v : Torus d → ℝ}
    (hu : Integrable u (haar d)) (hv : Integrable v (haar d)) (x : Torus d) :
    ‖meanFieldN G B u x - meanFieldN G B v x‖ ≤
      (g + b) * |u x - v x| + (2 * b * ∫ y, |u y - v y| ∂haar d) * |v x| := by
  have e : meanFieldN G B u x - meanFieldN G B v x =
      (u x - v x) • (G x + meanFieldConv B u x) +
        v x • (meanFieldConv B u x - meanFieldConv B v x) := by
    simp only [meanFieldN_eq]; module
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (abs_nonneg _)
    exact add_le_add (h.norm_G_le x) (norm_meanFieldConv_le h hu x)
  · rw [norm_smul, Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_meanFieldConv_sub_le h hu hv x) (abs_nonneg _)

/-! ### Measurability -/

theorem normPos_congr_ae {u v : Torus d → ℝ} (huv : u =ᵐ[haar d] v) :
    normPos u =ᵐ[haar d] normPos v := by
  have hI : ∫ y, max (u y) 0 ∂haar d = ∫ y, max (v y) 0 ∂haar d :=
    integral_congr_ae (huv.mono fun y hy => by simp only [hy])
  filter_upwards [huv] with y hy
  unfold normPos
  rw [hI, hy]

theorem meanFieldConv_congr_ae {u v : Torus d → ℝ} (huv : u =ᵐ[haar d] v) :
    meanFieldConv B u = meanFieldConv B v := by
  funext x
  unfold meanFieldConv
  exact integral_congr_ae ((normPos_congr_ae huv).mono fun y hy => by simp only [hy])

theorem measurable_normPos {u : Torus d → ℝ} (hu : Measurable u) : Measurable (normPos u) := by
  unfold normPos
  exact (hu.max measurable_const).div_const _

/-- Measurability of `x ↦ ∫ P(u)(y) • B x y dy`; only `u` a.e.-strongly measurable is needed. -/
theorem stronglyMeasurable_meanFieldConv (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : AEStronglyMeasurable u (haar d)) : StronglyMeasurable (meanFieldConv B u) := by
  rw [meanFieldConv_congr_ae hu.ae_eq_mk]
  have hm : Measurable hu.mk := hu.stronglyMeasurable_mk.measurable
  have hjoint : Measurable (fun p : Torus d × Torus d => normPos hu.mk p.2 • B p.1 p.2) :=
    ((measurable_normPos hm).comp measurable_snd).smul h.measurable_B
  exact hjoint.stronglyMeasurable.integral_prod_right'

theorem measurable_meanFieldConv (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : AEStronglyMeasurable u (haar d)) : Measurable (meanFieldConv B u) :=
  (stronglyMeasurable_meanFieldConv h hu).measurable

theorem aestronglyMeasurable_meanFieldN (h : MeanFieldData G B g b) {u : Torus d → ℝ}
    (hu : AEStronglyMeasurable u (haar d)) :
    AEStronglyMeasurable (meanFieldN G B u) (haar d) :=
  hu.smul (h.measurable_G.aestronglyMeasurable.add
    (stronglyMeasurable_meanFieldConv h hu).aestronglyMeasurable)

/-! ### `Lᵖ` estimates -/

theorem eLpNorm_meanFieldN_le (h : MeanFieldData G B g b) {u : Torus d → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hu : MemLp u p (haar d)) :
    eLpNorm (meanFieldN G B u) p (haar d) ≤
      ENNReal.ofReal (g + b) * eLpNorm u p (haar d) := by
  have hi : Integrable u (haar d) := hu.integrable hp
  calc eLpNorm (meanFieldN G B u) p (haar d)
      ≤ eLpNorm ((g + b) • u) p (haar d) := by
        refine eLpNorm_mono_ae (aestronglyMeasurable_meanFieldN h hu.aestronglyMeasurable)
          (Eventually.of_forall fun x => ?_)
        simpa [Real.norm_eq_abs, abs_of_nonneg (add_nonneg h.g_nonneg h.b_nonneg)]
          using norm_meanFieldN_le h hi x
    _ = ENNReal.ofReal (g + b) * eLpNorm u p (haar d) := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg (add_nonneg h.g_nonneg h.b_nonneg)]

theorem memLp_meanFieldN (h : MeanFieldData G B g b) {u : Torus d → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hu : MemLp u p (haar d)) : MemLp (meanFieldN G B u) p (haar d) :=
  by
  have hlt : eLpNorm (meanFieldN G B u) p (haar d) < ∞ :=
    lt_of_le_of_lt (eLpNorm_meanFieldN_le h hp hu)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.eLpNorm_lt_top)
  exact hlt

theorem eLpNorm_meanFieldN_sub_le (h : MeanFieldData G B g b) {u v : Torus d → ℝ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hu : MemLp u p (haar d)) (hv : MemLp v p (haar d)) :
    eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) p (haar d) ≤
      ENNReal.ofReal (g + b) * eLpNorm (fun x => u x - v x) p (haar d) +
        ENNReal.ofReal (2 * b) * eLpNorm v p (haar d) *
          eLpNorm (fun x => u x - v x) 1 (haar d) := by
  have hiu : Integrable u (haar d) := hu.integrable hp
  have hiv : Integrable v (haar d) := hv.integrable hp
  set D := ∫ y, |u y - v y| ∂haar d with hD
  have hD0 : 0 ≤ D := integral_nonneg fun y => abs_nonneg _
  have hb2 : 0 ≤ 2 * b := by linarith [h.b_nonneg]
  have hg : 0 ≤ g + b := add_nonneg h.g_nonneg h.b_nonneg
  have h1 : eLpNorm (fun x => u x - v x) 1 (haar d) = ENNReal.ofReal D :=
    eLpNorm_one_eq_ofReal_integral_abs (hiu.sub hiv)
  have hsub : MemLp (fun x => u x - v x) p (haar d) := hu.sub hv
  have hmeas : AEStronglyMeasurable (fun x => meanFieldN G B u x - meanFieldN G B v x)
      (haar d) :=
    (aestronglyMeasurable_meanFieldN h hu.aestronglyMeasurable).sub
      (aestronglyMeasurable_meanFieldN h hv.aestronglyMeasurable)
  calc eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) p (haar d)
      ≤ eLpNorm (((g + b) • fun x => ‖u x - v x‖) + (2 * b * D) • fun x => ‖v x‖) p (haar d) := by
        refine eLpNorm_mono_ae hmeas (Eventually.of_forall fun x => ?_)
        have := norm_meanFieldN_sub_le h hiu hiv x
        rw [← hD] at this
        refine this.trans ((le_of_eq ?_).trans (le_abs_self _))
        simp [Real.norm_eq_abs, mul_comm]
    _ ≤ eLpNorm ((g + b) • fun x => ‖u x - v x‖) p (haar d) +
          eLpNorm ((2 * b * D) • fun x => ‖v x‖) p (haar d) := eLpNorm_add_le hp
    _ = ENNReal.ofReal (g + b) * eLpNorm (fun x => u x - v x) p (haar d) +
          ENNReal.ofReal (2 * b) * eLpNorm v p (haar d) *
            eLpNorm (fun x => u x - v x) 1 (haar d) := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm _ hsub.aestronglyMeasurable,
          eLpNorm_norm _ hv.aestronglyMeasurable, h1,
          Real.enorm_of_nonneg hg, Real.enorm_of_nonneg (mul_nonneg hb2 hD0),
          ENNReal.ofReal_mul hb2]
        ring

end Estimates

/-! ### The map `Nvec : L² → L²(ℝ^d)` -/

section Nvec

variable {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- The mean-field nonlinearity as a map `L²(𝕋^d) → L²(𝕋^d; ℝ^d)`. -/
noncomputable def Nvec (h : MeanFieldData G B g b) (u : L2s d) : L2v d :=
  (memLp_meanFieldN h one_le_two (Lp.memLp u)).toLp (meanFieldN G B u)

theorem coeFn_Nvec (h : MeanFieldData G B g b) (u : L2s d) :
    ⇑(Nvec h u) =ᵐ[haar d] meanFieldN G B u :=
  MemLp.coeFn_toLp _

/-- `‖𝒩(u)‖₂ ≤ B₀ ‖u‖₂` with `B₀ = g + b`. -/
theorem norm_Nvec_le (h : MeanFieldData G B g b) (u : L2s d) :
    ‖Nvec h u‖ ≤ (g + b) * ‖u‖ := by
  have hg : 0 ≤ g + b := add_nonneg h.g_nonneg h.b_nonneg
  rw [Nvec, Lp.norm_toLp, Lp.norm_def]
  have hle := eLpNorm_meanFieldN_le h one_le_two (Lp.memLp u)
  have hfin : ENNReal.ofReal (g + b) * eLpNorm (⇑u) 2 (haar d) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp u).eLpNorm_lt_top).ne
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hg] at this
  exact this

theorem eLpNorm_coeFn_sub (u v : L2s d) :
    eLpNorm (⇑(u - v)) 2 (haar d) = eLpNorm (fun x => u x - v x) 2 (haar d) :=
  eLpNorm_congr_ae ((Lp.coeFn_sub u v).mono fun x hx => by simp only [hx, Pi.sub_apply])

/-- Local Lipschitz bound on `{‖v‖∞ ≤ R}`: `‖𝒩(u) − 𝒩(v)‖₂ ≤ (B₀ + 2 b R) ‖u − v‖₂`,
with `B₀ = g + b`; `u` is arbitrary in `L²`. -/
theorem norm_Nvec_sub_le (h : MeanFieldData G B g b) (u v : L2s d) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∀ᵐ x ∂haar d, |v x| ≤ R) :
    ‖Nvec h u - Nvec h v‖ ≤ (g + b + 2 * b * R) * ‖u - v‖ := by
  have hg : 0 ≤ g + b := add_nonneg h.g_nonneg h.b_nonneg
  have hb2 : 0 ≤ 2 * b := by linarith [h.b_nonneg]
  set E := eLpNorm (fun x => u x - v x) 2 (haar d) with hE
  have hEfin : E ≠ ∞ := by
    rw [hE, ← eLpNorm_coeFn_sub]; exact (Lp.memLp (u - v)).eLpNorm_lt_top.ne
  have hnorm : ‖u - v‖ = E.toReal := by rw [Lp.norm_def, eLpNorm_coeFn_sub]
  have hL : eLpNorm (⇑(Nvec h u - Nvec h v)) 2 (haar d) =
      eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) 2 (haar d) :=
    eLpNorm_congr_ae <| by
      filter_upwards [Lp.coeFn_sub (Nvec h u) (Nvec h v), coeFn_Nvec h u, coeFn_Nvec h v]
        with x h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
  have main := eLpNorm_meanFieldN_sub_le h one_le_two (Lp.memLp u) (Lp.memLp v)
  have hv2 : eLpNorm (⇑v) 2 (haar d) ≤ ENNReal.ofReal R := by
    have := eLpNorm_le_of_ae_bound (p := 2) (μ := haar d) (f := ⇑v) (C := R)
      (Lp.aestronglyMeasurable v) (hv.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
    simpa using this
  have h1le : eLpNorm (fun x => u x - v x) 1 (haar d) ≤ E :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have key : eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) 2 (haar d) ≤
      ENNReal.ofReal (g + b + 2 * b * R) * E := by
    refine main.trans ?_
    calc _ ≤ ENNReal.ofReal (g + b) * E + ENNReal.ofReal (2 * b) * ENNReal.ofReal R * E :=
          add_le_add le_rfl (mul_le_mul' (mul_le_mul' le_rfl hv2) h1le)
      _ = _ := by
          rw [ENNReal.ofReal_add hg (mul_nonneg hb2 hR), ENNReal.ofReal_mul hb2]; ring
  have hfin : ENNReal.ofReal (g + b + 2 * b * R) * E ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hEfin.lt_top).ne
  have := ENNReal.toReal_mono hfin key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity [h.b_nonneg, hg])] at this
  rw [Lp.norm_def, hL, hnorm]
  exact this

/-- The set `{v ∈ L² : ‖v‖∞ ≤ R}` (a.e.). -/
def aeBall (d : ℕ) (R : ℝ) : Set (L2s d) := {v | ∀ᵐ x ∂haar d, |v x| ≤ R}

theorem lipschitzOnWith_Nvec (h : MeanFieldData G B g b) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith ⟨g + b + 2 * b * R, by
      have := h.g_nonneg; have := h.b_nonneg; positivity⟩ (Nvec h) (aeBall d R) := by
  refine LipschitzOnWith.of_dist_le_mul fun u _ v hv => ?_
  rw [dist_eq_norm, dist_eq_norm]
  exact norm_Nvec_sub_le h u v hR hv

/-- `Nvec` is continuous on every a.e.-bounded ball. -/
theorem continuousOn_Nvec (h : MeanFieldData G B g b) {R : ℝ} (hR : 0 ≤ R) :
    ContinuousOn (Nvec h) (aeBall d R) :=
  (lipschitzOnWith_Nvec h hR).continuousOn

end Nvec

end DGPS.Lipschitz
