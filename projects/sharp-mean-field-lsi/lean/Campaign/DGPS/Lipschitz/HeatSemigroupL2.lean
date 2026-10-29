import DGPS.Lipschitz.MeanFieldLocalFlow

/-!
# The periodic heat semigroup on `L²` (LIP025a)

Bounded-operator packaging of the componentwise periodic heat semigroup:
`heatCLM h : L²(𝕋^d) →L L²(𝕋^d)` and `heatGradCLM h : L²(𝕋^d;ℝ^d) →L L²(𝕋^d;ℝ^d)`
(contractions for `h ≥ 0`, equal to the identity for `h ≤ 0`), their semigroup law and strong
continuity on `[0,∞)`, the composition identity `divHeat (τ+h) = divHeat τ ∘ heatGradCLM h`,
the Duhamel kernel instance for `divHeat`, and the `L²`-valued heat flow `heatL2`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A contraction semigroup on `[0,∞)` that is strongly continuous at `0⁺` is strongly continuous
on `[0,∞)`. -/
theorem continuousOn_Ici_of_semigroup (T : ℝ → X →L[ℝ] X)
    (hnorm : ∀ a, 0 ≤ a → ∀ f, ‖T a f‖ ≤ ‖f‖)
    (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → ∀ f, T (a + b) f = T a (T b f))
    (hzero : ∀ f, T 0 f = f)
    (hlim : ∀ f, Tendsto (fun δ => T δ f) (𝓝[>] 0) (𝓝 f)) (f : X) :
    ContinuousOn (fun h => T h f) (Ici 0) := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → ‖T (a + b) f - T a f‖ ≤ ‖T b f - f‖ := by
    intro a b ha hb
    have : T (a + b) f - T a f = T a (T b f - f) := by rw [map_sub, hadd a b ha hb]
    rw [this]
    exact hnorm a ha _
  intro x0 hx0
  have hx0' : 0 ≤ x0 := hx0
  have hψ : Tendsto (fun δ : ℝ => ‖T δ f - f‖) (𝓝[Ici 0] 0) (𝓝 0) := by
    rw [← Set.Ioi_insert, nhdsWithin_insert]
    refine Tendsto.sup ?_ ?_
    · refine tendsto_pure_left.mpr fun s hs => ?_
      simpa [hzero] using mem_of_mem_nhds hs
    · have := (hlim f).sub_const f
      simpa using this.norm
  have habs : Tendsto (fun x : ℝ => |x - x0|) (𝓝[Ici 0] x0) (𝓝[Ici 0] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun x => mem_Ici.mpr (abs_nonneg _)⟩
    have : Continuous fun x : ℝ => |x - x0| := by fun_prop
    simpa using (this.tendsto x0).mono_left nhdsWithin_le_nhds
  have hbound : ∀ x ∈ Ici (0 : ℝ), ‖T x f - T x0 f‖ ≤ ‖T |x - x0| f - f‖ := by
    intro x hx
    have hx' : 0 ≤ x := hx
    rcases le_total x0 x with h | h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have := key x0 (x - x0) hx0' (sub_nonneg.mpr h)
      rwa [add_sub_cancel] at this
    · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub, norm_sub_rev]
      have := key x (x0 - x) hx' (sub_nonneg.mpr h)
      rwa [add_sub_cancel] at this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (hψ.comp habs)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hbound x hx

end Abstract

/-! ### `L²` norms as integrals -/

theorem sq_toReal_eLpNorm_two {E : Type*} [NormedAddCommGroup E] {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun x => by positivity)]
  norm_num

theorem norm_Lp_two_sq {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp E 2 μ) : ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [Lp.norm_def]
  exact sq_toReal_eLpNorm_two (Lp.memLp u)

theorem integral_sq_heatOp_le {h : ℝ} (hh : 0 < h) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    ∫ y, (heatOp h f y) ^ 2 ∂haar d ≤ ∫ y, (f y) ^ 2 ∂haar d := by
  have hH := memLp_heatOp hh one_le_two (by simp) hf
  have h1 := ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_heatOp_le hh one_le_two (by simp) hf)
  have h2 := pow_le_pow_left₀ ENNReal.toReal_nonneg h1 2
  rw [sq_toReal_eLpNorm_two hH, sq_toReal_eLpNorm_two hf] at h2
  simpa only [Real.norm_eq_abs, sq_abs] using h2

/-! ### Linear structure of the heat operators -/

theorem heatOp_add_fun {h : ℝ} (hh : 0 < h) {f g : Torus d → ℝ} (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) :
    heatOp h (fun z => f z + g z) = fun y => heatOp h f y + heatOp h g y := by
  funext y
  unfold heatOp torusConv
  rw [← integral_add (integrable_conv_integrand (continuous_heatKernelT hh) hf y)
    (integrable_conv_integrand (continuous_heatKernelT hh) hg y)]
  congr 1; funext w; ring

theorem heatOp_smul_fun {h : ℝ} (c : ℝ) (f : Torus d → ℝ) :
    heatOp h (fun z => c * f z) = fun y => c * heatOp h f y := by
  funext y
  unfold heatOp torusConv
  rw [← integral_const_mul]
  congr 1; funext w; ring

/-! ### The scalar heat operator on `L²` -/

/-- The linear heat operator `H_h` on `L²(𝕋^d)`, for `h > 0`. -/
noncomputable def heatLin {h : ℝ} (hh : 0 < h) : L2s d →ₗ[ℝ] L2s d where
  toFun f := (memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)).toLp (heatOp h f)
  map_add' f g := by
    have h1 : heatOp h ⇑(f + g) = fun y => heatOp h ⇑f y + heatOp h ⇑g y :=
      (torusConv_congr_ae _ (Lp.coeFn_add f g)).trans
        (heatOp_add_fun hh ((Lp.memLp f).integrable one_le_two)
          ((Lp.memLp g).integrable one_le_two))
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_heatOp hh one_le_two (by simp) (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)).toLp (heatOp h f))
        ((memLp_heatOp hh one_le_two (by simp) (Lp.memLp g)).toLp (heatOp h g)),
      MemLp.coeFn_toLp (memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_heatOp hh one_le_two (by simp) (Lp.memLp g))] with y hy1 hy2 hy3 hy4
    rw [hy1, hy2, Pi.add_apply, hy3, hy4, h1]
  map_smul' c f := by
    have h1 : heatOp h ⇑(c • f) = fun y => c * heatOp h ⇑f y :=
      (torusConv_congr_ae _ (Lp.coeFn_smul c f)).trans (heatOp_smul_fun c _)
    refine Lp.ext ?_
    simp only [RingHom.id_apply]
    filter_upwards [MemLp.coeFn_toLp (memLp_heatOp hh one_le_two (by simp) (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)).toLp (heatOp h f)),
      MemLp.coeFn_toLp (memLp_heatOp hh one_le_two (by simp) (Lp.memLp f))] with y hy1 hy2 hy3
    rw [hy1, hy2, Pi.smul_apply, hy3, h1]
    rfl

theorem heatLin_apply {h : ℝ} (hh : 0 < h) (f : L2s d) :
    heatLin hh f = (memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)).toLp (heatOp h f) := rfl

theorem norm_heatLin_le {h : ℝ} (hh : 0 < h) (f : L2s d) : ‖heatLin hh f‖ ≤ ‖f‖ := by
  rw [heatLin_apply, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_heatOp_le hh one_le_two (by simp) (Lp.memLp f))

/-- The heat semigroup on `L²(𝕋^d)`: `H_h` for `h > 0`, and the identity for `h ≤ 0`. -/
noncomputable def heatCLM (h : ℝ) : L2s d →L[ℝ] L2s d :=
  if hh : 0 < h then LinearMap.mkContinuous (heatLin hh) 1 (fun f => by
    simpa using norm_heatLin_le hh f)
  else ContinuousLinearMap.id ℝ _

theorem heatCLM_of_pos {h : ℝ} (hh : 0 < h) (f : L2s d) :
    heatCLM h f = (memLp_heatOp hh one_le_two (by simp) (Lp.memLp f)).toLp (heatOp h f) := by
  simp only [heatCLM, hh, ↓reduceDIte]
  rfl

theorem heatCLM_of_nonpos {h : ℝ} (hh : h ≤ 0) (f : L2s d) : heatCLM h f = f := by
  simp [heatCLM, not_lt.mpr hh]

theorem heatCLM_zero (f : L2s d) : heatCLM 0 f = f := heatCLM_of_nonpos le_rfl f

theorem coeFn_heatCLM {h : ℝ} (hh : 0 < h) (f : L2s d) :
    ⇑(heatCLM h f) =ᵐ[haar d] heatOp h ⇑f := by
  rw [heatCLM_of_pos hh]
  exact MemLp.coeFn_toLp _

theorem norm_heatCLM_apply_le {h : ℝ} (hh : 0 ≤ h) (f : L2s d) : ‖heatCLM h f‖ ≤ ‖f‖ := by
  rcases hh.eq_or_lt with h0 | hpos
  · rw [← h0, heatCLM_zero]
  · rw [heatCLM_of_pos hpos]
    exact norm_heatLin_le hpos f

theorem opNorm_heatCLM_le {h : ℝ} (hh : 0 ≤ h) : ‖(heatCLM h : L2s d →L[ℝ] L2s d)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa using norm_heatCLM_apply_le hh f

theorem heatCLM_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (f : L2s d) :
    heatCLM (a + b) f = heatCLM a (heatCLM b f) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, heatCLM_zero, add_zero]
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0, heatCLM_zero, zero_add]
  have hab : 0 < a + b := add_pos hapos hbpos
  refine Lp.ext ?_
  filter_upwards [coeFn_heatCLM hab f, coeFn_heatCLM hapos (heatCLM b f)] with y hy1 hy2
  rw [hy1, hy2, show heatOp a ⇑(heatCLM b f) = heatOp a (heatOp b ⇑f) from
    torusConv_congr_ae _ (coeFn_heatCLM hbpos f), heatOp_add hapos hbpos
    ((Lp.memLp f).integrable one_le_two)]

theorem tendsto_heatCLM (f : L2s d) :
    Tendsto (fun δ : ℝ => heatCLM δ f) (𝓝[>] 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := ((tendsto_integral_sq_heatOp_sub (Lp.memLp f)).sqrt)
  rw [Real.sqrt_zero] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  rw [← Real.sqrt_sq (norm_nonneg (heatCLM δ f - f)), norm_Lp_two_sq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (heatCLM δ f) f, coeFn_heatCLM hδ' f] with y hy1 hy2
  rw [hy1, Pi.sub_apply, hy2, Real.norm_eq_abs, sq_abs]

theorem continuousOn_heatCLM (f : L2s d) : ContinuousOn (fun h => heatCLM h f) (Ici 0) :=
  continuousOn_Ici_of_semigroup (fun h => heatCLM h)
    (fun _ ha f => norm_heatCLM_apply_le ha f) (fun _ _ ha hb f => heatCLM_add ha hb f)
    heatCLM_zero tendsto_heatCLM f

/-! ### The vector heat operator on `L²(𝕋^d;ℝ^d)` -/

theorem heatGrad_apply (h : ℝ) (g : Torus d → Tangent d) (y : Torus d) (j : Fin d) :
    heatGrad h g y j = heatOp h (fun z => g z j) y := rfl

theorem heatGrad_congr_ae (h : ℝ) {F G : Torus d → Tangent d} (hFG : F =ᵐ[haar d] G) :
    heatGrad h F = heatGrad h G := by
  funext y
  ext j
  rw [heatGrad_apply, heatGrad_apply]
  exact congrFun (torusConv_congr_ae (heatKernelT h) (hFG.mono fun w hw => by simp [hw])) y

theorem integrable_coord {F : Torus d → Tangent d} (hF : Integrable F (haar d)) (j : Fin d) :
    Integrable (fun w => F w j) (haar d) :=
  (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integrable_comp hF

theorem heatGrad_add_fun {h : ℝ} (hh : 0 < h) {F G : Torus d → Tangent d}
    (hF : Integrable F (haar d)) (hG : Integrable G (haar d)) :
    heatGrad h (fun w => F w + G w) = fun y => heatGrad h F y + heatGrad h G y := by
  funext y
  ext j
  rw [PiLp.add_apply, heatGrad_apply, heatGrad_apply, heatGrad_apply]
  have := congrFun (heatOp_add_fun hh (integrable_coord hF j) (integrable_coord hG j)) y
  simpa using this

theorem heatGrad_smul_fun (h : ℝ) (c : ℝ) (F : Torus d → Tangent d) :
    heatGrad h (fun w => c • F w) = fun y => c • heatGrad h F y := by
  funext y
  ext j
  rw [PiLp.smul_apply, heatGrad_apply, heatGrad_apply]
  have := congrFun (heatOp_smul_fun (h := h) c (fun z => F z j)) y
  simpa using this

/-- The linear operator `F ↦ H_h F` (componentwise) on `L²(𝕋^d;ℝ^d)`, for `h > 0`. -/
noncomputable def heatGradLin {h : ℝ} (hh : 0 < h) : L2v d →ₗ[ℝ] L2v d where
  toFun F := (memLp_heatGrad hh (Lp.memLp F)).toLp (heatGrad h F)
  map_add' F G := by
    have h1 : heatGrad h ⇑(F + G) = fun y => heatGrad h ⇑F y + heatGrad h ⇑G y :=
      (heatGrad_congr_ae h (Lp.coeFn_add F G)).trans
        (heatGrad_add_fun hh ((Lp.memLp F).integrable one_le_two)
          ((Lp.memLp G).integrable one_le_two))
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp (F + G))),
      Lp.coeFn_add ((memLp_heatGrad hh (Lp.memLp F)).toLp (heatGrad h F))
        ((memLp_heatGrad hh (Lp.memLp G)).toLp (heatGrad h G)),
      MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp F)),
      MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp G))] with y hy1 hy2 hy3 hy4
    rw [hy1, hy2, Pi.add_apply, hy3, hy4, h1]
  map_smul' c F := by
    have h1 : heatGrad h ⇑(c • F) = fun y => c • heatGrad h ⇑F y :=
      (heatGrad_congr_ae h (Lp.coeFn_smul c F)).trans (heatGrad_smul_fun h c _)
    refine Lp.ext ?_
    simp only [RingHom.id_apply]
    filter_upwards [MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp (c • F))),
      Lp.coeFn_smul c ((memLp_heatGrad hh (Lp.memLp F)).toLp (heatGrad h F)),
      MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp F))] with y hy1 hy2 hy3
    rw [hy1, hy2, Pi.smul_apply, hy3, h1]

theorem heatGradLin_apply {h : ℝ} (hh : 0 < h) (F : L2v d) :
    heatGradLin hh F = (memLp_heatGrad hh (Lp.memLp F)).toLp (heatGrad h F) := rfl

theorem norm_heatGradLin_le {h : ℝ} (hh : 0 < h) (F : L2v d) : ‖heatGradLin hh F‖ ≤ ‖F‖ := by
  have hcomp : ∀ j : Fin d, MemLp (fun x => F x j) 2 (haar d) := fun j => memLp_coord (Lp.memLp F) j
  have key : ‖heatGradLin hh F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [norm_Lp_two_sq, norm_Lp_two_sq]
    have e1 : ∫ x, ‖(heatGradLin hh F) x‖ ^ 2 ∂haar d = ∫ x, ‖heatGrad h ⇑F x‖ ^ 2 ∂haar d := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_heatGrad hh (Lp.memLp F))] with y hy
      rw [heatGradLin_apply, hy]
    rw [e1]
    simp_rw [tangent_norm_sq, heatGrad_apply]
    rw [integral_finsetSum _ fun j _ => ((memLp_heatOp hh one_le_two (by simp) (hcomp j)).integrable_sq),
      integral_finsetSum _ fun j _ => (hcomp j).integrable_sq]
    exact Finset.sum_le_sum fun j _ => integral_sq_heatOp_le hh (hcomp j)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

/-- The heat semigroup on `L²(𝕋^d;ℝ^d)` (componentwise): `H_h` for `h > 0`, identity for
`h ≤ 0`. -/
noncomputable def heatGradCLM (h : ℝ) : L2v d →L[ℝ] L2v d :=
  if hh : 0 < h then LinearMap.mkContinuous (heatGradLin hh) 1 (fun F => by
    simpa using norm_heatGradLin_le hh F)
  else ContinuousLinearMap.id ℝ _

theorem heatGradCLM_of_pos {h : ℝ} (hh : 0 < h) (F : L2v d) :
    heatGradCLM h F = (memLp_heatGrad hh (Lp.memLp F)).toLp (heatGrad h F) := by
  simp only [heatGradCLM, hh, ↓reduceDIte]
  rfl

theorem heatGradCLM_of_nonpos {h : ℝ} (hh : h ≤ 0) (F : L2v d) : heatGradCLM h F = F := by
  simp [heatGradCLM, not_lt.mpr hh]

theorem heatGradCLM_zero (F : L2v d) : heatGradCLM 0 F = F := heatGradCLM_of_nonpos le_rfl F

theorem coeFn_heatGradCLM {h : ℝ} (hh : 0 < h) (F : L2v d) :
    ⇑(heatGradCLM h F) =ᵐ[haar d] heatGrad h ⇑F := by
  rw [heatGradCLM_of_pos hh]
  exact MemLp.coeFn_toLp _

theorem norm_heatGradCLM_apply_le {h : ℝ} (hh : 0 ≤ h) (F : L2v d) :
    ‖heatGradCLM h F‖ ≤ ‖F‖ := by
  rcases hh.eq_or_lt with h0 | hpos
  · rw [← h0, heatGradCLM_zero]
  · rw [heatGradCLM_of_pos hpos]
    exact norm_heatGradLin_le hpos F

theorem opNorm_heatGradCLM_le {h : ℝ} (hh : 0 ≤ h) :
    ‖(heatGradCLM h : L2v d →L[ℝ] L2v d)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun F => by
    simpa using norm_heatGradCLM_apply_le hh F

theorem heatGradCLM_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (F : L2v d) :
    heatGradCLM (a + b) F = heatGradCLM a (heatGradCLM b F) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [← hb0, heatGradCLM_zero, add_zero]
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0, heatGradCLM_zero, zero_add]
  have hab : 0 < a + b := add_pos hapos hbpos
  refine Lp.ext ?_
  filter_upwards [coeFn_heatGradCLM hab F, coeFn_heatGradCLM hapos (heatGradCLM b F)] with y hy1 hy2
  rw [hy1, hy2, heatGrad_congr_ae a (coeFn_heatGradCLM hbpos F)]
  ext j
  rw [heatGrad_apply, heatGrad_apply]
  have := congrFun (heatOp_add hapos hbpos
    (integrable_coord ((Lp.memLp F).integrable one_le_two) j)) y
  rw [← this]
  rfl

theorem tendsto_heatGradCLM (F : L2v d) :
    Tendsto (fun δ : ℝ => heatGradCLM δ F) (𝓝[>] 0) (𝓝 F) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := ((tendsto_integral_norm_sq_heatGrad_sub (Lp.memLp F)).sqrt)
  rw [Real.sqrt_zero] at h0
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  rw [← Real.sqrt_sq (norm_nonneg (heatGradCLM δ F - F)), norm_Lp_two_sq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (heatGradCLM δ F) F, coeFn_heatGradCLM hδ' F] with y hy1 hy2
  rw [hy1, Pi.sub_apply, hy2]

theorem continuousOn_heatGradCLM (F : L2v d) : ContinuousOn (fun h => heatGradCLM h F) (Ici 0) :=
  continuousOn_Ici_of_semigroup (fun h => heatGradCLM h)
    (fun _ ha F => norm_heatGradCLM_apply_le ha F) (fun _ _ ha hb F => heatGradCLM_add ha hb F)
    heatGradCLM_zero tendsto_heatGradCLM F

/-! ### Composition with the divergence and the Duhamel kernel instance -/

theorem divHeat_add_comp {τ h : ℝ} (hτ : 0 < τ) (hh : 0 ≤ h) :
    (divHeat (τ + h) : L2v d →L[ℝ] L2s d) = (divHeat τ).comp (heatGradCLM h) := by
  ext1 F
  rcases hh.eq_or_lt with h0 | hpos
  · subst h0
    simp [heatGradCLM_zero]
  · have hτh : 0 < τ + h := add_pos hτ hpos
    refine Lp.ext ?_
    simp only [ContinuousLinearMap.comp_apply]
    filter_upwards [coeFn_divHeat hτh F, coeFn_divHeat hτ (heatGradCLM h F)] with y hy1 hy2
    rw [hy1, hy2, divHeatFun_congr_ae τ (coeFn_heatGradCLM hpos F)]
    unfold divHeatFun
    refine Finset.sum_congr rfl fun j _ => ?_
    have := heatOp_add hτ hpos (integrable_coord ((Lp.memLp F).integrable one_le_two) j)
    rw [← this]
    rfl

theorem divHeat_duhamelKernel :
    DuhamelKernel (fun t : ℝ => (divHeat t : L2v d →L[ℝ] L2s d)) (Real.sqrt (d / 2)) where
  nonneg := Real.sqrt_nonneg _
  bound τ hτ w := norm_divHeat_apply_le hτ w
  cont w := by
    intro τ0 hτ0
    have hτ0' : 0 < τ0 := hτ0
    have hc : ContinuousOn (fun τ : ℝ => (divHeat (τ0 / 2) : L2v d →L[ℝ] L2s d)
        (heatGradCLM (τ - τ0 / 2) w)) (Ioi (τ0 / 2)) :=
      (divHeat (τ0 / 2) : L2v d →L[ℝ] L2s d).continuous.comp_continuousOn
        ((continuousOn_heatGradCLM w).comp (continuousOn_id.sub continuousOn_const)
          fun τ hτ => by simpa using (sub_nonneg.mpr (le_of_lt (mem_Ioi.mp hτ))))
    have hc2 : ContinuousOn (fun τ : ℝ => (divHeat τ : L2v d →L[ℝ] L2s d) w) (Ioi (τ0 / 2)) := by
      refine hc.congr fun τ hτ => ?_
      have hτ' : τ0 / 2 < τ := hτ
      have := divHeat_add_comp (d := d) (half_pos hτ0') (sub_nonneg.mpr hτ'.le)
      rw [add_sub_cancel] at this
      rw [this]
      rfl
    exact (hc2.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-! ### The `L²`-valued heat flow -/

/-- The heat flow of an `L²` initial datum, `t ↦ H_t ρ₀`. -/
noncomputable def heatL2 (ρ0 : L2s d) (t : ℝ) : L2s d := heatCLM t ρ0

theorem heatL2_zero (ρ0 : L2s d) : heatL2 ρ0 0 = ρ0 := heatCLM_zero ρ0

theorem continuousOn_heatL2 (ρ0 : L2s d) : ContinuousOn (heatL2 ρ0) (Ici 0) :=
  continuousOn_heatCLM ρ0

theorem norm_heatL2_le (ρ0 : L2s d) {t : ℝ} (ht : 0 ≤ t) : ‖heatL2 ρ0 t‖ ≤ ‖ρ0‖ :=
  norm_heatCLM_apply_le ht ρ0

theorem coeFn_heatL2 (ρ0 : L2s d) {t : ℝ} (ht : 0 < t) :
    ⇑(heatL2 ρ0 t) =ᵐ[haar d] heatOp t ⇑ρ0 :=
  coeFn_heatCLM ht ρ0

end DGPS.Lipschitz
