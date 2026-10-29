import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Paper.EntFinite

/-!
# `H¹(𝕋) ⊂ L^∞`: `|u - ū| ≤ ‖u'‖₁` a.e. (Phase 3, lane C)

For smooth periodic `v`: `|v(x) - v(y)| ≤ ∫|v'|` (fundamental theorem of calculus on one period).
For `u ∈ H¹(m)`: apply this to the mollifications (whose derivatives are mollified weak
derivatives, an `L¹` contraction) and pass to an a.e. limit.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-- The line `s ↦ (s)` in `Fin 1 → ℝ`. -/
def lineF (s : ℝ) : Fin 1 → ℝ := fun _ => s

theorem secT_eq_lineF (y : Torus 1) : secT y = lineF (secT y 0) := by
  funext i; rw [Subsingleton.elim i 0]; rfl

theorem integral_torus1_secT (g : ℝ → ℝ) :
    ∫ y : Torus 1, g (secT y 0) = ∫ t in Ioc (0 : ℝ) 1, g t := by
  have := integral_torus1 (fun z => g ((AddCircle.equivIoc 1 0 z : ℝ)))
  rw [show (fun y : Torus 1 => g (secT y 0)) =
    fun y => g ((AddCircle.equivIoc 1 0 (y 0) : ℝ)) from rfl, this]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  congr 1
  have : AddCircle.equivIoc 1 0 (t : UnitAddCircle) = ⟨t, by simpa using ht⟩ :=
    AddCircle.equivIoc_coe_eq (by simpa using ht)
  rw [this]

/-- For smooth periodic `v`: `|v x - v y| ≤ ∫ |v'|`. -/
theorem abs_sub_le_of_contDiff {v : Torus 1 → ℝ} (hv : ContDiff ℝ 1 (v ∘ liftT)) (x y : Torus 1) :
    |v x - v y| ≤ ∫ z, |fderiv ℝ (v ∘ liftT) (secT z) (Pi.single 0 1)| := by
  set Φ := v ∘ liftT
  set V : ℝ → ℝ := fun s => Φ (lineF s) with hV
  have hline : ∀ s, HasDerivAt (fun r : ℝ => lineF r) (Pi.single 0 1) s := by
    intro s
    have : (fun r : ℝ => lineF r) = fun r => r • (Pi.single 0 1 : Fin 1 → ℝ) := by
      funext r i; rw [Subsingleton.elim i 0]; simp [lineF]
    rw [this]
    simpa using (hasDerivAt_id s).smul_const (Pi.single 0 1 : Fin 1 → ℝ)
  have hVd : ∀ s, HasDerivAt V (fderiv ℝ Φ (lineF s) (Pi.single 0 1)) s := fun s =>
    ((hv.differentiable one_ne_zero) (lineF s)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hVc : Continuous fun s => fderiv ℝ Φ (lineF s) (Pi.single 0 1) :=
    ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (continuous_pi fun _ => continuous_id)
  have hvx : ∀ z, v z = V (secT z 0) := fun z => by
    simp only [hV, Φ, Function.comp_apply, ← secT_eq_lineF, liftT_secT]
  have hint : ∫ z, |fderiv ℝ Φ (secT z) (Pi.single 0 1)| =
      ∫ s in (0 : ℝ)..1, |fderiv ℝ Φ (lineF s) (Pi.single 0 1)| := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_torus1_secT]
    congr 1; funext z; rw [← secT_eq_lineF z]
  rw [hvx, hvx, hint]
  have hmem : ∀ z : Torus 1, secT z 0 ∈ Icc (0 : ℝ) 1 := fun z => by
    have := (AddCircle.measurableEquivIoc 1 0 (z 0)).2
    have h2 : ((AddCircle.measurableEquivIoc 1 0 (z 0) : ℝ)) ≤ 1 := by simpa using this.2
    exact ⟨this.1.le, h2⟩
  set a := secT x 0
  set b := secT y 0
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hVd s)
    (hVc.intervalIntegrable _ _)]
  set g : ℝ → ℝ := fun s => |fderiv ℝ Φ (lineF s) (Pi.single 0 1)| with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => abs_nonneg _
  have hgi : ∀ c d, IntervalIntegrable g volume c d := fun c d =>
    (continuous_abs.comp hVc).intervalIntegrable _ _
  have key : ∀ c d, c ∈ Icc (0 : ℝ) 1 → d ∈ Icc (0 : ℝ) 1 → c ≤ d →
      ∫ s in c..d, g s ≤ ∫ s in (0 : ℝ)..1, g s := fun c d hc hd hcd =>
    intervalIntegral.integral_mono_interval hc.1 hcd hd.2 (Eventually.of_forall hg0) (hgi 0 1)
  calc |∫ s in b..a, fderiv ℝ Φ (lineF s) (Pi.single 0 1)|
      ≤ |∫ s in b..a, g s| := by
        have := intervalIntegral.norm_integral_le_abs_integral_norm (a := b) (b := a)
          (f := fun s => fderiv ℝ Φ (lineF s) (Pi.single 0 1)) (μ := volume)
        simpa [Real.norm_eq_abs, hg] using this
    _ ≤ ∫ s in (0 : ℝ)..1, g s := by
        rcases le_total b a with hba | hab
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hba fun s _ => hg0 s)]
          exact key b a (hmem y) (hmem x) hba
        · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hab fun s _ => hg0 s)]
          exact key a b (hmem x) (hmem y) hab

/-- `H¹(𝕋) ⊂ L^∞`: `|u - ū| ≤ ∫ |u'|` a.e. -/
theorem ae_abs_sub_mean_le {u : Torus 1 → ℝ} (hu : MemH1 volume u) :
    ∀ᵐ x ∂(volume : Measure (Torus 1)), |u x - ∫ y, u y| ≤ ∫ y, |weakGrad u y 0| := by
  have hw := isWeakGrad_weakGrad hu.1
  have hui : Integrable u volume := hu.2.1.integrable one_le_two
  have hg2 : MemLp (fun y => weakGrad u y 0) 2 volume :=
    hu.2.2.of_le (hw.aestronglyMeasurable_grad 0) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ 0)
  have hgi : Integrable (fun y => weakGrad u y 0) volume := hg2.integrable one_le_two
  set Lg := ∫ y, |weakGrad u y 0| with hLg
  -- the bound for the mollifications
  have hn : ∀ n x y, |moll n u x - moll n u y| ≤ Lg := by
    intro n x y
    have hs : ContDiff ℝ 1 (moll n u ∘ liftT) := (moll_comp_liftT_contDiff n hui).of_le (by simp)
    refine (abs_sub_le_of_contDiff hs x y).trans ?_
    have hd : ∀ z, fderiv ℝ (moll n u ∘ liftT) (secT z) (Pi.single 0 1) =
        moll n (fun z => weakGrad u z 0) z := by
      intro z; rw [moll_comp_liftT, fderiv_mollL_of_isWeakGrad hw n (secT z) 0]; rfl
    simp_rw [hd]
    have h1 := lintegral_moll_le n hgi
    have hm := integrable_moll n hgi
    rw [hLg, integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable |> fun h =>
      (show ∫ z, |moll n (fun z => weakGrad u z 0) z| =
        (∫⁻ z, ‖moll n (fun z => weakGrad u z 0) z‖ₑ).toReal by simpa [Real.norm_eq_abs] using h),
      show ∫ y, |weakGrad u y 0| = (∫⁻ y, ‖weakGrad u y 0‖ₑ).toReal by
        simpa [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm hgi.aestronglyMeasurable]
    exact ENNReal.toReal_mono hgi.2.ne h1
  -- a.e. convergence along a subsequence
  obtain ⟨ns, -, hae⟩ := exists_subseq_ae_of_tendsto_lintegral
    (fun n => (measurable_moll n hui).aestronglyMeasurable) hui.aestronglyMeasurable
    (tendsto_moll hui)
  have hpair : ∀ x y, Tendsto (fun k => moll (ns k) u x) atTop (𝓝 (u x)) →
      Tendsto (fun k => moll (ns k) u y) atTop (𝓝 (u y)) → |u x - u y| ≤ Lg := by
    intro x y hx hy
    exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hx.sub hy)) fun k => hn (ns k) x y
  filter_upwards [hae] with x hx
  have hy : ∀ᵐ y ∂(volume : Measure (Torus 1)), |u x - u y| ≤ Lg := by
    filter_upwards [hae] with y hy
    exact hpair x y hx hy
  calc |u x - ∫ y, u y| = |∫ y, (u x - u y)| := by
        rw [integral_sub (integrable_const _) hui, integral_const]; simp
    _ ≤ ∫ y, |u x - u y| := abs_integral_le_integral_abs
    _ ≤ ∫ _y, Lg := integral_mono_ae ((integrable_const _).sub hui).abs (integrable_const _) hy
    _ = Lg := by simp

end SharpLSI
