import DGPS.Equilibrium.Hessian
import DGPS.Variational.FrozenGibbs
import DGPS.Foundations.TotalVariation

/-!
# STR005: derivative, compactness and quadratic remainder of the frozen Gibbs map

`X = zeroMass d` is the Banach space of finite signed Borel measures on the torus with total mass
zero, in the FULL variation norm (`SMeas d` is a type synonym of `SignedMeasure (Torus d)` carrying
that norm, since Mathlib has no normed space of signed measures).

Route change (recorded, as allowed by the spec): a self-contained proof.  Fix `μ`.  The map
`η ↦ P(μ+η) − Pμ` is defined on ALL of `X` by the explicit density formula
`q(e^{-h}/N − 1)` (`h = W*η`, `q` the density of `Pμ`), extended from the genuine map
(`frozenGibbsExt_eq`).  Then `frozenGibbsDeriv A μ η` has density `-q (h − ∫ q h)`; the Fréchet
derivative, a uniform quadratic remainder `10 Wb² ‖η‖²` for `Wb‖η‖ ≤ 1/4`, and compactness (via
Arzelà–Ascoli for the convolution operator `X → C(T^d)`) are proved without any hypothesis.  The
hypothesis `μ = Pμ` is used only to identify the derivative with
`-q(x) ∫ K(x,y) dη(y) dm(x)`, `K` the centered kernel at `μ` (`frozenGibbsDeriv_eq_kernel`).
-/


open MeasureTheory VectorMeasure Set
open scoped BoundedContinuousFunction

namespace DGPS.Structural

variable {d : ℕ}

/-- The vector space of finite signed Borel measures on the torus (a type synonym of
`SignedMeasure`, to carry the full-variation norm). -/
def SMeas (d : ℕ) : Type := SignedMeasure (Torus d)

noncomputable instance : AddCommGroup (SMeas d) :=
  inferInstanceAs (AddCommGroup (SignedMeasure (Torus d)))
noncomputable instance : Module ℝ (SMeas d) :=
  inferInstanceAs (Module ℝ (SignedMeasure (Torus d)))

/-- The identification `SMeas d = SignedMeasure (Torus d)` as a linear equivalence. -/
noncomputable def SMeas.equiv : SMeas d ≃ₗ[ℝ] SignedMeasure (Torus d) := LinearEquiv.refl ℝ _

instance (s : SignedMeasure (Torus d)) : IsFiniteMeasure s.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]; infer_instance

/-- The full-variation norm `‖s‖ = |s|(𝕋^d)`. -/
noncomputable def SMeas.fvar (s : SMeas d) : ℝ := (SMeas.equiv s).variation.real univ

theorem SMeas.fvar_nonneg (s : SMeas d) : 0 ≤ s.fvar := measureReal_nonneg

theorem SMeas.fvar_add_le (s t : SMeas d) : (s + t).fvar ≤ s.fvar + t.fvar := by
  unfold SMeas.fvar
  have h := VectorMeasure.variation_add_le (μ := SMeas.equiv s) (ν := SMeas.equiv t)
  rw [LinearEquiv.map_add]
  have h2 := h univ
  simp only [Measure.add_apply] at h2
  have := ENNReal.toReal_mono (by finiteness) h2
  rwa [ENNReal.toReal_add (by finiteness) (by finiteness)] at this

theorem SMeas.equiv_neg (s : SMeas d) : SMeas.equiv (-s) = -SMeas.equiv s := rfl

theorem SMeas.equiv_symm_sub (a b : SignedMeasure (Torus d)) :
    (SMeas.equiv (d := d)).symm (a - b) = SMeas.equiv.symm a - SMeas.equiv.symm b := rfl

theorem SMeas.fvar_neg (s : SMeas d) : (-s).fvar = s.fvar := by
  unfold SMeas.fvar
  rw [SMeas.equiv_neg, VectorMeasure.variation_neg]

theorem SMeas.fvar_smul (c : ℝ) (s : SMeas d) : (c • s).fvar = |c| * s.fvar := by
  unfold SMeas.fvar
  rw [LinearEquiv.map_smul, VectorMeasure.variation_smul]
  simp [Measure.real, ENNReal.toReal_mul]

theorem SMeas.apply_le_fvar (s : SMeas d) (E : Set (Torus d)) : |SMeas.equiv s E| ≤ s.fvar := by
  unfold SMeas.fvar
  have h := VectorMeasure.enorm_measure_le_variation (SMeas.equiv s) E
  have h2 := h.trans (measure_mono (Set.subset_univ E) : (SMeas.equiv s).variation E ≤ _)
  have := ENNReal.toReal_mono (by finiteness) h2
  simpa [Measure.real, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using this

theorem SMeas.eq_zero_of_fvar_eq_zero (s : SMeas d) (h : s.fvar = 0) : s = 0 := by
  have : ∀ E, SMeas.equiv s E = 0 := fun E => by
    have := SMeas.apply_le_fvar s E
    rw [h] at this
    exact abs_nonpos_iff.1 this
  apply SMeas.equiv.injective
  ext E hE
  simpa using this E

noncomputable instance : NormedAddCommGroup (SMeas d) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := SMeas.fvar
      map_zero' := by simp [SMeas.fvar]
      add_le' := SMeas.fvar_add_le
      neg' := SMeas.fvar_neg
      eq_zero_of_map_eq_zero' := SMeas.eq_zero_of_fvar_eq_zero }

theorem SMeas.norm_def (s : SMeas d) : ‖s‖ = s.fvar := rfl

noncomputable instance : NormedSpace ℝ (SMeas d) where
  norm_smul_le c s := by
    rw [SMeas.norm_def, SMeas.norm_def, SMeas.fvar_smul, Real.norm_eq_abs]


/-! ### The zero-mass subspace -/

/-- The total mass of a finite signed measure. -/
noncomputable def SMeas.massCLM (d : ℕ) : SMeas d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun s => SMeas.equiv s univ
      map_add' := fun s t => by simp
      map_smul' := fun c s => by simp }
    1 (fun s => by
      have := SMeas.apply_le_fvar s univ
      simpa [SMeas.norm_def] using this)

theorem SMeas.massCLM_apply (s : SMeas d) : SMeas.massCLM d s = SMeas.equiv s univ := rfl

/-- The closed subspace `X` of finite signed measures of total mass zero. -/
noncomputable def zeroMass (d : ℕ) : Submodule ℝ (SMeas d) := LinearMap.ker (SMeas.massCLM d : SMeas d →ₗ[ℝ] ℝ)

theorem mem_zeroMass {s : SMeas d} : s ∈ zeroMass d ↔ SMeas.equiv s univ = 0 := by
  simp [zeroMass, SMeas.massCLM_apply]

theorem isClosed_zeroMass : IsClosed (zeroMass d : Set (SMeas d)) :=
  isClosed_singleton.preimage (SMeas.massCLM d).continuous

/-- Full variation of `ν - η` is the norm of the signed measure `ν - η`. -/
theorem norm_toSignedMeasure_sub (ν η : Measure (Torus d)) [IsFiniteMeasure ν] [IsFiniteMeasure η] :
    ‖SMeas.equiv.symm (ν.toSignedMeasure - η.toSignedMeasure)‖ = fullVariation ν η := by
  rw [SMeas.norm_def, SMeas.fvar, LinearEquiv.apply_symm_apply, fullVariation,
    ← SignedMeasure.totalVariation_eq_variation]

/-! ### Integration against a finite signed measure -/

/-- `∫ f ds` for a finite signed measure. -/
noncomputable def SMeas.integral (s : SMeas d) (f : Torus d → ℝ) : ℝ :=
  ∫ᵛ y, f y ∂•(SMeas.equiv s)

theorem SMeas.integrable_of_continuous (s : SMeas d) {f : Torus d → ℝ} (hf : Continuous f) :
    (SMeas.equiv s).Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem SMeas.abs_integral_le (s : SMeas d) {f : Torus d → ℝ} {C : ℝ} (hf : ∀ y, |f y| ≤ C) :
    |s.integral f| ≤ C * ‖s‖ := by
  have := VectorMeasure.norm_integral_le_of_norm_le_const (μ := SMeas.equiv s)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := f) (C := C)
    (Filter.Eventually.of_forall fun y => by simpa using hf y)
  rw [Real.norm_eq_abs, ContinuousLinearMap.opNorm_lsmul ℝ ℝ, mul_one] at this
  exact this

theorem SMeas.integral_add_left (s t : SMeas d) {f : Torus d → ℝ} (hf : Continuous f) :
    (s + t).integral f = s.integral f + t.integral f := by
  unfold SMeas.integral
  rw [LinearEquiv.map_add, integral_add_vectorMeasure (SMeas.integrable_of_continuous s hf)
    (SMeas.integrable_of_continuous t hf)]

theorem SMeas.integral_neg_left (s : SMeas d) (f : Torus d → ℝ) :
    (-s).integral f = -s.integral f := by
  unfold SMeas.integral
  rw [SMeas.equiv_neg, integral_neg_vectorMeasure]

theorem SMeas.integral_smul_left (c : ℝ) (s : SMeas d) (f : Torus d → ℝ) :
    (c • s).integral f = c * s.integral f := by
  unfold SMeas.integral
  rw [LinearEquiv.map_smul, integral_smul_vectorMeasure]
  rfl

theorem SMeas.integral_sub_left (s t : SMeas d) {f : Torus d → ℝ} (hf : Continuous f) :
    (s - t).integral f = s.integral f - t.integral f := by
  rw [sub_eq_add_neg, SMeas.integral_add_left _ _ hf, SMeas.integral_neg_left, ← sub_eq_add_neg]

theorem SMeas.integral_zero_left (f : Torus d → ℝ) : (0 : SMeas d).integral f = 0 := by
  have := SMeas.integral_smul_left 0 (0 : SMeas d) f
  simpa using this

theorem SMeas.integral_add_fun (s : SMeas d) {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) : s.integral (fun y => f y + g y) = s.integral f + s.integral g := by
  unfold SMeas.integral
  exact integral_fun_add (SMeas.integrable_of_continuous s hf)
    (SMeas.integrable_of_continuous s hg)

theorem SMeas.integral_sub_fun (s : SMeas d) {f g : Torus d → ℝ} (hf : Continuous f)
    (hg : Continuous g) : s.integral (fun y => f y - g y) = s.integral f - s.integral g := by
  unfold SMeas.integral
  exact integral_fun_sub (SMeas.integrable_of_continuous s hf)
    (SMeas.integrable_of_continuous s hg)

theorem SMeas.integral_smul_fun (s : SMeas d) (c : ℝ) (f : Torus d → ℝ) :
    s.integral (fun y => c * f y) = c * s.integral f := by
  unfold SMeas.integral
  exact integral_fun_smul _ _ c f

theorem SMeas.integral_const (s : SMeas d) (c : ℝ) :
    s.integral (fun _ => c) = c * SMeas.equiv s univ := by
  simp [SMeas.integral]

theorem SMeas.abs_integral_sub_le (s : SMeas d) (f g : C(Torus d, ℝ)) :
    |s.integral f - s.integral g| ≤ ‖s‖ * ‖f - g‖ := by
  rw [← SMeas.integral_sub_fun s f.continuous g.continuous]
  have := SMeas.abs_integral_le s (f := fun y => f y - g y) (C := ‖f - g‖) (fun y => by
    have := ContinuousMap.norm_coe_le_norm (f - g) y
    simpa using this)
  linarith [mul_comm ‖f - g‖ ‖s‖]

/-! ### Densities and the map `f ↦ f m` -/

theorem integrable_of_cont {g : Torus d → ℝ} (hg : Continuous g) : Integrable g (haar d) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The signed measure `g m` with density `g` with respect to Haar measure. -/
noncomputable def ofDensity (g : Torus d → ℝ) : SMeas d :=
  SMeas.equiv.symm ((haar d).withDensityᵥ g)

theorem ofDensity_add {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ofDensity (fun x => f x + g x) = ofDensity f + ofDensity g := by
  unfold ofDensity
  rw [withDensityᵥ_add' (integrable_of_cont hf) (integrable_of_cont hg)]
  exact LinearEquiv.map_add _ _ _

theorem ofDensity_sub {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ofDensity (fun x => f x - g x) = ofDensity f - ofDensity g := by
  unfold ofDensity
  rw [withDensityᵥ_sub' (integrable_of_cont hf) (integrable_of_cont hg)]
  exact SMeas.equiv_symm_sub _ _

theorem ofDensity_smul (c : ℝ) (f : Torus d → ℝ) :
    ofDensity (fun x => c * f x) = c • ofDensity f := by
  unfold ofDensity
  have := withDensityᵥ_smul' (μ := haar d) f c
  simp only [smul_eq_mul] at this
  rw [this]
  exact LinearEquiv.map_smul _ _ _

theorem equiv_ofDensity_univ {g : Torus d → ℝ} (hg : Continuous g) :
    SMeas.equiv (ofDensity g) univ = ∫ x, g x ∂haar d := by
  unfold ofDensity
  rw [LinearEquiv.apply_symm_apply, withDensityᵥ_apply (integrable_of_cont hg) MeasurableSet.univ,
    Measure.restrict_univ]

theorem norm_ofDensity {g : Torus d → ℝ} (hg : Continuous g) :
    ‖ofDensity g‖ = ∫ x, |g x| ∂haar d := by
  rw [SMeas.norm_def, SMeas.fvar]
  unfold ofDensity
  rw [LinearEquiv.apply_symm_apply, Measure.variation_withDensityᵥ (integrable_of_cont hg),
    Measure.real, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have := integral_norm_eq_lintegral_enorm (μ := haar d) hg.aestronglyMeasurable
  simp only [Real.norm_eq_abs] at this
  exact this.symm

/-! ### The interaction convolution against a signed measure -/

section Model

variable (A : InteractionData d)

theorem continuous_W_right (x : Torus d) : Continuous (fun y => A.W x y) :=
  A.W_continuous.comp (continuous_const.prodMk continuous_id)

/-- `(W * s)(x) = ∫ W(x, y) ds(y)`. -/
noncomputable def wConv (s : SMeas d) (x : Torus d) : ℝ := s.integral (fun y => A.W x y)

/-- The curried interaction, `x ↦ W(x, ·) ∈ C(𝕋^d)`. -/
noncomputable def WC : C(Torus d, C(Torus d, ℝ)) :=
  ContinuousMap.curry ⟨fun p => A.W p.1 p.2, A.W_continuous⟩

theorem WC_apply (x y : Torus d) : WC A x y = A.W x y := rfl

/-- A uniform bound for `W`. -/
noncomputable def Wb : ℝ := |A.W_bounded.choose|

theorem abs_W_le (x y : Torus d) : |A.W x y| ≤ Wb A :=
  (A.W_bounded.choose_spec x y).trans (le_abs_self _)

theorem Wb_nonneg : 0 ≤ Wb A := abs_nonneg _

theorem abs_wConv_sub_le (s : SMeas d) (x x' : Torus d) :
    |wConv A s x - wConv A s x'| ≤ ‖s‖ * dist (WC A x) (WC A x') := by
  have := SMeas.abs_integral_sub_le s (WC A x) (WC A x')
  rw [← dist_eq_norm] at this
  exact this

theorem continuous_wConv (s : SMeas d) : Continuous (wConv A s) := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hc := (continuous_iff_continuousAt.1 (WC A).continuous x0).eventually
    (Metric.ball_mem_nhds (WC A x0) (show 0 < ε / (‖s‖ + 1) by positivity))
  filter_upwards [hc] with x hx
  rw [Real.dist_eq]
  have h1 := abs_wConv_sub_le A s x x0
  have h2 : dist (WC A x) (WC A x0) < ε / (‖s‖ + 1) := hx
  have hs : 0 ≤ ‖s‖ := norm_nonneg _
  calc |wConv A s x - wConv A s x0| ≤ ‖s‖ * dist (WC A x) (WC A x0) := h1
    _ ≤ ‖s‖ * (ε / (‖s‖ + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem abs_wConv_le (s : SMeas d) (x : Torus d) : |wConv A s x| ≤ Wb A * ‖s‖ := by
  have := SMeas.abs_integral_le s (f := fun y => A.W x y) (C := Wb A) (abs_W_le A x)
  exact this

theorem wConv_add (s t : SMeas d) (x : Torus d) :
    wConv A (s + t) x = wConv A s x + wConv A t x :=
  SMeas.integral_add_left s t (continuous_W_right A x)

theorem wConv_smul (c : ℝ) (s : SMeas d) (x : Torus d) :
    wConv A (c • s) x = c * wConv A s x :=
  SMeas.integral_smul_left c s _

theorem wConv_sub (s t : SMeas d) (x : Torus d) :
    wConv A (s - t) x = wConv A s x - wConv A t x :=
  SMeas.integral_sub_left s t (continuous_W_right A x)

/-- `W * s` as a bounded continuous function. -/
noncomputable def convBCF (s : SMeas d) : Torus d →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨wConv A s, continuous_wConv A s⟩

theorem convBCF_apply (s : SMeas d) (x : Torus d) : convBCF A s x = wConv A s x := rfl

/-- The bounded linear map `s ↦ W * s` from signed measures (full variation) to `C(𝕋^d)`. -/
noncomputable def convCLM : SMeas d →L[ℝ] (Torus d →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := convBCF A
      map_add' := fun s t => by ext x; simp [convBCF_apply, wConv_add]
      map_smul' := fun c s => by ext x; simp [convBCF_apply, wConv_smul] }
    (Wb A) (fun s => by
      refine (BoundedContinuousFunction.norm_le (mul_nonneg (Wb_nonneg A) (norm_nonneg _))).2
        fun x => ?_
      simpa [convBCF_apply] using abs_wConv_le A s x)

theorem convCLM_apply (s : SMeas d) (x : Torus d) : convCLM A s x = wConv A s x := rfl

theorem isCompactOperator_convCLM : IsCompactOperator (convCLM A) := by
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall
    (convCLM A).toLinearMap zero_lt_one).2 ?_
  refine BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) (Wb A))
    (isCompact_closedBall _ _) _ ?_ ?_
  · rintro f x ⟨s, hs, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hs ⊢
    have := abs_wConv_le A s x
    rw [Real.norm_eq_abs]
    calc |(convCLM A s) x| ≤ Wb A * ‖s‖ := this
      _ ≤ Wb A * 1 := by gcongr; exact Wb_nonneg A
      _ = Wb A := mul_one _
  · intro x0
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    have hc := (continuous_iff_continuousAt.1 (WC A).continuous x0).eventually
      (Metric.ball_mem_nhds (WC A x0) (half_pos hε))
    refine ⟨_, hc, ?_⟩
    rintro x hx x' hx' ⟨f, s, hs, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hs
    have h1 := abs_wConv_sub_le A s x x'
    have hx2 : dist (WC A x) (WC A x0) < ε / 2 := hx
    have hx3 : dist (WC A x') (WC A x0) < ε / 2 := hx'
    have h4 : dist (WC A x) (WC A x') < ε := by
      calc dist (WC A x) (WC A x') ≤ dist (WC A x) (WC A x0) + dist (WC A x0) (WC A x') :=
            dist_triangle _ _ _
        _ < ε := by rw [dist_comm (WC A x0)]; linarith
    show dist (convCLM A s x) (convCLM A s x') < ε
    rw [Real.dist_eq]
    calc |wConv A s x - wConv A s x'| ≤ ‖s‖ * dist (WC A x) (WC A x') := h1
      _ ≤ 1 * dist (WC A x) (WC A x') := by gcongr
      _ < ε := by rw [one_mul]; exact h4

end Model



/-! ### Continuous probability weights and the derivative operator -/

/-- A continuous nonnegative density `q` (with respect to Haar measure) of total mass one. -/
structure GibbsWeight (d : ℕ) where
  /-- The density. -/
  q : Torus d → ℝ
  cont : Continuous q
  nonneg : ∀ x, 0 ≤ q x
  mass : ∫ x, q x ∂haar d = 1

section Weight

variable (w : GibbsWeight d)

theorem GibbsWeight.integral_abs_le {f : Torus d → ℝ} (hf : Continuous f) {C : ℝ}
    (h : ∀ x, |f x| ≤ C * w.q x) : ∫ x, |f x| ∂haar d ≤ C := by
  have hq : Integrable w.q (haar d) := integrable_of_cont w.cont
  calc ∫ x, |f x| ∂haar d ≤ ∫ x, C * w.q x ∂haar d :=
        integral_mono (integrable_of_cont hf.abs) (hq.const_mul C) h
    _ = C := by rw [integral_const_mul, w.mass, mul_one]

theorem GibbsWeight.abs_integral_le {g : Torus d → ℝ} (hg : Continuous g) {C : ℝ}
    (h : ∀ x, |g x| ≤ C) : |∫ x, w.q x * g x ∂haar d| ≤ C := by
  have hi : Integrable (fun x => w.q x * g x) (haar d) := integrable_of_cont (w.cont.mul hg)
  calc |∫ x, w.q x * g x ∂haar d| = ‖∫ x, w.q x * g x ∂haar d‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖w.q x * g x‖ ∂haar d := norm_integral_le_integral_norm _
    _ ≤ C := by
        have := w.integral_abs_le (f := fun x => w.q x * g x) (w.cont.mul hg) (C := C)
          (fun x => by
            rw [abs_mul, abs_of_nonneg (w.nonneg x), mul_comm]
            exact mul_le_mul_of_nonneg_right (h x) (w.nonneg x))
        simpa only [Real.norm_eq_abs] using this

/-- The `q`-average `∫ q g dm`. -/
noncomputable def GibbsWeight.cavg (g : Torus d →ᵇ ℝ) : ℝ := ∫ x, w.q x * g x ∂haar d

theorem GibbsWeight.abs_cavg_le (g : Torus d →ᵇ ℝ) : |w.cavg g| ≤ ‖g‖ :=
  w.abs_integral_le g.continuous (fun x => by simpa using g.norm_coe_le_norm x)

theorem GibbsWeight.cavg_add (g h : Torus d →ᵇ ℝ) : w.cavg (g + h) = w.cavg g + w.cavg h := by
  unfold GibbsWeight.cavg
  simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, mul_add]
  exact integral_add (integrable_of_cont (w.cont.mul g.continuous))
    (integrable_of_cont (w.cont.mul h.continuous))

theorem GibbsWeight.cavg_smul (c : ℝ) (g : Torus d →ᵇ ℝ) : w.cavg (c • g) = c * w.cavg g := by
  unfold GibbsWeight.cavg
  simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

/-- The density `q (∫ q g − g)` of the derivative image. -/
noncomputable def GibbsWeight.phiDens (g : Torus d →ᵇ ℝ) (x : Torus d) : ℝ :=
  w.q x * (w.cavg g - g x)

theorem GibbsWeight.phiDens_cont (g : Torus d →ᵇ ℝ) : Continuous (w.phiDens g) :=
  w.cont.mul (continuous_const.sub g.continuous)

theorem GibbsWeight.integral_phiDens (g : Torus d →ᵇ ℝ) : ∫ x, w.phiDens g x ∂haar d = 0 := by
  unfold GibbsWeight.phiDens
  have h1 : ∀ x, w.q x * (w.cavg g - g x) = w.cavg g * w.q x - w.q x * g x :=
    fun x => by ring
  simp_rw [h1]
  have i1 : Integrable (fun x => w.cavg g * w.q x) (haar d) :=
    (integrable_of_cont w.cont).const_mul _
  have i2 : Integrable (fun x => w.q x * g x) (haar d) :=
    integrable_of_cont (w.cont.mul g.continuous)
  rw [integral_sub i1 i2, integral_const_mul, w.mass]
  simp [GibbsWeight.cavg]

theorem GibbsWeight.abs_phiDens_le (g : Torus d →ᵇ ℝ) (x : Torus d) :
    |w.phiDens g x| ≤ (2 * ‖g‖) * w.q x := by
  unfold GibbsWeight.phiDens
  rw [abs_mul, abs_of_nonneg (w.nonneg x), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (w.nonneg x)
  have h1 := w.abs_cavg_le g
  have h2 : |g x| ≤ ‖g‖ := by simpa using g.norm_coe_le_norm x
  calc |w.cavg g - g x| ≤ |w.cavg g| + |g x| := abs_sub _ _
    _ ≤ 2 * ‖g‖ := by linarith

/-- The map `g ↦ q (∫ q g − g) m` into signed measures. -/
noncomputable def GibbsWeight.PhiS : (Torus d →ᵇ ℝ) →L[ℝ] SMeas d :=
  LinearMap.mkContinuous
    { toFun := fun g => ofDensity (w.phiDens g)
      map_add' := fun g h => by
        rw [← ofDensity_add (w.phiDens_cont g) (w.phiDens_cont h)]
        congr 1
        ext x
        simp only [GibbsWeight.phiDens, w.cavg_add, BoundedContinuousFunction.coe_add,
          Pi.add_apply]
        ring
      map_smul' := fun c g => by
        rw [RingHom.id_apply, ← ofDensity_smul]
        congr 1
        ext x
        simp only [GibbsWeight.phiDens, w.cavg_smul, BoundedContinuousFunction.coe_smul,
          smul_eq_mul]
        ring }
    2 (fun g => by
      show ‖ofDensity (w.phiDens g)‖ ≤ 2 * ‖g‖
      rw [norm_ofDensity (w.phiDens_cont g)]
      exact w.integral_abs_le (w.phiDens_cont g) (w.abs_phiDens_le g))

theorem GibbsWeight.PhiS_apply (g : Torus d →ᵇ ℝ) : w.PhiS g = ofDensity (w.phiDens g) := rfl

variable (A : InteractionData d)

/-- The derivative, as a map into all signed measures. -/
noncomputable def GibbsWeight.derivS : zeroMass d →L[ℝ] SMeas d :=
  ((w.PhiS).comp (convCLM A)).comp (zeroMass d).subtypeL

theorem GibbsWeight.derivS_mem (η : zeroMass d) : w.derivS A η ∈ zeroMass d := by
  show ofDensity (w.phiDens (convCLM A η.1)) ∈ zeroMass d
  rw [mem_zeroMass, equiv_ofDensity_univ (w.phiDens_cont _)]
  exact w.integral_phiDens _

/-- The derivative operator `X → X` on zero-mass signed measures. -/
noncomputable def GibbsWeight.derivZ : zeroMass d →L[ℝ] zeroMass d :=
  (w.derivS A).codRestrict (zeroMass d) (w.derivS_mem A)

theorem GibbsWeight.isCompactOperator_derivZ : IsCompactOperator (w.derivZ A) := by
  have h1 := (((isCompactOperator_convCLM A).clm_comp w.PhiS)).comp_clm (zeroMass d).subtypeL
  exact h1.codRestrict (w.derivS_mem A) isClosed_zeroMass

/-! ### The extended map -/

theorem continuous_exp_neg_wConv (s : SMeas d) : Continuous (fun x => Real.exp (-wConv A s x)) :=
  (continuous_wConv A s).neg.rexp

/-- The normaliser `N(s) = ∫ q e^{-W*s} dm`. -/
noncomputable def GibbsWeight.normZ (s : SMeas d) : ℝ :=
  ∫ x, w.q x * Real.exp (-wConv A s x) ∂haar d

theorem GibbsWeight.normZ_ge (s : SMeas d) : Real.exp (-(Wb A * ‖s‖)) ≤ w.normZ A s := by
  unfold GibbsWeight.normZ
  have hi : Integrable (fun x => w.q x * Real.exp (-wConv A s x)) (haar d) :=
    integrable_of_cont (w.cont.mul (continuous_exp_neg_wConv A s))
  have h1 : ∫ x, w.q x * Real.exp (-(Wb A * ‖s‖)) ∂haar d = Real.exp (-(Wb A * ‖s‖)) := by
    rw [integral_mul_const, w.mass, one_mul]
  rw [← h1]
  refine integral_mono ((integrable_of_cont w.cont).mul_const _) hi fun x => ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (w.nonneg x)
  have := abs_le.1 (abs_wConv_le A s x)
  linarith [this.2]

theorem GibbsWeight.normZ_pos (s : SMeas d) : 0 < w.normZ A s :=
  lt_of_lt_of_le (Real.exp_pos _) (w.normZ_ge A s)

/-- The density `q (e^{-W*s}/N(s) − 1)` of the extended map. -/
noncomputable def GibbsWeight.fDens (s : SMeas d) (x : Torus d) : ℝ :=
  w.q x * (Real.exp (-wConv A s x) / w.normZ A s - 1)

theorem GibbsWeight.fDens_cont (s : SMeas d) : Continuous (w.fDens A s) :=
  w.cont.mul (((continuous_exp_neg_wConv A s).div_const _).sub continuous_const)

theorem GibbsWeight.integral_fDens (s : SMeas d) : ∫ x, w.fDens A s x ∂haar d = 0 := by
  unfold GibbsWeight.fDens
  have hN := (w.normZ_pos A s).ne'
  have h1 : ∀ x, w.q x * (Real.exp (-wConv A s x) / w.normZ A s - 1) =
      (w.normZ A s)⁻¹ * (w.q x * Real.exp (-wConv A s x)) - w.q x := fun x => by
    field_simp
  simp_rw [h1]
  have i1 : Integrable (fun x => (w.normZ A s)⁻¹ * (w.q x * Real.exp (-wConv A s x))) (haar d) :=
    (integrable_of_cont (w.cont.mul (continuous_exp_neg_wConv A s))).const_mul _
  rw [integral_sub i1 (integrable_of_cont w.cont), integral_const_mul, w.mass]
  have : ∫ x, w.q x * Real.exp (-wConv A s x) ∂haar d = w.normZ A s := rfl
  rw [this, inv_mul_cancel₀ hN, sub_self]

/-- The extended frozen Gibbs map, `s ↦ q (e^{-W*s}/N(s) − 1) m`, on all signed measures. -/
noncomputable def GibbsWeight.extS (s : SMeas d) : SMeas d := ofDensity (w.fDens A s)

/-- The extended frozen Gibbs map on the zero-mass signed measures. -/
noncomputable def GibbsWeight.ext (η : zeroMass d) : zeroMass d :=
  ⟨w.extS A η.1, by
    rw [mem_zeroMass, GibbsWeight.extS, equiv_ofDensity_univ (w.fDens_cont A _)]
    exact w.integral_fDens A _⟩

theorem GibbsWeight.ext_zero : w.ext A 0 = 0 := by
  apply Subtype.ext
  show ofDensity (w.fDens A 0) = 0
  have h : w.fDens A 0 = fun x => (0 : ℝ) * (fun _ => (0 : ℝ)) x := by
    ext x
    have h0 : ∀ y, wConv A (0 : SMeas d) y = 0 := fun y => SMeas.integral_zero_left _
    have hN : w.normZ A 0 = 1 := by
      unfold GibbsWeight.normZ
      simp [h0, w.mass]
    simp [GibbsWeight.fDens, h0, hN]
  rw [h, ofDensity_smul]
  simp

/-! ### The quadratic remainder -/

/-- Elementary algebra behind the quadratic remainder. -/
theorem alg_bound {u c r N B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ 1 / 4) (hu : |u| ≤ B) (hc : |c| ≤ B)
    (hr : |r| ≤ B ^ 2) (hR : |Real.exp (-u) - 1 + u| ≤ B ^ 2) (hN : N = 1 - c + r) :
    |Real.exp (-u) / N - 1 - c + u| ≤ 10 * B ^ 2 := by
  have hB2 : B ^ 2 ≤ B / 4 := by nlinarith
  have hNpos : 1 / 2 < N := by
    have h1 := (abs_le.1 hc).2
    have h2 := (abs_le.1 hr).1
    linarith
  have h3 : |c * u| ≤ B ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hc hu (abs_nonneg _) hB0
  have h4 : c ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs c]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have h5 : |r * (1 - u + c)| ≤ B ^ 2 * (3 / 2) := by
    rw [abs_mul]
    have : |1 - u + c| ≤ 3 / 2 := by
      have := abs_le.1 hu
      have := abs_le.1 hc
      rw [abs_le]
      constructor <;> linarith
    exact mul_le_mul hr this (abs_nonneg _) (sq_nonneg _)
  have key : |Real.exp (-u) - N * (1 - u + c)| ≤ 5 * B ^ 2 := by
    have e : Real.exp (-u) - N * (1 - u + c) =
        (Real.exp (-u) - 1 + u) - c * u + c ^ 2 - r * (1 - u + c) := by
      rw [hN]; ring
    rw [e]
    have a1 := abs_le.1 hR
    have a2 := abs_le.1 h3
    have a3 := abs_le.1 h5
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg c]
  have hN0 : N ≠ 0 := by linarith
  have e2 : Real.exp (-u) / N - 1 - c + u = (Real.exp (-u) - N * (1 - u + c)) / N := by
    field_simp
    ring
  rw [e2, abs_div, abs_of_pos (by linarith : 0 < N), div_le_iff₀ (by linarith : 0 < N)]
  nlinarith [sq_nonneg B]

theorem GibbsWeight.cavg_conv (s : SMeas d) :
    w.cavg (convBCF A s) = ∫ x, w.q x * wConv A s x ∂haar d := rfl

theorem GibbsWeight.fDens_sub_pointwise (s : SMeas d) (hB : Wb A * ‖s‖ ≤ 1 / 4) (x : Torus d) :
    |w.fDens A s x - w.phiDens (convBCF A s) x| ≤ 10 * (Wb A * ‖s‖) ^ 2 * w.q x := by
  set B := Wb A * ‖s‖ with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (Wb_nonneg A) (norm_nonneg _)
  have hu : ∀ y, |wConv A s y| ≤ B := fun y => abs_wConv_le A s y
  have hc : |w.cavg (convBCF A s)| ≤ B :=
    w.abs_integral_le (continuous_wConv A s) hu
  have hRpt : ∀ y, |Real.exp (-wConv A s y) - 1 + wConv A s y| ≤ B ^ 2 := by
    intro y
    have h1 : |-wConv A s y| ≤ 1 := by rw [abs_neg]; linarith [hu y]
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 : (-wConv A s y) ^ 2 ≤ B ^ 2 := by
      rw [neg_sq, ← sq_abs (wConv A s y)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hu y) 2
    have e : Real.exp (-wConv A s y) - 1 + wConv A s y
        = Real.exp (-wConv A s y) - 1 - -wConv A s y := by ring
    rw [e]
    exact h2.trans h3
  have hRcont : Continuous (fun y => Real.exp (-wConv A s y) - 1 + wConv A s y) :=
    ((continuous_exp_neg_wConv A s).sub continuous_const).add (continuous_wConv A s)
  have hr : |∫ y, w.q y * (Real.exp (-wConv A s y) - 1 + wConv A s y) ∂haar d| ≤ B ^ 2 :=
    w.abs_integral_le hRcont hRpt
  have hN : w.normZ A s = 1 - w.cavg (convBCF A s) +
      ∫ y, w.q y * (Real.exp (-wConv A s y) - 1 + wConv A s y) ∂haar d := by
    have h1 : ∀ y, w.q y * (Real.exp (-wConv A s y) - 1 + wConv A s y) =
        w.q y * Real.exp (-wConv A s y) - w.q y + w.q y * wConv A s y := fun y => by ring
    simp_rw [h1]
    have i1 : Integrable (fun y => w.q y * Real.exp (-wConv A s y)) (haar d) :=
      integrable_of_cont (w.cont.mul (continuous_exp_neg_wConv A s))
    have i2 : Integrable (fun y => w.q y * wConv A s y) (haar d) :=
      integrable_of_cont (w.cont.mul (continuous_wConv A s))
    have i3 := i1.sub (integrable_of_cont w.cont)
    rw [integral_add (f := fun y => w.q y * Real.exp (-wConv A s y) - w.q y)
      (g := fun y => w.q y * wConv A s y) i3 i2,
      integral_sub (f := fun y => w.q y * Real.exp (-wConv A s y)) (g := w.q) i1
      (integrable_of_cont w.cont), w.mass, GibbsWeight.cavg_conv]
    unfold GibbsWeight.normZ
    ring
  have := alg_bound hB0 hB (hu x) hc hr (hRpt x) hN
  have e : w.fDens A s x - w.phiDens (convBCF A s) x =
      w.q x * (Real.exp (-wConv A s x) / w.normZ A s - 1 - w.cavg (convBCF A s) +
        wConv A s x) := by
    simp only [GibbsWeight.fDens, GibbsWeight.phiDens, convBCF_apply]
    ring
  rw [e, abs_mul, abs_of_nonneg (w.nonneg x), mul_comm]
  exact mul_le_mul_of_nonneg_right (by
    rw [hN] at this ⊢
    exact this) (w.nonneg x)

theorem GibbsWeight.norm_extS_sub_le (s : SMeas d) (hB : Wb A * ‖s‖ ≤ 1 / 4) :
    ‖w.extS A s - w.PhiS (convBCF A s)‖ ≤ 10 * (Wb A * ‖s‖) ^ 2 := by
  have e : w.extS A s - w.PhiS (convBCF A s) =
      ofDensity (fun x => w.fDens A s x - w.phiDens (convBCF A s) x) := by
    rw [ofDensity_sub (w.fDens_cont A s) (w.phiDens_cont _)]
    rfl
  rw [e, norm_ofDensity (g := fun x => w.fDens A s x - w.phiDens (convBCF A s) x)
    ((w.fDens_cont A s).sub (w.phiDens_cont _))]
  exact w.integral_abs_le ((w.fDens_cont A s).sub (w.phiDens_cont _))
    (w.fDens_sub_pointwise A s hB)

/-- **Quadratic remainder** (explicit form): for `‖η‖_TV ≤ 1/(4 Wb)`, the remainder of the
extended frozen Gibbs map is at most `10 Wb² ‖η‖²_TV` in full variation. -/
theorem GibbsWeight.quadratic_remainder (η : zeroMass d) (hη : Wb A * ‖η‖ ≤ 1 / 4) :
    ‖w.ext A η - w.ext A 0 - w.derivZ A η‖ ≤ 10 * Wb A ^ 2 * ‖η‖ ^ 2 := by
  rw [w.ext_zero A, sub_zero]
  have h := w.norm_extS_sub_le A η.1 hη
  have e : ‖w.ext A η - w.derivZ A η‖ = ‖w.extS A η.1 - w.PhiS (convBCF A η.1)‖ := rfl
  rw [e]
  calc _ ≤ 10 * (Wb A * ‖η.1‖) ^ 2 := h
    _ = 10 * Wb A ^ 2 * ‖η‖ ^ 2 := by
      have h' : ‖η.1‖ = ‖η‖ := rfl
      rw [h', mul_pow]
      ring

/-- The explicit quadratic-remainder constants. -/
theorem GibbsWeight.quadratic_remainder_exists :
    ∃ C r : ℝ, 0 < r ∧ ∀ η : zeroMass d, ‖η‖ ≤ r →
      ‖w.ext A η - w.ext A 0 - w.derivZ A η‖ ≤ C * ‖η‖ ^ 2 := by
  refine ⟨10 * Wb A ^ 2, 1 / (4 * (Wb A + 1)), by have := Wb_nonneg A; positivity, ?_⟩
  intro η hη
  refine w.quadratic_remainder A η ?_
  have hW := Wb_nonneg A
  have hpos : 0 < 4 * (Wb A + 1) := by positivity
  calc Wb A * ‖η‖ ≤ Wb A * (1 / (4 * (Wb A + 1))) := mul_le_mul_of_nonneg_left hη hW
    _ ≤ 1 / 4 := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
      nlinarith

theorem GibbsWeight.hasFDerivAt_ext : HasFDerivAt (w.ext A) (w.derivZ A) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hW := Wb_nonneg A
  have hK : 0 < Wb A + 1 := by positivity
  set δ : ℝ := min (1 / (4 * (Wb A + 1))) (c / (10 * (Wb A + 1) ^ 2)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : zeroMass d) hδpos] with η hη
  rw [mem_ball_zero_iff] at hη
  have h1 : ‖η‖ ≤ 1 / (4 * (Wb A + 1)) := (hη.trans_le (min_le_left _ _)).le
  have h2 : ‖η‖ ≤ c / (10 * (Wb A + 1) ^ 2) := (hη.trans_le (min_le_right _ _)).le
  obtain ⟨C, r, hr, hbd⟩ := w.quadratic_remainder_exists A
  have hrem := w.quadratic_remainder A η (by
    have hpos : 0 < 4 * (Wb A + 1) := by positivity
    calc Wb A * ‖η‖ ≤ Wb A * (1 / (4 * (Wb A + 1))) := mul_le_mul_of_nonneg_left h1 hW
      _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
        nlinarith)
  simp only [zero_add]
  refine hrem.trans ?_
  have h3 : 10 * (Wb A + 1) ^ 2 * ‖η‖ ≤ c := by
    have := (le_div_iff₀ (by positivity : 0 < 10 * (Wb A + 1) ^ 2)).1 h2
    linarith
  have h4 : 10 * Wb A ^ 2 ≤ 10 * (Wb A + 1) ^ 2 := by nlinarith
  calc 10 * Wb A ^ 2 * ‖η‖ ^ 2 = (10 * Wb A ^ 2 * ‖η‖) * ‖η‖ := by ring
    _ ≤ c * ‖η‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc 10 * Wb A ^ 2 * ‖η‖ ≤ 10 * (Wb A + 1) ^ 2 * ‖η‖ :=
            mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
        _ ≤ c := h3

end Weight

/-! ### Signed measures from measures; Fubini -/

theorem vint_toSignedMeasure (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] (f : Torus d → ℝ) :
    ∫ᵛ x, f x ∂•ρ.toSignedMeasure = ∫ x, f x ∂ρ := by
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    simp
  rw [← integral_toSignedMeasure (f := f), hflip]

/-- The element of `SMeas d` given by a finite measure. -/
noncomputable def SMeas.ofMeasure (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] : SMeas d :=
  SMeas.equiv.symm ρ.toSignedMeasure

theorem SMeas.integral_ofMeasure (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] (f : Torus d → ℝ) :
    (SMeas.ofMeasure ρ).integral f = ∫ y, f y ∂ρ := by
  unfold SMeas.integral SMeas.ofMeasure
  rw [LinearEquiv.apply_symm_apply]
  exact vint_toSignedMeasure ρ f

theorem integral_wConv (A : InteractionData d) (ρ : Measure (Torus d)) [IsProbabilityMeasure ρ]
    (s : SMeas d) :
    ∫ x, wConv A s x ∂ρ = s.integral (fun y => ∫ x, A.W x y ∂ρ) := by
  have hint : Integrable (Function.uncurry fun x y => A.W x y)
      (ρ.toSignedMeasure.variation.prod (SMeas.equiv s).variation) :=
    A.W_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_integral_smul_swap (μ := ρ.toSignedMeasure) (ν := SMeas.equiv s)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) hint
  unfold wConv SMeas.integral
  rw [← integral_toSignedMeasure (μ := ρ)]
  simp only [vint_toSignedMeasure] at h
  exact h

/-! ### The frozen Gibbs specialisation -/

section Frozen

variable (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))

/-- The weight `q = dPμ/dm`, the density of the frozen Gibbs law at `μ`. -/
noncomputable def frozenWeight : GibbsWeight d where
  q := frozenDensity A (μ : Measure (Torus d))
  cont := frozenDensity_continuous A _
  nonneg := fun x => (Real.exp_pos _).le.trans (frozenDensity_bounds A _ x).1
  mass := integral_frozenDensity A _

/-- The extension of the frozen Gibbs map `ν ↦ Pν` to a neighbourhood of `μ` in `μ + X`,
written in the variable `η = ν − μ ∈ X`, as `η ↦ P(μ + η) − Pμ`: it has density
`q (e^{-W*η}/∫ q e^{-W*η} dm − 1)` with respect to Haar measure. -/
noncomputable def frozenGibbsExt : zeroMass d → zeroMass d := (frozenWeight A μ).ext A

/-- The derivative `DPμ : X → X`, `η ↦ -q (W*η − ∫ q (W*η) dm) m`. -/
noncomputable def frozenGibbsDeriv : zeroMass d →L[ℝ] zeroMass d := (frozenWeight A μ).derivZ A

theorem ofDensity_frozenDensity (ν : ProbabilityMeasure (Torus d)) :
    ofDensity (frozenDensity A (ν : Measure (Torus d))) =
      SMeas.ofMeasure (frozenGibbs A ν).measure := by
  unfold ofDensity SMeas.ofMeasure
  congr 1
  have hnn : ∀ x, 0 ≤ frozenDensity A (ν : Measure (Torus d)) x :=
    fun x => (Real.exp_pos _).le.trans (frozenDensity_bounds A _ x).1
  have hmeas : Measurable fun x => ENNReal.ofReal (frozenDensity A (ν : Measure (Torus d)) x) :=
    (frozenDensity_continuous A _).measurable.ennreal_ofReal
  have hfin : (∫⁻ x, ENNReal.ofReal (frozenDensity A (ν : Measure (Torus d)) x) ∂haar d) ≠ ⊤ := by
    have : (∫⁻ x, ENNReal.ofReal (frozenDensity A (ν : Measure (Torus d)) x) ∂haar d) =
        (frozenGibbs A ν).measure univ := by
      unfold BoundedPositiveReference.measure
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      rfl
    rw [this]
    exact measure_ne_top _ _
  have h := withDensityᵥ_toReal (μ := haar d) hmeas.aemeasurable hfin
  have e : (fun x => (ENNReal.ofReal (frozenDensity A (ν : Measure (Torus d)) x)).toReal) =
      frozenDensity A (ν : Measure (Torus d)) := by
    ext x
    exact ENNReal.toReal_ofReal (hnn x)
  rw [e] at h
  rw [h]
  rfl

/-- Pointwise: the density of `P(ν)` is `q e^{-W*η}/N(η)` when `η = ν − μ`. -/
theorem frozenDensity_eq_of_sub (ν : ProbabilityMeasure (Torus d)) (η : SMeas d)
    (hη : η = SMeas.ofMeasure (ν : Measure (Torus d)) - SMeas.ofMeasure (μ : Measure (Torus d)))
    (x : Torus d) :
    frozenDensity A (ν : Measure (Torus d)) x =
      (frozenWeight A μ).q x * Real.exp (-wConv A η x) / (frozenWeight A μ).normZ A η := by
  have hW : ∀ y, wConv A η y = ∫ z, A.W y z ∂(ν : Measure (Torus d)) -
      ∫ z, A.W y z ∂(μ : Measure (Torus d)) := by
    intro y
    unfold wConv
    rw [hη, SMeas.integral_sub_left _ _ (continuous_W_right A y), SMeas.integral_ofMeasure,
      SMeas.integral_ofMeasure]
  have hE : ∀ y, Real.exp (-frozenPotential A (ν : Measure (Torus d)) y) =
      frozenPartition A (μ : Measure (Torus d)) *
        ((frozenWeight A μ).q y * Real.exp (-wConv A η y)) := by
    intro y
    have hq : Real.exp (-frozenPotential A (μ : Measure (Torus d)) y) =
        frozenPartition A (μ : Measure (Torus d)) * (frozenWeight A μ).q y := by
      show _ = _ * frozenDensity A (μ : Measure (Torus d)) y
      unfold frozenDensity
      rw [mul_div_cancel₀ _ (frozenPartition_pos A _).ne']
    rw [← mul_assoc, ← hq, ← Real.exp_add, hW y]
    congr 1
    unfold frozenPotential
    ring
  have hZ : frozenPartition A (ν : Measure (Torus d)) =
      frozenPartition A (μ : Measure (Torus d)) * (frozenWeight A μ).normZ A η := by
    unfold frozenPartition GibbsWeight.normZ
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hE)
  unfold frozenDensity
  rw [hE x, hZ]
  have h1 := (frozenPartition_pos A (μ : Measure (Torus d))).ne'
  have h2 := ((frozenWeight A μ).normZ_pos A η).ne'
  field_simp

/-- The extension agrees with the frozen Gibbs map: `P(ν) − P(μ) = ext (ν − μ)`. -/
theorem frozenGibbsExt_eq (ν : ProbabilityMeasure (Torus d)) (η : zeroMass d)
    (hη : η.1 = SMeas.ofMeasure (ν : Measure (Torus d)) - SMeas.ofMeasure (μ : Measure (Torus d))) :
    (frozenGibbsExt A μ η).1 =
      SMeas.ofMeasure (frozenGibbs A ν).measure - SMeas.ofMeasure (frozenGibbs A μ).measure := by
  have hq : (frozenWeight A μ).q = frozenDensity A (μ : Measure (Torus d)) := rfl
  show ofDensity ((frozenWeight A μ).fDens A η.1) = _
  have e : (frozenWeight A μ).fDens A η.1 = fun x =>
      frozenDensity A (ν : Measure (Torus d)) x - frozenDensity A (μ : Measure (Torus d)) x := by
    ext x
    rw [frozenDensity_eq_of_sub A μ ν η.1 hη x]
    unfold GibbsWeight.fDens
    rw [hq]
    have h2 := ((frozenWeight A μ).normZ_pos A η.1).ne'
    field_simp
  rw [e, ofDensity_sub (frozenDensity_continuous A _) (frozenDensity_continuous A _),
    ofDensity_frozenDensity, ofDensity_frozenDensity]

/-- For `μ = Pμ`, integration against `μ` is integration against `q m`. -/
theorem integral_eq_weight (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (g : Torus d → ℝ) :
    ∫ x, g x ∂(μ : Measure (Torus d)) = ∫ x, (frozenWeight A μ).q x * g x ∂haar d := by
  rw [← hμ]
  show ∫ x, g x ∂((haar d).withDensity fun x =>
    ENNReal.ofReal (frozenDensity A (μ : Measure (Torus d)) x)) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (frozenDensity_continuous A _).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  have h0 : 0 ≤ frozenDensity A (μ : Measure (Torus d)) x := (frozenWeight A μ).nonneg x
  rw [ENNReal.toReal_ofReal h0]
  rfl

theorem cavg_conv_eq (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) (η : SMeas d) :
    (frozenWeight A μ).cavg (convBCF A η) = η.integral (interactionConvolution A μ) := by
  rw [GibbsWeight.cavg_conv, ← integral_eq_weight A μ hμ, integral_wConv A _ η]
  congr 1
  ext y
  unfold interactionConvolution
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => A.W_symm x y)

theorem integral_centeredKernel_eq (η : SMeas d) (hη : η ∈ zeroMass d) (x : Torus d) :
    η.integral (fun y => centeredKernel A μ x y) =
      wConv A η x - η.integral (interactionConvolution A μ) := by
  have e : (fun y => centeredKernel A μ x y) = fun y =>
      (A.W x y - interactionConvolution A μ y) +
        (meanInteraction A μ - interactionConvolution A μ x) := by
    ext y
    unfold centeredKernel
    ring
  rw [e, SMeas.integral_add_fun η (f := fun y => A.W x y - interactionConvolution A μ y)
    (g := fun _ => meanInteraction A μ - interactionConvolution A μ x)
    ((continuous_W_right A x).sub (continuous_interactionConvolution A μ)) continuous_const,
    SMeas.integral_sub_fun η (f := fun y => A.W x y) (g := interactionConvolution A μ)
    (continuous_W_right A x) (continuous_interactionConvolution A μ),
    SMeas.integral_const, mem_zeroMass.1 hη]
  simp [wConv]

/-- The centered-kernel form of the derivative, for `μ = Pμ`:
`DPμ[η](dx) = -q(x) (∫ K(x,y) dη(y)) dm(x)`. -/
theorem frozenGibbsDeriv_eq_kernel (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d)))
    (η : zeroMass d) :
    SMeas.equiv (frozenGibbsDeriv A μ η).1 =
      (haar d).withDensityᵥ (fun x => -(frozenGibbs A μ).density x *
        ∫ᵛ y, centeredKernel A μ x y ∂•(SMeas.equiv η.1)) := by
  show SMeas.equiv (ofDensity ((frozenWeight A μ).phiDens (convBCF A η.1))) = _
  unfold ofDensity
  rw [LinearEquiv.apply_symm_apply]
  congr 1
  ext x
  have h := integral_centeredKernel_eq A μ η.1 η.2 x
  rw [GibbsWeight.phiDens, cavg_conv_eq A μ hμ]
  unfold SMeas.integral at h ⊢
  rw [h]
  show (frozenWeight A μ).q x * _ = -(frozenWeight A μ).q x * _
  rw [convBCF_apply]
  ring

/-- **STR005, derivative (signed-measure form).**  With `X = zeroMass d` the space of zero-mass
finite signed measures in the full variation norm, `frozenGibbsExt A μ : X → X`,
`η ↦ P(μ+η) − Pμ`, extends the frozen Gibbs map (first conjunct), vanishes at `0`, is Fréchet
differentiable at `0` with derivative `frozenGibbsDeriv A μ`, and (for `μ = Pμ`) the derivative is
`η ↦ -q(x) (∫ K(x,y) dη(y)) m(dx)` with `q = dPμ/dm` and `K` the centered kernel at `μ`. -/
theorem frozenGibbs_fderiv_signedMeasure (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d))
    (hμ : (frozenGibbs A μ).measure = (μ : Measure (Torus d))) :
    (∀ (ν : ProbabilityMeasure (Torus d)) (η : zeroMass d),
        η.1 = SMeas.ofMeasure (ν : Measure (Torus d)) - SMeas.ofMeasure (μ : Measure (Torus d)) →
        (frozenGibbsExt A μ η).1 = SMeas.ofMeasure (frozenGibbs A ν).measure -
          SMeas.ofMeasure (frozenGibbs A μ).measure) ∧
      frozenGibbsExt A μ 0 = 0 ∧
      HasFDerivAt (frozenGibbsExt A μ) (frozenGibbsDeriv A μ) 0 ∧
      ∀ η : zeroMass d, SMeas.equiv (frozenGibbsDeriv A μ η).1 =
        (haar d).withDensityᵥ (fun x => -(frozenGibbs A μ).density x *
          ∫ᵛ y, centeredKernel A μ x y ∂•(SMeas.equiv η.1)) :=
  ⟨fun ν η hη => frozenGibbsExt_eq A μ ν η hη, (frozenWeight A μ).ext_zero A,
    (frozenWeight A μ).hasFDerivAt_ext A, frozenGibbsDeriv_eq_kernel A μ hμ⟩

/-- **STR005, compactness.**  The derivative `DPμ : X → X` is a compact operator in the full
variation norm (it is the Fréchet derivative at `0` of the extended map). -/
theorem frozenGibbs_fderiv_compact (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    fderiv ℝ (frozenGibbsExt A μ) 0 = frozenGibbsDeriv A μ ∧
      IsCompactOperator (frozenGibbsDeriv A μ) :=
  ⟨(frozenWeight A μ).hasFDerivAt_ext A |>.fderiv,
    (frozenWeight A μ).isCompactOperator_derivZ A⟩

/-- **STR005, quadratic remainder.**  Locally in the full variation norm,
`‖P(μ+η) − Pμ − DPμ η‖ ≤ C ‖η‖²`; stated both for the extension and for genuine probability
measures `ν = μ + η`. -/
theorem frozenGibbs_quadratic_remainder (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    ∃ C r : ℝ, 0 < r ∧
      (∀ η : zeroMass d, ‖η‖ ≤ r →
        ‖frozenGibbsExt A μ η - frozenGibbsExt A μ 0 - frozenGibbsDeriv A μ η‖ ≤ C * ‖η‖ ^ 2) ∧
      ∀ (ν : ProbabilityMeasure (Torus d)) (η : zeroMass d),
        η.1 = SMeas.ofMeasure (ν : Measure (Torus d)) - SMeas.ofMeasure (μ : Measure (Torus d)) →
        ‖η‖ ≤ r →
        ‖SMeas.ofMeasure (frozenGibbs A ν).measure - SMeas.ofMeasure (frozenGibbs A μ).measure -
          (frozenGibbsDeriv A μ η).1‖ ≤ C * ‖η‖ ^ 2 := by
  obtain ⟨C, r, hr, h⟩ := (frozenWeight A μ).quadratic_remainder_exists A
  refine ⟨C, r, hr, h, fun ν η hη hηr => ?_⟩
  have h1 := h η hηr
  rw [(frozenWeight A μ).ext_zero A, sub_zero] at h1
  rw [← frozenGibbsExt_eq A μ ν η hη]
  exact h1

end Frozen

end DGPS.Structural
