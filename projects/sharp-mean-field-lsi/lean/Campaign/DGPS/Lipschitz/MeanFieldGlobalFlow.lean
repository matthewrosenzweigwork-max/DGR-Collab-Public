import DGPS.Lipschitz.MeanFieldFlowPositivity

/-!
# Global bounded flow and `L¹` stability (LIP028)

Global mild probability solutions of the mean-field equation for bounded initial densities.
Route: exponentially weighted Banach fixed point on `[0,T]` (iterate contraction), `L¹`
stability via Duhamel duality and a weighted Gronwall inequality (which also gives
uniqueness), and patching the solutions on `[0,n]` into a global one.
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal Real

namespace DGPS.Lipschitz

theorem integral_rpow_neg_half_exp_le {l : ℝ} (hl : 0 < l) {t : ℝ} (ht : 0 ≤ t) :
    ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * Real.exp (-(l * r)) ≤ Real.sqrt (π / l) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2) * Real.exp (-(l * x))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 : ℝ) / 2) (b := l)
      (by norm_num) one_pos hl
    simpa using this
  have hval : ∫ x : ℝ in Ioi 0, x ^ (-(1 : ℝ) / 2) * Real.exp (-(l * x)) = Real.sqrt (π / l) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := l) (by norm_num) hl
    have e : (1 / 2 : ℝ) - 1 = -(1 : ℝ) / 2 := by norm_num
    rw [e] at this
    rw [this, Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
    congr 1; ring
  rw [intervalIntegral.integral_of_le ht, ← hval]
  refine setIntegral_mono_set hint ?_ ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => by
      have : 0 < x := hx
      positivity)
  · exact Eventually.of_forall (Ioc_subset_Ioi_self)


theorem intervalIntegrable_rpow_neg_half (a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => r ^ (-(1 : ℝ) / 2)) volume a b :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

theorem conv_exp_le {a l D t : ℝ} (ha : 0 ≤ a) (hl : 4 * π * a ^ 2 ≤ l) (hD : 0 ≤ D)
    (ht : 0 ≤ t) {ψ : ℝ → ℝ} (hψ : ∀ s ∈ Icc 0 t, ψ s ≤ D * Real.exp (l * s))
    (hi : IntervalIntegrable (fun r => r ^ (-(1 : ℝ) / 2) * ψ (t - r)) volume 0 t) :
    a * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * ψ (t - r) ≤ D / 2 * Real.exp (l * t) := by
  rcases ha.eq_or_lt with h0 | hapos
  · subst h0
    rw [zero_mul]; positivity
  have hl0 : 0 < l := lt_of_lt_of_le (by positivity) hl
  have h1 : ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * ψ (t - r) ≤
      ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * (D * Real.exp (l * (t - r))) := by
    refine intervalIntegral.integral_mono_on ht hi ?_ fun r hr => ?_
    · exact (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn
        (by fun_prop : Continuous fun r : ℝ => D * Real.exp (l * (t - r))).continuousOn
    · exact mul_le_mul_of_nonneg_left (hψ (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩)
        (Real.rpow_nonneg hr.1 _)
  have h2 : ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * (D * Real.exp (l * (t - r))) =
      D * Real.exp (l * t) * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * Real.exp (-(l * r)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    have : l * (t - r) = l * t + -(l * r) := by ring
    rw [this, Real.exp_add]; ring
  have h3 := integral_rpow_neg_half_exp_le hl0 ht
  have hs : a * Real.sqrt (π / l) ≤ 1 / 2 := by
    have : Real.sqrt (π / l) ≤ 1 / (2 * a) := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      rw [div_le_iff₀ hl0]
      have e : (1 / (2 * a)) ^ 2 * (4 * π * a ^ 2) = π := by field_simp; norm_num
      rw [← e]
      exact mul_le_mul_of_nonneg_left hl (by positivity)
    calc a * Real.sqrt (π / l) ≤ a * (1 / (2 * a)) := mul_le_mul_of_nonneg_left this ha
      _ = 1 / 2 := by field_simp
  have hDe : 0 ≤ D * Real.exp (l * t) := by positivity
  calc a * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * ψ (t - r)
      ≤ a * (D * Real.exp (l * t) * Real.sqrt (π / l)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans ?_)) ha
        exact mul_le_mul_of_nonneg_left h3 hDe
    _ = D * Real.exp (l * t) * (a * Real.sqrt (π / l)) := by ring
    _ ≤ D * Real.exp (l * t) * (1 / 2) := mul_le_mul_of_nonneg_left hs hDe
    _ = D / 2 * Real.exp (l * t) := by ring

theorem weighted_gronwall {A a l T : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hl : 4 * π * a ^ 2 ≤ l)
    (hT : 0 ≤ T) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 T)) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hineq : ∀ t ∈ Icc 0 T,
      f t ≤ A + a * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * f (t - r)) :
    ∀ t ∈ Icc 0 T, f t ≤ 2 * A * Real.exp (l * t) := by
  have hl0 : 0 ≤ l := le_trans (by positivity) hl
  set m : ℝ → ℝ := fun s => Real.exp (-(l * s)) * f s with hm
  have hmc : ContinuousOn m (Icc 0 T) :=
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-(l * s))).continuousOn.mul hf
  obtain ⟨s0, hs0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT) hmc
  set F := m s0 with hF
  have hF0 : 0 ≤ F := mul_nonneg (Real.exp_pos _).le (hf0 s0 hs0)
  have hfm : ∀ s, f s = Real.exp (l * s) * m s := fun s => by
    simp only [hm]; rw [← mul_assoc, ← Real.exp_add]; simp
  have key : ∀ t ∈ Icc 0 T, m t ≤ A + F / 2 := by
    intro t ht
    have hψ : ∀ s ∈ Icc 0 t, f s ≤ F * Real.exp (l * s) := by
      intro s hs
      have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
      have h1 : m s ≤ F := hmax hsT
      rw [hfm s, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    have hcont : ContinuousOn (fun r => f (t - r)) (uIcc 0 t) := by
      refine hf.comp (continuousOn_const.sub continuousOn_id) fun r hr => ?_
      rw [uIcc_of_le ht.1] at hr
      exact ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩
    have hi := (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn hcont
    have h2 := conv_exp_le ha hl hF0 ht.1 hψ hi
    have h3 : f t ≤ A + F / 2 * Real.exp (l * t) := (hineq t ht).trans (by linarith)
    have h4 : m t = Real.exp (-(l * t)) * f t := rfl
    have h5 : Real.exp (-(l * t)) * Real.exp (l * t) = 1 := by
      rw [← Real.exp_add]; simp
    have h6 : Real.exp (-(l * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
    rw [h4]
    calc Real.exp (-(l * t)) * f t ≤ Real.exp (-(l * t)) * (A + F / 2 * Real.exp (l * t)) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = A * Real.exp (-(l * t)) + F / 2 := by
          have : Real.exp (-(l * t)) * (F / 2 * Real.exp (l * t)) = F / 2 := by
            rw [mul_left_comm, h5, mul_one]
          rw [mul_add, this]; ring
      _ ≤ A * 1 + F / 2 := by gcongr
      _ = A + F / 2 := by ring
  have hFA : F ≤ 2 * A := by linarith [key s0 hs0]
  intro t ht
  rw [hfm t]
  calc Real.exp (l * t) * m t ≤ Real.exp (l * t) * F :=
        mul_le_mul_of_nonneg_left (hmax ht) (Real.exp_pos _).le
    _ ≤ Real.exp (l * t) * (2 * A) := mul_le_mul_of_nonneg_left hFA (Real.exp_pos _).le
    _ = 2 * A * Real.exp (l * t) := by ring

section AbstractDuhamel

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {D : ℝ → W →L[ℝ] E} {c : ℝ}

/-- Weighted norm bound for the Duhamel integral. -/
theorem duhamel_norm_le_weighted (hD : DuhamelKernel D c) {g : ℝ → W} {ψ : ℝ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hψ : ∀ s ∈ Icc 0 t, ‖g s‖ ≤ ψ s)
    (hi : IntervalIntegrable (fun r => r ^ (-(1 : ℝ) / 2) * ψ (t - r)) volume 0 t) :
    ‖duhamel D g t‖ ≤ c * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * ψ (t - r) := by
  unfold duhamel
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ (hi.const_mul c)
  refine Filter.Eventually.of_forall fun r hr => ?_
  have h1 := hD.bound r hr.1 (g (t - r))
  calc ‖D r (g (t - r))‖ ≤ c * r ^ (-(1 : ℝ) / 2) * ‖g (t - r)‖ := h1
    _ ≤ c * r ^ (-(1 : ℝ) / 2) * ψ (t - r) :=
        mul_le_mul_of_nonneg_left (hψ _ ⟨by linarith [hr.2], by linarith [hr.1]⟩)
          (mul_nonneg hD.nonneg (Real.rpow_nonneg hr.1.le _))
    _ = c * (r ^ (-(1 : ℝ) / 2) * ψ (t - r)) := by ring

/-- The Laplace-transform estimate for a pure exponential weight. -/
theorem conv_const_exp_le {c κ μ Dd t : ℝ} (hc : 0 ≤ c) (hκ : 0 ≤ κ) (hDd : 0 ≤ Dd)
    (hμ : 4 * π * (c * κ) ^ 2 ≤ μ) (ht : 0 ≤ t) :
    c * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * (κ * (Dd * Real.exp (μ * (t - r)))) ≤
      Dd / 2 * Real.exp (μ * t) := by
  have h1 : ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * (κ * (Dd * Real.exp (μ * (t - r)))) =
      κ * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * (Dd * Real.exp (μ * (t - r))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  have hi : IntervalIntegrable (fun r : ℝ => r ^ (-(1 : ℝ) / 2) * (Dd * Real.exp (μ * (t - r))))
      volume 0 t :=
    (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn
      (by fun_prop : Continuous fun r : ℝ => Dd * Real.exp (μ * (t - r))).continuousOn
  have h2 := conv_exp_le (a := c * κ) (l := μ) (D := Dd) (t := t) (mul_nonneg hc hκ) hμ hDd ht
    (ψ := fun s => Dd * Real.exp (μ * s)) (fun s _ => le_rfl) (by simpa using hi)
  rw [h1, ← mul_assoc]
  simpa using h2

/-- Weighted norm bound for the Duhamel integral, pure exponential weights. -/
theorem duhamel_norm_le_exp (hD : DuhamelKernel D c) {g : ℝ → W} {κ μ Dd t : ℝ} (hκ : 0 ≤ κ)
    (hDd : 0 ≤ Dd) (hμ : 4 * π * (c * κ) ^ 2 ≤ μ) (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, ‖g s‖ ≤ κ * (Dd * Real.exp (μ * s))) :
    ‖duhamel D g t‖ ≤ Dd / 2 * Real.exp (μ * t) := by
  refine (duhamel_norm_le_weighted hD ht hg ?_).trans (conv_const_exp_le hD.nonneg hκ hDd hμ ht)
  exact (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn
    (by fun_prop : Continuous fun r : ℝ => κ * (Dd * Real.exp (μ * (t - r)))).continuousOn

end AbstractDuhamel

section LInfty

variable {d : ℕ}

/-- `L∞` bound for the Duhamel integral with a time-weighted bound on the forcing. -/
theorem ae_abs_duhamel_le_weighted {g : ℝ → L2v d} (hg : Continuous g) {M0 : ℝ}
    (hM0 : ∀ r, ‖g r‖ ≤ M0) {K : ℝ → ℝ} (hKc : Continuous K) {t : ℝ} (ht : 0 ≤ t)
    (hK0 : ∀ s ∈ Icc 0 t, 0 ≤ K s)
    (hgK : ∀ s ∈ Icc 0 t, ∀ᵐ x ∂haar d, ‖g s x‖ ≤ K s) :
    ∀ᵐ x ∂haar d, |duhamel (divHeatFam d) g t x| ≤
      Real.sqrt (d / 2) * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * K (t - r) := by
  set D : ℝ → L2v d →L[ℝ] L2s d := fun τ => divHeat τ with hD
  set c := Real.sqrt (d / 2) with hc
  have hker : DuhamelKernel D c := divHeat_duhamelKernel
  have hint0 : IntervalIntegrable (fun r : ℝ => r ^ (-(1 : ℝ) / 2) * K (t - r)) volume 0 t :=
    (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn
      (hKc.comp (continuous_const.sub continuous_id)).continuousOn
  set w := duhamel D g t with hw
  set I := ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * K (t - r) with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht fun r hr =>
    mul_nonneg (Real.rpow_nonneg hr.1 _) (hK0 _ ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  set C := c * I with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hI0
  have key : ∀ A : Set (Torus d), MeasurableSet A →
      |∫ x in A, w x ∂haar d| ≤ C * (haar d).real A := by
    intro A hA
    have hAfin : haar d A ≠ ∞ := measure_ne_top _ _
    set ℓ : L2s d →L[ℝ] ℝ := innerSL ℝ (indicatorConstLp 2 hA hAfin (1 : ℝ)) with hℓ
    have hℓw : ∀ f : L2s d, ℓ f = ∫ x in A, f x ∂haar d := fun f => by
      rw [hℓ, innerSL_apply_apply]
      exact L2.inner_indicatorConstLp_one hA hAfin f
    have hint := intervalIntegrable_duhamel hker hg hM0 ht
    have e1 : ℓ w = ∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r))) := by
      rw [hw, duhamel]
      exact (ℓ.intervalIntegral_comp_comm hint).symm
    have hbi : IntervalIntegrable
        (fun r : ℝ => c * (haar d).real A * (r ^ (-(1 : ℝ) / 2) * K (t - r))) volume 0 t :=
      hint0.const_mul (c * (haar d).real A)
    have e2 : ‖∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r)))‖ ≤
        ∫ r in (0 : ℝ)..t, c * (haar d).real A * (r ^ (-(1 : ℝ) / 2) * K (t - r)) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hbi
      refine Filter.Eventually.of_forall fun r hr => ?_
      have hr0 : 0 < r := hr.1
      have hts : t - r ∈ Icc 0 t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
      have hb := divHeat_ae_le hr0 (g (t - r)) (hK0 _ hts) (hgK _ hts)
      rw [hℓw]
      refine (norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
        (hb.mono fun x hx _ => hx)).trans ?_
      have : (c * r ^ (-(1 : ℝ) / 2) * K (t - r)) * (haar d).real A =
          c * (haar d).real A * (r ^ (-(1 : ℝ) / 2) * K (t - r)) := by ring
      exact this.le
    have e3 : ∫ r in (0 : ℝ)..t, c * (haar d).real A * (r ^ (-(1 : ℝ) / 2) * K (t - r)) =
        C * (haar d).real A := by
      rw [intervalIntegral.integral_const_mul, hC]; ring
    rw [← hℓw, ← Real.norm_eq_abs, e1]
    exact e2.trans e3.le
  have hwi : Integrable (⇑w) (haar d) := (Lp.memLp w).integrable one_le_two
  have hp : 0 ≤ᵐ[haar d] fun x => C - w x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const C).sub hwi) fun A hA _ => ?_
    rw [integral_sub (integrable_const C).integrableOn hwi.integrableOn,
      setIntegral_const, smul_eq_mul, mul_comm]
    linarith [(abs_le.mp (key A hA)).2]
  have hn : 0 ≤ᵐ[haar d] fun x => C + w x := by
    refine ae_nonneg_of_forall_setIntegral_nonneg ((integrable_const C).add hwi) fun A hA _ => ?_
    rw [integral_add (integrable_const C).integrableOn hwi.integrableOn,
      setIntegral_const, smul_eq_mul, mul_comm]
    linarith [(abs_le.mp (key A hA)).1]
  filter_upwards [hp, hn] with x h1 h2
  rw [abs_le]
  constructor <;> simp only [Pi.zero_apply] at h1 h2 <;> linarith

end LInfty

section Existence

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

theorem aeBall_mono {R R' : ℝ} (hR : R ≤ R') : aeBall d R ⊆ aeBall d R' := fun v hv =>
  (show ∀ᵐ x ∂haar d, |v x| ≤ R from hv).mono fun _ hx => hx.trans hR

/-- Continuous `L²`-paths on `[0,T]` with the time-weighted a.e. bound `2 M e^{l t}`. -/
def wBallPaths (d : ℕ) (T M l : ℝ) : Set C(Icc (0 : ℝ) T, L2s d) :=
  {w | ∀ t : Icc (0 : ℝ) T, w t ∈ aeBall d (2 * M * Real.exp (l * t))}

theorem isClosed_wBallPaths (T M l : ℝ) : IsClosed (wBallPaths d T M l) := by
  have : wBallPaths d T M l = ⋂ t : Icc (0 : ℝ) T,
      (fun w : C(Icc (0 : ℝ) T, L2s d) => w t) ⁻¹' aeBall d (2 * M * Real.exp (l * t)) := by
    ext w; simp [wBallPaths]
  rw [this]
  exact isClosed_iInter fun t => (isClosed_aeBall _).preimage (continuous_eval_const t)

theorem wBallPaths_sub {T M l : ℝ} (hM : 0 ≤ M) (hl : 0 ≤ l) :
    wBallPaths d T M l ⊆ ballPaths d T (2 * M * Real.exp (l * T)) := fun w hw t =>
  aeBall_mono (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left t.2.2 hl)) (by positivity)) (hw t)

theorem ae_gpath_le_weighted (h : MeanFieldData G B g b) {T : ℝ} (hT : 0 ≤ T) {M l : ℝ}
    {w : C(Icc (0 : ℝ) T, L2s d)} (hw : w ∈ wBallPaths d T M l) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) :
    ∀ᵐ x ∂haar d, ‖gpath h hT w s x‖ ≤ (g + b) * (2 * M * Real.exp (l * s)) := by
  have hgb := add_nonneg h.g_nonneg h.b_nonneg
  have hm := hw ⟨s, hs⟩
  have hext : extPath hT w s = w ⟨s, hs⟩ := by simp [extPath, Set.projIcc_of_mem hT hs]
  filter_upwards [coeFn_Nvec h (extPath hT w s), hm] with x h1 h2
  have h3 := norm_meanFieldN_le h ((Lp.memLp (extPath hT w s)).integrable one_le_two) x
  change ‖(Nvec h (extPath hT w s)) x‖ ≤ _
  rw [h1]
  refine h3.trans (mul_le_mul_of_nonneg_left ?_ hgb)
  rw [hext]; exact h2

theorem Phi_mem_weighted (h : MeanFieldData G B g b) {T : ℝ} (hT : 0 ≤ T) {ρ0 : L2s d} {M : ℝ}
    (hM : 0 ≤ M) (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) {w : C(Icc (0 : ℝ) T, L2s d)}
    (hw : w ∈ wBallPaths d T M (2 * π * d * (g + b) ^ 2)) (t : Icc (0 : ℝ) T) :
    Phi h hT ρ0 w t ∈ aeBall d (2 * M * Real.exp (2 * π * d * (g + b) ^ 2 * t)) := by
  set l := 2 * π * d * (g + b) ^ 2 with hl
  have hl0 : 0 ≤ l := by positivity
  have hgb := add_nonneg h.g_nonneg h.b_nonneg
  have hR : 0 ≤ 2 * M * Real.exp (l * T) := by positivity
  have hw' := wBallPaths_sub hM hl0 hw
  have hd := ae_abs_duhamel_le_weighted (g := gpath h hT w)
    (continuous_gpath (h := h) (hT := hT) hR hw') (norm_gpath_le (h := h) (hT := hT) hw')
    (K := fun s => (g + b) * (2 * M * Real.exp (l * s))) (by fun_prop) t.2.1
    (fun s _ => by positivity)
    (fun s hs => ae_gpath_le_weighted h hT hw ⟨hs.1, hs.2.trans t.2.2⟩)
  have hμ : 4 * π * (Real.sqrt (d / 2) * (g + b)) ^ 2 ≤ l := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hl]; apply le_of_eq; ring
  have hconv := conv_const_exp_le (c := Real.sqrt (d / 2)) (κ := g + b) (μ := l) (Dd := 2 * M)
    (t := t) (Real.sqrt_nonneg _) hgb (by positivity) hμ t.2.1
  have he : 1 ≤ Real.exp (l * t) := Real.one_le_exp (by have := t.2.1; positivity)
  filter_upwards [ae_abs_heatL2_le ρ0 hρ0 t.2.1, hd,
    Lp.coeFn_add (heatL2 ρ0 t) (duhamel (divHeatFam d) (gpath h hT w) t)] with x h1 h2 h3
  unfold Phi
  rw [h3, Pi.add_apply]
  refine (abs_add_le _ _).trans ?_
  have h4 := h2.trans hconv
  nlinarith [mul_nonneg hM (sub_nonneg.2 he)]

theorem Phi_weighted_contract (h : MeanFieldData G B g b) {T : ℝ} (hT : 0 ≤ T) {ρ0 : L2s d}
    {M l μ : ℝ} (hM : 0 ≤ M) (hl0 : 0 ≤ l)
    (hμ : 4 * π * (Real.sqrt (d / 2) * (g + b + 2 * b * (2 * M * Real.exp (l * T)))) ^ 2 ≤ μ)
    {w w' : C(Icc (0 : ℝ) T, L2s d)} (hw : w ∈ wBallPaths d T M l)
    (hw' : w' ∈ wBallPaths d T M l) {Dd : ℝ} (hDd : 0 ≤ Dd)
    (hD : ∀ s : Icc (0 : ℝ) T, ‖w s - w' s‖ ≤ Dd * Real.exp (μ * s)) (t : Icc (0 : ℝ) T) :
    ‖Phi h hT ρ0 w t - Phi h hT ρ0 w' t‖ ≤ Dd / 2 * Real.exp (μ * t) := by
  set R := 2 * M * Real.exp (l * T) with hRdef
  have hb := h.b_nonneg
  have hg := h.g_nonneg
  have hR : 0 ≤ R := by positivity
  have hL : 0 ≤ g + b + 2 * b * R := by positivity
  have hw1 := wBallPaths_sub hM hl0 hw
  have hw1' := wBallPaths_sub hM hl0 hw'
  have hg1 := continuous_gpath (h := h) (hT := hT) hR hw1
  have hg2 := continuous_gpath (h := h) (hT := hT) hR hw1'
  have hsub : ∀ s ∈ Icc (0 : ℝ) t, ‖gpath h hT w s - gpath h hT w' s‖ ≤
      (g + b + 2 * b * R) * (Dd * Real.exp (μ * s)) := by
    intro s hs
    have sT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans t.2.2⟩
    unfold gpath
    refine (norm_Nvec_sub_le h _ _ hR (hw1' _)).trans
      (mul_le_mul_of_nonneg_left ?_ hL)
    have e1 : extPath hT w s = w ⟨s, sT⟩ := by
      simp only [extPath]; rw [Set.projIcc_of_mem hT sT]
    rw [e1, Set.projIcc_of_mem hT sT]
    exact hD ⟨s, sT⟩
  have e : Phi h hT ρ0 w t - Phi h hT ρ0 w' t =
      duhamel (divHeatFam d) (gpath h hT w) t - duhamel (divHeatFam d) (gpath h hT w') t := by
    unfold Phi; abel
  rw [e, ← duhamel_sub (divHeat_duhamelKernel (d := d)) hg1 hg2
    (norm_gpath_le (h := h) (hT := hT) hw1) (norm_gpath_le (h := h) (hT := hT) hw1') t.2.1]
  exact duhamel_norm_le_exp (divHeat_duhamelKernel (d := d)) hL hDd hμ t.2.1 hsub

theorem exists_weighted_flow (h : MeanFieldData G B g b) {T : ℝ} (hT : 0 ≤ T) {M : ℝ}
    (hM : 0 ≤ M) (ρ0 : L2s d) (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) :
    ∃ u : ℝ → L2s d, ContinuousOn u (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d,
        |u t x| ≤ 2 * (M * Real.exp (2 * π * d * (g + b) ^ 2 * t))) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        u t = heatL2 ρ0 t + duhamel (divHeatFam d) (fun s => Nvec h (u s)) t := by
  set l := 2 * π * d * (g + b) ^ 2 with hl
  have hl0 : 0 ≤ l := by positivity
  have hb := h.b_nonneg
  have hg := h.g_nonneg
  set R := 2 * M * Real.exp (l * T) with hRdef
  have hR : 0 ≤ R := by positivity
  set μ := 4 * π * (Real.sqrt (d / 2) * (g + b + 2 * b * R)) ^ 2 with hμdef
  have hμ0 : 0 ≤ μ := by positivity
  let f : wBallPaths d T M l → wBallPaths d T M l := fun w =>
    ⟨⟨Phi h hT ρ0 w.1, continuous_Phi ρ0 hR (wBallPaths_sub hM hl0 w.2)⟩,
      fun t => Phi_mem_weighted h hT hM hρ0 w.2 t⟩
  have hiter : ∀ (n : ℕ) (w w' : wBallPaths d T M l) (t : Icc (0 : ℝ) T),
      ‖(f^[n] w).1 t - (f^[n] w').1 t‖ ≤ (1 / 2 : ℝ) ^ n * dist w.1 w'.1 * Real.exp (μ * t) := by
    intro n
    induction n with
    | zero =>
      intro w w' t
      have h1 : 1 ≤ Real.exp (μ * t) := Real.one_le_exp (by have := t.2.1; positivity)
      have h2 : ‖w.1 t - w'.1 t‖ ≤ dist w.1 w'.1 := by
        rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist t
      simp only [Function.iterate_zero, id, pow_zero, one_mul]
      nlinarith [dist_nonneg (x := w.1) (y := w'.1)]
    | succ n ih =>
      intro w w' t
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have := Phi_weighted_contract h hT hM hl0 (le_of_eq hμdef.symm) (f^[n] w).2 (f^[n] w').2
        (ρ0 := ρ0) (Dd := (1 / 2 : ℝ) ^ n * dist w.1 w'.1)
        (by have := dist_nonneg (x := w.1) (y := w'.1); positivity) (fun s => ih w w' s) t
      refine this.trans (le_of_eq ?_)
      rw [pow_succ]; ring
  have hit : ∀ (n : ℕ) (w w' : wBallPaths d T M l),
      dist (f^[n] w) (f^[n] w') ≤ (1 / 2 : ℝ) ^ n * Real.exp (μ * T) * dist w w' := by
    intro n w w'
    rw [Subtype.dist_eq, Subtype.dist_eq]
    have hD := dist_nonneg (x := w.1) (y := w'.1)
    refine (ContinuousMap.dist_le (by positivity)).2 fun t => ?_
    rw [dist_eq_norm]
    refine (hiter n w w' t).trans ?_
    have : Real.exp (μ * t) ≤ Real.exp (μ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left t.2.2 hμ0)
    calc _ ≤ (1 / 2 : ℝ) ^ n * dist w.1 w'.1 * Real.exp (μ * T) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := 1 / (2 * Real.exp (μ * T))) (y := (1 / 2 : ℝ))
    (by positivity) (by norm_num)
  have hn' : (1 / 2 : ℝ) ^ n * Real.exp (μ * T) ≤ 1 / 2 := by
    have he := Real.exp_pos (μ * T)
    rw [lt_div_iff₀ (by positivity)] at hn
    nlinarith
  have hf : ContractingWith (1 / 2 : ℝ≥0) f^[n] := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
    have := hit n w w'
    have hd := dist_nonneg (x := w) (y := w')
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    nlinarith
  have : CompleteSpace (wBallPaths d T M l) := (isClosed_wBallPaths T M l).completeSpace_coe
  have : Nonempty (wBallPaths d T M l) := by
    refine ⟨⟨0, fun t => ?_⟩⟩
    show ∀ᵐ x ∂haar d, |((0 : C(Icc (0 : ℝ) T, L2s d)) t) x| ≤ _
    filter_upwards [Lp.coeFn_zero ℝ 2 (haar d)] with x hx
    simp only [ContinuousMap.zero_apply, hx, Pi.zero_apply, abs_zero]
    positivity
  have hfix : Function.IsFixedPt f (ContractingWith.fixedPoint f^[n] hf) :=
    hf.isFixedPt_fixedPoint_iterate
  set w := ContractingWith.fixedPoint f^[n] hf with hw
  have hmem : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T), extPath hT w.1 t = w.1 ⟨t, ht⟩ := by
    intro t ht
    simp [extPath, Set.projIcc_of_mem _ ht]
  refine ⟨extPath hT w.1, (continuous_extPath w.1).continuousOn, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hmem t ht]
    have := w.2 ⟨t, ht⟩
    rw [← mul_assoc]
    exact this
  · rw [hmem t ht]
    have := congrArg (fun z : wBallPaths d T M l => z.1 ⟨t, ht⟩) hfix
    refine this.symm.trans ?_
    rfl

end Existence


section L1

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- The `L¹` norm of a function on the torus. -/
noncomputable def n1 (f : Torus d → ℝ) : ℝ := ∫ x, |f x| ∂haar d

/-- The `L¹` norm of a vector field on the torus. -/
noncomputable def n1v (F : Torus d → Tangent d) : ℝ := ∫ x, ‖F x‖ ∂haar d

theorem n1_nonneg (f : Torus d → ℝ) : 0 ≤ n1 f := integral_nonneg fun _ => abs_nonneg _

theorem n1v_nonneg (F : Torus d → Tangent d) : 0 ≤ n1v F := integral_nonneg fun _ => norm_nonneg _

theorem ofReal_n1 {f : Torus d → ℝ} (hf : MemLp f 1 (haar d)) :
    ENNReal.ofReal (n1 f) = eLpNorm f 1 (haar d) := by
  have := ofReal_integral_norm_eq_lintegral_enorm (hf.integrable le_rfl)
  rw [eLpNorm_one_eq_lintegral_enorm, ← this]
  · simp [n1]
  · exact hf.aestronglyMeasurable

theorem ofReal_n1v {F : Torus d → Tangent d} (hF : MemLp F 1 (haar d)) :
    ENNReal.ofReal (n1v F) = eLpNorm F 1 (haar d) := by
  have := ofReal_integral_norm_eq_lintegral_enorm (hF.integrable le_rfl)
  rw [eLpNorm_one_eq_lintegral_enorm, ← this]
  · rfl
  · exact hF.aestronglyMeasurable

theorem memLp_one_L2s (f : L2s d) : MemLp (⇑f) 1 (haar d) :=
  (Lp.memLp f).mono_exponent (by norm_num)

theorem memLp_one_L2v (f : L2v d) : MemLp (⇑f) 1 (haar d) :=
  (Lp.memLp f).mono_exponent (by norm_num)

theorem n1_le_norm (f : L2s d) : n1 ⇑f ≤ ‖f‖ := by
  rw [Lp.norm_def, ← ENNReal.ofReal_le_iff_le_toReal (Lp.memLp f).eLpNorm_ne_top,
    ofReal_n1 (memLp_one_L2s f)]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

theorem n1_congr_ae {f f' : Torus d → ℝ} (h : f =ᵐ[haar d] f') : n1 f = n1 f' :=
  integral_congr_ae (h.mono fun x hx => by simp [hx])

theorem n1_sub_L2s (a c : L2s d) : n1 ⇑(a - c) = ∫ x, |a x - c x| ∂haar d :=
  integral_congr_ae ((Lp.coeFn_sub a c).mono fun x hx => by simp only [hx, Pi.sub_apply])

theorem integrable_abs_L2s (a : L2s d) : Integrable (fun x => |a x|) (haar d) :=
  ((Lp.memLp a).integrable one_le_two).abs

theorem abs_n1_sub_le (a c : L2s d) : |n1 ⇑a - n1 ⇑c| ≤ n1 ⇑(a - c) := by
  rw [n1_sub_L2s]
  unfold n1
  rw [← integral_sub (integrable_abs_L2s a) (integrable_abs_L2s c)]
  refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ?_
    (Eventually.of_forall fun x => abs_abs_sub_abs_le_abs_sub _ _)
  exact (((Lp.memLp a).integrable one_le_two).sub ((Lp.memLp c).integrable one_le_two)).abs

theorem continuous_n1 : Continuous fun a : L2s d => n1 ⇑a := by
  refine continuous_iff_continuousAt.2 fun a => ?_
  refine Metric.continuousAt_iff.2 fun ε hε => ⟨ε, hε, fun c hc => ?_⟩
  rw [Real.dist_eq]
  refine (abs_n1_sub_le c a).trans_lt ?_
  refine lt_of_le_of_lt (n1_le_norm _) ?_
  rwa [dist_eq_norm] at hc

theorem n1_neg (a : L2s d) : n1 ⇑(-a) = n1 ⇑a :=
  integral_congr_ae ((Lp.coeFn_neg a).mono fun x hx => by simp only [hx, Pi.neg_apply, abs_neg])

theorem n1_add_le (a c : L2s d) : n1 ⇑(a + c) ≤ n1 ⇑a + n1 ⇑c := by
  have hs : n1 ⇑(a + c) = ∫ x, |a x + c x| ∂haar d :=
    integral_congr_ae ((Lp.coeFn_add a c).mono fun x hx => by simp only [hx, Pi.add_apply])
  rw [hs]
  unfold n1
  rw [← integral_add (integrable_abs_L2s a) (integrable_abs_L2s c)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    ((integrable_abs_L2s a).add (integrable_abs_L2s c)) (Eventually.of_forall fun x => ?_)
  exact abs_add_le _ _

theorem n1_heatL2_le (ρ0 : L2s d) {t : ℝ} (ht : 0 ≤ t) : n1 ⇑(heatL2 ρ0 t) ≤ n1 ⇑ρ0 := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0; rw [heatL2_zero]
  · have h1 := DGPS.eLpNorm_heatOp_le hpos (p := 1) le_rfl ENNReal.one_ne_top (memLp_one_L2s ρ0)
    have h2 : eLpNorm (⇑(heatL2 ρ0 t)) 1 (haar d) = eLpNorm (heatOp t ⇑ρ0) 1 (haar d) :=
      eLpNorm_congr_ae (coeFn_heatL2 ρ0 hpos)
    rw [← ENNReal.ofReal_le_ofReal_iff (n1_nonneg _), ofReal_n1 (memLp_one_L2s _),
      ofReal_n1 (memLp_one_L2s _), h2]
    exact h1

theorem n1_divHeat_le {τ : ℝ} (hτ : 0 < τ) (F : L2v d) :
    n1 ⇑(divHeat τ F) ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) * n1v ⇑F := by
  have h1 := eLpNorm_divHeatFun_le hτ (p := 1) le_rfl (memLp_one_L2v F)
  have h2 : eLpNorm (⇑(divHeat τ F)) 1 (haar d) = eLpNorm (divHeatFun τ ⇑F) 1 (haar d) :=
    eLpNorm_congr_ae (coeFn_divHeat hτ F)
  have hc : 0 ≤ Real.sqrt (d / 2) * τ ^ (-(1 : ℝ) / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hτ.le _)
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (n1v_nonneg _)), ofReal_n1 (memLp_one_L2s _),
    ENNReal.ofReal_mul hc, ofReal_n1v (memLp_one_L2v F), h2]
  exact h1

theorem n1v_Nvec_sub_le (h : MeanFieldData G B g b) (u v : L2s d) (hv : n1 ⇑v = 1) :
    n1v ⇑(Nvec h u - Nvec h v) ≤ (g + 3 * b) * n1 ⇑(u - v) := by
  have hg := h.g_nonneg
  have hb := h.b_nonneg
  set D := n1 ⇑(u - v) with hDdef
  have hD0 : 0 ≤ D := n1_nonneg _
  have hD : eLpNorm (fun x => u x - v x) 1 (haar d) = ENNReal.ofReal D := by
    rw [hDdef, ofReal_n1 (memLp_one_L2s (u - v))]
    exact eLpNorm_congr_ae (Lp.coeFn_sub u v).symm
  have hv1 : eLpNorm (⇑v) 1 (haar d) = 1 := by
    rw [← ofReal_n1 (memLp_one_L2s v), hv]; simp
  have h1 := eLpNorm_meanFieldN_sub_le h (p := 1) le_rfl (memLp_one_L2s u) (memLp_one_L2s v)
  have h2 : eLpNorm (⇑(Nvec h u - Nvec h v)) 1 (haar d) =
      eLpNorm (fun x => meanFieldN G B u x - meanFieldN G B v x) 1 (haar d) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (Nvec h u) (Nvec h v), coeFn_Nvec h u, coeFn_Nvec h v] with x h3 h4 h5
    rw [h3, Pi.sub_apply, h4, h5]
  rw [hD, hv1] at h1
  have hc : 0 ≤ (g + 3 * b) * D := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hc, ofReal_n1v (memLp_one_L2v _), h2]
  refine h1.trans (le_of_eq ?_)
  rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

end L1

section L1Duhamel

variable {d : ℕ}

/-- `L¹` bound for the Duhamel integral, by duality with a sign function. -/
theorem n1_duhamel_le {g : ℝ → L2v d} (hg : Continuous g) {M0 : ℝ}
    (hM0 : ∀ r, ‖g r‖ ≤ M0) {κ : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) {t : ℝ}
    (ht : 0 ≤ t) (hgφ : ∀ s ∈ Icc 0 t, n1v ⇑(g s) ≤ κ * φ s) :
    n1 ⇑(duhamel (divHeatFam d) g t) ≤
      Real.sqrt (d / 2) * κ * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * φ (t - r) := by
  set D : ℝ → L2v d →L[ℝ] L2s d := fun τ => divHeat τ with hD
  set c := Real.sqrt (d / 2) with hc
  have hker : DuhamelKernel D c := divHeat_duhamelKernel
  have hint0 : IntervalIntegrable (fun r : ℝ => r ^ (-(1 : ℝ) / 2) * φ (t - r)) volume 0 t :=
    (intervalIntegrable_rpow_neg_half 0 t).mul_continuousOn
      (hφ.comp (continuous_const.sub continuous_id)).continuousOn
  set w := duhamel D g t with hw
  have hwm : Measurable (⇑w : Torus d → ℝ) := (Lp.stronglyMeasurable w).measurable
  set ψ : Torus d → ℝ := fun x => if 0 ≤ w x then 1 else -1 with hψdef
  have hψm : Measurable ψ := Measurable.ite (measurableSet_le measurable_const hwm)
    measurable_const measurable_const
  have hψb : ∀ x, ‖ψ x‖ ≤ 1 := fun x => by
    simp only [hψdef]; split_ifs <;> simp
  have hψL : MemLp ψ 2 (haar d) := MemLp.of_bound hψm.aestronglyMeasurable 1
    (Eventually.of_forall hψb)
  set ℓ : L2s d →L[ℝ] ℝ := innerSL ℝ (hψL.toLp ψ) with hℓ
  have hℓf : ∀ f : L2s d, ℓ f = ∫ x, ψ x * f x ∂haar d := fun f => by
    rw [hℓ, innerSL_apply_apply, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψL.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  have hℓle : ∀ f : L2s d, ℓ f ≤ n1 ⇑f := fun f => by
    rw [hℓf]
    refine (le_abs_self _).trans ?_
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (integrable_abs_L2s f) (Eventually.of_forall fun x => ?_)
    show |ψ x * f x| ≤ |f x|
    rw [abs_mul]
    have := hψb x
    rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (f x)]
  have hℓw : ℓ w = n1 ⇑w := by
    rw [hℓf]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hψdef]
    split_ifs with h1
    · rw [one_mul, abs_of_nonneg h1]
    · rw [neg_one_mul, abs_of_neg (not_le.1 h1)]
  have hint := intervalIntegrable_duhamel hker hg hM0 ht
  have e1 : ℓ w = ∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r))) := by
    rw [hw, duhamel]
    exact (ℓ.intervalIntegral_comp_comm hint).symm
  have hbi : IntervalIntegrable
      (fun r : ℝ => c * κ * (r ^ (-(1 : ℝ) / 2) * φ (t - r))) volume 0 t :=
    hint0.const_mul (c * κ)
  have e2 : ‖∫ r in (0 : ℝ)..t, ℓ (D r (g (t - r)))‖ ≤
      ∫ r in (0 : ℝ)..t, c * κ * (r ^ (-(1 : ℝ) / 2) * φ (t - r)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hbi
    refine Filter.Eventually.of_forall fun r hr => ?_
    have hr0 : 0 < r := hr.1
    have hts : t - r ∈ Icc 0 t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have hpos : 0 ≤ c * r ^ (-(1 : ℝ) / 2) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr0.le _)
    have hb1 := n1_divHeat_le hr0 (g (t - r))
    have hb2 := hgφ _ hts
    have hb3 : ℓ (D r (g (t - r))) ≤ n1 ⇑(D r (g (t - r))) := hℓle _
    have hb4 : -ℓ (D r (g (t - r))) ≤ n1 ⇑(D r (g (t - r))) := by
      rw [← map_neg ℓ]
      exact (hℓle _).trans (le_of_eq (n1_neg _))
    rw [Real.norm_eq_abs, abs_le]
    have hb5 : n1 ⇑(D r (g (t - r))) ≤ c * κ * (r ^ (-(1 : ℝ) / 2) * φ (t - r)) := by
      refine hb1.trans ?_
      calc c * r ^ (-(1 : ℝ) / 2) * n1v ⇑(g (t - r)) ≤ c * r ^ (-(1 : ℝ) / 2) * (κ * φ (t - r)) :=
            mul_le_mul_of_nonneg_left hb2 hpos
        _ = _ := by ring
    constructor <;> linarith
  have e3 : ∫ r in (0 : ℝ)..t, c * κ * (r ^ (-(1 : ℝ) / 2) * φ (t - r)) =
      c * κ * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * φ (t - r) :=
    intervalIntegral.integral_const_mul _ _
  rw [← hℓw, e1]
  exact (le_abs_self _).trans (e2.trans e3.le)

end L1Duhamel

section L1Stability

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

theorem heatL2_sub (ρ0 η0 : L2s d) (t : ℝ) :
    heatL2 (ρ0 - η0) t = heatL2 ρ0 t - heatL2 η0 t := map_sub (heatCLM t) ρ0 η0

/-- **`L¹` stability on a finite interval.** -/
theorem l1_stability_local (h : MeanFieldData G B g b) {T M1 M2 : ℝ} {ρ0 η0 : L2s d}
    {u v : ℝ → L2s d} (S1 : MildFlow h ρ0 T M1 u) (S2 : MildFlow h η0 T M2 v)
    (hv : ∀ t ∈ Icc (0 : ℝ) T, n1 ⇑(v t) = 1) :
    ∀ t ∈ Icc (0 : ℝ) T,
      n1 ⇑(u t - v t) ≤ 2 * n1 ⇑(ρ0 - η0) * Real.exp (2 * π * d * (g + 3 * b) ^ 2 * t) := by
  have hb := h.b_nonneg
  have hg := h.g_nonneg
  have hT := S1.hT
  set a := Real.sqrt (d / 2) * (g + 3 * b) with ha
  have ha0 : 0 ≤ a := by positivity
  set f : ℝ → ℝ := fun s => n1 ⇑(uX T u s - uX T v s) with hf
  have hfc : Continuous f := continuous_n1.comp (S1.continuous_uX.sub S2.continuous_uX)
  have hfT : ∀ s ∈ Icc (0 : ℝ) T, f s = n1 ⇑(u s - v s) := fun s hs => by
    simp only [hf, S1.uX_of_mem hs, S2.uX_of_mem hs]
  have hineq : ∀ t ∈ Icc (0 : ℝ) T,
      f t ≤ n1 ⇑(ρ0 - η0) + a * ∫ r in (0 : ℝ)..t, r ^ (-(1 : ℝ) / 2) * f (t - r) := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ht
    set Nu : ℝ → L2v d := fun s => Nvec h (uX T u s) with hNu
    set Nv : ℝ → L2v d := fun s => Nvec h (uX T v s) with hNv
    have hdec : uX T u t - uX T v t = heatL2 (ρ0 - η0) t +
        duhamel (divHeatFam d) (fun s => Nu s - Nv s) t := by
      rw [S1.uX_of_mem ht', S2.uX_of_mem ht', S1.mild t ht', S2.mild t ht', S1.duhamel_eq_uX ht',
        S2.duhamel_eq_uX ht', heatL2_sub,
        duhamel_sub (divHeat_duhamelKernel (d := d)) S1.continuous_NvecX S2.continuous_NvecX
          S1.norm_NvecX_le S2.norm_NvecX_le ht.1]
      abel
    have hgc : Continuous fun s => Nu s - Nv s := S1.continuous_NvecX.sub S2.continuous_NvecX
    have hgM : ∀ r, ‖Nu r - Nv r‖ ≤ (g + b) * (2 * M1) + (g + b) * (2 * M2) := fun r =>
      (norm_sub_le _ _).trans (add_le_add (S1.norm_NvecX_le r) (S2.norm_NvecX_le r))
    have hgφ : ∀ s ∈ Icc (0 : ℝ) t, n1v ⇑(Nu s - Nv s) ≤ (g + 3 * b) * f s := by
      intro s hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
      have := n1v_Nvec_sub_le h (uX T u s) (uX T v s) (by rw [S2.uX_of_mem hsT]; exact hv s hsT)
      exact this
    have hd := n1_duhamel_le hgc hgM hfc ht.1 hgφ
    have hfl : f t = n1 ⇑(uX T u t - uX T v t) := rfl
    rw [hfl, hdec]
    refine (n1_add_le _ _).trans ?_
    refine add_le_add (n1_heatL2_le _ ht.1) ?_
    rw [ha, mul_assoc] at *
    exact hd
  have hl : 4 * π * a ^ 2 ≤ 2 * π * d * (g + 3 * b) ^ 2 := by
    rw [ha, mul_pow, Real.sq_sqrt (by positivity)]; apply le_of_eq; ring
  have := weighted_gronwall (n1_nonneg _) ha0 hl hT hfc.continuousOn (fun s _ => n1_nonneg _) hineq
  intro t ht
  rw [← hfT t ht]
  exact this t ht

end L1Stability

section Global

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- A global bounded mild probability flow with initial datum `ρ0`: continuous into `L²` on
`[0,∞)`, locally bounded in `L∞`, nonnegative with unit mass, and satisfying the mild
(Duhamel) equation. (For probability densities the modified nonlinearity `Nvec` coincides with
the original one `ρ (∇V + B ∗ ρ)`; see `exists_global_prob_flow`.) -/
structure IsGlobalProbFlow (h : MeanFieldData G B g b) (ρ0 : L2s d) (u : ℝ → L2s d) :
    Prop where
  cont : ContinuousOn u (Ici 0)
  bdd : ∀ T : ℝ, 0 ≤ T → ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ M
  nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ᵐ[haar d] ⇑(u t)
  mass : ∀ t : ℝ, 0 ≤ t → ∫ x, u t x ∂haar d = 1
  mild : ∀ t : ℝ, 0 ≤ t →
    u t = heatL2 ρ0 t + duhamel (divHeatFam d) (fun s => Nvec h (u s)) t

theorem MildFlow.mono {h : MeanFieldData G B g b} {ρ0 : L2s d} {m M : ℝ} {u : ℝ → L2s d}
    (S : MildFlow h ρ0 m M u) {k : ℝ} (hk : 0 ≤ k) (hkm : k ≤ m) : MildFlow h ρ0 k M u :=
  ⟨hk, S.hM, S.cont.mono (Icc_subset_Icc_right hkm),
    fun t ht => S.bound t ⟨ht.1, ht.2.trans hkm⟩, fun t ht => S.mild t ⟨ht.1, ht.2.trans hkm⟩⟩

theorem IsGlobalProbFlow.toMild {h : MeanFieldData G B g b} {ρ0 : L2s d} {u : ℝ → L2s d}
    (S : IsGlobalProbFlow h ρ0 u) {T : ℝ} (hT : 0 ≤ T) : ∃ M, MildFlow h ρ0 T M u := by
  obtain ⟨M', hM'⟩ := S.bdd T hT
  refine ⟨|M'|, ?_⟩
  refine ⟨hT, abs_nonneg _, S.cont.mono fun t ht => ht.1, fun t ht => ?_, fun t ht => S.mild t ht.1⟩
  filter_upwards [hM' t ht] with x hx
  have := le_abs_self M'
  have := abs_nonneg M'
  linarith

theorem n1_eq_one {a : L2s d} (hnn : 0 ≤ᵐ[haar d] ⇑a) (hm : ∫ x, a x ∂haar d = 1) :
    n1 ⇑a = 1 := by
  refine Eq.trans ?_ hm
  exact MeasureTheory.integral_congr_ae (hnn.mono fun x hx => abs_of_nonneg hx)

theorem eq_of_n1_sub_eq_zero {a c : L2s d} (h0 : n1 ⇑(a - c) = 0) : a = c := by
  have h1 : ∫ x, |(a - c : L2s d) x| ∂haar d = 0 := h0
  rw [integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) (integrable_abs_L2s _)] at h1
  have h2 : a - c = 0 := by
    refine Lp.ext ?_
    filter_upwards [h1, Lp.coeFn_zero ℝ 2 (haar d)] with x hx hz
    simpa [hz] using hx
  exact sub_eq_zero.1 h2

theorem eLpNorm_sub_eq_ofReal_n1 (a c : L2s d) :
    eLpNorm (fun x => a x - c x) 1 (haar d) = ENNReal.ofReal (n1 ⇑(a - c)) := by
  rw [ofReal_n1 (memLp_one_L2s _)]
  exact eLpNorm_congr_ae (Lp.coeFn_sub a c).symm

/-- `L¹` stability of global probability flows. -/
theorem IsGlobalProbFlow.n1_sub_le {h : MeanFieldData G B g b} {ρ0 η0 : L2s d}
    {u v : ℝ → L2s d} (S1 : IsGlobalProbFlow h ρ0 u) (S2 : IsGlobalProbFlow h η0 v)
    {t : ℝ} (ht : 0 ≤ t) :
    n1 ⇑(u t - v t) ≤ 2 * n1 ⇑(ρ0 - η0) * Real.exp (2 * π * d * (g + 3 * b) ^ 2 * t) := by
  obtain ⟨M1, S1'⟩ := S1.toMild ht
  obtain ⟨M2, S2'⟩ := S2.toMild ht
  exact l1_stability_local h S1' S2' (fun s hs => n1_eq_one (S2.nonneg s hs.1) (S2.mass s hs.1)) t
    ⟨ht, le_rfl⟩

theorem n1_zero : n1 ⇑(0 : L2s d) = 0 := by
  unfold n1
  rw [← MeasureTheory.integral_zero (μ := haar d) (G := ℝ)]
  exact MeasureTheory.integral_congr_ae
    ((Lp.coeFn_zero ℝ 2 (haar d)).mono fun x hx => by simp)

theorem IsGlobalProbFlow.unique {h : MeanFieldData G B g b} {ρ0 : L2s d}
    {u v : ℝ → L2s d} (S1 : IsGlobalProbFlow h ρ0 u) (S2 : IsGlobalProbFlow h ρ0 v)
    {t : ℝ} (ht : 0 ≤ t) : u t = v t := by
  have := S1.n1_sub_le S2 ht
  rw [sub_self, n1_zero] at this
  simp only [mul_zero, zero_mul] at this
  exact eq_of_n1_sub_eq_zero (le_antisymm this (n1_nonneg _))

end Global


section GlobalExistence

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- Two mild flows on `[0,T]` from the same datum, the second one a probability flow, coincide. -/
theorem MildFlow.eq_of_prob {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M1 M2 : ℝ}
    {u v : ℝ → L2s d} (S1 : MildFlow h ρ0 T M1 u) (S2 : MildFlow h ρ0 T M2 v)
    (hnn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ᵐ[haar d] ⇑(v t))
    (hm : ∀ t ∈ Icc (0 : ℝ) T, ∫ x, v t x ∂haar d = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u t = v t := by
  have := l1_stability_local h S1 S2 (fun s hs => n1_eq_one (hnn s hs) (hm s hs)) t ht
  rw [sub_self, n1_zero] at this
  simp only [mul_zero, zero_mul] at this
  exact eq_of_n1_sub_eq_zero (le_antisymm this (n1_nonneg _))

/-- Local existence of a probability flow with the weighted `L∞` bound. -/
theorem exists_local_prob_flow (h : MeanFieldData G B g b) {ρ0 : L2s d}
    (h0 : 0 ≤ᵐ[haar d] ⇑ρ0) (hm : ∫ x, ρ0 x ∂haar d = 1) {M : ℝ}
    (hM : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → L2s d, MildFlow h ρ0 T (M * Real.exp (2 * π * d * (g + b) ^ 2 * T)) u ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * (M * Real.exp (2 * π * d * (g + b) ^ 2 * t))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ᵐ[haar d] ⇑(u t)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∫ x, u t x ∂haar d = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ⇑(Nvec h (u t)) =ᵐ[haar d]
        fun x => u t x • (G x + ∫ y, u t y • B x y ∂haar d)) := by
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hM.exists
    exact (abs_nonneg _).trans hx
  obtain ⟨u, hc, hb, hmild⟩ := exists_weighted_flow h hT hM0 ρ0 hM
  have hl : 0 ≤ 2 * π * d * (g + b) ^ 2 := by positivity
  have S : MildFlow h ρ0 T (M * Real.exp (2 * π * d * (g + b) ^ 2 * T)) u :=
    ⟨hT, by positivity, hc, fun t ht => by
      filter_upwards [hb t ht] with x hx
      refine hx.trans ?_
      have : Real.exp (2 * π * d * (g + b) ^ 2 * t) ≤ Real.exp (2 * π * d * (g + b) ^ 2 * T) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hl)
      nlinarith, hmild⟩
  obtain ⟨-, hnn, hmass, -, -, hN⟩ := flow_energy_regularity_positivity_and_mass S h0 hm
  exact ⟨u, S, hb, hnn, hmass, hN⟩

end GlobalExistence


section Patching

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- **Global existence.** -/
theorem exists_global_prob_flow (h : MeanFieldData G B g b) {ρ0 : L2s d}
    (h0 : 0 ≤ᵐ[haar d] ⇑ρ0) (hm : ∫ x, ρ0 x ∂haar d = 1) {M : ℝ}
    (hM : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) :
    ∃ u : ℝ → L2s d, IsGlobalProbFlow h ρ0 u ∧
      (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂haar d,
        |u t x| ≤ 2 * (M * Real.exp (2 * π * d * (g + b) ^ 2 * t))) ∧
      (∀ t : ℝ, 0 ≤ t → ⇑(Nvec h (u t)) =ᵐ[haar d]
        fun x => u t x • (G x + ∫ y, u t y • B x y ∂haar d)) := by
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hM.exists
    exact (abs_nonneg _).trans hx
  have hl : 0 ≤ 2 * π * d * (g + b) ^ 2 := by positivity
  choose u hS hb hnn hmass hN using
    fun n : ℕ => exists_local_prob_flow h h0 hm hM (Nat.cast_nonneg (α := ℝ) n)
  set U : ℝ → L2s d := fun t => u ⌈t⌉₊ t with hUdef
  have hmem : ∀ t : ℝ, 0 ≤ t → t ∈ Icc (0 : ℝ) (⌈t⌉₊ : ℕ) := fun t ht => ⟨ht, Nat.le_ceil t⟩
  have hU : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) n → U t = u n t := by
    intro n t ht
    have hle : ⌈t⌉₊ ≤ n := Nat.ceil_le.2 ht.2
    have hle' : ((⌈t⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
    have S2 := (hS n).mono (Nat.cast_nonneg ⌈t⌉₊) hle'
    exact MildFlow.eq_of_prob (hS ⌈t⌉₊) S2
      (fun s hs => hnn n s ⟨hs.1, hs.2.trans hle'⟩) (fun s hs => hmass n s ⟨hs.1, hs.2.trans hle'⟩)
      (hmem t ht.1)
  have hUe : ∀ t : ℝ, 0 ≤ t → U t = u ⌈t⌉₊ t := fun t _ => rfl
  have hcont : ContinuousOn U (Ici 0) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    set n : ℕ := ⌈t⌉₊ + 1 with hn
    have htn : t < n := by
      have := Nat.le_ceil t
      rw [hn]; push_cast; linarith
    have hnh : Icc (0 : ℝ) n ∈ 𝓝[Ici 0] t :=
      mem_nhdsWithin.2 ⟨Iio n, isOpen_Iio, htn, fun x hx => ⟨hx.2, hx.1.le⟩⟩
    have hc : ContinuousWithinAt (u n) (Icc 0 n) t :=
      (hS n).cont t ⟨ht0, htn.le⟩
    have hc' : ContinuousWithinAt (u n) (Ici 0) t := hc.mono_of_mem_nhdsWithin hnh
    refine hc'.congr_of_eventuallyEq ?_ (hU n t ⟨ht0, htn.le⟩)
    filter_upwards [hnh] with x hx using hU n x hx
  have hw : ∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂haar d,
      |U t x| ≤ 2 * (M * Real.exp (2 * π * d * (g + b) ^ 2 * t)) := fun t ht => by
    rw [hUe t ht]; exact hb ⌈t⌉₊ t (hmem t ht)
  refine ⟨U, ⟨hcont, ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩, hw, fun t ht => ?_⟩
  · intro T hT
    refine ⟨2 * (M * Real.exp (2 * π * d * (g + b) ^ 2 * T)), fun t htt => ?_⟩
    filter_upwards [hw t htt.1] with x hx
    refine hx.trans ?_
    have : Real.exp (2 * π * d * (g + b) ^ 2 * t) ≤ Real.exp (2 * π * d * (g + b) ^ 2 * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htt.2 hl)
    nlinarith
  · rw [hUe t ht]; exact hnn ⌈t⌉₊ t (hmem t ht)
  · rw [hUe t ht]; exact hmass ⌈t⌉₊ t (hmem t ht)
  · have hS' := (hS ⌈t⌉₊).mild t (hmem t ht)
    rw [hUe t ht, hS']
    congr 1
    unfold duhamel
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht] at hr
    simp only
    rw [hU ⌈t⌉₊ (t - r) ⟨by linarith [hr.2], by linarith [hr.1, (hmem t ht).2]⟩]
  · rw [hUe t ht]; exact hN ⌈t⌉₊ t (hmem t ht)

end Patching

section Main

variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

/-- **Global bounded flow and `L¹` stability.**

(1) For every bounded probability density `ρ0` (`|ρ0| ≤ M` a.e.) there is a global mild
probability flow `u` (continuous into `L²` on `[0,∞)`, locally `L∞`-bounded, nonnegative, of unit
mass), the modified nonlinearity `Nvec` along it is the original `ρ (G + B ∗ ρ)`, it obeys
`‖ρ_t‖∞ ≤ 2 exp(C t) M` with `C = 2π d (g+b)²`, and it is unique in this class.

(2) Any two global mild probability flows satisfy
`‖ρ_t - η_t‖₁ ≤ 2 exp(C′ t) ‖ρ0 - η0‖₁` with `C′ = 2π d (g+3b)²`, independent of density bounds. -/
theorem global_bounded_flow_and_l1_stability (h : MeanFieldData G B g b) :
    (∀ ρ0 : L2s d, 0 ≤ᵐ[haar d] ⇑ρ0 → ∫ x, ρ0 x ∂haar d = 1 → ∀ M : ℝ,
      (∀ᵐ x ∂haar d, |ρ0 x| ≤ M) →
      ∃ u : ℝ → L2s d, IsGlobalProbFlow h ρ0 u ∧
        (∀ t : ℝ, 0 ≤ t → ∀ᵐ x ∂haar d,
          |u t x| ≤ 2 * Real.exp (2 * π * d * (g + b) ^ 2 * t) * M) ∧
        (∀ t : ℝ, 0 ≤ t → ⇑(Nvec h (u t)) =ᵐ[haar d]
          fun x => u t x • (G x + ∫ y, u t y • B x y ∂haar d)) ∧
        (∀ v : ℝ → L2s d, IsGlobalProbFlow h ρ0 v → ∀ t : ℝ, 0 ≤ t → v t = u t)) ∧
    (∀ (ρ0 η0 : L2s d) (u v : ℝ → L2s d), IsGlobalProbFlow h ρ0 u → IsGlobalProbFlow h η0 v →
      ∀ t : ℝ, 0 ≤ t →
        eLpNorm (fun x => u t x - v t x) 1 (haar d) ≤
          ENNReal.ofReal (2 * Real.exp (2 * π * d * (g + 3 * b) ^ 2 * t)) *
            eLpNorm (fun x => ρ0 x - η0 x) 1 (haar d)) := by
  refine ⟨fun ρ0 h0 hm M hM => ?_, fun ρ0 η0 u v S1 S2 t ht => ?_⟩
  · obtain ⟨u, S, hw, hN⟩ := exists_global_prob_flow h h0 hm hM
    refine ⟨u, S, fun t ht => ?_, hN, fun v Sv t ht => Sv.unique S ht⟩
    filter_upwards [hw t ht] with x hx
    exact hx.trans_eq (by ring)
  · rw [eLpNorm_sub_eq_ofReal_n1, eLpNorm_sub_eq_ofReal_n1, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by
      have := S1.n1_sub_le S2 ht
      linarith [this, mul_comm (2 : ℝ) (n1 ⇑(ρ0 - η0)),
        mul_comm (2 * Real.exp (2 * π * d * (g + 3 * b) ^ 2 * t)) (n1 ⇑(ρ0 - η0))])

end Main

end DGPS.Lipschitz
