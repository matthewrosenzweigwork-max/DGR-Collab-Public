import DGPS.Analysis.PeriodicHolder
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryEuler
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryLocalization
import DGPS.Foundations.CircleRegularity

open MeasureTheory Filter Topology Function
open scoped ENNReal
open DGPS.Analysis.PeriodicHolder

/-!
# Ordinary optimizers: `C^{2,α}` bootstrap of the log-density (packet STR025b-iii)

For `h_j → 0` and global minimizers `ρ_j` of the ordinary quotient, the profiles
`f_j = log (W_j ∘ pt)²` (with `W_j` the continuous representative of `√ρ_j`, so
`ρ_j = exp (f_j)` almost everywhere on the circle) are eventually `C^{2,α}` periodic
functions with `phNorm α 2 f_j → 0`.

Route: `W_j → 1` uniformly (`H¹ ⊂ C^{1/2}` and `circle_H1_tendstoUniformly`); the weak Euler
equation gives `A_j = 2 W_j' − W_j σ_h` the weak derivative `−A_j σ_h / 2 − λ_j W_j (log W_j² − ℓ_h)`;
du Bois-Reymond upgrades to the classical ODE system on the line, whose small-data
analysis (`ode_logDensity_small`) gives `C^{2,α}` smallness of `log W_j²`.
-/

namespace DGPS.Examples.ThreeSpeciesCircle

/-! ### Uniform smallness of sequences of functions on `ℝ` -/

/-- A sequence of functions on `ℝ` tends to `0` uniformly. -/
def USmall (F : ℕ → ℝ → ℝ) : Prop := ∀ ε > 0, ∀ᶠ j in atTop, ∀ t, |F j t| ≤ ε

theorem USmall.add {F G : ℕ → ℝ → ℝ} (hF : USmall F) (hG : USmall G) :
    USmall (fun j t => F j t + G j t) := by
  intro ε hε
  filter_upwards [hF (ε / 2) (by positivity), hG (ε / 2) (by positivity)] with j h1 h2 t
  calc |F j t + G j t| ≤ |F j t| + |G j t| := abs_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 t) (h2 t)
    _ = ε := by ring

theorem USmall.neg {F : ℕ → ℝ → ℝ} (hF : USmall F) : USmall (fun j t => -F j t) := by
  intro ε hε
  filter_upwards [hF ε hε] with j h t
  simpa using h t

theorem USmall.sub {F G : ℕ → ℝ → ℝ} (hF : USmall F) (hG : USmall G) :
    USmall (fun j t => F j t - G j t) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem USmall.const_mul {F : ℕ → ℝ → ℝ} (hF : USmall F) (c : ℝ) :
    USmall (fun j t => c * F j t) := by
  intro ε hε
  filter_upwards [hF (ε / (|c| + 1)) (by positivity)] with j h t
  rw [abs_mul]
  calc |c| * |F j t| ≤ |c| * (ε / (|c| + 1)) := mul_le_mul_of_nonneg_left (h t) (abs_nonneg _)
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

theorem USmall.mul_bdd {F G : ℕ → ℝ → ℝ} (hF : USmall F) (M : ℝ)
    (hG : ∀ᶠ j in atTop, ∀ t, |G j t| ≤ M) : USmall (fun j t => F j t * G j t) := by
  intro ε hε
  filter_upwards [hF (ε / (|M| + 1)) (by positivity), hG] with j h1 h2 t
  rw [abs_mul]
  calc |F j t| * |G j t| ≤ (ε / (|M| + 1)) * |M| :=
        mul_le_mul (h1 t) ((h2 t).trans (le_abs_self M)) (abs_nonneg _) (by positivity)
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg M]

theorem USmall.of_le {F G : ℕ → ℝ → ℝ} (hG : USmall G) (c : ℝ)
    (h : ∀ᶠ j in atTop, ∀ t, |F j t| ≤ c * |G j t|) : USmall F := by
  intro ε hε
  filter_upwards [hG (ε / (|c| + 1)) (by positivity), h] with j h1 h2 t
  calc |F j t| ≤ c * |G j t| := h2 t
    _ ≤ |c| * (ε / (|c| + 1)) := mul_le_mul (le_abs_self c) (h1 t) (abs_nonneg _) (abs_nonneg _)
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

theorem USmall.bdd {F : ℕ → ℝ → ℝ} (hF : USmall F) : ∀ᶠ j in atTop, ∀ t, |F j t| ≤ 1 :=
  hF 1 one_pos

theorem USmall.of_seq {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) : USmall (fun j _ => a j) := by
  intro ε hε
  have := (tendsto_zero_iff_abs_tendsto_zero _).1 ha
  filter_upwards [this.eventually (gt_mem_nhds hε)] with j h t using h.le

theorem USmall.of_const_mul {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (F : ℕ → ℝ → ℝ) (c : ℝ)
    (h : ∀ j t, |F j t| ≤ c * |a j|) : USmall F :=
  (USmall.of_seq ha).of_le c (Eventually.of_forall h)

/-! ### The explicit data of the log-density ODE -/

/-- The log of the reference density along the circle parametrization. -/
noncomputable def ellF (a c t : ℝ) : ℝ := a * Real.cos (6 * Real.pi * t) - c
/-- Its derivative. -/
noncomputable def sg0 (a t : ℝ) : ℝ := -(6 * Real.pi) * a * Real.sin (6 * Real.pi * t)
/-- Its second derivative. -/
noncomputable def sg1 (a t : ℝ) : ℝ := -(6 * Real.pi) ^ 2 * a * Real.cos (6 * Real.pi * t)
/-- Its third derivative. -/
noncomputable def sg2 (a t : ℝ) : ℝ := (6 * Real.pi) ^ 3 * a * Real.sin (6 * Real.pi * t)

theorem hasDerivAt_ellF (a c t : ℝ) : HasDerivAt (ellF a c) (sg0 a t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 6 * Real.pi * t) (6 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (6 * Real.pi)
  have := (h1.cos.const_mul a).sub_const c
  unfold ellF sg0
  convert this using 1
  ring

theorem hasDerivAt_sg0 (a t : ℝ) : HasDerivAt (sg0 a) (sg1 a t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 6 * Real.pi * t) (6 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (6 * Real.pi)
  have := h1.sin.const_mul (-(6 * Real.pi) * a)
  unfold sg0 sg1
  convert this using 1
  ring

theorem hasDerivAt_sg1 (a t : ℝ) : HasDerivAt (sg1 a) (sg2 a t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 6 * Real.pi * t) (6 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (6 * Real.pi)
  have := h1.cos.const_mul (-(6 * Real.pi) ^ 2 * a)
  unfold sg1 sg2
  convert this using 1
  ring

theorem abs_sg0_le (a t : ℝ) : |sg0 a t| ≤ 6 * Real.pi * |a| := by
  unfold sg0
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 6 * Real.pi)]
  have := Real.abs_sin_le_one (6 * Real.pi * t)
  calc 6 * Real.pi * |a| * |Real.sin (6 * Real.pi * t)| ≤ 6 * Real.pi * |a| * 1 := by gcongr
    _ = _ := by ring

theorem abs_sg1_le (a t : ℝ) : |sg1 a t| ≤ (6 * Real.pi) ^ 2 * |a| := by
  unfold sg1
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < (6 * Real.pi) ^ 2)]
  have := Real.abs_cos_le_one (6 * Real.pi * t)
  calc (6 * Real.pi) ^ 2 * |a| * |Real.cos (6 * Real.pi * t)| ≤ (6 * Real.pi) ^ 2 * |a| * 1 := by gcongr
    _ = _ := by ring

theorem abs_sg2_le (a t : ℝ) : |sg2 a t| ≤ (6 * Real.pi) ^ 3 * |a| := by
  unfold sg2
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (6 * Real.pi) ^ 3)]
  have := Real.abs_sin_le_one (6 * Real.pi * t)
  calc (6 * Real.pi) ^ 3 * |a| * |Real.sin (6 * Real.pi * t)| ≤ (6 * Real.pi) ^ 3 * |a| * 1 := by gcongr
    _ = _ := by ring

theorem abs_ellF_le (a c t : ℝ) : |ellF a c t| ≤ |a| + |c| := by
  unfold ellF
  have := Real.abs_cos_le_one (6 * Real.pi * t)
  calc |a * Real.cos (6 * Real.pi * t) - c| ≤ |a * Real.cos (6 * Real.pi * t)| + |c| := abs_sub _ _
    _ ≤ |a| + |c| := by
      rw [abs_mul]
      have : |a| * |Real.cos (6 * Real.pi * t)| ≤ |a| * 1 := by gcongr
      linarith

/-- `v = A / W`. -/
noncomputable def vF (A W : ℝ → ℝ) (t : ℝ) : ℝ := A t / W t
/-- `f = log W²`. -/
noncomputable def fF (W : ℝ → ℝ) (t : ℝ) : ℝ := Real.log (W t ^ 2)
/-- `v'`. -/
noncomputable def v1F (a c lam : ℝ) (A W : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(vF A W t) * sg0 a t - vF A W t ^ 2 / 2 - lam * (fF W t - ellF a c t)
/-- `f''`. -/
noncomputable def f2F (a c lam : ℝ) (A W : ℝ → ℝ) (t : ℝ) : ℝ := v1F a c lam A W t + sg1 a t
/-- `f'''`. -/
noncomputable def f3F (a c lam : ℝ) (A W : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(v1F a c lam A W t) * sg0 a t - vF A W t * sg1 a t - vF A W t * v1F a c lam A W t
    - lam * vF A W t + sg2 a t

section Chain

variable {a c lam : ℝ} {A W : ℝ → ℝ}

theorem hasDerivAt_fF (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 a t) / 2) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) : HasDerivAt (fF W) (vF A W t + sg0 a t) t := by
  have h := ((hWd t).pow 2).log (pow_pos (hW t) 2).ne'
  unfold fF vF
  convert h using 1
  have := (hW t).ne'
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_vF (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 a t) / 2) t)
    (hAd : ∀ t, HasDerivAt A (-(A t * sg0 a t) / 2 -
      lam * (W t * (fF W t - ellF a c t))) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) : HasDerivAt (vF A W) (v1F a c lam A W t) t := by
  have h := (hAd t).div (hWd t) (hW t).ne'
  unfold vF v1F
  convert h using 1
  have := (hW t).ne'
  unfold vF
  field_simp
  ring

theorem hasDerivAt_v1F (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 a t) / 2) t)
    (hAd : ∀ t, HasDerivAt A (-(A t * sg0 a t) / 2 -
      lam * (W t * (fF W t - ellF a c t))) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) :
    HasDerivAt (v1F a c lam A W) (f3F a c lam A W t - sg2 a t) t := by
  have hv := hasDerivAt_vF hWd hAd hW t
  have hf := hasDerivAt_fF hWd hW t
  have hl := hasDerivAt_ellF a c t
  have hs := hasDerivAt_sg0 a t
  have h := (((hv.neg).mul hs).sub ((hv.pow 2).div_const 2)).sub
    ((hf.sub hl).const_mul lam)
  unfold v1F
  unfold f3F
  convert h using 1
  unfold vF
  simp only [Nat.cast_ofNat, Pi.neg_apply]
  ring

theorem hasDerivAt_f2F (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 a t) / 2) t)
    (hAd : ∀ t, HasDerivAt A (-(A t * sg0 a t) / 2 -
      lam * (W t * (fF W t - ellF a c t))) t)
    (hW : ∀ t, 0 < W t) (t : ℝ) :
    HasDerivAt (f2F a c lam A W) (f3F a c lam A W t) t := by
  have := (hasDerivAt_v1F hWd hAd hW t).add (hasDerivAt_sg1 a t)
  unfold f2F
  convert this using 1
  ring

end Chain

section Regular

variable {α : ℝ} {a c lam : ℝ} {A W : ℝ → ℝ}

theorem isPH_fF (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hWp : Periodic W 1)
    (hWd : ∀ t, HasDerivAt W ((A t + W t * sg0 a t) / 2) t)
    (hAd : ∀ t, HasDerivAt A (-(A t * sg0 a t) / 2 -
      lam * (W t * (fF W t - ellF a c t))) t)
    (hW : ∀ t, 0 < W t) :
    IsPH α 2 (fF W) ∧ deriv (fF W) = (fun t => vF A W t + sg0 a t) ∧
      deriv (fun t => vF A W t + sg0 a t) = f2F a c lam A W ∧
      deriv (f2F a c lam A W) = f3F a c lam A W := by
  have hper : Periodic (fF W) 1 := fun t => by simp [fF, hWp t]
  have hF0 := hasDerivAt_fF hWd hW
  have hF1 : ∀ t, HasDerivAt (fun t => vF A W t + sg0 a t) (f2F a c lam A W t) t := fun t =>
    (hasDerivAt_vF hWd hAd hW t).add (hasDerivAt_sg0 a t)
  have hF2 := hasDerivAt_f2F hWd hAd hW
  have e1 : deriv (fF W) = (fun t => vF A W t + sg0 a t) := funext fun t => (hF0 t).deriv
  have e2 : deriv (fun t => vF A W t + sg0 a t) = f2F a c lam A W := funext fun t => (hF1 t).deriv
  have e3 : deriv (f2F a c lam A W) = f3F a c lam A W := funext fun t => (hF2 t).deriv
  refine ⟨?_, e1, e2, e3⟩
  have hp1 : Periodic (fun t => vF A W t + sg0 a t) 1 := e1 ▸ periodic_deriv hper
  have hp2 : Periodic (f2F a c lam A W) 1 := e2 ▸ periodic_deriv hp1
  have hp3 : Periodic (f3F a c lam A W) 1 := e3 ▸ periodic_deriv hp2
  have hd2 : Differentiable ℝ (f2F a c lam A W) := fun t => (hF2 t).differentiableAt
  have hcv : Continuous (vF A W) := continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_vF hWd hAd hW t).continuousAt
  have hc1 : Continuous (v1F a c lam A W) := continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_v1F hWd hAd hW t).continuousAt
  have hs0 : Continuous (sg0 a) := by unfold sg0; fun_prop
  have hs1 : Continuous (sg1 a) := by unfold sg1; fun_prop
  have hs2 : Continuous (sg2 a) := by unfold sg2; fun_prop
  have hc3 : Continuous (f3F a c lam A W) := by
    have : f3F a c lam A W = fun t => -(v1F a c lam A W t) * sg0 a t - vF A W t * sg1 a t
        - vF A W t * v1F a c lam A W t - lam * vF A W t + sg2 a t := rfl
    rw [this]; fun_prop
  have hb2 : Bdd (f2F a c lam A W) := periodic_bdd hp2 hd2.continuous
  have hb3 : Bdd (f3F a c lam A W) := periodic_bdd hp3 hc3
  refine ⟨hper, fun t => (hF0 t).differentiableAt, ?_⟩
  rw [e1]
  refine ⟨hp1, fun t => (hF1 t).differentiableAt, ?_⟩
  rw [e2]
  refine ⟨hp2, hd2.continuous, ?_⟩
  refine HolderBdd.of_le (C := supNorm (f3F a c lam A W) + 2 * supNorm (f2F a c lam A W))
    (add_nonneg (supNorm_nonneg _) (mul_nonneg two_pos.le (supNorm_nonneg _))) ?_
  have := holder_of_lip (supNorm_nonneg (f3F a c lam A W)) (supNorm_nonneg (f2F a c lam A W))
    hα0 hα1 (u := f2F a c lam A W) (fun x y => by
      have := lip_bound hd2 (by rw [e3]; exact hb3) x y
      rwa [e3] at this) hb2.abs_le_supNorm
  exact this

end Regular

theorem abs_log_sq_le {w : ℝ} (hw : |w - 1| ≤ 1 / 2) : |Real.log (w ^ 2)| ≤ 4 * |w - 1| := by
  have hw0 : 0 < w := by have := (abs_le.1 hw).1; linarith
  have h1 := Real.log_le_sub_one_of_pos hw0
  have h2 := Real.one_sub_inv_le_log_of_pos hw0
  have hl : Real.log (w ^ 2) = 2 * Real.log w := by
    rw [Real.log_pow]; norm_num
  rw [hl, abs_mul, abs_two]
  have hinv : 1 - w⁻¹ = (w - 1) / w := by field_simp
  have h3 : -(2 * |w - 1|) ≤ Real.log w := by
    have : -(2 * |w - 1|) ≤ (w - 1) / w := by
      rw [le_div_iff₀ hw0]
      have h4 := neg_abs_le (w - 1)
      have h5 : w ≥ 1 / 2 := by have := (abs_le.1 hw).1; linarith
      nlinarith [abs_nonneg (w - 1)]
    linarith
  have h6 : Real.log w ≤ |w - 1| := h1.trans (le_abs_self _)
  have : |Real.log w| ≤ 2 * |w - 1| := abs_le.2 ⟨by linarith, by linarith [abs_nonneg (w - 1)]⟩
  linarith

theorem USmall.of_abs_le {F : ℕ → ℝ → ℝ} {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (h : ∀ j t, |F j t| ≤ b j) : USmall F := by
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with j hj t using (h j t).trans hj.le

theorem USmall.congr {F G : ℕ → ℝ → ℝ} (h : ∀ j t, F j t = G j t) (hG : USmall G) : USmall F := by
  intro ε hε
  filter_upwards [hG ε hε] with j hj t
  rw [h]; exact hj t

/-- The uniform-smallness step of the bootstrap: a sequence of solutions of the (W, A) system
with `W → 1` and `A → 0` uniformly has `log W²` tending to `0` in `C^{2,α}`. -/
theorem ode_logDensity_small {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {a c lam : ℕ → ℝ} {A W : ℕ → ℝ → ℝ} (Λ : ℝ)
    (ha : Tendsto a atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (hlam0 : ∀ j, 0 ≤ lam j) (hlam : ∀ j, lam j ≤ Λ)
    (hWp : ∀ j, Periodic (W j) 1)
    (hWd : ∀ j t, HasDerivAt (W j) ((A j t + W j t * sg0 (a j) t) / 2) t)
    (hAd : ∀ j t, HasDerivAt (A j) (-(A j t * sg0 (a j) t) / 2 -
      lam j * (W j t * (fF (W j) t - ellF (a j) (c j) t))) t)
    (hW1 : USmall (fun j t => W j t - 1)) (hA0 : USmall A) :
    ∀ ε > 0, ∀ᶠ j in atTop, (∀ t, 0 < W j t) ∧ IsPH α 2 (fF (W j)) ∧
      phNorm α 2 (fF (W j)) ≤ ε := by
  have haabs : Tendsto (fun j => |a j|) atTop (𝓝 0) := by simpa using ha.abs
  have hcabs : Tendsto (fun j => |c j|) atTop (𝓝 0) := by simpa using hc.abs
  have hlow : ∀ᶠ j in atTop, ∀ t, |W j t - 1| ≤ 1 / 2 := hW1 (1 / 2) (by norm_num)
  have hpos : ∀ᶠ j in atTop, ∀ t, 0 < W j t := by
    filter_upwards [hlow] with j hj t
    have := (abs_le.1 (hj t)).1; linarith
  -- the small quantities
  have hs0 : USmall (fun j t => sg0 (a j) t) :=
    USmall.of_abs_le (b := fun j => 6 * Real.pi * |a j|) (by simpa using haabs.const_mul (6 * Real.pi))
      (fun j t => abs_sg0_le _ _)
  have hs1 : USmall (fun j t => sg1 (a j) t) :=
    USmall.of_abs_le (b := fun j => (6 * Real.pi) ^ 2 * |a j|)
      (by simpa using haabs.const_mul ((6 * Real.pi) ^ 2)) (fun j t => abs_sg1_le _ _)
  have hs2 : USmall (fun j t => sg2 (a j) t) :=
    USmall.of_abs_le (b := fun j => (6 * Real.pi) ^ 3 * |a j|)
      (by simpa using haabs.const_mul ((6 * Real.pi) ^ 3)) (fun j t => abs_sg2_le _ _)
  have hel : USmall (fun j t => ellF (a j) (c j) t) :=
    USmall.of_abs_le (b := fun j => |a j| + |c j|) (by simpa using haabs.add hcabs)
      (fun j t => abs_ellF_le _ _ _)
  have hV : USmall (fun j t => vF (A j) (W j) t) := by
    refine hA0.of_le 2 ?_
    filter_upwards [hlow] with j hj t
    have h1 := (abs_le.1 (hj t)).1
    have hw : 1 / 2 ≤ W j t := by linarith
    unfold vF
    rw [abs_div, abs_of_pos (by linarith : 0 < W j t), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (A j t)]
  have hF : USmall (fun j t => fF (W j) t) := by
    refine hW1.of_le 4 ?_
    filter_upwards [hlow] with j hj t
    exact abs_log_sq_le (hj t)
  have hlamb : ∀ᶠ j in atTop, ∀ t : ℝ, |lam j| ≤ Λ := Eventually.of_forall fun j t => by
    rw [abs_of_nonneg (hlam0 j)]; exact hlam j
  have hs0b := hs0.bdd
  have hVb := hV.bdd
  have hF1 : USmall (fun j t => vF (A j) (W j) t + sg0 (a j) t) := hV.add hs0
  have hv1 : USmall (fun j t => v1F (a j) (c j) (lam j) (A j) (W j) t) := by
    have e1 : USmall (fun j t => -(vF (A j) (W j) t) * sg0 (a j) t) := hV.neg.mul_bdd 1 hs0b
    have e2 : USmall (fun j t => vF (A j) (W j) t ^ 2 / 2) := by
      refine USmall.congr (fun j t => by ring) ((hV.mul_bdd 1 hVb).const_mul (1 / 2))
    have e3 : USmall (fun j t => (fF (W j) t - ellF (a j) (c j) t) * lam j) :=
      (hF.sub hel).mul_bdd Λ hlamb
    refine USmall.congr (fun j t => ?_) ((e1.sub e2).sub e3)
    unfold v1F; ring
  have hv1b := hv1.bdd
  have hF2 : USmall (fun j t => f2F (a j) (c j) (lam j) (A j) (W j) t) :=
    hv1.add hs1
  have hF3 : USmall (fun j t => f3F (a j) (c j) (lam j) (A j) (W j) t) := by
    have e1 : USmall (fun j t => -(v1F (a j) (c j) (lam j) (A j) (W j) t) * sg0 (a j) t) :=
      hv1.neg.mul_bdd 1 hs0b
    have e2 : USmall (fun j t => vF (A j) (W j) t * sg1 (a j) t) := hV.mul_bdd 1 hs1.bdd
    have e3 : USmall (fun j t => vF (A j) (W j) t * v1F (a j) (c j) (lam j) (A j) (W j) t) :=
      hV.mul_bdd 1 hv1b
    have e4 : USmall (fun j t => vF (A j) (W j) t * lam j) := hV.mul_bdd Λ hlamb
    refine USmall.congr (fun j t => ?_) ((((e1.sub e2).sub e3).sub e4).add hs2)
    unfold f3F; ring
  intro ε hε
  have hε6 : 0 < ε / 6 := by positivity
  filter_upwards [hpos, hF (ε / 6) hε6, hF1 (ε / 6) hε6, hF2 (ε / 6) hε6, hF3 (ε / 6) hε6]
    with j hj hf0 hf1 hf2 hf3
  obtain ⟨hph, e1, e2, e3⟩ := isPH_fF hα0.le hα1.le (hWp j) (hWd j) (hAd j) hj
  refine ⟨hj, hph, ?_⟩
  have hb2 : Bdd (f2F (a j) (c j) (lam j) (A j) (W j)) := ⟨ε / 6, hf2⟩
  have hd2 : Differentiable ℝ (f2F (a j) (c j) (lam j) (A j) (W j)) := fun t =>
    (hasDerivAt_f2F (hWd j) (hAd j) hj t).differentiableAt
  have hb3 : Bdd (deriv (f2F (a j) (c j) (lam j) (A j) (W j))) := by
    rw [e3]; exact ⟨ε / 6, hf3⟩
  have hhold := holderSeminorm_le_succ hα0.le hα1.le hd2 hb2 hb3
  have s0 : supNorm (fF (W j)) ≤ ε / 6 := supNorm_le hf0
  have s1 : supNorm (fun t => vF (A j) (W j) t + sg0 (a j) t) ≤ ε / 6 := supNorm_le hf1
  have s2 : supNorm (f2F (a j) (c j) (lam j) (A j) (W j)) ≤ ε / 6 := supNorm_le hf2
  have s3 : supNorm (deriv (f2F (a j) (c j) (lam j) (A j) (W j))) ≤ ε / 6 := by
    rw [e3]; exact supNorm_le hf3
  have hnorm : phNorm α 2 (fF (W j)) = supNorm (fF (W j)) + (supNorm (deriv (fF (W j))) +
      (supNorm (deriv (deriv (fF (W j)))) + holderSeminorm α (deriv (deriv (fF (W j)))))) := by
    simp [phNorm]
  rw [hnorm, e1, e2]
  linarith

/-- Logarithm of the ordinary reference density, as a function on the torus. -/
noncomputable def ellT (h : ℝ) : Torus 1 → ℝ := fun x => Real.log ((ordinaryReference h).density x)

theorem ellT_lift (h : ℝ) (y : Fin 1 → ℝ) :
    ellT h (torusLift y) = h * Real.cos (2 * Real.pi * ((3:ℕ):ℝ) * y 0) - Real.log (besselI 0 h) := by
  unfold ellT
  show Real.log (Real.exp (h * cosHarm 3 (torusLift y)) / besselI 0 h) = _
  rw [Real.log_div (Real.exp_pos _).ne' besselI_zero_pos.ne', Real.log_exp, cosHarm_lift]

theorem ellT_lift_one (h t : ℝ) :
    ellT h (torusLift fun _ => t) = ellF h (Real.log (besselI 0 h)) t := by
  rw [ellT_lift]
  unfold ellF
  congr 2
  push_cast
  ring_nf

theorem isSmoothPeriodic_ellT (h : ℝ) : IsSmoothPeriodic (ellT h) := by
  unfold IsSmoothPeriodic
  have : (ellT h ∘ torusLift) = fun y : Fin 1 → ℝ =>
      h * Real.cos (2 * Real.pi * ((3:ℕ):ℝ) * y 0) - Real.log (besselI 0 h) := by
    funext y; exact ellT_lift h y
  rw [this]
  fun_prop

/-- The (smooth) score `∂ ℓ`. -/
noncomputable def sigT (h : ℝ) : Torus 1 → ℝ := coordPartial 0 (ellT h)

theorem sigT_lift (h t : ℝ) : sigT h (torusLift fun _ => t) = sg0 h t := by
  have h1 := hasDerivAt_smooth_one (isSmoothPeriodic_ellT h) t
  have h2 : HasDerivAt (fun t : ℝ => ellT h (torusLift fun _ => t)) (sg0 h t) t := by
    have : (fun t : ℝ => ellT h (torusLift fun _ => t)) = ellF h (Real.log (besselI 0 h)) := by
      funext s; exact ellT_lift_one h s
    rw [this]; exact hasDerivAt_ellF _ _ _
  exact h1.unique h2

theorem continuous_sigT (h : ℝ) : Continuous (sigT h) :=
  (isSmoothPeriodic_ellT h).continuous_coordPartial 0

theorem bs_exists_pt (x : Torus 1) : ∃ t : ℝ, pt t = x := by
  refine ⟨SharpLSI.secT x 0, ?_⟩
  have h := SharpLSI.liftT_secT x
  have e : (fun _ : Fin 1 => SharpLSI.secT x 0) = SharpLSI.secT x := by
    funext i; fin_cases i; rfl
  show SharpLSI.liftT (fun _ : Fin 1 => SharpLSI.secT x 0) = x
  rw [e]; exact h

theorem abs_sigT_le (h : ℝ) (x : Torus 1) : |sigT h x| ≤ 6 * Real.pi * |h| := by
  obtain ⟨t, rfl⟩ := bs_exists_pt x
  rw [sigT_lift]
  exact abs_sg0_le h t

theorem logScore_ae_eq (h : ℝ) : logScore h =ᵐ[haar 1] sigT h := by
  have h1 := isWeakGradient_weakGradient ((ordinaryReference h).memH1_log (ordinaryReference_lip h))
  have h2 := (isSmoothPeriodic_ellT h).isWeakGradient
  have := h1.ae_eq h2
  filter_upwards [this] with x hx
  unfold logScore sigT
  exact congrArg (fun v => v 0) hx


theorem bs_memLp_top {f : Torus 1 → ℝ} (hc : Continuous f) : MemLp f ∞ (haar 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact memLp_top_of_bound hc.aestronglyMeasurable C
    (Eventually.of_forall fun x => hC x (Set.mem_univ x))

/-- A scalar function viewed as a vector field in the (only) coordinate. -/
noncomputable def vec1 (f : Torus 1 → ℝ) : Torus 1 → Tangent 1 :=
  fun x => f x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)

@[simp] theorem vec1_apply (f : Torus 1 → ℝ) (x : Torus 1) : vec1 f x 0 = f x := by
  simp [vec1]

theorem norm_vec1 (f : Torus 1 → ℝ) (x : Torus 1) : ‖vec1 f x‖ = |f x| := by
  simp [vec1, norm_smul]

theorem memLp_vec1 {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) : MemLp (vec1 f) 2 (haar 1) := by
  refine hf.mono ?_ (Eventually.of_forall fun x => ?_)
  · exact hf.aestronglyMeasurable.smul aestronglyMeasurable_const
  · simp [norm_vec1]

theorem vec1_ae {f g : Torus 1 → ℝ} (hfg : f =ᵐ[haar 1] g) : vec1 f =ᵐ[haar 1] vec1 g := by
  filter_upwards [hfg] with x hx
  simp [vec1, hx]

/-- The weak Euler equation, rewritten with the continuous representative `Wc`: the function
`A = 2 ∂w - Wc σ` has the weak derivative `-(A σ)/2 - λ Wc (log Wc² - ℓ)`. -/
theorem bs_weak_A (h : ℝ) (ρ : AbsoluteDensity 1) (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ')
    {Wc : Torus 1 → ℝ} (hWc : Continuous Wc) (hae : Wc =ᵐ[haar 1] ρ.sqrt)
    (hW0 : ∀ x, 0 < Wc x) :
    IsWeakGradient (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - Wc x * sigT h x)
      (vec1 fun x => -((2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - Wc x * sigT h x) * sigT h x) / 2
        - (str025_quot h ρ).toReal * (Wc x * (Real.log (Wc x ^ 2) - ellT h x))) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨Gw, hGw⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  rw [← hGw] at hw ⊢
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (str025_quot h ρ).toReal := ⟨_, rfl⟩
  rw [← hlam]
  have hσc := continuous_sigT h
  have hellc : Continuous (ellT h) := (isSmoothPeriodic_ellT h).continuous_torus
  have hRc : Continuous (fun x => Wc x * (Real.log (Wc x ^ 2) - ellT h x)) :=
    hWc.mul (((hWc.pow 2).log fun x => (pow_pos (hW0 x) 2).ne').sub hellc)
  have hAmem : MemLp (fun x => 2 * Gw x 0 - Wc x * sigT h x) 2 (haar 1) :=
    ((memLp_coord hw.memLp_grad 0).const_mul 2).sub (memLp_two_of_continuous (hWc.mul hσc))
  obtain ⟨S, hS⟩ : ∃ S, ∀ x, |sigT h x| ≤ S := ⟨_, abs_sigT_le h⟩
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS 0)
  have hAσ : MemLp (fun x => (2 * Gw x 0 - Wc x * sigT h x) * sigT h x) 2 (haar 1) := by
    refine (hAmem.const_mul S).mono ((hAmem.aestronglyMeasurable.mul hσc.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg hS0]
    nlinarith [hS x, abs_nonneg (2 * Gw x 0 - Wc x * sigT h x)]
  have hg1 : MemLp (fun x => -((2 * Gw x 0 - Wc x * sigT h x) * sigT h x) / 2
        - lam * (Wc x * (Real.log (Wc x ^ 2) - ellT h x))) 2 (haar 1) := by
    have := (hAσ.const_mul (-(1/2:ℝ))).sub ((memLp_two_of_continuous hRc).const_mul lam)
    refine this.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  refine ⟨hAmem, memLp_vec1 hg1, ?_⟩
  intro φ hφ j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have E := ordinaryOptimizer_weakEuler h ρ hpos hmin hφ.isWeakGradient
  rw [← hGw, ← hlam] at E
  have hφc : Continuous φ := hφ.continuous_torus
  have hφ'c : Continuous (coordPartial 0 φ) := hφ.continuous_coordPartial 0
  have hL : ∫ x, (2 * Gw x 0 - ρ.sqrt x * logScore h x) * (2 * smoothGrad φ x 0 - φ x * logScore h x)
        ∂haar 1 =
      ∫ x, (2 * ((2 * Gw x 0 - Wc x * sigT h x) * coordPartial 0 φ x) -
        (2 * Gw x 0 - Wc x * sigT h x) * (sigT h x * φ x)) ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hae, logScore_ae_eq h] with x h1 h2
    rw [← h1, h2, smoothGrad_apply]
    ring
  have hR : ∫ x, ρ.sqrt x * φ x * (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1 =
      ∫ x, (Wc x * (Real.log (Wc x ^ 2) - ellT h x)) * φ x ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with x h1
    rw [← h1]
    have : ellT h x = Real.log (referenceDensity h x) := rfl
    rw [this]; ring
  rw [hL, hR] at E
  have i1 : Integrable (fun x => (2 * Gw x 0 - Wc x * sigT h x) * coordPartial 0 φ x) (haar 1) :=
    integrable_mul_of_memLp_two hAmem (bs_memLp_top hφ'c)
  have i2 : Integrable (fun x => (2 * Gw x 0 - Wc x * sigT h x) * (sigT h x * φ x)) (haar 1) :=
    integrable_mul_of_memLp_two hAmem (bs_memLp_top (hσc.mul hφc))
  have i3 : Integrable (fun x => (Wc x * (Real.log (Wc x ^ 2) - ellT h x)) * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous hRc) (bs_memLp_top hφc)
  rw [integral_sub (i1.const_mul 2) i2, integral_const_mul] at E
  have hI : ∫ x, vec1 (fun x => -((2 * Gw x 0 - Wc x * sigT h x) * sigT h x) / 2
        - lam * (Wc x * (Real.log (Wc x ^ 2) - ellT h x))) x 0 * φ x ∂haar 1 =
      -((1/2) * ∫ x, (2 * Gw x 0 - Wc x * sigT h x) * (sigT h x * φ x) ∂haar 1) -
        lam * ∫ x, (Wc x * (Real.log (Wc x ^ 2) - ellT h x)) * φ x ∂haar 1 := by
    simp only [vec1_apply]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_neg, ← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    · exact (i2.const_mul _).neg
    · exact i3.const_mul _
  rw [hI]
  linarith

theorem continuous_vec1 {f : Torus 1 → ℝ} (hf : Continuous f) : Continuous (vec1 f) :=
  hf.smul continuous_const

theorem bs_integral_grad {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hu : IsWeakGradient u g) :
    ∫ x, g x 0 ∂haar 1 = 0 := by
  have h1 : IsSmoothPeriodic (fun _ : Torus 1 => (1:ℝ)) := contDiff_const
  have := hu.ibp _ h1 0
  have h0 : coordPartial 0 (fun _ : Torus 1 => (1:ℝ)) = fun _ => 0 := by
    funext x; simp [coordPartial, Function.comp_def]
  simp [h0] at this
  linarith

theorem bs_Wc_pos {Wc : Torus 1 → ℝ} {δ : ℝ} (hδ0 : δ ≤ 1 / 2) (hδ : ∀ x, |Wc x - 1| ≤ δ)
    (x : Torus 1) : 0 < Wc x := by
  have := (abs_le.1 (hδ x)).1
  linarith

theorem bs_R_bound (h : ℝ) {Wc : Torus 1 → ℝ} {δ : ℝ} (hδ0 : δ ≤ 1 / 2)
    (hδ : ∀ x, |Wc x - 1| ≤ δ) (x : Torus 1) :
    |Wc x * (Real.log (Wc x ^ 2) - ellT h x)| ≤
      (1 + δ) * (4 * δ + (|h| + |Real.log (besselI 0 h)|)) := by
  have hδp : 0 ≤ δ := (abs_nonneg _).trans (hδ x)
  have hx := hδ x
  have h1 : |Wc x| ≤ 1 + δ := by
    have := abs_le.1 hx
    rw [abs_le]; constructor <;> linarith [this.1, this.2, hδp]
  have h2 : |Real.log (Wc x ^ 2)| ≤ 4 * δ := by
    have := abs_log_sq_le (hx.trans hδ0)
    linarith
  have h3 : |ellT h x| ≤ |h| + |Real.log (besselI 0 h)| := by
    obtain ⟨t, rfl⟩ := bs_exists_pt x
    have := abs_ellF_le h (Real.log (besselI 0 h)) t
    rwa [← ellT_lift_one] at this
  rw [abs_mul]
  have h4 : |Real.log (Wc x ^ 2) - ellT h x| ≤ 4 * δ + (|h| + |Real.log (besselI 0 h)|) :=
    (abs_sub _ _).trans (add_le_add h2 h3)
  exact mul_le_mul h1 h4 (abs_nonneg _) (by linarith)

theorem bootstrap_single (h : ℝ) (ρ : AbsoluteDensity 1) (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      str025_quot h ρ ≤ str025_quot h ρ')
    {Wc : Torus 1 → ℝ} (hWc : Continuous Wc) (hae : Wc =ᵐ[haar 1] ρ.sqrt)
    {δ : ℝ} (hδ0 : δ ≤ 1 / 2) (hδ : ∀ x, |Wc x - 1| ≤ δ) (hS1 : 6 * Real.pi * |h| ≤ 1) :
    ∃ Ac : Torus 1 → ℝ, Continuous Ac ∧
      (∀ t, HasDerivAt (fun s => Wc (pt s)) ((Ac (pt t) + Wc (pt t) * sg0 h t) / 2) t) ∧
      (∀ t, HasDerivAt (fun s => Ac (pt s))
        (-(Ac (pt t) * sg0 h t) / 2 - (str025_quot h ρ).toReal *
          (Wc (pt t) * (fF (fun s => Wc (pt s)) t - ellF h (Real.log (besselI 0 h)) t))) t) ∧
      ∀ x, |Ac x| ≤ 2 * ((1 + δ) * (6 * Real.pi * |h|) + (str025_quot h ρ).toReal *
          ((1 + δ) * (4 * δ + (|h| + |Real.log (besselI 0 h)|)))) := by
  have hW0 : ∀ x, 0 < Wc x := bs_Wc_pos hδ0 hδ
  have hA := bs_weak_A h ρ hpos hmin hWc hae hW0
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨Gw, hGw⟩ : ∃ Gw, Gw = weakGradient ρ.sqrt ρ.sqrt_mem := ⟨_, rfl⟩
  rw [← hGw] at hw hA
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = (str025_quot h ρ).toReal := ⟨_, rfl⟩
  rw [← hlam] at hA ⊢
  have hlam0 : 0 ≤ lam := hlam ▸ ENNReal.toReal_nonneg
  have hσc := continuous_sigT h
  have hellc : Continuous (ellT h) := (isSmoothPeriodic_ellT h).continuous_torus
  have hRc : Continuous (fun x => Wc x * (Real.log (Wc x ^ 2) - ellT h x)) :=
    hWc.mul (((hWc.pow 2).log fun x => (pow_pos (hW0 x) 2).ne').sub hellc)
  obtain ⟨AT, hAT⟩ : ∃ AT : Torus 1 → ℝ, AT = fun x => 2 * Gw x 0 - Wc x * sigT h x := ⟨_, rfl⟩
  obtain ⟨RT, hRT⟩ : ∃ RT : Torus 1 → ℝ,
      RT = fun x => Wc x * (Real.log (Wc x ^ 2) - ellT h x) := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ g1 : Torus 1 → ℝ,
      g1 = fun x => -(AT x * sigT h x) / 2 - lam * RT x := ⟨_, rfl⟩
  have hA' : IsWeakGradient AT (vec1 g1) := by rw [hg1, hAT, hRT]; exact hA
  have hRc' : Continuous RT := by rw [hRT]; exact hRc
  obtain ⟨Ac, hAc, hAae, -, hmean⟩ := circle_H1_holder_half hA'
  obtain ⟨g1c, hg1c⟩ : ∃ g1c : Torus 1 → ℝ,
      g1c = fun x => -(Ac x * sigT h x) / 2 - lam * RT x := ⟨_, rfl⟩
  have hg1cc : Continuous g1c := by
    rw [hg1c]; exact ((hAc.mul hσc).neg.div_const 2).sub (continuous_const.mul hRc')
  have hg1ae : g1 =ᵐ[haar 1] g1c := by
    filter_upwards [hAae] with x hx
    rw [hg1, hg1c]; simp only [hx]
  have hAw : IsWeakGradient Ac (vec1 g1) := hA'.congr_ae hAae.symm (ae_eq_refl _)
  obtain ⟨hAd, -⟩ := circle_duBoisReymond hAc hAw (continuous_vec1 hg1cc) (vec1_ae hg1ae)
  -- the equation for `W`
  have hwW : IsWeakGradient Wc Gw := hw.congr_ae hae.symm (ae_eq_refl _)
  obtain ⟨gW, hgW⟩ : ∃ gW : Torus 1 → ℝ, gW = fun x => (Ac x + Wc x * sigT h x) / 2 := ⟨_, rfl⟩
  have hgWc : Continuous gW := by
    rw [hgW]; exact (hAc.add (hWc.mul hσc)).div_const 2
  have hGae : Gw =ᵐ[haar 1] vec1 gW := by
    filter_upwards [hAae] with x hx
    have h0 : Gw x 0 = gW x := by
      rw [hgW]; simp only; rw [hx, hAT]; simp only; ring
    ext i
    fin_cases i
    simpa using h0
  obtain ⟨hWd, -⟩ := circle_duBoisReymond hWc hwW (continuous_vec1 hgWc) hGae
  -- the sup bound
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hAc.abs.continuousOn
  have hM : ∀ x, |Ac x| ≤ |Ac x0| := fun x => hx0 (Set.mem_univ x)
  have hδp : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set S : ℝ := 6 * Real.pi * |h| with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hσb : ∀ x, |sigT h x| ≤ S := abs_sigT_le h
  set Rb : ℝ := (1 + δ) * (4 * δ + (|h| + |Real.log (besselI 0 h)|)) with hRbdef
  have hRb0 : 0 ≤ Rb := by positivity
  have hRb : ∀ x, |RT x| ≤ Rb := fun x => by rw [hRT]; exact bs_R_bound h hδ0 hδ x
  set M : ℝ := |Ac x0| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg _
  have hC0 : 0 ≤ M * S / 2 + lam * Rb := by positivity
  have hnb : ∀ᵐ x ∂haar 1, ‖vec1 g1 x‖ ≤ M * S / 2 + lam * Rb := by
    filter_upwards [hAae] with x hx
    rw [norm_vec1, hg1]
    simp only
    rw [← hx]
    have e1 : |-(Ac x * sigT h x) / 2| ≤ M * S / 2 := by
      rw [abs_div, abs_neg, abs_mul, abs_two]
      have := mul_le_mul (hM x) (hσb x) (abs_nonneg _) hM0
      linarith
    have e2 : |lam * RT x| ≤ lam * Rb := by
      rw [abs_mul, abs_of_nonneg hlam0]
      exact mul_le_mul_of_nonneg_left (hRb x) hlam0
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  have hg1m : MemLp (vec1 g1) 2 (haar 1) := hA'.memLp_grad
  have hel : (eLpNorm (vec1 g1) 2 (haar 1)).toReal ≤ M * S / 2 + lam * Rb := by
    have := eLpNorm_le_of_ae_bound (p := 2) hg1m.aestronglyMeasurable hnb
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at this
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
    rwa [ENNReal.toReal_ofReal hC0] at h2
  have hmean0 : |∫ y, AT y ∂haar 1| ≤ (1 + δ) * S := by
    have hint : ∫ y, AT y ∂haar 1 = -∫ y, Wc y * sigT h y ∂haar 1 := by
      rw [hAT]
      simp only
      have iW : Integrable (fun y => Wc y * sigT h y) (haar 1) :=
        (memLp_two_of_continuous (hWc.mul hσc)).integrable one_le_two
      rw [integral_sub (((memLp_coord hw.memLp_grad 0).integrable one_le_two).const_mul 2) iW,
        integral_const_mul, bs_integral_grad hw]
      ring
    have hb : ∀ x, ‖Wc x * sigT h x‖ ≤ (1 + δ) * S := fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Wc x| ≤ 1 + δ := by
        have := abs_le.1 (hδ x)
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      exact mul_le_mul h1 (hσb x) (abs_nonneg _) (by linarith)
    have := norm_integral_le_of_norm_le_const (μ := haar 1) (f := fun y => Wc y * sigT h y)
      (Eventually.of_forall hb)
    simp at this
    rw [hint, abs_neg]
    simpa using this
  have hfin : M ≤ (1 + δ) * S + (M * S / 2 + lam * Rb) := by
    have h1 := hmean x0
    have h2 : |Ac x0| ≤ |Ac x0 - ∫ y, AT y ∂haar 1| + |∫ y, AT y ∂haar 1| := by
      have := abs_sub_abs_le_abs_sub (Ac x0) (∫ y, AT y ∂haar 1)
      have h3 := abs_add_le (Ac x0 - ∫ y, AT y ∂haar 1) (∫ y, AT y ∂haar 1)
      simpa using h3
    linarith
  have hMle : M ≤ 2 * ((1 + δ) * S + lam * Rb) := by
    nlinarith [mul_le_mul_of_nonneg_left hS1 hM0]
  refine ⟨Ac, hAc, ?_, ?_, fun x => (hM x).trans hMle⟩
  · intro t
    have := hWd t
    simp only [vec1_apply, hgW, sigT_lift] at this
    exact this
  · intro t
    have := hAd t
    simp only [vec1_apply, hg1c, hRT, sigT_lift, ellT_lift_one] at this
    exact this

theorem ev_shift {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ j in atTop, P (j + N)) :
    ∀ᶠ j in atTop, P j := by
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  refine eventually_atTop.2 ⟨M + N, fun j hj => ?_⟩
  have := hM (j - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at this

theorem abs_log_besselI_zero_le (h : ℝ) : |Real.log (besselI 0 h)| ≤ |h| := by
  have h1 := exp_neg_le_besselI_zero h
  have h2 := besselI_zero_le h
  have hp : 0 < besselI 0 h := besselI_zero_pos
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this
    linarith [neg_abs_le h]
  · have := Real.log_le_log hp h2
    rw [Real.log_exp] at this
    exact this

/-- The ODE-side statement with all eventual conditions assumed for every index. -/
theorem bs_aux {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    (Wc : ℕ → Torus 1 → ℝ) (hWc : ∀ j, Continuous (Wc j))
    (hae : ∀ j, Wc j =ᵐ[haar 1] (ρ j).sqrt)
    (δ : ℕ → ℝ) (hδ0 : ∀ j, δ j ≤ 1 / 2) (hδ : ∀ j x, |Wc j x - 1| ≤ δ j)
    (hδt : Tendsto δ atTop (𝓝 0))
    (hS : ∀ j, 6 * Real.pi * |h j| ≤ 1) (Λ : ℝ)
    (hlam : ∀ j, (str025_quot (h j) (ρ j)).toReal ≤ Λ) :
    ∀ ε > 0, ∀ᶠ j in atTop, (∀ t, 0 < Wc j (pt t)) ∧
      IsPH α 2 (fF (fun s => Wc j (pt s))) ∧ phNorm α 2 (fF (fun s => Wc j (pt s))) ≤ ε := by
  have hex : ∀ j, ∃ Ac : Torus 1 → ℝ, Continuous Ac ∧
      (∀ t, HasDerivAt (fun s => Wc j (pt s)) ((Ac (pt t) + Wc j (pt t) * sg0 (h j) t) / 2) t) ∧
      (∀ t, HasDerivAt (fun s => Ac (pt s))
        (-(Ac (pt t) * sg0 (h j) t) / 2 - (str025_quot (h j) (ρ j)).toReal *
          (Wc j (pt t) * (fF (fun s => Wc j (pt s)) t -
            ellF (h j) (Real.log (besselI 0 (h j))) t))) t) ∧
      ∀ x, |Ac x| ≤ 2 * ((1 + δ j) * (6 * Real.pi * |h j|) + (str025_quot (h j) (ρ j)).toReal *
        ((1 + δ j) * (4 * δ j + (|h j| + |Real.log (besselI 0 (h j))|)))) := fun j =>
    bootstrap_single (h j) (ρ j) (hpos j) (fun ρ' hρ' => hmin j ρ' hρ') (hWc j) (hae j)
      (hδ0 j) (hδ j) (hS j)
  choose Ac hAc hWd hAd hAb using hex
  set lam : ℕ → ℝ := fun j => (str025_quot (h j) (ρ j)).toReal with hlamdef
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => ENNReal.toReal_nonneg
  have hc : Tendsto (fun j => Real.log (besselI 0 (h j))) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => ?_) (by simpa using hh.abs)
    rw [Real.norm_eq_abs]; exact abs_log_besselI_zero_le _
  have hW1 : USmall (fun j t => Wc j (pt t) - 1) := by
    intro ε hε
    filter_upwards [(tendsto_order.1 hδt).2 ε hε] with j hj t
    exact (hδ j _).trans hj.le
  have hB : Tendsto (fun j => 2 * ((1 + δ j) * (6 * Real.pi * |h j|) + Λ *
      ((1 + δ j) * (4 * δ j + (|h j| + |Real.log (besselI 0 (h j))|))))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => |h j|) atTop (𝓝 0) := by simpa using hh.abs
    have h2 : Tendsto (fun j => |Real.log (besselI 0 (h j))|) atTop (𝓝 0) := by
      simpa using hc.abs
    have := (((tendsto_const_nhds (x := (1:ℝ))).add hδt).mul
      ((tendsto_const_nhds (x := 6 * Real.pi)).mul h1)).add
      ((tendsto_const_nhds (x := Λ)).mul (((tendsto_const_nhds (x := (1:ℝ))).add hδt).mul
        (((tendsto_const_nhds (x := (4:ℝ))).mul hδt).add (h1.add h2))))
    simpa using (tendsto_const_nhds (x := (2:ℝ))).mul this
  have hA0 : USmall (fun j t => Ac j (pt t)) := by
    intro ε hε
    filter_upwards [(tendsto_order.1 hB).2 ε hε] with j hj t
    refine (hAb j (pt t)).trans (le_trans ?_ hj.le)
    have hd0 : 0 ≤ 1 + δ j := by
      have := (abs_nonneg (Wc j 0 - 1)).trans (hδ j 0); linarith
    have hl := hlam j
    have hnn : 0 ≤ (1 + δ j) * (4 * δ j + (|h j| + |Real.log (besselI 0 (h j))|)) := by
      have : 0 ≤ δ j := (abs_nonneg _).trans (hδ j 0)
      positivity
    nlinarith [mul_le_mul_of_nonneg_right hl hnn]
  have hper : ∀ j, Periodic (fun s => Wc j (pt s)) 1 := fun j s => by
    show Wc j (pt (s + 1)) = Wc j (pt s)
    show Wc j (torusLift fun _ => s + 1) = _
    rw [torusLift_one_add]
  exact ode_logDensity_small hα0 hα1 (a := h) (c := fun j => Real.log (besselI 0 (h j)))
    (lam := lam) (A := fun j t => Ac j (pt t)) (W := fun j s => Wc j (pt s)) Λ hh hc hlam0
    hlam hper hWd hAd hW1 hA0

theorem tendsto_eLpNorm_of_toReal {f : ℕ → ℝ≥0∞} (hfin : ∀ n, f n ≠ ⊤)
    (h : Tendsto (fun n => (f n).toReal) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_iff hfin ENNReal.zero_ne_top).1 (by simpa using h)

/-- **C^{2,α} bootstrap for the ordinary optimizers.**  Under the hypotheses of
`ordinaryOptimizer_globalLocalization_H1`, for every `α ∈ (0,1)` there are 1-periodic profiles
`f j : ℝ → ℝ` with `phNorm α 2 (f j) → 0`, and eventually `f j` is a `C^{2,α}` periodic function
with `ρ_j = exp (f j)` almost everywhere on the circle (via `torusLift`). -/
theorem ordinaryOptimizer_logDensity_C2alpha (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (ρ : ℕ → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy (h j) (ρ j))
    (hmin : ∀ j, ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy (h j) ρ' →
      ordinaryFisher (h j) (ρ j) / (2 * ordinaryEntropy (h j) (ρ j)) ≤
        ordinaryFisher (h j) ρ' / (2 * ordinaryEntropy (h j) ρ'))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ f : ℕ → ℝ → ℝ,
      (∀ᶠ j in atTop, Periodic (f j) 1 ∧ IsPH α 2 (f j) ∧
        ∀ᵐ x ∂haar 1, ∀ s : ℝ, torusLift (fun _ => s) = x → (ρ j).density x = Real.exp (f j s)) ∧
      Tendsto (fun j => phNorm α 2 (f j)) atTop (𝓝 0) := by
  obtain ⟨hL2, hG2⟩ := ordinaryOptimizer_globalLocalization_H1 h hh ρ hpos hmin
  have hgw : ∀ n, IsWeakGradient (ρ n).sqrt (weakGradient (ρ n).sqrt (ρ n).sqrt_mem) :=
    fun n => isWeakGradient_weakGradient (ρ n).sqrt_mem
  choose Wc hWcc hWae _ _ using fun n => circle_H1_holder_half (hgw n)
  -- the two `L²` limits in `eLpNorm` form
  have hm1 : ∀ n, MemLp (fun x => (ρ n).sqrt x - (fun _ : Torus 1 => (1:ℝ)) x) 2 (haar 1) :=
    fun n => (ρ n).memLp_sqrt.sub (memLp_const 1)
  have h1 : Tendsto (fun n => eLpNorm (fun x => (ρ n).sqrt x - (fun _ : Torus 1 => (1:ℝ)) x) 2
      (haar 1)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_toReal (fun n => (hm1 n).eLpNorm_ne_top) ?_
    have : ∀ n, (eLpNorm (fun x => (ρ n).sqrt x - (fun _ : Torus 1 => (1:ℝ)) x) 2
        (haar 1)).toReal = Real.sqrt (∫ x, ((ρ n).sqrt x - 1) ^ 2 ∂haar 1) :=
      fun n => toReal_eLpNorm_two (hm1 n)
    simp only [this]
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hL2
  have hm2 : ∀ n, MemLp (fun x => weakGradient (ρ n).sqrt (ρ n).sqrt_mem x -
      (fun _ : Torus 1 => (0 : Tangent 1)) x) 2 (haar 1) := fun n => by
    simpa using (hgw n).memLp_grad
  have h2 : Tendsto (fun n => eLpNorm (fun x => weakGradient (ρ n).sqrt (ρ n).sqrt_mem x -
      (fun _ : Torus 1 => (0 : Tangent 1)) x) 2 (haar 1)) atTop (𝓝 0) := by
    refine tendsto_eLpNorm_of_toReal (fun n => (hm2 n).eLpNorm_ne_top) ?_
    have : ∀ n, (eLpNorm (fun x => weakGradient (ρ n).sqrt (ρ n).sqrt_mem x -
        (fun _ : Torus 1 => (0 : Tangent 1)) x) 2 (haar 1)).toReal =
        Real.sqrt (∫ x, ‖weakGradient (ρ n).sqrt (ρ n).sqrt_mem x‖ ^ 2 ∂haar 1) := fun n => by
      rw [toReal_eLpNorm_two_vec (hm2 n)]
      simp
    simp only [this]
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hG2
  have hU : TendstoUniformly Wc (fun _ : Torus 1 => (1:ℝ)) atTop :=
    circle_H1_tendstoUniformly (u0 := fun _ => (1:ℝ)) (g0 := fun _ => 0) hgw
      (isWeakGradient_const 1) hWcc hWae continuous_const (Filter.EventuallyEq.refl _ _) h1 h2
  -- sup deviation
  set δ : ℕ → ℝ := fun j => ⨆ x, |Wc j x - 1| with hδdef
  have hbdd : ∀ j, BddAbove (Set.range fun x => |Wc j x - 1|) := fun j =>
    (isCompact_range (((hWcc j).sub continuous_const).abs)).bddAbove
  have hδ : ∀ j x, |Wc j x - 1| ≤ δ j := fun j x => le_ciSup (hbdd j) x
  have hδnn : ∀ j, 0 ≤ δ j := fun j => (abs_nonneg _).trans (hδ j 0)
  have hδt : Tendsto δ atTop (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (hδnn j), fun b hb => ?_⟩
    have := (Metric.tendstoUniformly_iff.1 hU) (b / 2) (by positivity)
    filter_upwards [this] with j hj
    have : δ j ≤ b / 2 := ciSup_le fun x => by
      have := hj x
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le
    linarith
  -- eventual conditions
  have hS : ∀ᶠ j in atTop, 6 * Real.pi * |h j| ≤ 1 := by
    have h1 : Tendsto (fun j => 6 * Real.pi * |h j|) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := 6 * Real.pi)).mul hh.abs
    exact (tendsto_order.1 h1).2 1 one_pos |>.mono fun j hj => hj.le
  have hδh : ∀ᶠ j in atTop, δ j ≤ 1 / 2 :=
    ((tendsto_order.1 hδt).2 (1 / 2) (by norm_num)).mono fun j hj => hj.le
  have hlam : ∀ᶠ j in atTop, (str025_quot (h j) (ρ j)).toReal ≤ 4 * Real.pi ^ 2 + 1 := by
    filter_upwards [str025a_trial hh ρ hpos hmin (ε := 1) one_pos] with j hj
    unfold str025_quot
    rw [toReal_quot]
    have hE : 0 < (ordinaryEntropy (h j) (ρ j)).toReal :=
      ENNReal.toReal_pos (hpos j).ne' (str025_entropy_ne_top _ _)
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hS.and (hδh.and hlam))
  -- the shifted sequences
  have hmain := bs_aux (α := α) hα0 hα1 (fun j => h (j + N))
    (hh.comp (tendsto_add_atTop_nat N)) (fun j => ρ (j + N)) (fun j => hpos _)
    (fun j => hmin _) (fun j => Wc (j + N)) (fun j => hWcc _) (fun j => hWae _)
    (fun j => δ (j + N)) (fun j => (hN _ (by omega)).2.1) (fun j => hδ _)
    (hδt.comp (tendsto_add_atTop_nat N)) (fun j => (hN _ (by omega)).1) (4 * Real.pi ^ 2 + 1)
    (fun j => (hN _ (by omega)).2.2)
  have hev : ∀ ε > 0, ∀ᶠ j in atTop, (∀ t, 0 < Wc j (pt t)) ∧
      IsPH α 2 (fF (fun s => Wc j (pt s))) ∧ phNorm α 2 (fF (fun s => Wc j (pt s))) ≤ ε :=
    fun ε hε => ev_shift N (hmain ε hε)
  refine ⟨fun j => fF (fun s => Wc j (pt s)), ?_, ?_⟩
  · filter_upwards [hev 1 one_pos] with j hj
    obtain ⟨hp, hph, -⟩ := hj
    refine ⟨?_, hph, ?_⟩
    · intro s
      show Real.log (Wc j (pt (s + 1)) ^ 2) = Real.log (Wc j (pt s) ^ 2)
      show Real.log (Wc j (torusLift fun _ => s + 1) ^ 2) = _
      rw [torusLift_one_add]
    · filter_upwards [hWae j] with x hx s hs
      subst hs
      show (ρ j).sqrt (pt s) ^ 2 = Real.exp (Real.log (Wc j (pt s) ^ 2))
      rw [Real.exp_log (pow_pos (hp s) 2), ← hx]
  · rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun j => lt_of_lt_of_le ha (phNorm_nonneg _ _),
      fun b hb => ?_⟩
    filter_upwards [hev (b / 2) (by positivity)] with j hj
    linarith [hj.2.2]

end DGPS.Examples.ThreeSpeciesCircle
