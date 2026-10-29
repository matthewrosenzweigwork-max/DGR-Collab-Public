import DGPS.Examples.RoughBoundary.Feature
import DGPS.Analysis.PeriodicMollificationHolder

/-!
# Quantitative phase composition continuity (SEM005)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 8.1, equations (8.3)-(8.4).

For a circle function `f` (a "profile") and an amplitude `η` put
`θ_f(x) = A_L(2x) - 1/6 + η f(6x)` (`thetaF`), `U_f = e^{2π i θ_f}` (`UfeatF`), and for a second
profile `g2` put `d = η (g2 - f)(6·)` (`phaseDiff`) and `E = U_g2 - U_f` (`Efun`).  Then
`‖E‖_∞ ≤ 2π ‖d‖_∞`, `[E]_α ≤ 2π ([d]_α + ‖d‖_∞ [U_f]_α)`, `‖E‖_p ≤ 2π ‖d‖_p` and
`‖U_g2' - U_f'‖_p ≤ 2π ‖d'‖_p + 2π ‖E‖_∞ ‖θ_f'‖_p`, with `‖d'‖_p = 6 |η| ‖g2' - f'‖_p`.

For `f = g` (the primitive of the spike sum) these are the features of `Feature.lean`
(`thetaF_gT`, `UfeatF_gT`, `UprimeF_gT`).
-/

open MeasureTheory Set
open scoped Real ENNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Spikes (pt)
open DGPS.Examples.RoughBoundary.Feature (Aprim Qdens Zpart Jrot norm_Jrot Q2 measurable_Q2 mp_zsmul
  pt_secT zsmul_pt qdens_pos zpart_pos aprim_add_nat_third abs_aprim_sub_le torusDist_le_half)
open DGPS.Analysis.PeriodicMollification (TorusHolderBdd torusHolderSeminorm torusSupNorm
  torusHolderSeminorm_nonneg torusSupNorm_nonneg torusHolderSeminorm_le continuous_of_holderBdd
  exists_pt_eq torusDist_pt_le)

/-! ### Vector-valued sup norm and Hölder seminorm on the circle -/

/-- `‖F‖_∞ = sup_x ‖F x‖` for a vector-valued circle function. -/
noncomputable def vecSupNorm (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) : ℝ := ⨆ x, ‖F x‖

/-- `[F]_β = sup_{x ≠ y} ‖F x - F y‖ / d(x,y)^β` for a vector-valued circle function
(junk if unbounded). -/
noncomputable def vecHolderSeminorm (β : ℝ) (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ⨆ p : Torus 1 × Torus 1, ‖F p.1 - F p.2‖ / DGPS.torusDist p.1 p.2 ^ β

/-- `F` is `β`-Hölder with some finite constant. -/
def VecHolderBdd (β : ℝ) (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖F x - F y‖ ≤ C * DGPS.torusDist x y ^ β

lemma vecSupNorm_nonneg (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) : 0 ≤ vecSupNorm F :=
  Real.iSup_nonneg fun _ => norm_nonneg _

lemma vecSupNorm_le {F : Torus 1 → EuclideanSpace ℝ (Fin 2)} {M : ℝ} (h : ∀ x, ‖F x‖ ≤ M) :
    vecSupNorm F ≤ M := ciSup_le h

lemma norm_le_vecSupNorm {F : Torus 1 → EuclideanSpace ℝ (Fin 2)} {M : ℝ}
    (h : ∀ x, ‖F x‖ ≤ M) (x : Torus 1) : ‖F x‖ ≤ vecSupNorm F :=
  le_ciSup (f := fun x => ‖F x‖) ⟨M, by rintro _ ⟨y, rfl⟩; exact h y⟩ x

lemma vecHolderSeminorm_nonneg (β : ℝ) (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) :
    0 ≤ vecHolderSeminorm β F :=
  Real.iSup_nonneg fun _ =>
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

lemma vecHolderSeminorm_le {β : ℝ} {F : Torus 1 → EuclideanSpace ℝ (Fin 2)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, ‖F x - F y‖ ≤ C * DGPS.torusDist x y ^ β) : vecHolderSeminorm β F ≤ C := by
  refine ciSup_le fun p => ?_
  by_cases hp : DGPS.torusDist p.1 p.2 = 0
  · by_cases hβ : β = 0
    · subst hβ
      rw [hp, Real.rpow_zero, div_one]
      have := h p.1 p.2
      rwa [hp, Real.rpow_zero, mul_one] at this
    · rw [hp, Real.zero_rpow hβ, div_zero]
      exact hC
  · have hpos : 0 < DGPS.torusDist p.1 p.2 ^ β :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hp)) _
    rw [div_le_iff₀ hpos]
    exact h _ _

lemma VecHolderBdd.norm_sub_le {β : ℝ} {F : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hF : VecHolderBdd β F) (x y : Torus 1) :
    ‖F x - F y‖ ≤ vecHolderSeminorm β F * DGPS.torusDist x y ^ β := by
  obtain ⟨C, hC0, hC⟩ := hF
  by_cases hd : DGPS.torusDist x y = 0
  · have hxy : x = y := DGPS.torusDist_metric.2.2.2.1 x y hd
    subst hxy
    rw [sub_self, norm_zero]
    exact mul_nonneg (vecHolderSeminorm_nonneg _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  · have hpos : 0 < DGPS.torusDist x y ^ β :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hd)) _
    have hbdd : BddAbove (range fun p : Torus 1 × Torus 1 =>
        ‖F p.1 - F p.2‖ / DGPS.torusDist p.1 p.2 ^ β) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨p, rfl⟩
      by_cases hp : DGPS.torusDist p.1 p.2 = 0
      · have hxy : p.1 = p.2 := DGPS.torusDist_metric.2.2.2.1 _ _ hp
        have : ‖F p.1 - F p.2‖ = 0 := by rw [hxy]; simp
        simp only [this, zero_div]; exact hC0
      · have hp' : 0 < DGPS.torusDist p.1 p.2 ^ β :=
          Real.rpow_pos_of_pos (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hp)) _
        rw [div_le_iff₀ hp']
        exact hC _ _
    have := le_ciSup hbdd (x, y)
    simp only at this
    rwa [div_le_iff₀ hpos] at this

/-! ### The generalized phase and feature -/

/-- The phase `θ_f(x) = A_L(2x) - 1/6 + η f(6x)` of a profile `f` on the circle. -/
noncomputable def thetaF (L η : ℝ) (f : Torus 1 → ℝ) (x : ℝ) : ℝ :=
  Aprim L (2 * x) - 1 / 6 + η * f (pt (6 * x))

/-- `U_f(x) = (cos 2πθ_f(x), sin 2πθ_f(x))` on the real line. -/
noncomputable def UrealF (L η : ℝ) (f : Torus 1 → ℝ) (x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (2 * π * thetaF L η f x), Real.sin (2 * π * thetaF L η f x)]

/-- `U_f` as a function on the circle. -/
noncomputable def UfeatF (L η : ℝ) (f : Torus 1 → ℝ) (y : Torus 1) : EuclideanSpace ℝ (Fin 2) :=
  UrealF L η f (SharpLSI.secT y 0)

/-- The a.e. derivative `θ_f'` of the phase, on the circle, from a profile derivative `f'`:
`θ_f'(y) = 2 Q_L(2y) + 6 η f'(6y)`. -/
noncomputable def dthetaTF (L η : ℝ) (f' : Torus 1 → ℝ) (y : Torus 1) : ℝ :=
  2 * Q2 L y + 6 * η * f' ((6 : ℤ) • y)

/-- The a.e. derivative `U_f' = 2π θ_f' J U_f`. -/
noncomputable def UprimeF (L η : ℝ) (f f' : Torus 1 → ℝ) (y : Torus 1) :
    EuclideanSpace ℝ (Fin 2) :=
  (2 * π * dthetaTF L η f' y) • Jrot (UfeatF L η f y)

/-- The phase difference `d(y) = η (g2 - f)(6y)`. -/
noncomputable def phaseDiff (η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) : ℝ :=
  η * (g2 ((6 : ℤ) • y) - f ((6 : ℤ) • y))

/-- The derivative `d'(y) = 6 η (g2' - f')(6y)` of the phase difference. -/
noncomputable def phaseDiffDeriv (η : ℝ) (f' g2' : Torus 1 → ℝ) (y : Torus 1) : ℝ :=
  6 * η * (g2' ((6 : ℤ) • y) - f' ((6 : ℤ) • y))

/-- The feature difference `E = U_g2 - U_f`. -/
noncomputable def Efun (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) : EuclideanSpace ℝ (Fin 2) :=
  UfeatF L η g2 y - UfeatF L η f y

/-! ### Agreement with the features of `Feature.lean` -/

lemma thetaF_gT (L ε : ℝ) :
    thetaF L ε Spikes.gT = Feature.theta L ε := rfl

lemma UfeatF_gT (L ε : ℝ) : UfeatF L ε Spikes.gT = Feature.Ufeat L ε := rfl

lemma UprimeF_gT (L ε : ℝ) :
    UprimeF L ε Spikes.gT (fun y => Spikes.hSum y - Spikes.hMean) = Feature.Uprime L ε := by
  funext y
  unfold UprimeF Feature.Uprime
  rw [Feature.dthetaT_eq']
  rfl

/-! ### Complex coordinates -/

/-- Complex coordinate of a vector of the plane. -/
def toC (v : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨v 0, v 1⟩

lemma norm_toC (v : EuclideanSpace ℝ (Fin 2)) : ‖toC v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  simp [toC, Fin.sum_univ_two, sq, Real.norm_eq_abs, abs_mul_abs_self]

lemma toC_sub (v w : EuclideanSpace ℝ (Fin 2)) : toC (v - w) = toC v - toC w := by
  apply Complex.ext <;> simp [toC]

lemma toC_UrealF (L η : ℝ) (f : Torus 1 → ℝ) (x : ℝ) :
    toC (UrealF L η f x) = Complex.exp (Complex.I * ((2 * π * thetaF L η f x : ℝ) : ℂ)) := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [toC, UrealF, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    simp
  · simp only [toC, UrealF, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    simp

lemma norm_UrealF (L η : ℝ) (f : Torus 1 → ℝ) (x : ℝ) : ‖UrealF L η f x‖ = 1 := by
  rw [← norm_toC, toC_UrealF, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_UfeatF (L η : ℝ) (f : Torus 1 → ℝ) (y : Torus 1) : ‖UfeatF L η f y‖ = 1 :=
  norm_UrealF _ _ _ _

lemma norm_exp_I_sub_exp_I_le (s t : ℝ) :
    ‖Complex.exp (Complex.I * (s : ℂ)) - Complex.exp (Complex.I * (t : ℂ))‖ ≤ |s - t| := by
  have e : Complex.exp (Complex.I * (s : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) * Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t)
  have e2 : Complex.exp (Complex.I * (s : ℂ)) - Complex.exp (Complex.I * (t : ℂ)) =
      Complex.exp (Complex.I * (t : ℂ)) *
        (Complex.exp (Complex.I * ((s - t : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← e, mul_one]
  rw [e2, norm_mul]
  have : ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul]
  simpa using h

lemma norm_UrealF_sub_le (L η : ℝ) (f : Torus 1 → ℝ) (a b : ℝ) :
    ‖UrealF L η f a - UrealF L η f b‖ ≤ 2 * π * |thetaF L η f a - thetaF L η f b| := by
  rw [← norm_toC, toC_sub, toC_UrealF, toC_UrealF]
  refine (norm_exp_I_sub_exp_I_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-! ### Periodicity and the torus representation -/

lemma thetaF_add_one {L : ℝ} (hL : 0 < L) (η : ℝ) (f : Torus 1 → ℝ) (x : ℝ) :
    thetaF L η f (x + 1) = thetaF L η f x + 2 := by
  have e1 : Aprim L (2 * (x + 1)) = Aprim L (2 * x) + 2 := by
    have := aprim_add_nat_third hL (2 * x) 6
    have e : 2 * (x + 1) = 2 * x + ((6 : ℕ) : ℝ) * (1 / 3) := by push_cast; ring
    rw [e, this]; push_cast; ring
  have e2 : f (pt (6 * (x + 1))) = f (pt (6 * x)) := by
    have : 6 * (x + 1) = 6 * x + ((6 : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    have h6 : pt (6 * x + ((6 : ℕ) : ℝ)) = pt (6 * x) := by
      have := Spikes.pt_add_int (6 * x) 6
      simpa using this
    rw [h6]
  unfold thetaF; rw [e1, e2]; ring

lemma UrealF_periodic {L : ℝ} (hL : 0 < L) (η : ℝ) (f : Torus 1 → ℝ) :
    Function.Periodic (UrealF L η f) 1 := by
  intro x
  have h : 2 * π * thetaF L η f (x + 1) = 2 * π * thetaF L η f x + (2 : ℕ) * (2 * π) := by
    rw [thetaF_add_one hL]; push_cast; ring
  unfold UrealF
  rw [h, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

lemma UfeatF_pt {L : ℝ} (hL : 0 < L) (η : ℝ) (f : Torus 1 → ℝ) (t : ℝ) :
    UfeatF L η f (pt t) = UrealF L η f t := by
  unfold UfeatF
  obtain ⟨n, hn⟩ := Spikes.secT_pt_exists t
  have := ((UrealF_periodic hL η f).int_mul n) (SharpLSI.secT (pt t) 0)
  rw [mul_one] at this
  rw [← this, ← hn]

lemma zsmul6_secT (y : Torus 1) : ((6 : ℤ) • y) = pt (6 * SharpLSI.secT y 0) := by
  conv_lhs => rw [← pt_secT y]
  rw [zsmul_pt]; norm_num

/-- The phase of `g2` is the phase of `f` shifted by `d`. -/
lemma thetaF_sub_secT (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) :
    thetaF L η g2 (SharpLSI.secT y 0) - thetaF L η f (SharpLSI.secT y 0) = phaseDiff η f g2 y := by
  unfold thetaF phaseDiff
  rw [zsmul6_secT]; ring

lemma toC_UfeatF_rot (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) :
    toC (UfeatF L η g2 y) =
      toC (UfeatF L η f y) * Complex.exp (Complex.I * ((2 * π * phaseDiff η f g2 y : ℝ) : ℂ)) := by
  unfold UfeatF
  rw [toC_UrealF, toC_UrealF, ← Complex.exp_add]
  congr 1
  rw [← thetaF_sub_secT L η f g2 y]
  push_cast; ring

lemma toC_Efun (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) :
    toC (Efun L η f g2 y) = toC (UfeatF L η f y) *
      (Complex.exp (Complex.I * ((2 * π * phaseDiff η f g2 y : ℝ) : ℂ)) - 1) := by
  unfold Efun
  rw [toC_sub, toC_UfeatF_rot]; ring

/-! ### Pointwise estimates -/

lemma norm_Efun_le (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) :
    ‖Efun L η f g2 y‖ ≤ 2 * π * |phaseDiff η f g2 y| := by
  rw [← norm_toC, toC_Efun, norm_mul, norm_toC, norm_UfeatF, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * phaseDiff η f g2 y)
  refine h.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

lemma norm_Efun_le_two (L η : ℝ) (f g2 : Torus 1 → ℝ) (y : Torus 1) :
    ‖Efun L η f g2 y‖ ≤ 2 := by
  unfold Efun
  calc _ ≤ ‖UfeatF L η g2 y‖ + ‖UfeatF L η f y‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_UfeatF, norm_UfeatF]; norm_num

lemma norm_Efun_sub_le (L η : ℝ) (f g2 : Torus 1 → ℝ) (x y : Torus 1) :
    ‖Efun L η f g2 x - Efun L η f g2 y‖ ≤
      ‖UfeatF L η f x - UfeatF L η f y‖ * (2 * π * |phaseDiff η f g2 x|) +
        2 * π * |phaseDiff η f g2 x - phaseDiff η f g2 y| := by
  set a := 2 * π * phaseDiff η f g2 x with ha
  set b := 2 * π * phaseDiff η f g2 y with hb
  set u := toC (UfeatF L η f x)
  set v := toC (UfeatF L η f y)
  set A := Complex.exp (Complex.I * ((a : ℝ) : ℂ))
  set B := Complex.exp (Complex.I * ((b : ℝ) : ℂ))
  have key : toC (Efun L η f g2 x - Efun L η f g2 y) = (u - v) * (A - 1) + v * (A - B) := by
    rw [toC_sub, toC_Efun, toC_Efun]; ring
  have hv : ‖v‖ = 1 := by rw [norm_toC, norm_UfeatF]
  have h1 : ‖A - 1‖ ≤ |a| := by
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a)
    simpa using this
  have h2 : ‖A - B‖ ≤ |a - b| := norm_exp_I_sub_exp_I_le a b
  have hab : |a| = 2 * π * |phaseDiff η f g2 x| := by
    rw [ha, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hab2 : |a - b| = 2 * π * |phaseDiff η f g2 x - phaseDiff η f g2 y| := by
    rw [ha, hb, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  rw [← norm_toC, key]
  have hu : ‖u - v‖ = ‖UfeatF L η f x - UfeatF L η f y‖ := by rw [← toC_sub, norm_toC]
  calc _ ≤ ‖(u - v) * (A - 1)‖ + ‖v * (A - B)‖ := norm_add_le _ _
    _ = ‖u - v‖ * ‖A - 1‖ + ‖A - B‖ := by rw [norm_mul, norm_mul, hv, one_mul]
    _ ≤ ‖u - v‖ * |a| + |a - b| := by gcongr
    _ = _ := by rw [hu, hab, hab2]

/-! ### Hölder regularity of `U_f` -/

lemma holder_UfeatF {L : ℝ} (hL : 0 < L) (η : ℝ) {α : ℝ} (h0 : 0 < α) (h1 : α < 1)
    {f : Torus 1 → ℝ} (hf : TorusHolderBdd α f) :
    VecHolderBdd α (UfeatF L η f) := by
  obtain ⟨K, hK0, hK⟩ := hf
  set M := Real.exp L / Zpart L with hMdef
  have hM : 0 ≤ M := (div_pos (Real.exp_pos _) (zpart_pos hL)).le
  refine ⟨2 * π * (2 * M + |η| * 6 ^ α * K), by positivity, fun x y => ?_⟩
  obtain ⟨a, b, rfl, rfl, hab⟩ := Spikes.exists_lifts x y
  rw [UfeatF_pt hL, UfeatF_pt hL]
  set δ := DGPS.torusDist (pt a) (pt b) with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ, DGPS.torusDist]; exact Real.sqrt_nonneg _
  have hδ1 : δ ≤ 1 / 2 := torusDist_le_half _ _
  have hba : |a - b| = δ := by rw [abs_sub_comm]; exact hab
  have hδα : δ ≤ δ ^ α := by
    rcases hδ0.eq_or_lt with h | h
    · rw [← h, Real.zero_rpow h0.ne']
    · calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ α := Real.rpow_le_rpow_of_exponent_ge h (by linarith) h1.le
  have hA : |Aprim L (2 * a) - Aprim L (2 * b)| ≤ M * (2 * δ) := by
    refine (abs_aprim_sub_le hL _ _).trans ?_
    have : |2 * a - 2 * b| = 2 * δ := by rw [← hba, ← mul_sub, abs_mul]; norm_num
    rw [this]
  have hG : |f (pt (6 * a)) - f (pt (6 * b))| ≤ K * (6 ^ α * δ ^ α) := by
    refine (hK _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK0
    rw [← Real.mul_rpow (by norm_num) hδ0]
    apply Real.rpow_le_rpow (Real.sqrt_nonneg _) _ h0.le
    refine (torusDist_pt_le _ _).trans ?_
    rw [← mul_sub, abs_mul, hba]; norm_num
  have hθ : |thetaF L η f a - thetaF L η f b| ≤ (2 * M + |η| * 6 ^ α * K) * δ ^ α := by
    have e : thetaF L η f a - thetaF L η f b =
        (Aprim L (2 * a) - Aprim L (2 * b)) + η * (f (pt (6 * a)) - f (pt (6 * b))) := by
      unfold thetaF; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have h6 : 0 ≤ (6 : ℝ) ^ α := by positivity
    calc _ ≤ M * (2 * δ) + |η| * (K * (6 ^ α * δ ^ α)) :=
          add_le_add hA (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ ≤ M * (2 * δ ^ α) + |η| * (K * (6 ^ α * δ ^ α)) := by gcongr
      _ = _ := by ring
  calc ‖UrealF L η f a - UrealF L η f b‖ ≤ 2 * π * |thetaF L η f a - thetaF L η f b| :=
        norm_UrealF_sub_le _ _ _ _ _
    _ ≤ 2 * π * ((2 * M + |η| * 6 ^ α * K) * δ ^ α) :=
        mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = _ := by ring

/-! ### The degree-six covering -/

lemma surjective_zsmul6 : Function.Surjective (fun y : Torus 1 => (6 : ℤ) • y) := by
  intro y
  obtain ⟨t, rfl⟩ := exists_pt_eq y
  refine ⟨pt (t / 6), ?_⟩
  show (6 : ℤ) • pt (t / 6) = pt t
  rw [zsmul_pt]; congr 1; push_cast; ring

lemma torusDist_zsmul6_le (x y : Torus 1) :
    DGPS.torusDist ((6 : ℤ) • x) ((6 : ℤ) • y) ≤ 6 * DGPS.torusDist x y := by
  obtain ⟨a, b, rfl, rfl, hab⟩ := Spikes.exists_lifts x y
  rw [zsmul_pt, zsmul_pt, ← hab]
  refine (torusDist_pt_le _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_sub_comm]; norm_num

lemma continuous_zsmul6 : Continuous (fun y : Torus 1 => (6 : ℤ) • y) :=
  continuous_const_smul _

lemma abs_le_torusSupNorm {g : Torus 1 → ℝ} {M : ℝ} (h : ∀ x, |g x| ≤ M) (x : Torus 1) :
    |g x| ≤ torusSupNorm g :=
  le_ciSup (f := fun x => |g x|) ⟨M, by rintro _ ⟨y, rfl⟩; exact h y⟩ x

lemma exists_bound_of_continuous {g : Torus 1 → ℝ} (hg : Continuous g) : ∃ M, ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨M, fun x => by simpa using hM x (mem_univ x)⟩

lemma torusHolderBdd_sub {α : ℝ} {f g : Torus 1 → ℝ} (hf : TorusHolderBdd α f)
    (hg : TorusHolderBdd α g) : TorusHolderBdd α (fun y => g y - f y) := by
  obtain ⟨C, hC0, hC⟩ := hf
  obtain ⟨D, hD0, hD⟩ := hg
  refine ⟨D + C, add_nonneg hD0 hC0, fun x y => ?_⟩
  have : g x - f x - (g y - f y) = (g x - g y) - (f x - f y) := by ring
  rw [this, add_mul]
  exact (abs_sub _ _).trans (add_le_add (hD x y) (hC x y))

lemma continuous_phaseDiff {η : ℝ} {f g2 : Torus 1 → ℝ} (hf : Continuous f) (hg2 : Continuous g2) :
    Continuous (phaseDiff η f g2) := by
  unfold phaseDiff
  exact continuous_const.mul ((hg2.comp continuous_zsmul6).sub (hf.comp continuous_zsmul6))

lemma torusSupNorm_phaseDiff (η : ℝ) (f g2 : Torus 1 → ℝ) :
    torusSupNorm (phaseDiff η f g2) = |η| * torusSupNorm (fun y => g2 y - f y) := by
  unfold torusSupNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg _)]
  have : (fun y => |phaseDiff η f g2 y|) =
      (fun x : Torus 1 => |η| * |g2 x - f x|) ∘ (fun y : Torus 1 => (6 : ℤ) • y) := by
    funext y; simp [phaseDiff, abs_mul]
  rw [this]
  exact surjective_zsmul6.iSup_comp (fun x => |η| * |g2 x - f x|)

lemma torusHolderSeminorm_phaseDiff_le {α : ℝ} (hα : 0 < α) (η : ℝ) {f g2 : Torus 1 → ℝ}
    (hf : TorusHolderBdd α f) (hg2 : TorusHolderBdd α g2) :
    torusHolderSeminorm α (phaseDiff η f g2) ≤
      |η| * 6 ^ α * torusHolderSeminorm α (fun y => g2 y - f y) := by
  have hh := torusHolderBdd_sub hf hg2
  refine torusHolderSeminorm_le (by have := hh.seminorm_nonneg; positivity) fun x y => ?_
  have h1 := hh.abs_sub_le ((6 : ℤ) • x) ((6 : ℤ) • y)
  have h2 : DGPS.torusDist ((6 : ℤ) • x) ((6 : ℤ) • y) ^ α ≤ (6 * DGPS.torusDist x y) ^ α :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (torusDist_zsmul6_le x y) hα.le
  rw [Real.mul_rpow (x := 6) (y := DGPS.torusDist x y) (by norm_num) (Real.sqrt_nonneg _)] at h2
  have e : phaseDiff η f g2 x - phaseDiff η f g2 y =
      η * ((g2 ((6 : ℤ) • x) - f ((6 : ℤ) • x)) - (g2 ((6 : ℤ) • y) - f ((6 : ℤ) • y))) := by
    unfold phaseDiff; ring
  rw [e, abs_mul]
  have hs := hh.seminorm_nonneg
  calc |η| * |(g2 ((6 : ℤ) • x) - f ((6 : ℤ) • x)) - (g2 ((6 : ℤ) • y) - f ((6 : ℤ) • y))|
      ≤ |η| * (torusHolderSeminorm α (fun y => g2 y - f y) *
          DGPS.torusDist ((6 : ℤ) • x) ((6 : ℤ) • y) ^ α) := by gcongr
    _ ≤ |η| * (torusHolderSeminorm α (fun y => g2 y - f y) *
          (6 ^ α * DGPS.torusDist x y ^ α)) := by gcongr
    _ = _ := by ring

/-! ### The Lp estimates -/

lemma aestronglyMeasurable_comp_zsmul6 {g : Torus 1 → ℝ}
    (hg : AEStronglyMeasurable g (DGPS.haar 1)) :
    AEStronglyMeasurable (fun y => g ((6 : ℤ) • y)) (DGPS.haar 1) :=
  hg.comp_quasiMeasurePreserving (mp_zsmul 6 (by norm_num)).quasiMeasurePreserving

lemma eLpNorm_comp_zsmul6 (p : ℝ≥0∞) {g : Torus 1 → ℝ}
    (hg : AEStronglyMeasurable g (DGPS.haar 1)) :
    eLpNorm (fun y => g ((6 : ℤ) • y)) p (DGPS.haar 1) = eLpNorm g p (DGPS.haar 1) :=
  eLpNorm_comp_measurePreserving hg (mp_zsmul 6 (by norm_num))

lemma eLpNorm_phaseDiff (p : ℝ≥0∞) (η : ℝ) {f g2 : Torus 1 → ℝ}
    (h : AEStronglyMeasurable (fun y => g2 y - f y) (DGPS.haar 1)) :
    eLpNorm (phaseDiff η f g2) p (DGPS.haar 1) =
      ENNReal.ofReal |η| * eLpNorm (fun y => g2 y - f y) p (DGPS.haar 1) := by
  have : phaseDiff η f g2 = η • (fun y => (fun x => g2 x - f x) ((6 : ℤ) • y)) := by
    funext y; simp [phaseDiff]
  rw [this, eLpNorm_const_smul, eLpNorm_comp_zsmul6 p h, Real.enorm_eq_ofReal_abs]

lemma eLpNorm_phaseDiffDeriv (p : ℝ≥0∞) (η : ℝ) {f' g2' : Torus 1 → ℝ}
    (h : AEStronglyMeasurable (fun y => g2' y - f' y) (DGPS.haar 1)) :
    eLpNorm (phaseDiffDeriv η f' g2') p (DGPS.haar 1) =
      ENNReal.ofReal (6 * |η|) * eLpNorm (fun y => g2' y - f' y) p (DGPS.haar 1) := by
  have : phaseDiffDeriv η f' g2' = (6 * η) • (fun y => (fun x => g2' x - f' x) ((6 : ℤ) • y)) := by
    funext y; simp [phaseDiffDeriv]
  rw [this, eLpNorm_const_smul, eLpNorm_comp_zsmul6 p h, Real.enorm_eq_ofReal_abs, abs_mul]
  norm_num

lemma norm_Uprime_sub_le (L η : ℝ) (f g2 f' g2' : Torus 1 → ℝ) (y : Torus 1) :
    ‖UprimeF L η g2 g2' y - UprimeF L η f f' y‖ ≤
      2 * π * |phaseDiffDeriv η f' g2' y| +
        2 * π * ‖Efun L η f g2 y‖ * |dthetaTF L η f' y| := by
  have hJ : ∀ v w : EuclideanSpace ℝ (Fin 2), Jrot (v - w) = Jrot v - Jrot w := by
    intro v w; ext i; fin_cases i
    · simp [Jrot]; ring
    · simp [Jrot]
  have hdt : dthetaTF L η g2' y = dthetaTF L η f' y + phaseDiffDeriv η f' g2' y := by
    unfold dthetaTF phaseDiffDeriv; ring
  have e : UprimeF L η g2 g2' y - UprimeF L η f f' y =
      (2 * π * phaseDiffDeriv η f' g2' y) • Jrot (UfeatF L η g2 y) +
        (2 * π * dthetaTF L η f' y) • Jrot (Efun L η f g2 y) := by
    unfold UprimeF Efun
    rw [hJ, hdt, smul_sub, mul_add, add_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_Jrot, norm_Jrot, norm_UfeatF, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_mul (2 * π) (phaseDiffDeriv η f' g2' y), abs_mul (2 * π) (dthetaTF L η f' y),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  exact le_of_eq (by ring)

lemma aestronglyMeasurable_dthetaTF (L η : ℝ) {f' : Torus 1 → ℝ}
    (h : AEStronglyMeasurable f' (DGPS.haar 1)) :
    AEStronglyMeasurable (dthetaTF L η f') (DGPS.haar 1) := by
  have h1 : AEStronglyMeasurable (fun y => 2 * Q2 L y) (DGPS.haar 1) :=
    ((measurable_Q2 L).const_mul 2).aestronglyMeasurable
  have h2 := (aestronglyMeasurable_comp_zsmul6 h).const_mul (6 * η)
  exact h1.add h2

lemma continuous_Jrot : Continuous Jrot := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simp <;> fun_prop

lemma aestronglyMeasurable_UfeatF (L η : ℝ) {f : Torus 1 → ℝ}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) :
    AEStronglyMeasurable (UfeatF L η f) (DGPS.haar 1) := by
  have hcA : Continuous fun s : ℝ => Aprim L (2 * s) :=
    continuous_iff_continuousAt.2 fun s =>
      ((Feature.hasDerivAt_aprim L (2 * s)).continuousAt).comp (by fun_prop : Continuous fun s : ℝ => 2 * s).continuousAt
  have hA : AEStronglyMeasurable (fun y : Torus 1 => Aprim L (2 * SharpLSI.secT y 0))
      (DGPS.haar 1) :=
    (Spikes.measurable_comp_secT hcA).aestronglyMeasurable
  have hB := aestronglyMeasurable_comp_zsmul6 hf
  have hg : Continuous (fun p : ℝ × ℝ =>
      (!₂[Real.cos (2 * π * (p.1 - 1 / 6 + η * p.2)), Real.sin (2 * π * (p.1 - 1 / 6 + η * p.2))] :
        EuclideanSpace ℝ (Fin 2))) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  have hg' : Continuous (Function.uncurry fun a b : ℝ =>
      (!₂[Real.cos (2 * π * (a - 1 / 6 + η * b)), Real.sin (2 * π * (a - 1 / 6 + η * b))] :
        EuclideanSpace ℝ (Fin 2))) := hg
  have := hg'.comp_aestronglyMeasurable₂ (f := fun y : Torus 1 => Aprim L (2 * SharpLSI.secT y 0))
    (f' := fun y : Torus 1 => f ((6 : ℤ) • y)) hA hB
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [UfeatF, UrealF, thetaF, zsmul6_secT]

lemma aestronglyMeasurable_Efun (L η : ℝ) {f g2 : Torus 1 → ℝ}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) (hg2 : AEStronglyMeasurable g2 (DGPS.haar 1)) :
    AEStronglyMeasurable (Efun L η f g2) (DGPS.haar 1) :=
  (aestronglyMeasurable_UfeatF L η hg2).sub (aestronglyMeasurable_UfeatF L η hf)

lemma aestronglyMeasurable_UprimeF (L η : ℝ) {f f' : Torus 1 → ℝ}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) (hf' : AEStronglyMeasurable f' (DGPS.haar 1)) :
    AEStronglyMeasurable (UprimeF L η f f') (DGPS.haar 1) :=
  ((aestronglyMeasurable_dthetaTF L η hf').const_mul (2 * π)).smul
    (continuous_Jrot.comp_aestronglyMeasurable (aestronglyMeasurable_UfeatF L η hf))

/-! ### SEM005 -/

/-- **SEM005 (quantitative phase composition continuity).**  Fix `L > 0`, an amplitude `η`, and two
circle profiles `f`, `g2`.  Put `d = η (g2 - f)(6·)` (`phaseDiff`), `E = U_g2 - U_f` (`Efun`).

(a) For continuous profiles: `‖E‖_∞ ≤ 2π ‖d‖_∞` and `‖d‖_∞ = |η| ‖g2 - f‖_∞`.
(b) For `α`-Hölder profiles (`0 < α < 1`): `[E]_α ≤ 2π ([d]_α + ‖d‖_∞ [U_f]_α)` and
    `[d]_α ≤ |η| 6^α [g2 - f]_α`.
(c) For every exponent `p`: `‖E‖_p ≤ 2π ‖d‖_p`; for measurable `g2 - f`: `‖d‖_p = |η| ‖g2 - f‖_p`.
(d) For `1 ≤ p` and measurable profile derivatives `f'`, `g2'`:
    `‖U_g2' - U_f'‖_p ≤ 2π ‖d'‖_p + 2π ‖E‖_∞ ‖θ_f'‖_p` and, for measurable `g2' - f'`,
    `‖d'‖_p = 6 |η| ‖g2' - f'‖_p` where `d' = 6 η (g2' - f')(6·)`. -/
theorem quantitative_phase_composition_continuity {L : ℝ} (hL : 0 < L) (η : ℝ) :
    (∀ f g2 : Torus 1 → ℝ, Continuous f → Continuous g2 →
      vecSupNorm (Efun L η f g2) ≤ 2 * π * torusSupNorm (phaseDiff η f g2) ∧
      torusSupNorm (phaseDiff η f g2) = |η| * torusSupNorm (fun y => g2 y - f y)) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∀ f g2 : Torus 1 → ℝ, TorusHolderBdd α f → TorusHolderBdd α g2 →
      vecHolderSeminorm α (Efun L η f g2) ≤
        2 * π * (torusHolderSeminorm α (phaseDiff η f g2) +
          torusSupNorm (phaseDiff η f g2) * vecHolderSeminorm α (UfeatF L η f)) ∧
      torusHolderSeminorm α (phaseDiff η f g2) ≤
        |η| * 6 ^ α * torusHolderSeminorm α (fun y => g2 y - f y)) ∧
    (∀ (p : ℝ≥0∞) (f g2 : Torus 1 → ℝ),
      (AEStronglyMeasurable f (DGPS.haar 1) → AEStronglyMeasurable g2 (DGPS.haar 1) →
        eLpNorm (Efun L η f g2) p (DGPS.haar 1) ≤
          ENNReal.ofReal (2 * π) * eLpNorm (phaseDiff η f g2) p (DGPS.haar 1)) ∧
      (AEStronglyMeasurable (fun y => g2 y - f y) (DGPS.haar 1) →
        eLpNorm (phaseDiff η f g2) p (DGPS.haar 1) =
          ENNReal.ofReal |η| * eLpNorm (fun y => g2 y - f y) p (DGPS.haar 1))) ∧
    (∀ (p : ℝ≥0∞), 1 ≤ p → ∀ f f' g2 g2' : Torus 1 → ℝ,
      (AEStronglyMeasurable f (DGPS.haar 1) → AEStronglyMeasurable g2 (DGPS.haar 1) →
        AEStronglyMeasurable f' (DGPS.haar 1) → AEStronglyMeasurable g2' (DGPS.haar 1) →
        eLpNorm (fun y => UprimeF L η g2 g2' y - UprimeF L η f f' y) p (DGPS.haar 1) ≤
          ENNReal.ofReal (2 * π) * eLpNorm (phaseDiffDeriv η f' g2') p (DGPS.haar 1) +
            ENNReal.ofReal (2 * π * vecSupNorm (Efun L η f g2)) *
              eLpNorm (dthetaTF L η f') p (DGPS.haar 1)) ∧
      (AEStronglyMeasurable (fun y => g2' y - f' y) (DGPS.haar 1) →
        eLpNorm (phaseDiffDeriv η f' g2') p (DGPS.haar 1) =
          ENNReal.ofReal (6 * |η|) * eLpNorm (fun y => g2' y - f' y) p (DGPS.haar 1))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g2 hf hg2
    have hb : ∃ M, ∀ y, |phaseDiff η f g2 y| ≤ M :=
      exists_bound_of_continuous (continuous_phaseDiff hf hg2)
    refine ⟨vecSupNorm_le fun y => ?_, torusSupNorm_phaseDiff η f g2⟩
    obtain ⟨M, hM⟩ := hb
    exact (norm_Efun_le L η f g2 y).trans
      (mul_le_mul_of_nonneg_left (abs_le_torusSupNorm hM y) (by positivity))
  · intro α hα0 hα1 f g2 hf hg2
    refine ⟨?_, torusHolderSeminorm_phaseDiff_le hα0 η hf hg2⟩
    have hcf := continuous_of_holderBdd hα0 hf
    have hcg2 := continuous_of_holderBdd hα0 hg2
    obtain ⟨M, hM⟩ := exists_bound_of_continuous (continuous_phaseDiff (η := η) hcf hcg2)
    have hU := holder_UfeatF hL η hα0 hα1 hf
    have hd : TorusHolderBdd α (phaseDiff η f g2) := by
      have hh := torusHolderBdd_sub hf hg2
      obtain ⟨C, hC0, hC⟩ := hh
      refine ⟨|η| * (6 ^ α * C), by positivity, fun x y => ?_⟩
      have h2 : DGPS.torusDist ((6 : ℤ) • x) ((6 : ℤ) • y) ^ α ≤
          (6 * DGPS.torusDist x y) ^ α :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) (torusDist_zsmul6_le x y) hα0.le
      rw [Real.mul_rpow (x := 6) (y := DGPS.torusDist x y) (by norm_num) (Real.sqrt_nonneg _)] at h2
      have e : phaseDiff η f g2 x - phaseDiff η f g2 y =
          η * ((g2 ((6 : ℤ) • x) - f ((6 : ℤ) • x)) - (g2 ((6 : ℤ) • y) - f ((6 : ℤ) • y))) := by
        unfold phaseDiff; ring
      rw [e, abs_mul]
      calc |η| * |(g2 ((6 : ℤ) • x) - f ((6 : ℤ) • x)) - (g2 ((6 : ℤ) • y) - f ((6 : ℤ) • y))|
          ≤ |η| * (C * DGPS.torusDist ((6 : ℤ) • x) ((6 : ℤ) • y) ^ α) := by
            gcongr; exact hC _ _
        _ ≤ |η| * (C * (6 ^ α * DGPS.torusDist x y ^ α)) := by gcongr
        _ = _ := by ring
    refine vecHolderSeminorm_le (by
      have := torusHolderSeminorm_nonneg α (phaseDiff η f g2)
      have := torusSupNorm_nonneg (phaseDiff η f g2)
      have := vecHolderSeminorm_nonneg α (UfeatF L η f)
      positivity) fun x y => ?_
    have hE := norm_Efun_sub_le L η f g2 x y
    have h1 := hU.norm_sub_le x y
    have h2 := hd.abs_sub_le x y
    have h3 := abs_le_torusSupNorm hM x
    have hdist : 0 ≤ DGPS.torusDist x y ^ α := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hS := vecHolderSeminorm_nonneg α (UfeatF L η f)
    calc _ ≤ _ := hE
      _ ≤ (vecHolderSeminorm α (UfeatF L η f) * DGPS.torusDist x y ^ α) *
            (2 * π * torusSupNorm (phaseDiff η f g2)) +
          2 * π * (torusHolderSeminorm α (phaseDiff η f g2) * DGPS.torusDist x y ^ α) := by
          gcongr
      _ = _ := by ring
  · intro p f g2
    refine ⟨fun hf hg2 => ?_, fun h => eLpNorm_phaseDiff p η h⟩
    calc eLpNorm (Efun L η f g2) p (DGPS.haar 1)
        ≤ eLpNorm (fun y => (2 * π) * phaseDiff η f g2 y) p (DGPS.haar 1) := by
          refine eLpNorm_mono (aestronglyMeasurable_Efun L η hf hg2) fun y => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          exact norm_Efun_le L η f g2 y
      _ = _ := by
          have : (fun y => (2 * π) * phaseDiff η f g2 y) = (2 * π) • phaseDiff η f g2 := rfl
          rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  · intro p hp f f' g2 g2'
    refine ⟨fun hf hg2 hf' hg2' => ?_, fun hmeas => eLpNorm_phaseDiffDeriv p η hmeas⟩
    have hmeas : AEStronglyMeasurable (fun y => g2' y - f' y) (DGPS.haar 1) := hg2'.sub hf'
    set S := vecSupNorm (Efun L η f g2) with hS
    have hd' : AEStronglyMeasurable (phaseDiffDeriv η f' g2') (DGPS.haar 1) := by
      have : phaseDiffDeriv η f' g2' = fun y => (6 * η) * ((fun x => g2' x - f' x) ((6 : ℤ) • y)) := by
        funext y; simp [phaseDiffDeriv]
      rw [this]
      exact (aestronglyMeasurable_comp_zsmul6 hmeas).const_mul _
    have hθ := aestronglyMeasurable_dthetaTF L η hf'
    have hE : ∀ y, ‖Efun L η f g2 y‖ ≤ S := fun y =>
      norm_le_vecSupNorm (fun y => norm_Efun_le_two L η f g2 y) y
    have hS0 : 0 ≤ S := vecSupNorm_nonneg _
    calc eLpNorm (fun y => UprimeF L η g2 g2' y - UprimeF L η f f' y) p (DGPS.haar 1)
        ≤ eLpNorm ((fun y => (2 * π) * ‖phaseDiffDeriv η f' g2' y‖) +
            (fun y => (2 * π * S) * ‖dthetaTF L η f' y‖)) p (DGPS.haar 1) := by
          refine eLpNorm_mono ((aestronglyMeasurable_UprimeF L η hg2 hg2').sub
            (aestronglyMeasurable_UprimeF L η hf hf')) fun y => ?_
          have h := norm_Uprime_sub_le L η f g2 f' g2' y
          have hm : 2 * π * ‖Efun L η f g2 y‖ * |dthetaTF L η f' y| ≤
              2 * π * S * |dthetaTF L η f' y| := by
            gcongr; exact hE y
          rw [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          simp only [Real.norm_eq_abs]
          linarith
      _ ≤ eLpNorm (fun y => (2 * π) * ‖phaseDiffDeriv η f' g2' y‖) p (DGPS.haar 1) +
            eLpNorm (fun y => (2 * π * S) * ‖dthetaTF L η f' y‖) p (DGPS.haar 1) :=
          eLpNorm_add_le hp
      _ = _ := by
          have e1 : (fun y => (2 * π) * ‖phaseDiffDeriv η f' g2' y‖) =
              (2 * π) • (fun y => ‖phaseDiffDeriv η f' g2' y‖) := rfl
          have e2 : (fun y => (2 * π * S) * ‖dthetaTF L η f' y‖) =
              (2 * π * S) • (fun y => ‖dthetaTF L η f' y‖) := rfl
          rw [e1, e2, eLpNorm_const_smul, eLpNorm_const_smul, eLpNorm_norm _ hd', eLpNorm_norm _ hθ,
            Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
            abs_of_nonneg (by positivity : 0 ≤ 2 * π * S)]

end DGPS.Examples.RoughBoundary.Semicontinuity
