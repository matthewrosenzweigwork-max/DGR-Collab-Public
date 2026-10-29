import DGPS.Lipschitz.MeanFieldFixedPoint
import DGPS.Basic.ParabolicChainRuleFinal
import DGPS.Basic.SquareRootHeatRecovery
import DGPS.Lipschitz.DuhamelSemigroup

/-!
# Regularity, energy inequality and mass of the local mean-field flow (LIP027, partial)

Sorry-free partial result for `flow_energy_regularity_positivity_and_mass`: for a mild flow
`MildFlow` (the output of `modified_mean_field_mild_contraction`) we prove the projected
energy inequality for every cutoff, the uniform `H¹` bound, the Fourier-side `H⁻¹` time-derivative
statement, and conservation of the mean.  Positivity and `P ρ = ρ` are NOT proved here.
-/

open MeasureTheory Set
open scoped Real RealInnerProductSpace ComplexConjugate

namespace DGPS.Lipschitz
variable {d : ℕ} {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g b : ℝ}

theorem norm_mFourier_neg_le (k : Fin d → ℤ) (x : Torus d) :
    ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
  have := ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)) x
  rwa [UnitAddTorus.mFourier_norm] at this

theorem integrable_mFourier_mul {f : Torus d → ℝ} (hf : Integrable f (haar d)) (k : Fin d → ℤ) :
    Integrable (fun x => UnitAddTorus.mFourier (-k) x * (f x : ℂ)) (haar d) := by
  have hem : Measurable (fun x : Torus d => UnitAddTorus.mFourier (-k) x) :=
    (UnitAddTorus.mFourier (-k) : C(UnitAddTorus (Fin d), ℂ)).continuous.measurable
  have := hf.ofReal.bdd_mul (c := 1) hem.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_mFourier_neg_le k x)
  exact this

theorem fourierCoeff_add_L2 (f g : L2s d) (k : Fin d → ℤ) :
    fourierCoeff (fun x => ((f + g : L2s d) : Torus d → ℝ) x) k =
      fourierCoeff (fun x => (f : Torus d → ℝ) x) k + fourierCoeff (fun x => (g : Torus d → ℝ) x) k := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq]
  rw [← integral_add (integrable_mFourier_mul ((Lp.memLp f).integrable one_le_two) k)
    (integrable_mFourier_mul ((Lp.memLp g).integrable one_le_two) k)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with x hx
  simp only [hx, Pi.add_apply]
  push_cast; ring

theorem fourierCoeff_smul_L2 (c : ℝ) (f : L2s d) (k : Fin d → ℤ) :
    fourierCoeff (fun x => ((c • f : L2s d) : Torus d → ℝ) x) k =
      (c : ℂ) * fourierCoeff (fun x => (f : Torus d → ℝ) x) k := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

/-- The `k`-th Fourier coefficient as a continuous real-linear functional on `L²`. -/
noncomputable def cfL (k : Fin d → ℤ) : L2s d →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => fourierCoeff (fun x => (f : Torus d → ℝ) x) k
      map_add' := fun f g => fourierCoeff_add_L2 f g k
      map_smul' := fun c f => by simpa using fourierCoeff_smul_L2 c f k } 1
    (fun f => by
      have h : ‖fourierCoeff (fun x => (f : Torus d → ℝ) x) k‖ ^ 2 ≤ ∫ x, (f : Torus d → ℝ) x ^ 2 ∂haar d :=
        le_hasSum (hasSum_sq_fourierCoeff (Lp.memLp f)) k fun _ _ => by positivity
      have h2 : ‖fourierCoeff (fun x => (f : Torus d → ℝ) x) k‖ ^ 2 ≤ ‖f‖ ^ 2 := by
        rw [norm_Lp_two_sq]
        simpa [Real.norm_eq_abs, sq_abs] using h
      simpa using abs_le_of_sq_le_sq' (by simpa using h2) (norm_nonneg _) |>.2)

theorem cfL_apply (k : Fin d → ℤ) (f : L2s d) :
    cfL k f = fourierCoeff (fun x => (f : Torus d → ℝ) x) k := rfl


theorem fourierCoeff_congr_ae {f g : Torus d → ℝ} (h : f =ᵐ[haar d] g) (k : Fin d → ℤ) :
    fourierCoeff f k = fourierCoeff g k := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

theorem fourierCoeff_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) (haar d)) (k : Fin d → ℤ) :
    fourierCoeff (fun y => ∑ i ∈ s, f i y) k = ∑ i ∈ s, fourierCoeff (f i) k := by
  unfold fourierCoeff
  simp_rw [mFourierCoeff_ofReal_eq]
  rw [← integral_finsetSum _ (fun i hi => integrable_mFourier_mul (hf i hi) k)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_sum, Finset.mul_sum]

/-- The coordinate projection `L²(𝕋^d; ℝ^d) → L²(𝕋^d)`. -/
noncomputable def coordL (j : Fin d) : L2v d →L[ℝ] L2s d :=
  (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).compLpL 2 (haar d)

theorem coeFn_coordL (j : Fin d) (F : L2v d) :
    (fun x => (coordL j F : Torus d → ℝ) x) =ᵐ[haar d] fun x => (F : Torus d → Tangent d) x j :=
  ContinuousLinearMap.coeFn_compLpL _ _

/-- Fourier coefficient of the divergence heat-flow data: `∑ⱼ 2πi kⱼ F̂ⱼ(k)`. -/
noncomputable def divCoef (k : Fin d → ℤ) : L2v d →L[ℝ] ℂ :=
  ∑ j, ((2 * π * Complex.I * (k j : ℂ)) • (cfL k).comp (coordL j))

theorem divCoef_apply (k : Fin d → ℤ) (F : L2v d) :
    divCoef k F = ∑ j, 2 * π * Complex.I * (k j : ℂ) *
      fourierCoeff (fun x => (F : Torus d → Tangent d) x j) k := by
  unfold divCoef
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, cfL_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fourierCoeff_congr_ae (coeFn_coordL j F) k]

theorem cfL_divHeat {τ : ℝ} (hτ : 0 < τ) (F : L2v d) (k : Fin d → ℤ) :
    cfL k (divHeat τ F) = (Real.exp (-(gradWeight k * τ)) : ℂ) * divCoef k F := by
  rw [cfL_apply, fourierCoeff_congr_ae (coeFn_divHeat hτ F) k, divCoef_apply]
  have hFj : ∀ j : Fin d, Integrable (fun w => (F : Torus d → Tangent d) w j) (haar d) :=
    fun j => integrable_coord ((Lp.memLp F).integrable one_le_two) j
  unfold divHeatFun
  have hsm : ∀ j : Fin d, IsSmoothPeriodic (heatOp τ fun w => (F : Torus d → Tangent d) w j) :=
    fun j => isSmoothPeriodic_heatOp hτ (hFj j)
  rw [fourierCoeff_finset_sum _ (fun j _ => integrable_of_continuous_torus
    ((hsm j).continuous_coordPartial j)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e1 : fourierCoeff (coordPartial j (heatOp τ fun w => (F : Torus d → Tangent d) w j)) k =
      2 * π * Complex.I * (k j : ℂ) * fourierCoeff (heatOp τ fun w => (F : Torus d → Tangent d) w j) k :=
    mFourierCoeff_of_ibp (integrable_of_continuous_torus (hsm j).continuous_torus)
      (integrable_of_continuous_torus ((hsm j).continuous_coordPartial j)) j
      (fun φ hφ => integral_mul_coordPartial_of_smooth (hsm j) hφ j) k
  rw [e1, fourierCoeff_heatOp hτ (hFj j)]
  ring

/-- The clamped extension of a path on `[0,T]` to all of `ℝ`. -/
noncomputable def uX (T : ℝ) (u : ℝ → L2s d) (s : ℝ) : L2s d := u (DGPS.Lipschitz.ParabolicChainRule.lip026b_clamp T s)

/-- The local mild flow data (output of the local fixed point). -/
structure MildFlow (h : MeanFieldData G B g b) (ρ0 : L2s d) (T M : ℝ) (u : ℝ → L2s d) : Prop where
  hT : 0 ≤ T
  hM : 0 ≤ M
  cont : ContinuousOn u (Icc 0 T)
  bound : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * M
  mild : ∀ t ∈ Icc (0 : ℝ) T,
    u t = heatL2 ρ0 t + duhamel (divHeatFam d) (fun s => Nvec h (u s)) t

section MildFlowLemmas
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.uX_of_mem (_ : MildFlow h ρ0 T M u) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : uX T u s = u s := by
  unfold uX; rw [DGPS.Lipschitz.ParabolicChainRule.lip026b_clamp_of_mem hs]

theorem MildFlow.continuous_uX (S : MildFlow h ρ0 T M u) : Continuous (uX T u) :=
  S.cont.comp_continuous (DGPS.Lipschitz.ParabolicChainRule.lip026b_continuous_clamp T) (fun s => DGPS.Lipschitz.ParabolicChainRule.lip026b_clamp_mem S.hT s)

theorem MildFlow.uX_mem_aeBall (S : MildFlow h ρ0 T M u) (s : ℝ) : uX T u s ∈ aeBall d (2 * M) :=
  S.bound _ (DGPS.Lipschitz.ParabolicChainRule.lip026b_clamp_mem S.hT s)

theorem MildFlow.norm_uX_le (S : MildFlow h ρ0 T M u) (s : ℝ) : ‖uX T u s‖ ≤ 2 * M :=
  norm_le_of_aeBall (S.uX_mem_aeBall s)

theorem MildFlow.continuous_NvecX (S : MildFlow h ρ0 T M u) : Continuous (fun s => Nvec h (uX T u s)) :=
  (continuousOn_Nvec h (by linarith [S.hM] : (0 : ℝ) ≤ 2 * M)).comp_continuous S.continuous_uX
    S.uX_mem_aeBall

theorem MildFlow.norm_NvecX_le (S : MildFlow h ρ0 T M u) (s : ℝ) :
    ‖Nvec h (uX T u s)‖ ≤ (g + b) * (2 * M) :=
  (norm_Nvec_le h _).trans (mul_le_mul_of_nonneg_left (S.norm_uX_le s)
    (add_nonneg h.g_nonneg h.b_nonneg))

theorem MildFlow.u_zero (S : MildFlow h ρ0 T M u) : u 0 = ρ0 := by
  rw [S.mild 0 ⟨le_rfl, S.hT⟩]
  simp [duhamel, heatL2_zero]

theorem MildFlow.duhamel_eq_uX (S : MildFlow h ρ0 T M u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    duhamel (divHeatFam d) (fun s => Nvec h (u s)) t =
      duhamel (divHeatFam d) (fun s => Nvec h (uX T u s)) t := by
  unfold duhamel
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [Set.uIcc_of_le ht.1] at hr
  simp only
  rw [S.uX_of_mem ⟨by linarith [hr.2], by linarith [hr.1, ht.2]⟩]

/-- Mild equation on the Fourier side. -/
theorem MildFlow.cfL_mild (S : MildFlow h ρ0 T M u) (k : Fin d → ℤ) {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cfL k (u t) = (Real.exp (-(gradWeight k * t)) : ℂ) * cfL k ρ0 +
      ∫ s in Ioo 0 t, (Real.exp (-(gradWeight k * (t - s))) : ℂ) *
        divCoef k (Nvec h (uX T u s)) := by
  have htm : t ∈ Icc (0 : ℝ) T := ⟨ht.le, htT⟩
  rw [S.mild t htm, S.duhamel_eq_uX htm, map_add]
  congr 1
  · unfold heatL2
    rw [cfL_apply, cfL_apply, fourierCoeff_congr_ae (coeFn_heatCLM ht ρ0) k,
      fourierCoeff_heatOp ht ((Lp.memLp ρ0).integrable one_le_two)]
  · have hint := intervalIntegrable_duhamel (divHeat_duhamelKernel (d := d)) S.continuous_NvecX
      (M := (g + b) * (2 * M)) S.norm_NvecX_le ht.le
    unfold duhamel
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    have e1 : ∀ r ∈ Ioc (0 : ℝ) t, cfL k (divHeatFam d r (Nvec h (uX T u (t - r)))) =
        (Real.exp (-(gradWeight k * r)) : ℂ) * divCoef k (Nvec h (uX T u (t - r))) :=
      fun r hr => cfL_divHeat hr.1 _ k
    have e2 : ∫ r in (0 : ℝ)..t, cfL k (divHeatFam d r (Nvec h (uX T u (t - r)))) =
        ∫ r in (0 : ℝ)..t, (Real.exp (-(gradWeight k * r)) : ℂ) * divCoef k (Nvec h (uX T u (t - r))) := by
      refine intervalIntegral.integral_congr_ae ?_
      refine Filter.Eventually.of_forall fun r hr => ?_
      rw [Set.uIoc_of_le ht.le] at hr
      exact e1 r hr
    rw [e2]
    have e3 := intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => (Real.exp (-(gradWeight k * (t - s))) : ℂ) * divCoef k (Nvec h (uX T u s))) t
      (a := 0) (b := t)
    simp only [sub_sub_cancel, sub_self, sub_zero] at e3
    rw [e3, intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]

end MildFlowLemmas

theorem young_aux {w a b n : ℝ} (hw : 0 ≤ w) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hbn : b ^ 2 ≤ w * n) : 2 * (a * b) ≤ w * a ^ 2 + n := by
  rcases hw.eq_or_lt with h0 | hpos
  · subst h0
    have : b = 0 := by nlinarith
    subst this; simp; nlinarith
  · have h1 : w * (2 * (a * b)) ≤ w * (w * a ^ 2 + n) := by nlinarith [sq_nonneg (w * a - b)]
    exact le_of_mul_le_mul_left h1 hpos

/-- Scalar energy inequality for one Fourier mode. -/
theorem scalar_mode_energy {w T : ℝ} (hw : 0 ≤ w) {y c : ℝ → ℂ} {n : ℝ → ℝ}
    (hy : Continuous y) (hc : Continuous c) (hn : Continuous n) (hn0 : ∀ s, 0 ≤ n s)
    (hint : ∀ τ ∈ Icc (0 : ℝ) T, y τ = y 0 + ∫ s in (0 : ℝ)..τ, (-(w : ℂ) * y s + c s))
    (hcn : ∀ s, ‖c s‖ ^ 2 ≤ w * n s) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖y t‖ ^ 2 + w * ∫ s in (0 : ℝ)..t, ‖y s‖ ^ 2 ≤ ‖y 0‖ ^ 2 + ∫ s in (0 : ℝ)..t, n s := by
  have hcont : Continuous (fun s => -(w : ℂ) * y s + c s) := by fun_prop
  have hder : ∀ τ ∈ Ioo (0 : ℝ) t, HasDerivAt y (-(w : ℂ) * y τ + c τ) τ := by
    intro τ hτ
    have h1 := (hcont.integral_hasStrictDerivAt 0 τ).hasDerivAt.const_add (y 0)
    refine h1.congr_of_eventuallyEq ?_
    have : Ioo (0 : ℝ) T ∈ nhds τ := Ioo_mem_nhds hτ.1 (lt_of_lt_of_le hτ.2 htT)
    filter_upwards [this] with σ hσ
    exact hint σ ⟨hσ.1.le, hσ.2.le⟩
  have hder2 : ∀ τ ∈ Ioo (0 : ℝ) t, HasDerivAt (fun s => ‖y s‖ ^ 2)
      (2 * ⟪y τ, -(w : ℂ) * y τ + c τ⟫) τ := fun τ hτ => (hder τ hτ).norm_sq
  have hfc : Continuous (fun s => 2 * ⟪y s, -(w : ℂ) * y s + c s⟫) := by fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht0
    (f := fun s => ‖y s‖ ^ 2) (by fun_prop) hder2 (hfc.intervalIntegrable _ _)
  have hle : ∀ s, 2 * ⟪y s, -(w : ℂ) * y s + c s⟫ ≤ -w * ‖y s‖ ^ 2 + n s := by
    intro s
    have e : ⟪y s, -(w : ℂ) * y s + c s⟫ = -w * ‖y s‖ ^ 2 + ⟪y s, c s⟫ := by
      rw [inner_add_right]
      congr 1
      have : (-(w : ℂ) * y s) = (-w : ℝ) • y s := by simp [Complex.real_smul]
      rw [this, inner_smul_right, real_inner_self_eq_norm_sq]
    have h2 : ⟪y s, c s⟫ ≤ ‖y s‖ * ‖c s‖ := real_inner_le_norm _ _
    have h3 := young_aux (a := ‖y s‖) hw (norm_nonneg (c s)) (hn0 s) (hcn s)
    rw [e]
    nlinarith
  have hmono : ∫ s in (0 : ℝ)..t, 2 * ⟪y s, -(w : ℂ) * y s + c s⟫ ≤
      ∫ s in (0 : ℝ)..t, (-w * ‖y s‖ ^ 2 + n s) :=
    intervalIntegral.integral_mono_on ht0 (hfc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun s => -w * ‖y s‖ ^ 2 + n s).intervalIntegrable _ _)
      (fun s _ => hle s)
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun s => -w * ‖y s‖ ^ 2).intervalIntegrable _ _)
    (hn.intervalIntegrable _ _), intervalIntegral.integral_const_mul (-w) (fun s => ‖y s‖ ^ 2)] at hmono
  linarith

theorem cfL_coordL (j : Fin d) (F : L2v d) (k : Fin d → ℤ) :
    cfL k (coordL j F) = fourierCoeff (fun x => (F : Torus d → Tangent d) x j) k := by
  rw [cfL_apply, fourierCoeff_congr_ae (coeFn_coordL j F) k]

theorem divCoef_eq (k : Fin d → ℤ) (F : L2v d) :
    divCoef k F = ∑ j, 2 * π * Complex.I * (k j : ℂ) * cfL k (coordL j F) := by
  rw [divCoef_apply]; simp_rw [cfL_coordL]

theorem norm_divCoef_sq_le (k : Fin d → ℤ) (F : L2v d) :
    ‖divCoef k F‖ ^ 2 ≤ gradWeight k * ∑ j, ‖cfL k (coordL j F)‖ ^ 2 := by
  rw [divCoef_eq]
  have h1 : ‖∑ j, 2 * π * Complex.I * (k j : ℂ) * cfL k (coordL j F)‖ ≤
      ∑ j, (2 * π * |((k j : ℤ) : ℝ)|) * ‖cfL k (coordL j F)‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_mul]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => 2 * π * |((k j : ℤ) : ℝ)|)
    (fun j => ‖cfL k (coordL j F)‖)
  have h3 : ∑ j, (2 * π * |((k j : ℤ) : ℝ)|) ^ 2 = gradWeight k := by
    unfold gradWeight
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, mul_pow, sq_abs]; ring
  rw [h3] at h2
  have h0 : 0 ≤ ∑ j, (2 * π * |((k j : ℤ) : ℝ)|) * ‖cfL k (coordL j F)‖ :=
    Finset.sum_nonneg fun j _ => by positivity
  calc _ ≤ (∑ j, (2 * π * |((k j : ℤ) : ℝ)|) * ‖cfL k (coordL j F)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem gradWeight_nonneg (k : Fin d → ℤ) : 0 ≤ gradWeight k := by
  unfold gradWeight; positivity

section MildFlowLemmas
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.mode_integral_form (S : MildFlow h ρ0 T M u) (k : Fin d → ℤ) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    cfL k (uX T u τ) = cfL k (uX T u 0) + ∫ s in (0 : ℝ)..τ,
      (-(gradWeight k : ℂ) * cfL k (uX T u s) + divCoef k (Nvec h (uX T u s))) := by
  have h0 : uX T u 0 = ρ0 := by rw [S.uX_of_mem ⟨le_rfl, S.hT⟩, S.u_zero]
  have hyc : Continuous fun s => cfL k (uX T u s) := (cfL k).continuous.comp S.continuous_uX
  have hcc : Continuous fun s => divCoef k (Nvec h (uX T u s)) :=
    (divCoef k).continuous.comp S.continuous_NvecX
  rcases hτ.1.eq_or_lt with h00 | hpos
  · subst h00; simp
  · have hM' : ∀ s, ‖divCoef k (Nvec h (uX T u s))‖ ≤ ‖divCoef k‖ * ((g + b) * (2 * M)) :=
      fun s => ((divCoef k).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (S.norm_NvecX_le s) (norm_nonneg _))
    have key := mode_integral_ode (w := gradWeight k) hpos (cfL k ρ0) hcc.measurable hM'
      (U := fun s => cfL k (uX T u s)) (fun τ' h1 h2 => by
        rw [S.uX_of_mem ⟨h1.le, h2.trans hτ.2⟩]
        exact S.cfL_mild k h1 (h2.trans hτ.2))
    rw [h0]
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun s =>
        -(gradWeight k : ℂ) * cfL k (uX T u s)).intervalIntegrable _ _)
      (hcc.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le hpos.le, intervalIntegral.integral_of_le hpos.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    rw [← key]; ring

end MildFlowLemmas

/-- The finite set of frequencies in the ball `|k| ≤ R`. -/
noncomputable def ballSet (R : ℝ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(⌈R⌉ : ℤ)) ⌈R⌉).filter (InFreqBall R)

theorem mem_ballSet {R : ℝ} {k : Fin d → ℤ} : k ∈ ballSet R ↔ InFreqBall R k := by
  unfold ballSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun hk => ⟨fun j => ?_, hk⟩⟩
  have h1 : ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : |((k j : ℤ) : ℝ)| ≤ R := by
    refine le_trans ?_ hk
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h1
  have h3 : |((k j : ℤ) : ℝ)| ≤ (⌈R⌉ : ℝ) := h2.trans (Int.le_ceil R)
  rw [Finset.mem_Icc]
  have := abs_le.mp h3
  constructor
  · have : (-(⌈R⌉ : ℝ)) ≤ (k j : ℝ) := this.1
    exact_mod_cast this
  · exact_mod_cast this.2

theorem hasSum_ball {R : ℝ} (f : (Fin d → ℤ) → ℝ) :
    HasSum (fun k => if InFreqBall R k then f k else 0) (∑ k ∈ ballSet R, f k) := by
  have : HasSum (fun k => if InFreqBall R k then f k else 0)
      (∑ k ∈ ballSet R, if InFreqBall R k then f k else 0) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => by
      rw [mem_ballSet] at hk; simp [hk])
  convert this using 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_ballSet] at hk; simp [hk]

theorem norm_cutCoeff_sq (c : (Fin d → ℤ) → ℂ) (R : ℝ) (k : Fin d → ℤ) :
    ‖cutCoeff c R k‖ ^ 2 = if InFreqBall R k then ‖c k‖ ^ 2 else 0 := by
  unfold cutCoeff; split_ifs <;> simp

/-- Parseval for the projection `Π_R`. -/
theorem integral_sq_cutoff_eq (f : Torus d → ℝ) (R : ℝ) :
    ∫ x, (fourierCutoff f R x) ^ 2 ∂haar d = ∑ k ∈ ballSet R, ‖fourierCoeff f k‖ ^ 2 := by
  have h1 := hasSum_sq_fourierCoeff (memLp_fourierCutoff f R)
  have h2 : HasSum (fun k => ‖fourierCoeff (fourierCutoff f R) k‖ ^ 2)
      (∑ k ∈ ballSet R, ‖fourierCoeff f k‖ ^ 2) := by
    have := hasSum_ball (R := R) (fun k => ‖fourierCoeff f k‖ ^ 2)
    convert this using 1
    funext k
    rw [fourierCoeff_fourierCutoff, norm_cutCoeff_sq]
  exact h1.unique h2

theorem fourierCoeff_coordPartial_cutoff (f : Torus d → ℝ) (R : ℝ) (j : Fin d) (k : Fin d → ℤ) :
    fourierCoeff (coordPartial j (fourierCutoff f R)) k =
      2 * π * Complex.I * (k j : ℂ) * fourierCoeff (fourierCutoff f R) k := by
  have hsm : IsSmoothPeriodic (fourierCutoff f R) := isSmoothPeriodic_psum _ _
  exact mFourierCoeff_of_ibp (integrable_of_continuous_torus hsm.continuous_torus)
    (integrable_of_continuous_torus (hsm.continuous_coordPartial j)) j
    (fun φ hφ => integral_mul_coordPartial_of_smooth hsm hφ j) k

/-- The gradient of the trigonometric polynomial `Π_R f`, as a vector field. -/
noncomputable def cutGrad (f : Torus d → ℝ) (R : ℝ) (x : Torus d) : Tangent d :=
  WithLp.toLp 2 fun j => coordPartial j (fourierCutoff f R) x

theorem memLp_coordPartial_cutoff (f : Torus d → ℝ) (R : ℝ) (j : Fin d) :
    MemLp (coordPartial j (fourierCutoff f R)) 2 (haar d) := by
  have : coordPartial j (fourierCutoff f R) = SharpLSI.psum
      (fun k => 2 * π * Complex.I * (k j : ℂ) * cutCoeff (fourierCoeff f) R k) ⌈R⌉₊ := by
    funext x
    exact coordPartial_psum _ _ j x
  rw [this]
  exact SharpLSI.memLp_psum _ _ 2

theorem isWeakGradient_cutoff_cutGrad {f : Torus d → ℝ} (R : ℝ) :
    IsWeakGradient (fourierCutoff f R) (cutGrad f R) :=
  isWeakGradient_of_fourierCoeff (memLp_fourierCutoff f R)
    (memLp_piLp_iff.mpr fun j => memLp_coordPartial_cutoff f R j)
    (fun j k => fourierCoeff_coordPartial_cutoff f R j k)

theorem integral_norm_sq_cutGrad {f : Torus d → ℝ} (R : ℝ) :
    ∫ x, ‖cutGrad f R x‖ ^ 2 ∂haar d =
      ∑ k ∈ ballSet R, gradWeight k * ‖fourierCoeff f k‖ ^ 2 := by
  have h1 := hasSum_gradWeight_weakGradient (isWeakGradient_cutoff_cutGrad (f := f) R)
  have h2 : HasSum (fun k => gradWeight k * ‖fourierCoeff (fourierCutoff f R) k‖ ^ 2)
      (∑ k ∈ ballSet R, gradWeight k * ‖fourierCoeff f k‖ ^ 2) := by
    have := hasSum_ball (R := R) (fun k => gradWeight k * ‖fourierCoeff f k‖ ^ 2)
    convert this using 1
    funext k
    rw [fourierCoeff_fourierCutoff, norm_cutCoeff_sq]
    split_ifs <;> simp
  exact h1.unique h2

theorem integral_norm_sq_fourierCutoffGrad {F : Torus d → Tangent d} (R : ℝ) :
    ∫ x, ‖fourierCutoffGrad F R x‖ ^ 2 ∂haar d =
      ∑ j, ∑ k ∈ ballSet R, ‖fourierCoeff (fun x => F x j) k‖ ^ 2 := by
  have hj : ∀ x, ‖fourierCutoffGrad F R x‖ ^ 2 = ∑ j, (fourierCutoff (fun y => F y j) R x) ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [fourierCutoffGrad]
  simp_rw [hj]
  rw [integral_finsetSum _ (fun j _ => (memLp_fourierCutoff _ R).integrable_sq)]
  exact Finset.sum_congr rfl fun j _ => integral_sq_cutoff_eq _ R

section MildFlowLemmas
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.mode_energy (S : MildFlow h ρ0 T M u) (k : Fin d → ℤ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ‖cfL k (uX T u t)‖ ^ 2 + gradWeight k * ∫ s in (0 : ℝ)..t, ‖cfL k (uX T u s)‖ ^ 2 ≤
      ‖cfL k (uX T u 0)‖ ^ 2 + ∫ s in (0 : ℝ)..t,
        ∑ j, ‖cfL k (coordL j (Nvec h (uX T u s)))‖ ^ 2 := by
  refine scalar_mode_energy (gradWeight_nonneg k) (y := fun s => cfL k (uX T u s))
    (c := fun s => divCoef k (Nvec h (uX T u s)))
    (n := fun s => ∑ j, ‖cfL k (coordL j (Nvec h (uX T u s)))‖ ^ 2)
    ((cfL k).continuous.comp S.continuous_uX)
    ((divCoef k).continuous.comp S.continuous_NvecX) ?_ (fun s => by positivity)
    (fun τ hτ => S.mode_integral_form k hτ) (fun s => norm_divCoef_sq_le k _) ht0 htT
  refine continuous_finsetSum _ fun j _ => ?_
  have : Continuous fun s => cfL k (coordL j (Nvec h (uX T u s))) :=
    (cfL k).continuous.comp ((coordL j).continuous.comp S.continuous_NvecX)
  fun_prop

theorem MildFlow.int_cutGrad_eq (_S : MildFlow h ρ0 T M u) (R : ℝ) (s : ℝ) :
    ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d =
      ∑ k ∈ ballSet R, gradWeight k * ‖cfL k (uX T u s)‖ ^ 2 := by
  rw [integral_norm_sq_cutGrad]
  simp_rw [cfL_apply]

theorem MildFlow.int_cutN_eq (_S : MildFlow h ρ0 T M u) (R : ℝ) (s : ℝ) :
    ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d =
      ∑ k ∈ ballSet R, ∑ j, ‖cfL k (coordL j (Nvec h (uX T u s)))‖ ^ 2 := by
  rw [integral_norm_sq_fourierCutoffGrad, Finset.sum_comm]
  simp_rw [cfL_coordL]

theorem MildFlow.int_cut_eq (_S : MildFlow h ρ0 T M u) (R : ℝ) (s : ℝ) :
    ∫ x, (fourierCutoff (⇑(uX T u s)) R x) ^ 2 ∂haar d =
      ∑ k ∈ ballSet R, ‖cfL k (uX T u s)‖ ^ 2 := by
  rw [integral_sq_cutoff_eq]
  simp_rw [cfL_apply]

theorem MildFlow.continuous_cutGrad (S : MildFlow h ρ0 T M u) (R : ℝ) :
    Continuous fun s => ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d := by
  simp_rw [S.int_cutGrad_eq R]
  refine continuous_finsetSum _ fun k _ => ?_
  have := (cfL k).continuous.comp S.continuous_uX
  fun_prop

theorem MildFlow.continuous_cutN (S : MildFlow h ρ0 T M u) (R : ℝ) :
    Continuous fun s => ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d := by
  simp_rw [S.int_cutN_eq R]
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ => ?_
  have : Continuous fun s => cfL k (coordL j (Nvec h (uX T u s))) :=
    (cfL k).continuous.comp ((coordL j).continuous.comp S.continuous_NvecX)
  fun_prop

theorem MildFlow.cutoff_energy_uX (S : MildFlow h ρ0 T M u) (R : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ x, (fourierCutoff (⇑(uX T u t)) R x) ^ 2 ∂haar d +
      ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d ≤
    ∫ x, (fourierCutoff (⇑(uX T u 0)) R x) ^ 2 ∂haar d +
      ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d := by
  have hsum := Finset.sum_le_sum (s := ballSet R) fun k _ => S.mode_energy k ht0 htT
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hA := S.int_cutGrad_eq R
  have hB := S.int_cutN_eq R
  have hP := S.int_cut_eq R
  have hcy : ∀ k : Fin d → ℤ, Continuous fun s => gradWeight k * ‖cfL k (uX T u s)‖ ^ 2 :=
    fun k => by
      have := (cfL k).continuous.comp S.continuous_uX
      fun_prop
  have hcn : ∀ k : Fin d → ℤ, Continuous fun s =>
      ∑ j, ‖cfL k (coordL j (Nvec h (uX T u s)))‖ ^ 2 := fun k => by
    refine continuous_finsetSum _ fun j _ => ?_
    have : Continuous fun s => cfL k (coordL j (Nvec h (uX T u s))) :=
      (cfL k).continuous.comp ((coordL j).continuous.comp S.continuous_NvecX)
    fun_prop
  simp_rw [hA, hB, hP]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hcy k).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun k _ => (hcn k).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul] at *
  exact hsum

theorem MildFlow.cutoff_energy (S : MildFlow h ρ0 T M u) (R : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ x, (fourierCutoff (⇑(u t)) R x) ^ 2 ∂haar d +
      ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
    ∫ x, (fourierCutoff (⇑ρ0) R x) ^ 2 ∂haar d +
      ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (u s))) R x‖ ^ 2 ∂haar d := by
  have := S.cutoff_energy_uX R ht0 htT
  have e0 : uX T u 0 = ρ0 := by rw [S.uX_of_mem ⟨le_rfl, S.hT⟩, S.u_zero]
  rw [S.uX_of_mem ⟨ht0, htT⟩, e0] at this
  have e1 : ∀ s ∈ Set.uIcc (0 : ℝ) t, uX T u s = u s := fun s hs => by
    rw [Set.uIcc_of_le ht0] at hs
    exact S.uX_of_mem ⟨hs.1, hs.2.trans htT⟩
  have i1 : ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d =
      ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d :=
    intervalIntegral.integral_congr fun s hs => by simp only [e1 s hs]
  have i2 : ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d =
      ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (u s))) R x‖ ^ 2 ∂haar d :=
    intervalIntegral.integral_congr fun s hs => by simp only [e1 s hs]
  rw [i1, i2] at this
  exact this

end MildFlowLemmas

theorem fourierCoeff_zero_eq (f : Torus d → ℝ) :
    fourierCoeff f 0 = ((∫ x, f x ∂haar d : ℝ) : ℂ) := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq]
  simp [UnitAddTorus.mFourier_zero, integral_complex_ofReal]

theorem integral_sq_cutoff_le {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (R : ℝ) :
    ∫ x, (fourierCutoff f R x) ^ 2 ∂haar d ≤ ∫ x, (f x) ^ 2 ∂haar d := by
  rw [integral_sq_cutoff_eq]
  exact sum_le_hasSum (ballSet R) (fun k _ => by positivity) (hasSum_sq_fourierCoeff hf)

theorem integral_norm_sq_fourierCutoffGrad_le {F : Torus d → Tangent d} (hF : MemLp F 2 (haar d))
    (R : ℝ) : ∫ x, ‖fourierCutoffGrad F R x‖ ^ 2 ∂haar d ≤ ∫ x, ‖F x‖ ^ 2 ∂haar d := by
  rw [integral_norm_sq_fourierCutoffGrad]
  have hj : ∀ x, ‖F x‖ ^ 2 = ∑ j, (F x j) ^ 2 := fun x => by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by simp
  simp_rw [hj]
  rw [integral_finsetSum _ (fun j _ => (memLp_coord hF j).integrable_sq)]
  exact Finset.sum_le_sum fun j _ =>
    sum_le_hasSum (ballSet R) (fun k _ => by positivity) (hasSum_sq_fourierCoeff (memLp_coord hF j))

theorem Lp_norm_sq_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Lp E 2 (haar d)) : ‖F‖ ^ 2 = ∫ x, ‖(F : Torus d → E) x‖ ^ 2 ∂haar d := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

section MildFlowLemmas
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.mass_const (S : MildFlow h ρ0 T M u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ x, (u t : Torus d → ℝ) x ∂haar d = ∫ x, (ρ0 : Torus d → ℝ) x ∂haar d := by
  have key := fun hpos : 0 < t => S.cfL_mild 0 hpos ht.2
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0; rw [S.u_zero]
  · have hz : divCoef (0 : Fin d → ℤ) = 0 := by
      ext F
      simp [divCoef_apply]
    have := key hpos
    have gw : gradWeight (0 : Fin d → ℤ) = 0 := by simp [gradWeight]
    simp [hz, gw] at this
    rw [cfL_apply, cfL_apply, fourierCoeff_zero_eq, fourierCoeff_zero_eq] at this
    exact_mod_cast this

end MildFlowLemmas

theorem sq_div_le_aux {w : ℝ} (hw : 0 ≤ w) {y c : ℂ} {n : ℝ} (hn : 0 ≤ n) (hcn : ‖c‖ ^ 2 ≤ w * n) :
    ‖-(w : ℂ) * y + c‖ ^ 2 / (1 + w) ≤ 2 * w * ‖y‖ ^ 2 + 2 * n := by
  rw [div_le_iff₀ (by linarith)]
  have h1 : ‖-(w : ℂ) * y + c‖ ≤ w * ‖y‖ + ‖c‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  have h2 : ‖-(w : ℂ) * y + c‖ ^ 2 ≤ (w * ‖y‖ + ‖c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (w * ‖y‖ - ‖c‖), norm_nonneg y, norm_nonneg c, mul_nonneg hw hn,
    mul_nonneg hw (sq_nonneg ‖y‖), mul_nonneg (mul_nonneg hw hw) (sq_nonneg ‖y‖)]

section MildFlowLemmas
variable {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ} {u : ℝ → L2s d}

theorem MildFlow.integral_uX_congr (S : MildFlow h ρ0 T M u) (F : L2s d → ℝ) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    ∫ s in (0 : ℝ)..t, F (uX T u s) = ∫ s in (0 : ℝ)..t, F (u s) :=
  intervalIntegral.integral_congr fun s hs => by
    rw [Set.uIcc_of_le ht0] at hs
    simp only [S.uX_of_mem ⟨hs.1, hs.2.trans htT⟩]

theorem MildFlow.norm_N_le (S : MildFlow h ρ0 T M u) (s : ℝ) :
    ‖Nvec h (uX T u s)‖ ≤ (g + b) * (2 * M) := S.norm_NvecX_le s

theorem MildFlow.H1_bound_uX (S : MildFlow h ρ0 T M u) (R : ℝ) :
    ∫ s in (0 : ℝ)..T, ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d ≤
      ‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2 := by
  have e := S.cutoff_energy_uX R S.hT le_rfl
  have e0 : uX T u 0 = ρ0 := by rw [S.uX_of_mem ⟨le_rfl, S.hT⟩, S.u_zero]
  rw [e0] at e
  have h1 : 0 ≤ ∫ x, (fourierCutoff (⇑(uX T u T)) R x) ^ 2 ∂haar d :=
    integral_nonneg fun x => sq_nonneg _
  have h2 : ∫ x, (fourierCutoff (⇑ρ0) R x) ^ 2 ∂haar d ≤ ‖ρ0‖ ^ 2 := by
    rw [Lp_norm_sq_eq]
    refine (integral_sq_cutoff_le (Lp.memLp ρ0) R).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have h3 : ∫ s in (0 : ℝ)..T, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d ≤
      T * ((g + b) * (2 * M)) ^ 2 := by
    have : ∫ s in (0 : ℝ)..T, ((g + b) * (2 * M)) ^ 2 = T * ((g + b) * (2 * M)) ^ 2 := by
      simp
    rw [← this]
    refine intervalIntegral.integral_mono_on S.hT ((S.continuous_cutN R).intervalIntegrable _ _)
      (by simp) fun s _ => ?_
    refine (integral_norm_sq_fourierCutoffGrad_le (Lp.memLp _) R).trans ?_
    rw [← Lp_norm_sq_eq]
    exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_N_le s) 2
  linarith

theorem MildFlow.H1_bound (S : MildFlow h ρ0 T M u) (R : ℝ) :
    ∫ s in (0 : ℝ)..T, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
      ‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2 := by
  rw [← S.integral_uX_congr (fun f => ∫ x, ‖cutGrad (⇑f) R x‖ ^ 2 ∂haar d) S.hT le_rfl]
  exact S.H1_bound_uX R

/-- The time derivative of the `k`-th Fourier coefficient of the flow. -/
noncomputable def MildFlow.modeDeriv (h : MeanFieldData G B g b) (u : ℝ → L2s d) (k : Fin d → ℤ) (s : ℝ) : ℂ :=
  -(gradWeight k : ℂ) * cfL k (u s) + divCoef k (Nvec h (u s))

theorem MildFlow.modeDeriv_integral (S : MildFlow h ρ0 T M u) (k : Fin d → ℤ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    cfL k (u t) = cfL k ρ0 + ∫ s in (0 : ℝ)..t, modeDeriv h u k s := by
  have := S.mode_integral_form k ht
  have e0 : uX T u 0 = ρ0 := by rw [S.uX_of_mem ⟨le_rfl, S.hT⟩, S.u_zero]
  rw [S.uX_of_mem ht, e0] at this
  rw [this]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht.1] at hs
  simp only [modeDeriv, S.uX_of_mem ⟨hs.1, hs.2.trans ht.2⟩]

theorem MildFlow.continuousOn_modeDeriv (S : MildFlow h ρ0 T M u) (k : Fin d → ℤ) :
    ContinuousOn (modeDeriv h u k) (Icc 0 T) := by
  have hc : Continuous fun s => -(gradWeight k : ℂ) * cfL k (uX T u s) +
      divCoef k (Nvec h (uX T u s)) := by
    have h1 := (cfL k).continuous.comp S.continuous_uX
    have h2 := (divCoef k).continuous.comp S.continuous_NvecX
    fun_prop
  refine hc.continuousOn.congr fun s hs => ?_
  simp only [modeDeriv, S.uX_of_mem hs]

theorem MildFlow.H_neg1_bound (S : MildFlow h ρ0 T M u) (R : ℝ) :
    ∫ s in (0 : ℝ)..T, ∑ k ∈ ballSet R, ‖modeDeriv h u k s‖ ^ 2 / (1 + gradWeight k) ≤
      2 * (‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) + 2 * (T * ((g + b) * (2 * M)) ^ 2) := by
  have hcont : Continuous fun s => ∑ k ∈ ballSet R,
      ‖-(gradWeight k : ℂ) * cfL k (uX T u s) + divCoef k (Nvec h (uX T u s))‖ ^ 2 /
        (1 + gradWeight k) := by
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 := (cfL k).continuous.comp S.continuous_uX
    have h2 := (divCoef k).continuous.comp S.continuous_NvecX
    fun_prop
  have hpt : ∀ s, ∑ k ∈ ballSet R,
      ‖-(gradWeight k : ℂ) * cfL k (uX T u s) + divCoef k (Nvec h (uX T u s))‖ ^ 2 /
        (1 + gradWeight k) ≤
      2 * (∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d) +
        2 * (∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d) := by
    intro s
    rw [S.int_cutGrad_eq R, S.int_cutN_eq R, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := sq_div_le_aux (gradWeight_nonneg k) (y := cfL k (uX T u s))
      (c := divCoef k (Nvec h (uX T u s)))
      (n := ∑ j, ‖cfL k (coordL j (Nvec h (uX T u s)))‖ ^ 2) (by positivity)
      (norm_divCoef_sq_le k _)
    linarith
  have hsum : ∫ s in (0 : ℝ)..T, ∑ k ∈ ballSet R,
      ‖-(gradWeight k : ℂ) * cfL k (uX T u s) + divCoef k (Nvec h (uX T u s))‖ ^ 2 /
        (1 + gradWeight k) ≤
      2 * (‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) + 2 * (T * ((g + b) * (2 * M)) ^ 2) := by
    have hN : ∫ s in (0 : ℝ)..T, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d ≤
        T * ((g + b) * (2 * M)) ^ 2 := by
      have : ∫ s in (0 : ℝ)..T, ((g + b) * (2 * M)) ^ 2 = T * ((g + b) * (2 * M)) ^ 2 := by
        simp
      rw [← this]
      refine intervalIntegral.integral_mono_on S.hT ((S.continuous_cutN R).intervalIntegrable _ _)
        (by simp) fun s _ => ?_
      refine (integral_norm_sq_fourierCutoffGrad_le (Lp.memLp _) R).trans ?_
      rw [← Lp_norm_sq_eq]
      exact pow_le_pow_left₀ (norm_nonneg _) (S.norm_N_le s) 2
    have c1 : Continuous fun s => 2 * ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d :=
      continuous_const.mul (S.continuous_cutGrad R)
    have c2 : Continuous fun s =>
        2 * ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d :=
      continuous_const.mul (S.continuous_cutN R)
    calc _ ≤ ∫ s in (0 : ℝ)..T, (2 * (∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d) +
        2 * (∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d)) :=
          intervalIntegral.integral_mono_on S.hT (hcont.intervalIntegrable _ _)
            ((c1.add c2).intervalIntegrable _ _) fun s _ => hpt s
      _ = 2 * (∫ s in (0 : ℝ)..T, ∫ x, ‖cutGrad (⇑(uX T u s)) R x‖ ^ 2 ∂haar d) +
          2 * (∫ s in (0 : ℝ)..T, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (uX T u s))) R x‖ ^ 2 ∂haar d) := by
          rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ _ := by linarith [S.H1_bound_uX R]
  have e := S.integral_uX_congr (fun f => ∑ k ∈ ballSet R,
    ‖-(gradWeight k : ℂ) * cfL k f + divCoef k (Nvec h f)‖ ^ 2 / (1 + gradWeight k)) S.hT le_rfl
  unfold modeDeriv
  rw [← e]
  exact hsum

end MildFlowLemmas

/-- The local flow of `modified_mean_field_mild_contraction` is a `MildFlow`. -/
theorem exists_mildFlow (h : MeanFieldData G B g b) (ρ0 : L2s d) (M : ℝ)
    (hρ0 : ∀ᵐ x ∂haar d, |ρ0 x| ≤ M) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → L2s d, MildFlow h ρ0 T M u := by
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hρ0.exists
    exact (abs_nonneg _).trans hx
  obtain ⟨T, hT, u, hc, hb, hm⟩ := (modified_mean_field_mild_contraction h).2.2.2.2 ρ0 M hρ0
  exact ⟨T, hT, u, ⟨hT.le, hM, hc, hb, hm⟩⟩

/-- Partial regularity theorem for a mild flow: continuity, `L∞` bound, uniform `H¹` bound,
Fourier-side `H⁻¹` time derivative, mass conservation and the projected energy inequality for
every cutoff.  (Positivity and `P ρ = ρ` are not included.) -/
theorem mildFlow_regularity_energy_mass {h : MeanFieldData G B g b} {ρ0 : L2s d} {T M : ℝ}
    {u : ℝ → L2s d} (S : MildFlow h ρ0 T M u) :
    ContinuousOn u (Icc 0 T) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ x ∂haar d, |u t x| ≤ 2 * M) ∧
    (∀ R : ℝ, ∫ s in (0 : ℝ)..T, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
      ‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) ∧
    (∀ k : Fin d → ℤ, ContinuousOn (MildFlow.modeDeriv h u k) (Icc 0 T) ∧
      ∀ t ∈ Icc (0 : ℝ) T, cfL k (u t) = cfL k ρ0 + ∫ s in (0 : ℝ)..t, MildFlow.modeDeriv h u k s) ∧
    (∀ R : ℝ, ∫ s in (0 : ℝ)..T, ∑ k ∈ ballSet R, ‖MildFlow.modeDeriv h u k s‖ ^ 2 / (1 + gradWeight k) ≤
      2 * (‖ρ0‖ ^ 2 + T * ((g + b) * (2 * M)) ^ 2) + 2 * (T * ((g + b) * (2 * M)) ^ 2)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, ∫ x, (u t : Torus d → ℝ) x ∂haar d = ∫ x, (ρ0 : Torus d → ℝ) x ∂haar d) ∧
    (∀ R : ℝ, ∀ t ∈ Icc (0 : ℝ) T,
      ∫ x, (fourierCutoff (⇑(u t)) R x) ^ 2 ∂haar d +
          ∫ s in (0 : ℝ)..t, ∫ x, ‖cutGrad (⇑(u s)) R x‖ ^ 2 ∂haar d ≤
        ∫ x, (fourierCutoff (⇑ρ0) R x) ^ 2 ∂haar d +
          ∫ s in (0 : ℝ)..t, ∫ x, ‖fourierCutoffGrad (⇑(Nvec h (u s))) R x‖ ^ 2 ∂haar d) :=
  ⟨S.cont, S.bound, fun R => S.H1_bound R,
    fun k => ⟨S.continuousOn_modeDeriv k, fun _ ht => S.modeDeriv_integral k ht⟩,
    fun R => S.H_neg1_bound R, fun _ ht => S.mass_const ht,
    fun R _ ht => S.cutoff_energy R ht.1 ht.2⟩

end DGPS.Lipschitz
