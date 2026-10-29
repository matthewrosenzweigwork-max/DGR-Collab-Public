import DGPS.Examples.PositiveH1.Model
import DGPS.Model.Barycenter
import DGPS.Model.Drift
import DGPS.Foundations.SobolevCalculus
import DGPS.Model.FreeEnergy
import DGPS.Equilibrium.Hessian

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff


/-!
# Admissible density regularity and convolution force (H1007)

For every absolute-admissible `ρ = u²` on `𝕋¹` (`AbsoluteDensity 1`):
* `u` has a bounded continuous representative with an absolutely continuous (FTC) profile on the
  lifts `t ↦ u (lift1 t)` (`density_regular`, via the 1D Sobolev theorem `sobolev1`);
* `ρ ∈ H¹ ∩ L∞` with weak derivative `ρ' = 2 u u' ∈ L²` (`densityDeriv`);
* the actual drift of the positive `H¹` model, `positiveH1Drift.force ρ = κ R' * ρ`, is a continuous
  bounded vector field with `‖·‖ ≤ κ ‖R'‖₂ ‖ρ‖₂` and is an `L¹` weak gradient of the interaction
  potential (hence an `AbsoluteDrift`);
* `R' * ρ` is `C¹` along lifts with derivative `R' * ρ'`;
* scores `a ∇u + b u F` are `L²` for every density `u` and every drift density `σ`.
-/

namespace DGPS.Examples.PositiveH1.Nonlinear



/-- The lift `ℝ → 𝕋¹`. -/
noncomputable def lift1 (t : ℝ) : Torus 1 := torusLift fun _ => t

theorem lift1_add (s t : ℝ) : lift1 (s + t) = lift1 s + lift1 t := by
  unfold lift1
  exact SharpLSI.liftT_add (fun _ => s) (fun _ => t)

theorem lift1_sub (s t : ℝ) : lift1 (s - t) = lift1 s - lift1 t := by
  unfold lift1
  exact SharpLSI.liftT_sub (fun _ => s) (fun _ => t)

theorem lift1_add_one (t : ℝ) : lift1 (t + 1) = lift1 t := by
  funext i
  exact AddCircle.coe_add_period (1 : ℝ) t

theorem continuous_lift1 : Continuous lift1 :=
  continuous_pi fun _ => AddCircle.continuous_mk' _

theorem periodic_lift1 : Function.Periodic lift1 1 := lift1_add_one

theorem lift1_exists (x : Torus 1) : ∃ t : ℝ, x = lift1 t :=
  Examples.PositiveH1.Fourier.torus_exists_lift x

instance haar1_negInvariant : (haar 1).IsNegInvariant :=
  Measure.IsAddHaarMeasure.isNegInvariant_of_regular (haar 1)

theorem haar1_eq_map : haar 1 = (volume.restrict (Ioc (0 : ℝ) 1)).map lift1 := by
  have hb : (volume : Measure (Fin 1 → ℝ)).restrict (SharpLSI.unitBox (Fin 1)) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 1) := by
    rw [SharpLSI.unitBox, ← Measure.restrict_pi_pi, volume_pi]
  rw [haar_eq_map_unitBox, hb]
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have h := (measurePreserving_funUnique μ (Fin 1)).symm
    (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have h2 : Measure.pi (fun _ : Fin 1 => μ) =
      μ.map (MeasurableEquiv.funUnique (Fin 1) ℝ).symm := h.map_eq.symm
  rw [h2, Measure.map_map SharpLSI.measurable_liftT
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurable]
  rfl



theorem sup_bound {p p' : ℝ → ℝ} (hp : ∀ t, HasDerivAt p (p' t) t) (hp' : Continuous p')
    (hper : Function.Periodic p 1) (t : ℝ) :
    |p t| ≤ (∫ s in (0:ℝ)..1, |p s|) + ∫ s in (0:ℝ)..1, |p' s| := by
  have hpc : Continuous p := continuous_iff_continuousAt.2 fun t => (hp t).continuousAt
  have hosc : ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1,
      |p r - p s| ≤ ∫ x in (0:ℝ)..1, |p' x| := by
    intro s hs r hr
    have h1 : p r - p s = ∫ x in s..r, p' x :=
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hp x)
        (hp'.intervalIntegrable _ _)).symm
    rw [h1]
    have h2 := intervalIntegral.norm_integral_le_integral_norm_uIoc (a := s) (b := r)
      (f := p') (μ := volume)
    rw [Real.norm_eq_abs] at h2
    refine h2.trans ?_
    simp only [Real.norm_eq_abs]
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_mono_set (hp'.abs.integrableOn_Ioc) (Eventually.of_forall fun x => abs_nonneg _) ?_
    refine (LE.le.eventuallySubset ?_)
    intro x hx
    simp only [Set.uIoc, mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt (le_min hs.1 hr.1) hx.1, hx.2.trans (max_le hs.2 hr.2)⟩
  have ht : p t = p (Int.fract t) := by
    have := hper.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at this
    rw [Int.fract]; exact this.symm
  rw [ht]
  set r := Int.fract t with hr
  have hr01 : r ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hsplit : p r = (∫ s in (0:ℝ)..1, (p r - p s)) + ∫ s in (0:ℝ)..1, p s := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hpc.intervalIntegrable _ _)]
    simp
  have hA : |∫ s in (0:ℝ)..1, (p r - p s)| ≤ ∫ x in (0:ℝ)..1, |p' x| := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine (intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.sub hpc).abs.intervalIntegrable _ _) intervalIntegrable_const
      (fun s hs => hosc s hs r hr01)).trans ?_
    simp
  have hB : |∫ s in (0:ℝ)..1, p s| ≤ ∫ s in (0:ℝ)..1, |p s| :=
    intervalIntegral.abs_integral_le_integral_abs zero_le_one
  rw [hsplit]
  calc _ ≤ |∫ s in (0:ℝ)..1, (p r - p s)| + |∫ s in (0:ℝ)..1, p s| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem abs_integral_le_periodic {f : ℝ → ℝ} (hper : Function.Periodic f 1)
    (hint : ∀ t₁ t₂, IntervalIntegrable f volume t₁ t₂) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ (⌈|b - a|⌉₊ : ℝ) * ∫ x in (0:ℝ)..1, |f x| := by
  have hint' : ∀ t₁ t₂, IntervalIntegrable (fun x => |f x|) volume t₁ t₂ := fun t₁ t₂ => (hint t₁ t₂).abs
  have hperabs : Function.Periodic (fun x => |f x|) 1 := fun x => by simp [hper x]
  have key : ∀ a b : ℝ, a ≤ b → |∫ x in a..b, f x| ≤ (⌈b - a⌉₊ : ℝ) * ∫ x in (0:ℝ)..1, |f x| := by
    intro a b hab
    refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
    have hn : b ≤ a + (⌈b - a⌉₊ : ℝ) := by linarith [Nat.le_ceil (b - a)]
    have h1 : ∫ x in a..b, |f x| ≤ ∫ x in a..a + (⌈b - a⌉₊ : ℝ), |f x| :=
      intervalIntegral.integral_mono_interval le_rfl hab hn
        (Eventually.of_forall fun x => abs_nonneg _) (hint' _ _)
    refine h1.trans ?_
    have h2 := hperabs.intervalIntegral_add_zsmul_eq (⌈b - a⌉₊ : ℤ) a hint'
    simp only [zsmul_eq_mul, Int.cast_natCast, mul_one] at h2
    rw [h2, hperabs.intervalIntegral_add_eq a 0]
    simp
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact key a b h
  · rw [intervalIntegral.integral_symm, abs_neg, abs_of_nonpos (sub_nonpos.2 h), neg_sub]
    exact key b a h



theorem integral_haar1 {F : Torus 1 → ℝ} (hF : AEStronglyMeasurable F (haar 1)) :
    ∫ x, F x ∂haar 1 = ∫ t in (0:ℝ)..1, F (lift1 t) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  rw [haar1_eq_map] at hF ⊢
  exact integral_map continuous_lift1.aemeasurable hF

theorem integrable_haar1_iff {F : Torus 1 → ℝ} (hF : AEStronglyMeasurable F (haar 1)) :
    Integrable F (haar 1) ↔ IntegrableOn (fun t => F (lift1 t)) (Ioc (0:ℝ) 1) := by
  rw [haar1_eq_map] at hF ⊢
  exact (integrable_map_measure hF continuous_lift1.aemeasurable).symm.symm

theorem smooth_hasDerivAt {v : Torus 1 → ℝ} (hv : IsSmoothPeriodic v) (t : ℝ) :
    HasDerivAt (fun t => v (lift1 t)) (smoothGrad v (lift1 t) 0) t := by
  have hd : DifferentiableAt ℝ (v ∘ torusLift) (fun _ : Fin 1 => t) :=
    (hv.differentiable (by norm_num)) _
  have h : HasDerivAt (fun t : ℝ => (fun _ : Fin 1 => t)) (fun _ : Fin 1 => (1:ℝ)) t :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id t
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t h
  have e : (fun _ : Fin 1 => (1:ℝ)) = Pi.single 0 1 := by
    funext i; fin_cases i; simp
  rw [e] at h2
  have e2 : smoothGrad v (lift1 t) 0 = fderiv ℝ (v ∘ torusLift) (fun _ : Fin 1 => t) (Pi.single 0 1) :=
    congrFun (coordPartial_comp_torusLift 0 v) (fun _ => t)
  rw [e2]
  exact h2

theorem smooth_periodic {v : Torus 1 → ℝ} (t : ℝ) : v (lift1 (t + 1)) = v (lift1 t) := by
  rw [lift1_add_one]



theorem integral_abs_le_eLpNorm {f : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) :
    ∫ x, |f x| ∂haar 1 ≤ (eLpNorm f 2 (haar 1)).toReal := by
  have h1 : ∫ x, |f x| ∂haar 1 = (eLpNorm f 1 (haar 1)).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable]
    · simp only [Real.norm_eq_abs]
    · exact hf.aestronglyMeasurable
  rw [h1]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

theorem lift1_eq_iff {a b : ℝ} (h : lift1 a = lift1 b) : ∃ k : ℤ, a = b + k := by
  have h0 : lift1 (a - b) = 0 := by rw [lift1_sub, h, sub_self]
  have h1 := congrFun h0 0
  have h2 : (((a - b : ℝ)) : AddCircle (1:ℝ)) = 0 := h1
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).1 h2
  refine ⟨n, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hn
  linarith

theorem lift1_coord (y : Fin 1 → ℝ) : torusLift y = lift1 (y 0) := by
  unfold lift1
  congr 1
  funext i
  rw [Subsingleton.elim i 0]

theorem memLp_coord {g : Torus 1 → Tangent 1} (hg : MemLp g 2 (haar 1)) :
    MemLp (fun x => g x 0) 2 (haar 1) := by
  refine hg.of_le ?_ (Eventually.of_forall fun x => ?_)
  · exact (continuous_apply 0 |>.comp (PiLp.continuous_ofLp 2 _)).aestronglyMeasurable.comp_aemeasurable hg.aestronglyMeasurable.aemeasurable
  · simpa using PiLp.norm_apply_le (g x) 0



theorem integrable_of_cont {f : Torus 1 → ℝ} (hc : Continuous f) : Integrable f (haar 1) :=
  (memLp_two_of_continuous hc).integrable (by norm_num)

theorem sobolev1 {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (h : IsWeakGradient u g) :
    ∃ Ub : Torus 1 → ℝ, Continuous Ub ∧ Ub =ᵐ[haar 1] u ∧
      ∀ a b : ℝ, Ub (lift1 b) - Ub (lift1 a) = ∫ t in a..b, g (lift1 t) 0 := by
  obtain ⟨v, hvs, hvw, hv1, hv2⟩ := exists_smooth_tendsto_H1 h
  have hv2 := hv2 0
  set P : ℕ → ℝ → ℝ := fun n t => v n (lift1 t) with hP
  set P' : ℕ → ℝ → ℝ := fun n t => smoothGrad (v n) (lift1 t) 0 with hP'
  have hPd : ∀ n t, HasDerivAt (P n) (P' n t) t := fun n t => smooth_hasDerivAt (hvs n) t
  have hP'c : ∀ n, Continuous (P' n) := fun n =>
    ((hvs n).continuous_coordPartial 0).comp continuous_lift1
  have hPc : ∀ n, Continuous (P n) := fun n =>
    (hvs n).continuous_torus.comp continuous_lift1
  have hPper : ∀ n, Function.Periodic (P n) 1 := fun n t => by simp only [hP, lift1_add_one]
  have hP'per : ∀ n, Function.Periodic (P' n) 1 := fun n t => by simp only [hP', lift1_add_one]
  set A : ℕ → ℝ := fun n => (eLpNorm (v n - u) 2 (haar 1)).toReal with hA
  set B : ℕ → ℝ := fun n =>
    (eLpNorm (fun x => smoothGrad (v n) x 0 - g x 0) 2 (haar 1)).toReal with hB
  have hAt : Tendsto A atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hv1
    exact this
  have hBt : Tendsto B atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hv2
    exact this
  have hg0 : MemLp (fun x => g x 0) 2 (haar 1) := memLp_coord h.memLp_grad
  have hw : ∀ n, MemLp (fun x => smoothGrad (v n) x 0) 2 (haar 1) := fun n =>
    memLp_coord (hvw n).memLp_grad
  have hvm : ∀ n, MemLp (v n - u) 2 (haar 1) := fun n => (hvw n).memLp.sub h.memLp
  have hwm : ∀ n, MemLp (fun x => smoothGrad (v n) x 0 - g x 0) 2 (haar 1) := fun n =>
    (hw n).sub hg0
  have hA0 : ∀ n, 0 ≤ A n := fun n => ENNReal.toReal_nonneg
  have hB0 : ∀ n, 0 ≤ B n := fun n => ENNReal.toReal_nonneg
  -- L¹ bounds
  have hL1v : ∀ n, ∫ x, |v n x - u x| ∂haar 1 ≤ A n := fun n =>
    integral_abs_le_eLpNorm (hvm n)
  have hL1w : ∀ n, ∫ x, |smoothGrad (v n) x 0 - g x 0| ∂haar 1 ≤ B n := fun n =>
    integral_abs_le_eLpNorm (hwm n)
  -- difference bound
  have i1 : ∀ n, Integrable (fun x => |v n x - u x|) (haar 1) := fun n =>
    ((hvm n).integrable (by norm_num)).abs
  have i2 : ∀ n, Integrable (fun x => |smoothGrad (v n) x 0 - g x 0|) (haar 1) := fun n =>
    ((hwm n).integrable (by norm_num)).abs
  have hdiff : ∀ n m t, |P n t - P m t| ≤ (A n + B n) + (A m + B m) := by
    intro n m t
    have hs := sup_bound (p := fun t => P n t - P m t) (p' := fun t => P' n t - P' m t)
      (fun t => (hPd n t).sub (hPd m t)) ((hP'c n).sub (hP'c m))
      (fun t => by simp only [hPper n t, hPper m t]) t
    refine hs.trans ?_
    have c1 : Continuous fun x => |v n x - v m x| :=
      ((hvs n).continuous_torus.sub (hvs m).continuous_torus).abs
    have c2 : Continuous fun x => |smoothGrad (v n) x 0 - smoothGrad (v m) x 0| :=
      (((hvs n).continuous_coordPartial 0).sub ((hvs m).continuous_coordPartial 0)).abs
    have e1 : ∫ s in (0:ℝ)..1, |P n s - P m s| = ∫ x, |v n x - v m x| ∂haar 1 :=
      (integral_haar1 (F := fun x => |v n x - v m x|) c1.aestronglyMeasurable).symm
    have e2 : ∫ s in (0:ℝ)..1, |P' n s - P' m s| =
        ∫ x, |smoothGrad (v n) x 0 - smoothGrad (v m) x 0| ∂haar 1 :=
      (integral_haar1 (F := fun x => |smoothGrad (v n) x 0 - smoothGrad (v m) x 0|)
        c2.aestronglyMeasurable).symm
    rw [e1, e2]
    have b1 : ∫ x, |v n x - v m x| ∂haar 1 ≤ A n + A m := by
      calc _ ≤ ∫ x, (|v n x - u x| + |v m x - u x|) ∂haar 1 :=
            integral_mono (integrable_of_cont c1) ((i1 n).add (i1 m)) (fun x => by
              have := abs_sub_le (v n x) (u x) (v m x)
              simp only
              calc |v n x - v m x| ≤ |v n x - u x| + |u x - v m x| := this
                _ = _ := by rw [abs_sub_comm (u x) (v m x)])
        _ = ∫ x, |v n x - u x| ∂haar 1 + ∫ x, |v m x - u x| ∂haar 1 :=
            integral_add (i1 n) (i1 m)
        _ ≤ _ := add_le_add (hL1v n) (hL1v m)
    have b2 : ∫ x, |smoothGrad (v n) x 0 - smoothGrad (v m) x 0| ∂haar 1 ≤ B n + B m := by
      calc _ ≤ ∫ x, (|smoothGrad (v n) x 0 - g x 0| + |smoothGrad (v m) x 0 - g x 0|) ∂haar 1 :=
            integral_mono (integrable_of_cont c2) ((i2 n).add (i2 m)) (fun x => by
              have := abs_sub_le (smoothGrad (v n) x 0) (g x 0) (smoothGrad (v m) x 0)
              simp only
              calc _ ≤ |smoothGrad (v n) x 0 - g x 0| + |g x 0 - smoothGrad (v m) x 0| := this
                _ = _ := by rw [abs_sub_comm (g x 0) (smoothGrad (v m) x 0)])
        _ = ∫ x, |smoothGrad (v n) x 0 - g x 0| ∂haar 1 +
              ∫ x, |smoothGrad (v m) x 0 - g x 0| ∂haar 1 :=
            integral_add (i2 n) (i2 m)
        _ ≤ _ := add_le_add (hL1w n) (hL1w m)
    linarith
  -- pointwise limit
  have hCt : Tendsto (fun n => A n + B n) atTop (𝓝 0) := by simpa using hAt.add hBt
  have hcau : ∀ t, CauchySeq (fun n => P n t) := by
    intro t
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hCt) (ε / 2) (by linarith)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (hA0 m) (hB0 m))] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (hA0 n) (hB0 n))] at h2
    rw [Real.dist_eq]
    have := hdiff m n t
    linarith
  choose U hU using fun t => cauchySeq_tendsto_of_complete (hcau t)
  have hUb : ∀ n t, |P n t - U t| ≤ A n + B n := by
    intro n t
    have h1 : Tendsto (fun m => |P n t - P m t|) atTop (𝓝 |P n t - U t|) :=
      (tendsto_const_nhds.sub (hU t)).abs
    have h2 : Tendsto (fun m => (A n + B n) + (A m + B m)) atTop (𝓝 ((A n + B n) + 0)) :=
      tendsto_const_nhds.add hCt
    rw [add_zero] at h2
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun m => hdiff n m t)
  have hUper : Function.Periodic U 1 := by
    intro t
    exact tendsto_nhds_unique (hU (t + 1)) (by simpa [hPper _ t] using hU t)
  have hUunif : TendstoUniformly P U atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hCt) ε hε
    filter_upwards [eventually_ge_atTop N] with n hn t
    have h1 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg (hA0 n) (hB0 n))] at h1
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hUb n t) h1
  have hUc : Continuous U := hUunif.continuous (Eventually.of_forall hPc).frequently
  -- the representative
  set Ub : Torus 1 → ℝ := fun x => U (SharpLSI.secT x 0) with hUbdef
  have hUb_lift : ∀ t, Ub (lift1 t) = U t := by
    intro t
    have e : lift1 (SharpLSI.secT (lift1 t) 0) = lift1 t := by
      rw [← lift1_coord (SharpLSI.secT (lift1 t))]
      exact SharpLSI.liftT_secT _
    obtain ⟨k, hk⟩ := lift1_eq_iff e
    show U (SharpLSI.secT (lift1 t) 0) = U t
    rw [hk]
    have := (hUper.int_mul k) t
    simpa using this
  have hUbc : Continuous Ub := by
    refine continuous_of_comp_torusLift ?_
    have : Ub ∘ torusLift = fun y => U (y 0) := by
      funext y
      simp only [Function.comp, lift1_coord, hUb_lift]
    rw [this]
    exact hUc.comp (continuous_apply 0)
  have hvUb : ∀ n x, |v n x - Ub x| ≤ A n + B n := by
    intro n x
    obtain ⟨t, rfl⟩ := lift1_exists x
    rw [hUb_lift]
    exact hUb n t
  refine ⟨Ub, hUbc, ?_, ?_⟩
  · -- a.e. equality
    have hint : Integrable (fun x => |u x - Ub x|) (haar 1) :=
      (h.memLp.sub (memLp_two_of_continuous hUbc)).integrable (by norm_num) |>.abs
    have hle : ∀ n, ∫ x, |u x - Ub x| ∂haar 1 ≤ A n + (A n + B n) := by
      intro n
      calc _ ≤ ∫ x, (|v n x - u x| + (A n + B n)) ∂haar 1 :=
            integral_mono hint ((i1 n).add (integrable_const _)) (fun x => by
              simp only
              calc |u x - Ub x| ≤ |u x - v n x| + |v n x - Ub x| := abs_sub_le _ _ _
                _ ≤ _ := by rw [abs_sub_comm (u x) (v n x)]; exact add_le_add le_rfl (hvUb n x))
        _ = ∫ x, |v n x - u x| ∂haar 1 + (A n + B n) := by
            rw [integral_add (i1 n) (integrable_const _)]; simp
        _ ≤ _ := add_le_add (hL1v n) le_rfl
    have hlim : Tendsto (fun n => A n + (A n + B n)) atTop (𝓝 0) := by
      simpa using hAt.add hCt
    have h0 : ∫ x, |u x - Ub x| ∂haar 1 ≤ 0 := ge_of_tendsto' hlim hle
    have h0' : ∫ x, |u x - Ub x| ∂haar 1 = 0 :=
      le_antisymm h0 (integral_nonneg fun x => abs_nonneg _)
    have := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg _) hint).1 h0'
    filter_upwards [this] with x hx
    have : |u x - Ub x| = 0 := hx
    have := abs_eq_zero.1 this
    linarith
  · -- FTC
    intro a b
    rw [hUb_lift, hUb_lift]
    have hG : Integrable (fun x => g x 0) (haar 1) := hg0.integrable (by norm_num)
    have hGi : IntervalIntegrable (fun t => g (lift1 t) 0) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact (integrable_haar1_iff hg0.aestronglyMeasurable).1 hG
    have hGper : Function.Periodic (fun t => g (lift1 t) 0) 1 := fun t => by
      simp only [lift1_add_one]
    have hGint := hGper.intervalIntegrable₀ one_ne_zero hGi
    have hk : ∀ n, |(∫ t in a..b, P' n t) - ∫ t in a..b, g (lift1 t) 0| ≤
        (⌈|b - a|⌉₊ : ℝ) * B n := by
      intro n
      have hfi : ∀ t₁ t₂, IntervalIntegrable (fun t => P' n t - g (lift1 t) 0) volume t₁ t₂ :=
        fun t₁ t₂ => ((hP'c n).intervalIntegrable _ _).sub (hGint _ _)
      have hfp : Function.Periodic (fun t => P' n t - g (lift1 t) 0) 1 := fun t => by
        simp only [hP', lift1_add_one]
      have := abs_integral_le_periodic hfp hfi a b
      rw [intervalIntegral.integral_sub ((hP'c n).intervalIntegrable _ _) (hGint _ _)] at this
      refine this.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have c := integral_haar1 (F := fun x => |smoothGrad (v n) x 0 - g x 0|)
        (i2 n).aestronglyMeasurable
      refine le_trans (le_of_eq ?_) (hL1w n)
      exact c.symm
    have hT1 : Tendsto (fun n => P n b - P n a) atTop (𝓝 (U b - U a)) :=
      (hU b).sub (hU a)
    have hT2 : Tendsto (fun n => ∫ t in a..b, P' n t) atTop (𝓝 (∫ t in a..b, g (lift1 t) 0)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hBt.const_mul (⌈|b - a|⌉₊ : ℝ))
      exact hk n
    have hE : ∀ n, P n b - P n a = ∫ t in a..b, P' n t := fun n =>
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hPd n t)
        ((hP'c n).intervalIntegrable _ _)).symm
    have hT1' : Tendsto (fun n => ∫ t in a..b, P' n t) atTop (𝓝 (U b - U a)) := by
      simpa only [hE] using hT1
    exact tendsto_nhds_unique hT1' hT2



/-- Regularity of the square root and the density of an absolute-admissible density. -/
theorem density_regular (ρ : AbsoluteDensity 1) :
    (∃ U : Torus 1 → ℝ, Continuous U ∧ (∃ M : ℝ, ∀ x, |U x| ≤ M) ∧ U =ᵐ[haar 1] ρ.sqrt ∧
      ∀ a b : ℝ, U (lift1 b) - U (lift1 a) =
        ∫ t in a..b, weakGradient ρ.sqrt ρ.sqrt_mem (lift1 t) 0) ∧
    MemLp ρ.density ⊤ (haar 1) ∧
    IsWeakGradient ρ.density (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  obtain ⟨U, hUc, hUae, hUf⟩ := sobolev1 hw
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (f := U) hUc.continuousOn
  have hM' : ∀ x, |U x| ≤ M := fun x => by simpa using hM x (mem_univ x)
  have hs : ∀ᵐ x ∂haar 1, |ρ.sqrt x| ≤ M := by
    filter_upwards [hUae] with x hx
    rw [← hx]; exact hM' x
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  have hdens : MemLp ρ.density ⊤ (haar 1) := by
    refine memLp_top_of_bound (C := M ^ 2) ?_ ?_
    · exact (ρ.memLp_sqrt.aestronglyMeasurable.pow 2)
    · filter_upwards [hs] with x hx
      simp only [AbsoluteDensity.density, Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hfac : MemLp (fun x => 2 * ρ.sqrt x) ⊤ (haar 1) := by
    refine memLp_top_of_bound (C := 2 * M) ?_ ?_
    · exact (ρ.memLp_sqrt.aestronglyMeasurable.const_mul 2)
    · filter_upwards [hs] with x hx
      simp only [Real.norm_eq_abs, abs_mul, abs_two]
      linarith
  have hfield : MemLp (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) 2 (haar 1) :=
    hfac.smul hw.memLp_grad
  refine ⟨⟨U, hUc, ⟨M, hM'⟩, hUae, hUf⟩, hdens, ?_⟩
  exact (density_gradient ρ).2 (hdens.mono_exponent le_top) hfield



theorem torusLift_add_secT {d : ℕ} (z : Fin d → ℝ) (y : Torus d) :
    torusLift (z + SharpLSI.secT y) = torusLift z + y := by
  have := SharpLSI.liftT_add z (SharpLSI.secT y)
  rw [SharpLSI.liftT_secT] at this
  exact this

theorem translate_comp {d : ℕ} (φ : Torus d → ℝ) (y : Torus d) :
    (fun x => φ (x + y)) ∘ torusLift = fun z => (φ ∘ torusLift) (z + SharpLSI.secT y) := by
  funext z
  simp only [Function.comp]
  rw [torusLift_add_secT]

theorem translate_smooth {d : ℕ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (y : Torus d) :
    IsSmoothPeriodic (fun x => φ (x + y)) := by
  unfold IsSmoothPeriodic
  rw [translate_comp]
  exact hφ.comp (contDiff_id.add contDiff_const)

theorem translate_coordPartial {d : ℕ} (φ : Torus d → ℝ) (j : Fin d) (y x : Torus d) :
    coordPartial j (fun x => φ (x + y)) x = coordPartial j φ (x + y) := by
  obtain ⟨z, rfl⟩ : ∃ z, x = torusLift z := ⟨SharpLSI.secT x, (SharpLSI.liftT_secT x).symm⟩
  have h1 := congrFun (coordPartial_comp_torusLift j (fun x => φ (x + y))) z
  have h2 := congrFun (coordPartial_comp_torusLift j φ) (z + SharpLSI.secT y)
  simp only [Function.comp] at h1 h2
  rw [h1, translate_comp, fderiv_comp_add_right]
  rw [torusLift_add_secT] at h2
  rw [h2]



/-- The convolution `(f * g)(x) = ∫ f(y) g(x - y) dy` on `𝕋¹`. -/
noncomputable def conv (f g : Torus 1 → ℝ) (x : Torus 1) : ℝ := ∫ y, f y * g (x - y) ∂haar 1

theorem swap_conv {f g ψ : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1))
    (hψ : Continuous ψ) :
    ∫ x, conv f g x * ψ x ∂haar 1 = ∫ y, f y * ∫ x, g (x - y) * ψ x ∂haar 1 ∂haar 1 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (f := ψ) hψ.continuousOn
  have hconv : Integrable (fun p : Torus 1 × Torus 1 => f p.2 * g (p.1 - p.2)) ((haar 1).prod (haar 1)) :=
    hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  have hint : Integrable (fun p : Torus 1 × Torus 1 => ψ p.1 * (f p.2 * g (p.1 - p.2)))
      ((haar 1).prod (haar 1)) := by
    refine hconv.bdd_mul (c := C) (hψ.comp continuous_fst).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => hC p.1 (mem_univ _)
  have e1 : ∀ x, conv f g x * ψ x = ∫ y, f y * g (x - y) * ψ x ∂haar 1 := fun x => by
    unfold conv; rw [integral_mul_const]
  simp_rw [e1]
  have hint' : Integrable (Function.uncurry fun x y => f y * g (x - y) * ψ x)
      ((haar 1).prod (haar 1)) := by
    refine hint.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]; ring
  rw [integral_integral_swap hint']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only; ring



theorem shift_integral (g ψ : Torus 1 → ℝ) (y : Torus 1) :
    ∫ x, g (x - y) * ψ x ∂haar 1 = ∫ z, g z * ψ (z + y) ∂haar 1 := by
  rw [← integral_add_right_eq_self (fun x => g (x - y) * ψ x) y]
  simp only [add_sub_cancel_right]

theorem conv_ibp {f g G : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hg : Integrable g (haar 1))
    (hG : Integrable G (haar 1))
    (hibp : ∀ φ : Torus 1 → ℝ, IsSmoothPeriodic φ →
      ∫ x, g x * coordPartial 0 φ x ∂haar 1 = -∫ x, G x * φ x ∂haar 1)
    (φ : Torus 1 → ℝ) (hφ : IsSmoothPeriodic φ) :
    ∫ x, conv f g x * coordPartial 0 φ x ∂haar 1 = -∫ x, conv f G x * φ x ∂haar 1 := by
  rw [swap_conv hf hg (hφ.continuous_coordPartial 0), swap_conv hf hG hφ.continuous_torus,
    ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [shift_integral, shift_integral, ← mul_neg]
  congr 1
  have := hibp (fun x => φ (x + y)) (translate_smooth hφ y)
  simp only [translate_coordPartial] at this
  exact this



theorem conv_continuous {f g : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hg : Continuous g) :
    Continuous (conv f g) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (f := g) hg.continuousOn
  have hgm : ∀ x, Continuous fun y => g (x - y) := fun x =>
    hg.comp (continuous_const.sub continuous_id)
  refine continuous_of_dominated (bound := fun y => |f y| * C) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact hf.aestronglyMeasurable.mul (hgm x).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by simpa using hC (x - y) (mem_univ _)) (abs_nonneg _)
  · exact hf.abs.mul_const C
  · exact Eventually.of_forall fun y =>
      continuous_const.mul (hg.comp (continuous_id.sub continuous_const))

theorem cs_sq {a b : Torus 1 → ℝ} (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1)) :
    (∫ x, a x * b x ∂haar 1) ^ 2 ≤ (∫ x, a x ^ 2 ∂haar 1) * ∫ x, b x ^ 2 ∂haar 1 := by
  have h1 : Integrable (fun x => a x ^ 2) (haar 1) := ha.integrable_sq
  have h2 : Integrable (fun x => b x ^ 2) (haar 1) := hb.integrable_sq
  have h3 : Integrable (fun x => a x * b x) (haar 1) := ha.integrable_mul hb
  have key : ∀ t : ℝ, 0 ≤ (∫ x, a x ^ 2 ∂haar 1) * t * t + (-2 * ∫ x, a x * b x ∂haar 1) * t +
      ∫ x, b x ^ 2 ∂haar 1 := by
    intro t
    have : ∫ x, (t * a x - b x) ^ 2 ∂haar 1 =
        (∫ x, a x ^ 2 ∂haar 1) * t * t + (-2 * ∫ x, a x * b x ∂haar 1) * t +
          ∫ x, b x ^ 2 ∂haar 1 := by
      have e : ∀ x, (t * a x - b x) ^ 2 = (t * t) * a x ^ 2 + (-2 * t) * (a x * b x) + b x ^ 2 := by
        intro x; ring
      simp_rw [e]
      have i1 := h1.const_mul (t * t)
      have i2 := h3.const_mul (-2 * t)
      have i12 := i1.add i2
      have s1 : ∫ x, ((t * t) * a x ^ 2 + (-2 * t) * (a x * b x) + b x ^ 2) ∂haar 1 =
          ∫ x, (((fun x => (t * t) * a x ^ 2) + (fun x => (-2 * t) * (a x * b x))) x + b x ^ 2) ∂haar 1 := rfl
      rw [s1, integral_add i12 h2, Pi.add_def, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← this]
    exact integral_nonneg fun x => sq_nonneg _
  have key' : ∀ t : ℝ, 0 ≤ (∫ x, a x ^ 2 ∂haar 1) * (t * t) + (-2 * ∫ x, a x * b x ∂haar 1) * t +
      ∫ x, b x ^ 2 ∂haar 1 := fun t => by have := key t; linarith
  have := discrim_le_zero key'
  unfold discrim at this
  nlinarith

theorem abs_integral_mul_le {a b : Torus 1 → ℝ} (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1)) :
    |∫ x, a x * b x ∂haar 1| ≤
      Real.sqrt (∫ x, a x ^ 2 ∂haar 1) * Real.sqrt (∫ x, b x ^ 2 ∂haar 1) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (cs_sq ha hb)

theorem memLp_sub_left {g : Torus 1 → ℝ} (hg : MemLp g 2 (haar 1)) (x : Torus 1) :
    MemLp (fun y => g (x - y)) 2 (haar 1) :=
  hg.comp_measurePreserving (Measure.measurePreserving_sub_left (haar 1) x)

theorem integral_sq_sub_left (g : Torus 1 → ℝ) (x : Torus 1) :
    ∫ y, g (x - y) ^ 2 ∂haar 1 = ∫ y, g y ^ 2 ∂haar 1 :=
  integral_sub_left_eq_self (fun y => g y ^ 2) (haar 1) x

theorem conv_bound {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (hg : MemLp g 2 (haar 1))
    (x : Torus 1) :
    |conv f g x| ≤ Real.sqrt (∫ y, f y ^ 2 ∂haar 1) * Real.sqrt (∫ y, g y ^ 2 ∂haar 1) := by
  have := abs_integral_mul_le hf (memLp_sub_left hg x)
  rw [integral_sq_sub_left] at this
  exact this



theorem conv_comm (f g : Torus 1 → ℝ) (x : Torus 1) : conv f g x = conv g f x := by
  unfold conv
  rw [← integral_sub_left_eq_self (fun y => f y * g (x - y)) (haar 1) x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show f (x - y) * g (x - (x - y)) = g y * f (x - y)
  rw [sub_sub_cancel, mul_comm]

theorem memLp_of_cont {E : Type*} [NormedAddCommGroup E] {f : Torus 1 → E} (hf : Continuous f)
    (p : ℝ≥0∞) : MemLp f p (haar 1) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => hC x (mem_univ _))

theorem sqrt_integral_sq_le {h : Torus 1 → ℝ} (hh : MemLp h 2 (haar 1)) {ε : ℝ} (hε : 0 ≤ ε)
    (H : eLpNorm h 2 (haar 1) ≤ ENNReal.ofReal ε) : Real.sqrt (∫ y, h y ^ 2 ∂haar 1) ≤ ε := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at H
  rw [ENNReal.ofReal_le_ofReal_iff hε] at H
  have : (∫ y, ‖h y‖ ^ (ENNReal.toReal 2) ∂haar 1) = ∫ y, h y ^ 2 ∂haar 1 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [sq_abs]
  rw [this] at H
  simpa [Real.sqrt_eq_rpow] using H

theorem conv_continuous_L2 {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (hg : MemLp g 2 (haar 1)) :
    Continuous (conv f g) := by
  set C := Real.sqrt (∫ y, f y ^ 2 ∂haar 1) with hC
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hex : ∀ n : ℕ, ∃ h : Torus 1 → ℝ, eLpNorm (g - h) 2 (haar 1) ≤
      ENNReal.ofReal (1 / ((n + 1) * (C + 1))) ∧ Continuous h ∧ MemLp h 2 (haar 1) := by
    intro n
    have hpos : 0 < 1 / (((n : ℝ) + 1) * (C + 1)) := by positivity
    obtain ⟨h, -, h1, h2, h3⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
      (ε := ENNReal.ofReal (1 / ((n + 1) * (C + 1)))) (by simpa using hpos)
    exact ⟨h, h1, h2, h3⟩
  choose h hh1 hh2 hh3 using hex
  have hint : ∀ (k : Torus 1 → ℝ), MemLp k 2 (haar 1) → ∀ x,
      Integrable (fun y => f y * k (x - y)) (haar 1) := fun k hk x =>
    hf.integrable_mul (memLp_sub_left hk x)
  have hunif : TendstoUniformly (fun n => conv f (h n)) (conv f g) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hε)
    filter_upwards [hev] with n hn x
    have hsub : conv f g x - conv f (h n) x = conv f (g - h n) x := by
      unfold conv
      rw [← integral_sub (hint g hg x) (hint (h n) (hh3 n) x)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [mul_sub]
    have hb := conv_bound hf (hg.sub (hh3 n)) x
    have hs := sqrt_integral_sq_le (hg.sub (hh3 n)) (by positivity) (hh1 n)
    rw [Real.dist_eq, hsub]
    have h3 : C * Real.sqrt (∫ y, (g - h n) y ^ 2 ∂haar 1) ≤ 1 / ((n : ℝ) + 1) := by
      calc C * Real.sqrt (∫ y, (g - h n) y ^ 2 ∂haar 1)
          ≤ C * (1 / (((n : ℝ) + 1) * (C + 1))) := mul_le_mul_of_nonneg_left hs hC0
        _ = (C / (C + 1)) * (1 / ((n : ℝ) + 1)) := by field_simp
        _ ≤ 1 * (1 / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).2 (by linarith))
              (by positivity)
        _ = 1 / ((n : ℝ) + 1) := one_mul _
    exact lt_of_le_of_lt (hb.trans h3) hn
  exact hunif.continuous (Eventually.of_forall fun n =>
    conv_continuous (hf.integrable (by norm_num)) (hh2 n)).frequently



open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model

theorem memLp_density_two (ρ : AbsoluteDensity 1) : MemLp ρ.density 2 (haar 1) :=
  (density_regular ρ).2.1.mono_exponent le_top

theorem continuous_driftField (ρ : AbsoluteDensity 1) : Continuous (conv dR ρ.density) :=
  conv_continuous_L2 memLp_dR (memLp_density_two ρ)

theorem continuous_single_comp {c : Torus 1 → ℝ} (hc : Continuous c) :
    Continuous (fun x => (EuclideanSpace.single (0 : Fin 1) (c x) : Tangent 1)) := by
  let L : ℝ →ₗ[ℝ] Tangent 1 :=
    { toFun := fun a => EuclideanSpace.single (0 : Fin 1) a
      map_add' := fun a b => by
        ext i; simp [PiLp.single_apply]
        split_ifs <;> simp
      map_smul' := fun r a => by
        ext i; simp [PiLp.single_apply] }
  exact L.continuous_of_finiteDimensional.comp hc

theorem potential_eq (ρ : AbsoluteDensity 1) (x : Torus 1) :
    interactionPotential positiveH1 ρ x = kappa * (conv ρ.density R x - A) := by
  rw [interactionPotential_eq]
  have hi : Integrable (fun y => ρ.density y * R (x - y)) (haar 1) :=
    (memLp_density_two ρ).integrable_mul
      (memLp_sub_left (memLp_of_cont continuous_R 2) x)
  have e : ∀ y, ρ.density y * positiveH1.W x y =
      kappa * (ρ.density y * R (x - y)) - kappa * A * ρ.density y := fun y => by
    show ρ.density y * (kappa * (R (x - y) - A)) = _
    ring
  simp_rw [e]
  rw [integral_sub (hi.const_mul _) (ρ.integrable_density.const_mul _), integral_const_mul,
    integral_const_mul, ρ.integral_density]
  show (0 : ℝ) + _ = _
  unfold conv
  ring

theorem integral_coordPartial_zero {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, coordPartial 0 φ x ∂haar 1 = 0 := by
  have h := (isWeakGradient_const (d := 1) 1).ibp φ hφ 0
  simpa using h

theorem weak_gradient_R_zero {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, R x * coordPartial 0 φ x ∂haar 1 = -∫ x, dR x * φ x ∂haar 1 := by
  have h := weak_gradient_R.ibp φ hφ 0
  simpa using h

theorem potential_ibp (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, interactionPotential positiveH1 ρ x * coordPartial 0 φ x ∂haar 1 =
      -∫ x, kappa * conv dR ρ.density x * φ x ∂haar 1 := by
  have hc1 : Continuous (conv ρ.density R) := conv_continuous ρ.integrable_density continuous_R
  have hd := hφ.continuous_coordPartial 0
  have i1 : Integrable (fun x => conv ρ.density R x * coordPartial 0 φ x) (haar 1) :=
    integrable_of_cont (hc1.mul hd)
  have i2 : Integrable (fun x => coordPartial 0 φ x) (haar 1) := integrable_of_cont hd
  have key := conv_ibp (f := ρ.density) (g := R) (G := dR) ρ.integrable_density
    (integrable_of_cont continuous_R) ((memLp_dR).integrable (by norm_num))
    (fun ψ hψ => weak_gradient_R_zero hψ) φ hφ
  simp_rw [potential_eq]
  have e : ∀ x, kappa * (conv ρ.density R x - A) * coordPartial 0 φ x =
      kappa * (conv ρ.density R x * coordPartial 0 φ x) - kappa * A * coordPartial 0 φ x :=
    fun x => by ring
  simp_rw [e]
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_coordPartial_zero hφ, key]
  have : ∀ x, conv ρ.density dR x = conv dR ρ.density x := fun x => conv_comm _ _ _
  simp_rw [this]
  have h2 : ∫ x, kappa * conv dR ρ.density x * φ x ∂haar 1 =
      kappa * ∫ x, conv dR ρ.density x * φ x ∂haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [h2]
  ring

/-- The actual drift of the positive `H¹` model: `κ R′ * ρ` as a vector field on `𝕋¹`. -/
noncomputable def positiveH1Drift : AbsoluteDrift positiveH1 where
  force ρ x := EuclideanSpace.single (0 : Fin 1) (kappa * conv dR ρ.density x)
  measurable_force ρ :=
    (continuous_single_comp (continuous_const.mul (continuous_driftField ρ))).measurable
  weak_gradient ρ := by
    have hpc : Continuous (interactionPotential positiveH1 ρ) := by
      have : interactionPotential positiveH1 ρ = fun x => kappa * (conv ρ.density R x - A) :=
        funext (potential_eq ρ)
      rw [this]
      exact continuous_const.mul
        ((conv_continuous ρ.integrable_density continuous_R).sub continuous_const)
    refine ⟨memLp_of_cont hpc 1,
      memLp_of_cont (continuous_single_comp (continuous_const.mul (continuous_driftField ρ))) 1,
      fun φ hφ j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simpa using potential_ibp ρ hφ



open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model

/-- The derivative `ρ′ = 2 u u′` of the density `ρ = u²`, as a scalar function on `𝕋¹`. -/
noncomputable def densityDeriv (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  2 * ρ.sqrt x * weakGradient ρ.sqrt ρ.sqrt_mem x 0

theorem memLp_densityDeriv (ρ : AbsoluteDensity 1) : MemLp (densityDeriv ρ) 2 (haar 1) := by
  have h := memLp_coord_of_memLp (density_regular ρ).2.2.memLp_grad 0
  have h2 : MemLp (fun x => 2 * ρ.sqrt x * weakGradient ρ.sqrt ρ.sqrt_mem x 0) 2 (haar 1) := by
    simpa using h
  exact h2

theorem density_ibp (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    ∫ x, ρ.density x * coordPartial 0 φ x ∂haar 1 = -∫ x, densityDeriv ρ x * φ x ∂haar 1 := by
  have h := (density_regular ρ).2.2.ibp φ hφ 0
  simpa [densityDeriv] using h

theorem isWeakGradient_driftField (ρ : AbsoluteDensity 1) :
    IsWeakGradient (conv dR ρ.density)
      (fun x => (EuclideanSpace.single (0 : Fin 1) (conv dR (densityDeriv ρ) x) : Tangent 1)) := by
  have hDc : Continuous (conv dR (densityDeriv ρ)) :=
    conv_continuous_L2 memLp_dR (memLp_densityDeriv ρ)
  refine ⟨memLp_of_cont (continuous_driftField ρ) 2,
    memLp_of_cont (continuous_single_comp hDc) 2, fun φ hφ j => ?_⟩
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  have key := conv_ibp (f := dR) (g := ρ.density) (G := densityDeriv ρ)
    (memLp_dR.integrable (by norm_num)) ρ.integrable_density
    ((memLp_densityDeriv ρ).integrable (by norm_num))
    (fun ψ hψ => density_ibp ρ hψ) φ hφ
  simpa using key

theorem driftField_c1 (ρ : AbsoluteDensity 1) :
    ContDiff ℝ 1 (fun t : ℝ => conv dR ρ.density (lift1 t)) ∧
      ∀ t : ℝ, HasDerivAt (fun t : ℝ => conv dR ρ.density (lift1 t))
        (conv dR (densityDeriv ρ) (lift1 t)) t := by
  have hDc : Continuous (conv dR (densityDeriv ρ)) :=
    conv_continuous_L2 memLp_dR (memLp_densityDeriv ρ)
  obtain ⟨Ub, hUc, hUae, hFTC⟩ := sobolev1 (isWeakGradient_driftField ρ)
  have hUeq : Ub = conv dR ρ.density :=
    (Continuous.ae_eq_iff_eq (haar 1) hUc (continuous_driftField ρ)).1 hUae
  subst hUeq
  have hD : Continuous fun s : ℝ => conv dR (densityDeriv ρ) (lift1 s) :=
    hDc.comp continuous_lift1
  have hrepr : ∀ t : ℝ, conv dR ρ.density (lift1 t) = conv dR ρ.density (lift1 0) +
      ∫ s in (0 : ℝ)..t, conv dR (densityDeriv ρ) (lift1 s) := by
    intro t
    have := hFTC 0 t
    simp at this
    linarith
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => conv dR ρ.density (lift1 t))
      (conv dR (densityDeriv ρ) (lift1 t)) t := by
    intro t
    have h1 := (hD.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (conv dR ρ.density (lift1 0))
    exact h1.congr_of_eventuallyEq (Eventually.of_forall fun s => hrepr s)
  refine ⟨?_, hderiv⟩
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hderiv t).differentiableAt, ?_⟩
  have : deriv (fun t : ℝ => conv dR ρ.density (lift1 t)) =
      fun t => conv dR (densityDeriv ρ) (lift1 t) := funext fun t => (hderiv t).deriv
  rw [this]
  exact hD



open DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model

theorem drift_bound (ρ : AbsoluteDensity 1) (x : Torus 1) :
    ‖positiveH1Drift.force ρ x‖ ≤
      kappa * (Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) * Real.sqrt (∫ y, ρ.density y ^ 2 ∂haar 1)) := by
  show ‖(EuclideanSpace.single (0 : Fin 1) (kappa * conv dR ρ.density x) : Tangent 1)‖ ≤ _
  rw [PiLp.norm_single, Real.norm_eq_abs, abs_mul, abs_of_pos kappa_pos]
  exact mul_le_mul_of_nonneg_left (conv_bound memLp_dR (memLp_density_two ρ) x) kappa_pos.le

theorem continuous_drift (ρ : AbsoluteDensity 1) : Continuous (positiveH1Drift.force ρ) :=
  continuous_single_comp (continuous_const.mul (continuous_driftField ρ))

theorem score_memLp (ρ σ : AbsoluteDensity 1) (a b : ℝ) :
    MemLp (fun x => a • weakGradient ρ.sqrt ρ.sqrt_mem x +
      (b * ρ.sqrt x) • positiveH1Drift.force σ x) 2 (haar 1) := by
  have h1 : MemLp (fun x => a • weakGradient ρ.sqrt ρ.sqrt_mem x) 2 (haar 1) :=
    (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad.const_smul a
  have h2 : MemLp (fun x => b * ρ.sqrt x) 2 (haar 1) := ρ.memLp_sqrt.const_mul b
  have h3 : MemLp (positiveH1Drift.force σ) ⊤ (haar 1) := memLp_of_cont (continuous_drift σ) _
  exact h1.add (h2.smul h3)

/-- Regularity package for one absolute-admissible density `ρ = u²`. -/
def AdmissibleRegularity (ρ : AbsoluteDensity 1) : Prop :=
  (∃ U : Torus 1 → ℝ, Continuous U ∧ (∃ M : ℝ, ∀ x, |U x| ≤ M) ∧ U =ᵐ[haar 1] ρ.sqrt ∧
      ∀ a b : ℝ, U (lift1 b) - U (lift1 a) =
        ∫ t in a..b, weakGradient ρ.sqrt ρ.sqrt_mem (lift1 t) 0) ∧
    (ρ.density = fun x => ρ.sqrt x ^ 2) ∧
    MemLp ρ.density ⊤ (haar 1) ∧
    IsWeakGradient ρ.density (fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x) ∧
    (∀ x, (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x 0 = densityDeriv ρ x) ∧
    MemLp (densityDeriv ρ) 2 (haar 1) ∧
    Continuous (positiveH1Drift.force ρ) ∧
    (∀ x, positiveH1Drift.force ρ x =
      EuclideanSpace.single (0 : Fin 1) (kappa * ∫ y, dR y * ρ.density (x - y) ∂haar 1)) ∧
    (∀ x, ‖positiveH1Drift.force ρ x‖ ≤
      kappa * (Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) * Real.sqrt (∫ y, ρ.density y ^ 2 ∂haar 1))) ∧
    ContDiff ℝ 1 (fun t : ℝ => conv dR ρ.density (lift1 t)) ∧
    ∀ t : ℝ, HasDerivAt (fun t : ℝ => conv dR ρ.density (lift1 t))
      (conv dR (densityDeriv ρ) (lift1 t)) t

theorem admissibleRegularity (ρ : AbsoluteDensity 1) : AdmissibleRegularity ρ := by
  obtain ⟨h1, h2, h3⟩ := density_regular ρ
  exact ⟨h1, rfl, h2, h3, fun x => by simp [densityDeriv, mul_assoc], memLp_densityDeriv ρ,
    continuous_drift ρ, fun x => rfl, drift_bound ρ, (driftField_c1 ρ).1, (driftField_c1 ρ).2⟩

/-- **H1007.** Regularity of admissible densities and the convolution force of the positive `H¹`
model. -/
theorem admissible_density_regularity_and_convolution_force :
    (∀ ρ : AbsoluteDensity 1, AdmissibleRegularity ρ) ∧
    (∀ F : SpeciesFamily 1, AdmissibleRegularity (barycenter F) ∧
      (barycenter F).sqrt = F.barycenterSqrt) ∧
    (∀ (ρ σ : AbsoluteDensity 1) (a b : ℝ),
      MemLp (fun x => a • weakGradient ρ.sqrt ρ.sqrt_mem x +
        (b * ρ.sqrt x) • positiveH1Drift.force σ x) 2 (haar 1)) ∧
    (∀ (F : SpeciesFamily 1) (s : Fin F.count) (a b : ℝ),
      MemLp (fun x => a • F.sqrtGradient s x +
        (b * (F.density s).sqrt x) • positiveH1Drift.force (barycenter F) x) 2 (haar 1)) ∧
    (∀ (b : AbsoluteDrift positiveH1) (ρ : AbsoluteDensity 1),
      b.force ρ =ᵐ[haar 1] positiveH1Drift.force ρ) :=
  ⟨admissibleRegularity, fun _ => ⟨admissibleRegularity _, rfl⟩, score_memLp,
    fun F s a b => score_memLp (F.density s) (barycenter F) a b,
    fun b ρ => absoluteDrift_unique b positiveH1Drift ρ⟩


/-! ### H1008: Fourier free energy and Haar equilibrium -/

/-- The Fourier coefficient `ν̂(n) = ∫ e^{-2π i n x} dν(x)` of a measure on `𝕋`. -/
noncomputable def measureFourier (ν : Measure (Torus 1)) (n : ℕ) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-freq n) x ∂ν

theorem mFourier_sub_apply (k : Fin 1 → ℤ) (x y : Torus 1) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * (starRingEnd ℂ) (UnitAddTorus.mFourier k y) := by
  rw [← UnitAddTorus.mFourier_neg]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.sub_apply, Pi.neg_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sub_eq_add_neg, fourier_neg, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul, smul_neg, fourier_neg', fourier_apply]
  rfl

theorem integrable_mFourier_prob (ν : ProbabilityMeasure (Torus 1)) (j : Fin 1 → ℤ) :
    Integrable (UnitAddTorus.mFourier j) (ν : Measure (Torus 1)) :=
  (UnitAddTorus.mFourier j).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem norm_measureFourier_le (ν : ProbabilityMeasure (Torus 1)) (n : ℕ) :
    ‖measureFourier ν n‖ ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus 1)))
    (f := fun x => UnitAddTorus.mFourier (-freq n) x) (C := 1)
    (Filter.Eventually.of_forall fun x => (norm_mFourier_apply _ x).le)
  simpa [measureFourier] using this

theorem integral_cosMode_sub (ν : ProbabilityMeasure (Torus 1)) (n : ℕ) :
    ∫ p : Torus 1 × Torus 1, cosMode n (p.1 - p.2)
      ∂((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) = ‖measureFourier ν n‖ ^ 2 := by
  set μ : Measure (Torus 1) := (ν : Measure (Torus 1)) with hμ
  have hint : Integrable (fun p : Torus 1 × Torus 1 =>
      UnitAddTorus.mFourier (freq n) (p.1 - p.2)) (μ.prod μ) := by
    have : Continuous fun p : Torus 1 × Torus 1 =>
        UnitAddTorus.mFourier (freq n) (p.1 - p.2) :=
      (UnitAddTorus.mFourier (freq n)).continuous.comp (continuous_fst.sub continuous_snd)
    exact this.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ p : Torus 1 × Torus 1, cosMode n (p.1 - p.2) ∂(μ.prod μ) =
      (∫ p : Torus 1 × Torus 1, UnitAddTorus.mFourier (freq n) (p.1 - p.2) ∂(μ.prod μ)).re := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    exact this
  have hm : measureFourier ν n = (starRingEnd ℂ) (∫ x, UnitAddTorus.mFourier (freq n) x ∂μ) := by
    unfold measureFourier
    rw [← integral_conj]
    simp_rw [UnitAddTorus.mFourier_neg]
    rfl
  have h2 : ∫ p : Torus 1 × Torus 1, UnitAddTorus.mFourier (freq n) (p.1 - p.2) ∂(μ.prod μ) =
      (∫ x, UnitAddTorus.mFourier (freq n) x ∂μ) * measureFourier ν n := by
    simp_rw [mFourier_sub_apply]
    rw [integral_prod_mul (fun x => UnitAddTorus.mFourier (freq n) x)
      (fun y => (starRingEnd ℂ) (UnitAddTorus.mFourier (freq n) y)), integral_conj]
    rw [hm]
  rw [h1, h2, hm, mul_comm, Complex.conj_mul', ]
  rw [RCLike.norm_conj, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem summable_fourierEnergy (ν : ProbabilityMeasure (Torus 1)) :
    Summable fun n : ℕ => a n * ‖measureFourier ν n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (a_nonneg n) (sq_nonneg _)) (fun n => ?_)
    a_summable
  have h := norm_measureFourier_le ν n
  have h0 := norm_nonneg (measureFourier ν n)
  calc a n * ‖measureFourier ν n‖ ^ 2 ≤ a n * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (a_nonneg n)
    _ = a n := mul_one _

theorem integral_R_sub (ν : ProbabilityMeasure (Torus 1)) :
    ∫ p : Torus 1 × Torus 1, R (p.1 - p.2)
      ∂((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) =
      ∑' n : ℕ, a n * ‖measureFourier ν n‖ ^ 2 := by
  set μ : Measure (Torus 1) := (ν : Measure (Torus 1)) with hμ
  have hcont : ∀ n, Continuous fun p : Torus 1 × Torus 1 => a n * cosMode n (p.1 - p.2) :=
    fun n => continuous_const.mul ((continuous_cosMode n).comp (continuous_fst.sub continuous_snd))
  have hF : ∀ n, Integrable (fun p : Torus 1 × Torus 1 => a n * cosMode n (p.1 - p.2))
      (μ.prod μ) := fun n =>
    (hcont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsum : Summable fun n => ∫ p : Torus 1 × Torus 1, ‖a n * cosMode n (p.1 - p.2)‖ ∂(μ.prod μ) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _)
      (fun n => ?_) a_summable
    have := norm_integral_le_of_norm_le_const (μ := μ.prod μ)
      (f := fun p : Torus 1 × Torus 1 => ‖a n * cosMode n (p.1 - p.2)‖) (C := a n)
      (Filter.Eventually.of_forall fun p => by
        simpa using term_abs_le n (p.1 - p.2))
    refine le_trans (le_abs_self _) ?_
    simpa [Real.norm_eq_abs] using this
  have := integral_tsum_of_summable_integral_norm hF hsum
  have e1 : ∀ p : Torus 1 × Torus 1, R (p.1 - p.2) = ∑' n, a n * cosMode n (p.1 - p.2) :=
    fun p => rfl
  simp_rw [e1]
  rw [← this]
  refine tsum_congr fun n => ?_
  rw [integral_const_mul, integral_cosMode_sub]

/-- The Fourier energy `Σ_{n≥2} a_n |ν̂(n)|²` (the terms with `n < 2` vanish since `a n = 0`). -/
noncomputable def fourierEnergy (ν : ProbabilityMeasure (Torus 1)) : ℝ :=
  ∑' n : ℕ, a n * ‖measureFourier ν n‖ ^ 2

theorem fourierEnergy_nonneg (ν : ProbabilityMeasure (Torus 1)) : 0 ≤ fourierEnergy ν :=
  tsum_nonneg fun n => mul_nonneg (a_nonneg n) (sq_nonneg _)

theorem interactionEnergy_positiveH1 (ν : ProbabilityMeasure (Torus 1)) :
    interactionEnergy positiveH1 ν = kappa * (fourierEnergy ν - A) := by
  have hc : Continuous fun p : Torus 1 × Torus 1 => R (p.1 - p.2) :=
    continuous_R.comp (continuous_fst.sub continuous_snd)
  have hi : Integrable (fun p : Torus 1 × Torus 1 => R (p.1 - p.2))
      ((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  show ∫ p : Torus 1 × Torus 1, kappa * (R (p.1 - p.2) - A) ∂_ = _
  rw [integral_const_mul, integral_sub hi (integrable_const _), integral_R_sub]
  simp [fourierEnergy]

theorem freeEnergy_positiveH1_eq (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy positiveH1 ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) +
        ((-(kappa * A / 2) + kappa / 2 * fourierEnergy ν : ℝ) : EReal) := by
  unfold freeEnergy
  have hV : potentialEnergy positiveH1 ν = 0 := by simp [potentialEnergy, positiveH1]
  rw [hV, interactionEnergy_positiveH1, add_assoc, ← EReal.coe_add]
  congr 2
  ring

theorem ereal_add_sub_aux {x : EReal} (hx : x ≠ ⊥) (c d : ℝ) :
    x + (c : EReal) - (d : EReal) = x + ((c - d : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => rw [EReal.top_add_coe, EReal.top_sub_coe, EReal.top_add_coe]
  | coe r => norm_cast; ring

theorem freeEnergy_sub_minimum_aux (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy positiveH1 ν - ((-(kappa * A / 2) : ℝ) : EReal) =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) +
        ((kappa / 2 * fourierEnergy ν : ℝ) : EReal) := by
  rw [freeEnergy_positiveH1_eq, ereal_add_sub_aux (EReal.coe_ennreal_ne_bot _)]
  congr 2
  ring

theorem fourierEnergy_haar : fourierEnergy (haarProbability 1) = 0 := by
  unfold fourierEnergy
  refine (tsum_congr fun n => ?_).trans tsum_zero
  by_cases hn : 2 ≤ n
  · have hne : -freq (n : ℤ) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [freq] at this
      omega
    have : measureFourier (haarProbability 1) n = 0 := by
      unfold measureFourier
      show ∫ x, UnitAddTorus.mFourier (-freq (n : ℤ)) x ∂haar 1 = 0
      rw [integral_mFourier]; simp [hne]
    rw [this]; simp
  · rw [a_zero_of_lt (by omega)]; simp

theorem freeEnergy_haar_value :
    freeEnergy positiveH1 (haarProbability 1) = ((-(kappa * A / 2) : ℝ) : EReal) := by
  rw [freeEnergy_positiveH1_eq, fourierEnergy_haar]
  show ((relativeEntropy (haar 1) (haar 1) : ℝ≥0∞) : EReal) + _ = _
  rw [relativeEntropy_self]
  simp

theorem freeEnergyMinimum_positiveH1 :
    freeEnergyMinimum positiveH1 = ((-(kappa * A / 2) : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf fun ν => ?_)
  · rw [← freeEnergy_haar_value]; exact iInf_le _ _
  · rw [freeEnergy_positiveH1_eq]
    have h0 : (0 : EReal) ≤ ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_nonneg _
    have hs : ((-(kappa * A / 2) : ℝ) : EReal) ≤
        ((-(kappa * A / 2) + kappa / 2 * fourierEnergy ν : ℝ) : EReal) := by
      have := fourierEnergy_nonneg ν
      have hk := kappa_pos
      exact_mod_cast (by nlinarith : -(kappa * A / 2) ≤ -(kappa * A / 2) + kappa / 2 * fourierEnergy ν)
    exact hs.trans (le_add_of_nonneg_left h0)

/-- **H1008.** Fourier free energy and Haar equilibrium for the positive `H¹` model, with
`ν̂(n) = ∫ e^{-2π i n x} dν` (`measureFourier`) and `G(ν) = F(ν) - F_*`. -/
theorem fourier_free_energy_and_haar_equilibrium :
    (∀ ν : ProbabilityMeasure (Torus 1),
      Summable (fun n : ℕ => a n * ‖measureFourier ν n‖ ^ 2) ∧
      freeEnergy positiveH1 ν =
        ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) +
          ((-(kappa * A / 2) + kappa / 2 * ∑' n : ℕ, a n * ‖measureFourier ν n‖ ^ 2 : ℝ) :
            EReal)) ∧
    freeEnergyMinimum positiveH1 = ((-(kappa * A / 2) : ℝ) : EReal) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy positiveH1 ν = freeEnergyMinimum positiveH1 ↔ ν = haarProbability 1) ∧
    (∀ ν : ProbabilityMeasure (Torus 1),
      freeEnergy positiveH1 ν - freeEnergyMinimum positiveH1 =
        ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) +
          ((kappa / 2 * ∑' n : ℕ, a n * ‖measureFourier ν n‖ ^ 2 : ℝ) : EReal) ∧
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) ≤
        freeEnergy positiveH1 ν - freeEnergyMinimum positiveH1) := by
  have hge : ∀ ν : ProbabilityMeasure (Torus 1),
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) ≤
        freeEnergy positiveH1 ν - freeEnergyMinimum positiveH1 := by
    intro ν
    rw [freeEnergyMinimum_positiveH1, freeEnergy_sub_minimum_aux]
    refine le_add_of_nonneg_right ?_
    have := fourierEnergy_nonneg ν
    have hk := kappa_pos
    exact_mod_cast (by positivity : 0 ≤ kappa / 2 * fourierEnergy ν)
  refine ⟨fun ν => ⟨summable_fourierEnergy ν, freeEnergy_positiveH1_eq ν⟩,
    freeEnergyMinimum_positiveH1, fun ν => ⟨fun h => ?_, fun h => ?_⟩,
    fun ν => ⟨by rw [freeEnergyMinimum_positiveH1]; exact freeEnergy_sub_minimum_aux ν, hge ν⟩⟩
  · have h1 := hge ν
    rw [h, freeEnergyMinimum_positiveH1, EReal.sub_self (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _)] at h1
    have h2 : relativeEntropy (ν : Measure (Torus 1)) (haar 1) ≤ 0 := by
      exact_mod_cast h1
    have h3 : relativeEntropy (ν : Measure (Torus 1)) (haar 1) = 0 := nonpos_iff_eq_zero.mp h2
    have h4 : (ν : Measure (Torus 1)) = haar 1 := relativeEntropy_zero_iff.mp h3
    exact Subtype.ext h4
  · rw [h, freeEnergyMinimum_positiveH1]
    exact freeEnergy_haar_value

/-! ### H1009: the density Hessian of the positive example at the Haar equilibrium -/

open DGPS

theorem integral_R_sub_left (x : Torus 1) : ∫ z, R (x - z) ∂haar 1 = 0 := by
  rw [integral_sub_left_eq_self (fun z => R z) (haar 1) x]
  exact integral_R

theorem interactionConvolution_positiveH1 (x : Torus 1) :
    interactionConvolution positiveH1 (haarProbability 1) x = -(kappa * A) := by
  unfold interactionConvolution
  show ∫ z, kappa * (R (x - z) - A) ∂haar 1 = _
  have hi : Integrable (fun z => R (x - z)) (haar 1) :=
    (continuous_R.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_const_mul, integral_sub hi (integrable_const _), integral_R_sub_left]
  simp

theorem meanInteraction_positiveH1 :
    meanInteraction positiveH1 (haarProbability 1) = -(kappa * A) := by
  unfold meanInteraction
  have h := integral_prod (μ := (haarProbability 1 : Measure (Torus 1)))
    (ν := (haarProbability 1 : Measure (Torus 1)))
    (f := fun p : Torus 1 × Torus 1 => positiveH1.W p.1 p.2) (integrable_W_prod positiveH1 (haarProbability 1))
  rw [h]
  have := interactionConvolution_positiveH1
  unfold interactionConvolution at this
  simp_rw [this]
  simp

theorem centeredKernel_positiveH1 (x y : Torus 1) :
    centeredKernel positiveH1 (haarProbability 1) x y = kappa * R (x - y) := by
  unfold centeredKernel
  rw [interactionConvolution_positiveH1, interactionConvolution_positiveH1,
    meanInteraction_positiveH1]
  show kappa * (R (x - y) - A) - _ - _ + _ = _
  ring


/-- The Fourier coefficient `ĥ(n) = ∫ e^{-2π i n x} h(x) dm` of a real `L²(m)` class. -/
noncomputable def lpFourier (h : Lp ℝ 2 (haar 1)) (n : ℕ) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-freq n) x * ((h x : ℝ) : ℂ) ∂haar 1

theorem integrable_lp_haar (h : Lp ℝ 2 (haar 1)) : Integrable h (haar 1) :=
  (Lp.memLp h).integrable (by norm_num)

theorem integral_cosMode_pair (g f : Lp ℝ 2 (haar 1)) (n : ℕ) :
    ∫ p : Torus 1 × Torus 1, cosMode n (p.1 - p.2) * (g p.1 * f p.2)
      ∂((haar 1).prod (haar 1)) = ((starRingEnd ℂ) (lpFourier g n) * lpFourier f n).re := by
  set G : Torus 1 → ℂ := fun x => UnitAddTorus.mFourier (freq n) x * ((g x : ℝ) : ℂ) with hG
  set F : Torus 1 → ℂ := fun y =>
    (starRingEnd ℂ) (UnitAddTorus.mFourier (freq n) y) * ((f y : ℝ) : ℂ) with hF
  have hGi : Integrable G (haar 1) :=
    integrable_mFourier_mul (integrable_lp_haar g) (freq n)
  have hFi : Integrable F (haar 1) := by
    have := integrable_mFourier_mul (integrable_lp_haar f) (-freq n)
    simpa [hF, UnitAddTorus.mFourier_neg] using this
  have e1 : (starRingEnd ℂ) (lpFourier g n) = ∫ x, G x ∂haar 1 := by
    unfold lpFourier
    rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [hG, UnitAddTorus.mFourier_neg]
  have e2 : lpFourier f n = ∫ x, F x ∂haar 1 := by
    unfold lpFourier
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [hF, UnitAddTorus.mFourier_neg]
  have hint : Integrable (fun p : Torus 1 × Torus 1 => G p.1 * F p.2) ((haar 1).prod (haar 1)) :=
    hGi.mul_prod hFi
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [e1, e2, ← integral_prod_mul G F, ← hre]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have : G p.1 * F p.2 = UnitAddTorus.mFourier (freq n) (p.1 - p.2) * ((g p.1 * f p.2 : ℝ) : ℂ) := by
    rw [mFourier_sub_apply]; simp [hG, hF]; ring
  show _ = (G p.1 * F p.2).re
  rw [this]
  simp only [Complex.re_mul_ofReal, cosMode]
  rfl


theorem integral_R_pair (g f : Lp ℝ 2 (haar 1)) :
    Summable (fun n : ℕ => a n * ((starRingEnd ℂ) (lpFourier g n) * lpFourier f n).re) ∧
    ∫ p : Torus 1 × Torus 1, R (p.1 - p.2) * (g p.1 * f p.2) ∂((haar 1).prod (haar 1)) =
      ∑' n : ℕ, a n * ((starRingEnd ℂ) (lpFourier g n) * lpFourier f n).re := by
  have hg := integrable_lp_haar g
  have hf := integrable_lp_haar f
  set F : ℕ → Torus 1 × Torus 1 → ℝ := fun n p =>
    a n * cosMode n (p.1 - p.2) * (g p.1 * f p.2) with hFdef
  have hFi : ∀ n, Integrable (F n) ((haar 1).prod (haar 1)) := fun n => by
    have := integrable_prod_cont_mul (haarProbability 1)
      (fun p : Torus 1 × Torus 1 => a n * cosMode n (p.1 - p.2))
      (continuous_const.mul ((continuous_cosMode n).comp (continuous_fst.sub continuous_snd)))
      hg hf
    change Integrable _ ((haar 1).prod (haar 1)) at this
    simpa [hFdef, mul_assoc] using this
  have hbound : ∀ n, ∫ p, ‖F n p‖ ∂((haar 1).prod (haar 1)) ≤
      a n * ((∫ x, ‖g x‖ ∂haar 1) * ∫ y, ‖f y‖ ∂haar 1) := by
    intro n
    have h1 : Integrable (fun p : Torus 1 × Torus 1 => a n * (‖g p.1‖ * ‖f p.2‖))
        ((haar 1).prod (haar 1)) := (hg.norm.mul_prod hf.norm).const_mul _
    calc ∫ p, ‖F n p‖ ∂((haar 1).prod (haar 1))
        ≤ ∫ p : Torus 1 × Torus 1, a n * (‖g p.1‖ * ‖f p.2‖) ∂((haar 1).prod (haar 1)) := by
          refine integral_mono (hFi n).norm h1 fun p => ?_
          have hc := cosMode_abs_le n (p.1 - p.2)
          have ha := a_nonneg n
          have h0 : 0 ≤ |g p.1| * |f p.2| := by positivity
          have e : ‖F n p‖ = a n * |cosMode n (p.1 - p.2)| * (|g p.1| * |f p.2|) := by
            simp only [hFdef, norm_mul, Real.norm_eq_abs, abs_of_nonneg ha]
          rw [e]
          calc a n * |cosMode n (p.1 - p.2)| * (|g p.1| * |f p.2|)
              ≤ a n * 1 * (|g p.1| * |f p.2|) := by gcongr
            _ = a n * (‖g p.1‖ * ‖f p.2‖) := by simp
      _ = _ := by
          rw [integral_const_mul, integral_prod_mul (fun x => ‖g x‖) (fun y => ‖f y‖)]
  have hsum : Summable fun n => ∫ p, ‖F n p‖ ∂((haar 1).prod (haar 1)) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun p => norm_nonneg _) hbound
      (a_summable.mul_right _)
  have hint : ∀ n, ∫ p, F n p ∂((haar 1).prod (haar 1)) =
      a n * ((starRingEnd ℂ) (lpFourier g n) * lpFourier f n).re := by
    intro n
    rw [← integral_cosMode_pair, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [hFdef]; ring
  have hsumm : Summable fun n : ℕ => a n * ((starRingEnd ℂ) (lpFourier g n) * lpFourier f n).re := by
    refine Summable.of_norm_bounded (a_summable.mul_right
      ((∫ x, ‖g x‖ ∂haar 1) * ∫ y, ‖f y‖ ∂haar 1)) fun n => ?_
    rw [← hint n]
    exact (norm_integral_le_integral_norm _).trans (hbound n)
  refine ⟨hsumm, ?_⟩
  have := integral_tsum_of_summable_integral_norm hFi hsum
  have e : ∀ p : Torus 1 × Torus 1, R (p.1 - p.2) * (g p.1 * f p.2) = ∑' n, F n p := by
    intro p
    unfold R
    rw [← tsum_mul_right]
  simp_rw [e]
  rw [← this]
  exact tsum_congr hint


theorem inner_densityHessian_bilinear (g f : centeredL2 (haarProbability 1)) :
    inner ℝ g (densityHessian positiveH1 (haarProbability 1) f) =
      inner ℝ g.1 f.1 + kappa * ∑' n : ℕ, a n *
        ((starRingEnd ℂ) (lpFourier g.1 n) *
          lpFourier f.1 n).re := by
  have h1 : inner ℝ g (densityHessian positiveH1 (haarProbability 1) f) =
      inner ℝ g.1 f.1 + inner ℝ g.1
        (kernelOp positiveH1 (haarProbability 1) f.1) := by
    show inner ℝ g.1 (f.1 + kernelOp positiveH1 (haarProbability 1) f.1) = _
    rw [inner_add_right]
  rw [h1]
  congr 1
  rw [inner_kernelOp]
  have : ∀ p : Torus 1 × Torus 1, centeredKernel positiveH1 (haarProbability 1) p.1 p.2 *
      ((g.1 : Torus 1 → ℝ) p.1 * (f.1 : Torus 1 → ℝ) p.2) =
      kappa * (R (p.1 - p.2) * ((g.1 : Torus 1 → ℝ) p.1 *
        (f.1 : Torus 1 → ℝ) p.2)) := fun p => by
    rw [centeredKernel_positiveH1]; ring
  simp_rw [this]
  rw [integral_const_mul]
  congr 1
  exact (integral_R_pair _ _).2


theorem norm_lpFourier_sq_eq (f : Lp ℝ 2 (haar 1)) (n : ℕ) :
    ((starRingEnd ℂ) (lpFourier f n) * lpFourier f n).re = ‖lpFourier f n‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem quadratic_densityHessian (f : centeredL2 (haarProbability 1)) :
    Summable (fun n : ℕ => a n * ‖lpFourier f.1 n‖ ^ 2) ∧
    inner ℝ f (densityHessian positiveH1 (haarProbability 1) f) =
      ‖f‖ ^ 2 + kappa * ∑' n : ℕ, a n * ‖lpFourier f.1 n‖ ^ 2 := by
  have e : ∀ n : ℕ, a n * ((starRingEnd ℂ) (lpFourier f.1 n) * lpFourier f.1 n).re =
      a n * ‖lpFourier f.1 n‖ ^ 2 := fun n => by rw [norm_lpFourier_sq_eq f.1 n]
  have hs := (integral_R_pair f.1 f.1).1
  refine ⟨hs.congr e, ?_⟩
  have := inner_densityHessian_bilinear f f
  rw [tsum_congr e] at this
  rw [this]
  congr 1
  exact real_inner_self_eq_norm_sq f.1

theorem densityHessian_coercive_form (f : centeredL2 (haarProbability 1)) :
    ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian positiveH1 (haarProbability 1) f) := by
  rw [(quadratic_densityHessian f).2]
  have : 0 ≤ ∑' n : ℕ, a n * ‖lpFourier f.1 n‖ ^ 2 :=
    tsum_nonneg fun n => mul_nonneg (a_nonneg n) (sq_nonneg _)
  have := kappa_pos
  nlinarith

theorem densityHessian_eq_conv (f : centeredL2 (haarProbability 1)) :
    ∀ᵐ x ∂haar 1, (densityHessian positiveH1 (haarProbability 1) f).1 x =
      f.1 x + kappa * conv f.1 R x := by
  have h1 : (densityHessian positiveH1 (haarProbability 1) f).1 =
      f.1 + kernelOp positiveH1 (haarProbability 1) f.1 := rfl
  rw [h1]
  filter_upwards [Lp.coeFn_add f.1 (kernelOp positiveH1 (haarProbability 1) f.1),
    kernelOp_ae positiveH1 (haarProbability 1) f.1] with x hx hk
  rw [hx, Pi.add_apply, hk]
  congr 1
  unfold kernelTransform conv
  simp_rw [centeredKernel_positiveH1]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  ring


/-- The real trigonometric mode `x ↦ 2 Re (c e_n(x))` with complex amplitude `c`. -/
noncomputable def modeFn (c : ℂ) (n : ℕ) (x : Torus 1) : ℝ :=
  2 * (c * UnitAddTorus.mFourier (freq n) x).re

theorem modeFn_complex (c : ℂ) (n : ℕ) (x : Torus 1) :
    ((modeFn c n x : ℝ) : ℂ) = c * UnitAddTorus.mFourier (freq n) x +
      (starRingEnd ℂ) c * UnitAddTorus.mFourier (-freq n) x := by
  unfold modeFn
  have := Complex.add_conj (c * UnitAddTorus.mFourier (freq n) x)
  rw [map_mul, ← UnitAddTorus.mFourier_neg] at this
  rw [← this]

theorem conj_lpFourier (g : Lp ℝ 2 (haar 1)) (n : ℕ) :
    (starRingEnd ℂ) (lpFourier g n) =
      ∫ x, UnitAddTorus.mFourier (freq n) x * ((g x : ℝ) : ℂ) ∂haar 1 := by
  unfold lpFourier
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [UnitAddTorus.mFourier_neg]

theorem lpFourier_mode {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (f : Lp ℝ 2 (haar 1))
    (hf : ∀ᵐ x ∂haar 1, f x = modeFn c n x) (m : ℕ) :
    lpFourier f m = if m = n then c else 0 := by
  unfold lpFourier
  have h1 : ∫ x, UnitAddTorus.mFourier (-freq m) x * ((f x : ℝ) : ℂ) ∂haar 1 =
      ∫ x, (c * UnitAddTorus.mFourier (-freq m + freq n) x +
        (starRingEnd ℂ) c * UnitAddTorus.mFourier (-freq m + -freq n) x) ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx, modeFn_complex, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
    ring
  rw [h1, integral_add ((integrable_mFourier _).const_mul c)
    ((integrable_mFourier _).const_mul _), integral_const_mul, integral_const_mul,
    integral_mFourier, integral_mFourier]
  have h2 : ¬ (-freq m + -freq n = 0) := fun h => by
    have := (freq_cond2 m n).1 h
    omega
  by_cases hm : m = n
  · subst hm
    simp [h2]
  · have h3 : ¬ (-freq m + freq n = 0) := fun h => hm ((freq_cond1 m n).1 h)
    simp [h2, h3, hm]

theorem inner_mode (c : ℂ) (n : ℕ) (g f : Lp ℝ 2 (haar 1))
    (hf : ∀ᵐ x ∂haar 1, f x = modeFn c n x) :
    inner ℝ g f = (2 * ((starRingEnd ℂ) (lpFourier g n) * c)).re := by
  have hg := integrable_lp_haar g
  rw [L2.inner_def]
  have h1 : ∫ x, inner ℝ (g x) (f x) ∂haar 1 =
      ∫ x, (2 * (c * (UnitAddTorus.mFourier (freq n) x * ((g x : ℝ) : ℂ)))).re ∂haar 1 := by
    refine integral_congr_ae ?_
    filter_upwards [hf] with x hx
    rw [hx]
    have : 2 * (c * (UnitAddTorus.mFourier (freq n) x * ((g x : ℝ) : ℂ))) =
        (2 * (c * UnitAddTorus.mFourier (freq n) x)) * ((g x : ℝ) : ℂ) := by ring
    rw [this, Complex.re_mul_ofReal]
    simp only [modeFn, RCLike.inner_apply, conj_trivial]
    simp
  rw [h1]
  have hint : Integrable (fun x => 2 * (c * (UnitAddTorus.mFourier (freq n) x *
      ((g x : ℝ) : ℂ)))) (haar 1) :=
    ((integrable_mFourier_mul hg (freq n)).const_mul c).const_mul 2
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [hre, integral_const_mul, integral_const_mul, ← conj_lpFourier, mul_comm c]


theorem densityHessian_mode {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (f : centeredL2 (haarProbability 1))
    (hf : ∀ᵐ x ∂haar 1, f.1 x = modeFn c n x) :
    densityHessian positiveH1 (haarProbability 1) f = (1 + kappa * a n / 2) • f := by
  set lam : ℝ := 1 + kappa * a n / 2 with hlam
  have key : ∀ g : centeredL2 (haarProbability 1),
      inner ℝ g (densityHessian positiveH1 (haarProbability 1) f) = lam * inner ℝ g f := by
    intro g
    rw [inner_densityHessian_bilinear]
    have e1 : ∑' m : ℕ, a m * ((starRingEnd ℂ) (lpFourier g.1 m) * lpFourier f.1 m).re =
        a n * ((starRingEnd ℂ) (lpFourier g.1 n) * c).re := by
      rw [tsum_eq_single n]
      · rw [lpFourier_mode hn c f.1 hf n]; simp
      · intro m hm
        rw [lpFourier_mode hn c f.1 hf m]; simp [hm]
    rw [e1]
    have e2 : inner ℝ g.1 f.1 = 2 * ((starRingEnd ℂ) (lpFourier g.1 n) * c).re := by
      exact (inner_mode c n g.1 f.1 hf).trans (by simp)
    show inner ℝ g.1 f.1 + _ = lam * inner ℝ g.1 f.1
    rw [e2, hlam]; ring
  set d : centeredL2 (haarProbability 1) :=
    densityHessian positiveH1 (haarProbability 1) f - lam • f with hd
  have h0 : inner ℝ d d = 0 := by
    have h1 := key d
    have : inner ℝ d d = inner ℝ d (densityHessian positiveH1 (haarProbability 1) f) -
        lam * inner ℝ d f := by
      have hdd : inner ℝ d d = inner ℝ d (densityHessian positiveH1 (haarProbability 1) f - lam • f) := rfl
      rw [hdd, inner_sub_right, real_inner_smul_right d f lam]
    rw [this, h1]; ring
  have : d = 0 := inner_self_eq_zero.mp h0
  exact sub_eq_zero.mp this


theorem continuous_modeFn (c : ℂ) (n : ℕ) : Continuous (modeFn c n) :=
  continuous_const.mul (Complex.continuous_re.comp
    (continuous_const.mul (UnitAddTorus.mFourier (freq n)).continuous))

theorem exists_unit_mode {n : ℕ} (hn : 1 ≤ n) (c : ℂ) (hc : ‖c‖ ^ 2 = 1 / 2) :
    ∃ f : centeredL2 (haarProbability 1), ‖f‖ = 1 ∧ ∀ᵐ x ∂haar 1, f.1 x = modeFn c n x := by
  have hm : MemLp (modeFn c n) 2 (haar 1) := memLp_two_of_continuous (continuous_modeFn c n)
  set w : Lp ℝ 2 (haar 1) := hm.toLp (modeFn c n) with hw
  have hae : ∀ᵐ x ∂haar 1, w x = modeFn c n x := MemLp.coeFn_toLp hm
  have hne1 : ¬ (freq n = 0) := fun h => by
    have := (freq_cond3 n n).1 (by rw [← two_smul ℕ, h]; simp)
    omega
  have hne2 : ¬ (-freq n = 0) := fun h => hne1 (neg_eq_zero.mp h)
  have hint : Integrable (fun x => ((modeFn c n x : ℝ) : ℂ)) (haar 1) :=
    (continuous_modeFn c n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      |>.ofReal
  have hcent : ∫ x, w x ∂haar 1 = 0 := by
    have h1 : ∫ x, w x ∂haar 1 = ∫ x, modeFn c n x ∂haar 1 := integral_congr_ae hae
    rw [h1]
    have h2 : (((∫ x, modeFn c n x ∂haar 1 : ℝ)) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      simp_rw [modeFn_complex]
      rw [integral_add ((integrable_mFourier _).const_mul c) ((integrable_mFourier _).const_mul _),
        integral_const_mul, integral_const_mul, integral_mFourier, integral_mFourier]
      simp [hne1, hne2]
    exact_mod_cast h2
  have hnorm : ‖w‖ ^ 2 = 1 := by
    rw [norm_Lp_sq]
    have h1 : ∫ x, (w x) ^ 2 ∂haar 1 = ∫ x, (modeFn c n x) ^ 2 ∂haar 1 :=
      integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx])
    rw [h1]
    have hsq : ∀ x : Torus 1, (((modeFn c n x) ^ 2 : ℝ) : ℂ) =
        c ^ 2 * UnitAddTorus.mFourier (freq n + freq n) x +
        (starRingEnd ℂ) c ^ 2 * UnitAddTorus.mFourier (-freq n + -freq n) x +
        2 * (c * (starRingEnd ℂ) c) := by
      intro x
      have h0 : UnitAddTorus.mFourier (freq n) x * UnitAddTorus.mFourier (-freq n) x = 1 := by
        rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]; rfl
      push_cast
      rw [modeFn_complex, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_add]
      linear_combination (2 * (c * (starRingEnd ℂ) c)) * h0
    have h2 : (((∫ x, (modeFn c n x) ^ 2 ∂haar 1 : ℝ)) : ℂ) = 1 := by
      rw [← integral_complex_ofReal]
      simp_rw [hsq]
      have hne3 : ¬ (freq n + freq n = 0) := fun h => by
        have := (freq_cond3 n n).1 h
        omega
      have hne4 : ¬ (-freq n + -freq n = 0) := fun h => by
        have := (freq_cond2 n n).1 h
        omega
      have iA : Integrable (fun x => c ^ 2 * UnitAddTorus.mFourier (freq n + freq n) x) (haar 1) :=
        (integrable_mFourier _).const_mul _
      have iB : Integrable (fun x => (starRingEnd ℂ) c ^ 2 *
          UnitAddTorus.mFourier (-freq n + -freq n) x) (haar 1) :=
        (integrable_mFourier _).const_mul _
      have iAB : Integrable (fun x => c ^ 2 * UnitAddTorus.mFourier (freq n + freq n) x +
          (starRingEnd ℂ) c ^ 2 * UnitAddTorus.mFourier (-freq n + -freq n) x) (haar 1) := iA.add iB
      rw [integral_add iAB (integrable_const _),
        integral_add ((integrable_mFourier _).const_mul _) ((integrable_mFourier _).const_mul _),
        integral_const_mul, integral_const_mul, integral_mFourier, integral_mFourier]
      have hr : (haar 1).real univ = 1 := by simp [Measure.real]
      simp only [hne3, hne4, ite_false, mul_zero, zero_add, integral_const, hr, one_smul]
      have : c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj']; push_cast; ring
      rw [this, hc]; push_cast; ring
    have h3 : (∫ x, (modeFn c n x) ^ 2 ∂haar 1 : ℝ) = 1 := by exact_mod_cast h2
    rw [h3]
  refine ⟨⟨w, hcent⟩, ?_, hae⟩
  have : ‖w‖ = 1 := by
    have h0 := norm_nonneg w
    nlinarith
  exact this


/-- Real normalized `cos`/`sin` eigenpair at frequency `n` with eigenvalue `lam`: unit vectors of
`L²_0(m)` equal a.e. to `√2 cos (2π n ·)` and `√2 sin (2π n ·)`, both eigenvectors of the density
Hessian at the Haar equilibrium for `lam`. -/
def IsSinCosEigenpair (n : ℕ) (lam : ℝ) : Prop :=
  ∃ u v : centeredL2 (haarProbability 1), ‖u‖ = 1 ∧ ‖v‖ = 1 ∧
    (∀ᵐ x ∂haar 1, u.1 x = Real.sqrt 2 * cosMode n x) ∧
    (∀ᵐ x ∂haar 1, v.1 x = Real.sqrt 2 * sinMode n x) ∧
    densityHessian positiveH1 (haarProbability 1) u = lam • u ∧
    densityHessian positiveH1 (haarProbability 1) v = lam • v

theorem sinCosEigenpair {n : ℕ} (hn : 1 ≤ n) :
    IsSinCosEigenpair n (1 + kappa * a n / 2) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hc1 : ‖((Real.sqrt 2 / 2 : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, hs]; norm_num
  have hc2 : ‖(-Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact hc1
  have e1 : ∀ x, modeFn ((Real.sqrt 2 / 2 : ℝ) : ℂ) n x = Real.sqrt 2 * cosMode n x := by
    intro x
    unfold modeFn cosMode
    rw [Complex.re_ofReal_mul]
    have hf : freq (n : ℤ) = fun _ : Fin 1 => (n : ℤ) := rfl
    rw [hf]
    ring
  have e2 : ∀ x, modeFn (-Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ)) n x =
      Real.sqrt 2 * sinMode n x := by
    intro x
    unfold modeFn sinMode
    have : -Complex.I * ((Real.sqrt 2 / 2 : ℝ) : ℂ) * UnitAddTorus.mFourier (freq n) x =
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (-Complex.I * UnitAddTorus.mFourier (freq n) x) := by ring
    rw [this, Complex.re_ofReal_mul]
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im]
    have hf : freq (n : ℤ) = fun _ : Fin 1 => (n : ℤ) := rfl
    rw [hf]
    ring
  obtain ⟨u, hu, hua⟩ := exists_unit_mode hn _ hc1
  obtain ⟨v, hv, hva⟩ := exists_unit_mode hn _ hc2
  refine ⟨u, v, hu, hv, ?_, ?_, densityHessian_mode hn _ u hua, densityHessian_mode hn _ v hva⟩
  · filter_upwards [hua] with x hx
    rw [hx, e1]
  · filter_upwards [hva] with x hx
    rw [hx, e2]

/-- **H1009 (positive example, density Hessian).** At the Haar equilibrium of the positive `H¹`
example, on real centered `L²(m)` the density Hessian is `I + T` with `T h = κ R * h` (a.e.);
its quadratic form is `⟨h, (I+T) h⟩ = ‖h‖² + κ Σ_{n ≥ 2} a_n |ĥ(n)|²` (the series is summable,
and `a_n = 0` for `n < 2`), hence `≥ ‖h‖²` and the Hessian is coercive with constant `1`; the real
normalized `cos`/`sin` modes are eigenvectors with eigenvalue `1` at `n = 1` and
`1 + κ a_n / 2` at every `n ≥ 2`. -/
theorem positive_example_density_hessian :
    (∀ f : centeredL2 (haarProbability 1),
      ∀ᵐ x ∂haar 1, (densityHessian positiveH1 (haarProbability 1) f).1 x =
        f.1 x + kappa * conv f.1 R x) ∧
    (∀ f : centeredL2 (haarProbability 1),
      Summable (fun n : ℕ => a n * ‖lpFourier f.1 n‖ ^ 2) ∧
      inner ℝ f (densityHessian positiveH1 (haarProbability 1) f) =
        ‖f‖ ^ 2 + kappa * ∑' n : ℕ, a n * ‖lpFourier f.1 n‖ ^ 2) ∧
    (∀ f : centeredL2 (haarProbability 1),
      ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian positiveH1 (haarProbability 1) f)) ∧
    IsCoerciveDensityHessian positiveH1 (haarProbability 1) ∧
    IsSinCosEigenpair 1 1 ∧
    (∀ n : ℕ, 2 ≤ n → IsSinCosEigenpair n (1 + kappa * a n / 2)) := by
  refine ⟨densityHessian_eq_conv, quadratic_densityHessian, densityHessian_coercive_form,
    ⟨1, one_pos, fun f => by simpa using densityHessian_coercive_form f⟩, ?_,
    fun n hn => sinCosEigenpair (by omega)⟩
  have h1 : a 1 = 0 := by simp [a]
  have := sinCosEigenpair (n := 1) le_rfl
  rwa [h1, mul_zero, zero_div, add_zero] at this

end DGPS.Examples.PositiveH1.Nonlinear
