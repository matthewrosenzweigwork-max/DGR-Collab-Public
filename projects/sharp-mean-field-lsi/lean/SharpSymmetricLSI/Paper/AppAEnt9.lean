import SharpSymmetricLSI.Paper.AppAEnt8
import SharpSymmetricLSI.Paper.AppAConv4

/-!
# The entropy (9): the limit `δ → 0` of the rate at a fixed time

For a bounded probability density `f ∈ H¹` with `J = ∇f + f a_f`:
`R_δ(f, f a_f) = ∫ G_δ''(f) |J|² + ∑ⱼ ∫ (1 - f G_δ''(f)) a_{f,j} J_j` (`limRate_split`), and with
`B = ∑ⱼ ∫ |a_{f,j}| |J_j|`, `R_{δₙ} + B → ∫ |J|²/f + B` in `[0, ∞]` (`tendsto_limRate_delta`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

theorem entGpp_zero {δ : ℝ} (hδ : 0 < δ) : entGpp δ 0 = δ⁻¹ := by
  simp [entGpp, Real.sqrt_sq hδ.le]

theorem entGpp_anti {δ δ' : ℝ} (hδ' : 0 < δ') (h : δ' ≤ δ) (r : ℝ) : entGpp δ r ≤ entGpp δ' r := by
  unfold entGpp
  refine inv_anti₀ (sqrt_sq_add_pos hδ' r) (Real.sqrt_le_sqrt ?_)
  nlinarith

theorem mul_entGpp_nonneg {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ r * entGpp δ r :=
  mul_nonneg hr (entGpp_pos hδ r).le

theorem mul_entGpp_le_one {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 ≤ r) : r * entGpp δ r ≤ 1 := by
  unfold entGpp
  rw [← div_eq_mul_inv, div_le_one (sqrt_sq_add_pos hδ r)]
  have := abs_lt_sqrt_sq_add hδ r
  rw [abs_of_nonneg hr] at this; exact this.le

theorem tendsto_entGpp {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ => entGpp δ r) (𝓝[>] 0) (𝓝 r⁻¹) := by
  have hc : ContinuousAt (fun δ : ℝ => entGpp δ r) 0 := by
    unfold entGpp
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]; exact hr.ne'
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  convert this using 2
  simp [entGpp, Real.sqrt_sq hr.le]

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **The rate at level `δ` converges as `δ → 0`.** For `B ≥ C₁ ∫ |∇f|² + C₂`,
`R_{δₙ}(f) + B → ∫ |J|²/f + B` in `[0, ∞]`. -/
theorem tendsto_limRate_delta (hyp : Hyp V W KV KW) (K : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {f : Torus d → ℝ}, Measurable f → (∀ x, |f x| ≤ K) →
      (∀ᵐ x ∂haar d, 0 ≤ f x) → ∫ x, f x ∂haar d = 1 →
      ∀ {g : Torus d → Fin d → ℝ}, IsWeakGrad f g → (∀ j, MemLp (fun y => g y j) 2 volume) →
      ∀ B : ℝ, C₁ * (∑ j, ∫ x, g x j ^ 2) + C₂ ≤ B →
      (∀ n : ℕ, 0 ≤ limRate V W (1 / ((n : ℝ) + 1)) f (fun y k => modFlux V W f y k) + B) ∧
      Tendsto (fun n : ℕ => ENNReal.ofReal
        (limRate V W (1 / ((n : ℝ) + 1)) f (fun y k => modFlux V W f y k) + B)) atTop
      (𝓝 ((∫⁻ x, ENNReal.ofReal (∑ j, (weakGrad f x j + f x * aD V W f x j) ^ 2) /
        ENNReal.ofReal (f x) ∂haar d) + ENNReal.ofReal B)) := by
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hLV0 : 0 ≤ LV := NNReal.coe_nonneg _
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  set c := LV + Cb
  have hc0 : 0 ≤ c := by positivity
  set K' := max K 0
  refine ⟨c, Fintype.card (Fin d) * (c * (1 + K' * c)), hc0, by positivity,
    fun {f} hf hK h0 h1 {g} hg hg2 B hB => ?_⟩
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hKK : K ≤ K' := le_max_left _ _
  set w := weakGrad f with hwdef
  have hwg : w =ᵐ[volume] g := appA_weakGrad_ae_eq hg
  have hw2 : ∀ j, MemLp (fun y => w y j) 2 volume := fun j =>
    (hg2 j).ae_eq (hwg.mono fun x hx => (congrFun hx j).symm)
  have hVg := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCg := isWeakGrad_convDens' hyp hfi
  have habs1 : ∫ y, |f y| ∂haar d = 1 :=
    (integral_congr_ae (h0.mono fun x hx => abs_of_nonneg hx)).trans h1
  have haD : ∀ x j, |aD V W f x j| ≤ c := fun x j => by
    have := appA_abs_bForceL_le hCb hfi x j
    rw [habs1, mul_one] at this
    exact (abs_add_le _ _).trans (add_le_add (hLV x j) this)
  have haDm : ∀ j, AEStronglyMeasurable (fun x => aD V W f x j) (haar d) := fun j =>
    (appA_aestronglyMeasurable_grad hVg j).add (appA_aestronglyMeasurable_grad hCg j)
  have hN : ∀ y k, modFlux V W f y k = f y * aD V W f y k := fun y k => by
    unfold modFlux aD; rw [bForceL_congr_ae (posNorm_ae_eq h0 h1)]
  set J : Torus d → Fin d → ℝ := fun x j => w x j + f x * aD V W f x j with hJdef
  have hJ2 : ∀ j, MemLp (fun x => J x j) 2 (haar d) := fun j =>
    (hw2 j).add (MemLp.of_bound (hf.aestronglyMeasurable.mul (haDm j)) (K * c)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hK x) (haD x j) (abs_nonneg _) hK0))
  set S : Torus d → ℝ := fun x => ∑ j, J x j ^ 2 with hSdef
  have hSi : Integrable S (haar d) := integrable_finsetSum _ fun j _ => (hJ2 j).integrable_sq
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have haJ : ∀ j, Integrable (fun x => |aD V W f x j| * |J x j|) (haar d) := fun j =>
    ((hJ2 j).integrable one_le_two).abs.bdd_mul (c := c)
      (continuous_abs.comp_aestronglyMeasurable (haDm j))
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact haD x j)
  -- `∑ⱼ ∫ |a_j| |J_j| ≤ B`
  have hwgi : ∀ j, ∫ x, w x j ^ 2 ∂haar d = ∫ x, g x j ^ 2 ∂haar d := fun j =>
    integral_congr_ae (hwg.mono fun x hx => by show w x j ^ 2 = g x j ^ 2; rw [congrFun hx j])
  have hB0 : ∑ j, ∫ x, |aD V W f x j| * |J x j| ∂haar d ≤ B := by
    refine le_trans ?_ hB
    have eS : c * (∑ j, ∫ x, g x j ^ 2 ∂haar d) + (Fintype.card (Fin d) : ℝ) * (c * (1 + K' * c)) =
        ∑ j : Fin d, (c * (∫ x, g x j ^ 2 ∂haar d) + c * (1 + K' * c)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [eS]
    refine Finset.sum_le_sum fun j _ => ?_
    have hpt : ∀ x, |aD V W f x j| * |J x j| ≤ c * w x j ^ 2 + c * (1 + K' * c) := fun x => by
      have h1' : |J x j| ≤ 1 + w x j ^ 2 + K' * c := by
        have : |f x * aD V W f x j| ≤ K' * c := by
          rw [abs_mul]; exact mul_le_mul ((hK x).trans hKK) (haD x j) (abs_nonneg _) (by positivity)
        have hw1 : |w x j| ≤ 1 + w x j ^ 2 := by nlinarith [sq_abs (w x j), abs_nonneg (w x j)]
        exact (abs_add_le _ _).trans (by linarith)
      calc |aD V W f x j| * |J x j| ≤ c * (1 + w x j ^ 2 + K' * c) :=
            mul_le_mul (haD x j) h1' (abs_nonneg _) hc0
        _ = c * w x j ^ 2 + c * (1 + K' * c) := by ring
    calc ∫ x, |aD V W f x j| * |J x j| ∂haar d
        ≤ ∫ x, (c * w x j ^ 2 + c * (1 + K' * c)) ∂haar d :=
          integral_mono (haJ j) (((hw2 j).integrable_sq.const_mul c).add (integrable_const _)) hpt
      _ = c * ∫ x, g x j ^ 2 ∂haar d + c * (1 + K' * c) := by
          rw [integral_add ((hw2 j).integrable_sq.const_mul c) (integrable_const _), integral_const_mul,
            hwgi j]; simp
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδn : ∀ n, 0 < δn n := fun n => by positivity
  have hGm : ∀ n, AEStronglyMeasurable (fun x => entGpp (δn n) (f x)) (haar d) := fun n =>
    ((continuous_entGpp (hδn n)).measurable.comp hf).aestronglyMeasurable
  have hGb : ∀ n x, ‖entGpp (δn n) (f x)‖ ≤ (δn n)⁻¹ := fun n x => by
    rw [Real.norm_eq_abs, abs_of_pos (entGpp_pos (hδn n) _)]; exact entGpp_le (hδn n) _
  set Qr : ℕ → ℝ := fun n => ∫ x, entGpp (δn n) (f x) * S x ∂haar d with hQrdef
  set Sr : ℕ → ℝ := fun n => ∑ j, ∫ x, (1 - f x * entGpp (δn n) (f x)) * aD V W f x j * J x j ∂haar d
    with hSrdef
  have hQi : ∀ n, Integrable (fun x => entGpp (δn n) (f x) * S x) (haar d) := fun n =>
    hSi.bdd_mul (hGm n) (Eventually.of_forall (hGb n))
  have hXi : ∀ n j, Integrable (fun x => entGpp (δn n) (f x) * J x j ^ 2) (haar d) := fun n j =>
    (hJ2 j).integrable_sq.bdd_mul (hGm n) (Eventually.of_forall (hGb n))
  have hYi : ∀ n j, Integrable (fun x => (1 - f x * entGpp (δn n) (f x)) * aD V W f x j * J x j)
      (haar d) := fun n j => by
    refine ((hJ2 j).integrable one_le_two).bdd_mul (c := (1 + K * (δn n)⁻¹) * c)
      ((aestronglyMeasurable_const.sub (hf.aestronglyMeasurable.mul (hGm n))).mul (haDm j))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ (haD x j) (abs_nonneg _) (by positivity)
    refine (abs_sub _ _).trans ?_
    rw [abs_one, abs_mul]
    have := hGb n x; rw [Real.norm_eq_abs] at this
    have h2 : |f x| * |entGpp (δn n) (f x)| ≤ K * (δn n)⁻¹ :=
      mul_le_mul (hK x) this (abs_nonneg _) hK0
    linarith
  have hsplit : ∀ n, limRate V W (δn n) f (fun y k => modFlux V W f y k) = Qr n + Sr n := fun n => by
    have hQr : Qr n = ∑ j, ∫ x, entGpp (δn n) (f x) * J x j ^ 2 ∂haar d := by
      simp only [hQrdef, hSdef, Finset.mul_sum]
      exact integral_finsetSum _ fun j _ => hXi n j
    rw [hQr, hSrdef, ← Finset.sum_add_distrib]
    unfold limRate
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_add (hXi n j) (hYi n j)]
    congr 1; funext x
    simp only [hN, hJdef, aD]
    ring
  have hSr : ∀ n, |Sr n| ≤ B := fun n => by
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)).trans hB0
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hYi n j).abs (haJ j) ?_)
    filter_upwards [h0] with x hx
    have h1' : |1 - f x * entGpp (δn n) (f x)| ≤ 1 := abs_le.2
      ⟨by linarith [mul_entGpp_le_one (hδn n) hx], by linarith [mul_entGpp_nonneg (hδn n) hx]⟩
    rw [abs_mul, abs_mul]
    calc |1 - f x * entGpp (δn n) (f x)| * |aD V W f x j| * |J x j|
        ≤ 1 * |aD V W f x j| * |J x j| := by gcongr
      _ = |aD V W f x j| * |J x j| := by ring
  have hQr0 : ∀ n, 0 ≤ Qr n := fun n =>
    integral_nonneg fun x => mul_nonneg (entGpp_pos (hδn n) _).le (hS0 x)
  have hstep : ∀ n, ENNReal.ofReal (limRate V W (δn n) f (fun y k => modFlux V W f y k) + B) =
      ENNReal.ofReal (Qr n) + ENNReal.ofReal (Sr n + B) := fun n => by
    rw [hsplit n, add_assoc, ENNReal.ofReal_add (hQr0 n) (by linarith [(abs_le.1 (hSr n)).1])]
  refine ⟨fun n => by rw [hsplit n]; linarith [hQr0 n, (abs_le.1 (hSr n)).1], ?_⟩
  -- monotone convergence for the main part
  have hQconv : Tendsto (fun n => ENNReal.ofReal (Qr n)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (S x) / ENNReal.ofReal (f x) ∂haar d)) := by
    have e : ∀ n, ENNReal.ofReal (Qr n) = ∫⁻ x, ENNReal.ofReal (entGpp (δn n) (f x) * S x) ∂haar d :=
      fun n => ofReal_integral_eq_lintegral_ofReal (hQi n)
        (Eventually.of_forall fun x => mul_nonneg (entGpp_pos (hδn n) _).le (hS0 x))
    simp_rw [e]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (hQi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal) ?_ ?_
    · refine Eventually.of_forall fun x m n hmn => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (entGpp_anti (hδn n) ?_ (f x)) (hS0 x))
      simp only [δn]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    · filter_upwards [h0] with x hx
      rcases hx.lt_or_eq with hx | hx
      · have := ENNReal.tendsto_ofReal
          (((tendsto_entGpp hx).comp tendsto_delta_seq).mul_const (S x))
        rw [← ENNReal.ofReal_div_of_pos hx, div_eq_inv_mul]
        exact this
      · rw [← hx]
        simp only [entGpp_zero (hδn _), ENNReal.ofReal_zero]
        by_cases hSx : S x = 0
        · simp [hSx]
        · have hSp : 0 < S x := (hS0 x).lt_of_ne' hSx
          rw [ENNReal.div_zero (by simpa using hSp)]
          refine ENNReal.tendsto_ofReal_atTop.comp ?_
          have e2 : ∀ n, (δn n)⁻¹ * S x = ((n : ℝ) + 1) * S x := fun n => by
            simp only [δn, one_div, inv_inv]
          simp_rw [e2]
          exact (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_mul_const hSp
  by_cases hQ0 : (∫⁻ x, ENNReal.ofReal (S x) / ENNReal.ofReal (f x) ∂haar d) = ⊤
  · show Tendsto _ atTop (𝓝 ((∫⁻ x, ENNReal.ofReal (S x) / ENNReal.ofReal (f x) ∂haar d) +
      ENNReal.ofReal B))
    rw [hQ0, top_add]
    rw [hQ0] at hQconv
    refine tendsto_nhds_top_mono hQconv (Eventually.of_forall fun n => ?_)
    show ENNReal.ofReal (Qr n) ≤ ENNReal.ofReal (limRate V W (δn n) f (fun y k => modFlux V W f y k) + B)
    rw [hstep n]; exact le_self_add
  · have hQm : AEMeasurable (fun x => ENNReal.ofReal (S x) / ENNReal.ofReal (f x)) (haar d) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable hSi.aestronglyMeasurable.aemeasurable).div
        (ENNReal.measurable_ofReal.comp hf).aemeasurable
    have hfin := ae_lt_top' hQm hQ0
    have hSr0 : Tendsto Sr atTop (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ _j : Fin d, (0 : ℝ) by simp]
      refine tendsto_finsetSum _ fun j _ => ?_
      have := tendsto_integral_of_dominated_convergence (μ := haar d)
        (F := fun n x => (1 - f x * entGpp (δn n) (f x)) * aD V W f x j * J x j) (f := fun _ => 0)
        (fun x => |aD V W f x j| * |J x j|) (fun n => (hYi n j).aestronglyMeasurable) (haJ j)
        (fun n => by
          filter_upwards [h0] with x hx
          have h1' : |1 - f x * entGpp (δn n) (f x)| ≤ 1 := abs_le.2
            ⟨by linarith [mul_entGpp_le_one (hδn n) hx], by linarith [mul_entGpp_nonneg (hδn n) hx]⟩
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          calc |1 - f x * entGpp (δn n) (f x)| * |aD V W f x j| * |J x j|
              ≤ 1 * |aD V W f x j| * |J x j| := by gcongr
            _ = |aD V W f x j| * |J x j| := by ring)
        (by
          filter_upwards [h0, hfin] with x hx hxf
          rcases hx.lt_or_eq with hx | hx
          · have h3 := (((tendsto_const_nhds (x := (1 : ℝ))).sub
              (((tendsto_entGpp hx).comp tendsto_delta_seq).const_mul (f x))).mul_const
              (aD V W f x j)).mul_const (J x j)
            rw [mul_inv_cancel₀ hx.ne', sub_self, zero_mul, zero_mul] at h3
            exact h3
          · rw [← hx, ENNReal.ofReal_zero] at hxf
            have hS : S x = 0 := by
              by_contra hne
              have hSp : 0 < S x := (hS0 x).lt_of_ne' hne
              rw [ENNReal.div_zero (by simpa using hSp)] at hxf
              exact lt_irrefl _ hxf
            have hJ : J x j = 0 := by
              have : J x j ^ 2 ≤ S x := Finset.single_le_sum (f := fun j => J x j ^ 2)
                (fun j _ => sq_nonneg _) (Finset.mem_univ j)
              rw [hS] at this
              exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
            simp only [hJ, mul_zero]
            exact tendsto_const_nhds)
      simpa using this
    have h2 : Tendsto (fun n => ENNReal.ofReal (Sr n + B)) atTop (𝓝 (ENNReal.ofReal B)) := by
      have := ENNReal.tendsto_ofReal (hSr0.add_const B)
      simpa using this
    have h3 := hQconv.add h2
    exact h3.congr fun n => (hstep n).symm

end SharpLSI
