import SharpSymmetricLSI.Paper.AppAEnt7

/-!
# The entropy (8): identification of the dissipation

For a bounded probability density `f ∈ H¹` with weak gradient `w` and `J = w + f a_f`
(`a_f = ∇V + ∇(W*f)`): if `∫ |J|²/f < ∞` then `√f ∈ H¹`, with `∇√f = w/(2√f)` on `{f > 0}`
and `0` elsewhere, and `D(f) ≤ ∫ |J|²/f` (`dissipation_le_fisher`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `a_f = ∇V + ∇(W*f)`, pointwise. -/
noncomputable def aD (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (f : Torus d → ℝ)
    (x : Torus d) (j : Fin d) : ℝ :=
  lipGrad V x j + bForceL W f x j

theorem tendsto_delta_seq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity⟩

theorem dissipation_le_fisher (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x)
    {w : Torus d → Fin d → ℝ} (hw : IsWeakGrad f w) (hw2 : ∀ j, MemLp (fun y => w y j) 2 volume)
    (hQ : ∫⁻ x, ENNReal.ofReal (∑ j, (w x j + f x * aD V W f x j) ^ 2) / ENNReal.ofReal (f x)
      ∂haar d ≠ ⊤) :
    dissipation V W f ≤
      ∫⁻ x, ENNReal.ofReal (∑ j, (w x j + f x * aD V W f x j) ^ 2) / ENNReal.ofReal (f x) ∂haar d := by
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hwi : ∀ k, Integrable (fun y => w y k) (haar d) := fun k => (hw2 k).integrable one_le_two
  set LV : ℝ := ((Real.toNNReal (KV * Fintype.card (Fin d) / 2) : NNReal) : ℝ)
  have hLV : ∀ x k, |lipGrad V x k| ≤ LV := fun x k => abs_lipGrad_le (lipschitz_V hyp (W := W)) x k
  have hVg := isWeakGrad_lipGrad hyp.continuous_V (lipschitz_V hyp (W := W))
  have hCg := isWeakGrad_convDens' hyp hfi
  obtain ⟨Cb₀, hCb₀⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb₀ 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb₀ x y k).trans (le_max_left _ _)
  set c := LV + Cb * ∫ y, |f y| ∂haar d
  have haD : ∀ x j, |aD V W f x j| ≤ c := fun x j =>
    (abs_add_le _ _).trans (add_le_add (hLV x j) (appA_abs_bForceL_le hCb hfi x j))
  have haDm : ∀ j, AEStronglyMeasurable (fun x => aD V W f x j) (haar d) := fun j =>
    (appA_aestronglyMeasurable_grad hVg j).add (appA_aestronglyMeasurable_grad hCg j)
  set S : Torus d → ℝ := fun x => ∑ j, (w x j + f x * aD V W f x j) ^ 2 with hS
  have hSm : AEStronglyMeasurable S (haar d) :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (((hw2 j).aestronglyMeasurable.add (hf.aestronglyMeasurable.mul (haDm j))).pow 2)
  set Q : Torus d → ℝ≥0∞ := fun x => ENNReal.ofReal (S x) / ENNReal.ofReal (f x) with hQdef
  have hQm : AEMeasurable Q (haar d) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hSm.aemeasurable).div
      (ENNReal.measurable_ofReal.comp hf).aemeasurable
  -- the candidate gradient of `√f`
  set h : Torus d → Fin d → ℝ := fun x j => if 0 < f x then w x j / (2 * Real.sqrt (f x)) else 0
    with hhdef
  have hm : ∀ j, AEStronglyMeasurable (fun x => h x j) (haar d) := fun j => by
    have e : (fun x => h x j) = {x | 0 < f x}.indicator
        (fun x => w x j * (2 * Real.sqrt (f x))⁻¹) := by
      funext x; simp only [hhdef, Set.indicator, Set.mem_setOf_eq, div_eq_mul_inv]
    rw [e]
    exact ((hw2 j).aestronglyMeasurable.mul ((measurable_const.mul
      (Real.continuous_sqrt.measurable.comp hf)).inv.aestronglyMeasurable)).indicator
      (measurableSet_lt measurable_const hf)
  have hpt : ∀ x j, ENNReal.ofReal (h x j ^ 2) ≤ Q x + ENNReal.ofReal (K * c ^ 2) := fun x j => by
    by_cases hx : 0 < f x
    · simp only [hhdef, if_pos hx]
      rw [hQdef]; dsimp only
      rw [← ENNReal.ofReal_div_of_pos hx, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hs2 : Real.sqrt (f x) ^ 2 = f x := Real.sq_sqrt hx.le
      have hsp : 0 < Real.sqrt (f x) := Real.sqrt_pos.2 hx
      have hJ : (w x j + f x * aD V W f x j) ^ 2 ≤ S x :=
        Finset.single_le_sum (f := fun j => (w x j + f x * aD V W f x j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ j)
      have ha2 : aD V W f x j ^ 2 ≤ c ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (haD x j) 2
      have hfK : f x ≤ K := (le_abs_self _).trans (hK x)
      rw [div_pow, mul_pow, hs2]
      have e : w x j = (w x j + f x * aD V W f x j) - f x * aD V W f x j := by ring
      have key : w x j ^ 2 ≤ 2 * (w x j + f x * aD V W f x j) ^ 2 + 2 * (f x * aD V W f x j) ^ 2 := by
        nlinarith [sq_nonneg (w x j + f x * aD V W f x j + f x * aD V W f x j)]
      rw [div_le_iff₀ (by positivity)]
      have : (f x * aD V W f x j) ^ 2 ≤ f x * K * c ^ 2 := by
        rw [mul_pow]
        have : f x ^ 2 ≤ f x * K := by nlinarith
        nlinarith [sq_nonneg (aD V W f x j)]
      have hSdiv : S x / f x * (2 ^ 2 * f x) = 4 * S x := by field_simp; ring
      nlinarith
    · simp only [hhdef, if_neg hx]; simp
  have hh2 : ∀ j, MemLp (fun x => h x j) 2 (haar d) := fun j => by
    rw [memLp_two_iff_integrable_sq (hm j)]
    refine ⟨(hm j).pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg _)]
    refine lt_of_le_of_lt (lintegral_mono fun x => hpt x j) ?_
    rw [lintegral_add_right' _ aemeasurable_const, lintegral_const]
    exact ENNReal.add_lt_top.2 ⟨hQ.lt_top, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top _ _)⟩
  have hhi : ∀ k, Integrable (fun y => h y k) (haar d) := fun k => (hh2 k).integrable one_le_two
  -- `√f` has weak gradient `h`
  set δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδn : ∀ n, 0 < δn n := fun n => by positivity
  have hδn1 : ∀ n, δn n ≤ 1 := fun n => by
    simp only [δn]; rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hFG : ∀ n, IsWeakGrad (fun y => sig (δn n) (f y)) (fun y k => sigp (δn n) (f y) * w y k) :=
    fun n => by
      have := isWeakGrad_comp hw hfi hwi (contDiff_sig (hδn n)) (L := 1 / (2 * Real.sqrt (δn n)))
        fun t => by rw [deriv_sig (hδn n)]; exact abs_sigp_le (hδn n) t
      simpa only [deriv_sig (hδn n)] using this
  set Ms := Real.sqrt (Real.sqrt (K ^ 2 + 1))
  have hFi : ∀ n, Integrable (fun y => sig (δn n) (f y)) (haar d) := fun n =>
    appA_integrable_of_abs_le' ((contDiff_sig (hδn n)).continuous.measurable.comp hf)
      (C := Ms) fun y => abs_sig_le (hδn n).le (hδn1 n) (hK y)
  have hGi : ∀ n k, Integrable (fun y => sigp (δn n) (f y) * w y k) (haar d) := fun n k =>
    (hwi k).bdd_mul (c := 1 / (2 * Real.sqrt (δn n)))
      ((contDiff_sig (hδn n)).continuous_deriv le_rfl |> fun hc => by
        rw [deriv_sig (hδn n)] at hc; exact (hc.measurable.comp hf).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_sigp_le (hδn n) _)
  have hsqi : Integrable (fun y => Real.sqrt (f y)) (haar d) :=
    appA_integrable_of_abs_le' (Real.continuous_sqrt.measurable.comp hf) (C := Real.sqrt K)
      fun y => by
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hK y))
  have hlimδ := tendsto_delta_seq
  have hFc : Tendsto (fun n => ∫⁻ y, ‖sig (δn n) (f y) - Real.sqrt (f y)‖ₑ ∂haar d) atTop (𝓝 0) := by
    have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
      (F := fun n y => sig (δn n) (f y)) (f := fun y => Real.sqrt (f y)) (bound := fun _ => Ms)
      (fun n => (hFi n).aestronglyMeasurable) (integrable_const Ms).hasFiniteIntegral
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_sig_le (hδn n).le (hδn1 n) (hK y))
      (by filter_upwards [h0] with y hy; exact (tendsto_sig hy).comp hlimδ)
    simpa only [ofReal_norm] using this
  have hGc : ∀ k, Tendsto (fun n => ∫⁻ y, ‖sigp (δn n) (f y) * w y k - h y k‖ₑ ∂haar d) atTop
      (𝓝 0) := fun k => by
    have := tendsto_lintegral_norm_of_dominated_convergence (μ := haar d)
      (F := fun n y => sigp (δn n) (f y) * w y k) (f := fun y => h y k)
      (bound := fun y => |h y k|)
      (fun n => (hGi n k).aestronglyMeasurable) (hhi k).abs.hasFiniteIntegral
      (fun n => by
        filter_upwards [h0] with y hy
        rw [Real.norm_eq_abs, abs_mul]
        rcases hy.lt_or_eq with hy | hy
        · simp only [hhdef, if_pos hy]
          rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (f y)), div_eq_mul_inv,
            mul_comm (|w y k|)]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          have := abs_sigp_le_of_pos (hδn n) hy
          rwa [one_div] at this
        · rw [← hy, sigp_zero, abs_zero, zero_mul]; exact abs_nonneg _)
      (by
        filter_upwards [h0] with y hy
        rcases hy.lt_or_eq with hy | hy
        · simp only [hhdef, if_pos hy]
          have := ((tendsto_sigp hy).comp hlimδ).mul_const (w y k)
          have e : w y k / (2 * Real.sqrt (f y)) = 1 / (2 * Real.sqrt (f y)) * w y k := by ring
          rw [e]; exact this
        · have hfy : ¬ (0 < f y) := by rw [← hy]; exact lt_irrefl 0
          simp only [hhdef, if_neg hfy]
          rw [← hy]; simp only [sigp_zero, zero_mul]; exact tendsto_const_nhds)
    simpa only [ofReal_norm] using this
  have hsq : IsWeakGrad (fun y => Real.sqrt (f y)) h :=
    isWeakGrad_of_tendsto hFG hFi hGi hsqi hhi hFc hGc
  -- `√f ∈ H¹`
  have hsqNorm : MemLp (fun x => Real.sqrt (sqNorm (h x))) 2 (haar d) := by
    have hsn : AEStronglyMeasurable (fun x => sqNorm (h x)) (haar d) := by
      unfold sqNorm; exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hm j).pow 2
    have hm' : AEStronglyMeasurable (fun x => Real.sqrt (sqNorm (h x))) (haar d) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hsn
    rw [memLp_two_iff_integrable_sq hm']
    refine (integrable_finsetSum (Finset.univ : Finset (Fin d))
      fun j _ => (hh2 j).integrable_sq).congr (Eventually.of_forall fun x => ?_)
    show ∑ j, h x j ^ 2 = Real.sqrt (sqNorm (h x)) ^ 2
    unfold sqNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (h x j))]
  have hH1 : MemH1 (haar d) (fun x => Real.sqrt (f x)) := by
    refine ⟨⟨h, hsq⟩, memLp_of_abs_le (Real.continuous_sqrt.measurable.comp hf)
      (C := Real.sqrt K) (fun y => by
        show |Real.sqrt (f y)| ≤ _
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt ((le_abs_self _).trans (hK y))) 2, ?_⟩
    refine hsqNorm.ae_eq ?_
    filter_upwards [appA_weakGrad_ae_eq hsq] with x hx
    rw [hx]
  have hpot := hVg.add hCg
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hpot⟩⟩]
  refine lintegral_mono_ae ?_
  filter_upwards [appA_weakGrad_ae_eq hsq, appA_weakGrad_ae_eq hpot, h0] with x e1 e2 hx0
  rw [e1, e2]
  rcases hx0.lt_or_eq with hx | hx
  · simp only [hhdef, if_pos hx]
    rw [← ENNReal.ofReal_div_of_pos hx]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hs2 : Real.sqrt (f x) ^ 2 = f x := Real.sq_sqrt hx.le
    have hsp : 0 < Real.sqrt (f x) := Real.sqrt_pos.2 hx
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [aD]
    field_simp
    rw [hs2]; ring
  · simp only [hhdef, ← hx, lt_irrefl, if_false, Real.sqrt_zero]
    simp

end SharpLSI
