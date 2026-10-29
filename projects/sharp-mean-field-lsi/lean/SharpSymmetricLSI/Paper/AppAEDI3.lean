import SharpSymmetricLSI.Paper.AppAEDI2
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.ELEquation

/-!
# The energy–dissipation inequality (2): renormalization and the limit `δ → 0` of the energy

* `limE_eq`: `E_δ(f) = E^K_δ(f) - log δ` for a probability density (`G_δ = K_δ - r log δ`).
* `tendsto_limEK`: `E^K_{δₙ}(f) → E^K_0(f)`.
* `freeEnergy_eq_limEK0`: `F(f m) = E^K_0(f) + 1 - log 2`.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped Real ENNReal

namespace SharpLSI

theorem continuous_entK {δ : ℝ} (hδ : 0 < δ) : Continuous (entK δ) := by
  unfold entK
  have h1 : Continuous fun r : ℝ => r + Real.sqrt (r ^ 2 + δ ^ 2) := by fun_prop
  exact (continuous_id.mul (h1.log fun r => (entArg_pos hδ r).ne')).sub (by fun_prop)

theorem entK0_eq {r : ℝ} (hr : 0 ≤ r) : entK0 r = klFun r - 1 + r * Real.log 2 := by
  unfold entK0 klFun
  rcases hr.lt_or_eq with hr | hr
  · rw [Real.log_mul two_ne_zero hr.ne']; ring
  · subst hr; simp

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The renormalized regularized free energy. -/
noncomputable def limEK (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (δ : ℝ)
    (f : Torus d → ℝ) : ℝ :=
  (∫ x, (entK δ (f x) + V x * f x)) + (∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)) / 2

/-- Its limit `δ → 0`. -/
noncomputable def limEK0 (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (f : Torus d → ℝ) : ℝ :=
  (∫ x, (entK0 (f x) + V x * f x)) + (∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume)) / 2

theorem integrable_entK_add (hyp : Hyp V W KV KW) {δ : ℝ} (hδ : 0 < δ) {f : Torus d → ℝ}
    (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Integrable (fun x => entK δ (f x) + V x * f x) (haar d) := by
  obtain ⟨M, -, hM⟩ := exists_bound_on_Icc (continuous_entK hδ) K
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  have hMV0 : 0 ≤ MV := (abs_nonneg _).trans (hVb 0)
  exact integrable_of_abs_le_finite (((continuous_entK hδ).measurable.comp hf).add
    (hyp.continuous_V.measurable.mul hf)).aestronglyMeasurable (B := M + MV * K) fun x => by
    refine (abs_add_le _ _).trans (add_le_add (hM _ (hK x)) ?_)
    rw [abs_mul]; exact mul_le_mul (hVb x) (hK x) (abs_nonneg _) hMV0

theorem limE_eq (hyp : Hyp V W KV KW) {δ : ℝ} (hδ : 0 < δ) {f : Torus d → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ x, |f x| ≤ K) (h1 : ∫ x, f x ∂haar d = 1) :
    limE V W δ f = limEK V W δ f - Real.log δ := by
  have hfi : Integrable f (haar d) := appA_integrable_of_abs_le' hf hK
  unfold limE limEK
  have e : ∫ x, (entG δ (f x) + V x * f x) ∂haar d =
      (∫ x, (entK δ (f x) + V x * f x) ∂haar d) - Real.log δ := by
    have : (fun x => entG δ (f x) + V x * f x) =
        fun x => (entK δ (f x) + V x * f x) - Real.log δ * f x := by
      funext x; rw [entG_eq hδ]; ring
    rw [this, integral_sub (integrable_entK_add hyp hδ hf hK) (hfi.const_mul _), integral_const_mul,
      h1, mul_one]
  rw [e]; ring

theorem tendsto_limEK (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, |f x| ≤ K) (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) :
    Tendsto (fun n : ℕ => limEK V W (1 / ((n : ℝ) + 1)) f) atTop (𝓝 (limEK0 V W f)) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  have hMV0 : 0 ≤ MV := (abs_nonneg _).trans (hVb 0)
  unfold limEK limEK0
  refine Tendsto.add_const _ ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => K * (2 * K + 1) + 1 + (K + 1) + MV * K)
    (fun n => (integrable_entK_add hyp (by positivity) hf hK).aestronglyMeasurable)
    (integrable_const _) (fun n => ?_) ?_
  · filter_upwards [h0] with x hx
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hδ1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add (abs_entK_le hK0 hδ hδ1 hx ((le_abs_self _).trans (hK x))) ?_)
    rw [abs_mul]; exact mul_le_mul (hVb x) (hK x) (abs_nonneg _) hMV0
  · filter_upwards [h0] with x hx
    exact ((tendsto_entK hx).comp tendsto_delta_seq).add_const _

/-- **`F(f m) = E^K_0(f) + 1 - log 2`.** -/
theorem freeEnergy_eq_limEK0 (hyp : Hyp V W KV KW) {f : Torus d → ℝ} (hf : Measurable f) {K : ℝ}
    (hK : ∀ x, |f x| ≤ K) (h0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1) :
    freeEnergy V W (densMeasure f) = ((limEK0 V W f + 1 - Real.log 2 : ℝ) : EReal) := by
  set fp : Torus d → ℝ := fun x => max (f x) 0 with hfp
  have hae : f =ᵐ[haar d] fp := posPart_ae_eq h0
  have hfpm : Measurable fp := hf.max measurable_const
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfpK : ∀ x, |fp x| ≤ K := fun x => by
    rw [abs_of_nonneg (hfp0 x)]; exact max_le ((le_abs_self _).trans (hK x)) ((abs_nonneg _).trans (hK x))
  have hfp1 : ∫ x, fp x ∂haar d = 1 := by rw [← integral_congr_ae hae, h1]
  have hfpi : Integrable fp (haar d) := appA_integrable_of_abs_le' hfpm hfpK
  have hkl : Integrable (fun x => klFun (fp x)) (haar d) := by
    obtain ⟨M, -, hM⟩ := exists_bound_on_Icc (by unfold klFun; fun_prop : Continuous klFun) K
    exact appA_integrable_of_abs_le' ((by unfold klFun; fun_prop : Continuous klFun).measurable.comp hfpm)
      fun x => hM _ (hfpK x)
  rw [densMeasure_congr_ae hae, freeEnergy_densMeasure hyp hfpm hfp0 hfp1 hkl]
  congr 1
  -- replace `f` by `fp` in `limEK0`
  have hWm : Measurable fun p : Torus d × Torus d => W p.1 p.2 := hyp.continuous_W.measurable
  obtain ⟨MV, hMV⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_V.continuousOn
  have hVb : ∀ x, |V x| ≤ MV := fun x => by simpa [Real.norm_eq_abs] using hMV x (mem_univ _)
  have hMV0 : 0 ≤ MV := (abs_nonneg _).trans (hVb 0)
  obtain ⟨MW, hMW⟩ := isCompact_univ.exists_bound_of_continuousOn hyp.continuous_W.continuousOn
  have hWb : ∀ x y, |W x y| ≤ MW := fun x y => by
    simpa [Real.norm_eq_abs] using hMW (x, y) (mem_univ _)
  have hMW0 : 0 ≤ MW := (abs_nonneg _).trans (hWb 0 0)
  have hVf : Integrable (fun x => fp x * V x) (haar d) :=
    integrable_of_abs_le_finite (hfpm.mul hyp.continuous_V.measurable).aestronglyMeasurable
      (B := K * MV) fun x => by
        rw [abs_mul]; exact mul_le_mul (hfpK x) (hVb x) (abs_nonneg _) ((abs_nonneg _).trans (hfpK x))
  have hI2 : Integrable (fun x => Real.log 2 * fp x + fp x * V x) (haar d) :=
    (hfpi.const_mul _).add hVf
  have e1 : ∫ x, (entK0 (f x) + V x * f x) ∂haar d =
      (∫ x, klFun (fp x) ∂haar d) - 1 + Real.log 2 + ∫ x, fp x * V x ∂haar d := by
    have : (fun x => entK0 (f x) + V x * f x) =ᵐ[haar d]
        fun x => (klFun (fp x) + (Real.log 2 * fp x + fp x * V x)) - 1 := by
      filter_upwards [hae] with x hx
      rw [hx, entK0_eq (hfp0 x)]; ring
    rw [integral_congr_ae this,
      integral_sub (f := fun x => klFun (fp x) + (Real.log 2 * fp x + fp x * V x)) (g := fun _ => 1)
        (hkl.add hI2) (integrable_const _),
      integral_add (f := fun x => klFun (fp x)) (g := fun x => Real.log 2 * fp x + fp x * V x) hkl hI2,
      integral_add (f := fun x => Real.log 2 * fp x) (g := fun x => fp x * V x) (hfpi.const_mul _) hVf,
      integral_const_mul, hfp1]
    simp; ring
  have hWi : Integrable (fun p : Torus d × Torus d => W p.1 p.2 * (fp p.1 * fp p.2)) (volume.prod volume) :=
    integrable_of_abs_le_finite (hWm.mul ((hfpm.comp measurable_fst).mul
      (hfpm.comp measurable_snd))).aestronglyMeasurable (B := MW * (K * K)) fun p => by
      rw [abs_mul, abs_mul]
      have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
      exact mul_le_mul (hWb _ _) (mul_le_mul (hfpK _) (hfpK _) (abs_nonneg _) hK0) (by positivity) hMW0
  have e2 : ∫ p, W p.1 p.2 * (f p.1 * f p.2) ∂(volume.prod volume) = Aform W fp fp := by
    rw [integral_congr_ae (g := fun p : Torus d × Torus d => W p.1 p.2 * (fp p.1 * fp p.2))
      (by filter_upwards [ae_fst_of_ae hae, ae_snd_of_ae hae] with p h1 h2; rw [h1, h2]),
      integral_prod _ hWi]
    unfold Aform convDens
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    congr 1; funext y; ring
  unfold limEK0
  rw [e1, e2]; ring

end SharpLSI
