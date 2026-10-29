import SharpSymmetricLSI.Paper.AppACont2

/-!
# Lemma A.1: existence of the mild probability solution

For a bounded probability density `ρ₀`, the Picard solution of the modified equation is a mild
solution of (4.7) in the class of Lemma A.1 (`exists_appAMild`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `‖g‖₁ ≤ ‖g‖₂` on the torus. -/
theorem eLpNorm_one_le_sqrt {g : Torus d → ℝ} (hg : MemLp g 2 volume) :
    eLpNorm g 1 volume ≤ ENNReal.ofReal (Real.sqrt (∫ x, g x ^ 2)) := by
  have hgi : Integrable g := hg.integrable one_le_two
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hgi]
  refine ENNReal.ofReal_le_ofReal ?_
  set m := ∫ x, ‖g x‖
  have hm0 : 0 ≤ m := integral_nonneg fun x => norm_nonneg _
  rw [Real.le_sqrt hm0 (integral_nonneg fun x => sq_nonneg _)]
  have h2 := hg.integrable_sq
  have hvar : 0 ≤ ∫ x, (‖g x‖ - m) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (‖g x‖ - m) ^ 2 = (∫ x, g x ^ 2) - m ^ 2 := by
    have e1 : (fun x => (‖g x‖ - m) ^ 2) = fun x => (g x ^ 2 + (-(2 * m)) * ‖g x‖) + m ^ 2 := by
      funext x; rw [Real.norm_eq_abs]; nlinarith [sq_abs (g x)]
    rw [e1, integral_add (f := fun x => g x ^ 2 + -(2 * m) * ‖g x‖) (g := fun _ => m ^ 2)
      (h2.add (hgi.norm.const_mul _)) (integrable_const _),
      integral_add (f := fun x => g x ^ 2) (g := fun x => -(2 * m) * ‖g x‖) h2
        (hgi.norm.const_mul _), integral_const_mul, integral_const, probReal_univ,
      one_smul]
    ring
  linarith
  all_goals exact hgi.aestronglyMeasurable

/-- The Picard solution of the modified equation is a mild probability solution of (4.7). -/
theorem appAMild_of_linMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ} {A : ℝ}
    (hL : LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A)
    (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1) : AppAMild V W ρ₀ ρ := by
  have hpos : ∀ t, 0 ≤ t → ∀ᵐ x ∂haar d, 0 ≤ ρ t x := fun t ht => hL.ae_nonneg h0 ht
  have hmass : ∀ t, 0 ≤ t → ∫ x, ρ t x ∂haar d = 1 := fun t ht => by
    rw [hL.integral_eq ht, h1]
  refine ⟨fun t ht => ⟨hpos t ht, hmass t ht⟩, fun t ht => ?_, hL.init, fun T => ?_,
    fun t ht => ?_⟩
  · -- continuity in `L¹`
    obtain ⟨K, hK0, hK⟩ := hL.bdd (t + 1)
    have hL2 := hL.tendsto_L2 hK0 hK ⟨ht, by linarith⟩
    have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
      refine mem_of_superset (inter_mem_nhdsWithin (Ici 0) (Iio_mem_nhds (by linarith : t < t + 1)))
        fun s hs => ⟨hs.1, hs.2.le⟩
    have hsq : Tendsto (fun s => ENNReal.ofReal (Real.sqrt (∫ x, (ρ s x - ρ t x) ^ 2)))
        (𝓝[Ici 0] t) (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hL2))
      simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at this
      exact this.mono_left (nhdsWithin_le_of_mem hmem)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [hmem] with s hs
    exact eLpNorm_one_le_sqrt ((hL.memLp_two_section hK hs).sub
      (hL.memLp_two_section hK ⟨ht, by linarith⟩))
  · obtain ⟨K, -, hK⟩ := hL.bdd T
    exact ⟨K, fun t ht => Eventually.of_forall (hK t ht)⟩
  · -- the mild equation with the true flux
    refine Eventually.of_forall fun x => ?_
    rw [hL.mild t ht x]
    congr 1
    unfold duhamel
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    obtain ⟨K, -, hK⟩ := hL.bdd u
    have hui : Integrable (ρ u) (haar d) :=
      appA_integrable_of_abs_le' (hL.measurable_section u) (hK u ⟨hu.1.le, le_rfl⟩)
    exact congrFun (divHeatT_congr_ae fun k =>
      modFlux_ae_eq hyp hui (hpos u hu.1.le) (hmass u hu.1.le) k) x


/-- The constructed solution, with its linear mild structure. -/
theorem exists_appAMild_linMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hm : Measurable ρ₀)
    (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1) (hb : ∃ B, ∀ x, ρ₀ x ≤ B) :
    ∃ ρ : ℝ → Torus d → ℝ, ∃ A : ℝ,
      LinMild ρ₀ ρ (fun u y k => modFlux V W (ρ u) y k) A ∧ AppAMild V W ρ₀ ρ := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨ρ, A, hL⟩ := modMild_linMild hyp hm (M := B) fun x => by
    rw [abs_of_nonneg (h0 x)]; exact hB x
  exact ⟨ρ, A, hL, appAMild_of_linMild hyp hL h0 h1⟩

/-- **Existence** of the mild probability solution of (4.7). -/
theorem exists_appAMild (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hm : Measurable ρ₀)
    (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1) (hb : ∃ B, ∀ x, ρ₀ x ≤ B) :
    ∃ ρ, AppAMild V W ρ₀ ρ := by
  obtain ⟨ρ, A, -, hρ⟩ := exists_appAMild_linMild hyp hm h0 h1 hb
  exact ⟨ρ, hρ⟩

end SharpLSI
