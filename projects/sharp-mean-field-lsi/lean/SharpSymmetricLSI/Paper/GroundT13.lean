import SharpSymmetricLSI.Paper.GroundT12

/-!
# R30 groundwork: change of measure identities and test functions for (7.8)–(7.10)
-/

open MeasureTheory InformationTheory Set Filter Topology Real
open scoped ENNReal NNReal BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- `∫ G dP_N = ∫ p_N G dμ^{⊗N}`. -/
theorem integral_gibbs_eq' (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {N : ℕ} (G : Config N d → ℝ) :
    ∫ X, G X ∂gibbs V W N = ∫ X, rexp (-Ucentered W μ N X) / centeredPartition W μ N * G X
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hm := measurable_Ucentered hyp (μ : Measure (Torus d)) N
  rw [gibbs_eq_centered_aux hyp hμ N, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable fun X : Config N d =>
      ENNReal.ofReal (rexp (-Ucentered W μ N X) / centeredPartition W μ N))
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le
    (centeredPartition_pos hyp (μ : Measure (Torus d)) N).le)]

/-- The weight `w(u) = e^{-u}/K'`. -/
noncomputable def wK (K' u : ℝ) : ℝ := rexp (-u) / K'

theorem wK_pos {K' : ℝ} (hK' : 0 < K') (u : ℝ) : 0 < wK K' u := div_pos (Real.exp_pos _) hK'

theorem continuous_wK (K' : ℝ) : Continuous (wK K') := by unfold wK; fun_prop

theorem div_sqrt_wK {K' : ℝ} (hK' : 0 < K') (x u : ℝ) :
    x * Real.sqrt (wK K' u) / Real.sqrt (wK K' u) = x :=
  mul_div_cancel_right₀ x (Real.sqrt_pos.2 (wK_pos hK' u)).ne'

theorem dens_eq_wK {K K' : ℝ} (hK : 0 < K) (u : ℝ) :
    rexp (-u) / K = K' / K * wK K' u ∨ K' = 0 := by
  rcases eq_or_ne K' 0 with h | h
  · exact Or.inr h
  · left; unfold wK; field_simp

/-- `(ψ, z), u ↦ g(ψ/√w(u), z)`. -/
noncomputable def phiG {J : ℕ} {K' : ℝ} (hK' : 0 < K') (g : ℝ × (Fin J → ℝ) →ᵇ ℝ) :
    (ℝ × (Fin J → ℝ)) × ℝ →ᵇ ℝ :=
  g.compContinuous ⟨fun t => (t.1.1 / Real.sqrt (wK K' t.2), t.1.2), by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_fst.comp continuous_fst).div
      (Real.continuous_sqrt.comp ((continuous_wK K').comp continuous_snd))
      fun t => (Real.sqrt_pos.2 (wK_pos hK' _)).ne'⟩

theorem phiG_apply {J : ℕ} {K' : ℝ} (hK' : 0 < K') (g : ℝ × (Fin J → ℝ) →ᵇ ℝ)
    (t : (ℝ × (Fin J → ℝ)) × ℝ) : phiG hK' g t = g (t.1.1 / Real.sqrt (wK K' t.2), t.1.2) := rfl

/-- Rearranging `(ψ, u, z)` into `((ψ, z), u)`. -/
noncomputable def rearr {J : ℕ} (G : (ℝ × (Fin J → ℝ)) × ℝ →ᵇ ℝ) : ℝ × ℝ × (Fin J → ℝ) →ᵇ ℝ :=
  G.compContinuous ⟨fun t => ((t.1, t.2.2), t.2.1), by fun_prop⟩

theorem rearr_apply {J : ℕ} (G : (ℝ × (Fin J → ℝ)) × ℝ →ᵇ ℝ) (ψ u : ℝ) (z : Fin J → ℝ) :
    rearr G (ψ, u, z) = G ((ψ, z), u) := rfl

/-- The clipping `x ↦ max(-M, min(x, M))`. -/
noncomputable def clipB (M : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => max (-|M|) (min x |M|), by fun_prop⟩ (2 * |M|)
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have h1 : |max (-|M|) (min a |M|)| ≤ |M| := abs_le.2 ⟨le_max_left _ _,
        max_le (by linarith [abs_nonneg M]) (min_le_right _ _)⟩
      have h2 : |max (-|M|) (min b |M|)| ≤ |M| := abs_le.2 ⟨le_max_left _ _,
        max_le (by linarith [abs_nonneg M]) (min_le_right _ _)⟩
      have := abs_sub (max (-|M|) (min a |M|)) (max (-|M|) (min b |M|))
      linarith

theorem clipB_apply (M x : ℝ) : clipB M x = max (-|M|) (min x |M|) := rfl

theorem abs_sub_clipB_le {M : ℝ} (hM : 0 < M) (x : ℝ) : |x - clipB M x| ≤ x ^ 2 / M := by
  rw [clipB_apply, abs_of_pos hM]
  rcases le_or_gt |x| M with h | h
  · rw [abs_le] at h
    rw [min_eq_left h.2, max_eq_right h.1, sub_self, abs_zero]; positivity
  · have hx : |x| ≤ x ^ 2 / M := by
      rw [le_div_iff₀ hM, ← sq_abs]; nlinarith [abs_nonneg x]
    refine le_trans ?_ hx
    rcases le_or_gt 0 x with hx0 | hx0
    · rw [abs_of_nonneg hx0] at h
      rw [min_eq_right h.le, max_eq_right (by linarith), abs_of_nonneg (by linarith),
        abs_of_nonneg hx0]; linarith
    · rw [abs_of_neg hx0] at h
      rw [min_eq_left (by linarith), max_eq_left (by linarith), abs_of_neg (by linarith),
        abs_of_neg hx0]; linarith

end SharpLSI
