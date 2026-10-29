import SharpSymmetricLSI.Paper.ParticleForce
import SharpSymmetricLSI.Paper.SubGaussSq
import SharpSymmetricLSI.Paper.GibbsVariational

/-!
# (5.13): the exponential force bound (Phase 3, lane D; R20)

`∫ exp(a₀|∇U_N|²) dμ^{⊗N} ≤ C` uniformly in `N`. By (5.12), `∇ᵢU_N = N⁻¹(Sᵢ - β(Xᵢ))` with
`Sᵢ = ∑_{l≠i} (∇₁W(Xᵢ,X_l) - β(Xᵢ))`, whose summands are, given `Xᵢ`, independent, centered
and bounded. Jensen over `(i,k)` reduces to one coordinate, and `lintegral_exp_sq_sum_le`
bounds each.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem pi_ac_volume {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hac : μ ≪ haar d) (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ) ≪ (volume : Measure (Config N d)) := by
  set f := densOf μ
  have hρ : (haar d).withDensity (fun x => ENNReal.ofReal (f x)) = μ := by
    conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ (haar d) hac]
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ (haar d)] with x hx
    simp only [f, densOf, ENNReal.ofReal_toReal hx.ne]
  have hpi := pi_withDensity_ofReal (N := N) (measurable_densOf μ)
    (fun x => ENNReal.toReal_nonneg) (integrable_densOf μ)
  rw [hρ] at hpi
  rw [hpi]; exact withDensity_absolutelyContinuous _ _

/-- One coordinate: `E exp(c Sᵢ²/N) ≤ ∫ e^{g²/4} dγ` (condition on `Xᵢ`). -/
theorem lintegral_exp_Sik (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (n : ℕ)
    (i : Fin (n + 1)) {F : Torus d → Torus d → ℝ} (hF : Measurable (Function.uncurry F)) {M : ℝ}
    (hFb : ∀ x y, |F x y| ≤ M) (hF0 : ∀ x, ∫ y, F x y ∂μ = 0) {c : ℝ} (hc0 : 0 ≤ c)
    (hcM : c * M ^ 2 ≤ 1 / 4) :
    ∫⁻ X, ENNReal.ofReal (exp (c * (∑ l ∈ Finset.univ.erase i, F (X i) (X l)) ^ 2 /
      ((n + 1 : ℕ) : ℝ))) ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤ gaussSqConst := by
  set G : Torus d × (Fin n → Torus d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (exp (c * (∑ l, F p.1 (p.2 l)) ^ 2 / (n + 1))) with hG
  have hGm : Measurable G := by
    refine ENNReal.measurable_ofReal.comp (measurable_exp.comp ?_)
    refine ((measurable_const.mul ((Finset.measurable_sum _ fun l _ => ?_).pow_const 2)).div_const _)
    exact hF.comp (measurable_fst.prodMk ((measurable_pi_apply l).comp measurable_snd))
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have e : ∀ X : Fin (n + 1) → Torus d,
      ENNReal.ofReal (exp (c * (∑ l ∈ Finset.univ.erase i, F (X i) (X l)) ^ 2 /
        ((n + 1 : ℕ) : ℝ))) = G (MeasurableEquiv.piFinSuccAbove (fun _ => Torus d) i X) := by
    intro X
    simp only [hG]
    have hs : ∑ l ∈ Finset.univ.erase i, F (X i) (X l) = ∑ l : Fin n, F (X i) (X (i.succAbove l)) := by
      have := Fin.sum_univ_succAbove (fun l => F (X i) (X l)) i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
      linarith
    rw [hs]
    push_cast
    rfl
  simp_rw [e]
  rw [hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), lintegral_prod _
    hGm.aemeasurable]
  calc ∫⁻ x, ∫⁻ Z, G (x, Z) ∂(Measure.pi fun _ : Fin n => μ) ∂μ ≤ ∫⁻ _, gaussSqConst ∂μ :=
        lintegral_mono fun x => lintegral_exp_sq_sum_le μ n (hF.comp measurable_prodMk_left)
          (hFb x) (hF0 x) hc0 hcM
    _ = gaussSqConst := by simp

/-- (5.12) in closed form, a.e. under `μ^{⊗N}`. -/
theorem weakGradC_Ucentered_ae (hyp : Hyp V W KV KW) {μ : Measure (Torus d)}
    [IsProbabilityMeasure μ] (hac : μ ≪ haar d) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i k, weakGradC (Ucentered W μ N) X i k =
      (N : ℝ)⁻¹ * ((∑ l ∈ Finset.univ.erase i, (bGrad W (X i) (X l) k -
        bForceL W (densOf μ) (X i) k)) + -bForceL W (densOf μ) (X i) k) := by
  have hflat : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have hU := hflat.quasiMeasurePreserving.ae (weakGrad_ae_eq (isWeakGrad_Ucentered hyp hac
    (N := N)))
  filter_upwards [pi_ac_volume hac N |>.ae_le hU] with X hX i k
  have e0 : weakGradC (Ucentered W μ N) X i k =
      weakGrad (Ucentered W μ N ∘ unflat) (flat X) (i, k) := rfl
  rw [e0, congrFun hX (i, k), GUsum_flat hyp hN]

/-- The pointwise Jensen step: `exp(a₀ ∑ᵢₖ (N⁻¹(S - b))²) ≤ e^{c₀} · avg exp(2a₀d S²/N)`. -/
theorem exp_gradSq_le {n d : ℕ} (hd : 1 ≤ d) {a₀ Cβ : ℝ} (ha₀ : 0 ≤ a₀)
    (Sv bv : Fin (n + 1) → Fin d → ℝ) (hb : ∀ i k, |bv i k| ≤ Cβ) :
    exp (a₀ * ∑ i, ∑ k, (((n + 1 : ℕ) : ℝ)⁻¹ * (Sv i k + -bv i k)) ^ 2) ≤
      exp (2 * a₀ * d * Cβ ^ 2) * ∑ q : Fin (n + 1) × Fin d,
        (1 / (((n + 1 : ℕ) : ℝ) * d)) * exp (2 * a₀ * d * Sv q.1 q.2 ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  set Nr : ℝ := ((n + 1 : ℕ) : ℝ) with hNr
  have hNr1 : (1 : ℝ) ≤ Nr := by rw [hNr]; exact_mod_cast Nat.succ_pos n
  have hNr0 : 0 < Nr := by linarith
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hsq : ∀ i k, (Nr⁻¹ * (Sv i k + -bv i k)) ^ 2 ≤
      (Nr ^ 2)⁻¹ * (2 * Sv i k ^ 2 + 2 * Cβ ^ 2) := fun i k => by
    have hb2 : bv i k ^ 2 ≤ Cβ ^ 2 := by
      have := hb i k
      have h0 := abs_nonneg (bv i k)
      nlinarith [sq_abs (bv i k)]
    rw [mul_pow, inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith [sq_nonneg (Sv i k + bv i k)]
  have hgrad : a₀ * ∑ i, ∑ k, (Nr⁻¹ * (Sv i k + -bv i k)) ^ 2 ≤
      ∑ q : Fin (n + 1) × Fin d, (1 / (Nr * d)) * (2 * a₀ * d * Sv q.1 q.2 ^ 2 / Nr) +
        2 * a₀ * d * Cβ ^ 2 := by
    have h1 : a₀ * ∑ i, ∑ k, (Nr⁻¹ * (Sv i k + -bv i k)) ^ 2 ≤
        a₀ * ∑ i : Fin (n + 1), ∑ k : Fin d, (Nr ^ 2)⁻¹ * (2 * Sv i k ^ 2 + 2 * Cβ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum
        fun k _ => hsq i k) ha₀
    have h2 : a₀ * ∑ i : Fin (n + 1), ∑ k : Fin d, (Nr ^ 2)⁻¹ * (2 * Sv i k ^ 2 + 2 * Cβ ^ 2) =
        ∑ q : Fin (n + 1) × Fin d, (1 / (Nr * d)) * (2 * a₀ * d * Sv q.1 q.2 ^ 2 / Nr) +
          2 * a₀ * d * Cβ ^ 2 * (1 / Nr) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      have hcard : ∑ i : Fin (n + 1), ∑ k : Fin d, (Nr ^ 2)⁻¹ * (2 * Cβ ^ 2) =
          Nr * d * ((Nr ^ 2)⁻¹ * (2 * Cβ ^ 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hNr]
        push_cast; ring
      have e : ∀ i : Fin (n + 1), a₀ * ∑ k : Fin d, (Nr ^ 2)⁻¹ * (2 * Sv i k ^ 2 + 2 * Cβ ^ 2) =
          ∑ k : Fin d, (1 / (Nr * d)) * (2 * a₀ * d * Sv i k ^ 2 / Nr) +
            a₀ * ∑ k : Fin d, (Nr ^ 2)⁻¹ * (2 * Cβ ^ 2) := fun i => by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
      rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, ← Finset.mul_sum, hcard]
      congr 1
      field_simp
    have h3 : 2 * a₀ * d * Cβ ^ 2 * (1 / Nr) ≤ 2 * a₀ * d * Cβ ^ 2 := by
      have : 0 ≤ 2 * a₀ * d * Cβ ^ 2 := by positivity
      calc 2 * a₀ * d * Cβ ^ 2 * (1 / Nr) ≤ 2 * a₀ * d * Cβ ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left ((div_le_one hNr0).mpr hNr1) this
        _ = _ := mul_one _
    linarith
  have hw1 : ∑ _q : Fin (n + 1) × Fin d, (1 / (Nr * d)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, nsmul_eq_mul, hNr]
    push_cast
    field_simp
  have hJ := (convexOn_exp).map_sum_le (t := Finset.univ) (w := fun _ : Fin (n + 1) × Fin d =>
    1 / (Nr * d)) (p := fun q => 2 * a₀ * d * Sv q.1 q.2 ^ 2 / Nr) (fun _ _ => by positivity) hw1
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  calc exp (a₀ * ∑ i, ∑ k, (Nr⁻¹ * (Sv i k + -bv i k)) ^ 2)
      ≤ exp (∑ q : Fin (n + 1) × Fin d, (1 / (Nr * d)) * (2 * a₀ * d * Sv q.1 q.2 ^ 2 / Nr) +
          2 * a₀ * d * Cβ ^ 2) := exp_le_exp.mpr hgrad
    _ = exp (2 * a₀ * d * Cβ ^ 2) * exp (∑ q : Fin (n + 1) × Fin d,
          (1 / (Nr * d)) * (2 * a₀ * d * Sv q.1 q.2 ^ 2 / Nr)) := by rw [exp_add, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hJ (exp_pos _).le

theorem measurable_exp_Sik {n : ℕ} {F : Torus d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) (i : Fin (n + 1)) (c D : ℝ) :
    Measurable fun X : Fin (n + 1) → Torus d =>
      ENNReal.ofReal (exp (c * (∑ l ∈ Finset.univ.erase i, F (X i) (X l)) ^ 2 / D)) := by
  have h1 : Measurable fun X : Fin (n + 1) → Torus d => ∑ l ∈ Finset.univ.erase i, F (X i) (X l) :=
    Finset.measurable_sum _ fun l _ => by
      have hp : Measurable fun X : Fin (n + 1) → Torus d => (X i, X l) := by fun_prop
      exact hF.comp hp
  exact ENNReal.measurable_ofReal.comp (measurable_exp.comp
    ((measurable_const.mul (h1.pow_const 2)).div_const D))

/-- **(5.13)**: `∫ exp(a₀|∇U_N|²) dμ^{⊗N} ≤ C`, uniformly in `N`. -/
theorem force_exp_moment (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ENNReal.ofReal (exp (a₀ * gradSqC (Ucentered W μ N) X))
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ ENNReal.ofReal C := by
  have hac := minimizer_ac hyp hμ
  obtain ⟨-, hβm, ⟨Cβ, hCβ⟩, hβint⟩ := forceMean_props hyp hac
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  obtain ⟨M, hM⟩ : ∃ M, M = Cb + Cβ := ⟨_, rfl⟩
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℝ, a₀ = 1 / (8 * d * (M ^ 2 + 1)) := ⟨_, rfl⟩
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have hc0 : 0 ≤ 2 * a₀ * d := by positivity
  have hcM : 2 * a₀ * d * M ^ 2 ≤ 1 / 4 := by
    rw [ha₀]
    have h1 : 0 < M ^ 2 + 1 := by positivity
    rw [show 2 * (1 / (8 * d * (M ^ 2 + 1))) * d * M ^ 2 = M ^ 2 / (4 * (M ^ 2 + 1)) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]; nlinarith
  refine ⟨a₀, exp (2 * a₀ * d * Cβ ^ 2) * gaussSqConst.toReal, ha₀0, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hNr0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hd0 : (0 : ℝ) < d := by linarith
  -- the centered one-particle summands
  have hFm : ∀ k, Measurable (Function.uncurry fun x y =>
      bGrad W x y k - bForceL W (densOf (μ : Measure (Torus d))) x k) := fun k =>
    (measurable_bGrad hyp (W := W) k).sub ((hβm k).comp measurable_fst)
  have hFb : ∀ k x y, |bGrad W x y k - bForceL W (densOf (μ : Measure (Torus d))) x k| ≤ M :=
    fun k x y => by rw [hM]; exact (abs_sub _ _).trans (add_le_add (hCb x y k) (hCβ x k))
  have hF0 : ∀ k x, ∫ y, (bGrad W x y k - bForceL W (densOf (μ : Measure (Torus d))) x k)
      ∂(μ : Measure (Torus d)) = 0 := fun k x => by
    have hbi : Integrable (fun y => bGrad W x y k) (μ : Measure (Torus d)) :=
      Integrable.of_bound ((measurable_bGrad hyp (W := W) k).comp measurable_prodMk_left
        ).aestronglyMeasurable Cb (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hCb x y k)
    rw [integral_sub hbi (integrable_const _), integral_const, hβint x k]
    simp
  have hSm : ∀ q : Fin (n + 1) × Fin d, Measurable fun X : Fin (n + 1) → Torus d =>
      ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1,
        (bGrad W (X q.1) (X l) q.2 - bForceL W (densOf (μ : Measure (Torus d))) (X q.1) q.2)) ^ 2 /
          ((n + 1 : ℕ) : ℝ))) := fun q =>
    measurable_exp_Sik (F := fun x y => bGrad W x y q.2 -
      bForceL W (densOf (μ : Measure (Torus d))) x q.2) (hFm q.2) q.1 _ _
  have hw1 : ∑ _q : Fin (n + 1) × Fin d, ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) = 1 := by
    have hr : ∑ _q : Fin (n + 1) × Fin d, (1 / (((n + 1 : ℕ) : ℝ) * d)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      field_simp
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), hr, ENNReal.ofReal_one]
  have hae := weakGradC_Ucentered_ae hyp hac (N := n + 1) hN
  calc ∫⁻ X, ENNReal.ofReal (exp (a₀ * gradSqC (Ucentered W μ (n + 1)) X))
        ∂Measure.pi (fun _ : Fin (n + 1) => (μ : Measure (Torus d)))
      ≤ ∫⁻ X, ENNReal.ofReal (exp (2 * a₀ * d * Cβ ^ 2)) * ∑ q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) *
          ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1,
            (bGrad W (X q.1) (X l) q.2 - bForceL W (densOf (μ : Measure (Torus d))) (X q.1) q.2)) ^ 2 /
              ((n + 1 : ℕ) : ℝ))) ∂Measure.pi (fun _ : Fin (n + 1) => (μ : Measure (Torus d))) := by
        refine lintegral_mono_ae (hae.mono fun X hX => ?_)
        have hg : gradSqC (Ucentered W μ (n + 1)) X = ∑ i, ∑ k, (((n + 1 : ℕ) : ℝ)⁻¹ *
            ((∑ l ∈ Finset.univ.erase i, (bGrad W (X i) (X l) k -
              bForceL W (densOf (μ : Measure (Torus d))) (X i) k)) +
              -bForceL W (densOf (μ : Measure (Torus d))) (X i) k)) ^ 2 := by
          unfold gradSqC; simp_rw [hX]
        rw [hg]
        refine (ENNReal.ofReal_le_ofReal (exp_gradSq_le hd ha₀0.le _ _ fun i k => hCβ (X i) k)).trans
          (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (exp_pos _).le, ENNReal.ofReal_sum_of_nonneg
          (fun q _ => by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (exp (2 * a₀ * d * Cβ ^ 2)) * ∑ q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) *
          ∫⁻ X, ENNReal.ofReal (exp (2 * a₀ * d * (∑ l ∈ Finset.univ.erase q.1,
            (bGrad W (X q.1) (X l) q.2 - bForceL W (densOf (μ : Measure (Torus d))) (X q.1) q.2)) ^ 2 /
              ((n + 1 : ℕ) : ℝ))) ∂Measure.pi (fun _ : Fin (n + 1) => (μ : Measure (Torus d))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum' _ fun q _ =>
          ((hSm q).const_mul _).aemeasurable]
        congr 1
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (exp (2 * a₀ * d * Cβ ^ 2)) * ∑ _q : Fin (n + 1) × Fin d,
          ENNReal.ofReal (1 / (((n + 1 : ℕ) : ℝ) * d)) * gaussSqConst := by
        gcongr with q
        exact lintegral_exp_Sik (μ : Measure (Torus d)) n q.1 (hFm q.2) (hFb q.2) (hF0 q.2) hc0 hcM
    _ = ENNReal.ofReal (exp (2 * a₀ * d * Cβ ^ 2) * gaussSqConst.toReal) := by
        rw [← Finset.sum_mul, hw1, one_mul, ENNReal.ofReal_mul (exp_pos _).le,
          ENNReal.ofReal_toReal gaussSqConst_ne_top]

end SharpLSI
