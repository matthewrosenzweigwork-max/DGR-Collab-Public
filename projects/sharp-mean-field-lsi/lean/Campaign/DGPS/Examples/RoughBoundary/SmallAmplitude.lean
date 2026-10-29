import DGPS.Examples.RoughBoundary.KernelConvergence
import DGPS.Examples.RoughBoundary.SpikesModulus

/-!
# Strong small amplitude convergence at every fixed exponent (SEM013)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 8.4.

With the common primitive `g = gT` of RUF002, `U_ε = Feature.Ufeat L ε`, `U_0 = Feature.Ufeat L 0`
(the smooth base) and `W_ε = Model.modelW L ε`, the feature difference is the phase difference of
SEM005 with profiles `f = 0`, `g2 = g`, amplitude `η = ε`, i.e. `d = ε g(6·)`.  Then

* `‖U_ε - U_0‖_∞ ≤ 2π|ε| ‖g‖_∞`;
* `[U_ε - U_0]_α ≤ 2π|ε| (6^α [g]_α + ‖g‖_∞ [U_0]_α)` for `0 < α < 1`;
* `‖U_ε' - U_0'‖_p ≤ |ε| (12π ‖g'‖_p + 4π² ‖g‖_∞ ‖b_L'‖_p)` for `1 ≤ p < 2`, where
  `b_L' = θ_0' = 2 Q_L(2·)` is the phase derivative of the base (`Feature.dthetaT L 0`);

and, by the product kernel estimates of SEM006, `W_ε → W_0` with norm `O(|ε|)` in every fixed
`C^α` (`0 < α < 1`, for `|ε| ≤ 1`) and `W^{1,p}` (`1 ≤ p < 2`).
-/

open MeasureTheory Set
open scoped Real ENNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Analysis.RateTopology (q1 q2)
open DGPS.Analysis.PeriodicMollification (TorusHolderBdd torusHolderSeminorm torusSupNorm
  torusHolderSeminorm_nonneg torusSupNorm_nonneg continuous_of_holderBdd)

/-! ### Reduction to profile `0` -/

lemma UfeatF_zero (L η : ℝ) : UfeatF L η (fun _ => (0 : ℝ)) = Feature.Ufeat L 0 := by
  funext y
  unfold UfeatF Feature.Ufeat UrealF Feature.Ureal thetaF Feature.theta
  simp

lemma dthetaTF_zero (L η : ℝ) : dthetaTF L η (fun _ => (0 : ℝ)) = Feature.dthetaT L 0 := by
  funext y
  rw [Feature.dthetaT_eq']
  simp [dthetaTF]

lemma UprimeF_zero (L η : ℝ) :
    UprimeF L η (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) = Feature.Uprime L 0 := by
  funext y
  unfold UprimeF Feature.Uprime
  rw [dthetaTF_zero, UfeatF_zero]

lemma Efun_zero (L η : ℝ) :
    Efun L η (fun _ => (0 : ℝ)) Spikes.gT =
      fun y => Feature.Ufeat L η y - Feature.Ufeat L 0 y := by
  funext y
  unfold Efun
  rw [UfeatF_zero]
  rfl

lemma holder_gT {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : TorusHolderBdd α Spikes.gT := by
  refine ⟨max (Spikes.modulusConst * Real.exp (2 / (3 * Real.sqrt (3 * (1 - α)))))
    (2 * Spikes.hMean * Real.exp (8 * α)), ?_, fun x y =>
    Spikes.explicit_sub_lipschitz_modulus_and_every_strict_holder_exponent.2.2 α h0 h1 x y⟩
  exact le_max_of_le_right (by have := Spikes.hMean_pos; positivity)

lemma holder_zero (α : ℝ) : TorusHolderBdd α (fun _ => (0 : ℝ)) :=
  ⟨0, le_rfl, fun x y => by simp⟩

lemma continuous_gT : Continuous Spikes.gT := continuous_of_holderBdd (by norm_num : (0 : ℝ) < 1 / 2)
  (holder_gT (by norm_num) (by norm_num))

lemma aesm_gT : AEStronglyMeasurable Spikes.gT (DGPS.haar 1) :=
  continuous_gT.aestronglyMeasurable

lemma aesm_gprime : AEStronglyMeasurable (fun y => Spikes.hSum y - Spikes.hMean) (DGPS.haar 1) :=
  (Spikes.hSum_meas.sub measurable_const).aestronglyMeasurable

lemma torusSupNorm_gT_sub : torusSupNorm (fun y => Spikes.gT y - (fun _ => (0 : ℝ)) y) =
    torusSupNorm Spikes.gT := by
  simp

lemma torusHolderSeminorm_gT_sub (α : ℝ) :
    torusHolderSeminorm α (fun y => Spikes.gT y - (fun _ => (0 : ℝ)) y) =
      torusHolderSeminorm α Spikes.gT := by
  simp

/-! ### The three feature bounds -/

theorem feature_bounds {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    vecSupNorm (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
      2 * π * |ε| * torusSupNorm Spikes.gT ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      vecHolderSeminorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
        2 * π * |ε| * (6 ^ α * torusHolderSeminorm α Spikes.gT +
          torusSupNorm Spikes.gT * vecHolderSeminorm α (Feature.Ufeat L 0))) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      eLpNorm (fun y => Feature.Uprime L ε y - Feature.Uprime L 0 y) (ENNReal.ofReal p)
          (DGPS.haar 1) ≤
        ENNReal.ofReal |ε| *
          (ENNReal.ofReal (12 * π) *
              eLpNorm (fun y => Spikes.hSum y - Spikes.hMean) (ENNReal.ofReal p) (DGPS.haar 1) +
            ENNReal.ofReal (4 * π ^ 2 * torusSupNorm Spikes.gT) *
              eLpNorm (Feature.dthetaT L 0) (ENNReal.ofReal p) (DGPS.haar 1))) := by
  have H := quantitative_phase_composition_continuity hL ε
  have hS : vecSupNorm (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
      2 * π * |ε| * torusSupNorm Spikes.gT := by
    obtain ⟨h1, h2⟩ := H.1 (fun _ => (0 : ℝ)) Spikes.gT continuous_const continuous_gT
    rw [Efun_zero] at h1
    rw [h2, torusSupNorm_gT_sub] at h1
    linarith
  refine ⟨hS, fun α h0 h1 => ?_, fun p hp hp2 => ?_⟩
  · obtain ⟨hA, hB⟩ := H.2.1 α h0 h1 (fun _ => (0 : ℝ)) Spikes.gT (holder_zero α) (holder_gT h0 h1)
    obtain ⟨hC, hD⟩ := H.1 (fun _ => (0 : ℝ)) Spikes.gT continuous_const continuous_gT
    rw [Efun_zero, UfeatF_zero] at hA
    rw [torusHolderSeminorm_gT_sub] at hB
    rw [hD, torusSupNorm_gT_sub] at hA
    have hS0 := torusSupNorm_nonneg Spikes.gT
    have hK0 := torusHolderSeminorm_nonneg α Spikes.gT
    have hU0 := vecHolderSeminorm_nonneg α (Feature.Ufeat L 0)
    have hpi : 0 < π := Real.pi_pos
    calc _ ≤ _ := hA
      _ ≤ 2 * π * (|ε| * 6 ^ α * torusHolderSeminorm α Spikes.gT +
            |ε| * torusSupNorm Spikes.gT * vecHolderSeminorm α (Feature.Ufeat L 0)) := by
          gcongr
      _ = _ := by ring
  · set P := ENNReal.ofReal p with hP
    have hP1 : 1 ≤ P := by
      rw [hP]; exact ENNReal.one_le_ofReal.2 hp
    obtain ⟨hA, hB⟩ := (H.2.2.2 P hP1 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) Spikes.gT
      (fun y => Spikes.hSum y - Spikes.hMean))
    have hA' := hA aestronglyMeasurable_const aesm_gT aestronglyMeasurable_const aesm_gprime
    have hB' := hB (by simpa using aesm_gprime)
    rw [UprimeF_zero, dthetaTF_zero, UprimeF_gT] at hA'
    rw [Efun_zero] at hA'
    have hB'' : eLpNorm (phaseDiffDeriv ε (fun _ => (0 : ℝ)) (fun y => Spikes.hSum y - Spikes.hMean))
        P (DGPS.haar 1) = ENNReal.ofReal (6 * |ε|) *
          eLpNorm (fun y => Spikes.hSum y - Spikes.hMean) P (DGPS.haar 1) := by
      rw [hB']; simp
    rw [hB''] at hA'
    have hpi : 0 < π := Real.pi_pos
    have hS0 := torusSupNorm_nonneg Spikes.gT
    have e1 : ENNReal.ofReal (2 * π) * ENNReal.ofReal (6 * |ε|) =
        ENNReal.ofReal |ε| * ENNReal.ofReal (12 * π) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1; ring
    have e2 : ENNReal.ofReal (2 * π * (2 * π * |ε| * torusSupNorm Spikes.gT)) =
        ENNReal.ofReal |ε| * ENNReal.ofReal (4 * π ^ 2 * torusSupNorm Spikes.gT) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1; ring
    have hle : ENNReal.ofReal (2 * π * vecSupNorm
        (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y)) ≤
        ENNReal.ofReal (2 * π * (2 * π * |ε| * torusSupNorm Spikes.gT)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hS (by positivity))
    calc _ ≤ _ := hA'
      _ ≤ ENNReal.ofReal (2 * π) * (ENNReal.ofReal (6 * |ε|) *
            eLpNorm (fun y => Spikes.hSum y - Spikes.hMean) P (DGPS.haar 1)) +
          ENNReal.ofReal (2 * π * (2 * π * |ε| * torusSupNorm Spikes.gT)) *
            eLpNorm (Feature.dthetaT L 0) P (DGPS.haar 1) := by gcongr
      _ = _ := by rw [← mul_assoc, e1, e2]; ring


/-! ### Hölder seminorm bookkeeping -/

lemma vecHolderBdd_sub' {β : ℝ} {F G : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hF : VecHolderBdd β F) (hG : VecHolderBdd β G) : VecHolderBdd β (fun z => F z - G z) := by
  obtain ⟨C1, hC1, h1⟩ := hF
  obtain ⟨C2, hC2, h2⟩ := hG
  refine ⟨C1 + C2, add_nonneg hC1 hC2, fun a b => ?_⟩
  have e : (F a - G a) - (F b - G b) = (F a - F b) - (G a - G b) := by abel
  rw [e]
  calc _ ≤ ‖F a - F b‖ + ‖G a - G b‖ := norm_sub_le _ _
    _ ≤ _ := by have := h1 a b; have := h2 a b; linarith

lemma vecHolderSeminorm_add_le' {β : ℝ} {F G : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hF : VecHolderBdd β F) (hG : VecHolderBdd β G) :
    vecHolderSeminorm β (fun z => F z + G z) ≤ vecHolderSeminorm β F + vecHolderSeminorm β G := by
  refine vecHolderSeminorm_le (add_nonneg (vecHolderSeminorm_nonneg _ _)
    (vecHolderSeminorm_nonneg _ _)) fun x y => ?_
  have e : (F x + G x) - (F y + G y) = (F x - F y) + (G x - G y) := by abel
  rw [e]
  calc _ ≤ ‖F x - F y‖ + ‖G x - G y‖ := norm_add_le _ _
    _ ≤ _ := by
      have := hF.norm_sub_le x y
      have := hG.norm_sub_le x y
      linarith

lemma dthetaT_zero_eq (L : ℝ) : Feature.dthetaT L 0 = fun y => 2 * Feature.Q2 L y := by
  funext y; rw [Feature.dthetaT_eq']; simp

/-! ### Product kernel convergence -/

theorem kernel_holder_bound {L : ℝ} (hL : 0 < L) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ 1 →
      prodHolderNorm α (fun x y => Model.modelW L ε x y - Model.modelW L 0 x y) ≤ C * |ε| := by
  set S0 := torusSupNorm Spikes.gT with hS0d
  set K := torusHolderSeminorm α Spikes.gT with hKd
  set u0 := vecHolderSeminorm α (Feature.Ufeat L 0) with hu0d
  have hS0 : 0 ≤ S0 := torusSupNorm_nonneg _
  have hK : 0 ≤ K := torusHolderSeminorm_nonneg _ _
  have hu0 : 0 ≤ u0 := vecHolderSeminorm_nonneg _ _
  have hk := kappa_nonneg
  have hpi : 0 < π := Real.pi_pos
  have h6 : (0 : ℝ) ≤ 6 ^ α := by positivity
  set B1 := 2 * π * (S0 + 6 ^ α * K + S0 * u0) with hB1d
  have hB1 : 0 ≤ B1 := by positivity
  set N0 := 1 + u0 with hN0d
  have hN0 : 0 ≤ N0 := by positivity
  refine ⟨Model.kappa * (2 * N0 + B1) * B1, by positivity, fun ε hε => ?_⟩
  have hUe : VecHolderBdd α (Feature.Ufeat L ε) := holder_UfeatF hL ε h0 h1 (holder_gT h0 h1)
  have hU0 : VecHolderBdd α (Feature.Ufeat L 0) := by
    have := holder_UfeatF hL 0 h0 h1 (holder_zero α)
    rwa [UfeatF_zero] at this
  have hE : VecHolderBdd α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) :=
    vecHolderBdd_sub' hUe hU0
  obtain ⟨hsup, hhol, -⟩ := feature_bounds hL ε
  have hhol := hhol α h0 h1
  have hε0 := abs_nonneg ε
  have hsE : vecHolderSeminorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
      |ε| * B1 := by
    have hhol' : vecHolderSeminorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
        2 * π * |ε| * (6 ^ α * K + S0 * u0) := hhol
    have hx : 0 ≤ |ε| * (2 * π * S0) := by positivity
    refine hhol'.trans ?_
    rw [hB1d]
    nlinarith [hx]
  have hsup' : vecSupNorm (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
      |ε| * (2 * π * S0) := by
    refine hsup.trans (le_of_eq ?_); ring
  have hEn : vecHolderNorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤ |ε| * B1 := by
    unfold vecHolderNorm
    have : |ε| * (2 * π * S0) + |ε| * (2 * π * (6 ^ α * K + S0 * u0)) = |ε| * B1 := by
      rw [hB1d]; ring
    have hhol' : vecHolderSeminorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
        |ε| * (2 * π * (6 ^ α * K + S0 * u0)) := by
      refine hhol.trans (le_of_eq ?_); simp only [hS0d, hKd, hu0d]; ring
    exact (add_le_add hsup' hhol').trans (le_of_eq this)
  have hEn' : vecHolderNorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤ B1 :=
    hEn.trans (by nlinarith)
  have hEnn : 0 ≤ vecHolderNorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) :=
    add_nonneg (vecSupNorm_nonneg _) (vecHolderSeminorm_nonneg _ _)
  have hUeS : vecHolderSeminorm α (Feature.Ufeat L ε) ≤ B1 + u0 := by
    have hdec : Feature.Ufeat L ε = fun y =>
        (Feature.Ufeat L ε y - Feature.Ufeat L 0 y) + Feature.Ufeat L 0 y := by
      funext y; abel
    rw [hdec]
    refine (vecHolderSeminorm_add_le' hE hU0).trans ?_
    have : |ε| * B1 ≤ B1 := by nlinarith
    linarith
  have hnU : ∀ y, ‖Feature.Ufeat L ε y‖ = 1 := norm_UfeatF L ε Spikes.gT
  have hnU0 : ∀ y, ‖Feature.Ufeat L 0 y‖ = 1 := norm_UfeatF L 0 Spikes.gT
  have key := (quantitative_product_kernel_convergence (U := Feature.Ufeat L 0)
    (Ut := Feature.Ufeat L ε) (U' := fun _ => 0) (Ut' := fun _ => 0) hnU0 hnU).1 α h0 hU0 hUe
  have h3 := key.2.2.1
  have hvU : vecHolderNorm α (Feature.Ufeat L ε) ≤ B1 + N0 := by
    unfold vecHolderNorm; rw [vecSupNorm_unit hnU]; linarith
  have hvU0 : vecHolderNorm α (Feature.Ufeat L 0) = N0 := by
    unfold vecHolderNorm; rw [vecSupNorm_unit hnU0]
  have hvUn : 0 ≤ vecHolderNorm α (Feature.Ufeat L ε) :=
    add_nonneg (vecSupNorm_nonneg _) (vecHolderSeminorm_nonneg _ _)
  show prodHolderNorm α (fun x y => prodKernel (Feature.Ufeat L ε) x y -
    prodKernel (Feature.Ufeat L 0) x y) ≤ _
  refine h3.trans ?_
  rw [hvU0]
  calc Model.kappa * (vecHolderNorm α (Feature.Ufeat L ε) + N0) *
        vecHolderNorm α (fun z => Feature.Ufeat L ε z - Feature.Ufeat L 0 z)
      ≤ Model.kappa * (B1 + N0 + N0) * (|ε| * B1) := by
        gcongr
    _ = _ := by ring


theorem kernel_sobolev_bound {L : ℝ} (hL : 0 < L) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε : ℝ,
      eLpNorm (fun z : Torus 2 => prodKernel (Feature.Ufeat L ε) (q1 z) (q2 z) -
          prodKernel (Feature.Ufeat L 0) (q1 z) (q2 z)) (ENNReal.ofReal p) (DGPS.haar 2) ≤
        C * ENNReal.ofReal |ε| ∧
      eLpNorm (fun z : Torus 2 => prodGradX (Feature.Ufeat L ε) (Feature.Uprime L ε) (q1 z) (q2 z) -
          prodGradX (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z))
          (ENNReal.ofReal p) (DGPS.haar 2) ≤ C * ENNReal.ofReal |ε| ∧
      eLpNorm (fun z : Torus 2 => prodGradY (Feature.Ufeat L ε) (Feature.Uprime L ε) (q1 z) (q2 z) -
          prodGradY (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z))
          (ENNReal.ofReal p) (DGPS.haar 2) ≤ C * ENNReal.ofReal |ε| := by
  set P := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by rw [hP]; exact ENNReal.one_le_ofReal.2 hp
  set S0 := torusSupNorm Spikes.gT with hS0d
  have hS0 : 0 ≤ S0 := torusSupNorm_nonneg _
  have hpi : 0 < π := Real.pi_pos
  have hk := kappa_nonneg
  set G := eLpNorm (fun y => Spikes.hSum y - Spikes.hMean) P (DGPS.haar 1) with hGd
  set T := eLpNorm (Feature.dthetaT L 0) P (DGPS.haar 1) with hTd
  set P0 := eLpNorm (Feature.Uprime L 0) P (DGPS.haar 1) with hP0d
  have hG : G ≠ ⊤ := (Spikes.memLp_hSum_sub_mean hp hp2).eLpNorm_lt_top.ne
  have hdth : MemLp (Feature.dthetaT L 0) P (DGPS.haar 1) := by
    rw [dthetaT_zero_eq]; exact (Feature.memLp_Q2 hL P).const_mul 2
  have hT : T ≠ ⊤ := hdth.eLpNorm_lt_top.ne
  have hP0 : P0 ≠ ⊤ := by
    have hm : AEStronglyMeasurable (Feature.Uprime L 0) (DGPS.haar 1) := by
      have := aestronglyMeasurable_UprimeF L 0 aesm_gT aesm_gprime
      rwa [UprimeF_gT] at this
    have : MemLp (Feature.Uprime L 0) P (DGPS.haar 1) := by
      refine MemLp.of_le (hdth.const_mul (2 * π)) hm (Filter.Eventually.of_forall fun y => ?_)
      unfold Feature.Uprime
      rw [norm_smul, Feature.norm_Jrot, ← UfeatF_gT, norm_UfeatF, mul_one, Real.norm_eq_abs]
    exact this.eLpNorm_lt_top.ne
  have hg : MemLp Spikes.gT P (DGPS.haar 1) :=
    MemLp.of_bound aesm_gT Spikes.hMean (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact Spikes.abs_gT_le y)
  set C1 := ENNReal.ofReal (2 * Model.kappa) * (ENNReal.ofReal (2 * π) *
    eLpNorm Spikes.gT P (DGPS.haar 1)) with hC1d
  set C2 := ENNReal.ofReal Model.kappa * (ENNReal.ofReal (12 * π) * G +
    ENNReal.ofReal (4 * π ^ 2 * S0) * T + P0 * ENNReal.ofReal (2 * π * S0)) with hC2d
  have hgn : eLpNorm Spikes.gT P (DGPS.haar 1) ≠ ⊤ := hg.eLpNorm_lt_top.ne
  refine ⟨C1 + C2, ?_, fun ε => ?_⟩
  · simp only [hC1d, hC2d]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩ <;> finiteness
  have hfb := (feature_bounds hL ε)
  have hUb := hfb.2.2 p hp hp2
  have hSb := hfb.1
  have hnU : ∀ y, ‖Feature.Ufeat L ε y‖ = 1 := norm_UfeatF L ε Spikes.gT
  have hnU0 : ∀ y, ‖Feature.Ufeat L 0 y‖ = 1 := norm_UfeatF L 0 Spikes.gT
  have hmU : ∀ η : ℝ, AEStronglyMeasurable (Feature.Ufeat L η) (DGPS.haar 1) := fun η =>
    aestronglyMeasurable_UfeatF L η aesm_gT
  have hmU' : ∀ η : ℝ, AEStronglyMeasurable (Feature.Uprime L η) (DGPS.haar 1) := fun η => by
    have := aestronglyMeasurable_UprimeF L η aesm_gT aesm_gprime
    rwa [UprimeF_gT] at this
  have key := quantitative_product_kernel_convergence (U := Feature.Ufeat L 0)
    (Ut := Feature.Ufeat L ε) (U' := Feature.Uprime L 0) (Ut' := Feature.Uprime L ε) hnU0 hnU
  refine ⟨?_, ?_⟩
  · have h1 := prodKernel_UfeatF_Lp_le hL ε hP1 (f := fun _ => (0 : ℝ)) (g2 := Spikes.gT)
      aestronglyMeasurable_const aesm_gT (by simpa using aesm_gT)
    rw [UfeatF_zero] at h1
    have h1' : eLpNorm (fun z : Torus 2 => prodKernel (Feature.Ufeat L ε) (q1 z) (q2 z) -
          prodKernel (Feature.Ufeat L 0) (q1 z) (q2 z)) P (DGPS.haar 2) ≤
        C1 * ENNReal.ofReal |ε| := by
      refine h1.trans (le_of_eq ?_)
      simp only [hC1d, sub_zero]
      ring
    exact h1'.trans (by gcongr; exact le_self_add)
  · have hX := (key.2.2 P hP1 (hmU 0) (hmU ε) (hmU' 0) (hmU' ε))
    have hfin : ∀ D : ℝ≥0∞, D ≤ ENNReal.ofReal Model.kappa *
          (eLpNorm (fun z => Feature.Uprime L ε z - Feature.Uprime L 0 z) P (DGPS.haar 1) +
            P0 * ENNReal.ofReal (vecSupNorm (fun z => Feature.Ufeat L ε z - Feature.Ufeat L 0 z))) →
        D ≤ (C1 + C2) * ENNReal.ofReal |ε| := by
      intro D hD
      refine hD.trans ?_
      have e1 : ENNReal.ofReal (vecSupNorm (fun z => Feature.Ufeat L ε z - Feature.Ufeat L 0 z)) ≤
          ENNReal.ofReal (2 * π * S0) * ENNReal.ofReal |ε| := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal (hSb.trans (le_of_eq ?_))
        simp only [hS0d]; ring
      have e2 := hUb
      calc _ ≤ ENNReal.ofReal Model.kappa *
            (ENNReal.ofReal |ε| * (ENNReal.ofReal (12 * π) * G +
              ENNReal.ofReal (4 * π ^ 2 * S0) * T) +
              P0 * (ENNReal.ofReal (2 * π * S0) * ENNReal.ofReal |ε|)) := by
            gcongr
        _ = C2 * ENNReal.ofReal |ε| := by simp only [hC2d]; ring
        _ ≤ _ := by gcongr; exact le_add_self
    exact ⟨hfin _ hX.1, hfin _ hX.2⟩

/-- **SEM013.**  Strong small amplitude convergence at every fixed exponent. -/
theorem strong_small_amplitude_convergence_at_every_fixed_exponent {L : ℝ} (hL : 0 < L) :
    (∀ ε : ℝ,
      vecSupNorm (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
        2 * π * |ε| * torusSupNorm Spikes.gT ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        vecHolderSeminorm α (fun y => Feature.Ufeat L ε y - Feature.Ufeat L 0 y) ≤
          2 * π * |ε| * (6 ^ α * torusHolderSeminorm α Spikes.gT +
            torusSupNorm Spikes.gT * vecHolderSeminorm α (Feature.Ufeat L 0))) ∧
      (∀ p : ℝ, 1 ≤ p → p < 2 →
        eLpNorm (fun y => Feature.Uprime L ε y - Feature.Uprime L 0 y) (ENNReal.ofReal p)
            (DGPS.haar 1) ≤
          ENNReal.ofReal |ε| *
            (ENNReal.ofReal (12 * π) *
                eLpNorm (fun y => Spikes.hSum y - Spikes.hMean) (ENNReal.ofReal p) (DGPS.haar 1) +
              ENNReal.ofReal (4 * π ^ 2 * torusSupNorm Spikes.gT) *
                eLpNorm (Feature.dthetaT L 0) (ENNReal.ofReal p) (DGPS.haar 1)))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, |ε| ≤ 1 →
      prodHolderNorm α (fun x y => Model.modelW L ε x y - Model.modelW L 0 x y) ≤ C * |ε|) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ε : ℝ,
      eLpNorm (fun z : Torus 2 => Model.modelW L ε (q1 z) (q2 z) - Model.modelW L 0 (q1 z) (q2 z))
          (ENNReal.ofReal p) (DGPS.haar 2) ≤ C * ENNReal.ofReal |ε| ∧
      eLpNorm (fun z : Torus 2 =>
          prodGradX (Feature.Ufeat L ε) (Feature.Uprime L ε) (q1 z) (q2 z) -
          prodGradX (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z))
          (ENNReal.ofReal p) (DGPS.haar 2) ≤ C * ENNReal.ofReal |ε| ∧
      eLpNorm (fun z : Torus 2 =>
          prodGradY (Feature.Ufeat L ε) (Feature.Uprime L ε) (q1 z) (q2 z) -
          prodGradY (Feature.Ufeat L 0) (Feature.Uprime L 0) (q1 z) (q2 z))
          (ENNReal.ofReal p) (DGPS.haar 2) ≤ C * ENNReal.ofReal |ε|) :=
  ⟨feature_bounds hL, fun _ h0 h1 => kernel_holder_bound hL h0 h1,
    fun _ hp hp2 => kernel_sobolev_bound hL hp hp2⟩

end DGPS.Examples.RoughBoundary.Semicontinuity
