import FullLabeledLSI.Paper.Hybrid63AltF
import FullLabeledLSI.Paper.Sec6Continuity
import FullLabeledLSI.Paper.LindebergTransfer
import FullLabeledLSI.Paper.Lindeberg3

/-!
# Proposition 6.3: real formulas and the four test functions

* `ent_toReal_formula`: `(Ent_P X²).toReal = max (∫ φ(X) - ψ(∫ X²)) 0` for `X ∈ L⁴`.
* boundedness/measurability of `polyEval`/`polyB` for a good basis, and `L⁴`-integrability on the
  hybrid space from `HybridPolyMoment`.
* continuity and polynomial growth of the tests `s²`, `φ(s)`, `s² · quad(zext z)`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

theorem abs_phi_le (x : ℝ) : |Sec6.phi x| ≤ 1 + x ^ 4 := by
  unfold Sec6.phi
  set t : ℝ := x ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg x
  have h4 : x ^ 4 = t ^ 2 := by rw [ht]; ring
  rw [h4]
  by_cases h1 : t ≤ 1
  · have := Sec6.abs_mul_log_le_one (x := t) (by rw [abs_of_nonneg ht0]; exact h1)
    have h' : |t * Real.log t| ≤ 1 := this
    nlinarith [sq_nonneg t]
  · push_neg at h1
    have hl0 : 0 ≤ Real.log t := Real.log_nonneg h1.le
    have hl1 : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos (lt_trans one_pos h1); linarith
    rw [abs_of_nonneg (mul_nonneg ht0 hl0)]
    nlinarith [mul_le_mul_of_nonneg_left hl1 ht0]

theorem ent_toReal_formula {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : Measurable X)
    (h4 : Integrable (fun ω => |X ω| ^ 4) P) :
    (ent P (fun ω => X ω ^ 2)).toReal =
      max (∫ ω, Sec6.phi (X ω) ∂P - Sec6.psi (∫ ω, X ω ^ 2 ∂P)) 0 := by
  have hb : Integrable (fun ω => 1 + |X ω| ^ 4) P := (integrable_const (1 : ℝ)).add h4
  have hX2 : Integrable (fun ω => X ω ^ 2) P := by
    refine hb.mono' (hX.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |X ω| ^ 2 ≤ 1 + |X ω| ^ 4 := by nlinarith [sq_nonneg (|X ω| ^ 2 - 1)]
    simpa [sq_abs] using this
  have hphi : Integrable (fun ω => X ω ^ 2 * Real.log (X ω ^ 2)) P := by
    have hm : Measurable fun ω => X ω ^ 2 * Real.log (X ω ^ 2) :=
      (hX.pow_const 2).mul (Real.measurable_log.comp (hX.pow_const 2))
    refine hb.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have := abs_phi_le (X ω)
    have h4' : X ω ^ 4 = |X ω| ^ 4 := by
      rw [← Even.pow_abs (by decide : Even 4)]
    unfold Sec6.phi at this
    rw [h4'] at this
    exact this
  rw [ent_eq_formula P _ (fun ω => sq_nonneg _) hX2 hphi, ENNReal.toReal_ofReal']
  rfl

section good
variable {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

theorem measurable_polyEval (hG : GoodBasis μ e) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) :
    Measurable (polyEval e c : Config N d → ℝ) := by
  unfold polyEval
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  exact Finset.measurable_prod _ fun i _ => (hG.meas _).comp (measurable_pi_apply i)

theorem polyEval_bounded (hG : GoodBasis μ e) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) :
    ∃ K : ℝ, ∀ X : Config N d, |polyEval e c X| ≤ K := by
  choose Cb hCb using hG.bdd
  refine ⟨∑ j : Fin N → Fin (J + 1), |c j| * ∏ i, Cb (j i), fun X => ?_⟩
  unfold polyEval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
    fun i _ => hCb _ _) (abs_nonneg _)

theorem measurable_polyB (hG : GoodBasis μ e) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) :
    Measurable (polyB e c B : Config N d × (Fin N → Fin J → ℝ) → ℝ) := by
  unfold polyB
  refine Finset.measurable_sum _ fun j _ => measurable_const.mul ?_
  refine Finset.measurable_prod _ fun i _ => ?_
  unfold hybFactor
  by_cases hi : i ∈ B
  · simp only [hi, if_true]
    exact (hG.meas _).comp ((measurable_pi_apply i).comp measurable_fst)
  · simp only [hi, if_false]
    by_cases hm : ((j i : Fin (J + 1)) : ℕ) = 0
    · simp only [hm, dif_pos]; exact measurable_const
    · simp only [hm, dif_neg, not_false_eq_true]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply i).comp measurable_snd)

variable [IsProbabilityMeasure μ] {lam : ℕ → ℝ} {J : ℕ}

theorem hyb_integrable_pow (hG : GoodBasis μ e) (hmom : HybridPolyMoment μ e lam J) (L : ℝ) (q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ),
      SpectralCoeff lam L c →
        Integrable (fun w => |polyB e c B w| ^ q) (hybMeasure μ N J) ∧
          ∫ w, |polyB e c B w| ^ q ∂hybMeasure μ N J ≤ K * Real.sqrt (∑ j, c j ^ 2) ^ q := by
  obtain ⟨K, hK0, hK⟩ := hmom L q
  refine ⟨K, hK0, fun N B c hc => ?_⟩
  exact integrable_integral_le_of_lintegral_le
    (((measurable_polyB hG c B).abs).pow_const q).aestronglyMeasurable (fun w => by positivity)
    (by positivity) (hK N B c hc)

end good

section tests

/-- The test `s² (quad(zext z) + c0)`. -/
def PhiQuad (JR : ℕ) (s : Finset ℕ) (Qm : ℕ → ℕ → ℝ) (c0 : ℝ) : ℝ × (Fin JR → ℝ) → ℝ :=
  fun p => p.1 ^ 2 * (quadFA s Qm (zext p.2) + c0)

theorem abs_zext_le {JR : ℕ} (z : Fin JR → ℝ) (i : ℕ) : |zext z i| ≤ ‖z‖ := by
  unfold zext
  split_ifs with h
  · simpa [Real.norm_eq_abs] using norm_le_pi_norm z ⟨i, h⟩
  · simp

theorem continuous_zext {JR : ℕ} (i : ℕ) : Continuous fun z : Fin JR → ℝ => zext z i := by
  unfold zext
  by_cases h : i < JR
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

theorem continuous_quadF_zext {JR : ℕ} (s : Finset ℕ) (Qm : ℕ → ℕ → ℝ) :
    Continuous fun z : Fin JR → ℝ => quadFA s Qm (zext z) := by
  unfold quadFA
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((continuous_const.mul (continuous_zext i)).mul (continuous_zext j))

theorem abs_quadF_zext_le {JR : ℕ} (s : Finset ℕ) (Qm : ℕ → ℕ → ℝ) (z : Fin JR → ℝ) :
    |quadFA s Qm (zext z)| ≤ (∑ i ∈ s, ∑ j ∈ s, |Qm i j|) * ‖z‖ ^ 2 := by
  unfold quadFA
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 := abs_zext_le z i
  have h2 := abs_zext_le z j
  calc |Qm i j| * |zext z i| * |zext z j| ≤ |Qm i j| * ‖z‖ * ‖z‖ := by gcongr
    _ = |Qm i j| * ‖z‖ ^ 2 := by ring

theorem continuous_PhiQuad (JR : ℕ) (s : Finset ℕ) (Qm : ℕ → ℕ → ℝ) (c0 : ℝ) :
    Continuous (PhiQuad JR s Qm c0) := by
  unfold PhiQuad
  exact (continuous_fst.pow 2).mul (((continuous_quadF_zext s Qm).comp continuous_snd).add
    continuous_const)

theorem growth_PhiQuad (JR : ℕ) (s : Finset ℕ) (Qm : ℕ → ℕ → ℝ) (c0 : ℝ) :
    ∃ (K : ℝ) (k : ℕ), ∀ p, |PhiQuad JR s Qm c0 p| ≤ K * (1 + ‖p‖) ^ k := by
  set C : ℝ := ∑ i ∈ s, ∑ j ∈ s, |Qm i j| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨C + |c0|, 4, fun p => ?_⟩
  unfold PhiQuad
  have h1 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
  have h2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hq := abs_quadF_zext_le s Qm p.2
  have hn0 : 0 ≤ ‖p‖ := norm_nonneg p
  set r : ℝ := ‖p‖ with hr
  have hq' : |quadFA s Qm (zext p.2) + c0| ≤ C * r ^ 2 + |c0| := by
    refine (abs_add_le _ _).trans ?_
    have : C * ‖p.2‖ ^ 2 ≤ C * r ^ 2 := by gcongr
    linarith
  rw [abs_mul, abs_pow]
  have h3 : |p.1| ^ 2 ≤ r ^ 2 := by gcongr
  calc |p.1| ^ 2 * |quadFA s Qm (zext p.2) + c0| ≤ r ^ 2 * (C * r ^ 2 + |c0|) := by
        gcongr
    _ ≤ (C + |c0|) * (1 + r) ^ 4 := by
        have e1 : r ^ 2 * r ^ 2 ≤ (1 + r) ^ 4 := by
          have : r ^ 4 ≤ (1 + r) ^ 4 := by gcongr; linarith
          nlinarith
        have e2 : r ^ 2 ≤ (1 + r) ^ 4 := by
          have : r ^ 2 ≤ (1 + r) ^ 2 := by gcongr; linarith
          have h' : (1 + r) ^ 2 ≤ (1 + r) ^ 4 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
          linarith
        nlinarith [abs_nonneg c0]

def Phi0 (JR : ℕ) : ℝ × (Fin JR → ℝ) → ℝ := fun p => p.1 ^ 2

def Phi1 (JR : ℕ) : ℝ × (Fin JR → ℝ) → ℝ := fun p => Sec6.phi p.1

theorem continuous_Phi0 (JR : ℕ) : Continuous (Phi0 JR) := continuous_fst.pow 2

theorem continuous_Phi1 (JR : ℕ) : Continuous (Phi1 JR) :=
  Sec6.continuous_phi.comp continuous_fst

theorem growth_Phi0 (JR : ℕ) : ∃ (K : ℝ) (k : ℕ), ∀ p, |Phi0 JR p| ≤ K * (1 + ‖p‖) ^ k := by
  refine ⟨1, 4, fun p => ?_⟩
  unfold Phi0
  have h1 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
  have hn0 : 0 ≤ ‖p‖ := norm_nonneg p
  rw [abs_pow]
  have : |p.1| ^ 2 ≤ (1 + ‖p‖) ^ 2 := by gcongr; linarith
  have h' : (1 + ‖p‖) ^ 2 ≤ (1 + ‖p‖) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
  linarith

theorem growth_Phi1 (JR : ℕ) : ∃ (K : ℝ) (k : ℕ), ∀ p, |Phi1 JR p| ≤ K * (1 + ‖p‖) ^ k := by
  refine ⟨1, 4, fun p => ?_⟩
  unfold Phi1
  have h1 : |p.1| ≤ ‖p‖ := by simpa [Real.norm_eq_abs] using norm_fst_le p
  have hn0 : 0 ≤ ‖p‖ := norm_nonneg p
  refine (abs_phi_le p.1).trans ?_
  have : p.1 ^ 4 = |p.1| ^ 4 := by rw [← Even.pow_abs (by decide : Even 4)]
  rw [this]
  have h2 : |p.1| ^ 4 ≤ ‖p‖ ^ 4 := by gcongr
  have h3 : ‖p‖ ^ 4 + 1 ≤ (1 + ‖p‖) ^ 4 := by nlinarith [pow_nonneg hn0 3, pow_nonneg hn0 2]
  linarith

end tests

end SharpLSI.FL

end
