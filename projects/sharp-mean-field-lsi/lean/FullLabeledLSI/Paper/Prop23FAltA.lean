import FullLabeledLSI.Paper.Prop23SchroB
import FullLabeledLSI.Paper.Prop23SchroC
import FullLabeledLSI.Paper.Prop23ReplaceB
import FullLabeledLSI.Paper.Prop23ReplaceC
import FullLabeledLSI.Paper.Prop23Ground1
import FullLabeledLSI.Paper.Prop23Ground2
import FullLabeledLSI.Defs.F05_FiniteRank

/-!
# Proposition 2.3, WP-F (alt), part A: auxiliary lemmas

* bounded measurable (`BM`) representatives of `u_R(Z_N)`, `v_R(Z_N)`, `V_{N,R}` (with `fluct eC`),
  and the transfer `fluct e = fluct eC` `Q_N`-a.e.;
* integrability of `Ψ² g` for `Ψ ∈ L²` and `g` a.e. equal to a bounded measurable function;
* the elementary entropy bound `Ent_P(f²) ≤ B² |log B²| + 1` for `|f| ≤ B`;
* the real-number bookkeeping lemma `fa_alg` of `(reduce-J)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

section FAltAux

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e eC : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

theorem fa_BM_const {α : Type*} [MeasurableSpace α] (c : ℝ) : BM (fun _ : α => c) :=
  ⟨⟨|c|, fun _ => le_rfl⟩, measurable_const⟩

theorem fa_BM_add {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : BM f) (hg : BM g) :
    BM (fun x => f x + g x) := by
  obtain ⟨⟨B, hB⟩, hfm⟩ := hf
  obtain ⟨⟨C, hC⟩, hgm⟩ := hg
  exact ⟨⟨B + C, fun x => (abs_add_le _ _).trans (add_le_add (hB x) (hC x))⟩, hfm.add hgm⟩

theorem fa_BM_sq {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : BM f) :
    BM (fun x => f x ^ 2) := by
  have := hf.mul hf
  simpa [sq] using this

theorem fa_BM_uR (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (A : FiniteRankApprox W μ e) (R N : ℕ) :
    BM (fun X : Config N d => uR A R (fun n => fluct eC N n X)) := by
  unfold uR
  refine BM.const_mul _ (BM.sum _ fun i _ => BM.sum _ fun j _ => ?_)
  exact ((BM_fluct hφ N i).const_mul _).mul (BM_fluct hφ N j)

theorem fa_BM_vR (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (A : FiniteRankApprox W μ e)
    (lam : ℕ → ℝ) (R N : ℕ) :
    BM (fun X : Config N d => vR A lam R (fun n => fluct eC N n X)) := by
  unfold vR
  refine fa_BM_add (BM.sub (BM.const_mul _ (BM.sum _ fun m _ => BM.const_mul _ ?_))
    (fa_BM_const _)) (BM.const_mul _ (BM.sum _ fun i _ => BM.sum _ fun j _ => ?_))
  · exact fa_BM_sq (BM.sum _ fun j _ => (BM_fluct hφ N j).const_mul _)
  · exact (((BM_fluct hφ N i).mul (fa_BM_const _)).mul (fa_BM_const _)).mul (BM_fluct hφ N j)

theorem fa_BM_VNR (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (A : FiniteRankApprox W μ e)
    (lam : ℕ → ℝ) (R N : ℕ) :
    BM (fun X : Config N d => VNR A lam eC R N X) := by
  unfold VNR
  refine fa_BM_add (BM.sub (BM.const_mul _ (BM.sum _ fun i _ => BM.sum _ fun j _ => ?_))
    (BM.const_mul _ (BM.sum _ fun i _ => BM.sum _ fun j _ => ?_)))
    (BM.const_mul _ (BM.sum _ fun i _ => ?_))
  · exact ((BM_TR hφ A R i).mul (BM_ANmat hφ N i j)).mul (BM_TR hφ A R j)
  · exact (fa_BM_const _).mul (BM_ANmat hφ N i j)
  · exact ((fa_BM_const _).mul (BM_fluct hφ N i)).mul (BM_TR hφ A R i)

/-- `Z_N` computed with `e` agrees `Q_N`-a.e. with `Z_N` computed with `eC`. -/
theorem fa_fluct_ae [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) :
    ∀ᵐ X ∂QN μ N, (fun n => fluct e N n X) = fun n => fluct eC N n X := by
  filter_upwards [schroC_ae_all hac heC N] with X hX
  funext n
  unfold fluct
  congr 1
  exact Finset.sum_congr rfl fun l _ => (hX l (n + 1)).symm

theorem fa_ae_comp [IsProbabilityMeasure μ] (hac : μ ≪ haar d)
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (N : ℕ) (G : (ℕ → ℝ) → ℝ) :
    (fun X : Config N d => G (fun n => fluct e N n X)) =ᵐ[QN μ N]
      fun X => G (fun n => fluct eC N n X) := by
  filter_upwards [fa_fluct_ae hac heC N] with X hX
  rw [hX]

/-- `Ψ² g` is integrable for `Ψ ∈ L²` and `g` a.e. equal to a bounded measurable function. -/
theorem fa_integrable_sq_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} {Ψ g g' : α → ℝ}
    (hΨ : MemLp Ψ 2 ν) (hg' : BM g') (hae : g =ᵐ[ν] g') :
    Integrable (fun x => Ψ x ^ 2 * g x) ν := by
  obtain ⟨⟨B, hB⟩, hm⟩ := hg'
  have h1 : Integrable (fun x => Ψ x ^ 2 * g' x) ν :=
    hΨ.integrable_sq.mul_bdd hm.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
  refine h1.congr ?_
  filter_upwards [hae] with x hx
  rw [hx]

end FAltAux

/-! ### The elementary entropy bound -/

theorem fa_mul_log_bounds {t M : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) :
    -1 ≤ t * Real.log t ∧ t * Real.log t ≤ M * |Real.log M| := by
  have hM : 0 ≤ M := ht.trans htM
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_mul, Real.log_zero]
    exact ⟨by norm_num, mul_nonneg hM (abs_nonneg _)⟩
  refine ⟨?_, ?_⟩
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have : t * (1 - t⁻¹) ≤ t * Real.log t := mul_le_mul_of_nonneg_left h ht
    have e1 : t * (1 - t⁻¹) = t - 1 := by field_simp
    linarith
  · by_cases h1 : t ≤ 1
    · have : t * Real.log t ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht (Real.log_nonpos ht h1)
      exact this.trans (mul_nonneg hM (abs_nonneg _))
    · have h1 := not_le.1 h1
      have hlt : 0 ≤ Real.log t := Real.log_nonneg h1.le
      have hlM : Real.log t ≤ Real.log M := Real.log_le_log hpos htM
      calc t * Real.log t ≤ M * Real.log t := mul_le_mul_of_nonneg_right htM hlt
        _ ≤ M * Real.log M := mul_le_mul_of_nonneg_left hlM hM
        _ ≤ M * |Real.log M| := mul_le_mul_of_nonneg_left (le_abs_self _) hM

theorem fa_ent_sq_toReal_le {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {f : α → ℝ} (hf : AEStronglyMeasurable f P) {B : ℝ}
    (hB : ∀ᵐ x ∂P, |f x| ≤ B) :
    (SharpLSI.ent P (fun x => f x ^ 2)).toReal ≤ B ^ 2 * |Real.log (B ^ 2)| + 1 := by
  set M : ℝ := B ^ 2 with hMdef
  have hM0 : 0 ≤ M := sq_nonneg _
  have hbd : ∀ᵐ x ∂P, f x ^ 2 ≤ M := by
    filter_upwards [hB] with x hx
    exact sq_le_sq' (by linarith [abs_le.1 hx]) (abs_le.1 hx).2
  have hu_aes : AEStronglyMeasurable (fun x => f x ^ 2) P := hf.pow 2
  have hint : Integrable (fun x => f x ^ 2) P := by
    refine Integrable.of_bound hu_aes M ?_
    filter_upwards [hbd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  have hlog_aes : AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P :=
    (hu_aes.aemeasurable.mul (Real.measurable_log.comp_aemeasurable hu_aes.aemeasurable)).aestronglyMeasurable
  have hlogb : ∀ᵐ x ∂P, |f x ^ 2 * Real.log (f x ^ 2)| ≤ M * |Real.log M| + 1 := by
    filter_upwards [hbd] with x hx
    obtain ⟨h1, h2⟩ := fa_mul_log_bounds (sq_nonneg (f x)) hx
    have : 0 ≤ M * |Real.log M| := mul_nonneg hM0 (abs_nonneg _)
    rw [abs_le]
    constructor <;> linarith
  have hlogint : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P := by
    refine Integrable.of_bound hlog_aes (M * |Real.log M| + 1) ?_
    filter_upwards [hlogb] with x hx
    rwa [Real.norm_eq_abs]
  rw [SharpLSI.ent_eq_formula P _ (fun x => sq_nonneg _) hint hlogint]
  set m : ℝ := ∫ x, f x ^ 2 ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg fun x => sq_nonneg _
  have hI : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P ≤ M * |Real.log M| := by
    have : ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P ≤ ∫ _x, M * |Real.log M| ∂P := by
      refine integral_mono_ae hlogint (integrable_const _) ?_
      filter_upwards [hbd] with x hx
      exact (fa_mul_log_bounds (sq_nonneg (f x)) hx).2
    simpa using this
  have hm1 : -1 ≤ m * Real.log m := by
    obtain ⟨h1, -⟩ := fa_mul_log_bounds hm0 (le_refl m)
    exact h1
  rw [ENNReal.toReal_ofReal']
  refine max_le (by linarith) ?_
  have : 0 ≤ M * |Real.log M| := mul_nonneg hM0 (abs_nonneg _)
  linarith

/-! ### Real bookkeeping for `(reduce-J)` -/

theorem fa_alg {a1 shR rE IV IVe eQ IU IUN lg lK m Eg ε₁ ε₂ ε₃ η ME bR b0 : ℝ}
    (h1 : |a1 - shR| ≤ ε₁) (h2 : shR = rE + IV) (h3 : |IV - IVe| ≤ ε₂)
    (h4 : Eg = eQ + IUN + lK * m) (h5 : |(IUN - IU) + (lK - lg) * m| ≤ ε₃)
    (h6 : 0 ≤ Eg) (h6' : Eg ≤ ME) (hbR0 : 0 ≤ bR) (hbR1 : bR ≤ b0 + 1)
    (hbη : |bR - b0| ≤ η) (hη : 0 ≤ η) :
    (rE + IVe - bR / 2 * (eQ + IU + lg * m)) - (ε₁ + ε₂ + (b0 + 1) / 2 * ε₃ + η / 2 * ME) ≤
      a1 - b0 / 2 * Eg := by
  set δ : ℝ := (IUN - IU) + (lK - lg) * m with hδ
  have hEg : Eg = eQ + IU + lg * m + δ := by rw [h4, hδ]; ring
  have hδle : δ ≤ ε₃ := (le_abs_self _).trans h5
  have ha1 : shR - ε₁ ≤ a1 := by linarith [(abs_le.1 h1).1, (abs_le.1 h1).2]
  have hIV : IVe - ε₂ ≤ IV := by linarith [(abs_le.1 h3).1, (abs_le.1 h3).2]
  have e1 : bR / 2 * δ ≤ (b0 + 1) / 2 * ε₃ := by
    have hε₃ : 0 ≤ ε₃ := (abs_nonneg _).trans h5
    calc bR / 2 * δ ≤ bR / 2 * ε₃ := mul_le_mul_of_nonneg_left hδle (by linarith)
      _ ≤ (b0 + 1) / 2 * ε₃ := mul_le_mul_of_nonneg_right (by linarith) hε₃
  have e2 : (b0 - bR) / 2 * Eg ≤ η / 2 * ME := by
    have hb : b0 - bR ≤ η := by linarith [(abs_le.1 hbη).1, (abs_le.1 hbη).2]
    calc (b0 - bR) / 2 * Eg ≤ η / 2 * Eg := mul_le_mul_of_nonneg_right (by linarith) h6
      _ ≤ η / 2 * ME := mul_le_mul_of_nonneg_left h6' (by linarith)
  have key : rE + IVe - bR / 2 * (eQ + IU + lg * m) =
      rE + IVe - bR / 2 * Eg + bR / 2 * δ := by rw [hEg]; ring
  have key2 : a1 - b0 / 2 * Eg = a1 - bR / 2 * Eg + (bR - b0) / 2 * Eg := by ring
  have e3 : -((bR - b0) / 2 * Eg) ≤ η / 2 * ME := by
    have : -((bR - b0) / 2 * Eg) = (b0 - bR) / 2 * Eg := by ring
    rw [this]; exact e2
  rw [key]
  nlinarith [e1, e3, ha1, hIV, h2, key2]

end SharpLSI.FL
