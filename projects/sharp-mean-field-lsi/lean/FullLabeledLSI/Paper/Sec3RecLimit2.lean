import FullLabeledLSI.Paper.Sec3RecLimit
import FullLabeledLSI.Paper.Sec3Entropy

/-!
# Proposition 3.2: entropy limit of the nonidentical products to `G_θ`
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The assignment with the group sizes `groupSize s0 θ N`. -/
def assignOf {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1)
    (N : ℕ) : Fin N → Fin q :=
  (exists_assign (groupSize s0 θ N) N (sum_groupSize s0 θ hθ0 hθ1 N)).choose

theorem assignOf_fiber {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ) (hθ0 : ∀ s, 0 ≤ θ s)
    (hθ1 : ∑ s, θ s = 1) (N : ℕ) (s : Fin q) :
    (Finset.univ.filter fun i => assignOf s0 θ hθ0 hθ1 N i = s).card = groupSize s0 θ N s :=
  (exists_assign (groupSize s0 θ N) N (sum_groupSize s0 θ hθ0 hθ1 N)).choose_spec s


theorem entropy_limit_family (hyp : Hyp V W KV KW) {q : ℕ} (s0 : Fin q) (θ : Fin q → ℝ)
    (ρ : Fin q → Torus d → ℝ) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1)
    (hρ : ∀ s, IsSmoothT (ρ s) ∧ (∀ x, 0 < ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1) :
    Tendsto (fun N : ℕ => klDiv (Measure.pi fun i : Fin N =>
        densMeasure (ρ (assignOf s0 θ hθ0 hθ1 N i))) (gibbs V W N) / N) atTop
      (𝓝 (msGap V W (⟨q, θ, ρ⟩ : Family d)).toENNReal) := by
  have hρ0 : ∀ s x, 0 ≤ ρ s x := fun s x => (hρ s).2.1 x |>.le
  have hρ1 : ∀ s, ∫ x, ρ s x ∂haar d = 1 := fun s => (hρ s).2.2
  have hρc : ∀ s, Continuous (ρ s) := fun s => (hρ s).1.continuous
  have hKLt : ∀ s, klDiv (densMeasure (ρ s)) (haar d) ≠ ⊤ := fun s =>
    klDiv_densMeasure_ne_top_of_continuous (hρc s) (hρ0 s) (hρ1 s)
  set KL : Fin q → ℝ := fun s => (klDiv (densMeasure (ρ s)) (haar d)).toReal with hKL
  set P : Fin q → ℝ := fun s => potE V (densMeasure (ρ s)) with hP
  set I : Fin q → Fin q → ℝ := fun s t => interE W (densMeasure (ρ s)) (densMeasure (ρ t)) with hI
  set L : ℝ := ∑ s, θ s * (KL s + P s) + 1 / 2 * ∑ s, ∑ t, θ s * θ t * I s t -
    0 * ∑ s, θ s * I s s + -(Fstar V W).toReal with hL
  -- the real-valued limit
  have hreal : Tendsto (fun N : ℕ => (klDiv (Measure.pi fun i : Fin N =>
      densMeasure (ρ (assignOf s0 θ hθ0 hθ1 N i))) (gibbs V W N)).toReal / N) atTop (𝓝 L) := by
    have hlim := tendsto_entropy_expr (fun N s => (groupSize s0 θ N s : ℝ) / N) θ
      (fun s => tendsto_groupSize s0 θ hθ0 hθ1 s) (fun s => KL s + P s) I
      (fun N => Real.log (partitionFn V W N) / N) (-(Fstar V W).toReal) (tendsto_log_partition hyp)
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (entropy_expr hyp hN ρ (fun s => ⟨hρ0 s, hρ1 s, hKLt s⟩)
      (assignOf s0 θ hθ0 hθ1 N) (groupSize s0 θ N) (assignOf_fiber s0 θ hθ0 hθ1 N)).2.symm
  -- identify the limit with `G_θ`
  have hG : (msGap V W (⟨q, θ, ρ⟩ : Family d)) = (L : EReal) := by
    set S : ℝ≥0∞ := ∑ a, ENNReal.ofReal (θ a) * klDiv (densMeasure (ρ a)) (haar d) with hS
    have hSt : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun a _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKLt a)
    have hSr : S.toReal = ∑ a, θ a * KL a := by
      rw [hS, ENNReal.toReal_sum fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hKLt a)]
      exact Finset.sum_congr rfl fun a _ => by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hθ0 a)]
    have hbar : (⟨q, θ, ρ⟩ : Family d).bar = fun x => ∑ s, θ s * ρ s x := rfl
    have hpm := potE_mix θ ρ hyp hρ0 hρ1 hθ0 hθ1
    have him := interE_mix θ ρ hyp hρc hρ0 hρ1 hθ0 hθ1
    have hFs : Fstar V W = ((Fstar V W).toReal : EReal) := Fstar_eq_coe hyp
    unfold msGap
    rw [hbar, hpm, him]
    show ((S : ℝ≥0∞) : EReal) + _ - _ = _
    rw [← EReal.coe_ennreal_toReal hSt, hSr]
    nth_rewrite 1 [hFs]
    simp only [← EReal.coe_add, ← EReal.coe_sub]
    congr 1
    simp only [hL, hP, hI, mul_add, Finset.sum_add_distrib]
    ring
  rw [hG, EReal.real_coe_toENNReal]
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hne, -⟩ := entropy_expr hyp hN ρ (fun s => ⟨hρ0 s, hρ1 s, hKLt s⟩)
    (assignOf s0 θ hθ0 hθ1 N) (groupSize s0 θ N) (assignOf_fiber s0 θ hθ0 hθ1 N)
  rw [ENNReal.ofReal_div_of_pos hN0, ENNReal.ofReal_toReal hne]
  simp

end SharpLSI.FL
