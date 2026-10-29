import FullLabeledLSI.Statements.S04_Prop_2_3
import FullLabeledLSI.Paper.Prop23Defs

/-!
# Proposition 2.3, WP-I: from the subsequence form `Ns k → ∞` to the `N`-indexed core

`boundedComparison_of_core : Hyp V W KV KW → PropBoundedCore V W b → BoundedComparison V W b`.
A bad `k` (failing the comparison inequality) gives, via `Classical.choose`, an `N`-indexed
family equal to `f k` at `N = Ns k` and to `0` elsewhere; the zero function is admissible.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Transport of a function along an equality of particle numbers. -/
def trCfg {N M : ℕ} (e : N = M) (f : Config N d → ℝ) : Config M d → ℝ := by
  subst e; exact f

theorem trCfg_rfl {N : ℕ} (f : Config N d → ℝ) : trCfg rfl f = f := rfl

theorem memH1C_trCfg {N M : ℕ} (e : N = M) {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : MemH1C (gibbs V W M) (trCfg e f) := by
  subst e; exact hf

theorem energy_trCfg {N M : ℕ} (e : N = M) (f : Config N d → ℝ) :
    energy V W M (trCfg e f) = energy V W N f := by
  subst e; rfl

theorem ae_bound_trCfg {N M : ℕ} (e : N = M) {f : Config N d → ℝ} {B : ℝ}
    (hf : ∀ᵐ X ∂gibbs V W N, |f X| ≤ B) : ∀ᵐ X ∂gibbs V W M, |trCfg e f X| ≤ B := by
  subst e; exact hf

/-- The comparison inequality at particle number `N`. -/
def CmpIneq (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (b : ℝ≥0∞) (ε : ℝ) (N : ℕ)
    (f : Config N d → ℝ) : Prop :=
  b / 2 * ent (gibbs V W N) (fun X => f X ^ 2) ≤ energy V W N f + ENNReal.ofReal ε

theorem cmpIneq_trCfg {b : ℝ≥0∞} {ε : ℝ} {N M : ℕ} (e : N = M) (f : Config N d → ℝ) :
    CmpIneq V W b ε M (trCfg e f) ↔ CmpIneq V W b ε N f := by
  subst e; exact Iff.rfl

/-- The zero function is in `H¹(P_N)`. -/
theorem memH1C_zero (hyp : Hyp V W KV KW) (N : ℕ) :
    MemH1C (gibbs V W N) (fun _ : Config N d => (0 : ℝ)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac := (gibbs_map_flat_ac hyp N).1
  have h0 : IsWeakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) 0 := isWeakGrad_const 0
  refine ⟨⟨_, h0⟩, memLp_const 0, ?_⟩
  refine (memLp_const (0 : ℝ)).ae_eq ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq h0)] with y hy
  change (0 : ℝ) = Real.sqrt (sqNorm (weakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) y))
  rw [hy]; simp [sqNorm]

theorem energy_zero (hyp : Hyp V W KV KW) (N : ℕ) :
    energy V W N (fun _ : Config N d => (0 : ℝ)) = 0 := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac := (gibbs_map_flat_ac hyp N).1
  have h0 : IsWeakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) 0 := isWeakGrad_const 0
  rw [energy_eq hyp ⟨_, h0⟩]
  rw [lintegral_congr_ae (g := fun _ => 0)]
  · simp
  · filter_upwards [hac.ae_le (weakGrad_ae_eq h0)] with y hy
    change ENNReal.ofReal (sqNorm (weakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) y)) = 0
    rw [hy]; simp [sqNorm]

/-- **WP-I.** The `N`-indexed core implies the subsequence form. -/
theorem boundedComparison_of_core {b : ℝ≥0∞} (hyp : Hyp V W KV KW)
    (hcore : PropBoundedCore V W b) : BoundedComparison V W b := by
  classical
  intro Ns hNs f hmem hB ε hε
  obtain ⟨B, hB⟩ := hB
  by_contra hcon
  have hfr : ∃ᶠ k in atTop, ¬ CmpIneq V W b ε (Ns k) (f k) := not_eventually.mp hcon
  -- the padded family
  let F : (N : ℕ) → Config N d → ℝ := fun N =>
    if hh : ∃ k, ¬ CmpIneq V W b ε (Ns k) (f k) ∧ Ns k = N then
      trCfg hh.choose_spec.2 (f hh.choose) else fun _ => 0
  have hFadm : ∀ N, MemH1C (gibbs V W N) (F N) ∧ (∀ᵐ X ∂gibbs V W N, |F N X| ≤ B) ∧
      energy V W N (F N) ≤ B := by
    intro N
    by_cases hh : ∃ k, ¬ CmpIneq V W b ε (Ns k) (f k) ∧ Ns k = N
    · have : F N = trCfg hh.choose_spec.2 (f hh.choose) := by simp only [F, dif_pos hh]
      rw [this]
      exact ⟨memH1C_trCfg _ (hmem _), ae_bound_trCfg _ (hB _).1,
        (energy_trCfg _ _).le.trans (hB _).2⟩
    · have : F N = fun _ => 0 := by simp only [F, dif_neg hh]
      rw [this]
      refine ⟨memH1C_zero hyp N, ?_, by rw [energy_zero hyp N]; exact zero_le⟩
      exact Eventually.of_forall fun X => by simp
  have hev := hcore F (fun N => (hFadm N).1) ⟨B, fun N => ⟨(hFadm N).2.1, (hFadm N).2.2⟩⟩ ε hε
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  have hlarge : ∀ᶠ k in atTop, N0 ≤ Ns k := hNs.eventually_ge_atTop N0
  obtain ⟨k, hk, hkN⟩ := (hfr.and_eventually hlarge).exists
  have hh : ∃ k', ¬ CmpIneq V W b ε (Ns k') (f k') ∧ Ns k' = Ns k := ⟨k, hk, rfl⟩
  have hFk : F (Ns k) = trCfg hh.choose_spec.2 (f hh.choose) := by simp only [F, dif_pos hh]
  have := hN0 (Ns k) hkN
  change CmpIneq V W b ε (Ns k) (F (Ns k)) at this
  rw [hFk, cmpIneq_trCfg] at this
  exact hh.choose_spec.1 this

end SharpLSI.FL
