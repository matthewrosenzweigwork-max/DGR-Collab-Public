import FullLabeledLSI.Paper.Prop23Defs

/-!
# Proposition 2.3, WP-I (alt): from the subsequence form `Ns k → ∞` to the `N`-indexed core

Same argument as `Prop23Ns.boundedComparison_of_core`, but stated with the body of
`BoundedComparison` written out, so that this file does not import `S04_Prop_2_3` (and S04 can import
it to prove `prop_bounded`).  `BoundedComparison V W b` is by definition the statement of
`boundedComparison_unfolded`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Transport of a function along an equality of particle numbers. -/
def trCfgA {N M : ℕ} (e : N = M) (f : Config N d → ℝ) : Config M d → ℝ := by
  subst e; exact f

theorem memH1C_trCfgA {N M : ℕ} (e : N = M) {f : Config N d → ℝ}
    (hf : MemH1C (gibbs V W N) f) : MemH1C (gibbs V W M) (trCfgA e f) := by
  subst e; exact hf

theorem energy_trCfgA {N M : ℕ} (e : N = M) (f : Config N d → ℝ) :
    energy V W M (trCfgA e f) = energy V W N f := by
  subst e; rfl

theorem ae_bound_trCfgA {N M : ℕ} (e : N = M) {f : Config N d → ℝ} {B : ℝ}
    (hf : ∀ᵐ X ∂gibbs V W N, |f X| ≤ B) : ∀ᵐ X ∂gibbs V W M, |trCfgA e f X| ≤ B := by
  subst e; exact hf

/-- The comparison inequality at particle number `N`. -/
def CmpIneqA (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (b : ℝ≥0∞) (ε : ℝ) (N : ℕ)
    (f : Config N d → ℝ) : Prop :=
  b / 2 * ent (gibbs V W N) (fun X => f X ^ 2) ≤ energy V W N f + ENNReal.ofReal ε

theorem cmpIneqA_trCfgA {b : ℝ≥0∞} {ε : ℝ} {N M : ℕ} (e : N = M) (f : Config N d → ℝ) :
    CmpIneqA V W b ε M (trCfgA e f) ↔ CmpIneqA V W b ε N f := by
  subst e; exact Iff.rfl

/-- The zero function is in `H¹(P_N)`. -/
theorem memH1C_zeroA (hyp : Hyp V W KV KW) (N : ℕ) :
    MemH1C (gibbs V W N) (fun _ : Config N d => (0 : ℝ)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac := (gibbs_map_flat_ac hyp N).1
  have h0 : IsWeakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) 0 := isWeakGrad_const 0
  refine ⟨⟨_, h0⟩, memLp_const 0, ?_⟩
  refine (memLp_const (0 : ℝ)).ae_eq ?_
  filter_upwards [hac.ae_le (weakGrad_ae_eq h0)] with y hy
  change (0 : ℝ) = Real.sqrt (sqNorm (weakGrad (fun _ : UnitAddTorus (Fin N × Fin d) => (0 : ℝ)) y))
  rw [hy]; simp [sqNorm]

theorem energy_zeroA (hyp : Hyp V W KV KW) (N : ℕ) :
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

/-- **WP-I (alt).** The `N`-indexed core implies the subsequence form (the body of
`BoundedComparison V W b`). -/
theorem boundedComparison_unfolded {b : ℝ≥0∞} (hyp : Hyp V W KV KW)
    (hcore : PropBoundedCore V W b) :
    ∀ (Ns : ℕ → ℕ), Tendsto Ns atTop atTop → ∀ f : (k : ℕ) → Config (Ns k) d → ℝ,
      (∀ k, MemH1C (gibbs V W (Ns k)) (f k)) →
      (∃ B : NNReal, ∀ k, (∀ᵐ X ∂gibbs V W (Ns k), |f k X| ≤ B) ∧
        energy V W (Ns k) (f k) ≤ B) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        b / 2 * ent (gibbs V W (Ns k)) (fun X => f k X ^ 2) ≤
          energy V W (Ns k) (f k) + ENNReal.ofReal ε := by
  classical
  intro Ns hNs f hmem hB ε hε
  obtain ⟨B, hB⟩ := hB
  by_contra hcon
  have hfr : ∃ᶠ k in atTop, ¬ CmpIneqA V W b ε (Ns k) (f k) := not_eventually.mp hcon
  -- the padded family
  let F : (N : ℕ) → Config N d → ℝ := fun N =>
    if hh : ∃ k, ¬ CmpIneqA V W b ε (Ns k) (f k) ∧ Ns k = N then
      trCfgA hh.choose_spec.2 (f hh.choose) else fun _ => 0
  have hFadm : ∀ N, MemH1C (gibbs V W N) (F N) ∧ (∀ᵐ X ∂gibbs V W N, |F N X| ≤ B) ∧
      energy V W N (F N) ≤ B := by
    intro N
    by_cases hh : ∃ k, ¬ CmpIneqA V W b ε (Ns k) (f k) ∧ Ns k = N
    · have : F N = trCfgA hh.choose_spec.2 (f hh.choose) := by simp only [F, dif_pos hh]
      rw [this]
      exact ⟨memH1C_trCfgA _ (hmem _), ae_bound_trCfgA _ (hB _).1,
        (energy_trCfgA _ _).le.trans (hB _).2⟩
    · have : F N = fun _ => 0 := by simp only [F, dif_neg hh]
      rw [this]
      refine ⟨memH1C_zeroA hyp N, ?_, by rw [energy_zeroA hyp N]; exact zero_le⟩
      exact Eventually.of_forall fun X => by simp
  have hev := hcore F (fun N => (hFadm N).1) ⟨B, fun N => ⟨(hFadm N).2.1, (hFadm N).2.2⟩⟩ ε hε
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hev
  have hlarge : ∀ᶠ k in atTop, N0 ≤ Ns k := hNs.eventually_ge_atTop N0
  obtain ⟨k, hk, hkN⟩ := (hfr.and_eventually hlarge).exists
  have hh : ∃ k', ¬ CmpIneqA V W b ε (Ns k') (f k') ∧ Ns k' = Ns k := ⟨k, hk, rfl⟩
  have hFk : F (Ns k) = trCfgA hh.choose_spec.2 (f hh.choose) := by simp only [F, dif_pos hh]
  have := hN0 (Ns k) hkN
  change CmpIneqA V W b ε (Ns k) (F (Ns k)) at this
  rw [hFk, cmpIneqA_trCfgA] at this
  exact hh.choose_spec.1 this

end SharpLSI.FL
