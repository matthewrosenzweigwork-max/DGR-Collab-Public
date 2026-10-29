import Mathlib

/-!
# Finite-rank uniform approximation of continuous kernels (lane s42; R16)

Stone–Weierstrass on `X × Y` (compact metric spaces): every continuous `F : X × Y → ℝ` is a
uniform limit of finite sums `∑ᵢ fᵢ(x) gᵢ(y)` with `fᵢ`, `gᵢ` continuous. Used in the proof of
Lemma 4.2 (the finite-rank approximation of the interaction).
-/

noncomputable section
open ContinuousMap

namespace SharpLSI

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- `h` is a finite sum of products `∑ᵢ fᵢ(x) gᵢ(y)`. -/
def IsFiniteRank (h : C(X × Y, ℝ)) : Prop :=
  ∃ n : ℕ, ∃ f : Fin n → C(X, ℝ), ∃ g : Fin n → C(Y, ℝ), ∀ p, h p = ∑ i, f i p.1 * g i p.2

theorem isFiniteRank_add {h₁ h₂ : C(X × Y, ℝ)} (h₁r : IsFiniteRank h₁) (h₂r : IsFiniteRank h₂) :
    IsFiniteRank (h₁ + h₂) := by
  obtain ⟨n, f, g, hfg⟩ := h₁r
  obtain ⟨m, f', g', hfg'⟩ := h₂r
  refine ⟨n + m, Fin.append f f', Fin.append g g', fun p => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [ContinuousMap.add_apply, Fin.append_left, Fin.append_right, hfg, hfg']

theorem isFiniteRank_mul {h₁ h₂ : C(X × Y, ℝ)} (h₁r : IsFiniteRank h₁) (h₂r : IsFiniteRank h₂) :
    IsFiniteRank (h₁ * h₂) := by
  obtain ⟨n, f, g, hfg⟩ := h₁r
  obtain ⟨m, f', g', hfg'⟩ := h₂r
  refine ⟨n * m, fun k => f (finProdFinEquiv.symm k).1 * f' (finProdFinEquiv.symm k).2,
    fun k => g (finProdFinEquiv.symm k).1 * g' (finProdFinEquiv.symm k).2, fun p => ?_⟩
  rw [ContinuousMap.mul_apply, hfg, hfg', Finset.sum_mul_sum,
    ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.symm_apply_apply, ContinuousMap.mul_apply]
  ring

theorem isFiniteRank_const (c : ℝ) : IsFiniteRank (ContinuousMap.const (X × Y) c) :=
  ⟨1, fun _ => ContinuousMap.const X c, fun _ => 1, fun p => by simp⟩

/-- The subalgebra of finite sums of products. -/
def finiteRankSubalgebra : Subalgebra ℝ C(X × Y, ℝ) where
  carrier := {h | IsFiniteRank h}
  mul_mem' := isFiniteRank_mul
  add_mem' := isFiniteRank_add
  algebraMap_mem' c := by
    have : algebraMap ℝ C(X × Y, ℝ) c = ContinuousMap.const (X × Y) c := by ext; simp
    rw [Set.mem_ofPred_eq, this]; exact isFiniteRank_const c

theorem finiteRankSubalgebra_separatesPoints :
    (finiteRankSubalgebra (X := X) (Y := Y)).SeparatesPoints := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
    let k : C(Y, ℝ) := ⟨fun y => dist y q.2, continuous_id.dist continuous_const⟩
    let h : C(X × Y, ℝ) := ⟨fun r => dist r.2 q.2, continuous_snd.dist continuous_const⟩
    have hmem : h ∈ finiteRankSubalgebra (X := X) (Y := Y) :=
      ⟨1, fun _ => 1, fun _ => k, fun r => by simp [h, k]⟩
    refine ⟨⇑h, ⟨h, hmem, rfl⟩, ?_⟩
    show dist p.2 q.2 ≠ dist q.2 q.2
    rw [dist_self]; exact dist_ne_zero.mpr h2
  · let k : C(X, ℝ) := ⟨fun x => dist x q.1, continuous_id.dist continuous_const⟩
    let h : C(X × Y, ℝ) := ⟨fun r => dist r.1 q.1, continuous_fst.dist continuous_const⟩
    have hmem : h ∈ finiteRankSubalgebra (X := X) (Y := Y) :=
      ⟨1, fun _ => k, fun _ => 1, fun r => by simp [h, k]⟩
    refine ⟨⇑h, ⟨h, hmem, rfl⟩, ?_⟩
    show dist p.1 q.1 ≠ dist q.1 q.1
    rw [dist_self]; exact dist_ne_zero.mpr h1

variable [CompactSpace X] [CompactSpace Y]

/-- **Finite-rank uniform approximation.** -/
theorem exists_finiteRank_approx {F : X → Y → ℝ} (hF : Continuous (Function.uncurry F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ f : Fin n → C(X, ℝ), ∃ g : Fin n → C(Y, ℝ),
      ∀ x y, |F x y - ∑ i, f i x * g i y| < ε := by
  set F' : C(X × Y, ℝ) := ⟨Function.uncurry F, hF⟩ with hF'
  obtain ⟨g', hh⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (finiteRankSubalgebra (X := X) (Y := Y)) finiteRankSubalgebra_separatesPoints F' ε hε
  have hr : IsFiniteRank (g' : C(X × Y, ℝ)) := g'.2
  obtain ⟨n, f, g, hfg⟩ := hr
  refine ⟨n, f, g, fun x y => ?_⟩
  have h1 := (ContinuousMap.norm_coe_le_norm ((g' : C(X × Y, ℝ)) - F') (x, y)).trans_lt hh
  have h2 : ((g' : C(X × Y, ℝ)) - F') (x, y) = (∑ i, f i x * g i y) - F x y := by
    rw [ContinuousMap.sub_apply, hfg]; rfl
  rw [h2, Real.norm_eq_abs, abs_sub_comm] at h1
  exact h1

end SharpLSI
