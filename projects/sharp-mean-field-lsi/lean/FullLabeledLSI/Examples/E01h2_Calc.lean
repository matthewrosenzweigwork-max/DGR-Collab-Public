import FullLabeledLSI.Examples.E01h0_Defs

/-!
# Lane D, Task B: calculus on the circle (`dT` through the periodic lift)

`lift1 t` is the point `t mod 1` of `Torus 1`.  `dT f (lift1 t) = d/dt f(lift1 t)` for every `f`
(the derivative of a 1-periodic function is 1-periodic), `dT` of a smooth function is smooth, and
`dT (cm n) = -2πn sm n`, `dT (sm n) = 2πn cm n`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- The point `t mod 1` of the circle `Torus 1`. -/
def lift1 (t : ℝ) : Torus 1 := liftT (fun _ : Fin 1 => t)

theorem liftT_eq_lift1 (x : Fin 1 → ℝ) : liftT x = lift1 (x 0) := by
  funext i; fin_cases i; rfl

theorem lift1_apply (t : ℝ) : lift1 t 0 = (t : UnitAddCircle) := rfl

theorem lift1_add_int (t : ℝ) (n : ℤ) : lift1 (t + n) = lift1 t := by
  funext i
  fin_cases i
  show ((t + n : ℝ) : UnitAddCircle) = (t : UnitAddCircle)
  rw [QuotientAddGroup.eq]
  refine ⟨-n, ?_⟩
  simp

theorem rep_spec (x : Torus 1) : ((rep x : ℝ) : UnitAddCircle) = x 0 :=
  (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (x 0)).choose_spec

theorem lift1_rep (x : Torus 1) : lift1 (rep x) = x := by
  funext i; fin_cases i; exact rep_spec x

theorem exists_int_rep (t : ℝ) : ∃ n : ℤ, rep (lift1 t) = t + n := by
  have h := rep_spec (lift1 t)
  have h2 : ((rep (lift1 t) : ℝ) : UnitAddCircle) = (t : UnitAddCircle) := h
  rw [QuotientAddGroup.eq] at h2
  obtain ⟨n, hn⟩ := h2
  refine ⟨-n, ?_⟩
  simp at hn
  push_cast
  linarith

/-- The derivative of a 1-periodic function is 1-periodic. -/
theorem deriv_periodic_int {F : ℝ → ℝ} (hF : ∀ t, F (t + 1) = F t) (n : ℤ) (t : ℝ) :
    deriv F (t + n) = deriv F t := by
  have hp : Function.Periodic F 1 := hF
  have h1 : (fun s => F (s + n)) = F := funext fun s => by simpa using (hp.int_mul n) s
  have h2 := deriv_comp_add_const (f := F) (a := (n : ℝ)) (x := t)
  rw [h1] at h2
  exact h2.symm

/-- `dT f (lift1 t) = d/dt f (lift1 t)`. -/
theorem dT_lift1 (f : Torus 1 → ℝ) (t : ℝ) :
    dT f (lift1 t) = deriv (fun s => f (lift1 s)) t := by
  unfold dT
  obtain ⟨n, hn⟩ := exists_int_rep t
  have hF : ∀ s, (fun s => f (liftT fun _ : Fin 1 => s)) (s + 1) = (fun s => f (liftT fun _ : Fin 1 => s)) s := by
    intro s
    have := lift1_add_int s 1
    simpa [lift1] using congrArg f this
  have h := deriv_periodic_int (F := fun s => f (liftT fun _ : Fin 1 => s)) hF n t
  rw [hn]
  exact h

theorem dT_apply (f : Torus 1 → ℝ) (x : Torus 1) : dT f x = deriv (fun s => f (lift1 s)) (rep x) := by
  conv_lhs => rw [← lift1_rep x]
  exact dT_lift1 f _

theorem isSmoothT_iff_lift1 {f : Torus 1 → ℝ} : IsSmoothT f ↔ ContDiff ℝ ∞ (fun t : ℝ => f (lift1 t)) := by
  constructor
  · intro h
    have : (fun t : ℝ => f (lift1 t)) = (f ∘ liftT) ∘ (fun t : ℝ => fun _ : Fin 1 => t) := rfl
    rw [this]
    exact h.comp (contDiff_pi.2 fun _ => contDiff_id)
  · intro h
    have : f ∘ liftT = (fun t : ℝ => f (lift1 t)) ∘ (fun x : Fin 1 → ℝ => x 0) := by
      funext x; simp [Function.comp, liftT_eq_lift1]
    unfold IsSmoothT
    rw [this]
    exact h.comp (contDiff_apply ℝ ℝ 0)

theorem isSmoothT_dT {f : Torus 1 → ℝ} (hf : IsSmoothT f) : IsSmoothT (dT f) := by
  rw [isSmoothT_iff_lift1] at hf ⊢
  have : (fun t : ℝ => dT f (lift1 t)) = deriv (fun s => f (lift1 s)) := funext fun t => dT_lift1 f t
  rw [this]
  exact (contDiff_infty_iff_deriv.mp hf).2

theorem continuous_of_smooth {f : Torus 1 → ℝ} (hf : IsSmoothT f) : Continuous f :=
  Sec8.continuous_of_isSmoothT hf

end SharpLSI.FL.Ex.LaneD
