import DGPS.Frontier.FIN068.T22

/-!
Task id and title: FIN068.06, Weighted Taylor remainder (module `DGPS.Frontier.FIN068.T06`).

Provides:
* `DGPS.Frontier.FIN068.fin068_06_weighted_taylor_remainder`: let `δ < 1`,
  `B = {|u| ≤ δ, |z| ≤ δ}` (`fixedRect_FIN06819 δ`), `J = fun q => liftPotential_FIN06804 q.1 q.2`
  on `ℝ × ℝ` and `P = quadP_FIN06820`, so `P(u,z) = J(0,0) + A u²/2 - d u z/32 + d z²/512`. If `M₃`
  bounds the third derivative of `J` on `B` in the `ℓ¹` form of FIN068.19 (hypothesis `hM`), then
  for every `h ∈ B`, writing `‖h‖₁ = |h.1| + |h.2|`: (i) `|J(h) - P(h)| ≤ (M₃/6) ‖h‖₁³`;
  (ii) `|D(J-P)(h)[v]| ≤ (M₃/2) ‖h‖₁² ‖v‖₁` for all `v`; (iii)
  `|D²(J-P)(h)[v,w]| ≤ M₃ ‖h‖₁ ‖v‖₁ ‖w‖₁` for all `v, w`.
* `DGPS.Frontier.FIN068.fin068_06_weighted_taylor_remainder_exists`: there are `δ ∈ (0,1)` and
  `M₃ ≥ 0` with `B ⊆ (-1,1)²`, segments from zero staying in `B`, the third derivative bound `hM` on
  `B`, and the three remainder bounds of the main declaration at every point of `B`.
* `DGPS.Frontier.FIN068.fin068_06_weighted_taylor_remainder_weighted`: after `z = y²`, for
  `|u| ≤ δ` and `y² ≤ δ`, `|J(u,y²) - P(u,y²)| ≤ (M₃/6) (|u| + y²)³`.

Proof: assembly. The three bounds are exactly FIN068.22 (value), FIN068.21 (gradient) and FIN068.20
(Hessian, with `D²(J-P) = D²J - D²P` at points of the patch, as in FIN068.21). The existence
declaration takes `δ` and `M₃` from FIN068.20 (which combines FIN068.19).

R5 notes:
* Hypotheses: `δ < 1` (the patch condition of FIN068.19 to FIN068.22) and `hM`, which says that
  `M₃` bounds the third derivative of `J` on `B`. These are the hypotheses of FIN068.20 to
  FIN068.22. "Sufficiently small closed rectangle" is read as `δ < 1`, and the existence
  declaration supplies a concrete `δ = 1/2` via FIN068.19. `0 < δ` and `0 ≤ M₃` are not used in the
  main declaration.
* Norms: the specification's norms are read in the directional `ℓ¹` form used in FIN068.19 to
  FIN068.22: `‖(a,b)‖₁ = |a| + |b|`, `‖D(J-P)(h)‖ ≤ c` as `|D(J-P)(h)[v]| ≤ c ‖v‖₁` for all `v`, and
  `‖D²(J-P)(h)‖ ≤ c` as `|D²(J-P)(h)[v,w]| ≤ c ‖v‖₁ ‖w‖₁` for all `v, w`. No Mathlib operator norm
  on `ℝ × ℝ` (the sup norm) and no custom `ℓ¹` instance is used.
* The second derivative of `J - P` is written as `iteratedFDeriv ℝ 2 (J - P) h ![v, w]` with the
  difference function written out as a lambda; this is `fderiv (fderiv (J-P)) h v w`.
* The integral form of the proof is replaced by the mean value and boundary inequalities proved in
  FIN068.20 to FIN068.22, which give the same constants `1`, `1/2`, `1/6`.
* `J(0,0)` in `P` is `liftPotential_FIN06804 0 0`; `A = quarticB/5 - deriv besselRatio 4` and
  `d = quarticB - 4 * deriv besselRatio 4` are as in FIN068.20. "The frozen weighted expansion"
  is not restated beyond the `z = y²` corollary for the value bound; the `z = y²` bound uses
  `|y²| = y²` and the requirement `y² ≤ δ` so that `(u, y²) ∈ B`.
* `M₃` is carried as an explicit parameter and is not computed. No definition body of FIN068.37 or
  FIN068.38 is used.
-/

namespace DGPS.Frontier.FIN068

/-- Weighted Taylor remainder: value, gradient and Hessian bounds for `J - P` on the rectangle. -/
theorem fin068_06_weighted_taylor_remainder (δ M₃ : ℝ) (hδ1 : δ < 1)
    (hM : ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) :
    ∀ h ∈ fixedRect_FIN06819 δ,
      |liftPotential_FIN06804 h.1 h.2 - quadP_FIN06820 h| ≤ M₃ / 6 * (|h.1| + |h.2|) ^ 3 ∧
      (∀ v : ℝ × ℝ,
        |fderiv ℝ (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q) h v| ≤
          M₃ / 2 * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|)) ∧
      (∀ v w : ℝ × ℝ,
        |iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q)
            h ![v, w]| ≤
          M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) := by
  intro h hh
  refine ⟨fin068_22_value_remainder δ M₃ hδ1 hM h hh,
    fin068_21_gradient_remainder δ M₃ hδ1 hM h hh, fun v w => ?_⟩
  have hpatch := mem_patch_FIN06821 hδ1 hh
  have heq := fderiv_fderiv_remF_FIN06821 h v w hpatch
  have hi : iteratedFDeriv ℝ 2 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q)
      h ![v, w] = fderiv ℝ (fderiv ℝ remF_FIN06821) h v w := by
    rw [iteratedFDeriv_two_apply]
    rfl
  rw [hi, heq]
  exact fin068_20_hessian_remainder δ M₃ hδ1 hM h hh v w

/-- Existence of a rectangle and a constant with all hypotheses and the three remainder bounds. -/
theorem fin068_06_weighted_taylor_remainder_exists :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      fixedRect_FIN06819 δ ⊆ Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1 ∧
      (∀ p ∈ fixedRect_FIN06819 δ, segment ℝ (0 : ℝ × ℝ) p ⊆ fixedRect_FIN06819 δ) ∧
      ∃ M₃ : ℝ, 0 ≤ M₃ ∧
        (∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
          |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
            M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) ∧
        ∀ h ∈ fixedRect_FIN06819 δ,
          |liftPotential_FIN06804 h.1 h.2 - quadP_FIN06820 h| ≤ M₃ / 6 * (|h.1| + |h.2|) ^ 3 ∧
          (∀ v : ℝ × ℝ,
            |fderiv ℝ (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q) h v| ≤
              M₃ / 2 * (|h.1| + |h.2|) ^ 2 * (|v.1| + |v.2|)) ∧
          (∀ v w : ℝ × ℝ,
            |iteratedFDeriv ℝ 2
                (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2 - quadP_FIN06820 q) h ![v, w]| ≤
              M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|)) := by
  obtain ⟨δ, hδ0, hδ1, hsub, hseg, M₃, hM₃, hM, -⟩ := fin068_20_hessian_remainder_exists
  exact ⟨δ, hδ0, hδ1, hsub, hseg, M₃, hM₃, hM, fin068_06_weighted_taylor_remainder δ M₃ hδ1 hM⟩

/-- The value remainder after the substitution `z = y²`. -/
theorem fin068_06_weighted_taylor_remainder_weighted (δ M₃ : ℝ) (hδ1 : δ < 1)
    (hM : ∀ x ∈ fixedRect_FIN06819 δ, ∀ h v w : ℝ × ℝ,
      |iteratedFDeriv ℝ 3 (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) x ![h, v, w]| ≤
        M₃ * (|h.1| + |h.2|) * (|v.1| + |v.2|) * (|w.1| + |w.2|))
    (u y : ℝ) (hu : |u| ≤ δ) (hy : y ^ 2 ≤ δ) :
    |liftPotential_FIN06804 u (y ^ 2) - quadP_FIN06820 (u, y ^ 2)| ≤
      M₃ / 6 * (|u| + y ^ 2) ^ 3 := by
  have hmem : (u, y ^ 2) ∈ fixedRect_FIN06819 δ := by
    refine ⟨hu, ?_⟩
    show |y ^ 2| ≤ δ
    rw [abs_of_nonneg (sq_nonneg y)]
    exact hy
  have h := (fin068_06_weighted_taylor_remainder δ M₃ hδ1 hM _ hmem).1
  simpa [abs_of_nonneg (sq_nonneg y)] using h

end DGPS.Frontier.FIN068
