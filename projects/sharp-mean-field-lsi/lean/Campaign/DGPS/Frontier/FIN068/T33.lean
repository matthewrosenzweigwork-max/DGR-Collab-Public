import DGPS.Frontier.FIN068.T32

/-!
Task id and title: FIN068.33, Quantitative derivative patch (module `DGPS.Frontier.FIN068.T33`).

Provides:
* `DGPS.Frontier.FIN068.fin068_33_quantitative_derivative_patch`: the full conclusion of FIN068.32
  (the curve `a`, the patch `P = (-4-δx, -4+δx) × (-δy, δy)`, the factor `a₂`, and the signed
  coordinate `v` with its smoothness, energy identity and base-point values, all exactly as stated
  there), together with an open set `U` such that `(-4, 0) ∈ U ⊆ P` and, for every `p ∈ U`,
  `sqrt A / 2 ≤ v_x p ≤ 2 sqrt A` and `|v_y p| ≤ 1`, where `v_x p = fderiv ℝ v p (1, 0)`,
  `v_y p = fderiv ℝ v p (0, 1)` and `A = quarticA_FIN06803`.
* Helper declarations, all with suffix `_FIN06833` (not part of the interface): none. The proof uses
  the continuity of `fderiv` on the open patch (`ContDiffOn.continuousOn_fderiv_of_isOpen`) and
  `ContinuousOn.isOpen_inter_preimage`, applied to the two partial derivatives.

R5 notes:
* No hypothesis is added. The statement is closed: it is an existential over the FIN068.32 data.
  The FIN068.32 conclusion is restated inline (with the same binder names and the same shape) rather
  than imported as a hypothesis, so that the theorem is unconditional and the consuming tasks see the
  patch, the coordinate `v` and the neighborhood in one statement.
* "Open neighborhood of `(-4,0)`" is read as `IsOpen U ∧ (-4, 0) ∈ U`, with `U` required to lie in
  the FIN068.32 patch `P` ("intersect them with the patch from 31"). The bounds are required only on
  `U`, not on all of `P`; `U` is existentially chosen, as the specification says "choose".
* The inequalities are non-strict, as written in the specification: `sqrt A / 2 ≤ v_x`,
  `v_x ≤ 2 * sqrt A`, and `|v_y| ≤ 1`. The strict versions hold on a smaller neighborhood by continuity.
* `v_x` and `v_y` are read as the Fréchet derivative `fderiv ℝ v p` evaluated at the unit vectors
  `(1, 0)` and `(0, 1)` of `ℝ × ℝ`, following FIN068.32. `sqrt` is `Real.sqrt`, and `A` is
  `quarticA_FIN06803` (positivity `0 < A` from FIN068.03 gives `0 < sqrt A`).
* The specification's "continuity of the two partial derivatives" is read as continuity of
  `fderiv ℝ v` on the open patch, which follows from `v` being `C^∞` there (FIN068.32).
* Dependency: the smoothness of `v` on `P` inherits the FIN068.27 / FIN068.37 / FIN068.38
  identifications through FIN068.32; this file adds nothing to them.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- Quantitative derivative patch (FIN068.33): the FIN068.32 data, together with an open
neighborhood `U ⊆ P` of `(-4, 0)` on which `sqrt A / 2 ≤ v_x ≤ 2 sqrt A` and `|v_y| ≤ 1`. -/
theorem fin068_33_quantitative_derivative_patch :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-δy) δy) ∧
        deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y])
          (Set.Ioo (-δy) δy) ∧
        ∃ a₂ : ℝ × ℝ → ℝ,
          (∀ p : ℝ × ℝ, a₂ p = 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
            deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
              (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2))))) ∧
          ContDiffOn ℝ ∞ a₂ (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
          a₂ (-4, 0) = quarticA_FIN06803 ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticA_FIN06803 / 2 ≤ a₂ (x, y) ∧ a₂ (x, y) ≤ 2 * quarticA_FIN06803) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] =
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) ∧
          ∃ v : ℝ × ℝ → ℝ,
            (∀ p : ℝ × ℝ, v p = (p.1 - (-4 + a (p.2 ^ 2))) * Real.sqrt (a₂ p)) ∧
            ContDiffOn ℝ ∞ v (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
            (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
              quarticPsi_FIN066 !₂[x, y] =
                v (x, y) ^ 2 / 2 + quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]) ∧
            v (-4, 0) = 0 ∧
            fderiv ℝ v (-4, 0) (1, 0) = Real.sqrt quarticA_FIN06803 ∧
            fderiv ℝ v (-4, 0) (0, 1) = 0 ∧
            ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (-4, 0) ∈ U ∧
              U ⊆ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy ∧
              ∀ p ∈ U, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                |fderiv ℝ v p (0, 1)| ≤ 1 := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy⟩ :=
    fin068_32_smooth_signed_coordinate_base_derivative
  obtain ⟨-, -, hApos, -⟩ := fin068_03_constants_exact_cancellation
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, ?_⟩
  have hPo : IsOpen (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hcont : ContinuousOn (fderiv ℝ v) (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) :=
    hvsm.continuousOn_fderiv_of_isOpen hPo (by simp)
  have hg : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ v p (1, 0))
      (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) :=
    hcont.clm_apply continuousOn_const
  have hk : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ v p (0, 1))
      (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) :=
    hcont.clm_apply continuousOn_const
  have hA : 0 < Real.sqrt quarticA_FIN06803 := Real.sqrt_pos.2 hApos
  have hU1 : IsOpen (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy ∩
      (fun p : ℝ × ℝ => fderiv ℝ v p (1, 0)) ⁻¹'
        Set.Ioo (Real.sqrt quarticA_FIN06803 / 2) (2 * Real.sqrt quarticA_FIN06803)) :=
    hg.isOpen_inter_preimage hPo isOpen_Ioo
  have hU2 : IsOpen ((Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy ∩
      (fun p : ℝ × ℝ => fderiv ℝ v p (1, 0)) ⁻¹'
        Set.Ioo (Real.sqrt quarticA_FIN06803 / 2) (2 * Real.sqrt quarticA_FIN06803)) ∩
      (fun p : ℝ × ℝ => fderiv ℝ v p (0, 1)) ⁻¹' Set.Ioo (-1 : ℝ) 1) :=
    (hk.mono (fun p hp => hp.1)).isOpen_inter_preimage hU1 isOpen_Ioo
  have hP0 : ((-4 : ℝ), (0 : ℝ)) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hg0 : fderiv ℝ v (-4, 0) (1, 0) ∈
      Set.Ioo (Real.sqrt quarticA_FIN06803 / 2) (2 * Real.sqrt quarticA_FIN06803) := by
    rw [hvx]
    exact ⟨by linarith, by linarith⟩
  have hk0 : fderiv ℝ v (-4, 0) (0, 1) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hvy]
    exact ⟨by norm_num, by norm_num⟩
  refine ⟨_, hU2, ⟨⟨hP0, hg0⟩, hk0⟩, fun p hp => hp.1.1, ?_⟩
  rintro p ⟨⟨-, hgp⟩, hkp⟩
  have hgp' : Real.sqrt quarticA_FIN06803 / 2 < fderiv ℝ v p (1, 0) ∧
      fderiv ℝ v p (1, 0) < 2 * Real.sqrt quarticA_FIN06803 := hgp
  have hkp' : -1 < fderiv ℝ v p (0, 1) ∧ fderiv ℝ v p (0, 1) < 1 := hkp
  refine ⟨hgp'.1.le, hgp'.2.le, ?_⟩
  rw [abs_le]
  exact ⟨hkp'.1.le, hkp'.2.le⟩

end DGPS.Frontier.FIN068
