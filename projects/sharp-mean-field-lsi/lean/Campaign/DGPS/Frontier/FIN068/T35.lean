import DGPS.Frontier.FIN068.T34

/-!
Task id and title: FIN068.35, Inverse derivatives and Jacobian (module
`DGPS.Frontier.FIN068.T35`).

Provides:
* `DGPS.Frontier.FIN068.fin068_35_inverse_derivatives_jacobian`: the full conclusion of
  FIN068.34 (the curve `a`, the patch `P`, the factor `a₂`, the signed coordinate `v`, the
  neighborhood `U`, the open set `N`, the rectangle `Q = (-ε, ε) × (-δ, δ)`, the inverse
  `X`, and the restricted source patch `W`), exactly as stated there, together with two
  conjuncts on the fixed rectangle `Q`. For every `q ∈ Q`, with source point `p = (X q, q.2)`:
  `X_v q = 1 / v_x p` and `X_y q = -v_y p / v_x p`, where `X_v q = fderiv ℝ X q (1, 0)`,
  `X_y q = fderiv ℝ X q (0, 1)`, `v_x p = fderiv ℝ v p (1, 0)` and `v_y p = fderiv ℝ v p (0, 1)`;
  and the density Jacobian `j q = X_v q` satisfies `1 / (2 sqrt A) ≤ j q ≤ 2 / sqrt A`.
* `DGPS.Frontier.FIN068.lin_FIN06835` (helper, not part of the interface): a continuous linear
  map `L : ℝ × ℝ →L[ℝ] ℝ` satisfies `L (a, b) = a * L (1, 0) + b * L (0, 1)`.

Proof: the FIN068.34 data is obtained and restated. For `q ∈ Q`, the map `q ↦ (X q, q.2)` is
differentiable at `q` with derivative `(fderiv ℝ X q).prod snd`, and `v` is differentiable at its
value `p ∈ W ⊆ U ⊆ P`. Since `v (X q, q.2) = q.1` on the open set `Q`, the chain rule and
uniqueness of the derivative give `fderiv ℝ v p (X_v q, 0) = 1` and
`fderiv ℝ v p (X_y q, 1) = 0`. Linearity of `fderiv ℝ v p` yields `X_v q * v_x p = 1` and
`X_y q * v_x p = -v_y p`. Since `v_x p ≥ sqrt A / 2 > 0` on `W`, division is allowed. The density
bounds follow from `v_x p ≤ 2 sqrt A` and `v_x p ≥ sqrt A / 2`.

R5 notes:
* No hypothesis is added. The statement is closed (an existential over the FIN068.34 data). The
  FIN068.34 conclusion is restated inline with the same binder names, so that the consuming tasks
  see the inverse, the derivative identities and the Jacobian bounds in one statement. The two new
  conjuncts are appended at the innermost level, after `X (v p, p.2) = p.1`.
* "Write the inverse as `(v, y) ↦ (X (v, y), y)`" is the map `q ↦ (X q, q.2)` of FIN068.34, with
  `X` only constrained on the open rectangle `Q`, where `q ↦ (X q, q.2)` is `C^∞` with values in `W`.
* "Evaluated at the corresponding source point" is read as evaluation at `p = (X q, q.2) ∈ W`,
  the point mapped to `q` by `T (x, y) = (v (x, y), y)`.
* `X_v` and `X_y` are the Fréchet derivative `fderiv ℝ X q` at `q` (an interior point of the open
  set `Q`, where `X` is `C^∞`) evaluated at the unit vectors `(1, 0)` and `(0, 1)`. Values of `X`
  outside `Q` play no role.
* `v_x`, `v_y` are `fderiv ℝ v p (1, 0)` and `fderiv ℝ v p (0, 1)`, as in FIN068.33/34.
* The density Jacobian `j` is read as `j = X_v`, the (1,1) entry of the Jacobian matrix of the
  inverse map `q ↦ (X q, q.2)`, which is triangular `[[X_v, X_y], [0, 1]]`. Its determinant is
  `X_v` and is positive by the lower bound. The determinant is not stated as a separate conjunct,
  since the specification states only `X_v`, `X_y` and the bound on `j = X_v`.
* The specification's `1/(2 sqrt A)` and `2/sqrt A` are `1 / (2 * Real.sqrt quarticA_FIN06803)`
  and `2 / Real.sqrt quarticA_FIN06803`. Bounds are non-strict, as in FIN068.33/34. The positivity
  `0 < A` comes from FIN068.03 and is used to divide by `v_x`.
* The partial derivative `X_y` is written `(-v_y) / v_x`, i.e. the specification's `-v_y/v_x`.
* Dependency: none beyond FIN068.34 (through the FIN068.33 and FIN068.32 identifications it
  inherits).
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the unit vectors. -/
lemma lin_FIN06835 (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) :
    L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have h : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Inverse derivatives and Jacobian (FIN068.35): the FIN068.34 data, together with the identities
`X_v = 1 / v_x` and `X_y = -v_y / v_x` at the source point `(X q, q.2)` for every `q` in the fixed
rectangle `Q`, and the density bounds `1 / (2 sqrt A) ≤ X_v ≤ 2 / sqrt A` on `Q`. -/
theorem fin068_35_inverse_derivatives_jacobian :
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
              (∀ p ∈ U, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                |fderiv ℝ v p (0, 1)| ≤ 1) ∧
              ∃ N : Set (ℝ × ℝ), IsOpen N ∧ (-4, 0) ∈ N ∧ N ⊆ U ∧
                Set.InjOn (fun p : ℝ × ℝ => (v p, p.2)) N ∧
                IsOpen ((fun p : ℝ × ℝ => (v p, p.2)) '' N) ∧
                ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
                  closure (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ⊆
                    (fun p : ℝ × ℝ => (v p, p.2)) '' N ∧
                  ∃ X : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ X (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                    ∃ W : Set (ℝ × ℝ),
                      W = N ∩ (fun p : ℝ × ℝ => (v p, p.2)) ⁻¹'
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      IsOpen W ∧ (-4, 0) ∈ W ∧ W ⊆ N ∧
                      (∀ p ∈ W, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                        fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                        |fderiv ℝ v p (0, 1)| ≤ 1) ∧
                      Set.BijOn (fun p : ℝ × ℝ => (v p, p.2)) W
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (v p, p.2)) W ∧
                      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2))
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, (X q, q.2) ∈ W) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, v (X q, q.2) = q.1) ∧
                      (∀ p ∈ W, X (v p, p.2) = p.1) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        fderiv ℝ X q (1, 0) = 1 / fderiv ℝ v (X q, q.2) (1, 0) ∧
                        fderiv ℝ X q (0, 1) =
                          (-fderiv ℝ v (X q, q.2) (0, 1)) / fderiv ℝ v (X q, q.2) (1, 0)) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        1 / (2 * Real.sqrt quarticA_FIN06803) ≤ fderiv ℝ X q (1, 0) ∧
                        fderiv ℝ X q (1, 0) ≤ 2 / Real.sqrt quarticA_FIN06803) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb,
    N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl, X, hX, W, hWdef, hWo, hW0, hWN, hWb,
    hbij, hTs, hXs, hXW, hXv, hXinv⟩ := fin068_34_smooth_inverse_fixed_image_rectangle
  obtain ⟨-, -, hApos, -⟩ := fin068_03_constants_exact_cancellation
  have hA : 0 < Real.sqrt quarticA_FIN06803 := Real.sqrt_pos.2 hApos
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb,
    N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl, X, hX, W, hWdef, hWo, hW0, hWN, hWb,
    hbij, hTs, hXs, hXW, hXv, hXinv, ?_⟩
  have hQo : IsOpen (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) := isOpen_Ioo.prod isOpen_Ioo
  have hPo : IsOpen (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hkey : ∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
      fderiv ℝ X q (1, 0) * fderiv ℝ v (X q, q.2) (1, 0) = 1 ∧
      fderiv ℝ X q (0, 1) * fderiv ℝ v (X q, q.2) (1, 0) = -fderiv ℝ v (X q, q.2) (0, 1) := by
    intro q hq
    have hXd : HasFDerivAt X (fderiv ℝ X q) q :=
      ((hX.differentiableOn (by simp)).differentiableAt (hQo.mem_nhds hq)).hasFDerivAt
    have hGd : HasFDerivAt (fun r : ℝ × ℝ => (X r, r.2))
        ((fderiv ℝ X q).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) q :=
      hXd.prodMk hasFDerivAt_snd
    have hpU : (X q, q.2) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy :=
      hUP (hNU (hWN (hXW q hq)))
    have hvd : HasFDerivAt v (fderiv ℝ v (X q, q.2)) (X q, q.2) :=
      ((hvsm.differentiableOn (by simp)).differentiableAt (hPo.mem_nhds hpU)).hasFDerivAt
    have hcomp : HasFDerivAt (fun r : ℝ × ℝ => v (X r, r.2))
        ((fderiv ℝ v (X q, q.2)).comp ((fderiv ℝ X q).prod (ContinuousLinearMap.snd ℝ ℝ ℝ))) q :=
      hvd.comp q hGd
    have hev : ∀ᶠ r in nhds q, v (X r, r.2) = r.1 :=
      Filter.eventually_of_mem (hQo.mem_nhds hq) fun r hr => hXv r hr
    have hfst : HasFDerivAt (fun r : ℝ × ℝ => v (X r, r.2)) (ContinuousLinearMap.fst ℝ ℝ ℝ) q :=
      hasFDerivAt_fst.congr_of_eventuallyEq hev
    have huniq := hcomp.unique hfst
    have e1 := DFunLike.congr_fun huniq (1, 0)
    have e2 := DFunLike.congr_fun huniq (0, 1)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst'] at e1 e2
    rw [lin_FIN06835 (fderiv ℝ v (X q, q.2)) (fderiv ℝ X q (1, 0)) 0] at e1
    rw [lin_FIN06835 (fderiv ℝ v (X q, q.2)) (fderiv ℝ X q (0, 1)) 1] at e2
    exact ⟨by linear_combination e1, by linear_combination e2⟩
  have hbnd : ∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
      Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v (X q, q.2) (1, 0) ∧
      fderiv ℝ v (X q, q.2) (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
      |fderiv ℝ v (X q, q.2) (0, 1)| ≤ 1 := fun q hq => hWb _ (hXW q hq)
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨h1', h2'⟩ := hkey q hq
    have hpos : 0 < fderiv ℝ v (X q, q.2) (1, 0) :=
      lt_of_lt_of_le (half_pos hA) (hbnd q hq).1
    exact ⟨(eq_div_iff hpos.ne').2 h1', (eq_div_iff hpos.ne').2 h2'⟩
  · have hpos : 0 < fderiv ℝ v (X q, q.2) (1, 0) :=
      lt_of_lt_of_le (half_pos hA) (hbnd q hq).1
    have hαeq : fderiv ℝ X q (1, 0) = 1 / fderiv ℝ v (X q, q.2) (1, 0) :=
      (eq_div_iff hpos.ne').2 (hkey q hq).1
    rw [hαeq]
    refine ⟨one_div_le_one_div_of_le hpos (hbnd q hq).2.1, ?_⟩
    calc 1 / fderiv ℝ v (X q, q.2) (1, 0) ≤ 1 / (Real.sqrt quarticA_FIN06803 / 2) :=
          one_div_le_one_div_of_le (half_pos hA) (hbnd q hq).1
      _ = 2 / Real.sqrt quarticA_FIN06803 := one_div_div _ _

end DGPS.Frontier.FIN068
