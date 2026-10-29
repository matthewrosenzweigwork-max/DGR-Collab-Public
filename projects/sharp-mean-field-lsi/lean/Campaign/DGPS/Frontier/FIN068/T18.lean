import DGPS.Frontier.FIN068.T02
import DGPS.Frontier.FIN068.T04
import DGPS.Frontier.FIN068.T17

/-!
Task id and title: FIN068.18, Assemble the jet of J (module `DGPS.Frontier.FIN068.T18`).

Provides:
* `DGPS.Frontier.FIN068.fin068_18_assemble_jet_j`: with `J = liftPotential_FIN06804`,
  `κ = quarticKappa`, `η = quarticEta`, `b = quarticB = besselRatio 4` and `v₀ = deriv besselRatio 4`,
  at `(u, z) = (0, 0)`: the scalar partials `J_u = -5/κ + b`, `J_z = 1/(2κη) - b/8`,
  `J_uu = 1/κ - v₀`, `J_uz = J_zu = v₀/8 - b/32`, `J_zz = b/256 - v₀/64`, and the same five values
  as Fréchet entries `fderiv J 0 eᵢ` and `fderiv (fderiv J) 0 eᵢ eⱼ` of `J` read on
  `EuclideanSpace ℝ (Fin 2)` (both mixed entries `(0,1)` and `(1,0)` are stated).
* `DGPS.Frontier.FIN068.jetPotential_FIN06818`: `J` read on `EuclideanSpace ℝ (Fin 2)`,
  `w ↦ liftPotential_FIN06804 (w 0) (w 1)` (a helper definition, not a claim).
* Helper declarations, all with suffix `_FIN06818` and not part of the interface: `ellLog_FIN06818`,
  `quadPart_FIN06818`, first and second Fréchet derivative formulas for `jetPotential_FIN06818`, and
  the generic line and slice identities that turn scalar slice derivatives into Fréchet entries.

Proof: `J = Q - ℓ ∘ R` where `Q` is the polynomial part, `ℓ = log I₀` (FIN068.02) and `R` is the
radical of FIN068.17. On the positive-radicand patch `fderiv J q v = Q'(q) v - g(R q) * fderiv R q v`
with `g = besselRatio = ℓ'` (FIN068.02). Differentiating `t ↦ fderiv J (t • w) v` at `0` by the
product and chain rules, with `g'(4) = deriv besselRatio 4 = ℓ''(4)` (FIN068.02) and the radical jet
`R = 4`, `dR = (-1, 1/8)`, `d²R = [[0, 1/32], [1/32, -1/256]]` (FIN068.17), gives
`d²J(w, v) = w₀ v₀ / κ - (v₀ dR(w) dR(v) + b d²R(w, v))`. The five formulas are then exact ring
arithmetic on these values. The scalar partials are the Fréchet entries by generic lemmas: the
derivative of a coordinate slice at `0` is `fderiv f 0 a`, and the iterated slice derivative is
`fderiv (fderiv f) 0 b a`; here `f = J` is `C²` at `0` (smooth by `ContDiff` composition).

R5 notes:
* No hypothesis is added. The statement is closed and unconditional.
* `b`, `κ`, `η` appear as the campaign constants `quarticB`, `quarticKappa`, `quarticEta`, and
  `v₀` as `deriv besselRatio 4` (which equals `iteratedDeriv 2 ℓ 4` by FIN068.02); the five values
  are stated exactly as in the specification, in terms of `κ`, `η`, `b`, `v₀`. The relations
  `1/κ = b/5` and `η = 4/5` are not used here, so FIN068.03 is not imported; they are needed only
  by the consumer FIN068.05 to rewrite these values as `0`, `0`, `A`, `-d/32`, `d/256`.
* Scalar partials are read as one-variable derivatives of coordinate slices of the two-real-variable
  function `liftPotential_FIN06804 u z`: `J_u = deriv (fun t => J t 0) 0`,
  `J_z = deriv (fun t => J 0 t) 0`, `J_uu = deriv (fun t => deriv (fun s => J s 0) t) 0`,
  `J_uz = deriv (fun t => deriv (fun s => J s t) 0) 0` (differentiate in `u` first),
  `J_zu = deriv (fun t => deriv (fun s => J t s) 0) 0` (differentiate in `z` first), and
  `J_zz = deriv (fun t => deriv (fun s => J 0 s) t) 0`. Both mixed orders are proved separately
  and both are also stated; their equality is a corollary (no appeal to Schwarz symmetry).
* Fréchet reading (non-literal addition for consumers): `J` is also read on
  `EuclideanSpace ℝ (Fin 2)` with `u = w 0`, `z = w 1`, the convention of FIN068.17, and the
  entries are tested on `EuclideanSpace.single i 1`; the second derivative is the bilinear
  `fderiv ℝ (fderiv ℝ J) 0 v w` (first argument is the outer direction). The reading on `ℝ × ℝ`
  used by FIN068.04's smoothness statement is not restated; the two are related by the coordinate
  linear map.
* The Fréchet and scalar forms are both part of the statement; the specification's "chain rule" is
  proved as the line identity above rather than by a symbolic multivariable chain rule.
* `ℓ` is `Real.log (besselI 0 ·)` with `I₀ = besselI 0` the campaign object, as in FIN068.02 and
  FIN068.04; no definition body of FIN068.37 or FIN068.38 is assumed beyond those tasks' lemmas.
-/

open Filter Topology DGPS.Models DGPS.Circle.BesselMoments
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The logarithm `ℓ(s) = log I₀(s)` of FIN068.02. -/
noncomputable def ellLog_FIN06818 (s : ℝ) : ℝ := Real.log (besselI 0 s)

/-- The lifted potential `J` read as a function on `EuclideanSpace ℝ (Fin 2)` through the
coordinates `u = w 0`, `z = w 1`. -/
noncomputable def jetPotential_FIN06818 (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  liftPotential_FIN06804 (w 0) (w 1)

/-- The polynomial part of `J` in the coordinates of `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def quadPart_FIN06818 (w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (-5 + w 0) ^ 2 / (2 * quarticKappa) + w 1 / (2 * quarticKappa * quarticEta)

lemma jetPotential_eq_FIN06818 (w : EuclideanSpace ℝ (Fin 2)) :
    jetPotential_FIN06818 w = quadPart_FIN06818 w - ellLog_FIN06818 (radicalR_FIN06817 w) := rfl

lemma contDiff_ellLog_FIN06818 : ContDiff ℝ ∞ ellLog_FIN06818 :=
  (fin068_02_logarithmic_derivative).1

lemma hasDerivAt_ellLog_FIN06818 (s : ℝ) : HasDerivAt ellLog_FIN06818 (besselRatio s) s := by
  have h := hasDerivAt_log_besselI_zero_FIN06802 s
  exact h

lemma hasDerivAt_besselRatio_four_FIN06818 :
    HasDerivAt besselRatio (deriv besselRatio 4) 4 :=
  (hasDerivAt_besselRatio 4).differentiableAt.hasDerivAt

lemma contDiff_quadPart_FIN06818 : ContDiff ℝ 2 quadPart_FIN06818 := by
  unfold quadPart_FIN06818
  fun_prop

lemma contDiffAt_ellRadical_FIN06818 :
    ContDiffAt ℝ 2 (fun w : EuclideanSpace ℝ (Fin 2) => ellLog_FIN06818 (radicalR_FIN06817 w)) 0 :=
  ((contDiff_ellLog_FIN06818.of_le (by simp)).contDiffAt).comp (0 : EuclideanSpace ℝ (Fin 2))
    contDiffAt_radicalR_FIN06817

lemma contDiffAt_jet_FIN06818 : ContDiffAt ℝ 2 jetPotential_FIN06818 0 := by
  have h : jetPotential_FIN06818 = fun w => quadPart_FIN06818 w -
      ellLog_FIN06818 (radicalR_FIN06817 w) := funext jetPotential_eq_FIN06818
  rw [h]
  exact contDiff_quadPart_FIN06818.contDiffAt.sub contDiffAt_ellRadical_FIN06818

/-- Generic line identity: the second Fréchet derivative along `w`, tested on `v`, is the derivative
of `t ↦ fderiv f (t • w) v`. -/
lemma hasDerivAt_fderiv_line_FIN06818 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (w v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => fderiv ℝ f (t • w) v) (fderiv ℝ (fderiv ℝ f) 0 w v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hF := hdiff.hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => fderiv ℝ f (t • w))
      (fderiv ℝ (fderiv ℝ f) 0 w) 0 := by
    have hF' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) 0)
        ((fun t : ℝ => t • w) 0) := by
      simpa using hF
    exact hF'.comp_hasDerivAt (x := (0 : ℝ)) hline
  simpa using hc.clm_apply (hasDerivAt_const (0 : ℝ) v)

lemma hasFDerivAt_quadPart_FIN06818 (q : EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt quadPart_FIN06818
      (((-5 + q 0) / quarticKappa) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        (1 / (2 * quarticKappa * quarticEta)) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) q := by
  have h0 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => w 0)
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : EuclideanSpace ℝ (Fin 2) => w 1)
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) q :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have h2 := (((h0.const_add (-5 : ℝ)).pow 2).mul_const (2 * quarticKappa)⁻¹).add
    (h1.mul_const (2 * quarticKappa * quarticEta)⁻¹)
  have hfun : quadPart_FIN06818 = fun w : EuclideanSpace ℝ (Fin 2) =>
      (-5 + w 0) ^ 2 * (2 * quarticKappa)⁻¹ + w 1 * (2 * quarticKappa * quarticEta)⁻¹ := by
    funext w
    simp [quadPart_FIN06818, div_eq_mul_inv]
  rw [hfun]
  refine h2.congr_fderiv ?_
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  simp
  ring

lemma hasFDerivAt_jet_FIN06818 (q : EuclideanSpace ℝ (Fin 2))
    (hq : 0 < (-4 + q 0) ^ 2 + q 1) :
    HasFDerivAt jetPotential_FIN06818
      ((((-5 + q 0) / quarticKappa) • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        (1 / (2 * quarticKappa * quarticEta)) • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) -
        besselRatio (radicalR_FIN06817 q) • fderiv ℝ radicalR_FIN06817 q) q := by
  have hR : HasFDerivAt radicalR_FIN06817 (fderiv ℝ radicalR_FIN06817 q) q :=
    (hasFDerivAt_radicalR_FIN06817 q hq).differentiableAt.hasFDerivAt
  have hG := (hasDerivAt_ellLog_FIN06818 (radicalR_FIN06817 q)).comp_hasFDerivAt q hR
  have h := (hasFDerivAt_quadPart_FIN06818 q).sub hG
  have hfun : jetPotential_FIN06818 = fun w => quadPart_FIN06818 w -
      (ellLog_FIN06818 ∘ radicalR_FIN06817) w := funext jetPotential_eq_FIN06818
  rw [hfun]
  exact h

lemma fderiv_jet_apply_FIN06818 (q v : EuclideanSpace ℝ (Fin 2))
    (hq : 0 < (-4 + q 0) ^ 2 + q 1) :
    fderiv ℝ jetPotential_FIN06818 q v =
      (-5 + q 0) / quarticKappa * v 0 + v 1 / (2 * quarticKappa * quarticEta) -
        besselRatio (radicalR_FIN06817 q) * fderiv ℝ radicalR_FIN06817 q v := by
  rw [(hasFDerivAt_jet_FIN06818 q hq).fderiv]
  simp
  ring

lemma radicand_pos_zero_FIN06818 : 0 < (-4 + (0 : EuclideanSpace ℝ (Fin 2)) 0) ^ 2 +
    (0 : EuclideanSpace ℝ (Fin 2)) 1 := by norm_num

lemma eventually_radicand_pos_line_FIN06818 (w : EuclideanSpace ℝ (Fin 2)) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 < (-4 + (t • w) 0) ^ 2 + (t • w) 1 := by
  have hc : Continuous fun t : ℝ => (-4 + (t • w) 0) ^ 2 + (t • w) 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    fun_prop
  have h0 : (0 : ℝ) < (fun t : ℝ => (-4 + (t • w) 0) ^ 2 + (t • w) 1) 0 := by norm_num
  exact hc.continuousAt.eventually (lt_mem_nhds h0)

lemma hasDerivAt_radical_line_FIN06818 (w : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => radicalR_FIN06817 (t • w)) (fderiv ℝ radicalR_FIN06817 0 w) 0 := by
  have hR : HasFDerivAt radicalR_FIN06817 (fderiv ℝ radicalR_FIN06817 0)
      ((fun t : ℝ => t • w) 0) := by
    rw [show ((fun t : ℝ => t • w) 0) = (0 : EuclideanSpace ℝ (Fin 2)) by simp]
    exact (contDiffAt_radicalR_FIN06817.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
  exact hR.comp_hasDerivAt (x := (0 : ℝ)) hline

/-- Second Fréchet entries of `J`, assembled from the jet of the radical (FIN068.17), `ℓ' = g` and
`ℓ'' = g'` (FIN068.02). -/
lemma fderiv_fderiv_jet_apply_FIN06818 (w v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 w v =
      w 0 * v 0 / quarticKappa -
        (deriv besselRatio 4 * fderiv ℝ radicalR_FIN06817 0 w * fderiv ℝ radicalR_FIN06817 0 v +
          besselRatio 4 * fderiv ℝ (fderiv ℝ radicalR_FIN06817) 0 w v) := by
  have hev : (fun t : ℝ => fderiv ℝ jetPotential_FIN06818 (t • w) v) =ᶠ[𝓝 0]
      fun t : ℝ => (-5 + t * w 0) / quarticKappa * v 0 + v 1 / (2 * quarticKappa * quarticEta) -
        besselRatio (radicalR_FIN06817 (t • w)) * fderiv ℝ radicalR_FIN06817 (t • w) v := by
    filter_upwards [eventually_radicand_pos_line_FIN06818 w] with t ht
    rw [fderiv_jet_apply_FIN06818 _ _ ht]
    simp
  have h1 : HasDerivAt (fun t : ℝ => (-5 + t * w 0) / quarticKappa * v 0 +
      v 1 / (2 * quarticKappa * quarticEta)) (w 0 / quarticKappa * v 0) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).mul_const (w 0)).const_add (-5 : ℝ)).div_const
      quarticKappa).mul_const (v 0) |>.add_const (v 1 / (2 * quarticKappa * quarticEta))
    convert h using 1
    simp
    ring
  have hRl := hasDerivAt_radical_line_FIN06818 w
  have hg : HasDerivAt (fun t : ℝ => besselRatio (radicalR_FIN06817 (t • w)))
      (deriv besselRatio 4 * fderiv ℝ radicalR_FIN06817 0 w) 0 := by
    refine HasDerivAt.comp_of_eq (h₂ := besselRatio) (y := 4) 0 ?_ hRl ?_
    · exact hasDerivAt_besselRatio_four_FIN06818
    · simp [radicalR_zero_FIN06817]
  have h2 := hg.mul (hasDerivAt_fderiv_line_FIN06818 radicalR_FIN06817
    contDiffAt_radicalR_FIN06817 w v)
  have h3 := h1.sub h2
  have h4 := hasDerivAt_fderiv_line_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818 w v
  rw [hev.hasDerivAt_iff] at h4
  have h5 := h4.unique h3
  rw [h5]
  simp [radicalR_zero_FIN06817]
  ring

lemma fderiv_jet_zero_FIN06818 (v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ jetPotential_FIN06818 0 v =
      -5 / quarticKappa * v 0 + v 1 / (2 * quarticKappa * quarticEta) -
        quarticB * ((1 / 8) * (-8 * v 0 + v 1)) := by
  rw [fderiv_jet_apply_FIN06818 0 v radicand_pos_zero_FIN06818, radicalR_zero_FIN06817,
    fderiv_radicalR_zero_FIN06817]
  simp [quarticB]

lemma differentiableAt_of_contDiffAt_FIN06818 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) : DifferentiableAt ℝ f 0 :=
  hf.differentiableAt (by norm_num)

lemma deriv_line_generic_FIN06818 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (a : EuclideanSpace ℝ (Fin 2)) :
    deriv (fun t : ℝ => f (t • a)) 0 = fderiv ℝ f 0 a := by
  have hR : HasFDerivAt f (fderiv ℝ f 0) ((fun t : ℝ => t • a) 0) := by
    rw [show ((fun t : ℝ => t • a) 0) = (0 : EuclideanSpace ℝ (Fin 2)) by simp]
    exact (differentiableAt_of_contDiffAt_FIN06818 f hf).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => t • a) a 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const a
  exact (hR.comp_hasDerivAt (x := (0 : ℝ)) hline).deriv

lemma tendsto_smul_zero_FIN06818 (a : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun t : ℝ => t • a) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun t : ℝ => t • a := by fun_prop
  simpa using hc.tendsto 0

/-- Mixed iterated slice derivative: first along `a` through `t • b`, then along `b`. -/
lemma deriv_deriv_slice_FIN06818 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (a b : EuclideanSpace ℝ (Fin 2)) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (t • b + s • a)) 0) 0 =
      fderiv ℝ (fderiv ℝ f) 0 b a := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => f (t • b + s • a)) 0) =ᶠ[𝓝 0]
      fun t : ℝ => fderiv ℝ f (t • b) a := by
    filter_upwards [(tendsto_smul_zero_FIN06818 b).eventually (hf.eventually (by simp))] with
      t ht
    have hF : HasFDerivAt f (fderiv ℝ f (t • b)) (t • b) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => t • b + s • a) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (t • b)
    exact (hF.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hline (by simp)).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_fderiv_line_FIN06818 f hf b a).deriv

/-- Diagonal iterated slice derivative: `deriv` of `s ↦ f (s • a)` at the moving point `t`. -/
lemma deriv_deriv_diag_FIN06818 (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (a : EuclideanSpace ℝ (Fin 2)) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => f (s • a)) t) 0 =
      fderiv ℝ (fderiv ℝ f) 0 a a := by
  have hev : (fun t : ℝ => deriv (fun s : ℝ => f (s • a)) t) =ᶠ[𝓝 0]
      fun t : ℝ => fderiv ℝ f (t • a) a := by
    filter_upwards [(tendsto_smul_zero_FIN06818 a).eventually (hf.eventually (by simp))] with
      t ht
    have hF : HasFDerivAt f (fderiv ℝ f (t • a)) ((fun s : ℝ => s • a) t) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => s • a) a t := by
      simpa using (hasDerivAt_id t).smul_const a
    exact (hF.comp_hasDerivAt (x := t) hline).deriv
  rw [hev.deriv_eq]
  exact (hasDerivAt_fderiv_line_FIN06818 f hf a a).deriv

lemma jet_slice_FIN06818 (s t : ℝ) :
    jetPotential_FIN06818 (t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) +
      s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) = liftPotential_FIN06804 s t := by
  unfold jetPotential_FIN06818
  simp

lemma jet_slice'_FIN06818 (s t : ℝ) :
    jetPotential_FIN06818 (t • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) = liftPotential_FIN06804 t s := by
  unfold jetPotential_FIN06818
  simp

lemma jet_line_u_FIN06818 (s : ℝ) :
    jetPotential_FIN06818 (s • EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) =
      liftPotential_FIN06804 s 0 := by
  unfold jetPotential_FIN06818
  simp

lemma jet_line_z_FIN06818 (s : ℝ) :
    jetPotential_FIN06818 (s • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
      liftPotential_FIN06804 0 s := by
  unfold jetPotential_FIN06818
  simp

/-- Main declaration. At `(u, z) = (0, 0)`, with `κ = quarticKappa`, `η = quarticEta`,
`b = quarticB` and `v₀ = deriv besselRatio 4`: the scalar partials of `J`, and the Fréchet first and
second derivative entries of `J` read on `EuclideanSpace ℝ (Fin 2)`. -/
theorem fin068_18_assemble_jet_j :
    deriv (fun t : ℝ => liftPotential_FIN06804 t 0) 0 = -5 / quarticKappa + quarticB ∧
    deriv (fun t : ℝ => liftPotential_FIN06804 0 t) 0 =
      1 / (2 * quarticKappa * quarticEta) - quarticB / 8 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 s 0) t) 0 =
      1 / quarticKappa - deriv besselRatio 4 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 s t) 0) 0 =
      deriv besselRatio 4 / 8 - quarticB / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 t s) 0) 0 =
      deriv besselRatio 4 / 8 - quarticB / 32 ∧
    deriv (fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 0 s) t) 0 =
      quarticB / 256 - deriv besselRatio 4 / 64 ∧
    fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 0 1) = -5 / quarticKappa + quarticB ∧
    fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 1 1) =
      1 / (2 * quarticKappa * quarticEta) - quarticB / 8 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 0 1) = 1 / quarticKappa - deriv besselRatio 4 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) = deriv besselRatio 4 / 8 - quarticB / 32 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 0 1) = deriv besselRatio 4 / 8 - quarticB / 32 ∧
    fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) = quarticB / 256 - deriv besselRatio 4 / 64 := by
  obtain ⟨_, _, _, _, _, _, _, h8, h9, h10, h11, h12, h13⟩ := fin068_17_radical_first_second_jet
  have hF0 : fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 0 1) =
      -5 / quarticKappa + quarticB := by
    rw [fderiv_jet_zero_FIN06818]
    simp
  have hF1 : fderiv ℝ jetPotential_FIN06818 0 (EuclideanSpace.single 1 1) =
      1 / (2 * quarticKappa * quarticEta) - quarticB / 8 := by
    rw [fderiv_jet_zero_FIN06818]
    simp
    ring
  have hS00 : fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 0 1) = 1 / quarticKappa - deriv besselRatio 4 := by
    rw [fderiv_fderiv_jet_apply_FIN06818, h8, h10]
    simp
  have hS01 : fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) = deriv besselRatio 4 / 8 - quarticB / 32 := by
    rw [fderiv_fderiv_jet_apply_FIN06818, h8, h9, h11]
    simp [quarticB]
    ring
  have hS10 : fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 0 1) = deriv besselRatio 4 / 8 - quarticB / 32 := by
    rw [fderiv_fderiv_jet_apply_FIN06818, h8, h9, h12]
    simp [quarticB]
    ring
  have hS11 : fderiv ℝ (fderiv ℝ jetPotential_FIN06818) 0 (EuclideanSpace.single 1 1)
      (EuclideanSpace.single 1 1) = quarticB / 256 - deriv besselRatio 4 / 64 := by
    rw [fderiv_fderiv_jet_apply_FIN06818, h9, h13]
    simp [quarticB]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hF0, hF1, hS00, hS01, hS10, hS11⟩
  · have h := deriv_line_generic_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 0 1)
    simp only [jet_line_u_FIN06818] at h
    rw [h, hF0]
  · have h := deriv_line_generic_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 1 1)
    simp only [jet_line_z_FIN06818] at h
    rw [h, hF1]
  · have h := deriv_deriv_diag_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 0 1)
    simp only [jet_line_u_FIN06818] at h
    rw [h, hS00]
  · have h := deriv_deriv_slice_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
    simp only [jet_slice_FIN06818] at h
    rw [h, hS10]
  · have h := deriv_deriv_slice_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)
    simp only [jet_slice'_FIN06818] at h
    rw [h, hS01]
  · have h := deriv_deriv_diag_FIN06818 jetPotential_FIN06818 contDiffAt_jet_FIN06818
      (EuclideanSpace.single 1 1)
    simp only [jet_line_z_FIN06818] at h
    rw [h, hS11]

end DGPS.Frontier.FIN068
