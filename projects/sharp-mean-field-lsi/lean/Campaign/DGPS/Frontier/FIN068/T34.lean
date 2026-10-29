import DGPS.Frontier.FIN068.T33

/-!
Task id and title: FIN068.34, Smooth inverse and fixed image rectangle (module
`DGPS.Frontier.FIN068.T34`).

Provides:
* `DGPS.Frontier.FIN068.fin068_34_smooth_inverse_fixed_image_rectangle`: the full conclusion of
  FIN068.33 (the curve `a`, the patch `P = (-4-δx, -4+δx) × (-δy, δy)`, the factor `a₂`, the signed
  coordinate `v` with its smoothness, energy identity and base-point values, and the open
  neighborhood `U ⊆ P` of `(-4, 0)` carrying the bounds `sqrt A / 2 ≤ v_x ≤ 2 sqrt A`,
  `|v_y| ≤ 1`, exactly as stated there), together with the smooth inverse of
  `T (x, y) = (v (x, y), y)`: an open set `N` with `(-4, 0) ∈ N ⊆ U` on which `T` is injective and
  has open image, numbers `ε, δ > 0` such that the closure of the rectangle
  `Q = (-ε, ε) × (-δ, δ)` lies in `T '' N`, a function `X : ℝ × ℝ → ℝ` that is `C^∞` on `Q`, and the
  restricted source patch `W = N ∩ T ⁻¹' Q`, which is open, contains `(-4, 0)`, lies in `N`, keeps
  the FIN068.33 bounds on `v_x`, `v_y`, is mapped bijectively onto `Q` by `T`, and satisfies:
  `T` is `C^∞` on `W`, `q ↦ (X q, q.2)` is `C^∞` on `Q` with values in `W`, `v (X q, q.2) = q.1` on
  `Q` and `X (v p, p.2) = p.1` on `W`.
* `DGPS.Frontier.FIN068.deriv_equiv_FIN06834`, `DGPS.Frontier.FIN068.core_FIN06834` (helpers, not
  part of the interface): `deriv_equiv_FIN06834` says that if `v_x ≠ 0` at `p` then the derivative
  of `T` at `p` is a continuous linear equivalence of `ℝ × ℝ`; `core_FIN06834` is the generic
  inverse-function and rectangle argument for a coordinate `v` that is `C^∞` on an open set `U`
  with `v_x ≠ 0` on `U`.

Proof: `DT (p) = (v_x p, v_y p; 0, 1)` has the explicit inverse `((1/v_x), -(v_y/v_x); 0, 1)` when
`v_x p ≠ 0`; on `U`, `v_x ≥ sqrt A / 2 > 0` by FIN068.33. The smooth inverse-function theorem
(`ContDiffAt.toOpenPartialHomeomorph` at the base point) gives an open partial homeomorphism `e`
with `T = e` and `(-4, 0) ∈ e.source`. Put `N = e.source ∩ U`. Then `T '' N = e.target ∩ e.symm ⁻¹' U`
is open and contains `T (-4, 0) = (0, 0)` (FIN068.32: `v (-4, 0) = 0`). A sup-metric ball around
`(0, 0)` inside `T '' N` contains the closure of a centered rectangle `Q`. The inverse `e.symm` is
`C^∞` at every point of `T '' N` because `DT` is invertible at the corresponding source point in
`U` (`OpenPartialHomeomorph.contDiffAt_symm`). Since `T (p) = (v p, p.2)`, `e.symm q = (X q, q.2)`
with `X q = (e.symm q).1`. Restricting the source to `W = N ∩ T ⁻¹' Q` gives the bijection with `Q`.

R5 notes:
* No hypothesis is added. The statement is closed (existential over the FIN068.33 data). The
  FIN068.33 conclusion is restated inline with the same binder names, so that the consuming tasks
  see the patch, `v`, the bounds and the inverse in a single statement; it is not assumed.
* "Smooth" is `ContDiffOn ℝ ∞` (the campaign reading of `C^∞`), as in FIN068.32/33.
* `T (x, y) = (v (x, y), y)` is written `fun p : ℝ × ℝ => (v p, p.2)`. The centre of `Q` is `(0, 0)`
  because `T (-4, 0) = (v (-4, 0), 0) = (0, 0)`.
* "Smooth local inverse near `(0,0)`" and "its image neighborhood" are realised as the open set `N`
  (a neighborhood of `(-4, 0)` inside the FIN068.33 neighborhood `U`, on which `T` is injective) and
  its open image `T '' N`, which contains `(0, 0)`. The inverse itself is exposed through its first
  component `X` (the inverse is `q ↦ (X q, q.2)`, matching the form `(v, y) ↦ (X (v, y), y)` of
  FIN068.35); `X` is only constrained on `Q`, where `Q ⊆ closure Q ⊆ T '' N`.
* "The closure of `Q` is contained in its image neighborhood" is `closure Q ⊆ T '' N` in the
  product topology of `ℝ × ℝ`.
* "Restrict the source patch to the inverse image of `Q`" is `W = N ∩ T ⁻¹' Q`. The restricted
  patch is required to lie in `N ⊆ U ⊆ P`; it is not claimed to be a rectangle.
* "Smooth diffeomorphism onto the fixed rectangle" is read as: `T` is `C^∞` on `W` and maps `W`
  bijectively onto `Q` (`Set.BijOn`), the inverse `q ↦ (X q, q.2)` is `C^∞` on `Q` and maps `Q` into
  `W`, and the two compositions are the identity (`v (X q, q.2) = q.1` with the second coordinate
  unchanged, and `X (v p, p.2) = p.1`).
* "Retains every bound from 33" is read as: `W ⊆ U` and the bounds `sqrt A / 2 ≤ v_x ≤ 2 sqrt A`,
  `|v_y| ≤ 1` (non-strict, as in FIN068.33) hold at every point of `W`; the other FIN068.32 data
  (such as `A/2 ≤ a₂ ≤ 2A`) hold on the larger patch `P ⊇ U ⊇ W` and are restated unchanged.
* `v_x`, `v_y` are `fderiv ℝ v p (1, 0)` and `fderiv ℝ v p (0, 1)`, and `A` is
  `quarticA_FIN06803`, exactly as in FIN068.33; invertibility of `DT` on `U` uses
  `0 < A` (FIN068.03).
* The proof uses the smooth inverse-function theorem (`ContDiffAt.toOpenPartialHomeomorph`), not the
  parameter implicit-function alternative sketched in the specification; both are named there as
  acceptable routes.
* Dependency: smoothness of `v` inherits the FIN068.27 / FIN068.37 / FIN068.38 identifications
  through FIN068.32; this file adds nothing to them.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- If the partial derivative `v_x` is nonzero at `p`, the derivative of `T = (v, y)` at `p` is a
continuous linear equivalence of `ℝ × ℝ`. -/
lemma deriv_equiv_FIN06834 {v : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hv : DifferentiableAt ℝ v p)
    (hx : fderiv ℝ v p (1, 0) ≠ 0) :
    ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt (fun q : ℝ × ℝ => (v q, q.2)) (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) p := by
  set c := fderiv ℝ v p (1, 0) with hc
  set d := fderiv ℝ v p (0, 1) with hd
  have hlin : ∀ q : ℝ × ℝ, fderiv ℝ v p q = c * q.1 + d * q.2 := by
    intro q
    have e1 : fderiv ℝ v p (q.1, 0) = c * q.1 := by
      have : ((q.1, (0 : ℝ)) : ℝ × ℝ) = q.1 • ((1 : ℝ), (0 : ℝ)) := by simp
      rw [this, map_smul, smul_eq_mul, mul_comm]
    have e2 : fderiv ℝ v p (0, q.2) = d * q.2 := by
      have : (((0 : ℝ), q.2) : ℝ × ℝ) = q.2 • ((0 : ℝ), (1 : ℝ)) := by simp
      rw [this, map_smul, smul_eq_mul, mul_comm]
    rw [← e1, ← e2, ← map_add]
    congr 1
    ext <;> simp
  let f₁ : ℝ × ℝ →L[ℝ] ℝ × ℝ := (fderiv ℝ v p).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  let f₂ : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (c⁻¹ • ContinuousLinearMap.fst ℝ ℝ ℝ - (d / c) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have h₁ : Function.LeftInverse f₂ f₁ := by
    intro q
    ext
    · simp [f₁, f₂, hlin]
      field_simp
      ring
    · simp [f₁, f₂]
  have h₂ : Function.RightInverse f₂ f₁ := by
    intro q
    ext
    · simp [f₁, f₂, hlin]
      field_simp
      ring
    · simp [f₁, f₂]
  refine ⟨ContinuousLinearEquiv.equivOfInverse f₁ f₂ h₁ h₂, ?_⟩
  exact hv.hasFDerivAt.prodMk hasFDerivAt_snd

/-- The generic inverse-function and fixed-rectangle argument: if `v` is `C^∞` on an open set `U`
with `v_x ≠ 0` on `U`, `p₀ ∈ U`, `v p₀ = 0` and `p₀.2 = 0`, then `T = (v, y)` has a smooth local
inverse on a neighborhood `N ⊆ U` of `p₀`, and for a centered rectangle `Q` with closure in `T '' N`
the restricted source `W = N ∩ T ⁻¹' Q` is mapped diffeomorphically onto `Q`. Any property `Bd`
valid on `U` is retained on `W`. -/
lemma core_FIN06834 {v : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {p₀ : ℝ × ℝ}
    (hv : ContDiffOn ℝ ∞ v U) (hUo : IsOpen U) (hp₀ : p₀ ∈ U) (hv0 : v p₀ = 0) (hy0 : p₀.2 = 0)
    (hne : ∀ p ∈ U, fderiv ℝ v p (1, 0) ≠ 0) (Bd : ℝ × ℝ → Prop) (hBd : ∀ p ∈ U, Bd p) :
    ∃ N : Set (ℝ × ℝ), IsOpen N ∧ p₀ ∈ N ∧ N ⊆ U ∧
      Set.InjOn (fun p : ℝ × ℝ => (v p, p.2)) N ∧
      IsOpen ((fun p : ℝ × ℝ => (v p, p.2)) '' N) ∧
      ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
        closure (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ⊆ (fun p : ℝ × ℝ => (v p, p.2)) '' N ∧
        ∃ X : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ X (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
          ∃ W : Set (ℝ × ℝ),
            W = N ∩ (fun p : ℝ × ℝ => (v p, p.2)) ⁻¹' (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
            IsOpen W ∧ p₀ ∈ W ∧ W ⊆ N ∧ (∀ p ∈ W, Bd p) ∧
            Set.BijOn (fun p : ℝ × ℝ => (v p, p.2)) W (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
            ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (v p, p.2)) W ∧
            ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2)) (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
            (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, (X q, q.2) ∈ W) ∧
            (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, v (X q, q.2) = q.1) ∧
            (∀ p ∈ W, X (v p, p.2) = p.1) := by
  set T : ℝ × ℝ → ℝ × ℝ := fun p => (v p, p.2) with hT
  have hTsm : ContDiffOn ℝ ∞ T U := hv.prodMk contDiffOn_snd
  have hTat : ∀ p ∈ U, ContDiffAt ℝ ∞ T p := fun p hp => hTsm.contDiffAt (hUo.mem_nhds hp)
  have hderiv : ∀ p ∈ U, ∃ L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      HasFDerivAt T (L : ℝ × ℝ →L[ℝ] ℝ × ℝ) p := fun p hp =>
    deriv_equiv_FIN06834 ((hv.differentiableOn (by simp)).differentiableAt (hUo.mem_nhds hp))
      (hne p hp)
  obtain ⟨L₀, hL₀⟩ := hderiv p₀ hp₀
  set e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    (hTat p₀ hp₀).toOpenPartialHomeomorph T hL₀ (by simp) with he
  have hecoe : (e : ℝ × ℝ → ℝ × ℝ) = T := rfl
  have hp₀e : p₀ ∈ e.source := (hTat p₀ hp₀).mem_toOpenPartialHomeomorph_source hL₀ (by simp)
  set N : Set (ℝ × ℝ) := e.source ∩ U with hN
  have hNo : IsOpen N := e.open_source.inter hUo
  have hp₀N : p₀ ∈ N := ⟨hp₀e, hp₀⟩
  have hNU : N ⊆ U := Set.inter_subset_right
  have hinj : Set.InjOn T N := e.injOn.mono Set.inter_subset_left
  -- the image of `N`
  have himg : T '' N = e.target ∩ e.symm ⁻¹' U := by
    ext q
    constructor
    · rintro ⟨p, ⟨hps, hpU⟩, rfl⟩
      refine ⟨e.map_source hps, ?_⟩
      show e.symm (e p) ∈ U
      rw [e.left_inv hps]
      exact hpU
    · rintro ⟨hqt, hqU⟩
      exact ⟨e.symm q, ⟨e.map_target hqt, hqU⟩, e.right_inv hqt⟩
  have himgo : IsOpen (T '' N) := by
    rw [himg]
    exact e.continuousOn_symm.isOpen_inter_preimage e.open_target hUo
  have hT0 : T p₀ = (0, 0) := by simp [hT, hv0, hy0]
  have hT0mem : ((0 : ℝ), (0 : ℝ)) ∈ T '' N := ⟨p₀, hp₀N, hT0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 himgo (0, 0) hT0mem
  have hrpos : 0 < r / 2 := half_pos hr
  have hcl : closure (Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2)) ⊆ T '' N := by
    rw [closure_prod_eq, closure_Ioo (by linarith)]
    intro q hq
    apply hball
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hq
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [sub_zero]
    refine max_lt ?_ ?_
    · rw [abs_lt]; constructor <;> linarith
    · rw [abs_lt]; constructor <;> linarith
  -- smoothness of the inverse on the image of `N`
  have hsymm : ∀ q ∈ T '' N, ContDiffAt ℝ ∞ e.symm q := by
    intro q hq
    rw [himg] at hq
    obtain ⟨L, hL⟩ := hderiv (e.symm q) hq.2
    exact e.contDiffAt_symm hq.1 hL (hTat _ hq.2)
  have hright : ∀ q ∈ T '' N, T (e.symm q) = q := by
    intro q hq
    rw [himg] at hq
    exact e.right_inv hq.1
  have hsrc : ∀ q ∈ T '' N, e.symm q ∈ N := by
    intro q hq
    rw [himg] at hq
    exact ⟨e.map_target hq.1, hq.2⟩
  have hXeq : ∀ q ∈ T '' N, ((e.symm q).1, q.2) = e.symm q := by
    intro q hq
    have h2 := congrArg Prod.snd (hright q hq)
    ext
    · rfl
    · exact h2.symm
  have hQsub : ∀ q ∈ Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2), q ∈ T '' N :=
    fun q hq => hcl (subset_closure hq)
  have hXs : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (e.symm q).1)
      (Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2)) :=
    fun q hq => (hsymm q (hQsub q hq)).fst.contDiffWithinAt
  have hTQ : ∀ q ∈ Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2),
      e.symm q ∈ N ∩ T ⁻¹' (Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2)) :=
    fun q hq => ⟨hsrc q (hQsub q hq), by
      rw [Set.mem_preimage, hright q (hQsub q hq)]
      exact hq⟩
  refine ⟨N, hNo, hp₀N, hNU, hinj, himgo, r / 2, r / 2, hrpos, hrpos, hcl,
    fun q => (e.symm q).1, hXs,
    N ∩ T ⁻¹' (Set.Ioo (-(r / 2)) (r / 2) ×ˢ Set.Ioo (-(r / 2)) (r / 2)),
    rfl, ?_, ?_, Set.inter_subset_left, fun p hp => hBd p (hNU hp.1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hTsm.continuousOn.mono hNU).isOpen_inter_preimage hNo (isOpen_Ioo.prod isOpen_Ioo)
  · refine ⟨hp₀N, ?_⟩
    rw [Set.mem_preimage, hT0]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · refine ⟨fun p hp => hp.2, hinj.mono Set.inter_subset_left, fun q hq => ?_⟩
    exact ⟨e.symm q, hTQ q hq, hright q (hQsub q hq)⟩
  · exact hTsm.mono (Set.inter_subset_left.trans hNU)
  · exact hXs.prodMk contDiffOn_snd
  · intro q hq
    rw [hXeq q (hQsub q hq)]
    exact hTQ q hq
  · intro q hq
    rw [hXeq q (hQsub q hq)]
    exact congrArg Prod.fst (hright q (hQsub q hq))
  · intro p hp
    exact congrArg Prod.fst (e.left_inv hp.1.1)

/-- Smooth inverse and fixed image rectangle (FIN068.34): the FIN068.33 data, together with a smooth
local inverse of `T (x, y) = (v (x, y), y)` on a neighborhood `N ⊆ U` of `(-4, 0)`, a centered
rectangle `Q = (-ε, ε) × (-δ, δ)` whose closure lies in `T '' N`, and the restricted source patch
`W = N ∩ T ⁻¹' Q`, which `T` maps diffeomorphically onto `Q` and on which the FIN068.33 bounds
hold. -/
theorem fin068_34_smooth_inverse_fixed_image_rectangle :
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
                      (∀ p ∈ W, X (v p, p.2) = p.1) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb⟩ :=
    fin068_33_quantitative_derivative_patch
  obtain ⟨-, -, hApos, -⟩ := fin068_03_constants_exact_cancellation
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb, ?_⟩
  have hA : 0 < Real.sqrt quarticA_FIN06803 := Real.sqrt_pos.2 hApos
  have hne : ∀ p ∈ U, fderiv ℝ v p (1, 0) ≠ 0 := fun p hp =>
    (lt_of_lt_of_le (half_pos hA) (hUb p hp).1).ne'
  exact core_FIN06834 (hvsm.mono hUP) hUo hU0 hv0 rfl hne
    (fun p : ℝ × ℝ => Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
      fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧ |fderiv ℝ v p (0, 1)| ≤ 1) hUb

end DGPS.Frontier.FIN068
