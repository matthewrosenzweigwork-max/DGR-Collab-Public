import DGPS.Frontier.STR029.T56
import DGPS.Frontier.STR029.T57
import DGPS.Frontier.STR029.T59

/-!
# STR029.60: Apply division and retain parameter derivative limits

Task STR029.60 of frontier packet STR029, "Apply division and retain parameter derivative limits".
The division step divides the weighted reduced jet of STR029.57 by `h ^ 4` with the coordinate
division lemma of STR029.59, and shows that every fixed parameter derivative of the quotient
converges uniformly, as `h → 0`, on each compact set of parameters.

Provides:
* `DGPS.Frontier.STR029.str029_60_apply_division_retain_parameter_derivative_limits`: there are
  `U`, `V`, `ψ` with the STR029.57 properties; an open `Ω` on which
  `G (h, z) = F (h A, h B, h, h ^ 2 * s)` (with `z = (A, B, s)`) is `C^∞` and satisfies the
  STR029.59 jet hypotheses; and an open `O` on which the division extension
  `quotientRemainder_STR02959 G` is `C^∞`, equals `G / h ^ 4` for `h ≠ 0`, has the value
  `J4red A B - s (A ^ 2 + B ^ 2) / 2` at `h = 0`, and has every `n`-th `z`-derivative converging
  uniformly on each compact set of parameters as `h → 0`.
* `DGPS.Frontier.STR029.Gs_STR02960`: the scaled function `G (h, z) = F (h A, h B, h, h ^ 2 * s)`.
* `DGPS.Frontier.STR029.cval_STR02960`: the closed form `J4red A B - s (A ^ 2 + B ^ 2) / 2`.
* `DGPS.Frontier.STR029.JC2_joint_STR02960`: joint `C^∞` regularity of the chart functional
  in the variables `(h, γ, u)`.
* `DGPS.Frontier.STR029.slice_iteratedFDeriv_STR02960`: the `n`-th derivative of a `z`-slice
  is the joint `n`-th derivative restricted to the `z`-directions.
* `DGPS.Frontier.STR029.tendsto_unif_slice_STR02960`: uniform convergence of the `z`-slice
  derivatives as `h → 0` on compact sets, from continuity on an open set containing `{0} × ℝ³`.
* `DGPS.Frontier.STR029.poly_zero_STR02960`, `DGPS.Frontier.STR029.jet_zero_STR02960`: a
  polynomial vanishing lemma and the Taylor identification of the first four derivatives.

R5 notes:
* Carrier of `ψ`. The statement quantifies over `U`, `V`, `ψ` with exactly the properties
  exported by STR029.57 (open domain, `C^∞` on `U`, `ψ 0 = 0`, values in `V`, and the
  zero set of `Rpar_STR02916`). The graph of STR029.16 enters only through that family.
  The existential is over the whole family, not over a fixed STR029.16 graph.
* Parameters. The node variables `(A, B, s)` are the coordinates `z 0`, `z 1`, `z 2` of
  `z : Fin 3 → ℝ`. The map `G (h, z) = F (h A, h B, h, h ^ 2 s)` is `Gs_STR02960 ψ (h, z)`, with
  `F` the composition `Fred_STR02956 ψ` of the variational chart `Jchart_STR02950` and the
  variational range graph `ψ`. No Euler range map is used.
* Division domain. The STR029.59 parameter set is `U = Set.univ` (every `z`). The open domain
  `Ω = scale_STR02960 ⁻¹' U` is open and contains `(0, z)` for every `z`, because
  `scale_STR02960 (0, z) = 0` and `0 ∈ U`. Smoothness of `Gs_STR02960 ψ` on `Ω` is proved here
  (from joint smoothness of the chart functional and of `ψ` on `U`), not assumed.
* Jet hypotheses. The vanishing of the first three `h`-derivatives at `0` and the value
  `iteratedDeriv 4 = 24 c` are derived from the STR029.57 remainder bound, applied with the
  singleton compact set `{(z 0, z 1, z 2)}` for each `z`, by Taylor's theorem with little-o
  remainder (`jet_zero_STR02960`). The bound from STR029.57 is per compact set, so the
  singleton is used for each `z` separately.
* Value at zero. The `.20` value is the closed form
  `V (0, A, B, s) = J4red A B - s (A ^ 2 + B ^ 2) / 2`, stated in the main theorem as
  `Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)`. The value of the STR029.59
  quotient at `0` is `iteratedDeriv 4 / 4!`, which equals this closed form.
* Extension domain. The Lean function `quotientRemainder_STR02959 G` is defined for all `h`
  by an integral. Its `C^∞` regularity, its identity with `G / h ^ 4`, and the derivative
  claims are asserted only on the open set `O` (the union of the STR029.59 neighbourhoods).
  Off `O` the integral value carries no claim.
* "Each smaller compact set". The derivative limit is proved for every compact `K` in
  `Fin 3 → ℝ`, which contains every smaller compact parameter set. The limit is taken as
  `h → 0` along all real `h` in the filter `𝓝 0`. It is uniform in `z ∈ K`, and it is obtained
  from continuity on `O` by the tube lemma on the compact set `K`, not from a Lipschitz bound.
* "Every fixed derivative in (A, B, s)". This is read as the full `n`-th Fréchet derivative in
  `z` of the slice `z ↦ extension (h, z)`, for every `n : ℕ`. It contains every fixed partial
  derivative in `(A, B, s)`. The slice identity `slice_iteratedFDeriv_STR02960` relates it to
  the joint derivative of the extension on `O`.
* Rate normalisation. No angular-to-physical rate normalisation is applied. The `h`-variable of
  the division is the scaled variable of the packet, exactly as in STR029.57.
* Size. The file is longer than the 85-110 line estimate in the brief. The statement was not
  weakened to fit the estimate.
-/

open scoped ContDiff Pointwise
open DGPS.Analysis.PeriodicHolder
open Filter Topology Set

namespace DGPS.Frontier.STR029

/-! ### Polynomial vanishing and the Taylor identification -/

theorem poly_zero_STR02960 (n : ℕ) : ∀ b : ℕ → ℝ,
    (fun h : ℝ => ∑ k ∈ Finset.range (n + 1), b k * h ^ k) =o[𝓝[≠] (0 : ℝ)] (fun h : ℝ => h ^ n) →
      ∀ k ≤ n, b k = 0 := by
  induction n with
  | zero =>
    intro b hb k hk
    obtain rfl : k = 0 := by omega
    have hfun : (fun h : ℝ => ∑ k ∈ Finset.range (0 + 1), b k * h ^ k) = fun _ : ℝ => b 0 := by
      funext h
      simp
    have hpow0 : (fun h : ℝ => h ^ 0) = fun _ : ℝ => (1 : ℝ) := by
      funext h
      simp
    rw [hfun, hpow0] at hb
    have ht : Tendsto (fun _ : ℝ => b 0) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (Asymptotics.isLittleO_one_iff ℝ).1 hb
    exact (tendsto_nhds_unique ht tendsto_const_nhds).symm
  | succ n ih =>
    intro b hb
    have hsplit : (fun h : ℝ => ∑ k ∈ Finset.range (n + 1 + 1), b k * h ^ k) =
        fun h => h * (∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k) + b 0 := by
      funext h
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · simp
    rw [hsplit] at hb
    have hpow : Tendsto (fun h : ℝ => h ^ (n + 1)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h0 : Tendsto (fun h : ℝ => h ^ (n + 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (n + 1))) :=
        (continuous_pow (n + 1)).tendsto 0
      rw [zero_pow (Nat.succ_ne_zero n)] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hT : Continuous fun h : ℝ => ∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k := by
      fun_prop
    have hmul : Tendsto (fun h : ℝ => h * (∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun h : ℝ => h * (∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k))
          (𝓝 0) (𝓝 ((0 : ℝ) * ∑ k ∈ Finset.range (n + 1), b (k + 1) * (0 : ℝ) ^ k)) :=
        (continuous_id.mul hT).tendsto (0 : ℝ)
      rw [zero_mul] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have hlim : Tendsto (fun h : ℝ => h * (∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k) + b 0)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := hb.tendsto_zero_of_tendsto hpow
    have hb0 : b 0 = 0 := by
      have h2 := tendsto_nhds_unique hlim (hmul.add tendsto_const_nhds)
      simp only [zero_add] at h2
      linarith
    have hb' : (fun h : ℝ => h * (∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k)) =o[𝓝[≠] (0 : ℝ)]
        (fun h : ℝ => h ^ (n + 1)) := by
      have h3 := hb
      simp only [hb0, add_zero] at h3
      exact h3
    have hS : (fun h : ℝ => ∑ k ∈ Finset.range (n + 1), b (k + 1) * h ^ k) =o[𝓝[≠] (0 : ℝ)]
        (fun h : ℝ => h ^ n) := by
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      filter_upwards [hb'.def hc, self_mem_nhdsWithin] with x hx hx0
      have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hx' : ‖x‖ * ‖∑ k ∈ Finset.range (n + 1), b (k + 1) * x ^ k‖ ≤
          c * (‖x‖ ^ n * ‖x‖) := by
        have hx2 : ‖x * (∑ k ∈ Finset.range (n + 1), b (k + 1) * x ^ k)‖ ≤
            c * ‖x ^ (n + 1)‖ := hx
        rw [norm_mul, norm_pow, pow_succ] at hx2
        exact hx2
      have key : ‖x‖ * ‖∑ k ∈ Finset.range (n + 1), b (k + 1) * x ^ k‖ ≤
          ‖x‖ * (c * ‖x‖ ^ n) := by
        calc _ ≤ c * (‖x‖ ^ n * ‖x‖) := hx'
          _ = ‖x‖ * (c * ‖x‖ ^ n) := by ring
      show ‖∑ k ∈ Finset.range (n + 1), b (k + 1) * x ^ k‖ ≤ c * ‖x ^ n‖
      rw [norm_pow]
      exact le_of_mul_le_mul_left key hxn
    intro k hk
    rcases k with _ | j
    · exact hb0
    · exact ih (fun k => b (k + 1)) hS j (by omega)

theorem jet_zero_STR02960 (g : ℝ → ℝ) {r c M : ℝ} (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (Metric.ball 0 r))
    (hb : ∀ᶠ h in 𝓝 (0 : ℝ), |g h - c * h ^ 4| ≤ M * |h| ^ 5) :
    (∀ j ≤ 3, iteratedDeriv j g 0 = 0) ∧ iteratedDeriv 4 g 0 = 24 * c := by
  have hg4 : ContDiffOn ℝ (4 : ℕ) g (Metric.ball 0 r) :=
    hg.of_le (by norm_cast)
  have hT := taylor_isLittleO (f := g) (x₀ := 0) (n := 4) (s := Metric.ball 0 r)
    (convex_ball 0 r) (Metric.mem_ball_self hr) hg4
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds 0 hr)] at hT
  have hP : ∀ x : ℝ, taylorWithinEval g 4 (Metric.ball 0 r) 0 x =
      ∑ k ∈ Finset.range 5, ((Nat.factorial k : ℝ)⁻¹ * x ^ k) * iteratedDeriv k g 0 := by
    intro x
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk' : iteratedDerivWithin k g (Metric.ball 0 r) 0 = iteratedDeriv k g 0 :=
      iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr)
    rw [smul_eq_mul, sub_zero, hk']
  have hT2 : (fun x : ℝ => g x - ∑ k ∈ Finset.range 5,
      ((Nat.factorial k : ℝ)⁻¹ * x ^ k) * iteratedDeriv k g 0) =o[𝓝 (0 : ℝ)]
        (fun x : ℝ => x ^ 4) := by
    have e : (fun x : ℝ => g x - ∑ k ∈ Finset.range 5,
        ((Nat.factorial k : ℝ)⁻¹ * x ^ k) * iteratedDeriv k g 0) =
        (fun x : ℝ => g x - taylorWithinEval g 4 (Metric.ball 0 r) 0 x) := by
      funext x
      rw [hP x]
    rw [e]
    simpa only [sub_zero] using hT
  have hO : (fun h : ℝ => g h - c * h ^ 4) =O[𝓝 (0 : ℝ)] (fun h : ℝ => h ^ 5) := by
    refine Asymptotics.IsBigO.of_bound M ?_
    filter_upwards [hb] with h hh
    simp only [Real.norm_eq_abs, norm_pow]
    exact hh
  have hA : (fun h : ℝ => g h - c * h ^ 4) =o[𝓝 (0 : ℝ)] (fun h : ℝ => h ^ 4) :=
    hO.trans_isLittleO (Asymptotics.isLittleO_pow_pow (by norm_num : 4 < 5))
  set b : ℕ → ℝ := fun k => (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k g 0 -
    if k = 4 then c else 0 with hb_def
  have hfun : (fun h : ℝ => ∑ k ∈ Finset.range (4 + 1), b k * h ^ k) =
      fun h : ℝ => (g h - c * h ^ 4) - (g h - ∑ k ∈ Finset.range 5,
        ((Nat.factorial k : ℝ)⁻¹ * h ^ k) * iteratedDeriv k g 0) := by
    funext h
    simp only [hb_def, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num [Nat.factorial]
    ring
  have hPL : (fun h : ℝ => ∑ k ∈ Finset.range (4 + 1), b k * h ^ k) =o[𝓝[≠] (0 : ℝ)]
      (fun h : ℝ => h ^ 4) := by
    rw [hfun]
    exact (hA.sub hT2).mono nhdsWithin_le_nhds
  have hz := poly_zero_STR02960 4 b hPL
  have hfac : ∀ j : ℕ, (Nat.factorial j : ℝ)⁻¹ ≠ 0 := fun j =>
    inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j))
  refine ⟨fun j hj => ?_, ?_⟩
  · have h1 : b j = 0 := hz j (by omega)
    have hne : j ≠ 4 := by omega
    have hbj : b j = (Nat.factorial j : ℝ)⁻¹ * iteratedDeriv j g 0 := by
      rw [hb_def]
      simp [hne]
    rw [hbj] at h1
    exact (mul_eq_zero.1 h1).resolve_left (hfac j)
  · have h1 : b 4 = 0 := hz 4 le_rfl
    have hbj : b 4 = (Nat.factorial 4 : ℝ)⁻¹ * iteratedDeriv 4 g 0 - c := by
      rw [hb_def]
      simp
    rw [hbj] at h1
    norm_num [Nat.factorial] at h1
    linarith

/-! ### Scalar and smooth-structure helpers -/

/-- The closed value `J4red A B - s (A ^ 2 + B ^ 2) / 2` of the `h = 0` coefficient. -/
noncomputable def cval_STR02960 (A B s : ℝ) : ℝ :=
  Jred_STR02918 A B - s * ((A ^ 2 + B ^ 2) / 2)

/-- Polynomial identity: the scaled `STR029.57` polynomial equals `cval · h ^ 4`. -/
theorem poly_c_STR02960 (A B s h : ℝ) :
    poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s) = cval_STR02960 A B s * h ^ 4 := by
  rw [poly19_scaled_STR02957]
  unfold cval_STR02960
  ring

theorem coord_contDiff_STR02960 (i : Fin 3) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => p.2 i) := by
  fun_prop

theorem nat_le_top_STR02960 (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.2 le_top

theorem Zh_STR02960 (h : ℝ) :
    Z_STR02954 (h, 0) = meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))) := by
  have h0 : ∀ t : ℝ, PeriodicHolder_STR02968.val 0 t = 0 := fun t =>
    congrFun (PeriodicHolder_STR02968.val_eq_zero.2 rfl) t
  rw [Z_eq_meanT_STR02954]
  congr 1
  funext s
  simp [h0]

/-- Joint `C^∞` regularity of the chart functional in `(h, γ, u)`. -/
theorem JC2_joint_STR02960 :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => JC2_STR02956 x.1 x.2.1 x.2.2) := by
  have h0 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e0_STR02955 x.2.2) :=
    e0_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => e1_STR02955 x.2.2) :=
    e1_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  have hρ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      rho_STR02954 (x.1, e0_STR02955 x.2.2)) :=
    rho_smooth_STR02954.comp (contDiff_fst.prodMk h0)
  have hZ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    logZ_smooth_STR02954.comp (contDiff_fst.prodMk h0)
  have hL : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      Real.log (Z_STR02954 (x.1, 0))) :=
    logZ_smooth_STR02954.comp (contDiff_fst.prodMk contDiff_const)
  have hI : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 *
        rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp ((h1.mul h1).mul hρ)
  have hE : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      meanCLM_STR02954 (e0_STR02955 x.2.2 * rho_STR02954 (x.1, e0_STR02955 x.2.2))) :=
    meanCLM_STR02954.contDiff.comp (h0.mul hρ)
  have hγ : ContDiff ℝ ∞ (fun x : ℝ × ℝ × PeriodicC2_STR02969 => 2 * (1 + x.2.1)) :=
    contDiff_const.mul (contDiff_const.add (contDiff_fst.comp contDiff_snd))
  have hfun : (fun x : ℝ × ℝ × PeriodicC2_STR02969 => JC2_STR02956 x.1 x.2.1 x.2.2) =
      fun x => meanCLM_STR02954 (e1_STR02955 x.2.2 * e1_STR02955 x.2.2 *
          rho_STR02954 (x.1, e0_STR02955 x.2.2)) -
        2 * (1 + x.2.1) * (meanCLM_STR02954 (e0_STR02955 x.2.2 *
            rho_STR02954 (x.1, e0_STR02955 x.2.2)) -
          Real.log (Z_STR02954 (x.1, e0_STR02955 x.2.2)) + Real.log (Z_STR02954 (x.1, 0))) := by
    funext x
    unfold JC2_STR02956
    rw [Zh_STR02960]
  rw [hfun]
  exact hI.sub (hγ.mul ((hE.sub hZ).add hL))

/-! ### The scaled function `G` and its smoothness -/

/-- The scaled parameter map `(h, z) ↦ (h z₀, h z₁, h, h² z₂)` with `z = (A, B, s)`. -/
def scale_STR02960 (p : ℝ × (Fin 3 → ℝ)) : Par_STR02916 :=
  (p.1 * p.2 0, p.1 * p.2 1, p.1, p.1 ^ 2 * p.2 2)

theorem scale_contDiff_STR02960 : ContDiff ℝ ∞ scale_STR02960 := by
  unfold scale_STR02960
  exact (contDiff_fst.mul (coord_contDiff_STR02960 0)).prodMk
    ((contDiff_fst.mul (coord_contDiff_STR02960 1)).prodMk
      (contDiff_fst.prodMk ((contDiff_fst.pow 2).mul (coord_contDiff_STR02960 2))))

/-- The scaled function `G (h, z) = F (h A, h B, h, h² s)` with `F = Fred_STR02956 ψ`. -/
noncomputable def Gs_STR02960 (ψ : Par_STR02916 → E_STR02969) (p : ℝ × (Fin 3 → ℝ)) : ℝ :=
  Fred_STR02956 ψ (p.1 * p.2 0, p.1 * p.2 1) (p.1, p.1 ^ 2 * p.2 2)

/-- The chart-side vector field of `Gs_STR02960`, with the parameter `ψ` evaluated at `scale`. -/
noncomputable def Lp_STR02960 (ψ : Par_STR02916 → E_STR02969) (p : ℝ × (Fin 3 → ℝ)) :
    PeriodicC2_STR02969 :=
  (p.1 * p.2 0) • cosC2_STR02915 + (p.1 * p.2 1) • sinC2_STR02915 +
    ((ψ (scale_STR02960 p) : E_STR02969) : PeriodicC2_STR02969)

theorem Gs_eq_STR02960 (ψ : Par_STR02916 → E_STR02969) (p : ℝ × (Fin 3 → ℝ)) :
    Gs_STR02960 ψ p = JC2_STR02956 p.1 (p.1 ^ 2 * p.2 2) (Lp_STR02960 ψ p) := by
  unfold Gs_STR02960
  exact Fred_eq_STR02956 ψ (p.1 * p.2 0, p.1 * p.2 1) (p.1, p.1 ^ 2 * p.2 2)

theorem Gs_contDiffOn_STR02960 {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (Gs_STR02960 ψ) (scale_STR02960 ⁻¹' U) := by
  have hsc : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      ((ψ (scale_STR02960 p) : E_STR02969) : PeriodicC2_STR02969)) (scale_STR02960 ⁻¹' U) :=
    E_STR02969.subtypeL.contDiff.comp_contDiffOn
      (hψ.comp scale_contDiff_STR02960.contDiffOn (fun p hp => hp))
  have hA : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => p.1 * p.2 0) :=
    contDiff_fst.mul (coord_contDiff_STR02960 0)
  have hB : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => p.1 * p.2 1) :=
    contDiff_fst.mul (coord_contDiff_STR02960 1)
  have hC : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => p.1 ^ 2 * p.2 2) :=
    (contDiff_fst.pow 2).mul (coord_contDiff_STR02960 2)
  have hLp : ContDiffOn ℝ ∞ (Lp_STR02960 ψ) (scale_STR02960 ⁻¹' U) := by
    unfold Lp_STR02960
    exact ((hA.smul (contDiff_const (c := cosC2_STR02915))).add
      (hB.smul (contDiff_const (c := sinC2_STR02915)))).contDiffOn.add hsc
  have hΦ : ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) =>
      ((p.1, p.1 ^ 2 * p.2 2, Lp_STR02960 ψ p) : ℝ × ℝ × PeriodicC2_STR02969))
      (scale_STR02960 ⁻¹' U) :=
    contDiff_fst.contDiffOn.prodMk (hC.contDiffOn.prodMk hLp)
  have hfun : Gs_STR02960 ψ = (fun x : ℝ × ℝ × PeriodicC2_STR02969 =>
      JC2_STR02956 x.1 x.2.1 x.2.2) ∘
      (fun p : ℝ × (Fin 3 → ℝ) => ((p.1, p.1 ^ 2 * p.2 2, Lp_STR02960 ψ p) :
        ℝ × ℝ × PeriodicC2_STR02969)) :=
    funext fun p => Gs_eq_STR02960 ψ p
  rw [hfun]
  exact JC2_joint_STR02960.comp_contDiffOn hΦ

/-! ### Slices of joint derivatives -/

/-- The joint `n`-th derivative of `E` transported to the `z`-directions. -/
noncomputable def slicePhi_STR02960 (E : ℝ × (Fin 3 → ℝ) → ℝ) (n : ℕ)
    (p : ℝ × (Fin 3 → ℝ)) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) ℝ :=
  (iteratedFDeriv ℝ n E p).compContinuousLinearMap
    (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))

/-- The `n`-th derivative of the `z`-slice at `(h, z)` is the joint derivative restricted to the
`z`-directions. -/
theorem slice_iteratedFDeriv_STR02960 {E : ℝ × (Fin 3 → ℝ) → ℝ} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hO : IsOpen O) (hE : ContDiffOn ℝ ∞ E O) (n : ℕ) {h : ℝ} {z : Fin 3 → ℝ}
    (hz : (h, z) ∈ O) :
    iteratedFDeriv ℝ n (fun w => E (h, w)) z = slicePhi_STR02960 E n (h, z) := by
  have hn : (n : WithTop ℕ∞) ≤ ∞ := nat_le_top_STR02960 n
  set a : ℝ × (Fin 3 → ℝ) := (h, 0) with ha
  set T : Set (ℝ × (Fin 3 → ℝ)) := (fun x => a + x) ⁻¹' O with hT
  set g : (Fin 3 → ℝ) →L[ℝ] ℝ × (Fin 3 → ℝ) := ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ) with hg
  have hTo : IsOpen T := hO.preimage (continuous_const.add continuous_id)
  have hS : IsOpen (g ⁻¹' T) := hTo.preimage g.continuous
  have htr : ContDiff ℝ ∞ (fun x : ℝ × (Fin 3 → ℝ) => a + x) := contDiff_const.add contDiff_id
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × (Fin 3 → ℝ) => E (a + x)) T :=
    hE.comp htr.contDiffOn (fun x hx => hx)
  have hVT : a +ᵥ T = O := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨-a + y, by show a + (-a + y) ∈ O; simpa using hy, by simp [vadd_eq_add]⟩
  have hzT : g z ∈ T := by
    show a + g z ∈ O
    have hpt : a + g z = (h, z) := by simp [ha, hg]
    rw [hpt]
    exact hz
  have hzS : z ∈ g ⁻¹' T := hzT
  have hfeq : (fun w => E (h, w)) = (fun x : ℝ × (Fin 3 → ℝ) => E (a + x)) ∘ g := by
    funext w
    simp [ha, hg]
  have hL : iteratedFDeriv ℝ n (fun w => E (h, w)) z =
      iteratedFDerivWithin ℝ n (fun w => E (h, w)) (g ⁻¹' T) z :=
    ((iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun w => E (h, w)) n hS hzS)).symm
  have hpt' : a + g z = (h, z) := by simp [ha, hg]
  have hinner : iteratedFDerivWithin ℝ n (fun x : ℝ × (Fin 3 → ℝ) => E (a + x)) T (g z) =
      iteratedFDeriv ℝ n E (h, z) := by
    rw [iteratedFDerivWithin_comp_add_left (f := E) (s := T) n a (g z), hVT,
      iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := E) n hO (show a + g z ∈ O from hzT), hpt']
  unfold slicePhi_STR02960
  rw [hL, hfeq,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right g hF hTo.uniqueDiffOn hS.uniqueDiffOn
      hzT hn, hinner]

/-- The joint derivative transported to the `z`-directions is continuous on the open domain. -/
theorem continuousOn_slice_STR02960 {E : ℝ × (Fin 3 → ℝ) → ℝ} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hO : IsOpen O) (hE : ContDiffOn ℝ ∞ E O) (n : ℕ) :
    ContinuousOn (slicePhi_STR02960 E n) O := by
  have hk : (n : WithTop ℕ∞) ≤ ∞ := nat_le_top_STR02960 n
  have hL : Continuous (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ)) :
      ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ × (Fin 3 → ℝ)) ℝ →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) ℝ) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ (Fin 3 → ℝ))).continuous
  exact hL.comp_continuousOn (ContinuousOn.continuousOn_iteratedFDeriv hE hO hk)

/-- Uniform convergence of the `n`-th `z`-slice derivatives as `h → 0` on compact sets, for an
extension `E` that is `C^∞` on an open set `O` containing `{0} × ℝ³`. -/
theorem tendsto_unif_slice_STR02960 {E : ℝ × (Fin 3 → ℝ) → ℝ} {O : Set (ℝ × (Fin 3 → ℝ))}
    (hO : IsOpen O) (hE : ContDiffOn ℝ ∞ E O) (h0 : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O)
    (n : ℕ) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (h : ℝ) (z : Fin 3 → ℝ) => iteratedFDeriv ℝ n (fun w => E (h, w)) z)
      (fun z => iteratedFDeriv ℝ n (fun w => E ((0 : ℝ), w)) z) (𝓝 0) K := by
  have hΦc : ContinuousOn (slicePhi_STR02960 E n) O := continuousOn_slice_STR02960 hO hE n
  have hslice : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O →
      iteratedFDeriv ℝ n (fun w => E (h, w)) z = slicePhi_STR02960 E n (h, z) :=
    fun h z hz => slice_iteratedFDeriv_STR02960 hO hE n hz
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ∀ z ∈ K,
      (h, z) ∈ O ∧ dist (slicePhi_STR02960 E n (h, z)) (slicePhi_STR02960 E n ((0 : ℝ), z)) < ε := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun (h : ℝ) (z : Fin 3 → ℝ) =>
        (h, z) ∈ O ∧ dist (slicePhi_STR02960 E n (h, z)) (slicePhi_STR02960 E n ((0 : ℝ), z)) < ε) ?_
    intro y _
    have hy0 : ((0 : ℝ), y) ∈ O := h0 y
    have h1 : ContinuousAt (slicePhi_STR02960 E n) ((0 : ℝ), y) :=
      hΦc.continuousAt (hO.mem_nhds hy0)
    have hq : Continuous (fun q : ℝ × (Fin 3 → ℝ) => ((0 : ℝ), q.2)) := by fun_prop
    have h2 : ContinuousAt (fun q : ℝ × (Fin 3 → ℝ) => slicePhi_STR02960 E n ((0 : ℝ), q.2))
        ((0 : ℝ), y) :=
      ContinuousAt.comp (f := fun q : ℝ × (Fin 3 → ℝ) => ((0 : ℝ), q.2))
        (x := ((0 : ℝ), y)) h1 hq.continuousAt
    have hcont : ContinuousAt
        (fun q : ℝ × (Fin 3 → ℝ) => dist (slicePhi_STR02960 E n q)
          (slicePhi_STR02960 E n ((0 : ℝ), q.2))) ((0 : ℝ), y) := h1.dist h2
    have hlt : ∀ᶠ q in 𝓝 ((0 : ℝ), y),
        dist (slicePhi_STR02960 E n q) (slicePhi_STR02960 E n ((0 : ℝ), q.2)) < ε :=
      hcont.eventually_lt
        (show ContinuousAt (fun _ : ℝ × (Fin 3 → ℝ) => ε) ((0 : ℝ), y) from continuousAt_const)
        (by simpa using hε)
    filter_upwards [hO.mem_nhds hy0, hlt] with q hq1 hq2
    exact ⟨hq1, hq2⟩
  filter_upwards [hev] with h hh z hz
  obtain ⟨hOh, hd⟩ := hh z hz
  show dist (iteratedFDeriv ℝ n (fun w => E ((0 : ℝ), w)) z)
    (iteratedFDeriv ℝ n (fun w => E (h, w)) z) < ε
  rw [hslice 0 z (h0 z), hslice h z hOh, dist_comm]
  exact hd

/-! ### Main theorem -/

/-- STR029.60. Apply division and retain parameter derivative limits. -/
theorem str029_60_apply_division_retain_parameter_derivative_limits :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      (∃ Ω : Set (ℝ × (Fin 3 → ℝ)), IsOpen Ω ∧ ContDiffOn ℝ ∞ (Gs_STR02960 ψ) Ω ∧
        (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ Ω) ∧
        ∀ j : ℕ, j ≤ 3 → ∀ z : Fin 3 → ℝ, iteratedDeriv j (fun h => Gs_STR02960 ψ (h, z)) 0 = 0) ∧
      ∃ O : Set (ℝ × (Fin 3 → ℝ)), IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧
        ContDiffOn ℝ ∞
          (fun p : ℝ × (Fin 3 → ℝ) => quotientRemainder_STR02959 (Gs_STR02960 ψ) p.1 p.2) O ∧
        (∀ h z, (h, z) ∈ O → h ≠ 0 →
          quotientRemainder_STR02959 (Gs_STR02960 ψ) h z = Gs_STR02960 ψ (h, z) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, quotientRemainder_STR02959 (Gs_STR02960 ψ) 0 z =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∀ (n : ℕ) (K : Set (Fin 3 → ℝ)), IsCompact K →
          TendstoUniformlyOn
            (fun (h : ℝ) (z : Fin 3 → ℝ) =>
              iteratedFDeriv ℝ n (fun w => quotientRemainder_STR02959 (Gs_STR02960 ψ) h w) z)
            (fun z => iteratedFDeriv ℝ n (fun w => quotientRemainder_STR02959 (Gs_STR02960 ψ) 0 w) z)
            (𝓝 0) K := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, hbd⟩ :=
    str029_57_weighted_fourth_jet_reduced_functional
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψC, hψ0, hψV, hRpar, ?_⟩
  have hΩ : IsOpen (scale_STR02960 ⁻¹' U) := hU.preimage scale_contDiff_STR02960.continuous
  have hGC : ContDiffOn ℝ ∞ (Gs_STR02960 ψ) (scale_STR02960 ⁻¹' U) :=
    Gs_contDiffOn_STR02960 hψC
  have h0Ω : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ scale_STR02960 ⁻¹' U := by
    intro z
    have hs0 : scale_STR02960 ((0 : ℝ), z) = 0 := by
      simp [scale_STR02960]
    show scale_STR02960 ((0 : ℝ), z) ∈ U
    rw [hs0]
    exact h0U
  -- Jet at zero for each parameter value, from the STR029.57 bound on a singleton.
  have hjet : ∀ z : Fin 3 → ℝ,
      (∀ j : ℕ, j ≤ 3 → iteratedDeriv j (fun h => Gs_STR02960 ψ (h, z)) 0 = 0) ∧
        iteratedDeriv 4 (fun h => Gs_STR02960 ψ (h, z)) 0 =
          24 * cval_STR02960 (z 0) (z 1) (z 2) := by
    intro z
    obtain ⟨δ, hδ, M, _, hb⟩ := hbd {((z 0, z 1, z 2) : ℝ × ℝ × ℝ)} isCompact_singleton
    have hcd : ContDiff ℝ ∞ (fun h : ℝ => (h, z)) := contDiff_id.prodMk contDiff_const
    have hmem : (fun h : ℝ => (h, z)) ⁻¹' (scale_STR02960 ⁻¹' U) ∈ 𝓝 (0 : ℝ) :=
      (hΩ.preimage hcd.continuous).mem_nhds (h0Ω z)
    obtain ⟨r, hr, hrΩ⟩ := Metric.mem_nhds_iff.1 hmem
    have hg : ContDiffOn ℝ ∞ (fun h => Gs_STR02960 ψ (h, z)) (Metric.ball 0 r) :=
      hGC.comp hcd.contDiffOn (fun h hh => hrΩ hh)
    have hev : ∀ᶠ h in 𝓝 (0 : ℝ),
        |Gs_STR02960 ψ (h, z) - cval_STR02960 (z 0) (z 1) (z 2) * h ^ 4| ≤ M * |h| ^ 5 := by
      filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with h hh
      have hh' : |h| ≤ δ := by simpa [Real.dist_eq] using Metric.mem_closedBall.1 hh
      have hb1 := (hb (z 0) (z 1) (z 2) (Set.mem_singleton _) h hh').2
      rw [← poly_c_STR02960]
      exact hb1
    exact jet_zero_STR02960 (fun h => Gs_STR02960 ψ (h, z)) hr hg hev
  have hvan : ∀ j : ℕ, j ≤ 3 → ∀ z ∈ (Set.univ : Set (Fin 3 → ℝ)),
      iteratedDeriv j (fun h => Gs_STR02960 ψ (h, z)) 0 = 0 :=
    fun j hj z _ => (hjet z).1 j hj
  -- Coordinate division on each parameter value, glued over the union of neighbourhoods.
  choose W hWo hW0 _ _ hWC hWval hWzero using fun z : Fin 3 → ℝ =>
    str029_59_smooth_division_coordinate_power (U := Set.univ) hΩ hGC
      (fun z _ => h0Ω z) hvan (z₀ := z) (Set.mem_univ z)
  have hOo : IsOpen (⋃ z, W z) := isOpen_iUnion hWo
  have h0O : ∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ ⋃ z', W z' :=
    fun z => Set.mem_iUnion.2 ⟨z, hW0 z⟩
  have hOC : ContDiffOn ℝ ∞
      (fun p : ℝ × (Fin 3 → ℝ) => quotientRemainder_STR02959 (Gs_STR02960 ψ) p.1 p.2)
      (⋃ z, W z) := by
    apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨z, hz⟩ := Set.mem_iUnion.1 hx
    exact ⟨W z, hWo z, hz, (hWC z).mono Set.inter_subset_right⟩
  have hval : ∀ h z, (h, z) ∈ (⋃ z', W z') → h ≠ 0 →
      quotientRemainder_STR02959 (Gs_STR02960 ψ) h z = Gs_STR02960 ψ (h, z) / h ^ 4 := by
    intro h z hhz hh0
    obtain ⟨z', hz'⟩ := Set.mem_iUnion.1 hhz
    exact hWval z' h z hz' (Set.mem_univ z) hh0
  have hzero : ∀ z : Fin 3 → ℝ, quotientRemainder_STR02959 (Gs_STR02960 ψ) 0 z =
      Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2) := by
    intro z
    rw [hWzero z z (hW0 z) (Set.mem_univ z), (hjet z).2]
    have hf4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf4]
    unfold cval_STR02960
    ring
  refine ⟨⟨scale_STR02960 ⁻¹' U, hΩ, hGC, h0Ω, fun j hj z => (hjet z).1 j hj⟩,
    ⋃ z, W z, hOo, h0O, hOC, hval, hzero, ?_⟩
  intro n K hK
  exact tendsto_unif_slice_STR02960 hOo hOC h0O n hK

end DGPS.Frontier.STR029
