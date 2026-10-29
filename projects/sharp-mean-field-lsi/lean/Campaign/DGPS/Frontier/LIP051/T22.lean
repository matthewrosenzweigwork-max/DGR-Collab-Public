import DGPS.Frontier.LIP051.T03
import DGPS.Frontier.LIP051.T10
import DGPS.Frontier.LIP051.T13
import DGPS.Frontier.LIP051.T16
import DGPS.Frontier.LIP051.T17
import DGPS.Frontier.LIP051.T21
import DGPS.Frontier.LIP051.T34
import DGPS.Frontier.LIP051.T44
import DGPS.Frontier.LIP051.T45

/-!
# LIP051.22: Characteristic-function error estimate

Task id `LIP051.22`, title "Characteristic-function error estimate" (node LIP051, "Joint Gaussian
and quadratic fluctuation limit", leaf formalization, verification V1, dispatch tier 4).

Fix `m ≥ 1`, `R ≥ m`, a vector `a : Fin m → ℝ` and a real `t`. On the sample side, `χ_N` is the
characteristic function at the frequency `(a, t)` of the joint vector `(Z_{N,1}, …, Z_{N,m}, U_N)`,
that is `E exp(i (∑_k a_k Z_{N,k} + t U_N))`, and `χ_{N,R}` is the same with `U_N` replaced by
`V_{N,R}`. On the limit side, `χ_∞` and `χ_{∞,R}` are the corresponding integrals against the
Gaussian reference law `γ₀` on `ℕ → ℝ`, with `U_∞ = (Q_T + d_K)/2` and `V_{∞,R}` the same
expression with the Wick section `Q_R` in place of `Q_T`. The main declaration proves

* `|χ_N - χ_{N,R}| ≤ (|t| / √2) ‖F_R‖₂ + |t| ‖D_{N,R}‖₁` for every `N ≥ 1`, and
* `|χ_∞ - χ_{∞,R}| ≤ (|t| / √2) ‖F_R‖₂` for every `L²(γ₀)` limit `Q_T` of the Wick sections.

## Provides

* `DGPS.Frontier.LIP051.lip051_22_characteristic_function_error_estimate`: the conjunction of the
  sample-side bound (for every `N ≥ 1`) and the limit-side bound (for every `L²(γ₀)` limit `Q_T`
  and every measurable representative `Q'` of it), both with the frequency `(a, t)`.
* `DGPS.Frontier.LIP051.exp_sub_le_LIP05122`: the Lipschitz bound `|e^{iu} - e^{iv}| ≤ |u - v|`.
* `DGPS.Frontier.LIP051.integrable_phase_LIP05122`: the phase `e^{i Z}` of a real measurable
  function is integrable on a finite measure.
* `DGPS.Frontier.LIP051.charDiff_LIP05122`: the difference of two characteristic-function integrals
  with a common phase `S` and energies `X`, `Y` is bounded by `|c| ∫|X - Y|`.
* `DGPS.Frontier.LIP051.abs_split_LIP05122`: `∫|E - F| ≤ ∫|A| + ∫|D|` when `E - F = A + D`.
* `DGPS.Frontier.LIP051.abs_pairSum_LIP05122`: integrability of the pair sum `A_N(F)` and its
  `L¹` bound `(1/√2) ‖F‖₂` from `LIP051.10`.

## R5 notes

1. Common hypotheses. The binders are those invoked by the prerequisites: `Continuous (uncurry W)`,
   symmetry of `W`, `0 ≤ M` with `|W x y| ≤ M`, the Hilbert basis `e` of `L²(μ)` with `e 0 = 1`,
   and measurable representatives `f j =ᵐ[μ] e j` (measurability is supplied by `hfm`). They are
   the node setting; the specification of this unit lists none of its own, and none is added
   beyond what `LIP051.03`, `.10`, `.13`, `.17`, `.21` and `.34` require. `μ` is a probability
   measure, as in the campaign setup.
2. Sample side for `N ≥ 1`. The bound is stated for `1 ≤ N` because `LIP051.10` requires it (the
   node defines `Z_{N,j}` and `U_N` for `N ≥ 1`). The case `N = 0` is not claimed.
3. Positive modes (defect FD-002). The Gaussian block is the positive modes `k + 1`, `k ∈ Fin m`,
   on both sides; the zero mode `e_0 = 1` never appears in the phase. The binder `R ≥ m` of the
   specification is kept in the statement but is not used, since the bounds hold for every `R`;
   it is cleared inside the proof so that the linter reports nothing.
4. Joint characteristic function. Reading "the joint characteristic function" as the integral at
   the frequency `(a, t)`, the phase is `∑_k a_k Z_{N,k} + t U_N`. The coordinate part has modulus
   one and cancels in the difference, so the coordinate block contributes no error term.
5. Sample energy. `U_N` is `energyLIP05121` of the pointwise centered kernel `K = centeredKernelOf_LIP05103 μ W`;
   the original continuous diagonal is retained and no almost-everywhere representative is used.
   `V_{N,R}` is `fixedRankLIP05121` with coefficients `T_ij` over `e = f`, and `D_{N,R}` is
   `diagRemLIP05121`. `‖F_R‖₂` is `(eLpNorm F_R 2 (μ ⊗ μ)).toReal`, and `‖D_{N,R}‖₁` is the
   Bochner integral of `|D_{N,R}|` under `Measure.pi`.
6. Limit energy. The specification's `Q_T` is any `L²(γ₀)` limit of the Wick sections, as given by
   `LIP051.17`; the statement quantifies over every such limit. The random variable `U_∞` is
   represented by an arbitrary measurable `Q'` with `Q' =ᵐ[γ₀] Q_T`, so the characteristic integrals
   are defined with that representative. The result does not depend on the choice, since the
   integrals are invariant under almost-everywhere modification.
7. Limit Wick section. `V_{∞,R}` is written `(Q_R + d_K)/2` with
   `Q_R = wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f)`, which is the expression
   `(1/2)[∑_{i,j=1}^R T_ij (z_i z_j - δ_ij) + d_K]` of the specification. `d_K` is `dK_LIP05145 μ W`
   (the integral of the original diagonal); on the sample side it is `dKLIP05121`, the same integral.
8. Constant. The factor `|t|/√2` on the limit side is derived: `‖Q_T - Q_R‖₂ = √2 ‖F_R‖₂` is the
   tail identity of `LIP051.17`, and `∫|·| ≤ ‖·‖₂` on the probability space `γ₀`. The sample-side
   factor `1/√2` is the `L¹` bound of `LIP051.10`.
9. Integrability. Every characteristic-function integrand has modulus one and is measurable, so
   each integral exists without further hypotheses. The pair sum `A_N` is integrable by `LIP051.10`
   (its second moment is finite), and `D_{N,R}` is integrable by `LIP051.13`.
10. Interchange. Only finite sums appear on the sample side, and the limit side involves a single
    fixed `R`; no limit is interchanged with an integral. The Tendsto hypothesis in the limit
    statement is the one needed by `LIP051.17` to identify the tail identity for `Q_T`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The Lipschitz bound for the complex exponential on the imaginary axis:
`|e^{iu} - e^{iv}| ≤ |u - v|` for real `u`, `v`. -/
lemma exp_sub_le_LIP05122 (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have hsplit : Complex.I * (u : ℂ) = Complex.I * (v : ℂ) + Complex.I * ((u - v : ℝ) : ℂ) := by
    push_cast
    ring
  have h1 : Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (v : ℂ))
      = Complex.exp (Complex.I * (v : ℂ)) * (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    rw [hsplit, Complex.exp_add, mul_sub, mul_one]
  rw [h1, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- The phase `e^{i Z}` of a real measurable function is integrable on a finite measure. -/
lemma integrable_phase_LIP05122 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) :
    Integrable (fun ω => Complex.exp (Complex.I * ((Z ω : ℝ) : ℂ))) P := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
  · exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).measurable.comp
      hZ).aestronglyMeasurable
  · exact (Complex.norm_exp_I_mul_ofReal _).le

/-- Characteristic-function difference with a common phase `S`: the two integrals with energies
`X` and `Y` differ by at most `|c| ∫|X - Y|`. -/
lemma charDiff_LIP05122 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S X Y : Ω → ℝ) (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => X ω - Y ω) P) (c : ℝ) :
    ‖(∫ ω, Complex.exp (Complex.I * ((S ω + c * X ω : ℝ) : ℂ)) ∂P)
        - ∫ ω, Complex.exp (Complex.I * ((S ω + c * Y ω : ℝ) : ℂ)) ∂P‖
      ≤ |c| * ∫ ω, |X ω - Y ω| ∂P := by
  have hI1 : Integrable (fun ω => Complex.exp (Complex.I * ((S ω + c * X ω : ℝ) : ℂ))) P :=
    integrable_phase_LIP05122 P _ (hS.add (measurable_const.mul hX))
  have hI2 : Integrable (fun ω => Complex.exp (Complex.I * ((S ω + c * Y ω : ℝ) : ℂ))) P :=
    integrable_phase_LIP05122 P _ (hS.add (measurable_const.mul hY))
  rw [← integral_sub hI1 hI2, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hXY.abs.const_mul |c|) (ae_of_all _ fun ω => ?_)
  have h := exp_sub_le_LIP05122 (S ω + c * X ω) (S ω + c * Y ω)
  have h2 : |(S ω + c * X ω) - (S ω + c * Y ω)| = |c| * |X ω - Y ω| := by
    rw [show (S ω + c * X ω) - (S ω + c * Y ω) = c * (X ω - Y ω) by ring, abs_mul]
  rw [h2] at h
  exact h

/-- Splitting an `L¹` norm: if `E - F = A + D` with `A`, `D` integrable, then
`∫|E - F| ≤ ∫|A| + ∫|D|`. -/
lemma abs_split_LIP05122 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E F A D : Ω → ℝ) (hA : Integrable A P) (hD : Integrable D P)
    (h : ∀ ω, E ω - F ω = A ω + D ω) :
    ∫ ω, |E ω - F ω| ∂P ≤ ∫ ω, |A ω| ∂P + ∫ ω, |D ω| ∂P := by
  have hEF : Integrable (fun ω => E ω - F ω) P :=
    (hA.add hD).congr (ae_of_all _ fun ω => (h ω).symm)
  rw [← integral_add hA.abs hD.abs]
  refine integral_mono hEF.abs (hA.abs.add hD.abs) fun ω => ?_
  show |E ω - F ω| ≤ |A ω| + |D ω|
  rw [h ω]
  exact abs_add_le _ _

/-- The pair sum `A_N(F) = N⁻¹ ∑_{i<j} F(x i, x j)` is integrable under the product law, and its
`L¹` norm is at most `(1/√2) ‖F‖₂`, by `LIP051.10`. -/
lemma abs_pairSum_LIP05122 {d : ℕ} {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (F : DGPS.Torus d → DGPS.Torus d → ℝ)
    (hF : Measurable (fun p : DGPS.Torus d × DGPS.Torus d => F p.1 p.2))
    (hsymm : ∀ x y, F x y = F y x)
    (hL2 : MemLp (fun p : DGPS.Torus d × DGPS.Torus d => F p.1 p.2) 2 (μ.prod μ))
    (hcent : ∀ᵐ y ∂μ, ∫ x, F x y ∂μ = 0) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (pairSumLIP05121 N F) (Measure.pi fun _ : Fin N => μ) ∧
      ∫ x, |pairSumLIP05121 N F x| ∂(Measure.pi fun _ : Fin N => μ)
        ≤ 1 / Real.sqrt 2
          * (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d => F p.1 p.2) 2 (μ.prod μ)).toReal := by
  have h10 := lip051_10_exact_u_statistic_l2_norm μ F hF hsymm hL2 hcent N hN
  obtain ⟨-, ⟨hAm, -⟩, hle⟩ := h10
  have hAeq : pairSumLIP05121 N F = fun x : Fin N → DGPS.Torus d =>
      (N : ℝ)⁻¹ * ∑ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2), F (x p.1) (x p.2) := by
    funext x
    unfold pairSumLIP05121
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hAeq]
  refine ⟨hAm.integrable (by norm_num), ?_⟩
  simp only [← Real.norm_eq_abs]
  rw [integral_norm_eq_lintegral_enorm hAm.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm hAm.aestronglyMeasurable]
  refine le_of_le_of_eq (ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL2.eLpNorm_ne_top) hle) ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- LIP051.22: characteristic-function error estimate, sample side and limit side. See the
module docstring, R5 notes. -/
theorem lip051_22_characteristic_function_error_estimate {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m R : ℕ} (_hm : 1 ≤ m) (_hRm : m ≤ R) (a : Fin m → ℝ) (t : ℝ) :
    (∀ N : ℕ, 1 ≤ N →
      ‖(∫ x : Fin N → DGPS.Torus d,
            Complex.exp (Complex.I * ((∑ k : Fin m, a k * zLIP05121 N f (k.val + 1) x
              + t * energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x : ℝ) : ℂ))
              ∂(Measure.pi fun _ : Fin N => μ))
        - (∫ x : Fin N → DGPS.Torus d,
            Complex.exp (Complex.I * ((∑ k : Fin m, a k * zLIP05121 N f (k.val + 1) x
              + t * fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x : ℝ) : ℂ))
              ∂(Measure.pi fun _ : Fin N => μ))‖
        ≤ |t| / Real.sqrt 2 * (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
              tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal
          + |t| * ∫ x : Fin N → DGPS.Torus d,
              |diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x|
                ∂(Measure.pi fun _ : Fin N => μ)) ∧
    (∀ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 →
      Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
        atTop (𝓝 0) →
      ∀ Q' : (ℕ → ℝ) → ℝ, Measurable Q' → Q' =ᵐ[gam_LIP05144] QT →
        ‖(∫ z : ℕ → ℝ, Complex.exp (Complex.I * ((∑ k : Fin m, a k * z (k.val + 1)
              + t * ((Q' z + dK_LIP05145 μ W) / 2) : ℝ) : ℂ)) ∂gam_LIP05144)
          - (∫ z : ℕ → ℝ, Complex.exp (Complex.I * ((∑ k : Fin m, a k * z (k.val + 1)
              + t * ((wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
                + dK_LIP05145 μ W) / 2) : ℝ) : ℂ)) ∂gam_LIP05144)‖
        ≤ |t| / Real.sqrt 2 * (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
              tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal) := by
  have hKm :Measurable (Function.uncurry (centeredKernelOf_LIP05103 μ W)) :=
    (lip051_03_centering_integrability_original_kernel hWc hs hM hb).1
  have hKs : ∀ x y, centeredKernelOf_LIP05103 μ W x y = centeredKernelOf_LIP05103 μ W y x :=
    kernel_symm_LIP05103 hs
  have hKm' : Measurable (fun p : DGPS.Torus d × DGPS.Torus d =>
      centeredKernelOf_LIP05103 μ W p.1 p.2) := hKm
  obtain ⟨-, -, -, -, hTL2, -, -, -, hTC⟩ :=
    lip051_34_positive_spectral_sections_tails hWc hs hM hb e he0 f hfm hfe
  have hsecm : Measurable (fun p : DGPS.Torus d × DGPS.Torus d =>
      kSecLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) := by
    unfold kSecLIP05121
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (measurable_const.mul ((hfm i).comp measurable_fst)).mul ((hfm j).comp measurable_snd)
  have hFm : Measurable (fun p : DGPS.Torus d × DGPS.Torus d =>
      tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) :=
    hKm.sub hsecm
  have hfL2 : ∀ j, 1 ≤ j → MemLp (f j) 2 μ := fun j _ =>
    MemLp.ae_eq (hfe j).symm (Lp.memLp (e j))
  have hon : ∀ i j, 1 ≤ i → 1 ≤ j → ∫ x, f i x * f j x ∂μ = if i = j then 1 else 0 := by
    intro i j _ _
    have hij := (orthonormal_iff_ite.mp e.orthonormal) i j
    rw [L2.inner_def] at hij
    rw [← hij]
    refine integral_congr_ae ?_
    filter_upwards [hfe i, hfe j] with x hi hj
    rw [hi, hj]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hDint : ∀ N : ℕ, Integrable (diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N)
      (Measure.pi fun _ : Fin N => μ) := by
    intro N
    have h13 := (lip051_13_fixed_rank_diagonal_correction μ W hWc hb f hfL2 hon R).1 N
    refine h13.congr (ae_of_all _ fun x => ?_)
    simp only [diagRemLIP05121, tailLIP05121, kSecLIP05121, traceLIP05121, dKLIP05121,
      tIJ_LIP05121, kernelRankLIP05107, tIJ_LIP05107, one_div]
  refine ⟨fun N hN => ?_, fun QT hQT hlim Q' hQ'm hQ'eq => ?_⟩
  · -- Sample side.
    have hAbs := abs_pairSum_LIP05122 (tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R)
      hFm (tail_symm_LIP05121 (μ := μ) (centeredKernelOf_LIP05103 μ W) hKs f R) (hTL2 R)
      (hTC R).1 N hN
    have hA := hAbs.1
    have hD := hDint N
    have hzm : ∀ j : ℕ, Measurable (fun x : Fin N → DGPS.Torus d => zLIP05121 N f j x) := by
      intro j
      unfold zLIP05121
      exact measurable_const.mul
        (Finset.measurable_sum _ fun l _ => (hfm j).comp (measurable_pi_apply l))
    have hSm : Measurable (fun x : Fin N → DGPS.Torus d =>
        ∑ k : Fin m, a k * zLIP05121 N f (k.val + 1) x) :=
      Finset.measurable_sum _ fun k _ => measurable_const.mul (hzm _)
    have hUm : Measurable (fun x : Fin N → DGPS.Torus d =>
        energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x) := by
      unfold energyLIP05121
      have hkl : ∀ l k : Fin N, Measurable (fun x : Fin N → DGPS.Torus d =>
          centeredKernelOf_LIP05103 μ W (x l) (x k)) := fun l k => by
        have hpair : Measurable (fun x : Fin N → DGPS.Torus d => (x l, x k)) :=
          (measurable_pi_apply l).prodMk (measurable_pi_apply k)
        exact hKm'.comp hpair
      exact measurable_const.mul (Finset.measurable_sum _ fun l _ =>
        Finset.measurable_sum _ fun k _ => hkl l k)
    have hVm : Measurable (fun x : Fin N → DGPS.Torus d =>
        fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x) := by
      unfold fixedRankLIP05121
      refine measurable_const.mul (Measurable.add ?_ measurable_const)
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ?_
      exact ((hzm i).mul (hzm j)).sub measurable_const
    have hdec : ∀ x : Fin N → DGPS.Torus d,
        energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x
          - fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x
          = pairSumLIP05121 N (tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R) x
            + diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x := by
      intro x
      have h21 := lip051_21_exact_empirical_energy_decomposition (μ := μ) hs f R N x
      linarith
    have hXY : Integrable (fun x : Fin N → DGPS.Torus d =>
        energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x
          - fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x)
        (Measure.pi fun _ : Fin N => μ) := by
      refine (hA.add hD).congr (ae_of_all _ fun x => ?_)
      exact (hdec x).symm
    have hbound := charDiff_LIP05122 (Measure.pi fun _ : Fin N => μ)
      (fun x => ∑ k : Fin m, a k * zLIP05121 N f (k.val + 1) x)
      (fun x => energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x)
      (fun x => fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x)
      hSm hUm hVm hXY t
    have hsplit := abs_split_LIP05122 (Measure.pi fun _ : Fin N => μ)
      (fun x => energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x)
      (fun x => fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x)
      (pairSumLIP05121 N (tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R))
      (diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N) hA hD hdec
    calc _ ≤ |t| * ∫ x : Fin N → DGPS.Torus d,
          |energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x
            - fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x|
            ∂(Measure.pi fun _ : Fin N => μ) := hbound
      _ ≤ |t| * ((1 / Real.sqrt 2 * (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
              tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal)
            + ∫ x : Fin N → DGPS.Torus d,
              |diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x|
                ∂(Measure.pi fun _ : Fin N => μ)) :=
          mul_le_mul_of_nonneg_left (hsplit.trans (by linarith [hAbs.2])) (abs_nonneg t)
      _ = |t| / Real.sqrt 2 * (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
              tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal
            + |t| * ∫ x : Fin N → DGPS.Torus d,
              |diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x|
                ∂(Measure.pi fun _ : Fin N => μ) := by
          ring
  · -- Limit side.
    obtain ⟨-, -, hcl⟩ := lip051_17_l2_wick_limit hWc hs hM hb e he0 f hfm hfe
    obtain ⟨-, htail, -⟩ := hcl QT hQT hlim
    have hmem := (lip051_44_cauchy_wick_sections_existence_limit hWc hs hM hb e he0 f hfm hfe).1
    have hwick : ∀ R' : ℕ, Measurable (fun z : ℕ → ℝ =>
        wickQuad_LIP05116 (Finset.Icc 1 R') (coefT_LIP05134 μ W f) z) := by
      intro R'
      unfold wickQuad_LIP05116
      exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
        measurable_const.mul (((measurable_pi_apply i).mul (measurable_pi_apply j)).sub measurable_const)
    have hS : Measurable (fun z : ℕ → ℝ => ∑ k : Fin m, a k * z (k.val + 1)) :=
      Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_pi_apply _)
    have hX : Measurable (fun z : ℕ → ℝ => (Q' z + dK_LIP05145 μ W) / 2) :=
      (hQ'm.add_const _).div_const _
    have hY : Measurable (fun z : ℕ → ℝ =>
        (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2) :=
      ((hwick R).add_const _).div_const _
    have hQ'mem : MemLp Q' 2 gam_LIP05144 := MemLp.ae_eq hQ'eq.symm hQT
    have hG : MemLp (fun z : ℕ → ℝ =>
        QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
      hQT.sub (hmem R)
    have hG' : MemLp (fun z : ℕ → ℝ =>
        Q' z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
      hQ'mem.sub (hmem R)
    have hXYi : Integrable (fun z : ℕ → ℝ =>
        (Q' z + dK_LIP05145 μ W) / 2
          - (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2)
        gam_LIP05144 := by
      refine ((hG'.integrable (by norm_num)).div_const 2).congr (ae_of_all _ fun z => ?_)
      dsimp only
      ring
    have hτeq : (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
          tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal
        = (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal := rfl
    have hτ0 : 0 ≤ (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal :=
      ENNReal.toReal_nonneg
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h2 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
      field_simp
      linarith [hs2]
    have hLb : lpNorm (fun z : ℕ → ℝ =>
        QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144
        ≤ Real.sqrt 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal := by
      have hL0 : 0 ≤ lpNorm (fun z : ℕ → ℝ =>
          QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
        lpNorm_nonneg
      have hsq : lpNorm (fun z : ℕ → ℝ =>
          QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2
          = (Real.sqrt 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) ^ 2 := by
        rw [htail R, mul_pow, hsq2]
      nlinarith [mul_nonneg hs0 hτ0, hsq, hL0]
    have hI : ∫ z : ℕ → ℝ, |(Q' z + dK_LIP05145 μ W) / 2
          - (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2|
          ∂gam_LIP05144
        ≤ 1 / Real.sqrt 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal := by
      have hpt : ∫ z : ℕ → ℝ, |(Q' z + dK_LIP05145 μ W) / 2
            - (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2|
            ∂gam_LIP05144
          = 1 / 2 * ∫ z : ℕ → ℝ, |QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z|
            ∂gam_LIP05144 := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hQ'eq] with z hz
        rw [hz, show (QT z + dK_LIP05145 μ W) / 2
              - (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2
              = 1 / 2 * (QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) by ring,
          abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have hL1 : ∫ z : ℕ → ℝ, |QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z|
            ∂gam_LIP05144
          ≤ lpNorm (fun z : ℕ → ℝ =>
              QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 := by
        simp only [← Real.norm_eq_abs]
        rw [integral_norm_eq_lintegral_enorm hG.aestronglyMeasurable,
          ← eLpNorm_one_eq_lintegral_enorm hG.aestronglyMeasurable]
        exact ENNReal.toReal_mono hG.eLpNorm_ne_top
          (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ENNReal) ≤ 2))
      rw [hpt, h2]
      linarith [hL1, hLb]
    rw [hτeq]
    calc _ ≤ |t| * ∫ z : ℕ → ℝ, |(Q' z + dK_LIP05145 μ W) / 2
            - (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z + dK_LIP05145 μ W) / 2|
            ∂gam_LIP05144 :=
          charDiff_LIP05122 gam_LIP05144 (fun z : ℕ → ℝ => ∑ k : Fin m, a k * z (k.val + 1))
            (fun z => (Q' z + dK_LIP05145 μ W) / 2)
            (fun z => (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
              + dK_LIP05145 μ W) / 2)
            hS hX hY hXYi t
      _ ≤ |t| * (1 / Real.sqrt 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) :=
          mul_le_mul_of_nonneg_left hI (abs_nonneg t)
      _ = |t| / Real.sqrt 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal := by
          ring
end DGPS.Frontier.LIP051
