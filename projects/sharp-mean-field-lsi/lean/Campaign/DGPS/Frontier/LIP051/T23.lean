import DGPS.Frontier.LIP051.T06
import DGPS.Frontier.LIP051.T13
import DGPS.Frontier.LIP051.T17
import DGPS.Frontier.LIP051.T20
import DGPS.Frontier.LIP051.T22

/-!
# LIP051.23: Pass to infinite rank

Task id `LIP051.23`, title "Pass to infinite rank" (node LIP051, "Joint Gaussian and quadratic
fluctuation limit", leaf formalization, verification V1).
Dependencies: LIP051.06 (file T06), LIP051.20 (file T20), LIP051.22 (file T22), together with the
diagonal correction LIP051.13 (file T13), the Wick limit LIP051.17 (file T17), and the verified
Lévy and continuous-mapping theorems of Mathlib.
Source: `frontier_decomposition_20261024/nodes/LIP051.md`, the `LIP051.23` statement and proof.

## Provides

* `DGPS.Frontier.LIP051.lip051_23_pass_infinite_rank`: main statement. For a probability measure
  `μ` on the torus `DGPS.Torus d`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, measurable
  representatives `f j` of the classes `e j`, a bounded continuous symmetric kernel `W`, and a
  fixed `m ≥ 1`: an `L²` Wick quadratic limit `Q_T` exists on `ℕ → ℝ` for the law
  `Measure.infinitePi (fun _ => gaussianReal 0 1)`, and for every measurable version `Q'` of it the
  vectors `(Z_{N,1}, …, Z_{N,m}, U_N)` under `Measure.pi (fun _ => μ)` converge in distribution to
  `(z_1, …, z_m, (Q' + d_K)/2)` under that Gaussian law.
* `DGPS.Frontier.LIP051.liftLIP05123`: embedding of `ℝ^m × ℝ` into `ℝ^(m+1)` (last coordinate last).
* `DGPS.Frontier.LIP051.projLIP05123`: the inverse projection `ℝ^(m+1) → ℝ^m × ℝ`.
* `DGPS.Frontier.LIP051.continuous_lift_LIP05123`, `DGPS.Frontier.LIP051.continuous_proj_LIP05123`:
  continuity of the two maps.
* `DGPS.Frontier.LIP051.proj_lift_LIP05123`: the projection undoes the embedding.
* `DGPS.Frontier.LIP051.inner_lift_LIP05123`: the inner product of an embedded pair with a vector.
* `DGPS.Frontier.LIP051.sum_Icc_fin_LIP05123`: a sum over `Finset.Icc 1 R` is a sum over `Fin R`
  at the shifted index `a + 1`.
* `DGPS.Frontier.LIP051.pow_neg_half_LIP05123`: `N ^ (-1/2) = (√N)⁻¹` for real powers.
* `DGPS.Frontier.LIP051.feature_eq_LIP05123`: the feature sum of LIP051.20 equals the normalised
  sum `Z_{N,j+1}` of LIP051.21.
* `DGPS.Frontier.LIP051.fixed_eq_LIP05123`, `DGPS.Frontier.LIP051.wick_eq_LIP05123`,
  `DGPS.Frontier.LIP051.tail_eq_LIP05123`, `DGPS.Frontier.LIP051.diag_eq_LIP05123`: index and
  rewriting identifications between the LIP051.06, .07, .13, .20, .21, .22 and .34 declarations.
* `DGPS.Frontier.LIP051.limit_eq_LIP05123`: the fixed-rank limit written as `(Q_R + d_K)/2`.
* `DGPS.Frontier.LIP051.measurable_zLIP05123`, `DGPS.Frontier.LIP051.measurable_energy_LIP05123`,
  `DGPS.Frontier.LIP051.measurable_pair_LIP05123`: measurability of the normalised sums, the energy
  and the pair `(Z, U)`.
* `DGPS.Frontier.LIP051.charFun_map_LIP05123`: characteristic function of a pushforward as an
  integral over the sample space.
* `DGPS.Frontier.LIP051.tendsto_fixed_LIP05123`: characteristic functions at fixed rank converge.
* `DGPS.Frontier.LIP051.tendsto_full_LIP05123`: characteristic functions of the full vector converge
  to those of the Gaussian limit, by the rank-truncation estimate of LIP051.22.

## R5 notes

1. Frozen statement and target. The sample spaces are `Fin N → DGPS.Torus d` with laws
   `Measure.pi (fun _ => μ)`, and the limit law is `Measure.infinitePi (fun _ => gaussianReal 0 1)`
   on `ℕ → ℝ`, as in LIP051.22. The joint vector is the pair
   `(toLp (Z_{N,1}, …, Z_{N,m}), U_N)` in `EuclideanSpace ℝ (Fin m) × ℝ`; the limit is
   `(toLp (z_1, …, z_m), (Q' + d_K)/2)`. This pairing encodes the specification's vector.
2. Positive modes. The coordinate `k : Fin m` (the specification's `Z_{N,k+1}`) uses the basis index
   `(k : ℕ) + 1`. The zero mode `e 0 = 1` never occurs in the statement, so the defect
   `Z_{N,0} = √N` is not quantified over. The Wick coefficients use the indices `a + 1`, `b + 1`
   for `a, b : Fin R`, which is the same as the `Finset.Icc 1 R` sums of the specification.
3. Hypotheses on `μ` and `e`. `μ` is a probability measure on `DGPS.Torus d` (`IsProbabilityMeasure`);
   `e` is a real Hilbert basis of `L²(μ)` with `e 0 = Lp.const 2 μ 1`. These are the hypotheses of
   LIP051.17 and LIP051.22. The specification's `e_0 = 1` is used only to exclude the mode zero.
4. Kernel hypotheses. `W` is continuous (`Continuous (Function.uncurry W)`), symmetric (`hs`), and
   bounded by `M ≥ 0` (`hb`). They are exactly the hypotheses of LIP051.17 and LIP051.22, which carry
   the specification's continuity and boundedness of `W`. The original centered kernel
   `centeredKernelOf_LIP05103 μ W` (file T03) is used throughout, including on the diagonal. The
   diagonal constant `d_K` is `dK_LIP05145 μ W = ∫ K(x,x) dμ`, the Bochner integral of the pointwise
   diagonal, not an `L²` class.
5. Representatives. `f j` are measurable functions with `f j =ᵐ[μ] e j` (`hfm`, `hfe`). The
   statement does not depend on the choice of representatives, because the sample laws and the
   coefficients are unchanged by null modifications.
6. Rank `m`. The hypothesis `1 ≤ m` is the specification's "fixed `m ≥ 1`". The rank `R` is internal
   to the proof (chosen with `m ≤ R` depending on the tolerance) and does not appear in the statement.
7. Wick limit (non-literal reading, strengthening). The specification says "`Q_T` is the `L²` Wick
   quadratic limit". The statement asserts existence of `QT` in `L²(γ₀)` with the `L²` convergence of
   the Wick sections (LIP051.17, conjunct 1), and then the convergence for every measurable version
   `Q'` of `QT`. This is an added existence conclusion, not an added hypothesis, and it makes the
   statement non-vacuous. The specification's `Q_T` is only determined up to a `γ₀`-null set; the
   quantifier over measurable versions makes the target law well defined.
8. Convergence in distribution is Mathlib's `TendstoInDistribution` along `atTop` on `ℕ`, with
   `Measure.map` laws and the weak topology on probability measures. The proof passes to
   `EuclideanSpace ℝ (Fin (m + 1))`, which is an inner-product space and so admits the Lévy
   characteristic-function criterion, and then maps back by the continuous projection
   `projLIP05123`. This lift changes the presentation, not the statement.
9. Normalisation at `N = 0`. The normalisation `(√N)⁻¹` is zero at `N = 0`, and the energy
   `(2N)⁻¹` is zero at `N = 0`. The convergence is along `atTop`, so these values do not affect the
   limit.
10. Characteristic-function bound. The estimate used is the LIP051.22 bound, which holds for `N ≥ 1`
    and is combined with the rank-truncation convergence from LIP051.06 and the diagonal `L¹`
    convergence from LIP051.13. The rank is chosen before the particle number tends to infinity, as in
    the specification's proof.
11. Signature of the specification's `U_N`. `U_N = (2N)⁻¹ ∑_{l,k} K(X_l, X_k)` is
    `energyLIP05121 (centeredKernelOf_LIP05103 μ W) N`, with the same `(2N)⁻¹` normalisation.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

variable {d : ℕ}

/-- The embedding `ℝ^m × ℝ → ℝ^(m+1)`, placing the first factor in the first `m` coordinates and
the second factor in the last coordinate. -/
noncomputable def liftLIP05123 (m : ℕ) (p : EuclideanSpace ℝ (Fin m) × ℝ) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) (fun k : Fin m => p.1 k) p.2)

/-- The projection `ℝ^(m+1) → ℝ^m × ℝ`, the inverse of `liftLIP05123` on pairs. -/
noncomputable def projLIP05123 (m : ℕ) (w : EuclideanSpace ℝ (Fin (m + 1))) :
    EuclideanSpace ℝ (Fin m) × ℝ :=
  (WithLp.toLp 2 (fun k : Fin m => w (Fin.castSucc k)), w (Fin.last m))

lemma continuous_lift_LIP05123 (m : ℕ) : Continuous (liftLIP05123 m) := by
  unfold liftLIP05123
  fun_prop

lemma continuous_proj_LIP05123 (m : ℕ) : Continuous (projLIP05123 m) := by
  unfold projLIP05123
  fun_prop

lemma proj_lift_LIP05123 (m : ℕ) (p : EuclideanSpace ℝ (Fin m) × ℝ) :
    projLIP05123 m (liftLIP05123 m p) = p := by
  simp [projLIP05123, liftLIP05123]

lemma inner_lift_LIP05123 (m : ℕ) (p : EuclideanSpace ℝ (Fin m) × ℝ)
    (t : EuclideanSpace ℝ (Fin (m + 1))) :
    ∑ k : Fin (m + 1), liftLIP05123 m p k * t k
      = ∑ k : Fin m, t (Fin.castSucc k) * p.1 k + t (Fin.last m) * p.2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [liftLIP05123, Fin.snoc_castSucc, Fin.snoc_last, PiLp.toLp_apply]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => mul_comm _ _) (mul_comm _ _)

lemma sum_Icc_fin_LIP05123 (h : ℕ → ℝ) (R : ℕ) :
    ∑ i ∈ Finset.Icc 1 R, h i = ∑ a : Fin R, h ((a : ℕ) + 1) := by
  induction R with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega), ih, Fin.sum_univ_castSucc]
    simp

lemma pow_neg_half_LIP05123 (N : ℕ) : (N : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (N : ℝ))⁻¹ := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg N)]

lemma feature_eq_LIP05123 (f : ℕ → DGPS.Torus d → ℝ) (N : ℕ) (x : Fin N → DGPS.Torus d)
    (j : ℕ) : feature_sum_LIP05120 f N x j = zLIP05121 N f (j + 1) x := by
  unfold feature_sum_LIP05120 zLIP05121
  rw [pow_neg_half_LIP05123]

lemma fixed_eq_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) :
    (1 / 2 : ℝ) * ((∑ a : Fin R, ∑ b : Fin R,
        tIJ_LIP05107 μ K f ((a : ℕ) + 1) ((b : ℕ) + 1) *
          (feature_sum_LIP05120 f N x (a : ℕ) * feature_sum_LIP05120 f N x (b : ℕ)
            - (if a = b then (1 : ℝ) else 0)))
        + ∫ y, K y y ∂μ) = fixedRankLIP05121 μ K f R N x := by
  unfold fixedRankLIP05121 dKLIP05121
  simp only [sum_Icc_fin_LIP05123, feature_eq_LIP05123]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [tIJ_LIP05107, tIJ_LIP05121, Fin.ext_iff]

lemma wick_eq_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (z : ℕ → ℝ) :
    wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
      = ∑ a : Fin R, ∑ b : Fin R,
          tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) f ((a : ℕ) + 1) ((b : ℕ) + 1) *
            (z ((a : ℕ) + 1) * z ((b : ℕ) + 1) - (if a = b then (1 : ℝ) else 0)) := by
  unfold wickQuad_LIP05116
  simp only [sum_Icc_fin_LIP05123]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [coefT_LIP05134, tIJ_LIP05107, Fin.ext_iff]

lemma limit_eq_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (z : ℕ → ℝ) :
    (1 / 2 : ℝ) * ((∑ a : Fin R, ∑ b : Fin R,
        tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) f ((a : ℕ) + 1) ((b : ℕ) + 1) *
          (z ((a : ℕ) + 1) * z ((b : ℕ) + 1) - (if a = b then (1 : ℝ) else 0)))
        + ∫ y, centeredKernelOf_LIP05103 μ W y y ∂μ)
      = (wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
          + dK_LIP05145 μ W) / 2 := by
  rw [wick_eq_LIP05123, dK_LIP05145]
  ring

lemma diag_eq_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) :
    diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x
      = (1 / (2 * (N : ℝ))) * (∑ l : Fin N,
            (centeredKernelOf_LIP05103 μ W (x l) (x l)
              - kernelRankLIP05107 μ (centeredKernelOf_LIP05103 μ W) f R (x l) (x l)))
        - (1 / 2 : ℝ) * ((∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ)
            - ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05107 μ (centeredKernelOf_LIP05103 μ W) f i i) := by
  simp only [diagRemLIP05121, tailLIP05121, kSecLIP05121, traceLIP05121, dKLIP05121,
    kernelRankLIP05107, tIJ_LIP05121, tIJ_LIP05107, one_div]

lemma tail_eq_LIP05123 {μ : Measure (DGPS.Torus d)} (W : DGPS.Torus d → DGPS.Torus d → ℝ)
    (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ) :
    tailKR_LIP05134 μ W f R
      = fun p => tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2 := by
  funext p
  simp only [tailKR_LIP05134, sectionKR_LIP05134, tailLIP05121, kSecLIP05121,
    coefT_LIP05134, tIJ_LIP05121]

lemma measurable_zLIP05123 (N : ℕ) (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (j : ℕ) : Measurable (fun x : Fin N → DGPS.Torus d => zLIP05121 N f j x) := by
  unfold zLIP05121
  exact measurable_const.mul
    (Finset.measurable_sum _ fun l _ => (hfm j).comp (measurable_pi_apply l))

lemma measurable_energy_LIP05123 (N : ℕ) (K : DGPS.Torus d → DGPS.Torus d → ℝ)
    (hK : Measurable (Function.uncurry K)) :
    Measurable (fun x : Fin N → DGPS.Torus d => energyLIP05121 K N x) := by
  unfold energyLIP05121
  refine measurable_const.mul (Finset.measurable_sum _ fun l _ => Finset.measurable_sum _ fun k _ => ?_)
  have hpair : Measurable (fun x : Fin N → DGPS.Torus d => (x l, x k)) :=
    (measurable_pi_apply l).prodMk (measurable_pi_apply k)
  exact hK.comp hpair

lemma measurable_pair_LIP05123 (m N : ℕ) (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (hK : Measurable (Function.uncurry K)) :
    Measurable (fun x : Fin N → DGPS.Torus d =>
      ((WithLp.toLp 2 (fun k : Fin m => zLIP05121 N f ((k : ℕ) + 1) x) :
          EuclideanSpace ℝ (Fin m)), energyLIP05121 K N x)) := by
  refine Measurable.prodMk ?_ (measurable_energy_LIP05123 N K hK)
  have hz : Measurable (fun x : Fin N → DGPS.Torus d => fun k : Fin m => zLIP05121 N f ((k : ℕ) + 1) x) :=
    measurable_pi_iff.mpr fun k => measurable_zLIP05123 N f hfm _
  exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp hz

lemma charFun_map_LIP05123 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin (m + 1))) (hX : AEMeasurable X P)
    (t : EuclideanSpace ℝ (Fin (m + 1))) :
    charFun (P.map X) t
      = ∫ ω, Complex.exp (Complex.I * ((∑ k : Fin (m + 1), X ω k * t k : ℝ) : ℂ)) ∂P := by
  have hc : Continuous fun w : EuclideanSpace ℝ (Fin (m + 1)) =>
      Complex.exp (((inner ℝ w t : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  have hin : ∀ w : EuclideanSpace ℝ (Fin (m + 1)),
      (inner ℝ w t : ℝ) = ∑ k : Fin (m + 1), w k * t k := by
    intro w
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [charFun_apply, integral_map hX hc.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [hin (X ω)]
  congr 1
  ring

lemma charFun_lift_LIP05123 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin m) × ℝ) (hX : AEMeasurable (liftLIP05123 m ∘ X) P)
    (t : EuclideanSpace ℝ (Fin (m + 1))) :
    charFun (P.map (liftLIP05123 m ∘ X)) t
      = ∫ ω, Complex.exp (Complex.I * ((∑ k : Fin m, t (Fin.castSucc k) * (X ω).1 k
          + t (Fin.last m) * (X ω).2 : ℝ) : ℂ)) ∂P := by
  rw [charFun_map_LIP05123 P m (liftLIP05123 m ∘ X) hX t]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Function.comp_apply, inner_lift_LIP05123]

lemma charFun_of_pointwise_LIP05123 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m : ℕ)
    (X : Ω → EuclideanSpace ℝ (Fin m) × ℝ) (hX : AEMeasurable (liftLIP05123 m ∘ X) P)
    (a : Fin m → ℝ) (s : ℝ) (G : Ω → ℝ)
    (hG : ∀ ω, ∑ k : Fin m, a k * (X ω).1 k + s * (X ω).2 = G ω) :
    charFun (P.map (liftLIP05123 m ∘ X))
        (liftLIP05123 m ((WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), s))
      = ∫ ω, Complex.exp (Complex.I * (G ω : ℂ)) ∂P := by
  have h1 : ∀ k : Fin m, liftLIP05123 m ((WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), s)
      (Fin.castSucc k) = a k := by
    intro k
    simp [liftLIP05123, Fin.snoc_castSucc]
  have h2 : liftLIP05123 m ((WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), s) (Fin.last m) = s := by
    simp [liftLIP05123]
  rw [charFun_lift_LIP05123 P m X hX]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [h1, h2, hG]

/-- Forward direction of the Lévy criterion on the level of integrals: convergence in distribution
gives convergence of the integrals of `exp (i (∑ a_k X_k + s X_{m+1}))`. -/
lemma tendsto_of_tendstoInDistribution_LIP05123 {Ω' : Type*} [MeasurableSpace Ω'] {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] (P : (N : ℕ) → Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (m : ℕ)
    (X : (N : ℕ) → Ω N → EuclideanSpace ℝ (Fin m) × ℝ) (Y : Ω' → EuclideanSpace ℝ (Fin m) × ℝ)
    (h : TendstoInDistribution X atTop Y P P') (a : Fin m → ℝ) (s : ℝ)
    (Φ : ℕ → ℂ) (Ψ : ℂ)
    (hΦ : ∀ N, Φ N = ∫ ω, Complex.exp (Complex.I *
      ((∑ k : Fin m, a k * (X N ω).1 k + s * (X N ω).2 : ℝ) : ℂ)) ∂(P N))
    (hΨ : Ψ = ∫ ω, Complex.exp (Complex.I *
      ((∑ k : Fin m, a k * (Y ω).1 k + s * (Y ω).2 : ℝ) : ℂ)) ∂P') :
    Tendsto Φ atTop (𝓝 Ψ) := by
  have hXl : ∀ N, AEMeasurable (liftLIP05123 m ∘ X N) (P N) := fun N =>
    (continuous_lift_LIP05123 m).measurable.comp_aemeasurable (h.forall_aemeasurable N)
  have hYl : AEMeasurable (liftLIP05123 m ∘ Y) P' :=
    (continuous_lift_LIP05123 m).measurable.comp_aemeasurable h.aemeasurable_limit
  have hc := (h.continuous_comp (continuous_lift_LIP05123 m)).tendsto_charFun
    (liftLIP05123 m ((WithLp.toLp 2 a : EuclideanSpace ℝ (Fin m)), s))
  rw [charFun_of_pointwise_LIP05123 P' m Y hYl a s
    (fun ω => ∑ k : Fin m, a k * (Y ω).1 k + s * (Y ω).2) (fun ω => rfl)] at hc
  subst hΨ
  refine Filter.Tendsto.congr (fun N => ?_) hc
  rw [hΦ N]
  exact charFun_of_pointwise_LIP05123 (P N) m (X N) (hXl N) a s
    (fun ω => ∑ k : Fin m, a k * (X N ω).1 k + s * (X N ω).2) (fun ω => rfl)

/-- Reverse direction of the Lévy criterion: convergence of the integrals of
`exp (i (∑ a_k X_k + s X_{m+1}))` for all `(a, s)` gives convergence in distribution. -/
lemma tendsto_dist_of_charFun_LIP05123 {Ω' : Type*} [MeasurableSpace Ω'] {Ω : ℕ → Type*}
    [∀ N, MeasurableSpace (Ω N)] (P : (N : ℕ) → Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
    (P' : Measure Ω') [IsProbabilityMeasure P'] (m : ℕ)
    (X : (N : ℕ) → Ω N → EuclideanSpace ℝ (Fin m) × ℝ) (Y : Ω' → EuclideanSpace ℝ (Fin m) × ℝ)
    (hX : ∀ N, AEMeasurable (X N) (P N)) (hY : AEMeasurable Y P')
    (h : ∀ (a : Fin m → ℝ) (s : ℝ), Tendsto (fun N => ∫ ω, Complex.exp (Complex.I *
        ((∑ k : Fin m, a k * (X N ω).1 k + s * (X N ω).2 : ℝ) : ℂ)) ∂(P N)) atTop
        (𝓝 (∫ ω, Complex.exp (Complex.I *
          ((∑ k : Fin m, a k * (Y ω).1 k + s * (Y ω).2 : ℝ) : ℂ)) ∂P'))) :
    TendstoInDistribution X atTop Y P P' := by
  have hXl : ∀ N, AEMeasurable (liftLIP05123 m ∘ X N) (P N) := fun N =>
    (continuous_lift_LIP05123 m).measurable.comp_aemeasurable (hX N)
  have hYl : AEMeasurable (liftLIP05123 m ∘ Y) P' :=
    (continuous_lift_LIP05123 m).measurable.comp_aemeasurable hY
  have hL : TendstoInDistribution (fun N => liftLIP05123 m ∘ X N) atTop
      (liftLIP05123 m ∘ Y) P P' := by
    refine TendstoInDistribution.of_tendsto_charFun hXl hYl fun t => ?_
    rw [charFun_lift_LIP05123 P' m Y hYl t]
    have h' := h (fun k => t (Fin.castSucc k)) (t (Fin.last m))
    exact Filter.Tendsto.congr (fun N => (charFun_lift_LIP05123 (P N) m (X N) (hXl N) t).symm) h'
  have hL' := hL.continuous_comp (continuous_proj_LIP05123 m)
  simpa only [Function.comp_def, proj_lift_LIP05123] using hL'

/-- The characteristic function of `(Z_{N,1}, …, Z_{N,m}, U_N)` at frequency `(a, s)` under `μ^N`. -/
noncomputable def phiLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (m : ℕ)
    (a : Fin m → ℝ) (s : ℝ) (N : ℕ) : ℂ :=
  ∫ x : Fin N → DGPS.Torus d, Complex.exp (Complex.I * ((∑ k : Fin m,
      a k * zLIP05121 N f (k.val + 1) x
        + s * energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x : ℝ) : ℂ))
    ∂(Measure.pi fun _ : Fin N => μ)

/-- The characteristic function of `(Z_{N,1}, …, Z_{N,m}, V_{N,R})` at frequency `(a, s)`. -/
noncomputable def phiFixLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R m : ℕ)
    (a : Fin m → ℝ) (s : ℝ) (N : ℕ) : ℂ :=
  ∫ x : Fin N → DGPS.Torus d, Complex.exp (Complex.I * ((∑ k : Fin m,
      a k * zLIP05121 N f (k.val + 1) x
        + s * fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x : ℝ) : ℂ))
    ∂(Measure.pi fun _ : Fin N => μ)

/-- The limit characteristic function at frequency `(a, s)` for the Gaussian law `γ₀`. -/
noncomputable def psiLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (m : ℕ) (a : Fin m → ℝ) (s : ℝ)
    (Q' : (ℕ → ℝ) → ℝ) : ℂ :=
  ∫ z : ℕ → ℝ, Complex.exp (Complex.I * ((∑ k : Fin m,
      a k * z (k.val + 1) + s * ((Q' z + dK_LIP05145 μ W) / 2) : ℝ) : ℂ)) ∂gam_LIP05144

/-- The limit characteristic function at frequency `(a, s)` with the Wick section `Q_R`. -/
noncomputable def psiFixLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R m : ℕ)
    (a : Fin m → ℝ) (s : ℝ) : ℂ :=
  ∫ z : ℕ → ℝ, Complex.exp (Complex.I * ((∑ k : Fin m,
      a k * z (k.val + 1) + s * ((wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
        + dK_LIP05145 μ W) / 2) : ℝ) : ℂ)) ∂gam_LIP05144

/-- The `L²(μ × μ)` norm of the rank-`R` tail kernel. -/
noncomputable def tailNormLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ) : ℝ :=
  (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
    tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R p.1 p.2) 2 (μ.prod μ)).toReal

/-- The `L¹(μ^N)` norm of the rank-`R` diagonal remainder. -/
noncomputable def diagIntLIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R N : ℕ) : ℝ :=
  ∫ x : Fin N → DGPS.Torus d,
    |diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) f R N x| ∂(Measure.pi fun _ : Fin N => μ)

lemma tailNorm_nonneg_LIP05123 (μ : Measure (DGPS.Torus d)) [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ) :
    0 ≤ tailNormLIP05123 μ W f R :=
  ENNReal.toReal_nonneg

/-- Lemma A: at fixed rank, the characteristic functions converge (Lévy's criterion direction via
LIP051.20). -/
lemma tendsto_fixed_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m R : ℕ} (hm : 1 ≤ m) (hmR : m ≤ R) (a : Fin m → ℝ) (s : ℝ) :
    Tendsto (fun N => phiFixLIP05123 μ W f R m a s N) atTop
      (𝓝 (psiFixLIP05123 μ W f R m a s)) := by
  have hT := lip051_20_fixed_rank_joint_polynomial_limit μ e he0 f hfm hfe
    (centeredKernelOf_LIP05103 μ W) m R hm hmR
  refine tendsto_of_tendstoInDistribution_LIP05123 _ _ m _ _ hT a s _ _ (fun N => ?_) ?_
  · unfold phiFixLIP05123
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [fixed_eq_LIP05123 (μ := μ) (centeredKernelOf_LIP05103 μ W) f R N x]
    simp only [feature_eq_LIP05123]
  · unfold psiFixLIP05123
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [limit_eq_LIP05123 (μ := μ) W f R z]

/-- The fixed-rank approximation error of the sample characteristic function (LIP051.22). -/
lemma phi_bound_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m R : ℕ} (hm : 1 ≤ m) (hmR : m ≤ R) (a : Fin m → ℝ) (s : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖phiLIP05123 μ W f m a s N - phiFixLIP05123 μ W f R m a s N‖
      ≤ |s| / Real.sqrt 2 * tailNormLIP05123 μ W f R + |s| * diagIntLIP05123 μ W f R N :=
  (lip051_22_characteristic_function_error_estimate hWc hs hM hb e he0 f hfm hfe hm hmR a s).1 N hN

/-- The limit-side approximation error (LIP051.22). -/
lemma psi_bound_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m R : ℕ} (hm : 1 ≤ m) (hmR : m ≤ R) (a : Fin m → ℝ) (s : ℝ)
    (QT : (ℕ → ℝ) → ℝ) (hQT : MemLp QT 2 gam_LIP05144)
    (hlim : Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
      wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
      atTop (𝓝 0))
    (Q' : (ℕ → ℝ) → ℝ) (hQ'm : Measurable Q') (hQ'eq : Q' =ᵐ[gam_LIP05144] QT) :
    ‖psiLIP05123 μ W m a s Q' - psiFixLIP05123 μ W f R m a s‖
      ≤ |s| / Real.sqrt 2 * tailNormLIP05123 μ W f R :=
  (lip051_22_characteristic_function_error_estimate hWc hs hM hb e he0 f hfm hfe hm hmR a s).2
    QT hQT hlim Q' hQ'm hQ'eq

/-- Lemma B: the characteristic functions of the full vector converge to those of the limit. -/
lemma tendsto_full_LIP05123 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m : ℕ} (hm : 1 ≤ m) (QT : (ℕ → ℝ) → ℝ) (hQT : MemLp QT 2 gam_LIP05144)
    (hlim : Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
      wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
      atTop (𝓝 0))
    (Q' : (ℕ → ℝ) → ℝ) (hQ'm : Measurable Q') (hQ'eq : Q' =ᵐ[gam_LIP05144] QT)
    (a : Fin m → ℝ) (s : ℝ) :
    Tendsto (fun N => phiLIP05123 μ W f m a s N) atTop (𝓝 (psiLIP05123 μ W m a s Q')) := by
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
  have hDiag : ∀ R : ℕ, Tendsto (fun N => diagIntLIP05123 μ W f R N) atTop (𝓝 0) := by
    intro R
    refine Filter.Tendsto.congr (fun N => ?_)
      (lip051_13_fixed_rank_diagonal_correction μ W hWc hb f hfL2 hon R).2
    simp only [diagIntLIP05123, diag_eq_LIP05123]
  obtain ⟨-, -, hcl⟩ := lip051_17_l2_wick_limit hWc hs hM hb e he0 f hfm hfe
  obtain ⟨-, hsqT, -⟩ := hcl QT hQT hlim
  have hsq : ∀ R : ℕ, lpNorm (fun z : ℕ → ℝ =>
      QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2
        = 2 * tailNormLIP05123 μ W f R ^ 2 := by
    intro R
    have h := hsqT R
    rw [tail_eq_LIP05123] at h
    exact h
  have hlim2 : Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
      QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144)
      atTop (𝓝 0) := by
    refine Filter.Tendsto.congr (fun R => ?_) hlim
    exact lpNorm_sub_comm (fun z : ℕ → ℝ =>
      wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) QT 2 gam_LIP05144
  have htail : Tendsto (fun R : ℕ => tailNormLIP05123 μ W f R) atTop (𝓝 0) := by
    have hq : Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
        QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2 / 2)
        atTop (𝓝 0) := by
      have h := (hlim2.pow 2).div_const 2
      rwa [show ((0 : ℝ) ^ 2 / 2) = 0 by norm_num] at h
    have hs' := hq.sqrt
    rw [Real.sqrt_zero] at hs'
    refine Filter.Tendsto.congr (fun R => ?_) hs'
    try dsimp only
    rw [hsq R]
    have h2 : 2 * tailNormLIP05123 μ W f R ^ 2 / 2 = tailNormLIP05123 μ W f R ^ 2 := by ring
    rw [h2]
    exact Real.sqrt_sq (tailNorm_nonneg_LIP05123 μ W f R)
  have hC : Tendsto (fun R : ℕ => |s| / Real.sqrt 2 * tailNormLIP05123 μ W f R) atTop (𝓝 0) := by
    have h := htail.const_mul (|s| / Real.sqrt 2)
    rwa [mul_zero] at h
  have hDs : ∀ R : ℕ, Tendsto (fun N => |s| * diagIntLIP05123 μ W f R N) atTop (𝓝 0) := by
    intro R
    have h := (hDiag R).const_mul (|s|)
    rwa [mul_zero] at h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  obtain ⟨R, hRsmall, hRm⟩ :=
    ((hC.eventually (gt_mem_nhds hε4)).and (eventually_ge_atTop m)).exists
  have hRsmall' : |s| / Real.sqrt 2 * tailNormLIP05123 μ W f R < ε / 4 := hRsmall
  have hA := Metric.tendsto_nhds.mp
    (tendsto_fixed_LIP05123 W e he0 f hfm hfe hm hRm a s) (ε / 4) hε4
  have hD := (hDs R).eventually (gt_mem_nhds hε4)
  filter_upwards [hA, hD, eventually_ge_atTop 1] with N hAN hDN hN
  have hAN' : dist (phiFixLIP05123 μ W f R m a s N) (psiFixLIP05123 μ W f R m a s) < ε / 4 := hAN
  have hDN' : |s| * diagIntLIP05123 μ W f R N < ε / 4 := hDN
  show dist (phiLIP05123 μ W f m a s N) (psiLIP05123 μ W m a s Q') < ε
  have h1 := phi_bound_LIP05123 hWc hs hM hb e he0 f hfm hfe hm hRm a s N hN
  have h2 := psi_bound_LIP05123 hWc hs hM hb e he0 f hfm hfe hm hRm a s QT hQT hlim Q' hQ'm hQ'eq
  have h3 := dist_triangle4 (phiLIP05123 μ W f m a s N) (phiFixLIP05123 μ W f R m a s N)
    (psiFixLIP05123 μ W f R m a s) (psiLIP05123 μ W m a s Q')
  rw [dist_comm (psiFixLIP05123 μ W f R m a s) (psiLIP05123 μ W m a s Q')] at h3
  rw [← dist_eq_norm] at h1 h2
  linarith

/-- LIP051.23: pass to infinite rank. See the module docstring, R5 notes. -/
theorem lip051_23_pass_infinite_rank {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ))
    {m : ℕ} (hm : 1 ≤ m) :
    (∃ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 ∧
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0)) ∧
    (∀ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        ∀ Q' : (ℕ → ℝ) → ℝ, Measurable Q' → Q' =ᵐ[gam_LIP05144] QT →
        TendstoInDistribution
          (fun (N : ℕ) (x : Fin N → DGPS.Torus d) =>
            ((WithLp.toLp 2 (fun k : Fin m => zLIP05121 N f ((k : ℕ) + 1) x) :
                EuclideanSpace ℝ (Fin m)),
              energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x))
          atTop
          (fun z : ℕ → ℝ =>
            ((WithLp.toLp 2 (fun k : Fin m => z ((k : ℕ) + 1)) : EuclideanSpace ℝ (Fin m)),
              (Q' z + dK_LIP05145 μ W) / 2))
          (fun N : ℕ => Measure.pi fun _ : Fin N => μ)
          (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) := by
  refine ⟨(lip051_17_l2_wick_limit hWc hs hM hb e he0 f hfm hfe).1,
    fun QT hQT hlim Q' hQ'm hQ'eq => ?_⟩
  have hK : Measurable (Function.uncurry (centeredKernelOf_LIP05103 μ W)) :=
    (lip051_03_centering_integrability_original_kernel hWc hs hM hb).1
  have hXm : ∀ N : ℕ, Measurable (fun x : Fin N → DGPS.Torus d =>
      ((WithLp.toLp 2 (fun k : Fin m => zLIP05121 N f ((k : ℕ) + 1) x) :
          EuclideanSpace ℝ (Fin m)), energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x)) :=
    fun N => measurable_pair_LIP05123 m N f hfm (centeredKernelOf_LIP05103 μ W) hK
  have hYm : Measurable (fun z : ℕ → ℝ =>
      ((WithLp.toLp 2 (fun k : Fin m => z ((k : ℕ) + 1)) : EuclideanSpace ℝ (Fin m)),
        (Q' z + dK_LIP05145 μ W) / 2)) := by
    refine Measurable.prodMk ?_ ((hQ'm.add_const _).div_const 2)
    exact (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).measurable.comp
      (measurable_pi_iff.mpr fun k => measurable_pi_apply _)
  refine tendsto_dist_of_charFun_LIP05123 _ _ m _ _ (fun N => (hXm N).aemeasurable)
    hYm.aemeasurable (fun a s => ?_)
  exact tendsto_full_LIP05123 hWc hs hM hb e he0 f hfm hfe hm QT hQT hlim Q' hQ'm hQ'eq a s

end DGPS.Frontier.LIP051
