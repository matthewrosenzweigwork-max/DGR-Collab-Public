import DGPS.Frontier.LIP051.T44
import DGPS.Frontier.LIP051.T06

/-!
# LIP051.45: Exact Wick tail, mean, and representative

Task id `LIP051.45`, title "Exact Wick tail, mean, and representative" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category leaf formalization, verification V1).
Proved inputs: `LIP051.03` (`DGPS.Frontier.LIP051.T03`), `LIP051.06` (`DGPS.Frontier.LIP051.T06`),
`LIP051.16` (`DGPS.Frontier.LIP051.T16`) and `LIP051.44` (`DGPS.Frontier.LIP051.T44`).

Setting. The data `μ`, `W`, `e`, `f` and the coefficients `coefT_LIP05134 μ W f` are those of
`LIP051.06`. The reference law is `γ₀ = Measure.infinitePi (gaussianReal 0 1)` on `ℕ → ℝ`. The
Wick section of rank `R` is `Q_R z = wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z`.
The tail `K - K_R` is `tailKR_LIP05134 μ W f R`, and `d_K` is `dK_LIP05145 μ W`.

## Provides

* `DGPS.Frontier.LIP051.lip051_45_exact_wick_tail_mean_representative`: the main theorem. The
  `L²(γ₀)` limit of the Wick sections exists (conjunct 1). For every such limit `Q_T`, the mean of
  `Q_T` under `γ₀` is zero, the identity `‖Q_T - Q_R‖² = 2 ‖K - K_R‖²` holds for every rank `R`,
  and some measurable representative `Q'` of `Q_T` makes `(Q' + d_K) / 2` measurable and in
  `L²(γ₀)` (conjunct 2).
* `DGPS.Frontier.LIP051.dK_LIP05145`: the diagonal integral `d_K = ∫ K(x, x) dμ(x)` of the
  centered kernel `centeredKernelOf_LIP05103`, with the original diagonal retained.
* `DGPS.Frontier.LIP051.abs_integral_le_LIP05145`: the absolute value of the mean of an `L²`
  function under a probability measure is at most its `lpNorm`.
* `DGPS.Frontier.LIP051.lpNorm_sq_LIP05145`: the squared `lpNorm` equals the integral of the square.
* `DGPS.Frontier.LIP051.eq_LIP05145`: for `R ≤ S`, the squared `L²(γ₀)` distance of the Wick
  sections of ranks `R` and `S` is twice a finite partial sum of the tail coefficients.
* `DGPS.Frontier.LIP051.tendsto_range_LIP05145`: a summable series over `ℕ × ℕ` has the square
  partial sums over `range (S+1) ×ˢ range (S+1)` converging to its total.

## R5 notes

1. Hypotheses. The binders of the main theorem are exactly those of `LIP051.44` and `LIP051.06`:
   continuity of `uncurry W`, symmetry of `W`, `0 ≤ M` with `|W| ≤ M`, the Hilbert basis `e` with
   `e 0 = 1` in `L²(μ)`, and measurable representatives `f j =ᵐ[μ] e j`. No hypothesis is added.
   The probability measure instance on `μ` is the one already required by `LIP051.06`.
2. Positive modes. The sums run over `i, j ∈ {1,…,R}` (`Finset.Icc 1 R`), as in the
   specification and the positive-mode convention of `LIP051.06` (defect FD-002). The zero mode
   is never read. The finite sums over the square `range (S+1) ×ˢ range (S+1)` in the proof are
   only a bookkeeping device: their terms with a zero index vanish identically.
3. Limit. "The limit in `LIP051.44`" is read as an arbitrary `L²(γ₀)` function `Q_T` with
   `lpNorm (Q_R - Q_T) 2 γ₀ → 0`. Conjunct 1 records that such a function exists, which is the
   content of `LIP051.44` (conjunct 3) and is needed for the statement to be non-vacuous. The mean
   and tail identity are stated for every such `Q_T`; by the a.e. uniqueness in `LIP051.44`, they
   do not depend on the choice.
4. Tail identity orientation. The identity is written as `‖Q_T - Q_R‖² = 2 ‖K - K_R‖²`, with
   `Q_T - Q_R` as the difference of functions. The `L²` norm of `K - K_R` is the `eLpNorm`
   with respect to `μ.prod μ`, read through `.toReal`, as in `LIP051.06`.
5. Mean. The mean is `∫ Q_T dγ₀`, an integral under the probability measure `γ₀`. Its zero value
   follows from the zero mean of each finite Wick section (`LIP051.16`) and the bound
   `|∫ h| ≤ lpNorm h 2`, which is proved here from the variance identity.
6. Representative. "A measurable representative of `Q_T` may be chosen" is formalized as: there
   is a measurable `Q'` with `Q' =ᵐ[γ₀] Q_T`. For that `Q'`, the function
   `z ↦ (Q' z + d_K) / 2` is measurable and in `L²(γ₀)`. The constant `d_K` is the Bochner
   integral of the centered kernel on its diagonal. This is a real number for every `μ` and `W`,
   so membership in `L²` of the constant needs no integrability hypothesis. Integrability of
   `K(x, x)` is not used, and the statement does not depend on it.
7. Identification with the campaign objects. The Gaussian law is `γ₀` only, and the campaign
   declarations `S.mu`, `D.K` and the named limit are not used here, as in `LIP051.44`. The
   identification is deferred to the adapter `LIP051.01`.
8. Specification defects. None found beyond the index convention already recorded in
   `LIP051.06` (defect FD-002).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- The diagonal integral `d_K = ∫ K(x, x) dμ(x)` of the centered kernel with the original
diagonal retained. -/
noncomputable def dK_LIP05145 {d : ℕ} (μ : Measure (DGPS.Torus d))
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) : ℝ :=
  ∫ x, centeredKernelOf_LIP05103 μ W x x ∂μ

/-- The squared `lpNorm` of an `L²` function under a finite measure is its second moment. -/
lemma lpNorm_sq_LIP05145 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) : lpNorm f 2 P ^ 2 = ∫ z, f z ^ 2 ∂P := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  have h0 : 0 ≤ ∫ z, ‖f z‖ ^ (ENNReal.toReal 2) ∂P :=
    integral_nonneg fun z => by positivity
  have h2 : ENNReal.toReal 2 = ((2:ℕ):ℝ) := by simp
  rw [h2] at h0 ⊢
  rw [Real.rpow_inv_natCast_pow (n := 2) h0 (by norm_num)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

/-- The absolute value of the mean of an `L²` function under a probability measure is bounded by
its `lpNorm`. -/
lemma abs_integral_le_LIP05145 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → ℝ) (hh : MemLp h 2 P) :
    |∫ ω, h ω ∂P| ≤ lpNorm h 2 P := by
  have hsq : lpNorm h 2 P ^ 2 = ∫ ω, h ω ^ 2 ∂P :=
    lpNorm_sq_LIP05145 P h hh.aestronglyMeasurable
  have hv : variance h P = ∫ ω, h ω ^ 2 ∂P - (∫ ω, h ω ∂P) ^ 2 := variance_eq_sub hh
  have hvar : 0 ≤ variance h P := variance_nonneg h P
  have hL : 0 ≤ lpNorm h 2 P := lpNorm_nonneg
  have hle : (∫ ω, h ω ∂P) ^ 2 ≤ lpNorm h 2 P ^ 2 := by
    rw [hsq]
    linarith
  exact abs_le_of_sq_le_sq hle hL

/-- For `R ≤ S`, the squared `L²(γ₀)` distance of the Wick sections of ranks `R` and `S` equals
twice a finite partial sum of the squared tail coefficients over `range (S+1) ×ˢ range (S+1)`. -/
lemma eq_LIP05145 (c : ℕ → ℕ → ℝ) (hsym : ∀ i j, c i j = c j i) (R S : ℕ) (hRS : R ≤ S) :
    lpNorm (fun z => wickQuad_LIP05116 (Finset.Icc 1 R) c z
      - wickQuad_LIP05116 (Finset.Icc 1 S) c z) 2 gam_LIP05144 ^ 2
      = 2 * ∑ q ∈ Finset.range (S + 1) ×ˢ Finset.range (S + 1),
          {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => c q.1 q.2 ^ 2) q := by
  have hA : ∀ i ∈ Finset.Icc 1 S, ∀ j ∈ Finset.Icc 1 S,
      trunc_LIP05144 c R i j = trunc_LIP05144 c R j i :=
    fun i _ j _ => trunc_symm_LIP05144 c hsym R i j
  have hB : ∀ i ∈ Finset.Icc 1 S, ∀ j ∈ Finset.Icc 1 S,
      trunc_LIP05144 c S i j = trunc_LIP05144 c S j i :=
    fun i _ j _ => trunc_symm_LIP05144 c hsym S i j
  obtain ⟨-, -, -, -, -, -, h5, -⟩ :=
    lip051_16_finite_wick_isometry (Finset.Icc 1 S) (trunc_LIP05144 c R) (trunc_LIP05144 c S) hA hB
  have hfun : (fun z => wickQuad_LIP05116 (Finset.Icc 1 R) c z
      - wickQuad_LIP05116 (Finset.Icc 1 S) c z)
      = (fun z => wickQuad_LIP05116 (Finset.Icc 1 S) (trunc_LIP05144 c R) z
      - wickQuad_LIP05116 (Finset.Icc 1 S) (trunc_LIP05144 c S) z) := by
    funext z
    rw [wick_trunc_LIP05144 c hsym R S hRS z, wick_trunc_LIP05144 c hsym S S le_rfl z]
  rw [hfun, h5]
  congr 1
  have hpt : ∀ a ∈ Finset.Icc 1 S, ∀ b ∈ Finset.Icc 1 S,
      (trunc_LIP05144 c R a b - trunc_LIP05144 c S a b) ^ 2
      = {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
          (fun q => c q.1 q.2 ^ 2) (a, b) := by
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    simp only [trunc_LIP05144, Set.indicator_apply, Set.mem_ofPred_eq, Finset.mem_Icc]
    split_ifs <;> first | (exfalso; omega) | ring
  calc ∑ i ∈ Finset.Icc 1 S, ∑ j ∈ Finset.Icc 1 S,
        (trunc_LIP05144 c R i j - trunc_LIP05144 c S i j) ^ 2
      = ∑ q ∈ Finset.Icc 1 S ×ˢ Finset.Icc 1 S,
          {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => c q.1 q.2 ^ 2) q := by
        rw [Finset.sum_product]
        exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hpt i hi j hj
    _ = ∑ q ∈ Finset.range (S + 1) ×ˢ Finset.range (S + 1),
          {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => c q.1 q.2 ^ 2) q := by
        apply Finset.sum_subset
        · apply Finset.product_subset_product <;> intro x hx <;>
            simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢ <;> omega
        · rintro ⟨a, b⟩ hq hnq
          simp only [Finset.mem_product, Finset.mem_range, Finset.mem_Icc] at hq hnq
          apply Set.indicator_of_notMem
          simp only [Set.mem_ofPred_eq]
          omega

/-- A summable series over `ℕ × ℕ` has its square partial sums over
`range (S+1) ×ˢ range (S+1)` converging to its total. -/
lemma tendsto_range_LIP05145 (g : ℕ × ℕ → ℝ) (a : ℝ) (hg : HasSum g a) :
    Tendsto (fun S : ℕ => ∑ q ∈ Finset.range (S + 1) ×ˢ Finset.range (S + 1), g q)
      atTop (𝓝 a) := by
  have hφ : Tendsto (fun S : ℕ => Finset.range (S + 1) ×ˢ Finset.range (S + 1)) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro s
    rw [Filter.eventually_atTop]
    refine ⟨s.sup (fun q => q.1 + q.2), fun S hS => ?_⟩
    intro q hq
    have h1 : q.1 + q.2 ≤ s.sup (fun q => q.1 + q.2) := Finset.le_sup (f := fun q => q.1 + q.2) hq
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  exact hg.comp hφ

theorem lip051_45_exact_wick_tail_mean_representative {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    (∃ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 ∧
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0)) ∧
    (∀ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        (∫ z, QT z ∂gam_LIP05144 = 0) ∧
        (∀ R : ℕ, lpNorm (fun z : ℕ → ℝ =>
            QT z - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2
          = 2 * (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2) ∧
        (∃ Q' : (ℕ → ℝ) → ℝ, Measurable Q' ∧ Q' =ᵐ[gam_LIP05144] QT ∧
          Measurable (fun z : ℕ → ℝ => (Q' z + dK_LIP05145 μ W) / 2) ∧
          MemLp (fun z : ℕ → ℝ => (Q' z + dK_LIP05145 μ W) / 2) 2 gam_LIP05144)) := by
  obtain ⟨hsymT, -, -, -, -, htailH, -, -, -, -, -, -⟩ :=
    lip051_06_spectral_section_convergence_coefficient_symmetry hWc hs hM hb e he0 f hfm hfe
  have hsym : ∀ i j, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i := hsymT
  obtain ⟨hmem, -, hex, -⟩ :=
    lip051_44_cauchy_wick_sections_existence_limit hWc hs hM hb e he0 f hfm hfe
  have hwm : ∀ R : ℕ, ∫ z, wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
      ∂gam_LIP05144 = 0 := fun R =>
    (lip051_16_finite_wick_isometry (Finset.Icc 1 R) _ _
      (fun i _ j _ => hsym i j) (fun i _ j _ => hsym i j)).2.2.1
  refine ⟨hex, fun QT hQT hTt => ⟨?_, ?_, ?_⟩⟩
  · -- mean zero
    have hbound : ∀ S : ℕ, |∫ z, QT z ∂gam_LIP05144| ≤
        lpNorm (fun z : ℕ → ℝ => QT z
          - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 := by
      intro S
      have h : |∫ z, (QT z - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z)
            ∂gam_LIP05144| ≤
          lpNorm (fun z : ℕ → ℝ => QT z
            - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
        abs_integral_le_LIP05145 gam_LIP05144 _ (hQT.sub (hmem S))
      have hi1 : Integrable QT gam_LIP05144 := hQT.integrable (by norm_num)
      have hi2 : Integrable (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) gam_LIP05144 :=
        (hmem S).integrable (by norm_num)
      rw [integral_sub hi1 hi2, hwm S, sub_zero] at h
      exact h
    have hlim : Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ => QT z
        - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144)
        atTop (𝓝 0) := by
      refine Tendsto.congr (fun S => ?_) hTt
      exact lpNorm_sub_comm (fun z : ℕ → ℝ => wickQuad_LIP05116 (Finset.Icc 1 S)
        (coefT_LIP05134 μ W f) z) QT 2 gam_LIP05144
    have h0 : |∫ z, QT z ∂gam_LIP05144| ≤ 0 := ge_of_tendsto' hlim hbound
    exact abs_nonpos_iff.mp h0
  · -- tail identity
    intro R
    have hHs : HasSum ({q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
        (fun q => coefT_LIP05134 μ W f q.1 q.2 ^ 2))
        ((eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2) :=
      (hasSum_subtype_iff_indicator).mp (htailH R)
    have hLp : Tendsto (fun S : ℕ => (hmem S).toLp (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z))
        atTop (𝓝 (hQT.toLp QT)) :=
      (tendsto_iff_LIP05144 gam_LIP05144
        (fun S z => wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z)
        hmem QT hQT).mp hTt
    have hD : Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144)
        atTop (𝓝 (lpNorm (fun z : ℕ → ℝ => QT z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144)) := by
      have h1 : Tendsto (fun S : ℕ => dist ((hmem S).toLp (fun z : ℕ → ℝ =>
            wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z))
            ((hmem R).toLp (fun z : ℕ → ℝ =>
              wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z)))
          atTop (𝓝 (dist (hQT.toLp QT) ((hmem R).toLp (fun z : ℕ → ℝ =>
              wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z)))) :=
        hLp.dist tendsto_const_nhds
      have h2 : dist (hQT.toLp QT) ((hmem R).toLp (fun z : ℕ → ℝ =>
            wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z))
          = lpNorm (fun z : ℕ → ℝ => QT z
            - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
        dist_LIP05144 gam_LIP05144 hQT (hmem R)
      rw [h2] at h1
      exact Tendsto.congr (fun S => dist_LIP05144 gam_LIP05144 (hmem S) (hmem R)) h1
    have hsq : Tendsto (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2)
        atTop (𝓝 (lpNorm (fun z : ℕ → ℝ => QT z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2)) :=
      hD.pow 2
    have hev : (fun S : ℕ => 2 * ∑ q ∈ Finset.range (S + 1) ×ˢ Finset.range (S + 1),
          {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => coefT_LIP05134 μ W f q.1 q.2 ^ 2) q)
        =ᶠ[atTop] (fun S : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 ^ 2) := by
      filter_upwards [eventually_ge_atTop R] with S hS
      have hflip : lpNorm (fun z : ℕ → ℝ =>
            wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z
            - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144
          = lpNorm (fun z : ℕ → ℝ =>
            wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
            - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
        lpNorm_sub_comm (fun z : ℕ → ℝ => wickQuad_LIP05116 (Finset.Icc 1 S)
          (coefT_LIP05134 μ W f) z) (fun z : ℕ → ℝ => wickQuad_LIP05116 (Finset.Icc 1 R)
          (coefT_LIP05134 μ W f) z) 2 gam_LIP05144
      rw [hflip, eq_LIP05145 (coefT_LIP05134 μ W f) hsym R S hS]
    have hsumT := (tendsto_range_LIP05145 _ _ hHs).const_mul 2
    have hsq2 := Tendsto.congr' hev hsumT
    exact tendsto_nhds_unique hsq hsq2
  · -- measurable representative
    have hae : AEMeasurable QT gam_LIP05144 := hQT.aestronglyMeasurable.aemeasurable
    have hq : MemLp (fun z : ℕ → ℝ => (QT z + dK_LIP05145 μ W) / 2) 2 gam_LIP05144 := by
      have h : MemLp (fun z : ℕ → ℝ => (1 / 2 : ℝ) * (QT z + dK_LIP05145 μ W)) 2 gam_LIP05144 :=
        (hQT.add (memLp_const (dK_LIP05145 μ W))).const_mul _
      have heq : (fun z : ℕ → ℝ => (1 / 2 : ℝ) * (QT z + dK_LIP05145 μ W))
          = fun z : ℕ → ℝ => (QT z + dK_LIP05145 μ W) / 2 := by
        funext z
        ring
      rw [heq] at h
      exact h
    have hcongr : (fun z : ℕ → ℝ => (hae.mk QT z + dK_LIP05145 μ W) / 2)
        =ᵐ[gam_LIP05144] (fun z : ℕ → ℝ => (QT z + dK_LIP05145 μ W) / 2) := by
      filter_upwards [hae.ae_eq_mk.symm] with z hz
      simp only [hz]
    exact ⟨hae.mk QT, hae.measurable_mk, hae.ae_eq_mk.symm,
      (hae.measurable_mk.add_const _).div_const _,
      MemLp.ae_eq hcongr.symm hq⟩

end DGPS.Frontier.LIP051
