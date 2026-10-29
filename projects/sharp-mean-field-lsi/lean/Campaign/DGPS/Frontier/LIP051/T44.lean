import DGPS.Frontier.LIP051.T06
import DGPS.Frontier.LIP051.T16

/-!
# LIP051.44: Cauchy Wick sections and existence of the limit

Task id `LIP051.44`, title "Cauchy Wick sections and existence of the limit" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", category leaf formalization, verification V1).
Proved inputs: `LIP051.06` (`DGPS.Frontier.LIP051.T06`) and `LIP051.16`
(`DGPS.Frontier.LIP051.T16`).

Setting. The data `μ`, `W`, `e`, `f` and the coefficients `T i j = coefT_LIP05134 μ W f i j` are
those of `LIP051.06`. The reference law is `γ₀ = Measure.infinitePi (gaussianReal 0 1)` on
`ℕ → ℝ`. The Wick section of rank `R` is `Q_R z = ∑_{i,j ∈ {1,…,R}} T i j (z i z j - δ i j)`, that
is `wickQuad_LIP05116 (Finset.Icc 1 R) T z`.

## Provides

* `DGPS.Frontier.LIP051.lip051_44_cauchy_wick_sections_existence_limit`: the main theorem. Every
  `Q_R` is in `L²(γ₀)`; the family is Cauchy in the `L²(γ₀)` seminorm; some `L²` function `Q_T`
  is the limit of `Q_R`; and any two `L²` limits agree `γ₀`-almost everywhere.
* `DGPS.Frontier.LIP051.gam_LIP05144`: the Gaussian reference measure `γ₀` on `ℕ → ℝ`.
* `DGPS.Frontier.LIP051.trunc_LIP05144`: zero extension of a coefficient matrix to `{1,…,R}²`.
* `DGPS.Frontier.LIP051.trunc_symm_LIP05144`: symmetry of a zero-extended symmetric matrix.
* `DGPS.Frontier.LIP051.wick_trunc_LIP05144`: the Wick section of rank `R` equals the Wick section
  over a larger rectangle built from the zero extension.
* `DGPS.Frontier.LIP051.key_LIP05144`: for `R ≤ S`, the squared `L²` distance of `Q_R` and `Q_S`
  is at most twice the squared tail norm at rank `R`.
* `DGPS.Frontier.LIP051.dist_LIP05144`: the distance of two `Lp` classes is the `lpNorm` of the
  difference.
* `DGPS.Frontier.LIP051.tendsto_iff_LIP05144`: `lpNorm` convergence to a limit is convergence of
  the `Lp` classes.
* `DGPS.Frontier.LIP051.limit_LIP05144`: a Cauchy family of `L²` functions has an `L²` limit.
* `DGPS.Frontier.LIP051.unique_LIP05144`: `L²` limits are unique up to almost-everywhere equality.

## R5 notes

1. Hypotheses. The binders are exactly those of `LIP051.06`: continuity of `uncurry W`, symmetry of
   `W`, `0 ≤ M` with `|W| ≤ M`, the Hilbert basis `e` with `e 0 = 1`, and measurable
   representatives `f j =ᵐ[μ] e j`. No hypothesis is added. The symmetry of the coefficients
   (needed by `LIP051.16`) is taken from the conclusion of `LIP051.06`.
2. Positive modes. The sums run over `i, j ∈ {1,…,R}` (`Finset.Icc 1 R`), as in the specification
   and in the positive-mode convention of `LIP051.06` (R5 note 4 there). The zero mode is never read:
   `Q_R` depends only on the coordinates `z i` with `1 ≤ i ≤ R`.
3. Cauchy property. "Cauchy in real `L²(γ₀)`" is formalized as: for every `ε > 0` there is `N` such
   that `lpNorm (Q_R - Q_S) 2 γ₀ < ε` whenever `N ≤ R` and `N ≤ S`. `lpNorm f p μ` is
   `(eLpNorm f p μ).toReal`.
4. Limit. "Unique `L²` limit `Q_T`" is formalized without dependent `Lp` coercions: there is an
   `L²(γ₀)` function `Q_T` with `lpNorm (Q_R - Q_T) 2 γ₀ → 0`, and any two such `L²` functions agree
   `γ₀`-almost everywhere. Uniqueness is therefore an almost-everywhere statement, which is the
   meaning of a unique element of `L²`.
5. Proof route. The zero extension to a common rectangle and the finite Wick identity of
   `LIP051.16` (conjunct 7) give `‖Q_R - Q_S‖² = 2 ∑ (T_R - T_S)²` over the larger rectangle. For
   `R ≤ S`, this finite sum is a partial sum of the tail series of `LIP051.06` (conjunct 6), whose
   total is `‖K - K_R‖₂²`, so `‖Q_R - Q_S‖² ≤ 2 ‖K - K_R‖₂²`. Since `‖K - K_R‖₂ → 0` by
   `LIP051.06` (conjunct 4), the family is Cauchy. The argument uses no orthonormality of the product
   basis: the bound is one-sided and only the tail identity is needed.
6. Index convention. The `L²` norms are the `eLpNorm` norms with respect to `μ.prod μ`, as in
   `LIP051.06`. The kernel `K` is the centered kernel `centeredKernelOf_LIP05103`, retained as a
   pointwise continuous function, so the original diagonal is kept.
7. Specification defects. None found beyond the index convention already recorded in `LIP051.06`
   (defect FD-002).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace DGPS.Frontier.LIP051

/-- Gaussian reference measure on the coordinate sequence space. -/
noncomputable abbrev gam_LIP05144 : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

/-- Zero extension of a coefficient matrix to the rectangle `{1,…,R}²`. -/
abbrev trunc_LIP05144 (c : ℕ → ℕ → ℝ) (R : ℕ) : ℕ → ℕ → ℝ :=
  fun i j => if i ∈ Finset.Icc 1 R ∧ j ∈ Finset.Icc 1 R then c i j else 0

lemma trunc_symm_LIP05144 (c : ℕ → ℕ → ℝ) (hsym : ∀ i j, c i j = c j i) (R : ℕ) (i j : ℕ) :
    trunc_LIP05144 c R i j = trunc_LIP05144 c R j i := by
  simp only [trunc_LIP05144]
  by_cases h : i ∈ Finset.Icc 1 R ∧ j ∈ Finset.Icc 1 R
  · have h' : j ∈ Finset.Icc 1 R ∧ i ∈ Finset.Icc 1 R := ⟨h.2, h.1⟩
    simp only [h, hsym i j]
  · have h' : ¬(j ∈ Finset.Icc 1 R ∧ i ∈ Finset.Icc 1 R) := fun h'' => h ⟨h''.2, h''.1⟩
    simp only [h, h', ↓reduceIte]

lemma wick_trunc_LIP05144 (c : ℕ → ℕ → ℝ) (hsym : ∀ i j, c i j = c j i) (R S : ℕ)
    (hRS : R ≤ S) (z : ℕ → ℝ) :
    wickQuad_LIP05116 (Finset.Icc 1 S) (trunc_LIP05144 c R) z
      = wickQuad_LIP05116 (Finset.Icc 1 R) c z := by
  obtain ⟨-, -, -, -, -, -, -, h6⟩ :=
    lip051_16_finite_wick_isometry (Finset.Icc 1 R) c c
      (fun i _ j _ => hsym i j) (fun i _ j _ => hsym i j)
  exact h6 (Finset.Icc 1 S) (Finset.Icc_subset_Icc le_rfl hRS) z

lemma key_LIP05144 (c : ℕ → ℕ → ℝ) (τ : ℕ → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hT : ∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)} =>
        c q.1.1 q.1.2 ^ 2) (τ R ^ 2))
    (R S : ℕ) (hRS : R ≤ S) :
    lpNorm (fun z => wickQuad_LIP05116 (Finset.Icc 1 R) c z
      - wickQuad_LIP05116 (Finset.Icc 1 S) c z) 2 gam_LIP05144 ^ 2 ≤ 2 * τ R ^ 2 := by
  have hA : ∀ i ∈ Finset.Icc 1 S, ∀ j ∈ Finset.Icc 1 S,
      trunc_LIP05144 c R i j = trunc_LIP05144 c R j i :=
    fun i _ j _ => trunc_symm_LIP05144 c hsym R i j
  have hB : ∀ i ∈ Finset.Icc 1 S, ∀ j ∈ Finset.Icc 1 S,
      trunc_LIP05144 c S i j = trunc_LIP05144 c S j i :=
    fun i _ j _ => trunc_symm_LIP05144 c hsym S i j
  obtain ⟨-, -, -, -, -, -, h5, h6⟩ :=
    lip051_16_finite_wick_isometry (Finset.Icc 1 S) (trunc_LIP05144 c R) (trunc_LIP05144 c S) hA hB
  have hfun : (fun z => wickQuad_LIP05116 (Finset.Icc 1 R) c z
      - wickQuad_LIP05116 (Finset.Icc 1 S) c z)
      = (fun z => wickQuad_LIP05116 (Finset.Icc 1 S) (trunc_LIP05144 c R) z
      - wickQuad_LIP05116 (Finset.Icc 1 S) (trunc_LIP05144 c S) z) := by
    funext z
    rw [wick_trunc_LIP05144 c hsym R S hRS z, wick_trunc_LIP05144 c hsym S S le_rfl z]
  rw [hfun, h5]
  have hpt : ∀ q ∈ Finset.Icc 1 S ×ˢ Finset.Icc 1 S,
      (trunc_LIP05144 c R q.1 q.2 - trunc_LIP05144 c S q.1 q.2) ^ 2
        = {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => c q.1 q.2 ^ 2) q := by
    rintro ⟨a, b⟩ hq
    simp only [Finset.mem_product, Finset.mem_Icc] at hq
    simp only [trunc_LIP05144, Set.indicator_apply, Set.mem_ofPred_eq, Finset.mem_Icc]
    split_ifs <;> first | (exfalso; omega) | ring
  have hHs : HasSum ({q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
      (fun q => c q.1 q.2 ^ 2)) (τ R ^ 2) :=
    (hasSum_subtype_iff_indicator).mp (hT R)
  have hnn : ∀ q, 0 ≤ {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
      (fun q => c q.1 q.2 ^ 2) q :=
    fun q => Set.indicator_nonneg (fun _ _ => sq_nonneg _) q
  have hle := sum_le_hasSum (Finset.Icc 1 S ×ˢ Finset.Icc 1 S) (fun q _ => hnn q) hHs
  have hsum : ∑ i ∈ Finset.Icc 1 S, ∑ j ∈ Finset.Icc 1 S,
      (trunc_LIP05144 c R i j - trunc_LIP05144 c S i j) ^ 2 ≤ τ R ^ 2 := by
    calc ∑ i ∈ Finset.Icc 1 S, ∑ j ∈ Finset.Icc 1 S,
          (trunc_LIP05144 c R i j - trunc_LIP05144 c S i j) ^ 2
        = ∑ q ∈ Finset.Icc 1 S ×ˢ Finset.Icc 1 S,
          (trunc_LIP05144 c R q.1 q.2 - trunc_LIP05144 c S q.1 q.2) ^ 2 := by
          rw [Finset.sum_product]
      _ = ∑ q ∈ Finset.Icc 1 S ×ˢ Finset.Icc 1 S,
          {q : ℕ × ℕ | (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}.indicator
            (fun q => c q.1 q.2 ^ 2) q := Finset.sum_congr rfl hpt
      _ ≤ τ R ^ 2 := hle
  linarith

lemma dist_LIP05144 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) {f g : Ω → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    dist (hf.toLp f) (hg.toLp g) = lpNorm (f - g) 2 ν := by
  rw [Lp.dist_def]
  unfold lpNorm
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  simp [h1, h2]

lemma tendsto_iff_LIP05144 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (g : ℕ → Ω → ℝ)
    (hg : ∀ R, MemLp (g R) 2 ν) (G : Ω → ℝ) (hG : MemLp G 2 ν) :
    Tendsto (fun R => lpNorm (g R - G) 2 ν) atTop (𝓝 0) ↔
      Tendsto (fun R => (hg R).toLp (g R)) atTop (𝓝 (hG.toLp G)) := by
  have h : (fun R => lpNorm (g R - G) 2 ν) = fun R => dist ((hg R).toLp (g R)) (hG.toLp G) := by
    funext R
    rw [dist_LIP05144 ν (hg R) hG]
  rw [h]
  exact tendsto_iff_dist_tendsto_zero.symm

lemma limit_LIP05144 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (g : ℕ → Ω → ℝ)
    (hg : ∀ R, MemLp (g R) 2 ν)
    (hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ R, N ≤ R → ∀ S, N ≤ S →
      lpNorm (g R - g S) 2 ν < ε) :
    ∃ G : Ω → ℝ, MemLp G 2 ν ∧ Tendsto (fun R => lpNorm (g R - G) 2 ν) atTop (𝓝 0) := by
  have hcs : CauchySeq (fun R => (hg R).toLp (g R)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_LIP05144 ν (hg m) (hg n)]
    exact hN m hm n hn
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨⇑L, Lp.memLp L, ?_⟩
  rw [tendsto_iff_LIP05144 ν g hg ⇑L (Lp.memLp L), Lp.toLp_coeFn L (Lp.memLp L)]
  exact hL

lemma unique_LIP05144 {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (g : ℕ → Ω → ℝ)
    (hg : ∀ R, MemLp (g R) 2 ν) (G₁ G₂ : Ω → ℝ) (h₁ : MemLp G₁ 2 ν) (h₂ : MemLp G₂ 2 ν)
    (t₁ : Tendsto (fun R => lpNorm (g R - G₁) 2 ν) atTop (𝓝 0))
    (t₂ : Tendsto (fun R => lpNorm (g R - G₂) 2 ν) atTop (𝓝 0)) :
    G₁ =ᵐ[ν] G₂ := by
  have heq := tendsto_nhds_unique ((tendsto_iff_LIP05144 ν g hg G₁ h₁).mp t₁)
    ((tendsto_iff_LIP05144 ν g hg G₂ h₂).mp t₂)
  exact (MemLp.toLp_eq_toLp_iff h₁ h₂).mp heq

/-- LIP051.44: Cauchy Wick sections and existence of the limit. -/
theorem lip051_44_cauchy_wick_sections_existence_limit {d : ℕ}
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    (∀ R : ℕ, MemLp (fun z : ℕ → ℝ =>
        wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ S : ℕ, N ≤ S →
        lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 < ε) ∧
    (∃ QT : (ℕ → ℝ) → ℝ, MemLp QT 2 gam_LIP05144 ∧
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - QT z) 2 gam_LIP05144)
          atTop (𝓝 0)) ∧
    (∀ Q₁ Q₂ : (ℕ → ℝ) → ℝ, MemLp Q₁ 2 gam_LIP05144 → MemLp Q₂ 2 gam_LIP05144 →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - Q₁ z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        Tendsto (fun R : ℕ => lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z - Q₂ z) 2 gam_LIP05144)
          atTop (𝓝 0) →
        Q₁ =ᵐ[gam_LIP05144] Q₂) := by
  obtain ⟨hsymT, -, -, htend, -, htailH, -, -, -, -, -, -⟩ :=
    lip051_06_spectral_section_convergence_coefficient_symmetry hWc hs hM hb e he0 f hfm hfe
  have hsym : ∀ i j, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i := hsymT
  have hmem : ∀ R : ℕ, MemLp (fun z : ℕ → ℝ =>
      wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
    fun R => (lip051_16_finite_wick_isometry (Finset.Icc 1 R) _ _
      (fun i _ j _ => hsym i j) (fun i _ j _ => hsym i j)).1
  have hcau : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ R : ℕ, N ≤ R → ∀ S : ℕ, N ≤ S →
      lpNorm (fun z : ℕ → ℝ =>
        wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
        - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (htend.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N, fun R hR S hS => ?_⟩
    have hτ0 : 0 ≤ (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal :=
      ENNReal.toReal_nonneg
    have hτ0' : 0 ≤ (eLpNorm (tailKR_LIP05134 μ W f S) 2 (μ.prod μ)).toReal :=
      ENNReal.toReal_nonneg
    have hL0 : 0 ≤ lpNorm (fun z : ℕ → ℝ =>
        wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
        - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 :=
      lpNorm_nonneg
    rcases le_total R S with h | h
    · have hk := key_LIP05144 (coefT_LIP05134 μ W f)
        (fun R => (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) hsym htailH R S h
      have hτ : (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal < ε / 2 := hN R hR
      nlinarith [mul_nonneg hτ0 hτ0, mul_pos hε hε]
    · have hk := key_LIP05144 (coefT_LIP05134 μ W f)
        (fun R => (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) hsym htailH S R h
      have hτ : (eLpNorm (tailKR_LIP05134 μ W f S) 2 (μ.prod μ)).toReal < ε / 2 := hN S hS
      have hc := lpNorm_sub_comm (fun z : ℕ → ℝ =>
        wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z)
        (fun z : ℕ → ℝ => wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z)
        2 gam_LIP05144
      have hc' : lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144
          = lpNorm (fun z : ℕ → ℝ =>
          wickQuad_LIP05116 (Finset.Icc 1 S) (coefT_LIP05134 μ W f) z
          - wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) 2 gam_LIP05144 := hc
      rw [hc']
      nlinarith [mul_nonneg hτ0' hτ0', mul_pos hε hε]
  obtain ⟨G, hGm, hGt⟩ := limit_LIP05144 gam_LIP05144
    (fun R z => wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) hmem hcau
  refine ⟨hmem, hcau, ⟨G, hGm, hGt⟩, fun Q₁ Q₂ h₁ h₂ t₁ t₂ => ?_⟩
  exact unique_LIP05144 gam_LIP05144
    (fun R z => wickQuad_LIP05116 (Finset.Icc 1 R) (coefT_LIP05134 μ W f) z) hmem Q₁ Q₂ h₁ h₂ t₁ t₂

end DGPS.Frontier.LIP051
