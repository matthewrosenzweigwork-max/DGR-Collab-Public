import FullLabeledLSI.Paper.Prop23ReplaceA

/-! # Prop 2.3 WP-D(c): replacement in the entropy terms -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### D(c): replacement in the entropy terms -/

section DC

/-- **Hölder step** `∫ Ψ² |g| ≤ ‖Ψ‖_{2p}² ‖g‖_{p'}`, `p' = p/(p-1)`, in lintegral form (no
integrability or measure-theoretic hypotheses besides a.e.-measurability; any measure).

Proof (about 30 lines): `ENNReal.lintegral_mul_le_Lp_mul_Lq` (conjugate exponents `p`, `p/(p-1)`,
`Real.HolderConjugate`) applied to `ofReal (Ψ²)` and `‖g‖ₑ`; `ofReal (Ψ^2)^p = ofReal (|Ψ|^(2p))` by
`ENNReal.ofReal_rpow_of_nonneg`, `Real.rpow_natCast`/`rpow_mul`; and
`eLpNorm g p' P = (∫⁻ ‖g‖ₑ^{p'})^{1/p'}` (`eLpNorm_eq_lintegral_rpow_enorm`). -/
theorem holder_sq_mul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Ψ g : Ω → ℝ} {p : ℝ}
    (hp : 1 < p) (hΨ : AEMeasurable Ψ P) (hg : AEMeasurable g P) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P ≤
      (∫⁻ ω, ENNReal.ofReal (|Ψ ω| ^ (2 * p)) ∂P) ^ (1 / p) *
        eLpNorm g (ENNReal.ofReal (p / (p - 1))) P := by
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < p / (p - 1) := hpq.symm.pos
  have hF : AEMeasurable (fun ω => ENNReal.ofReal (Ψ ω ^ 2)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hΨ.pow_const 2)
  have hG : AEMeasurable (fun ω => ‖g ω‖ₑ) P := hg.enorm
  have h1 : ∀ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) =
      ENNReal.ofReal (Ψ ω ^ 2) * ‖g ω‖ₑ := by
    intro ω
    rw [ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_eq_ofReal_abs]
  have h2 : ∀ ω, ENNReal.ofReal (Ψ ω ^ 2) ^ p = ENNReal.ofReal (|Ψ ω| ^ (2 * p)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by linarith), Real.rpow_mul (abs_nonneg _)]
    congr 1
    rw [← sq_abs (Ψ ω)]
    norm_cast
  have h3 : eLpNorm g (ENNReal.ofReal (p / (p - 1))) P =
      (∫⁻ ω, ‖g ω‖ₑ ^ (p / (p - 1)) ∂P) ^ (1 / (p / (p - 1))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable, ENNReal.toReal_ofReal hq0.le]
  calc ∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P
      = ∫⁻ ω, ((fun ω => ENNReal.ofReal (Ψ ω ^ 2)) * (fun ω => ‖g ω‖ₑ)) ω ∂P := by
        simp only [h1, Pi.mul_apply]
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2) ^ p ∂P) ^ (1 / p) *
          (∫⁻ ω, ‖g ω‖ₑ ^ (p / (p - 1)) ∂P) ^ (1 / (p / (p - 1))) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hF hG
    _ = _ := by simp only [h2, h3]

/-- Bochner-integral form of the Hölder step. -/
theorem norm_integral_sq_mul_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {Ψ g : Ω → ℝ}
    {p : ℝ} (hp : 1 < p) (hΨ : AEMeasurable Ψ P) (hg : AEMeasurable g P) {M : ℝ}
    (hM : ∫⁻ ω, ENNReal.ofReal (|Ψ ω| ^ (2 * p)) ∂P ≤ ENNReal.ofReal M) {η : ℝ} (hη : 0 ≤ η)
    (hn : eLpNorm g (ENNReal.ofReal (p / (p - 1))) P ≤ ENNReal.ofReal η) :
    ‖∫ ω, Ψ ω ^ 2 * g ω ∂P‖ ≤ (ENNReal.ofReal M ^ (1 / p)).toReal * η := by
  have h0 : 0 < p := by linarith
  have hH := holder_sq_mul P hp hΨ hg
  have hfin : ENNReal.ofReal M ^ (1 / p) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h1 : ∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P ≤
      ENNReal.ofReal M ^ (1 / p) * ENNReal.ofReal η := by
    refine hH.trans ?_
    gcongr
  calc ‖∫ ω, Ψ ω ^ 2 * g ω ∂P‖
      ≤ (∫⁻ ω, ENNReal.ofReal ‖Ψ ω ^ 2 * g ω‖ ∂P).toReal := norm_integral_le_lintegral_norm _
    _ = (∫⁻ ω, ENNReal.ofReal (Ψ ω ^ 2 * |g ω|) ∂P).toReal := by
        congr 1
        refine lintegral_congr fun ω => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ (ENNReal.ofReal M ^ (1 / p) * ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top) h1
    _ = (ENNReal.ofReal M ^ (1 / p)).toReal * η := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη]

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- **D(c): the entropy-side terms of (entropy-ground) and of `𝒥_{N,R}` agree asymptotically.**
By WP-C, `Ent_{P_N}(f²) = Ent_Q(Ψ²) + ∫Ψ²U_N dQ + log K_N ∫Ψ² dQ`, while `J_{N,R}` contains
`Ent_Q(Ψ²) + ∫Ψ² U_{N,R} dQ + log κ_R ∫Ψ² dQ`.  This lemma controls the difference
`∫Ψ² (U_N - U_{N,R}) dQ + (log K_N - log κ_R) ∫Ψ² dQ`, uniformly over all `Ψ` in a ball
`∫|Ψ|^{2p} dQ ≤ M` (in the application `Ψ = psiG f`, `p, M` from WP-A: `∫|Ψ|^{2p} ≤ C B^{2p}`).

HYPOTHESES (black boxes, all discharged by other work):
* `hU` = S23(1) `rank_errors .1` (lane 3);  * `hκ` = S23(2) `rank_errors .2.1` with
  `K∞ = Kinf W μ Q`;  * `hKN`, `hK0` = `gaussian_limit_law` (R27) conjuncts 1-2.

Statement order: `∃ R₁, ∀ R ≥ R₁, ∀ᶠ N` (the `N`-threshold may depend on `R`, exactly as the
`liminf` argument of WP-F needs).  The integrals are Bochner integrals; `Ψ² (U_N - U_{N,R})` is
integrable by Hölder and the hypothesis for `R ≥ R₁` (inside the proof), and the claim is a
statement about the combination only.

Proof (about 70-100 lines): choose `q = p/(p-1)` in `hU`; get `R₁` with `sup_{N≥1} ‖U_N - U_{N,R}‖_{q} ≤ η`
for `R ≥ R₁` (`Tendsto.eventually_lt`, `le_iSup₂`); `|∫Ψ²g| ≤ ∫⁻ ofReal(Ψ²|g|)` toReal
(`holder_sq_mul` with `P = QN μ N`, and `‖·‖` bound `ofReal M ^ (1/p) * η`); `∫Ψ² ≤ (∫|Ψ|^{2p})^{1/p}`
(Jensen / `holder_sq_mul` with `g = 1`, `eLpNorm_one_const`; probability measure); logs:
`Real.continuousAt_log` at `K∞ > 0` composed with `hKN`, `hκ` (eventually
`|log K_N - log K∞| < ε'` and, for `R ≥ R₁`, `|log κ_R - log K∞| < ε'`); combine. -/
theorem entropy_terms_replace [IsProbabilityMeasure μ] (A : FiniteRankApprox W μ e)
    {Kinf : ℝ} (hK0 : 0 < Kinf)
    (hKN : Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 Kinf))
    (hκ : Tendsto (fun R => kappaR A R) atTop (𝓝 Kinf))
    (hU : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
          eLpNorm (fun X => Ucentered W μ N X - URN A R N X) q (QN μ N)) atTop (𝓝 0))
    {p : ℝ} (hp : 1 < p) (M : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₁ : ℕ, ∀ R ≥ R₁, ∀ᶠ N in atTop, ∀ Ψ : Config N d → ℝ,
      AEStronglyMeasurable Ψ (QN μ N) →
      ∫⁻ X, ENNReal.ofReal (|Ψ X| ^ (2 * p)) ∂QN μ N ≤ ENNReal.ofReal M →
      |∫ X, Ψ X ^ 2 * (Ucentered W μ N X - URN A R N X) ∂QN μ N +
          (Real.log (centeredPartition W μ N) - Real.log (kappaR A R)) *
            ∫ X, Ψ X ^ 2 ∂QN μ N| ≤ ε := by
  intro ε hε
  set Qe : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hQe
  have hq1 : 1 ≤ p / (p - 1) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hQe1 : 1 ≤ Qe := ENNReal.one_le_ofReal.2 hq1
  have hQeT : Qe ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQe0 : Qe ≠ 0 := (zero_lt_one.trans_le hQe1).ne'
  set B : ℝ := (ENNReal.ofReal M ^ (1 / p)).toReal with hB
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  set η : ℝ := ε / (2 * (B + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηε : η * (2 * (B + 1)) = ε := by rw [hη]; field_simp
  have hlogκ : Tendsto (fun R => Real.log (kappaR A R)) atTop (𝓝 (Real.log Kinf)) :=
    ((Real.continuousAt_log hK0.ne').tendsto).comp hκ
  have hlogK : Tendsto (fun N => Real.log (centeredPartition W μ N)) atTop
      (𝓝 (Real.log Kinf)) :=
    ((Real.continuousAt_log hK0.ne').tendsto).comp hKN
  have e1 := (hU Qe hQe1 hQeT).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hη0))
  have e2 := (Metric.tendsto_nhds.1 hlogκ) (η / 2) (by positivity)
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 (e1.and e2)
  refine ⟨R₁, fun R hR => ?_⟩
  obtain ⟨hR1, hR2⟩ := hR₁ R hR
  have e3 := (Metric.tendsto_nhds.1 hlogK) (η / 2) (by positivity)
  filter_upwards [eventually_ge_atTop 1, e3] with N hN1 hN2 Ψ hΨ hbound
  have : IsProbabilityMeasure (QN μ N) := by unfold QN; infer_instance
  have hsup : eLpNorm (fun X => Ucentered W μ N X - URN A R N X) Qe (QN μ N) ≤
      ⨆ N ∈ {N : ℕ | 1 ≤ N},
        eLpNorm (fun X => Ucentered W μ N X - URN A R N X) Qe (QN μ N) :=
    le_iSup₂ (f := fun N (_ : N ∈ {N : ℕ | 1 ≤ N}) =>
      eLpNorm (fun X => Ucentered W μ N X - URN A R N X) Qe (QN μ N)) N hN1
  have hlt : eLpNorm (fun X => Ucentered W μ N X - URN A R N X) Qe (QN μ N) ≤
      ENNReal.ofReal η := (hsup.trans (le_of_lt hR1))
  have hgm : AEMeasurable (fun X => Ucentered W μ N X - URN A R N X) (QN μ N) :=
    (aestronglyMeasurable_of_eLpNorm_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlt)).aemeasurable
  have hΨm : AEMeasurable Ψ (QN μ N) := hΨ.aemeasurable
  have T1 := norm_integral_sq_mul_le (QN μ N) hp hΨm hgm hbound hη0.le hlt
  have T2 := norm_integral_sq_mul_le (QN μ N) hp hΨm (g := fun _ => (1 : ℝ))
    aemeasurable_const hbound zero_le_one (by
      rw [eLpNorm_const' _ hQe0 hQeT]
      simp)
  simp only [mul_one] at T2
  rw [Real.norm_eq_abs] at T1 T2
  have hlog : |Real.log (centeredPartition W μ N) - Real.log (kappaR A R)| ≤ η := by
    have a1 := hN2
    have a2 := hR2
    rw [Real.dist_eq] at a1 a2
    calc _ = |(Real.log (centeredPartition W μ N) - Real.log Kinf) +
          (Real.log Kinf - Real.log (kappaR A R))| := by ring_nf
      _ ≤ |Real.log (centeredPartition W μ N) - Real.log Kinf| +
          |Real.log Kinf - Real.log (kappaR A R)| := abs_add_le _ _
      _ ≤ η := by
        rw [abs_sub_comm (Real.log Kinf)] at *
        linarith
  calc _ ≤ |∫ X, Ψ X ^ 2 * (Ucentered W μ N X - URN A R N X) ∂QN μ N| +
        |(Real.log (centeredPartition W μ N) - Real.log (kappaR A R)) *
          ∫ X, Ψ X ^ 2 ∂QN μ N| := abs_add_le _ _
    _ ≤ B * η + η * B := by
        rw [abs_mul]
        gcongr
    _ ≤ ε := by nlinarith

end DC

end SharpLSI.FL
