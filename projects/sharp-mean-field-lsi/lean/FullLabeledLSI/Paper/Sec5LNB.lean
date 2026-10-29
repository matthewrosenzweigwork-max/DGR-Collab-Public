import FullLabeledLSI.Paper.Sec5LNDefs

/-!
# Large-N assembly B: conditional-law lemmas shared by L1 and L3
-/

open MeasureTheory Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-! ## 2. Conditional-law lemmas shared by L1 and L3 -/

section cond
variable {μ : Measure (Torus d)} {N : ℕ} {ν : Measure (Config N d)} {Q : Config N d → ℝ} {c C : ℝ}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} {s : Fin N → Fin d → Config N d → ℝ}
  {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}

/-- **Bounded `H¹` conditional densities.**  For a.e. revealed values `a`, every `ρ_{S,i}`, `i ∈ Sᶜ`,
is an `IsBddH1Dens` with gradient `gradCondS` and constants `c/C ≤ ρ ≤ C/c`.
Proof: `condDensS_bounds`, `measurable_condDensS`, `integral_condDensS` (always), and
`ae_isWeakGrad_condDensS`, `ae_memLp_gradCondS` (a.e. `a`; needs `gradW`, `gradL2` and
`Integrable (GQ · p)` from `gradL2`), then `ae_all_iff`/`Finset.eventually_all` over `i ∈ Sᶜ`.
Estimate: ~40 lines. -/
theorem ae_isBddH1Dens_condDensS (hS : ScoreData V W μ ν Q c C GQ s bF bΔ Bb)
    (S : Finset (Fin N)) :
    ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i ∈ Sᶜ,
      IsBddH1Dens (condDensS Q S i a) (gradCondS Q GQ S i a) (c / C) (C / c) := by
  have hQ := hS.dens
  have hcC : c ≤ C := (hQ.lower 0).trans (hQ.upper 0)
  have hC : 0 < C := hQ.pos.trans_le hcC
  have hGi : ∀ p, Integrable (fun y => GQ y p) volume := fun p =>
    (hS.gradL2 p).integrable one_le_two
  have h1 : ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i, i ∈ Sᶜ →
      IsWeakGrad (condDensS Q S i a) (gradCondS Q GQ S i a) := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ Sᶜ
    · filter_upwards [ae_isWeakGrad_condDensS hQ (Finset.mem_compl.mp hi) hS.gradW hGi]
        with a ha _ using ha
    · exact Eventually.of_forall fun a h => absurd h hi
  have h2 : ∀ᵐ a ∂(volume : Measure (S → Torus d)), ∀ i, i ∈ Sᶜ → ∀ k,
      MemLp (fun x => gradCondS Q GQ S i a x k) 2 (haar d) := by
    rw [ae_all_iff]
    intro i
    by_cases hi : i ∈ Sᶜ
    · filter_upwards [ae_memLp_gradCondS (Q := Q) (Finset.mem_compl.mp hi) hS.gradM hS.gradL2]
        with a ha _ using ha
    · exact Eventually.of_forall fun a h => absurd h hi
  filter_upwards [h1, h2] with a ha1 ha2 i hi
  exact ⟨div_pos hQ.pos hC, (measurable_condDensS hQ S i).of_uncurry_left,
    fun x => (condDensS_bounds hQ S i a x).1, fun x => (condDensS_bounds hQ S i a x).2,
    integral_condDensS hQ S i a, ha1 i hi, ha2 i hi⟩

/-- **The score identity (5.20) in the `(s, G)` language.**  For `i ∉ S`, ν-a.e.:
`∇ₓ log ρ_{S,i}(X_i | X_S) + ∇Φ_μ(X_i) = E_ν[s_i - G_i | X_S, X_i]` (componentwise `k`).
Proof: `score_ae_eq_condExp` (Sec5CondD, with `F = GQ/Q`, `hGi` from `gradL2`) gives
`gradCondS/condDensS =ᵐ E[GQ_{(i,k)}/Q | 𝒢]`; by `hS.score`, `GQ/Q =ᵐ s - Gpart - ∇Φ(X_i)`; the last
term is `𝒢`-measurable (function of `X_i`) and bounded (`lipGrad (PhiMF) ` is bounded:
`lipschitz_PhiMF` + `lipGrad` bound, see `exists_bound_gradH`-type lemmas), and `s_{i,k} ∈ L²(ν) ⊂ L¹`,
`Gpart` bounded; so `condExp_sub`, `condExp_of_stronglyMeasurable` give the claim.
Estimate: ~70 lines. -/
theorem condScore_ae_eq (hyp : Hyp V W KV KW) {μ' : ProbabilityMeasure (Torus d)}
    (hμ' : IsMinimizer V W μ') [IsFiniteMeasure ν]
    (hS : ScoreData V W (μ' : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) (k : Fin d) :
    (fun X => gradCondS Q GQ S i (restrictS S X) (X i) k / condDensS Q S i (restrictS S X) (X i) +
        lipGrad (PhiMF V W (μ' : Measure (Torus d))) (X i) k) =ᵐ[ν]
      condExp (revSigma S i) ν (fun Y => s i k Y - Gpart bF bΔ N Y i k) := by
  classical
  have hQ := hS.dens
  have hac := minimizer_ac hyp hμ'
  have hGi : Integrable (fun y => GQ y (i, k)) volume := (hS.gradL2 _).integrable one_le_two
  have hle : revSigma S i ≤ (inferInstance : MeasurableSpace (Config N d)) :=
    ((measurable_restrictS S).prodMk (measurable_pi_apply i)).comap_le
  have h1 := score_ae_eq_condExp hQ hi hS.eq hS.gradM k hGi
  obtain ⟨L, hL⟩ := lipschitz_PhiMF hyp hac (μ := (μ' : Measure (Torus d)))
  have hLm : Measurable fun x => lipGrad (PhiMF V W (μ' : Measure (Torus d))) x k :=
    measurable_lipGrad (continuous_PhiMF hyp) k
  set Lf : Config N d → ℝ := fun X => lipGrad (PhiMF V W (μ' : Measure (Torus d))) (X i) k with hLf
  have hLfm : Measurable Lf := hLm.comp (measurable_pi_apply i)
  have hLf𝒢 : StronglyMeasurable[revSigma S i] Lf :=
    (hLm.comp (measurable_snd.comp
      (comap_measurable (fun X : Config N d => (restrictS S X, X i))))).stronglyMeasurable
  have hLfi : Integrable Lf ν :=
    Integrable.of_bound hLfm.aestronglyMeasurable (L : ℝ) (Eventually.of_forall fun X => by
      rw [Real.norm_eq_abs]; exact abs_lipGrad_le hL (X i) k)
  have hsi : Integrable (s i k) ν := by
    have : MemLp (s i k) 2 ν :=
      (memLp_two_iff_integrable_sq (hS.sM i k).aestronglyMeasurable).mpr (hS.sL2 i k)
    exact this.integrable one_le_two
  have hGp : Integrable (fun Y => Gpart bF bΔ N Y i k) ν :=
    Integrable.of_bound (measurable_Gpart hS.force i k).aestronglyMeasurable
      ((N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb)) (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact abs_Gpart_le hS.force X i k)
  have hsG : Integrable (fun Y => s i k Y - Gpart bF bΔ N Y i k) ν := hsi.sub hGp
  have hF : (fun Y : Config N d => GQ (flat Y) (i, k) / Q Y) =ᵐ[ν]
      fun Y => (s i k Y - Gpart bF bΔ N Y i k) - Lf Y := by
    filter_upwards [hS.score] with X hX
    exact hX i k
  have h2 := condExp_congr_ae (m := revSigma S i) hF
  have h3 : ν[fun Y => s i k Y - Gpart bF bΔ N Y i k - Lf Y | revSigma S i] =ᵐ[ν]
      ν[fun Y => s i k Y - Gpart bF bΔ N Y i k | revSigma S i] - ν[Lf | revSigma S i] :=
    condExp_sub hsG hLfi (revSigma S i)
  have h4 : ν[Lf | revSigma S i] = Lf := condExp_of_stronglyMeasurable hle hLf𝒢 hLfi
  filter_upwards [h1, h2, h3] with X a b c
  rw [a, b]
  simp only [Pi.sub_apply] at c
  rw [c, h4]
  simp only [hLf]
  ring

/-- **Disintegration along `(X_S, X_i)`.**  For `i ∉ S` and jointly measurable `F ≥ 0`,
`∫⁻ F(X_S, X_i) dν = ∫⁻ (∫⁻ ρ_{S,i}(X_S)(x) F(X_S, x) dx) dν(X)`.
Proof: both sides equal `∫⁻ a, ZcS a * ∫⁻ x, condDensS a x * F a x` — left by `lintegral_revealCur`
(`margQS = ZcS · condDensS`, `condDensS = margQS / ZcS`); right by `lintegral_map` along `restrictS S`
and `map_restrictS_eq` (law of `X_S` has density `ZcS`).  This is the "T-interface" turning `ν`-averages
of functions of `(X_S, X_i)` into `a`-averages of slice integrals.
Estimate: ~50 lines. -/
theorem lintegral_pair_eq_lintegral_condDensS (hQ : IsBddDens Q c C) (hν : ν = qMeasure Q)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S)
    {F : (S → Torus d) → Torus d → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ X, F (restrictS S X) (X i) ∂ν =
      ∫⁻ X, ∫⁻ x, ENNReal.ofReal (condDensS Q S i (restrictS S X) x) * F (restrictS S X) x
        ∂haar d ∂ν := by
  have hQm := hQ.meas
  have hν' := hν
  have hpos : ∀ a, 0 < ZcS Q S i a := fun a => hQ.pos.trans_le (ZcS_bounds hQ S i a).1
  have hnn : ∀ a x, 0 ≤ condDensS Q S i a x := fun a x =>
    div_nonneg (hQ.pos.trans_le (margQS_bounds hQ S i a x).1).le (hpos a).le
  have hm1 : Measurable fun X : Config N d => F (restrictS S X) (X i) :=
    hF.comp ((measurable_restrictS S).prodMk (measurable_pi_apply i))
  have hQo : Measurable fun X => ENNReal.ofReal (Q X) := ENNReal.measurable_ofReal.comp hQm
  have hG : Measurable fun a : S → Torus d =>
      ∫⁻ x, ENNReal.ofReal (condDensS Q S i a x) * F a x ∂haar d :=
    (((ENNReal.measurable_ofReal.comp (measurable_condDensS hQ S i)).mul hF)).lintegral_prod_right'
  have hL : ∫⁻ X, F (restrictS S X) (X i) ∂ν =
      ∫⁻ a, ∫⁻ x, F a x * ENNReal.ofReal (margQS Q S i a x) ∂haar d := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ hQo hm1]
    rw [← lintegral_revealCur hQ hi hF]
    refine lintegral_congr fun X => ?_
    simp [mul_comm]
  have hR : ∫⁻ X, ∫⁻ x, ENNReal.ofReal (condDensS Q S i (restrictS S X) x) *
      F (restrictS S X) x ∂haar d ∂ν =
      ∫⁻ a, ∫⁻ x, F a x * ENNReal.ofReal (margQS Q S i a x) ∂haar d := by
    rw [← lintegral_map hG (measurable_restrictS S)]
    have hmap : ν.map (restrictS S) =
        (volume : Measure (S → Torus d)).withDensity fun a => ENNReal.ofReal (ZcS Q S i a) := by
      rw [hν]; exact map_restrictS_eq hQ hi
    have hZm : Measurable fun a : S → Torus d => ENNReal.ofReal (ZcS Q S i a) :=
      ENNReal.measurable_ofReal.comp (measurable_ZcS hQ S i)
    rw [hmap, lintegral_withDensity_eq_lintegral_mul _ hZm hG]
    refine lintegral_congr fun a => ?_
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    have : margQS Q S i a x = condDensS Q S i a x * ZcS Q S i a := by
      unfold condDensS; rw [div_mul_cancel₀ _ (hpos a).ne']
    rw [this, ENNReal.ofReal_mul (hnn a x)]
    ring
  rw [hL, hR]

/-- `bMean` of the conditional barycentre is the bounded-representative force `B_S`:
ν-a.e., `bMean W μ (barDensS Q S (X_S)) (X_i) k = BS bF ν S X (X_i) k`.
Proof: `bfixF = bForce` a.e. (`bForce_ae_prod hyp (minimizer_ac hyp hμ)`), `bForce = bF` a.e. (`hS.bF_ae`),
`barCond_ae_eq_densMeasure`, `condForce_ae_eq_of_ac` (Sec5ForceAE; `ν ≪ volume ≪ ν` from `IsBddDens`)
and `integral_densMeasure`-type rewriting `∫ bF x y dρ̄(y) = ∫ bF x y ρ̄(y) dy`.  Estimate: ~50 lines. -/
theorem bMean_ae_eq_BS (hyp : Hyp V W KV KW) {μ' : ProbabilityMeasure (Torus d)}
    (hμ' : IsMinimizer V W μ') [IsProbabilityMeasure ν]
    (hS : ScoreData V W (μ' : Measure (Torus d)) ν Q c C GQ s bF bΔ Bb)
    {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S) :
    ∀ᵐ X ∂ν, ∀ k, bMean W (μ' : Measure (Torus d)) (barDensS Q S (restrictS S X)) (X i) k =
      BS bF ν S X (X i) k := by
  have hQ := hS.dens
  have hac := minimizer_ac hyp hμ'
  have hν := hS.eq
  have hνac : ν ≪ (volume : Measure (Config N d)) := by
    rw [hν]; exact withDensity_absolutelyContinuous _ _
  have hvac : (volume : Measure (Config N d)) ≪ ν := by
    rw [hν]
    exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hQ.meas).aemeasurable
      (Eventually.of_forall fun X => by simpa using hQ.pos.trans_le (hQ.lower X))
  have hbg : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k,
      bfixF W (μ' : Measure (Torus d)) p.1 p.2 k = bF p.1 p.2 k := by
    filter_upwards [bForce_ae_prod hyp hac, hS.bF_ae] with p h1 h2 k
    rw [← h2 k, h1 k]; rfl
  have h3 := condForce_ae_eq_of_ac hbg ν hνac hvac S i hi
  have h4 := barCond_ae_eq_densMeasure hQ hν (S := S)
  filter_upwards [h3, h4] with X a b k
  have hcard : 0 < Sᶜ.card := Finset.card_pos.mpr ⟨i, Finset.mem_compl.mpr hi⟩
  have hnpos : (0 : ℝ) < (Sᶜ.card : ℝ) := by exact_mod_cast hcard
  have hC : 0 < C := hQ.pos.trans_le ((hQ.lower 0).trans (hQ.upper 0))
  have hnn : ∀ x, 0 ≤ barDensS Q S (restrictS S X) x := fun x => by
    unfold barDensS
    refine mul_nonneg (inv_nonneg.mpr hnpos.le) (Finset.sum_nonneg fun j _ => ?_)
    exact (div_pos hQ.pos hC).le.trans (condDensS_bounds hQ S j _ x).1
  have hint1 : ∫ x, barDensS Q S (restrictS S X) x ∂haar d = 1 := by
    unfold barDensS
    rw [integral_const_mul, integral_finsetSum _ fun j _ =>
      integrable_of_integral_eq_one' (integral_condDensS hQ S j (restrictS S X))]
    simp only [integral_condDensS hQ S _ (restrictS S X), Finset.sum_const, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hnpos.ne'
  unfold BS bMean
  rw [← a k, b, integral_densMeasure' hnn hint1]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

end cond


end SharpLSI.FL
