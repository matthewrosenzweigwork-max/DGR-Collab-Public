import FullLabeledLSI.Paper.Sec3DiluteB

/-!
# Proposition 3.3 (≤), part C: the dilute family for a bounded test function

For a bounded nonnegative `g ∈ H¹` with `a ∫ q g² = 1`, `u₁ = √a g`, `u₂ = √(1/(1-ε)) √(1 - εa g²)`:
the quotient of the family `diluteFam q u₁ u₂ ε` is at most
`2 D/Ent + 16 ε a M² D/Ent` (`D` an upper bound for `∫ q |∇g|²`, `Ent = Ent_μ(g²)`).
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem sqNorm_smul' (c : ℝ) (v : Fin d → ℝ) : sqNorm (fun k => c * v k) = c ^ 2 * sqNorm v := by
  simp only [sqNorm, mul_pow, Finset.mul_sum]

theorem sqNorm_le_of_abs_le {v w : Fin d → ℝ} {A : ℝ} (h : ∀ k, |v k| ≤ A * |w k|) :
    sqNorm v ≤ A ^ 2 * sqNorm w := by
  rw [sqNorm, sqNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have := pow_le_pow_left₀ (abs_nonneg _) (h k) 2
  rwa [sq_abs, mul_pow, sq_abs] at this

theorem isWeakGrad_sqrt_one_sub {g : Torus d → ℝ} {G : Torus d → Fin d → ℝ} {M r : ℝ}
    (hg : IsWeakGrad g G) (hgM : ∀ x, |g x| ≤ M) (hG : ∀ k, MemLp (fun y => G y k) 2 (haar d))
    (hr : 0 ≤ r) (hrM : r * M ^ 2 ≤ 1 / 2) :
    IsWeakGrad (fun y => Real.sqrt (1 - r * g y ^ 2))
      (fun y k => -(r * g y * G y k) / Real.sqrt (1 - r * g y ^ 2)) := by
  have hg2 : MemLp g 2 (haar d) :=
    MemLp.of_bound hg.aestronglyMeasurable_fun M (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hgM x)
  have hsq := isWeakGrad_sq hg hg2 hG
  have h1 : IsWeakGrad (fun y => 1 + -r * g y ^ 2)
      (fun y k => (0 : ℝ) + -r * (2 * g y * G y k)) :=
    (isWeakGrad_const (1 : ℝ)).add (hsq.cmul (-r))
  have hρ : ∀ y, 1 / 2 ≤ 1 + -r * g y ^ 2 := fun y => by
    have h2 : g y ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (g y)]; exact pow_le_pow_left₀ (abs_nonneg _) (hgM y) 2
    nlinarith [mul_le_mul_of_nonneg_left h2 hr]
  have hρi : Integrable (fun y => 1 + -r * g y ^ 2) volume :=
    (integrable_const 1).add (hg2.integrable_sq.const_mul (-r))
  have hgi : ∀ k, Integrable (fun y => (0 : ℝ) + -r * (2 * g y * G y k)) volume := fun k => by
    have := (hg2.integrable_mul (hG k)).const_mul (-r * 2)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]; ring
  have h2 := isWeakGrad_sqrt_of_ge h1 hρi hgi (c := 1 / 2) (by norm_num) hρ
  have e : ∀ y, 1 - r * g y ^ 2 = 1 + -r * g y ^ 2 := fun y => by ring
  simp only [e]
  convert h2 using 1
  funext y k
  ring

theorem abs_grad_sqrt_one_sub_le {g G : ℝ} {M r : ℝ} (hgM : |g| ≤ M) (hr : 0 ≤ r)
    (hrM : r * M ^ 2 ≤ 1 / 2) :
    |-(r * g * G) / Real.sqrt (1 - r * g ^ 2)| ≤ 2 * r * M * |G| := by
  have h2 : g ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs g]; exact pow_le_pow_left₀ (abs_nonneg _) hgM 2
  have hρ : 1 / 2 ≤ 1 - r * g ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h2 hr]
  have hs : 1 / 2 ≤ Real.sqrt (1 - r * g ^ 2) := by
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hM : 0 ≤ M := (abs_nonneg g).trans hgM
  rw [abs_div, abs_neg, abs_of_pos (by linarith : 0 < Real.sqrt (1 - r * g ^ 2)),
    div_le_iff₀ (by linarith), abs_mul, abs_mul, abs_of_nonneg hr]
  have : r * |g| * |G| ≤ r * M * |G| := by gcongr
  nlinarith [abs_nonneg G, mul_nonneg hr hM, mul_nonneg (mul_nonneg hr hM) (abs_nonneg G)]

/-- `H(ρ|q) = Ent_q(u²)` for `ρ = q u²`. -/
theorem klDiv_sqmul_eq_ent {q u : Torus d → ℝ} {c C B : ℝ} (hc : 0 < c)
    (hbd : ∀ x, c ≤ q x ∧ q x ≤ C) (hqm : Measurable q) (hq1 : ∫ x, q x ∂haar d = 1)
    (hum : AEStronglyMeasurable u (haar d)) (hu0 : ∀ x, 0 ≤ u x) (huB : ∀ x, u x ≤ B)
    (h1 : ∫ x, q x * u x ^ 2 ∂haar d = 1) :
    klDiv (densMeasure fun x => q x * u x ^ 2) (densMeasure q) =
      ent (densMeasure q) (fun x => u x ^ 2) := by
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  have hP : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  have hum2 : AEMeasurable (fun x => u x ^ 2) (haar d) := hum.aemeasurable.pow_const 2
  have hρm : AEMeasurable (fun x => q x * u x ^ 2) (haar d) := hqm.aemeasurable.mul hum2
  have h := klDiv_ratio_eq hρm hqm.aemeasurable (fun x => mul_nonneg (hq0 x).le (sq_nonneg _))
    (fun x => (hq0 x).le) (fun x hx => absurd hx (hq0 x).ne') h1 hq1
  rw [h]
  have hnorm : ∫ x, u x ^ 2 ∂densMeasure q = 1 := by
    rw [integral_densMeasure' (fun x => (hq0 x).le) hq1]; exact h1
  have hac : densMeasure q ≪ haar d := withDensity_absolutelyContinuous _ _
  have hint : Integrable (fun x => u x ^ 2) (densMeasure q) := by
    refine Integrable.of_bound (C := B ^ 2) (hum2.aestronglyMeasurable.mono_ac hac)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hu0 x) (huB x) 2
  rw [ent_normalized (densMeasure q) hint hnorm]
  have hb : AEMeasurable (fun x => ENNReal.ofReal (q x)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hqm.aemeasurable
  have hg : AEMeasurable (fun x => ENNReal.ofReal (klFun (u x ^ 2))) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (measurable_klFun.comp_aemeasurable hum2)
  unfold densMeasure
  rw [lintegral_withDensity_eq_lintegral_mul₀ hb hg]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (hq0 x).le, mul_div_cancel_left₀ _ (hq0 x).ne']

theorem lintegral_four_le {q : Torus d → ℝ} {g' G : Torus d → Fin d → ℝ} {κ Dhat : ℝ}
    (hq0 : ∀ x, 0 ≤ q x) (hκ : 0 ≤ κ)
    (hpt : ∀ x, sqNorm (g' x) ≤ κ / 4 * sqNorm (G x))
    (hD : ∫⁻ x, ENNReal.ofReal (q x * sqNorm (G x)) ∂haar d ≤ ENNReal.ofReal Dhat) :
    ∫⁻ x, ENNReal.ofReal (4 * (q x * sqNorm (g' x))) ∂haar d ≤ ENNReal.ofReal (κ * Dhat) := by
  calc ∫⁻ x, ENNReal.ofReal (4 * (q x * sqNorm (g' x)))
      ≤ ∫⁻ x, ENNReal.ofReal κ * ENNReal.ofReal (q x * sqNorm (G x)) ∂haar d := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hκ]
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left (hpt x) (hq0 x)
        nlinarith
    _ = ENNReal.ofReal κ * ∫⁻ x, ENNReal.ofReal (q x * sqNorm (G x)) ∂haar d :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal κ * ENNReal.ofReal Dhat := by gcongr
    _ = ENNReal.ofReal (κ * Dhat) := (ENNReal.ofReal_mul hκ).symm

theorem quot_arith {ε a M D Er : ℝ} {I₁ I₂ K : ℝ≥0∞} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 < a)
    (hD : 0 ≤ D) (hEr : 0 < Er) (h1 : I₁ ≤ ENNReal.ofReal (4 * a * D))
    (h2 : I₂ ≤ ENNReal.ofReal (32 * (ε * a) ^ 2 * M ^ 2 * D))
    (hK : K = ENNReal.ofReal a * ENNReal.ofReal Er) :
    (ENNReal.ofReal ε * I₁ + ENNReal.ofReal (1 - ε) * I₂) / (2 * (ENNReal.ofReal ε * K)) ≤
      ENNReal.ofReal (2 * D / Er + 16 * ε * a * M ^ 2 * D / Er) := by
  have hnum : ENNReal.ofReal ε * I₁ + ENNReal.ofReal (1 - ε) * I₂ ≤
      ENNReal.ofReal (ε * (4 * a * D) + (1 - ε) * (32 * (ε * a) ^ 2 * M ^ 2 * D)) := by
    have hA : 0 ≤ 4 * a * D := by positivity
    have hB : 0 ≤ 32 * (ε * a) ^ 2 * M ^ 2 * D := by positivity
    rw [ENNReal.ofReal_add (mul_nonneg hε0.le hA) (mul_nonneg (by linarith) hB),
      ENNReal.ofReal_mul hε0.le, ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - ε)]
    gcongr
  have hden : 2 * (ENNReal.ofReal ε * K) = ENNReal.ofReal (2 * ε * a * Er) := by
    rw [hK, ← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hε0.le]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  rw [hden]
  refine (ENNReal.div_le_div_right hnum _).trans ?_
  have hpos : 0 < 2 * ε * a * Er := by positivity
  rw [← ENNReal.ofReal_div_of_pos hpos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ hpos]
  have e : (2 * D / Er + 16 * ε * a * M ^ 2 * D / Er) * (2 * ε * a * Er) =
      4 * ε * a * D + 32 * ε ^ 2 * a ^ 2 * M ^ 2 * D := by
    field_simp; ring
  rw [e]
  nlinarith [show 0 ≤ ε * (32 * (ε * a) ^ 2 * M ^ 2 * D) by positivity]

theorem dilute_bounded (hyp : Hyp V W KV KW) {q : Torus d → ℝ} {c C : ℝ}
    (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C) (hqm : Measurable q)
    (hq1 : ∫ x, q x ∂haar d = 1) (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hD0 : dissipation V W q = 0) (hG0 : gap V W (densMeasure q) = 0)
    {g : Torus d → ℝ} {G : Torus d → Fin d → ℝ} {M a ε Dhat Er : ℝ}
    (hg : IsWeakGrad g G) (hg0 : ∀ x, 0 ≤ g x) (hgM : ∀ x, g x ≤ M)
    (hG : ∀ k, MemLp (fun y => G y k) 2 (haar d))
    (ha : 0 < a) (hZ : a * ∫ x, q x * g x ^ 2 ∂haar d = 1)
    (hEr : ent (densMeasure q) (fun x => g x ^ 2) = ENNReal.ofReal Er) (hEr0 : 0 < Er)
    (hDhat0 : 0 ≤ Dhat)
    (hD : ∫⁻ x, ENNReal.ofReal (q x * sqNorm (G x)) ∂haar d ≤ ENNReal.ofReal Dhat)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hεM : ε * a * M ^ 2 ≤ 1 / 2) :
    ∃ F : Family d, MsAdmissible V W F ∧ densMeasure F.bar = densMeasure q ∧
      msDiss V W F / (2 * (msGap V W F).toENNReal) ≤
        ENNReal.ofReal (2 * Dhat / Er + 16 * ε * a * M ^ 2 * Dhat / Er) := by
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  haveI hPq : IsProbabilityMeasure (densMeasure q) :=
    isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
  have hM0 : 0 ≤ M := (hg0 0).trans (hgM 0)
  have hgabs : ∀ x, |g x| ≤ M := fun x => by rw [abs_of_nonneg (hg0 x)]; exact hgM x
  have hr0 : 0 ≤ ε * a := by positivity
  have hε1' : ε < 1 := by linarith
  have hb0 : 0 < 1 - ε := by linarith
  -- the constants and functions
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.sqrt (1 / (1 - ε)) := ⟨_, rfl⟩
  have hb2 : b ^ 2 = 1 / (1 - ε) := by
    rw [hbdef, Real.sq_sqrt (by positivity)]
  have hb2le : b ^ 2 ≤ 2 := by
    rw [hb2, div_le_iff₀ hb0]; linarith
  have hb0' : 0 ≤ b := by rw [hbdef]; exact Real.sqrt_nonneg _
  obtain ⟨u₁, hu₁def⟩ : ∃ u₁ : Torus d → ℝ, u₁ = fun x => Real.sqrt a * g x := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂def⟩ : ∃ u₂ : Torus d → ℝ,
      u₂ = fun x => b * Real.sqrt (1 - ε * a * g x ^ 2) := ⟨_, rfl⟩
  obtain ⟨g₁, hg₁def⟩ : ∃ g₁ : Torus d → Fin d → ℝ, g₁ = fun x k => Real.sqrt a * G x k :=
    ⟨_, rfl⟩
  obtain ⟨g₂, hg₂def⟩ : ∃ g₂ : Torus d → Fin d → ℝ, g₂ = fun x k =>
      b * (-(ε * a * g x * G x k) / Real.sqrt (1 - ε * a * g x ^ 2)) := ⟨_, rfl⟩
  have hu₁ : IsWeakGrad u₁ g₁ := by rw [hu₁def, hg₁def]; exact hg.cmul _
  have hs := isWeakGrad_sqrt_one_sub hg hgabs hG hr0 hεM
  have hu₂ : IsWeakGrad u₂ g₂ := by rw [hu₂def, hg₂def]; exact hs.cmul b
  have hu₁0 : ∀ x, 0 ≤ u₁ x := fun x => by rw [hu₁def]; exact mul_nonneg (Real.sqrt_nonneg _) (hg0 x)
  have hu₂0 : ∀ x, 0 ≤ u₂ x := fun x => by rw [hu₂def]; exact mul_nonneg hb0' (Real.sqrt_nonneg _)
  have hu₁B : ∀ x, u₁ x ≤ Real.sqrt a * M := fun x => by
    rw [hu₁def]; exact mul_le_mul_of_nonneg_left (hgM x) (Real.sqrt_nonneg _)
  have hgsq : ∀ x, g x ^ 2 ≤ M ^ 2 := fun x => by
    rw [← sq_abs (g x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hgabs x) 2
  have hρ : ∀ x, 1 / 2 ≤ 1 - ε * a * g x ^ 2 := fun x => by
    nlinarith [mul_le_mul_of_nonneg_left (hgsq x) hr0]
  have hu₂B : ∀ x, u₂ x ≤ b := fun x => by
    rw [hu₂def]
    refine mul_le_of_le_one_right hb0' ?_
    rw [Real.sqrt_le_one]
    nlinarith [mul_nonneg hr0 (sq_nonneg (g x))]
  have hg₁2 : ∀ k, MemLp (fun y => g₁ y k) 2 (haar d) := fun k => by
    rw [hg₁def]; exact (hG k).const_mul _
  have hg₂2 : ∀ k, MemLp (fun y => g₂ y k) 2 (haar d) := fun k => by
    refine (hG k).of_le_mul (c := b * (2 * (ε * a) * M))
      (hu₂.aestronglyMeasurable_grad k) (Filter.Eventually.of_forall fun y => ?_)
    rw [hg₂def, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb0']
    have := abs_grad_sqrt_one_sub_le (G := G y k) (hgabs y) hr0 hεM
    calc b * |(-(ε * a * g y * G y k) / Real.sqrt (1 - ε * a * g y ^ 2))|
        ≤ b * (2 * (ε * a) * M * |G y k|) := by gcongr
      _ = b * (2 * (ε * a) * M) * |G y k| := by ring
  have hid : ∀ x, ε * u₁ x ^ 2 + (1 - ε) * u₂ x ^ 2 = 1 := fun x => by
    rw [hu₁def, hu₂def]
    simp only
    rw [mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt (by linarith [hρ x]), hb2]
    field_simp
    ring
  have hρ1 : ∀ x, q x * u₁ x ^ 2 = a * (q x * g x ^ 2) := fun x => by
    rw [hu₁def]; simp only; rw [mul_pow, Real.sq_sqrt ha.le]; ring
  have hint₁ : ∫ x, q x * u₁ x ^ 2 ∂haar d = 1 := by
    simp_rw [hρ1]
    rw [integral_const_mul]; exact hZ
  have hu1sq : (fun x => u₁ x ^ 2) = fun x => a * g x ^ 2 := by
    funext x; rw [hu₁def]; simp only; rw [mul_pow, Real.sq_sqrt ha.le]
  have hgint : Integrable (fun x => g x ^ 2) (densMeasure q) := by
    have hP : IsProbabilityMeasure (densMeasure q) :=
      isProbabilityMeasure_densMeasure' (fun x => (hq0 x).le) hq1
    have hac : densMeasure q ≪ haar d := withDensity_absolutelyContinuous _ _
    refine Integrable.of_bound (C := M ^ 2)
      ((hg.aestronglyMeasurable_fun.pow 2).mono_ac hac) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hgsq x
  have hKeq : klDiv (densMeasure fun x => q x * u₁ x ^ 2) (densMeasure q) =
      ENNReal.ofReal a * ENNReal.ofReal Er := by
    rw [klDiv_sqmul_eq_ent hc hbd hqm hq1 hu₁.aestronglyMeasurable_fun hu₁0 hu₁B hint₁, hu1sq,
      ent_const_mul _ hgint ha.le, hEr]
  have hKpos : 0 < klDiv (densMeasure fun x => q x * u₁ x ^ 2) (densMeasure q) := by
    rw [hKeq]
    exact ENNReal.mul_pos (by simpa using ha) (by simpa using hEr0)
  obtain ⟨hAd, hbar, hquot⟩ := dilute_quotient_le hyp hc hbd hqm hq1 hqH hε0 hε1' hu₁ hu₁0 hu₁B hg₁2
    hu₂ hu₂0 hu₂B hg₂2 hid hint₁ hKpos hD0 hG0
  refine ⟨diluteFam q u₁ u₂ ε, hAd, hbar, hquot.trans ?_⟩
  -- the Fisher informations
  have hI₁ := relFisher_sqrt_mul hc hbd hq1 hqH hu₁ hu₁0 hu₁B hg₁2
  have hI₂ := relFisher_sqrt_mul hc hbd hq1 hqH hu₂ hu₂0 hu₂B hg₂2
  refine quot_arith (M := M) hε0 (by linarith) ha hDhat0 hEr0 ?_ ?_ hKeq
  · rw [hI₁]
    have := lintegral_four_le (q := q) (g' := g₁) (G := G) (κ := 4 * a) (Dhat := Dhat)
      (fun x => (hq0 x).le) (by positivity) (fun x => ?_) hD
    · exact this
    · rw [hg₁def]
      simp only
      rw [sqNorm_smul', Real.sq_sqrt ha.le]
      linarith
  · rw [hI₂]
    have := lintegral_four_le (q := q) (g' := g₂) (G := G) (κ := 32 * (ε * a) ^ 2 * M ^ 2)
      (Dhat := Dhat) (fun x => (hq0 x).le) (by positivity) (fun x => ?_) hD
    · exact this
    · have hv : sqNorm (g₂ x) ≤ b ^ 2 * ((2 * (ε * a) * M) ^ 2 * sqNorm (G x)) := by
        have h1 : sqNorm (g₂ x) = b ^ 2 * sqNorm (fun k => -(ε * a * g x * G x k) /
            Real.sqrt (1 - ε * a * g x ^ 2)) := by
          rw [hg₂def]; exact sqNorm_smul' b _
        rw [h1]
        gcongr
        exact sqNorm_le_of_abs_le fun k => abs_grad_sqrt_one_sub_le (G := G x k) (hgabs x) hr0 hεM
      calc sqNorm (g₂ x) ≤ b ^ 2 * ((2 * (ε * a) * M) ^ 2 * sqNorm (G x)) := hv
        _ ≤ 2 * ((2 * (ε * a) * M) ^ 2 * sqNorm (G x)) :=
            mul_le_mul_of_nonneg_right hb2le (mul_nonneg (sq_nonneg _) (sqNorm_nonneg _))
        _ = 32 * (ε * a) ^ 2 * M ^ 2 / 4 * sqNorm (G x) := by ring

end SharpLSI.FL
