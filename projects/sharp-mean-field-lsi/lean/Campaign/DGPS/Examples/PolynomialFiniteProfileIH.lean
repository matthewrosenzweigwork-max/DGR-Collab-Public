import DGPS.Frontier.STR029.T46

/-! Actual normalized finite profiles over the TRUE cos-one reference at
independent reference parameter zero. Generic T45 is used with its full
normalization coefficients; no cos-three coefficient or PB=0 identity is used. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

def polynomialFiniteProfileDensity (A B C D h t : ℝ) : ℝ :=
  Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t) /
    normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h

def polynomialFiniteProfileReference (h t : ℝ) : ℝ :=
  Real.exp (h * Real.cos t) / normalizer_STR02944 Real.cos (fun _ => 0) h

def polynomialFiniteProfileFisher (A B C D h : ℝ) : ℝ :=
  normInt_STR02933 (fun t => deriv (uFun_STR02945 A B C D 0 0 h) t ^ 2 *
    polynomialFiniteProfileDensity A B C D h t)

def polynomialFiniteProfileEntropy (A B C D h : ℝ) : ℝ :=
  normInt_STR02933 (fun t =>
    (polynomialFiniteProfileDensity A B C D h t / polynomialFiniteProfileReference h t) *
      Real.log (polynomialFiniteProfileDensity A B C D h t / polynomialFiniteProfileReference h t) *
        polynomialFiniteProfileReference h t)

def polynomialFiniteI2 (A B : ℝ) : ℝ :=
  normInt_STR02933 (fun t => deriv (pFun_STR02945 A B) t ^ 2)

def polynomialFiniteI3 (A B C D : ℝ) : ℝ :=
  normInt_STR02933 (fun t => fk1_STR02945 (deriv (pFun_STR02945 A B) t)
    (deriv (qFun_STR02945 C D 0 0) t) (pFun_STR02945 (1 + A) B t) (qFun_STR02945 C D 0 0 t))

def polynomialFiniteI4 (A B C D : ℝ) : ℝ :=
  normInt_STR02933 (fun t => fk2_STR02945 (deriv (pFun_STR02945 A B) t)
    (deriv (qFun_STR02945 C D 0 0) t) (pFun_STR02945 (1 + A) B t) (qFun_STR02945 C D 0 0 t)) -
      polynomialFiniteI2 A B * z2_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0)

def polynomialFiniteH2 (A B C D : ℝ) : ℝ :=
  entC2_STR02945 Real.cos (pFun_STR02945 (1 + A) B) (pFun_STR02945 A B) (qFun_STR02945 C D 0 0)

def polynomialFiniteH3 (A B C D : ℝ) : ℝ :=
  entC3_STR02945 Real.cos (pFun_STR02945 (1 + A) B) (pFun_STR02945 A B) (qFun_STR02945 C D 0 0)

def polynomialFiniteH4 (A B C D : ℝ) : ℝ :=
  entC4_STR02945 Real.cos (pFun_STR02945 (1 + A) B) (pFun_STR02945 A B) (qFun_STR02945 C D 0 0)

private theorem profile_normInt_div (f : ℝ → ℝ) (z : ℝ) :
    normInt_STR02933 (fun t => f t / z) = normInt_STR02933 f / z := by
  have he : (fun t => f t / z) = fun t => z⁻¹ * f t := by funext t; ring
  rw [he, normInt_mul_const_STR02933]
  ring

theorem polynomialFiniteProfileDensity_mass (A B C D h : ℝ)
    (hZ : 0 < normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h) :
    normInt_STR02933 (polynomialFiniteProfileDensity A B C D h) = 1 := by
  unfold polynomialFiniteProfileDensity
  rw [profile_normInt_div]
  exact div_self hZ.ne'

theorem polynomialFiniteProfileReference_mass (h : ℝ)
    (hZ : 0 < normalizer_STR02944 Real.cos (fun _ => 0) h) :
    normInt_STR02933 (polynomialFiniteProfileReference h) = 1 := by
  unfold polynomialFiniteProfileReference
  rw [profile_normInt_div]
  have he : (fun t => Real.exp (h * Real.cos t)) =
      fun t => Real.exp (expArg_STR02944 Real.cos (fun _ => 0) h t) := by
    funext t
    simp only [expArg_STR02944, mul_zero, add_zero]
  rw [he]
  exact div_self hZ.ne'

theorem polynomialFiniteProfileFisher_eq (A B C D h : ℝ) :
    polynomialFiniteProfileFisher A B C D h =
      normInt_STR02933 (fun t => (h * deriv (pFun_STR02945 A B) t +
        h ^ 2 * deriv (qFun_STR02945 C D 0 0) t) ^ 2 *
          Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)) /
        normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h := by
  unfold polynomialFiniteProfileFisher
  have he (t : ℝ) : deriv (uFun_STR02945 A B C D 0 0 h) t ^ 2 *
      polynomialFiniteProfileDensity A B C D h t =
      (normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h)⁻¹ *
        ((h * deriv (pFun_STR02945 A B) t + h ^ 2 * deriv (qFun_STR02945 C D 0 0) t) ^ 2 *
          Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)) := by
    rw [deriv_uFun_STR02945]
    unfold polynomialFiniteProfileDensity
    ring
  rw [normInt_congr_STR02945 he, normInt_mul_const_STR02933, div_eq_inv_mul]

theorem polynomialFiniteProfileEntropy_eq (A B C D h : ℝ)
    (hZ : 0 < normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h)
    (hZb : 0 < normalizer_STR02944 Real.cos (fun _ => 0) h) :
    polynomialFiniteProfileEntropy A B C D h =
      normInt_STR02933 (fun t => uFun_STR02945 A B C D 0 0 h t *
        Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)) /
        normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h -
      Real.log (normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h) +
      Real.log (normalizer_STR02944 Real.cos (fun _ => 0) h) := by
  let Z := normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h
  let Zb := normalizer_STR02944 Real.cos (fun _ => 0) h
  have key (t : ℝ) :
      (polynomialFiniteProfileDensity A B C D h t / polynomialFiniteProfileReference h t) *
        Real.log (polynomialFiniteProfileDensity A B C D h t / polynomialFiniteProfileReference h t) *
          polynomialFiniteProfileReference h t =
      Z⁻¹ * (uFun_STR02945 A B C D 0 0 h t *
        Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)) +
      ((Real.log Zb - Real.log Z) * Z⁻¹) *
        Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t) := by
    have hE := Real.exp_pos (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)
    have hEb := Real.exp_pos (h * Real.cos t)
    have hxpos : 0 < Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B)
        (qFun_STR02945 C D 0 0) h t) / Z := div_pos hE hZ
    have hypos : 0 < Real.exp (h * Real.cos t) / Zb := div_pos hEb hZb
    have harg : expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t =
        h * Real.cos t + uFun_STR02945 A B C D 0 0 h t := by
      unfold expArg_STR02944 uFun_STR02945 pFun_STR02945
      ring
    have hlog : Real.log (Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B)
        (qFun_STR02945 C D 0 0) h t) / Z / (Real.exp (h * Real.cos t) / Zb)) =
        uFun_STR02945 A B C D 0 0 h t - Real.log Z + Real.log Zb := by
      rw [Real.log_div hxpos.ne' hypos.ne', Real.log_div hE.ne' hZ.ne',
        Real.log_div hEb.ne' hZb.ne', Real.log_exp, Real.log_exp, harg]
      ring
    change (Real.exp _ / Z / (Real.exp (h * Real.cos t) / Zb)) *
      Real.log (Real.exp _ / Z / (Real.exp (h * Real.cos t) / Zb)) *
        (Real.exp (h * Real.cos t) / Zb) = _
    calc
      _ = ((Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t) /
          Z / (Real.exp (h * Real.cos t) / Zb)) * (Real.exp (h * Real.cos t) / Zb)) *
          Real.log (Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B)
            (qFun_STR02945 C D 0 0) h t) / Z / (Real.exp (h * Real.cos t) / Zb)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hypos.ne', hlog]; ring
  have hc1 : Continuous (fun t => uFun_STR02945 A B C D 0 0 h t *
      Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h t)) := by
    unfold uFun_STR02945 expArg_STR02944 pFun_STR02945 qFun_STR02945
    fun_prop
  have hc2 : Continuous (fun t => Real.exp (expArg_STR02944 (pFun_STR02945 (1 + A) B)
      (qFun_STR02945 C D 0 0) h t)) := by
    unfold expArg_STR02944 pFun_STR02945 qFun_STR02945
    fun_prop
  unfold polynomialFiniteProfileEntropy
  rw [normInt_congr_STR02945 key, normInt_lin2_STR02945 _ _ hc1 hc2]
  change Z⁻¹ * _ + ((Real.log Zb - Real.log Z) * Z⁻¹) * Z = _
  dsimp only [Z, Zb]
  field_simp [hZ.ne']
  ring

private theorem polynomialFiniteProfile_admissible (R A B C D : ℝ)
    (hA : |A| ≤ R) (hB : |B| ≤ R) (hC : |C| ≤ R) (hD : |D| ≤ R) :
    let M := Mbound_STR02945 (max R 0 + 1)
    IsAdmissible_STR02944 M Real.cos ∧
      IsAdmissible_STR02944 M (pFun_STR02945 (1 + A) B) ∧
      IsAdmissible_STR02944 M (pFun_STR02945 A B) ∧
      IsAdmissible_STR02944 M (qFun_STR02945 C D 0 0) := by
  let S := max R 0 + 1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hRS : R ≤ S := (le_max_left R 0).trans (by dsimp [S]; linarith)
  have h1 : |(1 : ℝ)| ≤ S := by
    rw [abs_one]
    dsimp [S]
    linarith [le_max_right R (0 : ℝ)]
  have h0 : |(0 : ℝ)| ≤ S := by simpa using hS
  have hAA : |1 + A| ≤ S := by
    calc _ ≤ |1| + |A| := abs_add_le _ _
      _ ≤ 1 + R := by rw [abs_one]; linarith
      _ ≤ S := by dsimp [S]; linarith [le_max_left R 0]
  have hb := pFun_admissible_STR02945 S h1 h0
  have hb' : IsAdmissible_STR02944 (Mbound_STR02945 S) Real.cos := by
    have he : pFun_STR02945 1 0 = Real.cos := by funext t; simp [pFun_STR02945]
    rw [he] at hb
    exact hb
  exact ⟨hb', pFun_admissible_STR02945 S hAA (hB.trans hRS),
    pFun_admissible_STR02945 S (hA.trans hRS) (hB.trans hRS),
    qFun_admissible_STR02945 S (hC.trans hRS) (hD.trans hRS) h0 h0⟩

/-- Actual normalized cos-one reference/competitor information. One common
interval and error constant precede EVERY coefficient in the compact box.
Raw entropy coefficients retain the nonzero Haar correlation p*cos. -/
theorem polynomialFiniteProfile_information_expansion_raw (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ A B C D : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R → |D| ≤ R →
        ∀ h : ℝ, |h| ≤ h0 →
        0 < normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h ∧
        0 < normalizer_STR02944 Real.cos (fun _ => 0) h ∧
        normInt_STR02933 (polynomialFiniteProfileDensity A B C D h) = 1 ∧
        normInt_STR02933 (polynomialFiniteProfileReference h) = 1 ∧
        |polynomialFiniteProfileFisher A B C D h -
          (polynomialFiniteI2 A B * h ^ 2 + polynomialFiniteI3 A B C D * h ^ 3 +
            polynomialFiniteI4 A B C D * h ^ 4)| ≤ K * |h| ^ 5 ∧
        |polynomialFiniteProfileEntropy A B C D h -
          (polynomialFiniteH2 A B C D * h ^ 2 + polynomialFiniteH3 A B C D * h ^ 3 +
            polynomialFiniteH4 A B C D * h ^ 4)| ≤ K * |h| ^ 5 := by
  let S := max R 0 + 1
  let M := Mbound_STR02945 S
  obtain ⟨hI, hIpos, KI, hKI, hFisher⟩ := fisher_generic_STR02945 M
  obtain ⟨hE, hEpos, KE, hKE, hEntropy⟩ :=
    entropy_full_generic_STR02945 M (zero_admissible_STR02945 S)
  obtain ⟨hZ, hZpos, CZ, _, hNormalizer⟩ := str029_44_uniform_exponential_normalizer_expansions M
  refine ⟨min hI (min hE hZ), lt_min hIpos (lt_min hEpos hZpos), KI + KE,
    add_nonneg hKI hKE, fun A B C D hA hB hC hD h hh => ?_⟩
  obtain ⟨hb, hv, hp, hq⟩ := polynomialFiniteProfile_admissible R A B C D hA hB hC hD
  have hhI : |h| ≤ hI := hh.trans (min_le_left _ _)
  have hhE : |h| ≤ hE := hh.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhZ : |h| ≤ hZ := hh.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhalf := (hNormalizer _ _ hv hq h hhZ).2.2.2.1
  have hhalfb := (hNormalizer _ _ hb (zero_admissible_STR02945 S) h hhZ).2.2.2.1
  have hNp : 0 < normalizer_STR02944 (pFun_STR02945 (1 + A) B) (qFun_STR02945 C D 0 0) h := by
    linarith [(abs_le.mp hhalf).1]
  have hNbp : 0 < normalizer_STR02944 Real.cos (fun _ => 0) h := by
    linarith [(abs_le.mp hhalfb).1]
  have hIbound := hFisher _ _ _ _ hv hq (deriv_pFun_cont_STR02945 A B)
    (deriv_qFun_cont_STR02945 C D 0 0) (admissible_deriv_bound_STR02945 hp)
    (admissible_deriv_bound_STR02945 hq) h hhI
  have hEbound := hEntropy _ _ _ _ hb hv hp hq h hhE
  refine ⟨hNp, hNbp, polynomialFiniteProfileDensity_mass A B C D h hNp,
    polynomialFiniteProfileReference_mass h hNbp, ?_, ?_⟩
  · rw [polynomialFiniteProfileFisher_eq]
    exact hIbound.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKE) (by positivity))
  · rw [polynomialFiniteProfileEntropy_eq A B C D h hNp hNbp]
    exact hEbound.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKI) (by positivity))

end DGPS.Examples.PolynomialSpecies
