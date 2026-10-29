import SharpSymmetricLSI.Paper.LemmaA2_29

/-!
# R25 Lemma A.2, part 30: assembly of `kernel_approximation`

`K_R` is the square truncation (at level `N_R`) of the double eigen-series of
`K_{t_R} = (P_{t_R} ⊗ P_{t_R}) K`, `t_R = 1/(R+1)`, with `N_R` so large that the truncation is
`1/(R+1)`-close in `C¹`. Then `K_R → K` uniformly (`K_t → K` uniformly), in `H¹(μ⊗μ)` (energy
convergence of `K_t` and `C¹`-closeness of the truncation), with uniform `C¹` bounds (the
semigroup Lipschitz bound); the diagonal statements follow.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **(6.4) and Lemma A.2.** -/
theorem kernel_approximation_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ KR : ℕ → Torus d → Torus d → ℝ,
      (∀ R, ∃ (s : Finset ℕ) (a : ℕ → ℕ → ℝ), (∀ i j, a i j = a j i) ∧
        ∀ x y, KR R x y = ∑ i ∈ s, ∑ j ∈ s, a i j * e (i + 1) x * e (j + 1) y) ∧
      Tendsto (fun R => eLpNorm (fun X => kerC2 (KR R) X - kerC2 (centeredKernel W μ) X) ⊤
        (Measure.pi fun _ : Fin 2 => (μ : Measure (Torus d)))) atTop (𝓝 0) ∧
      Tendsto (fun R => ∫⁻ X, ENNReal.ofReal ((kerC2 (KR R) X - kerC2 (centeredKernel W μ) X) ^ 2 +
          gradSqC (fun Y => kerC2 (KR R) Y - kerC2 (centeredKernel W μ) Y) X)
        ∂Measure.pi (fun _ : Fin 2 => (μ : Measure (Torus d)))) atTop (𝓝 0) ∧
      (∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ R,
        eLpNorm (kerC2 (KR R)) ⊤ (Measure.pi fun _ : Fin 2 => (μ : Measure (Torus d))) +
        eLpNorm (fun X => Real.sqrt (gradSqC (kerC2 (KR R)) X)) ⊤
          (Measure.pi fun _ : Fin 2 => (μ : Measure (Torus d))) ≤ B) ∧
      Tendsto (fun R => eLpNorm (fun x => KR R x x - centeredKernel W μ x x) ⊤
        (μ : Measure (Torus d))) atTop (𝓝 0) ∧
      (∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ R,
        eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad (fun z => KR R z z) x))) ⊤
          (μ : Measure (Torus d)) ≤ B) := by
  obtain ⟨ρ, c, C, Lσ, hμρ, hρ, hρc, hσ⟩ := refSetup hyp hμ
  obtain ⟨K, hK0, hQ⟩ := semiconvex_negLog hyp hμ ⟨fun x => hρ.pos.trans_le (hρ.lower x), hμρ⟩
  rw [hμρ] at he ⊢
  haveI := hρ.isProb
  set P := densMeasure ρ
  set Kf := centeredKernel W P
  have hKc : Continuous (Function.uncurry Kf) := continuous_centeredKernel_A2 hyp P
  obtain ⟨BK, hBK⟩ := centeredKernel_bdd hyp P
  obtain ⟨LK, hLK0, hL1, hL2⟩ := centeredKernel_lip hyp P
  have hsymm : ∀ x y, Kf x y = Kf y x := centeredKernel_symm_A2 hyp P
  have hcent : ∀ y, ∫ x, Kf x y ∂P = 0 := integral_centeredKernel_left hyp P
  have hBK0 : 0 ≤ BK := (abs_nonneg _).trans (hBK 0 0)
  -- `C¹` representatives
  obtain ⟨Cc, q, hc1⟩ := c1rep hρ hρc hσ hd
  choose eC heC1 heCae heCb _ using fun j => hc1 (e j) (lam j) (isEig_of_basis he j)
  set M : ℕ → ℝ := fun j => Cc * (1 + lam j) ^ q
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => refLam_nonneg hρ he j
  have hM : ∀ j x, |eC j x| ≤ M j := fun j x =>
    le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (heCb j x)
  have hCc : 0 ≤ Cc := by
    have h0 := (abs_nonneg _).trans (hM 0 0)
    have : 0 < (1 + lam 0) ^ q := pow_pos (by linarith [hlam0 0]) q
    exact nonneg_of_mul_nonneg_left h0 this
  have hM0 : ∀ j, 0 ≤ M j := fun j => mul_nonneg hCc (pow_nonneg (by linarith [hlam0 j]) q)
  set M' : ℕ → ℝ := fun j => d * M j
  have hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j := by
    intro j x
    refine (norm_fderiv_le_sum _ x).trans ?_
    have hi : ∀ i, |fderiv ℝ (eC j ∘ liftT) x (Pi.single i 1)| ≤ M j := by
      intro i
      rw [← fderiv_lift_repTorus]
      refine (abs_le_sqrt_sqNorm (fun k => cpartial (eC j) k (liftT x)) i).trans ?_
      exact le_trans (le_add_of_nonneg_left (abs_nonneg _)) (heCb j _)
    calc ∑ i, |fderiv ℝ (eC j ∘ liftT) x (Pi.single i 1)| ≤ ∑ _i : Fin d, M j :=
          Finset.sum_le_sum fun i _ => hi i
      _ = M' j := by simp [M']
  have hS : ∀ t, 0 < t → Summable (fun j => Real.exp (-t * lam j) * M j) ∧
      Summable (fun j => Real.exp (-t * lam j) * M' j) := fun t ht =>
    ⟨summable_exp_poly hρ he hd ht Cc hCc q,
      ((summable_exp_poly hρ he hd ht Cc hCc q).mul_left (d : ℝ)).congr fun j => by
        simp only [M']; ring⟩
  -- times and truncation levels
  set tR : ℕ → ℝ := fun R => 1 / ((R : ℝ) + 1)
  have htR : ∀ R, 0 < tR R := fun R => by positivity
  have htR1 : ∀ R, tR R ≤ 1 := fun R => by
    simp only [tR]; rw [div_le_one (by positivity)]; linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)]
  have htR0 : Tendsto tR atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set g : ℕ → ℕ → ℝ := fun R j => Real.exp (-tR R * lam j)
  have hgM0 : ∀ R j, 0 ≤ g R j * M j := fun R j => mul_nonneg (Real.exp_pos _).le (hM0 j)
  have hgM0' : ∀ R j, 0 ≤ g R j * M' j := fun R j =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (Nat.cast_nonneg _) (hM0 j))
  have hN : ∀ R, ∃ N,
      BK * tailW (fun i => g R i * M i) (fun j => g R j * M j) (N + 1) ≤ tR R ∧
      BK * tailW (fun i => g R i * M' i) (fun j => g R j * M j) (N + 1) ≤ tR R := by
    intro R
    have hε : 0 < tR R / (BK + 1) := by have := htR R; positivity
    have h1 := ((tendsto_tailW (hgM0 R) (hgM0 R) (hS _ (htR R)).1 (hS _ (htR R)).1).comp
      (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds hε)
    have h2 := ((tendsto_tailW (hgM0' R) (hgM0 R) (hS _ (htR R)).2 (hS _ (htR R)).1).comp
      (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds hε)
    obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
    have hfin : ∀ x : ℝ, x < tR R / (BK + 1) → BK * x ≤ tR R := fun x hx => by
      have h3 : BK * x ≤ BK * (tR R / (BK + 1)) := mul_le_mul_of_nonneg_left hx.le hBK0
      have h4 : BK * (tR R / (BK + 1)) ≤ tR R := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith [htR R]
      linarith
    exact ⟨N, hfin _ hN1, hfin _ hN2⟩
  choose N hNb using hN
  -- the kernels
  set Kt' : ℕ → Torus d → Torus d → ℝ := fun R => Kt P e eC lam (tR R) Kf
  set KRc : ℕ → Torus d → Torus d → ℝ := fun R => KtN P e eC lam (tR R) Kf (N R + 1)
  set T : ℕ → ℕ → ℝ := fun i j => ∫ y', (∫ x', Kf x' y' * e i x' ∂P) * e j y' ∂P
  set a : ℕ → ℕ → ℕ → ℝ := fun R i j => g R (i + 1) * g R (j + 1) * T (i + 1) (j + 1)
  set KR : ℕ → Torus d → Torus d → ℝ := fun R x y =>
    ∑ i ∈ Finset.range (N R), ∑ j ∈ Finset.range (N R), a R i j * e (i + 1) x * e (j + 1) y
  have hT0l : ∀ j, ∫ y', (∫ x', Kf x' y' * e 0 x' ∂P) * e j y' ∂P = 0 :=
    T_zero_left hρ he hKc hsymm hcent
  have hT0r : ∀ i, ∫ y', (∫ x', Kf x' y' * e i x' ∂P) * e 0 y' ∂P = 0 :=
    T_zero_right hρ he hKc hsymm hcent
  have hKRc : ∀ R x y, KRc R x y = ∑ i ∈ Finset.range (N R), ∑ j ∈ Finset.range (N R),
      a R i j * eC (i + 1) x * eC (j + 1) y := by
    intro R x y
    simp only [KRc, KtN]
    rw [Finset.sum_range_succ']
    simp only [hT0l, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ']
    simp only [hT0r, mul_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a, g, T]
  -- a.e. identifications
  have hgood : ∀ᵐ x ∂P, ∀ i, e i x = eC i x :=
    ae_all_iff.mpr fun i => (heCae i).mono fun x hx => hx.symm
  have hgoodV : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ i, e i x = eC i x := hρ.ac'.ae_le hgood
  have hKRe : ∀ R x y, (∀ i, e i x = eC i x) → (∀ i, e i y = eC i y) → KR R x y = KRc R x y := by
    intro R x y hx hy; rw [hKRc]; simp only [KR, hx, hy]
  have hpiE : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => P), ∀ R, kerC2 (KR R) X = kerC2 (KRc R) X :=
    (ae_pi_two_coord hgood).mono fun X hX R => hKRe R _ _ hX.1 hX.2
  have hflatE : ∀ᵐ Y ∂(volume : Measure (UnitAddTorus (Fin 2 × Fin d))), ∀ R,
      (kerC2 (KR R) ∘ unflat) Y = (kerC2 (KRc R) ∘ unflat) Y :=
    (ae_flat_two_coord hgoodV).mono fun Y hY R => hKRe R _ _ hY.1 hY.2
  have hdiagE : ∀ᵐ x ∂P, ∀ R, KR R x x = KRc R x x := hgood.mono fun x hx R => hKRe R x x hx hx
  have hdiagEV : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ R, KR R x x = KRc R x x :=
    hgoodV.mono fun x hx R => hKRe R x x hx hx
  -- bounds for `K_t` and its truncations
  have KP := fun R => Kt_props hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 (htR R) hKc hBK hLK0 hL1 hL2
  have KC := fun R => Kt_KtN_close hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
    (htR R) (N R + 1)
  have hKsym : ∀ R x y, Kt' R x y = Kt' R y x := fun R x y =>
    Kt_symm hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 hsymm (htR R) x y
  have hKNsym : ∀ R x y, KRc R x y = KRc R y x := fun R x y =>
    KtN_symm hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 hsymm (N R + 1) x y
  have hexp : ∀ R, Real.exp (K * tR R) * LK ≤ Real.exp K * LK := fun R =>
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [htR1 R])) hLK0
  set L0 := Real.exp K * LK + 1
  have hL00 : 0 ≤ L0 := by positivity
  have hclose : ∀ R x y, |Kt' R x y - KRc R x y| ≤ tR R := fun R x y =>
    ((KC R).1 x y).trans (hNb R).1
  have hDx : ∀ R y a b, (KRc R (liftT a) y - Kt' R (liftT a) y) -
      (KRc R (liftT b) y - Kt' R (liftT b) y) ≤ tR R * dE a b := fun R y a b => by
    have := ((KC R).2 y b a).trans (mul_le_mul_of_nonneg_right (hNb R).2 (dE_nonneg _ _))
    rw [dE_symm'] at this; simp only [Kt', KRc] at this ⊢; linarith
  have hDy : ∀ R x a b, (KRc R x (liftT a) - Kt' R x (liftT a)) -
      (KRc R x (liftT b) - Kt' R x (liftT b)) ≤ tR R * dE a b := fun R x a b => by
    have := hDx R x a b
    rwa [hKNsym R (liftT a) x, hKNsym R (liftT b) x, hKsym R (liftT a) x, hKsym R (liftT b) x] at this
  have hKRcx : ∀ R y a b, KRc R (liftT a) y - KRc R (liftT b) y ≤ L0 * dE a b := fun R y a b => by
    have h1 := (KP R).2.1 y a b
    have h2 := hDx R y a b
    have h3 := mul_le_mul_of_nonneg_right (hexp R) (dE_nonneg a b)
    have h4 := mul_le_mul_of_nonneg_right (htR1 R) (dE_nonneg a b)
    simp only [Kt'] at h2; simp only [L0]; nlinarith
  have hKRcy : ∀ R x a b, KRc R x (liftT a) - KRc R x (liftT b) ≤ L0 * dE a b := fun R x a b => by
    rw [hKNsym R x, hKNsym R x]; exact hKRcx R x a b
  have hKRcb : ∀ R x y, |KRc R x y| ≤ BK + 1 := fun R x y => by
    have h1 := (KP R).1 x y
    have h2 := hclose R x y
    have h3 := htR1 R
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith
  have hKRcc : ∀ R, Continuous (Function.uncurry (KRc R)) := fun R =>
    continuous_uncurry_of_lip hd hL00 hL00 (hKRcx R) (hKRcy R)
  have hKtc : ∀ R, Continuous (Function.uncurry (Kt' R)) := fun R =>
    continuous_Kt hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 (htR R)
  have hU := uniform_Kt hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 htR htR1 htR0
  have htRe : ∀ ε > 0, ∀ᶠ R in atTop, tR R ≤ ε := fun ε hε =>
    (htR0.eventually (gt_mem_nhds hε)).mono fun R hR => hR.le
  -- the sup bound of `K_R - K`
  have hsup : ∀ ε > 0, ∀ᶠ R in atTop, ∀ x y, |KRc R x y - Kf x y| ≤ ε := by
    intro ε hε
    obtain ⟨N1, hN1⟩ := hU (ε / 2) (by positivity)
    filter_upwards [htRe (ε / 2) (by positivity), eventually_ge_atTop N1] with R hR hRN x y
    have h1 := hN1 R hRN x y
    have h2 := hclose R x y
    calc |KRc R x y - Kf x y| ≤ |KRc R x y - Kt' R x y| + |Kt' R x y - Kf x y| := abs_sub_le _ _ _
      _ ≤ ε := by rw [abs_sub_comm] at h2; linarith
  -- the gradient of `K_R` on `Config 2 d`
  have hgradKR : ∀ R, ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => P), ∀ k,
      weakGradC (kerC2 (KR R)) X 0 k = lipGrad (fun x => KRc R x (X 1)) (X 0) k ∧
      weakGradC (kerC2 (KR R)) X 1 k = lipGrad (fun y => KRc R (X 0) y) (X 1) k := by
    intro R
    have hw := isWeakGrad_lipGrad (continuous_kerC2_unflat (hKRcc R))
      (lipschitz_kerC2 hL00 hL00 (hKRcx R) (hKRcy R))
    have hcon := weakGrad_congr_ae ⟨_, hw⟩ (hflatE.mono fun Y hY => (hY R).symm)
    have h1 : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => P),
        weakGrad (kerC2 (KR R) ∘ unflat) (flat X) = weakGrad (kerC2 (KRc R) ∘ unflat) (flat X) :=
      ae_pi_of_ae_flat hρ.ac hcon.2
    filter_upwards [h1, weakGradC_kerC_ae hρ.ac (hKRcc R) hL00 hL00 (hKRcx R) (hKRcy R)]
      with X hX1 hX2 k
    simp only [weakGradC] at hX2 ⊢
    rw [hX1]; exact hX2 k
  -- clause (1)
  refine ⟨KR, fun R => ⟨Finset.range (N R), a R, fun i j => ?_, fun x y => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [a, T]
    rw [T_symm_A2 hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2 hsymm (i + 1) (j + 1)]
    ring
  -- clause (2): uniform convergence
  · refine tendsto_zero_of_forall_real fun ε hε => ?_
    filter_upwards [hsup ε hε] with R hR
    refine eLpNorm_top_le_of_ae (g := fun X => kerC2 (KRc R) X - kerC2 Kf X)
      ((continuous_kerC2 (hKRcc R)).sub (continuous_kerC2 hKc)).aestronglyMeasurable
      (hpiE.mono fun X hX => by rw [hX R]) (Eventually.of_forall fun X => hR _ _)
  -- clause (3): `H¹` convergence
  · set F : ℕ → Torus d → Torus d → ℝ := fun R x y => Kt' R x y - Kf x y
    set Gd : ℕ → Torus d → Torus d → ℝ := fun R x y => KRc R x y - Kt' R x y
    set Lc := Real.exp K * LK + LK + 1
    have hLc : 0 ≤ Lc := by positivity
    have hFx : ∀ R y a b, F R (liftT a) y - F R (liftT b) y ≤ Lc * dE a b := fun R y a b => by
      have h1 := (KP R).2.1 y a b; have h2 := hL1 y b a; rw [dE_symm'] at h2
      have h3 := mul_le_mul_of_nonneg_right (hexp R) (dE_nonneg a b)
      simp only [F, Kt', Lc]; nlinarith [dE_nonneg a b]
    have hFy : ∀ R x a b, F R x (liftT a) - F R x (liftT b) ≤ Lc * dE a b := fun R x a b => by
      have h1 := (KP R).2.2.1 x a b; have h2 := hL2 x b a; rw [dE_symm'] at h2
      have h3 := mul_le_mul_of_nonneg_right (hexp R) (dE_nonneg a b)
      simp only [F, Kt', Lc]; nlinarith [dE_nonneg a b]
    have hGx : ∀ R y a b, Gd R (liftT a) y - Gd R (liftT b) y ≤ Lc * dE a b := fun R y a b => by
      have := hDx R y a b
      have h4 := mul_le_mul_of_nonneg_right (htR1 R) (dE_nonneg a b)
      simp only [Gd, Lc]; nlinarith [dE_nonneg a b, mul_nonneg (mul_nonneg (Real.exp_pos K).le hLK0) (dE_nonneg a b), mul_nonneg hLK0 (dE_nonneg a b)]
    have hGy : ∀ R x a b, Gd R x (liftT a) - Gd R x (liftT b) ≤ Lc * dE a b := fun R x a b => by
      have := hDy R x a b
      have h4 := mul_le_mul_of_nonneg_right (htR1 R) (dE_nonneg a b)
      simp only [Gd, Lc]; nlinarith [dE_nonneg a b, mul_nonneg (mul_nonneg (Real.exp_pos K).le hLK0) (dE_nonneg a b), mul_nonneg hLK0 (dE_nonneg a b)]
    have hFc : ∀ R, Continuous (Function.uncurry (F R)) := fun R => (hKtc R).sub hKc
    have hGc : ∀ R, Continuous (Function.uncurry (Gd R)) := fun R => (hKRcc R).sub (hKtc R)
    set Bsum : ℕ → Config 2 d → ℝ := fun R X =>
      sqNorm (lipGrad (fun x => F R x (X 1)) (X 0)) + sqNorm (lipGrad (fun y => F R (X 0) y) (X 1))
    -- the pointwise bound
    have hpt : ∀ R s0, (∀ x y, |KRc R x y - Kf x y| ≤ s0) → ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => P),
        (kerC2 (KR R) X - kerC2 Kf X) ^ 2 + gradSqC (fun Y => kerC2 (KR R) Y - kerC2 Kf Y) X ≤
          s0 ^ 2 + 4 * d * (tR R * d) ^ 2 + 2 * Bsum R X := by
      intro R s0 hs0
      have hsum : (fun Y => kerC2 (KR R) Y - kerC2 Kf Y) ∘ unflat =ᵐ[volume]
          kerC2 (fun x y => Gd R x y + F R x y) ∘ unflat := by
        filter_upwards [hflatE] with Y hY
        have := hY R
        simp only [Function.comp] at this ⊢
        rw [this]; simp only [kerC2, Gd, F]; ring
      have hwsum := isWeakGrad_lipGrad (continuous_kerC2_unflat (G := fun x y => Gd R x y + F R x y) ((hGc R).add (hFc R)))
        (lipschitz_kerC2 (L₁ := 2 * Lc) (L₂ := 2 * Lc) (by positivity) (by positivity)
          (fun y a b => by have := hGx R y a b; have := hFx R y a b; linarith)
          (fun x a b => by have := hGy R x a b; have := hFy R x a b; linarith))
      have hcon := weakGrad_congr_ae ⟨_, hwsum⟩ hsum.symm
      have h1 : ∀ᵐ X ∂Measure.pi (fun _ : Fin 2 => P),
          weakGrad ((fun Y => kerC2 (KR R) Y - kerC2 Kf Y) ∘ unflat) (flat X) =
            weakGrad (kerC2 (fun x y => Gd R x y + F R x y) ∘ unflat) (flat X) :=
        ae_pi_of_ae_flat hρ.ac hcon.2
      filter_upwards [hpiE, h1, weakGradC_add_ae hρ.ac (hGc R) (hFc R) hLc (hGx R) (hGy R)
        (hFx R) (hFy R)] with X hX hX1 hX2
      have hA : ∀ i k, (weakGradC (fun Y => kerC2 (KR R) Y - kerC2 Kf Y) X i k) =
          weakGradC (kerC2 fun x y => Gd R x y + F R x y) X i k := fun i k => by
        simp only [weakGradC]; rw [hX1]
      have hAb : ∀ i k, |(if i = 0 then lipGrad (fun x => Gd R x (X 1)) (X 0) k
          else lipGrad (fun y => Gd R (X 0) y) (X 1) k)| ≤ tR R * d := by
        intro i k
        split_ifs
        · exact slice_lipGrad_bound hd (htR R).le (fun a b => by
            have := hDx R (X 1) a b; simp only [Gd]; linarith) _ k
        · exact slice_lipGrad_bound hd (htR R).le (fun a b => by
            have := hDy R (X 0) a b; simp only [Gd]; linarith) _ k
      have hsq : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by
        nlinarith [sq_nonneg (u - v)]
      have hgrad : gradSqC (fun Y => kerC2 (KR R) Y - kerC2 Kf Y) X ≤
          4 * d * (tR R * d) ^ 2 + 2 * Bsum R X := by
        simp only [gradSqC, Fin.sum_univ_two, hA, (hX2 _).1, (hX2 _).2]
        have e0 : ∀ k, (lipGrad (fun x => Gd R x (X 1)) (X 0) k +
            lipGrad (fun x => F R x (X 1)) (X 0) k) ^ 2 ≤
            2 * (tR R * d) ^ 2 + 2 * lipGrad (fun x => F R x (X 1)) (X 0) k ^ 2 := fun k => by
          have := hAb 0 k; simp only [if_true] at this
          have h2 : lipGrad (fun x => Gd R x (X 1)) (X 0) k ^ 2 ≤ (tR R * d) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          nlinarith [hsq (lipGrad (fun x => Gd R x (X 1)) (X 0) k) (lipGrad (fun x => F R x (X 1)) (X 0) k)]
        have e1 : ∀ k, (lipGrad (fun y => Gd R (X 0) y) (X 1) k +
            lipGrad (fun y => F R (X 0) y) (X 1) k) ^ 2 ≤
            2 * (tR R * d) ^ 2 + 2 * lipGrad (fun y => F R (X 0) y) (X 1) k ^ 2 := fun k => by
          have := hAb 1 k; simp only [one_ne_zero, if_false] at this
          have h2 : lipGrad (fun y => Gd R (X 0) y) (X 1) k ^ 2 ≤ (tR R * d) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
          nlinarith [hsq (lipGrad (fun y => Gd R (X 0) y) (X 1) k) (lipGrad (fun y => F R (X 0) y) (X 1) k)]
        have s0' := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => e0 k
        have s1' := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => e1 k
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum] at s0' s1'
        simp only [Bsum, sqNorm]
        nlinarith
      have hval : (kerC2 (KR R) X - kerC2 Kf X) ^ 2 ≤ s0 ^ 2 := by
        rw [hX R]; simp only [kerC2]
        rw [← sq_abs]
        have h := hs0 (X 0) (X 1)
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    -- the integral of `Bsum`
    have hBm : ∀ R, Measurable fun p : Torus d × Torus d =>
        sqNorm (lipGrad (fun x => F R x p.2) p.1) + sqNorm (lipGrad (fun y => F R p.1 y) p.2) :=
      fun R => (Finset.measurable_sum _ fun k _ => ((measurable_slice_lipGrad (hFc R) k).1).pow_const 2).add
        (Finset.measurable_sum _ fun k _ => ((measurable_slice_lipGrad (hFc R) k).2).pow_const 2)
    have hBb : ∀ R (p : Torus d × Torus d), |sqNorm (lipGrad (fun x => F R x p.2) p.1) +
        sqNorm (lipGrad (fun y => F R p.1 y) p.2)| ≤ 2 * (d * (Lc * d) ^ 2) := fun R (p : Torus d × Torus d) => by
      rw [abs_of_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
      have h1 := sqNorm_le_of_abs_le (fun k => slice_lipGrad_bound (f := fun x => F R x p.2) hd hLc (hFx R p.2) p.1 k)
      have h2 := sqNorm_le_of_abs_le (fun k => slice_lipGrad_bound (f := fun y => F R p.1 y) hd hLc (hFy R p.1) p.2 k)
      linarith
    have hBint : ∀ R, ∫⁻ X, ENNReal.ofReal (Bsum R X) ∂Measure.pi (fun _ : Fin 2 => P) =
        ENNReal.ofReal ((∫ y, (∫ x, sqNorm (lipGrad (fun x => F R x y) x) ∂P) ∂P) +
          ∫ y, (∫ x, sqNorm (lipGrad (fun x => F R y x) x) ∂P) ∂P) := by
      intro R
      rw [lintegral_pi_two]
      have hint : Integrable (fun p : Torus d × Torus d =>
          sqNorm (lipGrad (fun x => F R x p.2) p.1) + sqNorm (lipGrad (fun y => F R p.1 y) p.2))
          (P.prod P) :=
        (integrable_const (2 * (d * (Lc * d) ^ 2))).mono' (hBm R).aestronglyMeasurable
          (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hBb R p)
      have hi1 : Integrable (fun p : Torus d × Torus d => sqNorm (lipGrad (fun x => F R x p.2) p.1))
          (P.prod P) :=
        (integrable_const (d * (Lc * d) ^ 2)).mono'
          (Finset.measurable_sum _ fun k _ => ((measurable_slice_lipGrad (hFc R) k).1).pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            exact sqNorm_le_of_abs_le (fun k => slice_lipGrad_bound (f := fun x => F R x p.2) hd hLc (hFx R p.2) p.1 k))
      have hi2 : Integrable (fun p : Torus d × Torus d => sqNorm (lipGrad (fun y => F R p.1 y) p.2))
          (P.prod P) :=
        (integrable_const (d * (Lc * d) ^ 2)).mono'
          (Finset.measurable_sum _ fun k _ => ((measurable_slice_lipGrad (hFc R) k).2).pow_const 2).aestronglyMeasurable
          (Eventually.of_forall fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
            exact sqNorm_le_of_abs_le (fun k => slice_lipGrad_bound (f := fun y => F R p.1 y) hd hLc (hFy R p.1) p.2 k))
      have e1 : (fun p : Torus d × Torus d => ENNReal.ofReal (Bsum R ![p.1, p.2])) =
          fun p => ENNReal.ofReal (sqNorm (lipGrad (fun x => F R x p.2) p.1) +
            sqNorm (lipGrad (fun y => F R p.1 y) p.2)) := by
        funext p; rfl
      rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun p =>
        add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)),
        integral_add hi1 hi2, integral_prod_symm _ hi1, integral_prod _ hi2]
    have hEx := tendsto_energy_Kt_x hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
      htR htR0
    have hEy := tendsto_energy_Kt_y hρ hρc hQ he heC1 heCae hM hM' hS hd hK0 hKc hBK hLK0 hL1 hL2
      htR htR0
    refine tendsto_zero_of_forall_real fun ε hε => ?_
    set ε' := min 1 (ε / (8 + 4 * (d : ℝ) ^ 3))
    have hε' : 0 < ε' := lt_min one_pos (by positivity)
    have hε'1 : ε' ≤ 1 := min_le_left _ _
    have hε'2 : ε' ≤ ε / (8 + 4 * (d : ℝ) ^ 3) := min_le_right _ _
    filter_upwards [hsup ε' hε', htRe ε' hε', hEx.eventually (gt_mem_nhds hε'),
      hEy.eventually (gt_mem_nhds hε')] with R hR htRR hExR hEyR
    calc ∫⁻ X, ENNReal.ofReal ((kerC2 (KR R) X - kerC2 Kf X) ^ 2 +
          gradSqC (fun Y => kerC2 (KR R) Y - kerC2 Kf Y) X) ∂Measure.pi (fun _ : Fin 2 => P)
        ≤ ∫⁻ X, (ENNReal.ofReal (ε' ^ 2 + 4 * d * (tR R * d) ^ 2) +
            2 * ENNReal.ofReal (Bsum R X)) ∂Measure.pi (fun _ : Fin 2 => P) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpt R ε' hR] with X hX
          refine (ENNReal.ofReal_le_ofReal hX).trans (le_of_eq ?_)
          have hB0 : 0 ≤ Bsum R X := add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp
      _ = ENNReal.ofReal (ε' ^ 2 + 4 * d * (tR R * d) ^ 2) +
            2 * ENNReal.ofReal ((∫ y, (∫ x, sqNorm (lipGrad (fun x => F R x y) x) ∂P) ∂P) +
              ∫ y, (∫ x, sqNorm (lipGrad (fun x => F R y x) x) ∂P) ∂P) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ (by norm_num), hBint R]
      _ ≤ ENNReal.ofReal ε := by
          have hsqn : ∀ v : Fin d → ℝ, 0 ≤ sqNorm v := fun v => Finset.sum_nonneg fun _ _ => sq_nonneg _
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) (add_nonneg
              (integral_nonneg fun _ => integral_nonneg fun _ => hsqn _)
              (integral_nonneg fun _ => integral_nonneg fun _ => hsqn _)))]
          refine ENNReal.ofReal_le_ofReal ?_
          have hD : (0 : ℝ) ≤ d := Nat.cast_nonneg _
          have ht2 : (tR R * d) ^ 2 ≤ ε' * d ^ 2 := by
            have := htR R
            nlinarith [mul_le_mul htRR htRR this.le hε'.le]
          have hε2 : ε' ^ 2 ≤ ε' := by nlinarith
          have hd3 : 4 * (d : ℝ) * (tR R * d) ^ 2 ≤ 4 * d ^ 3 * ε' := by nlinarith
          have hfin : (8 + 4 * (d : ℝ) ^ 3) * ε' ≤ ε := by
            rw [le_div_iff₀ (by positivity)] at hε'2; linarith
          nlinarith
  -- clause (4): uniform `C¹` bounds
  · refine ⟨ENNReal.ofReal (BK + 1) + ENNReal.ofReal (Real.sqrt (2 * d) * (L0 * d)),
      ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩, fun R => ?_⟩
    obtain ⟨gR, hgR⟩ : ∃ gR : Config 2 d → ℝ, gR = fun X => Real.sqrt
      (∑ k, lipGrad (fun x => KRc R x (X 1)) (X 0) k ^ 2 +
        ∑ k, lipGrad (fun y => KRc R (X 0) y) (X 1) k ^ 2) := ⟨_, rfl⟩
    have hgRm : Measurable gR := by
      rw [hgR]
      refine Real.continuous_sqrt.measurable.comp ((Finset.measurable_sum _ fun k _ =>
        (((measurable_slice_lipGrad (hKRcc R) k).1).comp measurable_config_pair).pow_const 2).add
        (Finset.measurable_sum _ fun k _ =>
        (((measurable_slice_lipGrad (hKRcc R) k).2).comp measurable_config_pair).pow_const 2))
    refine add_le_add (eLpNorm_top_le_of_ae (g := kerC2 (KRc R))
      (continuous_kerC2 (hKRcc R)).aestronglyMeasurable (hpiE.mono fun X hX => hX R)
      (Eventually.of_forall fun X => hKRcb R _ _))
      (eLpNorm_top_le_of_ae (g := gR) hgRm.aestronglyMeasurable ?_ (Eventually.of_forall fun X => ?_))
    · filter_upwards [hgradKR R] with X hX
      simp only [hgR, gradSqC, Fin.sum_univ_two]
      congr 1; congr 1
      · exact Finset.sum_congr rfl fun k _ => by rw [(hX k).1]
      · exact Finset.sum_congr rfl fun k _ => by rw [(hX k).2]
    · simp only [hgR]
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      have hg : ∑ k, lipGrad (fun x => KRc R x (X 1)) (X 0) k ^ 2 +
          ∑ k, lipGrad (fun y => KRc R (X 0) y) (X 1) k ^ 2 ≤ 2 * d * (L0 * d) ^ 2 := by
        have h0 := sqNorm_le_of_abs_le (v := fun k => lipGrad (fun x => KRc R x (X 1)) (X 0) k)
          (fun k => slice_lipGrad_bound hd hL00 (hKRcx R (X 1)) _ k)
        have h1 := sqNorm_le_of_abs_le (v := fun k => lipGrad (fun y => KRc R (X 0) y) (X 1) k)
          (fun k => slice_lipGrad_bound hd hL00 (hKRcy R (X 0)) _ k)
        simp only [sqNorm] at h0 h1
        linarith
      calc _ ≤ Real.sqrt (2 * d * (L0 * d) ^ 2) :=
            Real.sqrt_le_sqrt hg
        _ = Real.sqrt (2 * d) * (L0 * d) := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- clause (5): the diagonal
  · refine tendsto_zero_of_forall_real fun ε hε => ?_
    filter_upwards [hsup ε hε] with R hR
    refine eLpNorm_top_le_of_ae (g := fun x => KRc R x x - Kf x x)
      (((hKRcc R).comp (continuous_id.prodMk continuous_id)).sub
        (hKc.comp (continuous_id.prodMk continuous_id))).aestronglyMeasurable
      (hdiagE.mono fun x hx => by rw [hx R]) (Eventually.of_forall fun x => hR _ _)
  -- clause (6): gradients of the diagonal
  · refine ⟨ENNReal.ofReal (Real.sqrt d * (2 * L0 * d)), ENNReal.ofReal_lt_top, fun R => ?_⟩
    have hdl : ∀ a b, KRc R (liftT a) (liftT a) - KRc R (liftT b) (liftT b) ≤ (2 * L0) * dE a b :=
      fun a b => by have h1 := hKRcx R (liftT a) a b; have h2 := hKRcy R (liftT b) a b; linarith
    have hdc : Continuous fun z => KRc R z z := (hKRcc R).comp (continuous_id.prodMk continuous_id)
    have hw := isWeakGrad_lipGrad hdc (lipschitzWith_of_lift_bound hd (by positivity) hdl)
    have hcon := weakGrad_congr_ae ⟨_, hw⟩ (hdiagEV.mono fun x hx => (hx R).symm)
    have hun := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
    have hP : ∀ᵐ x ∂P, weakGrad (fun z => KR R z z) x = lipGrad (fun z => KRc R z z) x :=
      hρ.ac.ae_le (hcon.2.trans hun)
    have hgm : Measurable fun x => Real.sqrt (sqNorm (lipGrad (fun z => KRc R z z) x)) :=
      Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun k _ =>
        (measurable_lipGrad hdc k).pow_const 2)
    refine eLpNorm_top_le_of_ae (g := fun x => Real.sqrt (sqNorm (lipGrad (fun z => KRc R z z) x)))
      hgm.aestronglyMeasurable (hP.mono fun x hx => by rw [hx])
      (Eventually.of_forall fun x => ?_)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hb : ∀ k, |lipGrad (fun z => KRc R z z) x k| ≤ 2 * L0 * d := fun k =>
      slice_lipGrad_bound hd (by positivity) hdl x k
    calc Real.sqrt (sqNorm (lipGrad (fun z => KRc R z z) x)) ≤ Real.sqrt (d * (2 * L0 * d) ^ 2) :=
          Real.sqrt_le_sqrt (sqNorm_le_of_abs_le hb)
      _ = Real.sqrt d * (2 * L0 * d) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]

end SharpLSI
