import FullLabeledLSI.Examples.Paper.Sec9DeficitReal
import FullLabeledLSI.Examples.Paper.Sec9DeficitCompact
import FullLabeledLSI.Examples.Paper.Sec9SmallRateA

/-!
# Lemma 9.5, L3: the deficit as a function of a finite-dimensional point; closedness of the profile set

Lane C of the Section 9 formalization.  An admissible profile is `f ≥ 0` in `H¹` with `∫ f² = 1`
(`Adm f`); the density is `f²`.  A profile has the point `Pt f = (m(f), J_r(f)) ∈ ℝ⁴ × ℝ`
(moments of `f²` against `cos, sin` of frequencies `k, 2k`, and `J_r = 4∫f'² - 2r H(f²)`).
The deficit of a family is `Λ(∑ θ_i Pt f_i)`, `Λ(m, j) = j + Ψ(m)` (`deficit_eq_Lam`).
`closed_K`: `K = {(m, j) | ∃ f ∈ Adm, m(f) = m ∧ J_r(f) ≤ j}` is closed (via `h1_compact`).
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Def

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Cmp

/-- Admissible profile: `f ≥ 0`, `f ∈ H¹`, `∫ f² = 1`. -/
def Adm (f : Torus 1 → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ MemH1 (haar 1) f ∧ ∫ x, f x ^ 2 ∂haar 1 = 1

noncomputable def Hf (f : Torus 1 → ℝ) : ℝ :=
  (klDiv (densMeasure fun x => f x ^ 2) (haar 1)).toReal

noncomputable def Wd (f : Torus 1 → ℝ) : ℝ := ∫ x, weakGrad f x 0 ^ 2 ∂haar 1

/-- `J_r(f) = 4∫f'² - 2r H(f²|m)`. -/
noncomputable def Jf (r : ℝ) (f : Torus 1 → ℝ) : ℝ := 4 * Wd f - 2 * r * Hf f

/-- The ambient finite-dimensional space `ℝ⁴ × ℝ`. -/
abbrev PE := (Fin 4 → ℝ) × ℝ

/-- The four moments `(c₁, s₁, c₂, s₂)` of the density `f²`. -/
noncomputable def mvecF (k : ℕ) (f : Torus 1 → ℝ) : Fin 4 → ℝ :=
  ![mcos k (fun x => f x ^ 2), msin k (fun x => f x ^ 2),
    mcos (2 * (k : ℤ)) (fun x => f x ^ 2), msin (2 * (k : ℤ)) (fun x => f x ^ 2)]

noncomputable def Pt (k : ℕ) (r : ℝ) (f : Torus 1 → ℝ) : PE := (mvecF k f, Jf r f)

noncomputable def PsiV (k : ℕ) (a r : ℝ) (m : Fin 4 → ℝ) : ℝ := Psi k a r (m 0) (m 1) (m 2) (m 3)

/-- `Λ(m, j) = j + Ψ(m)`. -/
noncomputable def Lam (k : ℕ) (a r : ℝ) (p : PE) : ℝ := p.2 + PsiV k a r p.1

theorem continuous_PsiV (k : ℕ) (a r : ℝ) : Continuous (PsiV k a r) := by
  unfold PsiV Psi
  fun_prop

theorem continuous_Lam (k : ℕ) (a r : ℝ) : Continuous (Lam k a r) := by
  unfold Lam
  exact continuous_snd.add ((continuous_PsiV k a r).comp continuous_fst)

/-! ### Basic facts about profiles -/

theorem Adm.dens {f : Torus 1 → ℝ} (hf : Adm f) :
    (∀ x, 0 ≤ f x ^ 2) ∧ ∫ x, f x ^ 2 ∂haar 1 = 1 ∧
      MemH1 (haar 1) (fun x => Real.sqrt (f x ^ 2)) := by
  refine ⟨fun _ => sq_nonneg _, hf.2.2, ?_⟩
  have : (fun x => Real.sqrt (f x ^ 2)) = f := funext fun x => Real.sqrt_sq (hf.1 x)
  rw [this]; exact hf.2.1

theorem Jfun_sq (r : ℝ) {f : Torus 1 → ℝ} (hf : Adm f) : Jfun r (fun x => f x ^ 2) = Jf r f := by
  obtain ⟨h0, h1, hM⟩ := hf.dens
  have hs : (fun x => Real.sqrt (f x ^ 2)) = f := funext fun x => Real.sqrt_sq (hf.1 x)
  unfold Jfun Jf Wd Hf
  rw [fisherInfo_densMeasure_eq h0 h1 hM, hs, ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _))]

theorem Hf_nonneg (f : Torus 1 → ℝ) : 0 ≤ Hf f := ENNReal.toReal_nonneg

theorem Wd_nonneg (f : Torus 1 → ℝ) : 0 ≤ Wd f := integral_nonneg fun _ => sq_nonneg _

theorem Hf_le {f : Torus 1 → ℝ} (hf : Adm f) : aCos * Hf f ≤ 2 * Wd f :=
  (entropy_le_energy hf.1 hf.2.1 hf.2.2).2

theorem Jf_ge {r : ℝ} (hr0 : 0 ≤ r) {f : Torus 1 → ℝ} (hf : Adm f) :
    4 * Wd f - 4 * (r / aCos) * Wd f ≤ Jf r f := by
  have hc : 0 < aCos := by unfold aCos; positivity
  have h1 := Hf_le hf
  have h2 : Hf f ≤ 2 * Wd f / aCos := by rw [le_div_iff₀ hc]; linarith
  have h3 : 2 * r * Hf f ≤ 2 * r * (2 * Wd f / aCos) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : 2 * r * (2 * Wd f / aCos) = 4 * (r / aCos) * Wd f := by field_simp; ring
  unfold Jf
  linarith

theorem Jf_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ aCos) {f : Torus 1 → ℝ} (hf : Adm f) :
    0 ≤ Jf r f := by
  have hc : 0 < aCos := by unfold aCos; positivity
  have h := Jf_ge hr0 hf
  have hW := Wd_nonneg f
  have hq : r / aCos ≤ 1 := (div_le_one hc).2 hr
  nlinarith [mul_nonneg hW (sub_nonneg.2 hq)]

theorem abs_mcos_le {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ (haar 1))
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (j : ℤ) : |mcos j ρ| ≤ 1 := by
  unfold mcos
  have := norm_integral_le_of_norm_le hρ (f := fun y => Reg.cosK j y * ρ y)
    (Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
      calc |Reg.cosK j y| * ρ y ≤ 1 * ρ y :=
            mul_le_mul_of_nonneg_right (abs_cosK_le j y) (h0 y)
        _ = ρ y := one_mul _)
  rw [Real.norm_eq_abs, h1] at this
  exact this

theorem abs_msin_le {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ (haar 1))
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (j : ℤ) : |msin j ρ| ≤ 1 := by
  unfold msin
  have := norm_integral_le_of_norm_le hρ (f := fun y => sinK j y * ρ y)
    (Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h0 y)]
      calc |sinK j y| * ρ y ≤ 1 * ρ y :=
            mul_le_mul_of_nonneg_right (abs_sinK_le j y) (h0 y)
        _ = ρ y := one_mul _)
  rw [Real.norm_eq_abs, h1] at this
  exact this

theorem abs_mvecF_le (k : ℕ) {f : Torus 1 → ℝ} (hf : Adm f) (i : Fin 4) : |mvecF k f i| ≤ 1 := by
  obtain ⟨h0, h1, -⟩ := hf.dens
  have hi : Integrable (fun x => f x ^ 2) (haar 1) := integrable_of_integral_eq_one' h1
  fin_cases i
  · exact abs_mcos_le h0 hi h1 _
  · exact abs_msin_le h0 hi h1 _
  · exact abs_mcos_le h0 hi h1 _
  · exact abs_msin_le h0 hi h1 _

/-! ### Families -/

/-- The square-root profile of the `i`-th species. -/
noncomputable def fOf (F : Family 1) (i : Fin F.q) : Torus 1 → ℝ := fun x => Real.sqrt (F.ρ i x)

theorem adm_fOf {F : Family 1} (hF : F.Admissible) (i : Fin F.q) : Adm (fOf F i) := by
  obtain ⟨h0, h1, hH⟩ := hF.2.2 i
  refine ⟨fun x => Real.sqrt_nonneg _, hH, ?_⟩
  unfold fOf
  simp_rw [Real.sq_sqrt (h0 _)]
  exact h1

theorem sq_fOf {F : Family 1} (hF : F.Admissible) (i : Fin F.q) :
    (fun x => fOf F i x ^ 2) = F.ρ i := by
  funext x
  unfold fOf
  exact Real.sq_sqrt ((hF.2.2 i).1 x)

theorem integrable_rho {F : Family 1} (hF : F.Admissible) (i : Fin F.q) :
    Integrable (F.ρ i) (haar 1) := integrable_of_integral_eq_one' (hF.2.2 i).2.1

theorem mcos_bar {F : Family 1} (hF : F.Admissible) (j : ℤ) :
    mcos j F.bar = ∑ i, F.θ i * mcos j (F.ρ i) := by
  unfold mcos Family.bar
  have e : ∀ y, Reg.cosK j y * ∑ i, F.θ i * F.ρ i y =
      ∑ i, F.θ i * (Reg.cosK j y * F.ρ i y) := fun y => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => (integrable_cosK_mul (integrable_rho hF i) j).const_mul _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]

theorem msin_bar {F : Family 1} (hF : F.Admissible) (j : ℤ) :
    msin j F.bar = ∑ i, F.θ i * msin j (F.ρ i) := by
  unfold msin Family.bar
  have e : ∀ y, sinK j y * ∑ i, F.θ i * F.ρ i y =
      ∑ i, F.θ i * (sinK j y * F.ρ i y) := fun y => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ fun i _ => (integrable_sinK_mul (integrable_rho hF i) j).const_mul _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]

theorem deficit_eq_Lam {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (F : Family 1) (hF : F.Admissible) :
    deficit (attrW (harmKernel k a)) r F = Lam k a r (∑ i, F.θ i • Pt k r (fOf F i)) := by
  rw [deficit_eq hk ha0 ha1 r F hF]
  unfold Lam PsiV Pt
  have hJ : ∑ i, F.θ i * Jfun r (F.ρ i) = (∑ i, F.θ i • (mvecF k (fOf F i), Jf r (fOf F i))).2 := by
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sq_fOf hF i, Jfun_sq r (adm_fOf hF i)]
  have hm : ∀ j : Fin 4, (∑ i, F.θ i • (mvecF k (fOf F i), Jf r (fOf F i))).1 j =
      ∑ i, F.θ i * mvecF k (fOf F i) j := by
    intro j
    simp [Prod.fst_sum, Finset.sum_apply]
  rw [hJ, hm 0, hm 1, hm 2, hm 3, mcos_bar hF, msin_bar hF, mcos_bar hF, msin_bar hF]
  congr 1
  simp only [mvecF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, sq_fOf hF]

/-- The family with fractions `θ` and densities `f_i²`. -/
noncomputable def mkFamily {n : ℕ} (θ : Fin n → ℝ) (f : Fin n → Torus 1 → ℝ) : Family 1 :=
  ⟨n, θ, fun i x => f i x ^ 2⟩

theorem mkFamily_adm {n : ℕ} {θ : Fin n → ℝ} {f : Fin n → Torus 1 → ℝ} (hθ : ∀ i, 0 < θ i)
    (hs : ∑ i, θ i = 1) (hf : ∀ i, Adm (f i)) : (mkFamily θ f).Admissible :=
  ⟨hθ, hs, fun i => ⟨fun x => sq_nonneg _, (hf i).2.2, (hf i).dens.2.2⟩⟩

theorem fOf_mkFamily {n : ℕ} {θ : Fin n → ℝ} {f : Fin n → Torus 1 → ℝ} (hf : ∀ i, Adm (f i))
    (i : Fin n) : fOf (mkFamily θ f) i = f i := by
  funext x
  unfold fOf mkFamily
  exact Real.sqrt_sq ((hf i).1 x)

theorem deficit_mkFamily {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    {n : ℕ} {θ : Fin n → ℝ} {f : Fin n → Torus 1 → ℝ} (hθ : ∀ i, 0 < θ i) (hs : ∑ i, θ i = 1)
    (hf : ∀ i, Adm (f i)) :
    deficit (attrW (harmKernel k a)) r (mkFamily θ f) = Lam k a r (∑ i, θ i • Pt k r (f i)) := by
  rw [deficit_eq_Lam hk ha0 ha1 r _ (mkFamily_adm hθ hs hf)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  show θ i • Pt k r (fOf (mkFamily θ f) i) = θ i • Pt k r (f i)
  rw [fOf_mkFamily hf i]

/-! ### Closedness of the profile set `K` (L3) -/

/-- `K = {(m, j) | ∃ f ∈ Adm, m(f) = m ∧ J_r(f) ≤ j}`. -/
def Kset (k : ℕ) (r : ℝ) : Set PE := {p | ∃ f, Adm f ∧ mvecF k f = p.1 ∧ Jf r f ≤ p.2}

theorem closed_K (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < aCos) : IsClosed (Kset k r) := by
  have hc : 0 < aCos := by unfold aCos; positivity
  have hθ1 : r / aCos < 1 := (div_lt_one hc).2 hr
  refine IsSeqClosed.isClosed fun pn p hpn hlim => ?_
  choose f hf hfm hfJ using hpn
  -- energy bound
  obtain ⟨B, hB⟩ := ((continuous_snd.tendsto p).comp hlim).bddAbove_range
  have hD : ∀ n, Wd (f n) ≤ B / (4 * (1 - r / aCos)) := by
    intro n
    have h1 := Jf_ge hr0 (hf n)
    have h2 : (pn n).2 ≤ B := hB ⟨n, rfl⟩
    rw [le_div_iff₀ (by nlinarith)]
    nlinarith [hfJ n]
  obtain ⟨φ, u, L, hφ, hu0, hMu, hmass, -, -, hLim, hlsc, hmom, hent⟩ :=
    h1_compact (fun n x => (hf n).1 x) (fun n => (hf n).2.1) (fun n => (hf n).2.2)
      (fun n => hD n)
  have huAdm : Adm u := ⟨hu0, hMu, hmass⟩
  refine ⟨u, huAdm, ?_, ?_⟩
  · -- moments
    have hlimφ : Tendsto (fun n => pn (φ n)) atTop (𝓝 p) := hlim.comp hφ.tendsto_atTop
    have hm1 : Tendsto (fun n => (pn (φ n)).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlimφ
    funext j
    have hmj : Tendsto (fun n => (pn (φ n)).1 j) atTop (𝓝 (p.1 j)) :=
      (continuous_apply j).tendsto _ |>.comp hm1
    have hmj' : Tendsto (fun n => mvecF k (f (φ n)) j) atTop (𝓝 (mvecF k u j)) := by
      fin_cases j
      · exact hmom (Reg.cosK k) (continuous_cosK k)
      · exact hmom (sinK k) (continuous_sinK k)
      · exact hmom (Reg.cosK (2 * (k : ℤ))) (continuous_cosK _)
      · exact hmom (sinK (2 * (k : ℤ))) (continuous_sinK _)
    have : (fun n => mvecF k (f (φ n)) j) = fun n => (pn (φ n)).1 j := by
      funext n; rw [hfm]
    rw [this] at hmj'
    exact tendsto_nhds_unique hmj' hmj
  · -- the value of J
    have hlimφ : Tendsto (fun n => (pn (φ n)).2) atTop (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp (hlim.comp hφ.tendsto_atTop)
    have hJlim : Tendsto (fun n => Jf r (f (φ n))) atTop
        (𝓝 (4 * L - 2 * r * Hf u)) := by
      unfold Jf Wd Hf
      exact ((hLim.const_mul 4).sub (hent.const_mul (2 * r)))
    have h1 : 4 * L - 2 * r * Hf u ≤ p.2 :=
      le_of_tendsto_of_tendsto hJlim hlimφ (Eventually.of_forall fun n => hfJ _)
    unfold Jf Wd
    unfold Wd at *
    nlinarith [hlsc]

end SharpLSI.FL.Ex.Def
