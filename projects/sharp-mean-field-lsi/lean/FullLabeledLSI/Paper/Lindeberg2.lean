import FullLabeledLSI.Paper.Lindeberg1
import FullLabeledLSI.Paper.LindebergTransfer
import FullLabeledLSI.Paper.LindebergAlg
import FullLabeledLSI.Infra.GaussianSwap
import FullLabeledLSI.Infra.GaussianPiUpdate
import FullLabeledLSI.Infra.GaussianPiMoments

/-!
# Lemma 7.1, part 3: one Lindeberg step, algebraic part

Fix a label `i` which is low-influence (`i ∈ (retained c δ)ᶜ`) and a label set `B ∋ i`. The
integrand of `IP … B` and of `IP … (B.erase i)` is, as a function of the label-`i` variables,
`Ψ_ω(u) = Φ (p(ω) + M(ω) u)` evaluated at `u = (e_{m+1}(x_i))_m` resp. `u = y_i`, where
`p(ω), M(ω)` depend only on the other labels.

* `Mlin`: the continuous linear map `u ↦ (∑ b_r u_r, a · u|_{JR})`, with `‖Mlin‖ ≤ ∑|b_r| + |a|`.
* `eps`: the feature vector `(e_1(x), …, e_J(x))`; its law has the moments of `γ_J` up to order 2.
* `bco`, `Cz`: the coefficient polynomials and the remaining fluctuation, independent of label `i`.
* `Fint_mem`/`Fint_not_mem`: the two integrands as `Ψ`.
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### The linear map `u ↦ (∑ b_r u_r, a u|_{JR})` -/

/-- `u ↦ (∑_r b_r u_r, (a u_{r'})_{r' < JR})` as a continuous linear map. -/
noncomputable def Mlin {J JR : ℕ} (hJ : JR ≤ J) (b : Fin J → ℝ) (a : ℝ) :
    (Fin J → ℝ) →L[ℝ] ℝ × (Fin JR → ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun u => (∑ r, b r * u r, fun r' => a * u (Fin.castLE hJ r'))
      map_add' := fun u v => Prod.ext (by simp [mul_add, Finset.sum_add_distrib])
        (funext fun r' => by simp [mul_add])
      map_smul' := fun t u => Prod.ext (by simp [Finset.mul_sum, mul_left_comm])
        (funext fun r' => by simp [mul_left_comm]) }
    (∑ r, |b r| + |a|) (fun u => by
      have hu : 0 ≤ ‖u‖ := norm_nonneg u
      have hC : 0 ≤ ∑ r, |b r| + |a| := by positivity
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · show ‖∑ r, b r * u r‖ ≤ _
        rw [Real.norm_eq_abs]
        calc |∑ r, b r * u r| ≤ ∑ r, |b r * u r| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ r, |b r| * ‖u‖ := Finset.sum_le_sum fun r _ => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm u r) (abs_nonneg _)
          _ = (∑ r, |b r|) * ‖u‖ := by rw [Finset.sum_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) hu
      · show ‖fun r' : Fin JR => a * u (Fin.castLE hJ r')‖ ≤ _
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun r' => ?_
        rw [Real.norm_eq_abs, abs_mul]
        calc |a| * |u (Fin.castLE hJ r')| ≤ |a| * ‖u‖ :=
              mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm u (Fin.castLE hJ r'))
                (abs_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
              (Finset.sum_nonneg fun r _ => abs_nonneg _)) hu)

theorem Mlin_apply {J JR : ℕ} (hJ : JR ≤ J) (b : Fin J → ℝ) (a : ℝ) (u : Fin J → ℝ) :
    Mlin hJ b a u = (∑ r, b r * u r, fun r' => a * u (Fin.castLE hJ r')) := rfl

theorem Mlin_norm_le {J JR : ℕ} (hJ : JR ≤ J) (b : Fin J → ℝ) (a : ℝ) :
    ‖Mlin hJ b a‖ ≤ ∑ r, |b r| + |a| :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-! ### The feature vector of one label -/

/-- `eps e J x = (e_1(x), …, e_J(x))`. -/
def eps (e : ℕ → Torus d → ℝ) (J : ℕ) (x : Torus d) : Fin J → ℝ := fun r => e ((r : ℕ) + 1) x

section eps

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}

theorem measurable_eps (hG : GoodBasis μ e) (J : ℕ) : Measurable (eps e J) :=
  measurable_pi_iff.2 fun r => hG.meas _

theorem eps_bound (hG : GoodBasis μ e) (J : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖eps e J x‖ ≤ A := by
  choose Cb hCb using hG.bdd
  refine ⟨∑ r : Fin J, |Cb ((r : ℕ) + 1)|, by positivity, fun x => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun r => ?_
  rw [Real.norm_eq_abs]
  calc |eps e J x r| ≤ Cb ((r : ℕ) + 1) := hCb _ x
    _ ≤ |Cb ((r : ℕ) + 1)| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun r : Fin J => |Cb ((r : ℕ) + 1)|)
        (fun r _ => abs_nonneg _) (Finset.mem_univ r)

/-- The law of the feature vector of one label under `μ`. -/
noncomputable abbrev epsLaw (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ) (J : ℕ) :
    Measure (Fin J → ℝ) := μ.map (eps e J)

theorem epsLaw_integrable_cube (hG : GoodBasis μ e) (J : ℕ) :
    Integrable (fun y : Fin J → ℝ => ‖y‖ ^ 3) (epsLaw μ e J) := by
  obtain ⟨A, hA0, hA⟩ := eps_bound hG J
  have hm : AEStronglyMeasurable (fun y : Fin J → ℝ => ‖y‖ ^ 3) (μ.map (eps e J)) :=
    (by fun_prop : Continuous fun y : Fin J → ℝ => ‖y‖ ^ 3).aestronglyMeasurable
  rw [epsLaw, integrable_map_measure hm (measurable_eps hG J).aemeasurable]
  refine Integrable.of_bound ((measurable_eps hG J).norm.pow_const 3).aestronglyMeasurable
    (A ^ 3) (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, norm_pow, norm_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (hA x) 3

theorem epsLaw_mean (hG : GoodBasis μ e) (J : ℕ) (m : Fin J) :
    ∫ y, y m ∂epsLaw μ e J = ∫ y, y m ∂gaussPi J := by
  rw [gaussPi_integral_coord, epsLaw, integral_map (measurable_eps hG J).aemeasurable
    (measurable_pi_apply m).aestronglyMeasurable]
  have h := hG.orth ((m : ℕ) + 1) 0
  simp only [hG.zero, mul_one] at h
  simpa [eps] using h

theorem epsLaw_cov (hG : GoodBasis μ e) (J : ℕ) (m m' : Fin J) :
    ∫ y, y m * y m' ∂epsLaw μ e J = ∫ y, y m * y m' ∂gaussPi J := by
  have hm : AEStronglyMeasurable (fun y : Fin J → ℝ => y m * y m') (μ.map (eps e J)) :=
    ((measurable_pi_apply m).mul (measurable_pi_apply m')).aestronglyMeasurable
  rw [gaussPi_integral_mul, epsLaw, integral_map (measurable_eps hG J).aemeasurable hm]
  have h := hG.orth ((m : ℕ) + 1) ((m' : ℕ) + 1)
  simp only [eps]
  rw [h]
  by_cases hm : m = m'
  · simp [hm]
  · have hne : ¬ ((m : ℕ) + 1 = (m' : ℕ) + 1) := fun h => hm (Fin.ext (by omega))
    rw [if_neg hne, if_neg hm]

end eps

/-! ### The label-`i` decomposition -/

section decomp

variable {N J JR : ℕ} {e : ℕ → Torus d → ℝ}

/-- The coefficient of `lf … i r.succ` in the polynomial: `polyF (cdrop c i m)`. -/
noncomputable def bco (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (i : Fin N) (m : Fin (J + 1)) (ω : Fin N → Torus d × (Fin J → ℝ)) : ℝ :=
  polyF (lf e B) (cdrop c i m) ω

/-- The part of the fluctuation `zP` carried by the labels other than `i`. -/
noncomputable def Cz (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (B : Finset (Fin N)) (i : Fin N) (r : Fin J) (ω : Fin N → Torus d × (Fin J → ℝ)) : ℝ :=
  (Real.sqrt (lowCount c δ))⁻¹ * ∑ l ∈ (retained c δ)ᶜ.erase i, lf e B l r.succ (ω l)

theorem pP_decomp (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (i : Fin N) (ω : Fin N → Torus d × (Fin J → ℝ)) :
    pP e c B ω = bco e c B i 0 ω + ∑ r : Fin J, lf e B i r.succ (ω i) * bco e c B i r.succ ω := by
  have h := polyF_decomp (lf e B) (fun l s => lf_zero e he0 B l s) c i ω
  show polyF (lf e B) c ω = _
  rw [h, Fin.sum_univ_succ, lf_zero e he0 B i, one_mul]
  rfl

theorem zP_decomp (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (B : Finset (Fin N)) (i : Fin N)
    (hi : i ∈ (retained c δ)ᶜ) (ω : Fin N → Torus d × (Fin J → ℝ)) (r : Fin J) :
    zP e c δ B ω r = Cz e c δ B i r ω + (Real.sqrt (lowCount c δ))⁻¹ * lf e B i r.succ (ω i) := by
  unfold zP Cz
  rw [← Finset.add_sum_erase _ _ hi]
  ring

theorem bco_congr (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) {B B' : Finset (Fin N)}
    (i : Fin N) (h : ∀ l, l ≠ i → (l ∈ B ↔ l ∈ B')) (m : Fin (J + 1))
    (ω : Fin N → Torus d × (Fin J → ℝ)) : bco e c B i m ω = bco e c B' i m ω :=
  polyF_cdrop_congr (fun l s => lf_zero e he0 B l s) (fun l s => lf_zero e he0 B' l s) i
    (fun l hl => lf_congr e (h l hl)) c m ω

theorem Cz_congr (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) {B B' : Finset (Fin N)}
    (i : Fin N) (h : ∀ l, l ≠ i → (l ∈ B ↔ l ∈ B')) (r : Fin J)
    (ω : Fin N → Torus d × (Fin J → ℝ)) : Cz e c δ B i r ω = Cz e c δ B' i r ω := by
  unfold Cz
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hli : l ≠ i := (Finset.mem_erase.mp hl).1
  rw [lf_congr e (h l hli)]

theorem bco_update (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (i : Fin N) (m : Fin (J + 1)) (ω : Fin N → Torus d × (Fin J → ℝ)) (s : Torus d × (Fin J → ℝ)) :
    bco e c B i m (Function.update ω i s) = bco e c B i m ω :=
  polyF_cdrop_update (lf e B) (fun l s => lf_zero e he0 B l s) c i m ω s

theorem Cz_update (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (B : Finset (Fin N)) (i : Fin N)
    (r : Fin J) (ω : Fin N → Torus d × (Fin J → ℝ)) (s : Torus d × (Fin J → ℝ)) :
    Cz e c δ B i r (Function.update ω i s) = Cz e c δ B i r ω := by
  unfold Cz
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  have hli : l ≠ i := (Finset.mem_erase.mp hl).1
  rw [Function.update_of_ne hli]

/-- The integrand of `IP`. -/
noncomputable def Fint (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (B : Finset (Fin N))
    (ω : Fin N → Torus d × (Fin J → ℝ)) : ℝ :=
  Φ (pP e c B ω, fun m => zP e c δ B ω (Fin.castLE hJ m))

/-- `Ψ_ω(u)`: the integrand as a function of the label-`i` feature vector `u`. -/
noncomputable def Psi (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (B : Finset (Fin N)) (i : Fin N)
    (ω : Fin N → Torus d × (Fin J → ℝ)) (u : Fin J → ℝ) : ℝ :=
  Φ (bco e c B i 0 ω + ∑ r, bco e c B i r.succ ω * u r,
    fun r' : Fin JR => Cz e c δ B i (Fin.castLE hJ r') ω +
      (Real.sqrt (lowCount c δ))⁻¹ * u (Fin.castLE hJ r'))

theorem Psi_eq_affine (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) (B : Finset (Fin N)) (i : Fin N)
    (ω : Fin N → Torus d × (Fin J → ℝ)) (u : Fin J → ℝ) :
    Psi e c δ hJ Φ B i ω u =
      Φ ((bco e c B i 0 ω, fun r' : Fin JR => Cz e c δ B i (Fin.castLE hJ r') ω) +
        Mlin hJ (fun r => bco e c B i r.succ ω) (Real.sqrt (lowCount c δ))⁻¹ u) := by
  rw [Mlin_apply]
  rfl

theorem Psi_update (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) (B : Finset (Fin N)) (i : Fin N)
    (ω : Fin N → Torus d × (Fin J → ℝ)) (s : Torus d × (Fin J → ℝ)) (u : Fin J → ℝ) :
    Psi e c δ hJ Φ B i (Function.update ω i s) u = Psi e c δ hJ Φ B i ω u := by
  unfold Psi
  simp only [bco_update he0, Cz_update]

theorem Fint_mem (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J)
    (Φ : ℝ × (Fin JR → ℝ) → ℝ) {B B₀ : Finset (Fin N)} (i : Fin N)
    (hi : i ∈ (retained c δ)ᶜ) (hiB : i ∈ B₀) (h : ∀ l, l ≠ i → (l ∈ B₀ ↔ l ∈ B))
    (ω : Fin N → Torus d × (Fin J → ℝ)) :
    Fint e c δ hJ Φ B₀ ω = Psi e c δ hJ Φ B i ω (eps e J (ω i).1) := by
  unfold Fint Psi
  congr 1
  refine Prod.ext ?_ ?_
  · show pP e c B₀ ω = _
    rw [pP_decomp he0 c B₀ i ω, bco_congr he0 c i h 0 ω]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [bco_congr he0 c i h r.succ ω, lf_of_mem e hiB]
    simp only [eps, Fin.val_succ]
    ring
  · funext r'
    show zP e c δ B₀ ω (Fin.castLE hJ r') = _
    rw [zP_decomp c δ B₀ i hi ω, Cz_congr c δ i h, lf_of_mem e hiB]
    simp [eps]

theorem Fint_not_mem (he0 : e 0 = fun _ => 1) (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) {B B₀ : Finset (Fin N)} (i : Fin N)
    (hi : i ∈ (retained c δ)ᶜ) (hiB : i ∉ B₀) (h : ∀ l, l ≠ i → (l ∈ B₀ ↔ l ∈ B))
    (ω : Fin N → Torus d × (Fin J → ℝ)) :
    Fint e c δ hJ Φ B₀ ω = Psi e c δ hJ Φ B i ω (ω i).2 := by
  unfold Fint Psi
  congr 1
  refine Prod.ext ?_ ?_
  · show pP e c B₀ ω = _
    rw [pP_decomp he0 c B₀ i ω, bco_congr he0 c i h 0 ω]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [bco_congr he0 c i h r.succ ω, lf_of_not_mem_succ e hiB]
    ring
  · funext r'
    show zP e c δ B₀ ω (Fin.castLE hJ r') = _
    rw [zP_decomp c δ B₀ i hi ω, Cz_congr c δ i h, lf_of_not_mem_succ e hiB]

end decomp

end SharpLSI.FL
