import FullLabeledLSI.Defs.F05_FiniteRank
import FullLabeledLSI.Paper.Sec6MomentsU
import SharpSymmetricLSI.Paper.ULimit8
import SharpSymmetricLSI.Paper.ULimit1
import SharpSymmetricLSI.Paper.CenteredEntropy

/-!
# Lemma 6.1, first conclusion: `sup_N ‖U_N - U_{N,R}‖_{L^q} → 0` (item M3)

Route.  With `K = centeredKernel W μ` and `K_R = ∑_{i,j ∈ s R} a R i j e_{i+1} ⊗ e_{j+1}` we have
`U_N - U_{N,R} = Ugen (K - K_R) N`, where `Ugen κ N X = (2N)⁻¹ ∑_{l,m} κ(X_l, X_m)`.
For a symmetric kernel `D` (here `D = K - K_R`) that is centered in each variable and bounded,

  `Ugen D N = offDiag D N + (2N)⁻¹ ∑_l D(X_l, X_l)`,

and the finished degenerate U-statistic moment bound `Sec6.ustat_moment_bound` gives
`‖offDiag D N‖_{2k} ≤ c_k ‖D‖_∞` uniformly in `N ≥ 1`, while the diagonal part is bounded by
`½ sup_x |D(x,x)|`.  Both sup-norms tend to `0` by `IsKernelApprox`.

Since the eigenfunctions `e_j` are only defined up to `μ`-null sets (they are `L²` classes), we
replace `e_j` by Borel measurable versions `e'_j` (equal `μ`-a.e.), which changes nothing a.e.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

namespace Rank1

/-! ### Generic part: `L^{2k}` norm of `Ugen D N` for a bounded degenerate kernel -/

section Generic

variable {α : Type}

/-- The finite-rank kernel `∑_{i,j ∈ s} a i j f_{i+1}(x) f_{j+1}(y)`. -/
def kerFR (s : Finset ℕ) (a : ℕ → ℕ → ℝ) (f : ℕ → α → ℝ) (x y : α) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i j * f (i + 1) x * f (j + 1) y

lemma kerFR_symm {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → α → ℝ} (ha : ∀ i j, a i j = a j i)
    (x y : α) : kerFR s a f x y = kerFR s a f y x := by
  unfold kerFR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [ha j i]; ring

lemma kerFR_congr {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f f' : ℕ → α → ℝ} {x y : α}
    (hx : ∀ j, f j x = f' j x) (hy : ∀ j, f j y = f' j y) :
    kerFR s a f x y = kerFR s a f' x y := by
  unfold kerFR
  simp only [hx, hy]

variable [MeasurableSpace α]

lemma measurable_kerFR {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → α → ℝ}
    (hf : ∀ j, Measurable (f j)) : Measurable (Function.uncurry (kerFR s a f)) := by
  show Measurable (fun p : α × α => ∑ i ∈ s, ∑ j ∈ s, a i j * f (i + 1) p.1 * f (j + 1) p.2)
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact (measurable_const.mul ((hf _).comp measurable_fst)).mul ((hf _).comp measurable_snd)

lemma integrable_kerFR_right {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → α → ℝ} {μ : Measure α}
    (hint : ∀ j, Integrable (f (j + 1)) μ) (x : α) :
    Integrable (fun y => kerFR s a f x y) μ := by
  unfold kerFR
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  exact (hint j).const_mul (a i j * f (i + 1) x)

lemma integral_kerFR_right {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → α → ℝ} {μ : Measure α}
    (hint : ∀ j, Integrable (f (j + 1)) μ) (hcen : ∀ j, ∫ y, f (j + 1) y ∂μ = 0) (x : α) :
    ∫ y, kerFR s a f x y ∂μ = 0 := by
  unfold kerFR
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (hint j).const_mul (a i j * f (i + 1) x)))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hint j).const_mul (a i j * f (i + 1) x))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, hcen j, mul_zero]

lemma measurable_offDiag {D : α → α → ℝ} (hD : Measurable (Function.uncurry D)) (N : ℕ) :
    Measurable (offDiag D N) := by
  unfold offDiag
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun j _ => ?_)
  by_cases h : i < j
  · simp only [h, ↓reduceIte]
    have h2 : Measurable (fun X : Fin N → α => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hD.comp h2
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- Off-diagonal part: `‖offDiag D N‖_{2k} ≤ c_k B` for `|D| ≤ B` a.e. and `D` centered. -/
theorem offDiag_eLpNorm_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ), 1 ≤ N → ∀ (D : α → α → ℝ) (B : ℝ), Measurable (Function.uncurry D) →
      (∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B) →
      (∀ᵐ x ∂μ, ∫ y, D x y ∂μ = 0) → (∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0) →
      eLpNorm (offDiag D N) ((2 * k : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => μ) ≤
        c * ENNReal.ofReal B := by
  obtain ⟨C, hC0, hC⟩ := Sec6.ustat_moment_bound k
  refine ⟨ENNReal.ofReal (C ^ (((2 * k : ℕ) : ℝ)⁻¹)), ENNReal.ofReal_ne_top, ?_⟩
  intro α _ μ _ N hN D B hD hB hX hY
  have hB0 : 0 ≤ B := by
    obtain ⟨z, hz⟩ := hB.exists
    exact (abs_nonneg _).trans hz
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hk0 : 2 * k ≠ 0 := by omega
  have hmom := hC α μ N D B hD hB hX hY
  -- measurability and a.e. boundedness
  have hfm : Measurable (offDiag D N) := measurable_offDiag hD N
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ),
      ∀ l m : Fin N, l ≠ m → |D (ω l) (ω m)| ≤ B := by
    rw [ae_all_iff]; intro l
    rw [ae_all_iff]; intro m
    by_cases hlm : l = m
    · exact Eventually.of_forall fun ω h => absurd hlm h
    · exact ((Sec6.measurePreserving_pair μ N hlm).quasiMeasurePreserving.ae hB).mono
        fun ω h _ => h
  have hbd : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ), ‖offDiag D N ω‖ ≤ N * B := by
    filter_upwards [hall] with ω hω
    unfold offDiag
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hNpos)]
    have hS : |∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0| ≤ N * N * B := by
      calc _ ≤ ∑ l : Fin N, |∑ m : Fin N, if l < m then D (ω l) (ω m) else 0| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l : Fin N, ∑ m : Fin N, |if l < m then D (ω l) (ω m) else 0| :=
            Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _l : Fin N, ∑ _m : Fin N, B :=
            Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => by
              split_ifs with h
              · exact hω l m h.ne
              · simpa using hB0
        _ = N * N * B := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    calc (N : ℝ)⁻¹ * |∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0|
        ≤ (N : ℝ)⁻¹ * (N * N * B) := by gcongr
      _ = N * B := by field_simp
  have hmem : MemLp (offDiag D N) ((2 * k : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => μ) :=
    (memLp_top_of_bound hfm.aestronglyMeasurable (N * B) hbd).mono_exponent le_top
  have hp1 : ((2 * k : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk0
  have hp2 : ((2 * k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hpr : (((2 * k : ℕ) : ℝ≥0∞)).toReal = ((2 * k : ℕ) : ℝ) := ENNReal.toReal_natCast _
  rw [hmem.eLpNorm_eq_integral_rpow_norm hp1 hp2, hpr]
  -- the integral
  have hint_eq : ∫ ω, ‖offDiag D N ω‖ ^ ((2 * k : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin N => μ) =
      ((N : ℝ)⁻¹) ^ (2 * k) *
        ∫ ω, (∑ l : Fin N, ∑ m : Fin N, if l < m then D (ω l) (ω m) else 0) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show ‖offDiag D N ω‖ ^ ((2 * k : ℕ) : ℝ) = _
    rw [Real.rpow_natCast, Real.norm_eq_abs, (even_two_mul k).pow_abs]
    unfold offDiag
    rw [mul_pow]
  have hI : ∫ ω, ‖offDiag D N ω‖ ^ ((2 * k : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin N => μ) ≤
      C * B ^ (2 * k) := by
    rw [hint_eq]
    have h2 := mul_le_mul_of_nonneg_left hmom
      (by positivity : (0 : ℝ) ≤ ((N : ℝ)⁻¹) ^ (2 * k))
    refine h2.trans (le_of_eq ?_)
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    rw [inv_pow]; field_simp
  have hnn : 0 ≤ ∫ ω, ‖offDiag D N ω‖ ^ ((2 * k : ℕ) : ℝ) ∂(Measure.pi fun _ : Fin N => μ) :=
    integral_nonneg fun _ => by positivity
  calc ENNReal.ofReal ((∫ ω, ‖offDiag D N ω‖ ^ ((2 * k : ℕ) : ℝ)
          ∂(Measure.pi fun _ : Fin N => μ)) ^ (((2 * k : ℕ) : ℝ)⁻¹))
      ≤ ENNReal.ofReal ((C * B ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hnn hI (by positivity))
    _ = ENNReal.ofReal (C ^ (((2 * k : ℕ) : ℝ)⁻¹)) * ENNReal.ofReal B := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hC0 _), Real.mul_rpow hC0 (pow_nonneg hB0 _),
          Real.pow_rpow_inv_natCast hB0 hk0]

/-- `Ugen D N = offDiag + diagonal`, and `‖Ugen D N‖_{2k} ≤ c_k B + δ`. -/
theorem Ugen_eLpNorm_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ), 1 ≤ N → ∀ (D : α → α → ℝ) (B δ : ℝ), Measurable (Function.uncurry D) →
      (∀ x y, D x y = D y x) → (∀ x, ∫ y, D x y ∂μ = 0) →
      (∀ᵐ z ∂(μ.prod μ), |D z.1 z.2| ≤ B) → (∀ᵐ x ∂μ, |D x x| ≤ δ) →
      eLpNorm (Ugen D N) ((2 * k : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => μ) ≤
        c * ENNReal.ofReal B + ENNReal.ofReal δ := by
  obtain ⟨c, hc, hcb⟩ := offDiag_eLpNorm_le k hk
  refine ⟨c, hc, ?_⟩
  intro α _ μ _ N hN D B δ hD hsymm hcent hB hδ
  have hY : ∀ᵐ y ∂μ, ∫ x, D x y ∂μ = 0 := Eventually.of_forall fun y => by
    simp_rw [hsymm _ y]; exact hcent y
  have hoff := hcb α μ N hN D B hD hB (Eventually.of_forall hcent) hY
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ0 : 0 ≤ δ := by
    obtain ⟨x, hx⟩ := hδ.exists
    exact (abs_nonneg _).trans hx
  have hgm : Measurable (fun X : Fin N → α => (2 * (N : ℝ))⁻¹ * ∑ i, D (X i) (X i)) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    have h2 : Measurable (fun X : Fin N → α => (X i, X i)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply i)
    exact hD.comp h2
  have hall : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i, |D (X i) (X i)| ≤ δ := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hδ
  have hgb : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ),
      ‖(2 * (N : ℝ))⁻¹ * ∑ i, D (X i) (X i)‖ ≤ δ := by
    filter_upwards [hall] with X hX
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (mul_pos two_pos hNpos))]
    have hs : |∑ i, D (X i) (X i)| ≤ N * δ := by
      calc _ ≤ ∑ i, |D (X i) (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, δ := Finset.sum_le_sum fun i _ => hX i
        _ = N * δ := by simp
    calc (2 * (N : ℝ))⁻¹ * |∑ i, D (X i) (X i)| ≤ (2 * (N : ℝ))⁻¹ * (N * δ) := by gcongr
      _ = δ / 2 := by field_simp
      _ ≤ δ := by linarith
  have hgn : eLpNorm (fun X : Fin N → α => (2 * (N : ℝ))⁻¹ * ∑ i, D (X i) (X i))
      ((2 * k : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => μ) ≤ ENNReal.ofReal δ := by
    refine (eLpNorm_le_of_ae_bound hgm.aestronglyMeasurable hgb).trans ?_
    simp
  have heq : Ugen D N = (offDiag D N) +
      (fun X : Fin N → α => (2 * (N : ℝ))⁻¹ * ∑ i, D (X i) (X i)) := by
    funext X; exact Ugen_eq_offDiag_add hsymm N X
  have hp1 : (1 : ℝ≥0∞) ≤ ((2 * k : ℕ) : ℝ≥0∞) := by
    have : (1 : ℕ) ≤ 2 * k := by omega
    exact_mod_cast this
  rw [heq]
  exact (eLpNorm_add_le hp1).trans (add_le_add hoff hgn)

end Generic

/-! ### The kernels of the paper -/

section Specific

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The difference kernel `D = K - K_R` for the family `f` of functions. -/
noncomputable def Dk (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (s : Finset ℕ)
    (a : ℕ → ℕ → ℝ) (f : ℕ → Torus d → ℝ) (x y : Torus d) : ℝ :=
  centeredKernel W μ x y - kerFR s a f x y

lemma Dk_symm (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) {s : Finset ℕ} {a : ℕ → ℕ → ℝ}
    {f : ℕ → Torus d → ℝ} (ha : ∀ i j, a i j = a j i) (x y : Torus d) :
    Dk W μ s a f x y = Dk W μ s a f y x := by
  unfold Dk
  have h : centeredKernel W μ x y = centeredKernel W μ y x := by
    unfold centeredKernel; rw [hyp.symm x y]; ring
  rw [h, kerFR_symm ha x y]

lemma measurable_Dk (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → Torus d → ℝ} (hf : ∀ j, Measurable (f j)) :
    Measurable (Function.uncurry (Dk W μ s a f)) :=
  (measurable_centeredKernel hyp μ).sub (measurable_kerFR hf)

lemma integral_Dk (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {s : Finset ℕ} {a : ℕ → ℕ → ℝ} {f : ℕ → Torus d → ℝ}
    (hint : ∀ j, Integrable (f (j + 1)) μ) (hcen : ∀ j, ∫ y, f (j + 1) y ∂μ = 0)
    (x : Torus d) : ∫ y, Dk W μ s a f x y ∂μ = 0 := by
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μ
  have hK : Integrable (fun y => centeredKernel W μ x y) μ :=
    Integrable.of_bound
      (((measurable_centeredKernel hyp μ).comp measurable_prodMk_left).aestronglyMeasurable) B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB x y)
  unfold Dk
  rw [integral_sub hK (integrable_kerFR_right hint x), integral_centeredKernel hyp μ x,
    integral_kerFR_right hint hcen x, sub_zero]

lemma mul_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (c : ℝ) (f : ι → κ → ℝ) :
    c * ∑ i ∈ s, ∑ j ∈ t, f i j = ∑ i ∈ s, ∑ j ∈ t, c * f i j := by
  simp_rw [Finset.mul_sum]

/-- The identity `U_{N,R} = Ugen K_R N`. -/
lemma URN_eq_Ugen {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (A : FiniteRankApprox W μ e) (R : ℕ) {N : ℕ} (hN : 1 ≤ N) (X : Config N d) :
    URN A R N X = Ugen (kerFR (A.s R) (A.a R) e) N X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (N : ℝ) ^ (-(1 / 2 : ℝ)) * (N : ℝ) ^ (-(1 / 2 : ℝ)) = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_add hN']; norm_num [Real.rpow_neg_one]
  have e1 : ∀ i j, ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (i + 1) (X l)) *
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (j + 1) (X l)) =
        (N : ℝ)⁻¹ * ∑ l, ∑ m, e (i + 1) (X l) * e (j + 1) (X m) := by
    intro i j
    rw [← hc, ← Finset.sum_mul_sum]; ring
  have hN0 : (N : ℝ) ≠ 0 := hN'.ne'
  have h4 := sum_four_comm (Finset.univ : Finset (Fin N)) (A.s R)
    (fun l m i j => A.a R i j * e (i + 1) (X l) * e (j + 1) (X m))
  beta_reduce at h4
  unfold URN uR fluct Ugen kerFR
  beta_reduce
  rw [h4, mul_sum_sum, mul_sum_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have key : ∑ l : Fin N, ∑ m : Fin N, A.a R i j * e (i + 1) (X l) * e (j + 1) (X m) =
      A.a R i j * ∑ l : Fin N, ∑ m : Fin N, e (i + 1) (X l) * e (j + 1) (X m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [key, mul_assoc (A.a R i j), e1]
  field_simp

lemma exists_measurable_version (μ : Measure (Torus d)) (e : ℕ → Torus d → ℝ)
    (he : ∀ j, AEStronglyMeasurable (e j) μ) :
    ∃ e' : ℕ → Torus d → ℝ, (∀ j, Measurable (e' j)) ∧ ∀ᵐ x ∂μ, ∀ j, e j x = e' j x := by
  refine ⟨fun j => (he j).mk (e j), fun j => (he j).measurable_mk, ?_⟩
  rw [ae_all_iff]
  exact fun j => (he j).ae_eq_mk

lemma exists_exponent (q : ℝ≥0∞) (hqtop : q ≠ ⊤) :
    ∃ k : ℕ, 1 ≤ k ∧ q ≤ ((2 * k : ℕ) : ℝ≥0∞) := by
  refine ⟨⌈q.toReal⌉₊ + 1, by omega, ?_⟩
  have h1 : q.toReal ≤ (((2 * (⌈q.toReal⌉₊ + 1) : ℕ)) : ℝ) := by
    have h2 : q.toReal ≤ (⌈q.toReal⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : (⌈q.toReal⌉₊ : ℝ) ≤ (((2 * (⌈q.toReal⌉₊ + 1) : ℕ)) : ℝ) := by
      exact_mod_cast (by omega : ⌈q.toReal⌉₊ ≤ 2 * (⌈q.toReal⌉₊ + 1))
    exact h2.trans h3
  calc q = ENNReal.ofReal q.toReal := (ENNReal.ofReal_toReal hqtop).symm
    _ ≤ ENNReal.ofReal (((2 * (⌈q.toReal⌉₊ + 1) : ℕ)) : ℝ) := ENNReal.ofReal_le_ofReal h1
    _ = _ := ENNReal.ofReal_natCast _

/-- A.e. bound for `D = K - K_R'` on `μ ⊗ μ` from the `L^∞` bound on `Config 2 d`. -/
lemma ae_abs_Dk_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (s : Finset ℕ)
    (a : ℕ → ℕ → ℝ) (e e' : ℕ → Torus d → ℝ) (hee' : ∀ᵐ x ∂μ, ∀ j, e j x = e' j x)
    (B : ℝ≥0∞) (hBt : B ≠ ⊤)
    (hB : eLpNorm (fun X : Config 2 d => kerC (kerFR s a e) X - kerC (centeredKernel W μ) X) ⊤
      (Measure.pi fun _ : Fin 2 => μ) ≤ B) :
    ∀ᵐ z ∂(μ.prod μ), |Dk W μ s a e' z.1 z.2| ≤ B.toReal := by
  set F : Config 2 d → ℝ :=
    fun X => kerC (kerFR s a e) X - kerC (centeredKernel W μ) X with hF
  have h1 : ∀ᵐ X ∂(Measure.pi fun _ : Fin 2 => μ), ‖F X‖ₑ ≤ B :=
    (enorm_ae_le_eLpNormEssSup F _).mono
      fun X hX => hX.trans (eLpNormEssSup_le_eLpNorm_top.trans hB)
  have h2 : ∀ᵐ z ∂(μ.prod μ),
      ‖F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Torus d)).symm z)‖ₑ ≤ B :=
    ((measurePreserving_piFinTwo (fun _ : Fin 2 => μ)).symm
      (MeasurableEquiv.piFinTwo _)).quasiMeasurePreserving.ae h1
  have h3 : ∀ᵐ z ∂(μ.prod μ), (∀ j, e j z.1 = e' j z.1) ∧ ∀ j, e j z.2 = e' j z.2 :=
    (measurePreserving_fst.quasiMeasurePreserving.ae hee').and
      (measurePreserving_snd.quasiMeasurePreserving.ae hee')
  filter_upwards [h2, h3] with z hz1 hz2
  have hz : F ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Torus d)).symm z) =
      kerFR s a e z.1 z.2 - centeredKernel W μ z.1 z.2 := by
    rfl
  rw [hz, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_iff_le_toReal hBt] at hz1
  have hk : kerFR s a e z.1 z.2 = kerFR s a e' z.1 z.2 := kerFR_congr hz2.1 hz2.2
  have hD : Dk W μ s a e' z.1 z.2 = -(kerFR s a e z.1 z.2 - centeredKernel W μ z.1 z.2) := by
    unfold Dk; rw [hk]; ring
  rw [hD, abs_neg]
  exact hz1

/-- A.e. bound for the diagonal of `D = K - K_R'`. -/
lemma ae_abs_Dk_diag_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (s : Finset ℕ)
    (a : ℕ → ℕ → ℝ) (e e' : ℕ → Torus d → ℝ) (hee' : ∀ᵐ x ∂μ, ∀ j, e j x = e' j x)
    (δ : ℝ≥0∞) (hδt : δ ≠ ⊤)
    (hδ : eLpNorm (fun x => kerFR s a e x x - centeredKernel W μ x x) ⊤ μ ≤ δ) :
    ∀ᵐ x ∂μ, |Dk W μ s a e' x x| ≤ δ.toReal := by
  have h1 : ∀ᵐ x ∂μ, ‖kerFR s a e x x - centeredKernel W μ x x‖ₑ ≤ δ :=
    (enorm_ae_le_eLpNormEssSup (fun x => kerFR s a e x x - centeredKernel W μ x x) μ).mono
      fun x hx => hx.trans (eLpNormEssSup_le_eLpNorm_top.trans hδ)
  filter_upwards [h1, hee'] with x hx1 hx2
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_iff_le_toReal hδt] at hx1
  have hk : kerFR s a e x x = kerFR s a e' x x := kerFR_congr hx2 hx2
  have hD : Dk W μ s a e' x x = -(kerFR s a e x x - centeredKernel W μ x x) := by
    unfold Dk; rw [hk]; ring
  rw [hD, abs_neg]
  exact hx1

end Specific

end Rank1

/-! ### The theorem -/

/-- **Lemma 6.1, first conclusion** (`rank_errors`, part 1): for every finite `q ≥ 1`,
`sup_{N ≥ 1} ‖U_N - U_{N,R}‖_{L^q(μ^{⊗N})} → 0` as `R → ∞`. -/
theorem rank_errors_part1 {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (μ : ProbabilityMeasure (Torus d))
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
          eLpNorm (fun X => Ucentered W μ N X - URN A R N X) q
            (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))))
        atTop (𝓝 0) := by
  intro q hq1 hqtop
  have : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
  obtain ⟨k, hk1, hqk⟩ := Rank1.exists_exponent q hqtop
  obtain ⟨c, hc, hcb⟩ := Rank1.Ugen_eLpNorm_le k hk1
  obtain ⟨e', he'm, he'ae⟩ := Rank1.exists_measurable_version (μ : Measure (Torus d)) e
    (fun j => (he.memH1 j).2.1.aestronglyMeasurable)
  have hint : ∀ j, Integrable (e' (j + 1)) (μ : Measure (Torus d)) := fun j =>
    (MemLp.integrable one_le_two (he.memH1 (j + 1)).2.1).congr
      (he'ae.mono fun x hx => hx (j + 1))
  have hcen : ∀ j, ∫ y, e' (j + 1) y ∂(μ : Measure (Torus d)) = 0 := fun j => by
    have h0 := he.orthonormal (j + 1) 0
    rw [he.zero] at h0
    simp at h0
    exact (integral_congr_ae (he'ae.mono fun x hx => (hx (j + 1)).symm)).trans h0
  -- the two rates
  have hε : Tendsto (fun R => eLpNorm (fun X : Config 2 d =>
      kerC (Rank1.kerFR (A.s R) (A.a R) e) X - kerC (centeredKernel W μ) X) ⊤
      (Measure.pi fun _ : Fin 2 => (μ : Measure (Torus d)))) atTop (𝓝 0) := A.approx.2.1
  have hδ : Tendsto (fun R => eLpNorm (fun x =>
      Rank1.kerFR (A.s R) (A.a R) e x x - centeredKernel W μ x x) ⊤
      (μ : Measure (Torus d))) atTop (𝓝 0) := A.approx.2.2.2.2.1
  have hgoal := (ENNReal.Tendsto.const_mul hε (Or.inr hc)).add hδ
  rw [mul_zero, add_zero] at hgoal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgoal
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hε.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1)),
    hδ.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))] with R hεR hδR
  refine iSup₂_le fun N hN => ?_
  have hN1 : 1 ≤ N := hN
  set ε : ℝ≥0∞ := eLpNorm (fun X : Config 2 d =>
      kerC (Rank1.kerFR (A.s R) (A.a R) e) X - kerC (centeredKernel W μ) X) ⊤
      (Measure.pi fun _ : Fin 2 => (μ : Measure (Torus d))) with hεdef
  set δ : ℝ≥0∞ := eLpNorm (fun x => Rank1.kerFR (A.s R) (A.a R) e x x -
      centeredKernel W μ x x) ⊤ (μ : Measure (Torus d)) with hδdef
  have hεt : ε ≠ ⊤ := (hεR.trans ENNReal.one_lt_top).ne
  have hδt : δ ≠ ⊤ := (hδR.trans ENNReal.one_lt_top).ne
  -- reduce the exponent
  refine (eLpNorm_le_eLpNorm_of_exponent_le hqk).trans ?_
  -- replace `e` by `e'`
  have hG : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => (μ : Measure (Torus d))),
      ∀ l, ∀ j, e j (X l) = e' j (X l) := by
    rw [ae_all_iff]
    intro l
    exact (measurePreserving_eval (fun _ : Fin N => (μ : Measure (Torus d))) l
      ).quasiMeasurePreserving.ae he'ae
  have hcongr : (fun X => Ucentered W μ N X - URN A R N X) =ᵐ[Measure.pi fun _ : Fin N =>
      (μ : Measure (Torus d))] Ugen (Rank1.Dk W μ (A.s R) (A.a R) e') N := by
    filter_upwards [hG] with X hX
    have h1 : Ucentered W μ N X = Ugen (centeredKernel W μ) N X := rfl
    rw [h1, Rank1.URN_eq_Ugen A R hN1 X]
    have h2 := Ugen_sub (centeredKernel W μ) (Rank1.kerFR (A.s R) (A.a R) e) N X
    rw [← h2]
    unfold Ugen
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    beta_reduce
    unfold Rank1.Dk
    rw [Rank1.kerFR_congr (hX i) (hX j)]
  rw [eLpNorm_congr_ae hcongr]
  have hsymm : ∀ x y, Rank1.Dk W μ (A.s R) (A.a R) e' x y = Rank1.Dk W μ (A.s R) (A.a R) e' y x :=
    Rank1.Dk_symm hyp (μ : Measure (Torus d)) (A.symm R)
  have := hcb (Torus d) (μ : Measure (Torus d)) N hN1 (Rank1.Dk W μ (A.s R) (A.a R) e')
    ε.toReal δ.toReal (Rank1.measurable_Dk hyp _ he'm) hsymm
    (Rank1.integral_Dk hyp _ hint hcen)
    (Rank1.ae_abs_Dk_le _ _ _ e e' he'ae ε hεt le_rfl)
    (Rank1.ae_abs_Dk_diag_le _ _ _ e e' he'ae δ hδt le_rfl)
  rwa [ENNReal.ofReal_toReal hεt, ENNReal.ofReal_toReal hδt] at this

end SharpLSI.FL
