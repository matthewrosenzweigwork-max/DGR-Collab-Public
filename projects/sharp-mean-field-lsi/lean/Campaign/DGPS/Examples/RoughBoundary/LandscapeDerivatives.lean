import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import DGPS.Examples.RoughBoundary.LandscapeLimit
import DGPS.Examples.RoughBoundary.Landscape
import DGPS.Examples.RoughBoundary.SymmetryRetention

/-!
# Compact uniform convergence of parameter derivatives (RUF021)

Source `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 3.1.  For the log-moment generating
function `Λ_{L,ε}(t) = log ∫ exp ⟪t, U_{L,ε}⟫ dm` (`featureLogPartition (Ufeat L ε)`), all `t`-derivatives
on a closed ball `B̄_R` converge as `L → ∞` (for `ε = 0`) to those of `Λ∞ = logPartition`, and
`‖Λ_{L,ε} - Λ_{L,0}‖_{C^k(B̄_R)} ≤ C_{k,R} |ε| ‖g‖∞` uniformly in `L > 0`.

The proof is organised as a generic parametric-integral calculus: for a smooth integrand
`Φ(u, t)` and a feature map `V` with `‖V‖ ≤ 1` a.e., `t ↦ ∫ Φ(V ω, t) dμ` is smooth, its `C^k(B̄_R)`
bounds are uniform in `(μ, V)`, they are Lipschitz in `V`, and weak convergence of the laws of
`V` gives `C^k(B̄_R)` convergence (pointwise convergence plus uniform Lipschitz bounds and a finite
net, applied inductively to the `t`-derivative integrands).  `Z ≥ e^{-R}` then lets the
logarithm be handled by `ckBound_log_sub`.

Main result:
`DGPS.Examples.RoughBoundary.Landscape.compact_uniform_convergence_of_parameter_derivatives`.
-/

open MeasureTheory Set Metric
open scoped ContDiff BoundedContinuousFunction Real

universe u

namespace DGPS.Examples.RoughBoundary.Landscape

section ck
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- `‖D^j f(t)‖ ≤ M` for all `j ≤ k` and `t ∈ S`: a `C^k(S)` seminorm bound. -/
def ckBound (S : Set E) (k : ℕ) (f : E → F) (M : ℝ) : Prop :=
  ∀ t ∈ S, ∀ j ≤ k, ‖iteratedFDeriv ℝ j f t‖ ≤ M

lemma ckBound_mono {S : Set E} {k : ℕ} {f : E → F} {M M' : ℝ} (h : ckBound S k f M)
    (hM : M ≤ M') : ckBound S k f M' := fun t ht j hj => (h t ht j hj).trans hM

lemma ckBound_le_k {S : Set E} {k k' : ℕ} {f : E → F} {M : ℝ} (h : ckBound S k f M)
    (hk : k' ≤ k) : ckBound S k' f M := fun t ht j hj => h t ht j (hj.trans hk)

lemma ckBound_smul {S : Set E} {k : ℕ} {f : E → ℝ} {g : E → F} {M₁ M₂ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (h₁ : ckBound S k f M₁) (h₂ : ckBound S k g M₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) : ckBound S k (fun t => f t • g t) (2 ^ k * M₁ * M₂) := by
  intro t ht n hn
  refine (norm_iteratedFDeriv_smul_le hf hg t (by exact_mod_cast le_top)).trans ?_
  calc ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f t‖ *
        ‖iteratedFDeriv ℝ (n - i) g t‖
      ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M₁ * M₂ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have a1 := h₁ t ht i (hi'.trans hn)
        have a2 := h₂ t ht (n - i) ((Nat.sub_le _ _).trans hn)
        have := mul_le_mul a1 a2 (norm_nonneg _) hM₁
        calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f t‖ * ‖iteratedFDeriv ℝ (n - i) g t‖
            = (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i f t‖ * ‖iteratedFDeriv ℝ (n - i) g t‖) := by
              ring
          _ ≤ (n.choose i : ℝ) * (M₁ * M₂) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
          _ = _ := by ring
    _ = 2 ^ n * M₁ * M₂ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose n
    _ ≤ 2 ^ k * M₁ * M₂ := by
        have : (2 : ℝ) ^ n ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hn
        have := mul_le_mul_of_nonneg_right this hM₁
        exact mul_le_mul_of_nonneg_right this hM₂


lemma ckBound_neg {S : Set E} {k : ℕ} {f : E → F} {M : ℝ} (h : ckBound S k f M) :
    ckBound S k (fun t => -f t) M := by
  intro t ht j hj
  have : iteratedFDeriv ℝ j (fun t => -f t) t = -iteratedFDeriv ℝ j f t := iteratedFDeriv_neg_apply
  rw [this, norm_neg]
  exact h t ht j hj

lemma ckBound_sub {S : Set E} {k : ℕ} {f g : E → F} {M₁ M₂ : ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h₁ : ckBound S k f M₁) (h₂ : ckBound S k g M₂) :
    ckBound S k (fun t => f t - g t) (M₁ + M₂) := by
  intro t ht j hj
  have : iteratedFDeriv ℝ j (fun t => f t - g t) t = iteratedFDeriv ℝ j f t - iteratedFDeriv ℝ j g t :=
    iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [this]
  exact (norm_sub_le _ _).trans (add_le_add (h₁ t ht j hj) (h₂ t ht j hj))

lemma ckBound_add {S : Set E} {k : ℕ} {f g : E → F} {M₁ M₂ : ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (h₁ : ckBound S k f M₁) (h₂ : ckBound S k g M₂) :
    ckBound S k (fun t => f t + g t) (M₁ + M₂) := by
  intro t ht j hj
  have : iteratedFDeriv ℝ j (fun t => f t + g t) t = iteratedFDeriv ℝ j f t + iteratedFDeriv ℝ j g t :=
    iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (h₁ t ht j hj) (h₂ t ht j hj))

/-- Bounds on derivatives of order `j + 1` are bounds on derivatives of order `j` of `fderiv`. -/
lemma ckBound_fderiv {S : Set E} {k : ℕ} {f : E → F} {M : ℝ} (h : ckBound S (k + 1) f M) :
    ckBound S k (fderiv ℝ f) M := by
  intro t ht j hj
  rw [norm_iteratedFDeriv_fderiv]
  exact h t ht (j + 1) (by omega)

lemma ckBound_of_fderiv {S : Set E} {k : ℕ} {f : E → F} {M : ℝ} (h0 : ∀ t ∈ S, ‖f t‖ ≤ M)
    (h : ckBound S k (fderiv ℝ f) M) : ckBound S (k + 1) f M := by
  intro t ht j hj
  rcases j with _ | j
  · simpa using h0 t ht
  · rw [← norm_iteratedFDeriv_fderiv]
    exact h t ht j (by omega)

lemma fderiv_inv_fun {f : E → ℝ} (hf : Differentiable ℝ f) (h0 : ∀ t, 0 < f t) :
    fderiv ℝ (fun t => (f t)⁻¹) = fun t => (-((f t)⁻¹ * (f t)⁻¹)) • fderiv ℝ f t := by
  funext t
  have h1 := (hasDerivAt_inv (h0 t).ne').comp_hasFDerivAt t (hf t).hasFDerivAt
  have h2 : HasFDerivAt (fun t => (f t)⁻¹) (-(f t ^ 2)⁻¹ • fderiv ℝ f t) t := h1
  rw [h2.fderiv]
  congr 1
  rw [neg_inj]
  field_simp

lemma contDiff_inv_fun {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : ∀ t, 0 < f t) :
    ContDiff ℝ ∞ (fun t => (f t)⁻¹) :=
  hf.inv (fun t => (h0 t).ne')


lemma ckBound_inv (S : Set E) (k : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : E → ℝ, ContDiff ℝ ∞ f → (∀ t, 0 < f t) → (∀ t ∈ S, c ≤ f t) →
      ckBound S k f M → ckBound S k (fun t => (f t)⁻¹) K := by
  induction k with
  | zero =>
    refine ⟨c⁻¹, by positivity, fun f hf h0 hc' _ => ?_⟩
    intro t ht j hj
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (h0 t))]
    exact inv_anti₀ hc (hc' t ht)
  | succ k ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    refine ⟨max K (2 ^ k * (2 ^ k * K * K) * M), le_max_of_le_left hK0, fun f hf h0 hc' hb => ?_⟩
    have hbk : ckBound S k f M := ckBound_le_k hb (Nat.le_succ k)
    have hKf := hK f hf h0 hc' hbk
    have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
    have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
    have hinv : ContDiff ℝ ∞ (fun t => (f t)⁻¹) := contDiff_inv_fun hf h0
    have hprod : ckBound S k (fun t => (-((f t)⁻¹ * (f t)⁻¹))) (2 ^ k * K * K) := by
      have := ckBound_smul hinv hinv hKf hKf hK0 hK0
      simpa [smul_eq_mul] using ckBound_neg this
    have hprodc : ContDiff ℝ ∞ (fun t => (-((f t)⁻¹ * (f t)⁻¹))) :=
      (hinv.mul hinv).neg
    have hfd : ckBound S k (fderiv ℝ f) M := ckBound_fderiv hb
    have hfinal := ckBound_smul hprodc hdf hprod hfd (by positivity) hM
    rw [← fderiv_inv_fun hdiff h0] at hfinal
    refine ckBound_of_fderiv (fun t ht => ?_) (ckBound_mono hfinal (le_max_right _ _))
    exact (hKf t ht 0 (Nat.zero_le _)).trans' (by simp) |>.trans (le_max_left _ _)


lemma fderiv_log_fun {f : E → ℝ} (hf : Differentiable ℝ f) (h0 : ∀ t, 0 < f t) :
    fderiv ℝ (fun t => Real.log (f t)) = fun t => (f t)⁻¹ • fderiv ℝ f t := by
  funext t
  exact ((hf t).hasFDerivAt.log (h0 t).ne').fderiv

lemma abs_log_sub_log_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / c := by
  have ha0 : 0 < a := hc.trans_le ha
  have hb0 : 0 < b := hc.trans_le hb
  have h1 : Real.log a - Real.log b ≤ |a - b| / c := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    refine this.trans ?_
    have e : a / b - 1 = (a - b) / b := by field_simp
    rw [e]
    calc (a - b) / b ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hb
  have h2 : Real.log b - Real.log a ≤ |a - b| / c := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    refine this.trans ?_
    have e : b / a - 1 = (b - a) / a := by field_simp
    rw [e]
    calc (b - a) / a ≤ |b - a| / a := div_le_div_of_nonneg_right (le_abs_self _) ha0.le
      _ = |a - b| / a := by rw [abs_sub_comm]
      _ ≤ |a - b| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc ha
  rw [abs_le]
  constructor <;> linarith

lemma ckBound_log_sub (S : Set E) (k : ℕ) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : E → ℝ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → (∀ t, 0 < f t) →
      (∀ t, 0 < g t) → (∀ t ∈ S, c ≤ f t) → (∀ t ∈ S, c ≤ g t) → ckBound S k f M →
      ckBound S k g M → ∀ η : ℝ, 0 ≤ η → ckBound S k (fun t => f t - g t) η →
      ckBound S k (fun t => Real.log (f t) - Real.log (g t)) (K * η) := by
  induction k with
  | zero =>
    refine ⟨c⁻¹, by positivity, fun f g hf hg hf0 hg0 hfc hgc _ _ η hη hd => ?_⟩
    intro t ht j hj
    obtain rfl : j = 0 := by omega
    have := hd t ht 0 le_rfl
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this ⊢
    refine (abs_log_sub_log_le hc (hfc t ht) (hgc t ht)).trans ?_
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  | succ k ih =>
    obtain ⟨K, hK0, hK⟩ := ih
    obtain ⟨K₁, hK₁0, hK₁⟩ := ckBound_inv S k hc hM (M := M)
    set C : ℝ := 2 ^ k * K₁ + 2 ^ k * (2 ^ k * K₁ * (2 ^ k * K₁)) * M with hC
    have hC0 : 0 ≤ C := by positivity
    refine ⟨max K C, le_max_of_le_left hK0, fun f g hf hg hf0 hg0 hfc hgc hbf hbg η hη hd => ?_⟩
    have hbfk := ckBound_le_k hbf (Nat.le_succ k)
    have hbgk := ckBound_le_k hbg (Nat.le_succ k)
    have hdk : ckBound S k (fun t => f t - g t) η := ckBound_le_k hd (Nat.le_succ k)
    have hlog := hK f g hf hg hf0 hg0 hfc hgc hbfk hbgk η hη hdk
    have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
    have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by exact_mod_cast le_rfl)
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hgd : Differentiable ℝ g := hg.differentiable (by simp)
    have hfi := hK₁ f hf hf0 hfc hbfk
    have hgi := hK₁ g hg hg0 hgc hbgk
    have hfic : ContDiff ℝ ∞ (fun t => (f t)⁻¹) := contDiff_inv_fun hf hf0
    have hgic : ContDiff ℝ ∞ (fun t => (g t)⁻¹) := contDiff_inv_fun hg hg0
    -- derivative of the difference
    have hdd : ckBound S k (fderiv ℝ (fun t => f t - g t)) η := ckBound_fderiv hd
    have e1 : fderiv ℝ (fun t => f t - g t) = fun t => fderiv ℝ f t - fderiv ℝ g t := by
      funext t; exact fderiv_sub (hfd t) (hgd t)
    rw [e1] at hdd
    -- inverse difference
    have hdc : ContDiff ℝ ∞ (fun t => f t - g t) := hf.sub hg
    have hdinv : ckBound S k (fun t => (f t)⁻¹ - (g t)⁻¹) (2 ^ k * K₁ * (2 ^ k * K₁ * η)) := by
      have hneg : ckBound S k (fun t => -(f t - g t)) η := ckBound_neg hdk
      have h1 := ckBound_smul hgic hdc.neg hgi hneg hK₁0 hη
      have h2 := ckBound_smul hfic (hgic.smul hdc.neg) hfi h1 hK₁0 (by positivity)
      have e : (fun t => (f t)⁻¹ - (g t)⁻¹) =
          fun t => (f t)⁻¹ • ((g t)⁻¹ • (-(f t - g t))) := by
        funext t
        have := (hf0 t).ne'
        have := (hg0 t).ne'
        simp only [smul_eq_mul]
        field_simp
        ring
      rw [e]
      exact h2
    have hdinvc : ContDiff ℝ ∞ (fun t => (f t)⁻¹ - (g t)⁻¹) := hfic.sub hgic
    have h3 := ckBound_smul hfic (hdf.sub hdg) hfi hdd hK₁0 hη
    have h4 := ckBound_smul hdinvc hdg hdinv (ckBound_fderiv hbg) (by positivity) hM
    have h5 := ckBound_add (hfic.smul (hdf.sub hdg)) (hdinvc.smul hdg) h3 h4
    have e2 : fderiv ℝ (fun t => Real.log (f t) - Real.log (g t)) =
        fun t => (f t)⁻¹ • (fderiv ℝ f t - fderiv ℝ g t) +
          ((f t)⁻¹ - (g t)⁻¹) • fderiv ℝ g t := by
      have hl1 := fderiv_log_fun hfd hf0
      have hl2 := fderiv_log_fun hgd hg0
      funext t
      have hd1 : DifferentiableAt ℝ (fun t => Real.log (f t)) t :=
        ((hfd t).hasFDerivAt.log (hf0 t).ne').differentiableAt
      have hd2 : DifferentiableAt ℝ (fun t => Real.log (g t)) t :=
        ((hgd t).hasFDerivAt.log (hg0 t).ne').differentiableAt
      have h : HasFDerivAt (fun t => Real.log (f t) - Real.log (g t))
          (fderiv ℝ (fun t => Real.log (f t)) t - fderiv ℝ (fun t => Real.log (g t)) t) t :=
        hd1.hasFDerivAt.sub hd2.hasFDerivAt
      rw [h.fderiv, congrFun hl1 t, congrFun hl2 t]
      simp only [smul_sub, sub_smul]
      abel
    have hfin : ckBound S k (fderiv ℝ (fun t => Real.log (f t) - Real.log (g t))) (C * η) := by
      rw [e2]
      refine ckBound_mono h5 (le_of_eq ?_)
      rw [hC]; ring
    refine ckBound_of_fderiv (fun t ht => ?_) (ckBound_mono hfin (mul_le_mul_of_nonneg_right
      (le_max_right _ _) hη))
    have := hlog t ht 0 (Nat.zero_le _)
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hη)

end ck

abbrev E2 : Type := EuclideanSpace ℝ (Fin 2)

section param
variable {Ω : Type*} [MeasurableSpace Ω]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Partial derivative in the second (parameter) variable. -/
noncomputable def pd (Φ : E2 × E2 → F) (p : E2 × E2) : E2 →L[ℝ] F :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inr ℝ E2 E2)

/-- The parametric integral `t ↦ ∫ Φ (V w, t) dμ`. -/
noncomputable def pint (μ : Measure Ω) (V : Ω → E2) (Φ : E2 × E2 → F) (t : E2) : F :=
  ∫ w, Φ (V w, t) ∂μ

lemma hasFDerivAt_pd {Φ : E2 × E2 → F} (hΦ : Differentiable ℝ Φ) (u t : E2) :
    HasFDerivAt (fun s => Φ (u, s)) (pd Φ (u, t)) t :=
  (hΦ (u, t)).hasFDerivAt.comp t (hasFDerivAt_prodMk_right u t)

lemma contDiff_pd {Φ : E2 × E2 → F} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (pd Φ) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  exact h.clm_comp contDiff_const

omit [NormedSpace ℝ F] in
lemma exists_bound_compact {Φ : E2 × E2 → F} (hΦ : Continuous Φ) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ u ∈ closedBall (0 : E2) 1, ∀ t ∈ closedBall (0 : E2) R, ‖Φ (u, t)‖ ≤ M := by
  have hK : IsCompact (closedBall (0 : E2) 1 ×ˢ closedBall (0 : E2) R) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun u hu t ht => (hM (u, t) ⟨hu, ht⟩).trans (le_max_left _ _)⟩

variable {μ : Measure Ω} {V : Ω → E2}

omit [NormedSpace ℝ F] in
lemma aesm_pint {Φ : E2 × E2 → F} (hΦ : Continuous Φ) (hV : Measurable V) (t : E2) :
    AEStronglyMeasurable (fun w => Φ (V w, t)) μ :=
  hΦ.comp_aestronglyMeasurable (hV.aestronglyMeasurable.prodMk aestronglyMeasurable_const)

omit [NormedSpace ℝ F] in
lemma integrable_pint [IsFiniteMeasure μ] {Φ : E2 × E2 → F} (hΦ : Continuous Φ) (hV : Measurable V)
    (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) : Integrable (fun w => Φ (V w, t)) μ := by
  obtain ⟨M, -, hM⟩ := exists_bound_compact hΦ ‖t‖
  refine Integrable.of_bound (aesm_pint hΦ hV t) M (hb.mono fun w hw => ?_)
  exact hM _ (by simpa using hw) t (by simp)

lemma norm_pint_le [IsProbabilityMeasure μ] {Φ : E2 × E2 → F} {R M : ℝ}
    (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1)
    (hM : ∀ u ∈ closedBall (0 : E2) 1, ∀ t ∈ closedBall (0 : E2) R, ‖Φ (u, t)‖ ≤ M)
    {t : E2} (ht : t ∈ closedBall (0 : E2) R) : ‖pint μ V Φ t‖ ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun w => Φ (V w, t)) (C := M)
    (hb.mono fun w hw => hM _ (by simpa using hw) t ht)
  simpa [pint] using this

lemma hasFDerivAt_pint [IsProbabilityMeasure μ] {Φ : E2 × E2 → F} [CompleteSpace F]
    (hΦ : ContDiff ℝ ∞ Φ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t₀ : E2) :
    HasFDerivAt (pint μ V Φ) (pint μ V (pd Φ) t₀) t₀ := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hpc : Continuous (pd Φ) := (contDiff_pd hΦ).continuous
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  obtain ⟨C, -, hC⟩ := exists_bound_compact hpc (‖t₀‖ + 1)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun x w => pd Φ (V w, x)) (ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun x => aesm_pint hΦc hV x) (integrable_pint hΦc hV hb t₀)
    (aesm_pint hpc hV t₀) ?_ (integrable_const C) ?_
  · refine hb.mono fun w hw x hx => hC _ (by simpa using hw) x ?_
    have : ‖x‖ ≤ ‖t₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x t₀
      have h2 : ‖x - t₀‖ < 1 := by simpa [dist_eq_norm] using hx
      linarith
    simpa using this
  · exact Filter.Eventually.of_forall fun w x _ => hasFDerivAt_pd hdiff _ x

lemma fderiv_pint [IsProbabilityMeasure μ] {Φ : E2 × E2 → F} [CompleteSpace F]
    (hΦ : ContDiff ℝ ∞ Φ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) :
    fderiv ℝ (pint μ V Φ) = pint μ V (pd Φ) := by
  funext t; exact (hasFDerivAt_pint hΦ hV hb t).fderiv

lemma contDiff_pint_aux [IsProbabilityMeasure μ] (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) :
    ∀ n : ℕ, ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (Φ : E2 × E2 → G), ContDiff ℝ ∞ Φ → ContDiff ℝ n (pint μ V Φ) := by
  intro n
  induction n with
  | zero =>
    intro G _ _ _ Φ hΦ
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun t => (hasFDerivAt_pint hΦ hV hb t).continuousAt
  | succ n ih =>
    intro G _ _ _ Φ hΦ
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨fun t => (hasFDerivAt_pint hΦ hV hb t).differentiableAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · rw [fderiv_pint hΦ hV hb]
      exact ih (pd Φ) (contDiff_pd hΦ)

lemma contDiff_pint [IsProbabilityMeasure μ] {Φ : E2 × E2 → F} [CompleteSpace F]
    (hΦ : ContDiff ℝ ∞ Φ) (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) :
    ContDiff ℝ ∞ (pint μ V Φ) :=
  contDiff_infty.mpr fun n => contDiff_pint_aux hV hb n Φ hΦ

lemma ckBound_pint_aux (R : ℝ) :
    ∀ k : ℕ, ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (Φ : E2 × E2 → G), ContDiff ℝ ∞ Φ →
      ∃ M, 0 ≤ M ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → E2), Measurable V →
        (∀ᵐ w ∂μ, ‖V w‖ ≤ 1) → ckBound (closedBall (0 : E2) R) k (pint μ V Φ) M := by
  intro k
  induction k with
  | zero =>
    intro G _ _ _ Φ hΦ
    obtain ⟨M, hM0, hM⟩ := exists_bound_compact hΦ.continuous R
    refine ⟨M, hM0, fun μ _ V hV hb t ht j hj => ?_⟩
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    rw [norm_iteratedFDeriv_zero]
    exact norm_pint_le hb hM ht
  | succ k ih =>
    intro G _ _ _ Φ hΦ
    obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_compact hΦ.continuous R
    obtain ⟨M₁, hM₁0, hM₁⟩ := ih (pd Φ) (contDiff_pd hΦ)
    refine ⟨max M₀ M₁, le_max_of_le_left hM₀0, fun μ _ V hV hb => ?_⟩
    refine ckBound_of_fderiv (fun t ht => (norm_pint_le hb hM₀ ht).trans (le_max_left _ _)) ?_
    rw [fderiv_pint hΦ hV hb]
    exact ckBound_mono (hM₁ μ V hV hb) (le_max_right _ _)

/-- Partial derivative in the first variable. -/
noncomputable def pdl (Φ : E2 × E2 → F) (p : E2 × E2) : E2 →L[ℝ] F :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ E2 E2)

lemma contDiff_pdl {Φ : E2 × E2 → F} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (pdl Φ) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ Φ) := hΦ.fderiv_right (by simp)
  exact h.clm_comp contDiff_const

lemma lip_in_u {Φ : E2 × E2 → F} (hΦ : ContDiff ℝ ∞ Φ) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u ∈ closedBall (0 : E2) 1, ∀ u' ∈ closedBall (0 : E2) 1,
      ∀ t ∈ closedBall (0 : E2) R, ‖Φ (u, t) - Φ (u', t)‖ ≤ C * ‖u - u'‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_compact (contDiff_pdl hΦ).continuous R
  refine ⟨C, hC0, fun u hu u' hu' t ht => ?_⟩
  have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hf : ∀ x : E2, HasFDerivAt (fun v => Φ (v, t)) (pdl Φ (x, t)) x := fun x =>
    (hdiff (x, t)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)
  have := (convex_closedBall (0 : E2) 1).norm_image_sub_le_of_norm_fderiv_le
    (f := fun v => Φ (v, t)) (C := C) (fun x _ => (hf x).differentiableAt)
    (fun x hx => by rw [(hf x).fderiv]; exact hC x hx t ht) hu' hu
  simpa using this

lemma ckBound_pint_diff_aux (R : ℝ) :
    ∀ k : ℕ, ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (Φ : E2 × E2 → G), ContDiff ℝ ∞ Φ →
      ∃ C, 0 ≤ C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (V V' : Ω → E2),
        Measurable V → Measurable V' → (∀ᵐ w ∂μ, ‖V w‖ ≤ 1) → (∀ᵐ w ∂μ, ‖V' w‖ ≤ 1) →
        ∀ δ : ℝ, 0 ≤ δ → (∀ᵐ w ∂μ, ‖V w - V' w‖ ≤ δ) →
        ckBound (closedBall (0 : E2) R) k (fun t => pint μ V Φ t - pint μ V' Φ t) (C * δ) := by
  intro k
  induction k with
  | zero =>
    intro G _ _ _ Φ hΦ
    obtain ⟨C, hC0, hC⟩ := lip_in_u hΦ R
    refine ⟨C, hC0, fun μ _ V V' hV hV' hb hb' δ hδ hd t ht j hj => ?_⟩
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    rw [norm_iteratedFDeriv_zero]
    have h1 := integrable_pint hΦ.continuous hV hb t
    have h2 := integrable_pint hΦ.continuous hV' hb' t
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun w => Φ (V w, t) - Φ (V' w, t)) (C := C * δ)
      ((hb.and (hb'.and hd)).mono fun w ⟨a, b, c⟩ =>
        (hC _ (by simpa using a) _ (by simpa using b) t ht).trans
          (mul_le_mul_of_nonneg_left c hC0))
    rw [integral_sub h1 h2] at this
    simpa [pint] using this
  | succ k ih =>
    intro G _ _ _ Φ hΦ
    obtain ⟨C₀, hC₀0, hC₀⟩ := lip_in_u hΦ R
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (pd Φ) (contDiff_pd hΦ)
    refine ⟨max C₀ C₁, le_max_of_le_left hC₀0, fun μ _ V V' hV hV' hb hb' δ hδ hd => ?_⟩
    have hz : ∀ t ∈ closedBall (0 : E2) R,
        ‖pint μ V Φ t - pint μ V' Φ t‖ ≤ max C₀ C₁ * δ := by
      intro t ht
      have h1 := integrable_pint hΦ.continuous hV hb t
      have h2 := integrable_pint hΦ.continuous hV' hb' t
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun w => Φ (V w, t) - Φ (V' w, t)) (C := C₀ * δ)
        ((hb.and (hb'.and hd)).mono fun w ⟨a, b, c⟩ =>
          (hC₀ _ (by simpa using a) _ (by simpa using b) t ht).trans
            (mul_le_mul_of_nonneg_left c hC₀0))
      rw [integral_sub h1 h2] at this
      have h3 : ‖pint μ V Φ t - pint μ V' Φ t‖ ≤ C₀ * δ := by simpa [pint] using this
      exact h3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ)
    refine ckBound_of_fderiv hz ?_
    have e : fderiv ℝ (fun t => pint μ V Φ t - pint μ V' Φ t) =
        fun t => pint μ V (pd Φ) t - pint μ V' (pd Φ) t := by
      funext t
      exact ((hasFDerivAt_pint hΦ hV hb t).sub (hasFDerivAt_pint hΦ hV' hb' t)).fderiv
    rw [e]
    exact ckBound_mono (hC₁ μ V V' hV hV' hb hb' δ hδ hd)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ)

end param

section conv

/-- Radial retraction onto the closed unit ball. -/
noncomputable def clamp (u : E2) : E2 := (max 1 ‖u‖)⁻¹ • u

lemma continuous_clamp : Continuous clamp := by
  unfold clamp
  exact ((continuous_const.max continuous_norm).inv₀
    (fun u => (lt_max_of_lt_left one_pos).ne')).smul continuous_id

lemma norm_clamp_le (u : E2) : ‖clamp u‖ ≤ 1 := by
  unfold clamp
  have h : 0 < max 1 ‖u‖ := lt_max_of_lt_left one_pos
  rw [norm_smul, norm_inv, Real.norm_of_nonneg h.le, inv_mul_le_iff₀ h, mul_one]
  exact le_max_right _ _

lemma clamp_of_norm_le {u : E2} (h : ‖u‖ ≤ 1) : clamp u = u := by
  simp [clamp, max_eq_left h]

lemma tendsto_of_forall_clm {ι : Type*} {l : Filter ι} {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] {x : ι → G} {y : G}
    (h : ∀ ℓ : G →L[ℝ] ℝ, Filter.Tendsto (fun i => ℓ (x i)) l (nhds (ℓ y))) :
    Filter.Tendsto x l (nhds y) := by
  let e := (Module.finBasis ℝ G).equivFunL
  have h1 : Filter.Tendsto (fun i => e (x i)) l (nhds (e y)) := by
    refine tendsto_pi_nhds.mpr fun j => ?_
    exact h ((ContinuousLinearMap.proj j).comp e.toContinuousLinearMap)
  have h2 := (e.symm.continuous.tendsto (e y)).comp h1
  simpa [Function.comp_def] using h2

variable {Ω : Type*} [MeasurableSpace Ω]
variable {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma ell_pint [CompleteSpace G] {m : Measure Ω} [IsProbabilityMeasure m] {V' : Ω → E2}
    (hV : Measurable V') (hb : ∀ᵐ w ∂m, ‖V' w‖ ≤ 1) {Φ : E2 × E2 → G} (hΦ : Continuous Φ)
    (ℓ : G →L[ℝ] ℝ) (t : E2) (f : E2 →ᵇ ℝ) (hf : ∀ u, f u = ℓ (Φ (clamp u, t))) :
    ℓ (pint m V' Φ t) = ∫ w, f (V' w) ∂m := by
  unfold pint
  rw [← ContinuousLinearMap.integral_comp_comm ℓ (integrable_pint hΦ hV hb t)]
  refine integral_congr_ae (hb.mono fun w hw => ?_)
  show ℓ (Φ (V' w, t)) = f (V' w)
  rw [hf, clamp_of_norm_le hw]

lemma tendsto_pint_pointwise {ι : Type*} {l : Filter ι} [CompleteSpace G] [FiniteDimensional ℝ G]
    {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)] {V : ι → Ω → E2} {ν : Measure E2}
    [IsProbabilityMeasure ν]
    (hV : ∀ i, Measurable (V i)) (hb : ∀ i, ∀ᵐ w ∂(μ i), ‖V i w‖ ≤ 1)
    (hν : ∀ᵐ u ∂ν, ‖u‖ ≤ 1)
    (hw : ∀ f : E2 →ᵇ ℝ, Filter.Tendsto (fun i => ∫ w, f (V i w) ∂(μ i)) l
      (nhds (∫ u, f u ∂ν)))
    {Φ : E2 × E2 → G} (hΦ : Continuous Φ) (t : E2) :
    Filter.Tendsto (fun i => pint (μ i) (V i) Φ t) l (nhds (pint ν id Φ t)) := by
  refine tendsto_of_forall_clm fun ℓ => ?_
  obtain ⟨M, -, hM⟩ := exists_bound_compact hΦ ‖t‖
  let f : E2 →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun u => ℓ (Φ (clamp u, t)))
    (ℓ.continuous.comp (hΦ.comp (continuous_clamp.prodMk continuous_const))) (‖ℓ‖ * M)
    (fun u => (ℓ.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hM _ (by simpa using norm_clamp_le u) t (by simp))
        (norm_nonneg _)))
  have hf : ∀ u, f u = ℓ (Φ (clamp u, t)) := fun u => rfl
  have h1 : ∀ i, ℓ (pint (μ i) (V i) Φ t) = ∫ w, f (V i w) ∂(μ i) := fun i =>
    ell_pint (hV i) (hb i) hΦ ℓ t f hf
  have h2 : ℓ (pint ν id Φ t) = ∫ u, f u ∂ν :=
    ell_pint (V' := id) measurable_id hν hΦ ℓ t f hf
  simp only [h1, h2]
  exact hw f

end conv

section param
variable {Ω : Type*} [MeasurableSpace Ω]
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

end param


section conv2
variable {ι : Type*} {l : Filter ι} {Ω : Type*} [MeasurableSpace Ω]
  {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)] {V : ι → Ω → E2} {ν : Measure E2}
  [IsProbabilityMeasure ν]
  (hV : ∀ i, Measurable (V i)) (hb : ∀ i, ∀ᵐ w ∂(μ i), ‖V i w‖ ≤ 1)
  (hν : ∀ᵐ u ∂ν, ‖u‖ ≤ 1)
  (hw : ∀ f : E2 →ᵇ ℝ, Filter.Tendsto (fun i => ∫ w, f (V i w) ∂(μ i)) l
    (nhds (∫ u, f u ∂ν)))
include hV hb hν hw

lemma uniform_pointwise (R : ℝ) {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] [FiniteDimensional ℝ G] {Φ : E2 × E2 → G} (hΦ : ContDiff ℝ ∞ Φ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in l, ∀ t ∈ closedBall (0 : E2) R,
      ‖pint (μ i) (V i) Φ t - pint ν id Φ t‖ ≤ η := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_compact (contDiff_pd hΦ).continuous R
  have hLip : ∀ i, ∀ t ∈ closedBall (0 : E2) R, ∀ s ∈ closedBall (0 : E2) R,
      ‖(pint (μ i) (V i) Φ t - pint ν id Φ t) - (pint (μ i) (V i) Φ s - pint ν id Φ s)‖ ≤
        2 * C * ‖t - s‖ := by
    intro i t ht s hs
    have hd : ∀ x : E2, HasFDerivAt (fun y => pint (μ i) (V i) Φ y - pint ν id Φ y)
        (pint (μ i) (V i) (pd Φ) x - pint ν id (pd Φ) x) x := fun x =>
      (hasFDerivAt_pint hΦ (hV i) (hb i) x).sub (hasFDerivAt_pint hΦ measurable_id hν x)
    have := (convex_closedBall (0 : E2) R).norm_image_sub_le_of_norm_fderiv_le
      (f := fun y => pint (μ i) (V i) Φ y - pint ν id Φ y) (C := 2 * C)
      (fun x _ => (hd x).differentiableAt)
      (fun x hx => by
        rw [(hd x).fderiv]
        refine (norm_sub_le _ _).trans ?_
        have h1 := norm_pint_le (hb i) hC hx
        have h2 := norm_pint_le (μ := ν) (V := id) hν hC hx
        linarith) hs ht
    simpa using this
  set r : ℝ := η / (4 * (C + 1)) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨T, hTs, hTfin, hTcov⟩ := (isCompact_closedBall (0 : E2) R).finite_cover_balls hr0
  have hev : ∀ᶠ i in l, ∀ p ∈ T, ‖pint (μ i) (V i) Φ p - pint ν id Φ p‖ < η / 2 := by
    rw [hTfin.eventually_all]
    intro p _
    have h := tendsto_pint_pointwise hV hb hν hw hΦ.continuous p
    have h0 : Filter.Tendsto (fun i => pint (μ i) (V i) Φ p - pint ν id Φ p) l (nhds 0) := by
      simpa using h.sub_const (pint ν id Φ p)
    have := Metric.tendsto_nhds.mp h0 (η / 2) (by positivity)
    simpa [dist_eq_norm] using this
  refine hev.mono fun i hi t ht => ?_
  obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp (hTcov ht)
  have h1 := hLip i t ht p (hTs hp)
  have h2 := hi p hp
  have h3 : ‖t - p‖ ≤ r := by
    have := mem_ball.mp htp
    rw [dist_eq_norm] at this
    exact this.le
  have h4 : 2 * C * r ≤ η / 2 := by
    calc 2 * C * r = η / 2 * (C / (C + 1)) := by rw [hr]; field_simp; ring
      _ ≤ η / 2 := mul_le_of_le_one_right (by positivity)
          (div_le_one_of_le₀ (by linarith) (by linarith))
  have h5 : ‖pint (μ i) (V i) Φ t - pint ν id Φ t‖ ≤
      ‖pint (μ i) (V i) Φ p - pint ν id Φ p‖ +
        ‖(pint (μ i) (V i) Φ t - pint ν id Φ t) - (pint (μ i) (V i) Φ p - pint ν id Φ p)‖ := by
    have := norm_add_le (pint (μ i) (V i) Φ p - pint ν id Φ p)
      ((pint (μ i) (V i) Φ t - pint ν id Φ t) - (pint (μ i) (V i) Φ p - pint ν id Φ p))
    simpa using this
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * C)]

lemma ckBound_conv_aux (R : ℝ) :
    ∀ k : ℕ, ∀ {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      [FiniteDimensional ℝ G] (Φ : E2 × E2 → G), ContDiff ℝ ∞ Φ →
      ∀ η : ℝ, 0 < η → ∀ᶠ i in l, ckBound (closedBall (0 : E2) R) k
        (fun t => pint (μ i) (V i) Φ t - pint ν id Φ t) η := by
  intro k
  induction k with
  | zero =>
    intro G _ _ _ _ Φ hΦ η hη
    refine (uniform_pointwise hV hb hν hw R hΦ hη).mono fun i hi t ht j hj => ?_
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    rw [norm_iteratedFDeriv_zero]
    exact hi t ht
  | succ k ih =>
    intro G _ _ _ _ Φ hΦ η hη
    filter_upwards [uniform_pointwise hV hb hν hw R hΦ hη,
      ih (pd Φ) (contDiff_pd hΦ) η hη] with i h0 h1
    refine ckBound_of_fderiv h0 ?_
    have e : fderiv ℝ (fun t => pint (μ i) (V i) Φ t - pint ν id Φ t) =
        fun t => pint (μ i) (V i) (pd Φ) t - pint ν id (pd Φ) t := by
      funext t
      exact ((hasFDerivAt_pint hΦ (hV i) (hb i) t).sub
        (hasFDerivAt_pint hΦ measurable_id hν t)).fderiv
    rw [e]
    exact h1

end conv2

section spec

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.ThreeState
open DGPS.Examples.RoughBoundary.Semicontinuity (featureLogPartition)
open DGPS.Examples.RoughBoundary.Spikes (gT)

/-- The exponential integrand `(u, t) ↦ exp ⟪t, u⟫`. -/
noncomputable def expPhi (p : E2 × E2) : ℝ := Real.exp (inner ℝ p.2 p.1)

lemma contDiff_expPhi : ContDiff ℝ ∞ expPhi :=
  Real.contDiff_exp.comp (contDiff_snd.inner ℝ contDiff_fst)

section expint
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {V : Ω → E2}

lemma exp_neg_norm_le_pint (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (t : E2) :
    Real.exp (-‖t‖) ≤ pint μ V expPhi t := by
  have hle : ∀ᵐ w ∂μ, Real.exp (-‖t‖) ≤ expPhi (V w, t) := hb.mono fun w hw => by
    have h1 := abs_real_inner_le_norm t (V w)
    have h2 : ‖t‖ * ‖V w‖ ≤ ‖t‖ := mul_le_of_le_one_right (norm_nonneg _) hw
    have h3 := (abs_le.mp (h1.trans h2)).1
    exact Real.exp_le_exp.mpr h3
  have := integral_mono_ae (integrable_const _) (integrable_pint contDiff_expPhi.continuous hV hb t) hle
  simpa [pint] using this

lemma pint_exp_props (hV : Measurable V) (hb : ∀ᵐ w ∂μ, ‖V w‖ ≤ 1) (R : ℝ) :
    ContDiff ℝ ∞ (pint μ V expPhi) ∧ (∀ t, 0 < pint μ V expPhi t) ∧
      ∀ t ∈ closedBall (0 : E2) R, Real.exp (-R) ≤ pint μ V expPhi t := by
  refine ⟨contDiff_pint contDiff_expPhi hV hb, fun t => ?_, fun t ht => ?_⟩
  · exact lt_of_lt_of_le (Real.exp_pos _) (exp_neg_norm_le_pint hV hb t)
  · refine le_trans (Real.exp_le_exp.mpr ?_) (exp_neg_norm_le_pint hV hb t)
    have := mem_closedBall_zero_iff.mp ht
    linarith

end expint

lemma ae_norm_limitLaw : ∀ᵐ u ∂limitLaw, ‖u‖ ≤ 1 := by
  rw [ae_iff]
  simp only [limitLaw, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp [norm_vertex]

lemma pint_limitLaw (t : E2) :
    pint limitLaw id expPhi t = 1 / 3 * ∑ i, Real.exp (inner ℝ t (vertex i)) := by
  unfold pint limitLaw
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, expPhi]
  · intro i _
    exact integrable_dirac enorm_lt_top

lemma logPartition_eq (t : E2) : logPartition t = Real.log (pint limitLaw id expPhi t) := by
  rw [pint_limitLaw]; rfl

end spec

section assembly

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Semicontinuity (featureLogPartition)
open DGPS.Examples.RoughBoundary.Spikes (gT)

lemma measurable_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) : Measurable (Ufeat L ε) :=
  (continuous_Ufeat hL ε).measurable

lemma ae_norm_Ufeat (L ε : ℝ) : ∀ᵐ y ∂(haar 1), ‖Ufeat L ε y‖ ≤ 1 :=
  Filter.Eventually.of_forall fun y => (norm_Ufeat L ε y).le

lemma featureLogPartition_eq (L ε : ℝ) (t : E2) :
    featureLogPartition (Ufeat L ε) t = Real.log (pint (haar 1) (Ufeat L ε) expPhi t) := rfl

/-- Weak convergence along `L ↦ U_{max L 1, 0}`, from RUF020. -/
lemma weak_conv_Ufeat (f : E2 →ᵇ ℝ) :
    Filter.Tendsto (fun L : ℝ => ∫ w, f (Ufeat (max L 1) 0 w) ∂(haar 1)) Filter.atTop
      (nhds (∫ u, f u ∂limitLaw)) := by
  have h4 := (pushforward_convergence_to_three_states).2.2.2.1 f
  refine h4.congr' ((Filter.eventually_ge_atTop (1 : ℝ)).mono fun L hL => ?_)
  show _ = ∫ w, f (Ufeat (max L 1) 0 w) ∂(haar 1)
  rw [max_eq_left hL, integral_map
    (continuous_Ufeat (by linarith) 0).aemeasurable f.continuous.aestronglyMeasurable]

theorem compact_uniform_convergence_of_parameter_derivatives :
    (∀ (k : ℕ) (R η : ℝ), 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ckBound (closedBall (0 : E2) R) k
        (fun t => featureLogPartition (Ufeat L 0) t - logPartition t) η) ∧
    (∀ (k : ℕ) (R : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ ε : ℝ,
      ckBound (closedBall (0 : E2) R) k
        (fun t => featureLogPartition (Ufeat L ε) t - featureLogPartition (Ufeat L 0) t)
        (C * |ε| * ⨆ z : Torus 1, |gT z|)) ∧
    (∀ L : ℝ, 0 < L → ∀ ε : ℝ, ContDiff ℝ ∞ (featureLogPartition (Ufeat L ε))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k R η hη
    obtain ⟨M₁, hM₁0, hM₁⟩ := ckBound_pint_aux (Ω := Torus 1) R k expPhi contDiff_expPhi
    obtain ⟨M₂, hM₂0, hM₂⟩ := ckBound_pint_aux (Ω := E2) R k expPhi contDiff_expPhi
    obtain ⟨K, hK0, hK⟩ := ckBound_log_sub (closedBall (0 : E2) R) k
      (Real.exp_pos (-R)) (le_max_of_le_left hM₁0 : 0 ≤ max M₁ M₂)
    have hη' : 0 < η / (K + 1) := by positivity
    have hev := ckBound_conv_aux (l := Filter.atTop) (μ := fun _ : ℝ => haar 1)
      (V := fun L : ℝ => Ufeat (max L 1) 0) (ν := limitLaw)
      (fun L => measurable_Ufeat (lt_of_lt_of_le one_pos (le_max_right _ _)) 0)
      (fun L => ae_norm_Ufeat _ _) ae_norm_limitLaw weak_conv_Ufeat R k expPhi
      contDiff_expPhi _ hη'
    obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max L₁ 1, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
    have hLL : L₁ ≤ L := le_trans (le_max_left _ _) hL
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hd := hL₁ L hLL
    rw [max_eq_left hL1] at hd
    obtain ⟨hc1, hp1, hl1⟩ := pint_exp_props (μ := haar 1) (measurable_Ufeat hLpos 0)
      (ae_norm_Ufeat L 0) R
    obtain ⟨hc2, hp2, hl2⟩ := pint_exp_props (μ := limitLaw) (V := id) measurable_id
      ae_norm_limitLaw R
    have h1 := hM₁ (haar 1) (Ufeat L 0) (measurable_Ufeat hLpos 0) (ae_norm_Ufeat L 0)
    have h2 := hM₂ limitLaw id measurable_id ae_norm_limitLaw
    have key := hK _ _ hc1 hc2 hp1 hp2 hl1 hl2 (ckBound_mono h1 (le_max_left _ _))
      (ckBound_mono h2 (le_max_right _ _)) _ hη'.le hd
    have e : (fun t => featureLogPartition (Ufeat L 0) t - logPartition t) =
        fun t => Real.log (pint (haar 1) (Ufeat L 0) expPhi t) -
          Real.log (pint limitLaw id expPhi t) := by
      funext t; rw [featureLogPartition_eq, logPartition_eq]
    rw [e]
    refine ckBound_mono key ?_
    calc K * (η / (K + 1)) = η * (K / (K + 1)) := by ring
      _ ≤ η := mul_le_of_le_one_right hη.le (div_le_one_of_le₀ (by linarith) (by linarith))
  · intro k R
    obtain ⟨M₁, hM₁0, hM₁⟩ := ckBound_pint_aux (Ω := Torus 1) R k expPhi contDiff_expPhi
    obtain ⟨C₁, hC₁0, hC₁⟩ := ckBound_pint_diff_aux (Ω := Torus 1) R k expPhi contDiff_expPhi
    obtain ⟨K, hK0, hK⟩ := ckBound_log_sub (closedBall (0 : E2) R) k
      (Real.exp_pos (-R)) hM₁0
    refine ⟨K * C₁ * (2 * π), by positivity, fun L hL ε => ?_⟩
    have hg0 : 0 ≤ ⨆ z : Torus 1, |gT z| := Real.iSup_nonneg fun _ => abs_nonneg _
    set δ : ℝ := 2 * π * |ε| * ⨆ z : Torus 1, |gT z| with hδ
    have hδ0 : 0 ≤ δ := by positivity
    obtain ⟨hc1, hp1, hl1⟩ := pint_exp_props (μ := haar 1) (measurable_Ufeat hL ε)
      (ae_norm_Ufeat L ε) R
    obtain ⟨hc2, hp2, hl2⟩ := pint_exp_props (μ := haar 1) (measurable_Ufeat hL 0)
      (ae_norm_Ufeat L 0) R
    have h1 := hM₁ (haar 1) (Ufeat L ε) (measurable_Ufeat hL ε) (ae_norm_Ufeat L ε)
    have h2 := hM₁ (haar 1) (Ufeat L 0) (measurable_Ufeat hL 0) (ae_norm_Ufeat L 0)
    have hd := hC₁ (haar 1) (Ufeat L ε) (Ufeat L 0) (measurable_Ufeat hL ε) (measurable_Ufeat hL 0)
      (ae_norm_Ufeat L ε) (ae_norm_Ufeat L 0) δ hδ0
      (Filter.Eventually.of_forall fun y =>
        (pushforward_convergence_to_three_states).2.2.1 L ε y)
    have key := hK _ _ hc1 hc2 hp1 hp2 hl1 hl2 h1 h2 _ (mul_nonneg hC₁0 hδ0) hd
    have e : (fun t => featureLogPartition (Ufeat L ε) t - featureLogPartition (Ufeat L 0) t) =
        fun t => Real.log (pint (haar 1) (Ufeat L ε) expPhi t) -
          Real.log (pint (haar 1) (Ufeat L 0) expPhi t) := by
      funext t; rw [featureLogPartition_eq, featureLogPartition_eq]
    rw [e]
    refine ckBound_mono key (le_of_eq ?_)
    rw [hδ]; ring
  · intro L hL ε
    obtain ⟨hc, hp, -⟩ := pint_exp_props (μ := haar 1) (measurable_Ufeat hL ε)
      (ae_norm_Ufeat L ε) 0
    exact hc.log fun t => (hp t).ne'

end assembly

end DGPS.Examples.RoughBoundary.Landscape
