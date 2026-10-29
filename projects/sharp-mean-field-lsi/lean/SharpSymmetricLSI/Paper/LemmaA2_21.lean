import SharpSymmetricLSI.Paper.LemmaA2_20
import SharpSymmetricLSI.Paper.CenteredEntropy

/-!
# R25 Lemma A.2, part 21: the semigroup in both variables

For a continuous bounded kernel `Kf` whose slices are `L`-Lipschitz (Euclidean distance on lifts),
`M_t(x,·) = P_t Kf(x,·)` and `K_t(·,y) = P_t M_t(·,y)` are bounded by `sup|Kf|` and Lipschitz with
constant `e^{Kt}L` in each variable: in the variable the semigroup acts on by (A.9), in the other
one by linearity and the `L^∞` contraction (`Kt_lip_left`, `Kt_lip_right`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem dist_le_dE (a b : Fin d → ℝ) : dist a b ≤ dE a b :=
  (dist_pi_le_iff (dE_nonneg a b)).mpr fun i => by rw [Real.dist_eq]; exact abs_sub_le_dE a b i

theorem lift_bound_of_lipschitz {f : Torus d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L (f ∘ liftT))
    (a b : Fin d → ℝ) : f (liftT a) - f (liftT b) ≤ L * dE a b := by
  have := hf.dist_le_mul a b
  rw [Real.dist_eq] at this
  exact (le_abs_self _).trans (this.trans (mul_le_mul_of_nonneg_left (dist_le_dE a b) L.2))

theorem continuous_of_lift_bound (hd : 1 ≤ d) {f : Torus d → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hf : ∀ a b, f (liftT a) - f (liftT b) ≤ L * dE a b) : Continuous f := by
  refine continuous_of_liftT' (LipschitzWith.continuous (K := Real.toNNReal (L * d)) ?_)
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (mul_nonneg hL0 (Nat.cast_nonneg _)), abs_le]
  have h1 := hf a b
  have h2 := hf b a
  have hs : dE b a = dE a b := by
    simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs] at h2
  have h3 := mul_le_mul_of_nonneg_left (dE_le_card_mul_dist hd a b) hL0
  simp only [Function.comp]
  constructor <;> nlinarith

theorem dE_symm' (a b : Fin d → ℝ) : dE b a = dE a b := by
  simp only [dE]; congr 1; exact Finset.sum_congr rfl fun i _ => by ring

section kt

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {K : ℝ}
  (hQ : ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : Fin d → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
        ∫ x, -Real.log (ρ (liftT x)) * secondDirDeriv φ ξ x)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
  {eC : ℕ → Torus d → ℝ} (heC1 : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
  (heCae : ∀ j, eC j =ᵐ[densMeasure ρ] e j)
  {M M' : ℕ → ℝ} (hM : ∀ j x, |eC j x| ≤ M j) (hM' : ∀ j x, ‖fderiv ℝ (eC j ∘ liftT) x‖ ≤ M' j)
  (hS : ∀ t, 0 < t → Summable (fun j => Real.exp (-t * lam j) * M j) ∧
    Summable (fun j => Real.exp (-t * lam j) * M' j))

/-- `M_t(x,y) = (P_t Kf(x,·))(y)`. -/
noncomputable def Mt (P : Measure (Torus d)) (e eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (t : ℝ)
    (Kf : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  semi P e eC lam t (fun y' => Kf x y') y

/-- `K_t(x,y) = (P_t M_t(·,y))(x)`. -/
noncomputable def Kt (P : Measure (Torus d)) (e eC : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (t : ℝ)
    (Kf : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  semi P e eC lam t (fun x' => Mt P e eC lam t Kf x' y) x

include hρ hb heC1 heCae hM hM' hS

theorem semi_sub {t : ℝ} (ht : 0 < t) {h₁ h₂ : Torus d → ℝ} (h₁m : AEStronglyMeasurable h₁ (densMeasure ρ))
    (h₂m : AEStronglyMeasurable h₂ (densMeasure ρ)) {B₁ B₂ : ℝ} (hB₁ : ∀ y, |h₁ y| ≤ B₁)
    (hB₂ : ∀ y, |h₂ y| ≤ B₂) (y : Torus d) :
    semi (densMeasure ρ) e eC lam t h₁ y - semi (densMeasure ρ) e eC lam t h₂ y =
      semi (densMeasure ρ) e eC lam t (fun z => h₁ z - h₂ z) y := by
  haveI := hρ.isProb
  have s1 := (summable_semi_coeff hρ hb heC1 heCae hM hM' hS ht h₁m hB₁).1
  have s2 := (summable_semi_coeff hρ hb heC1 heCae hM hM' hS ht h₂m hB₂).1
  simp only [semi, series]
  rw [← (summable_series_at hM s1 y).tsum_sub (summable_series_at hM s2 y)]
  refine tsum_congr fun j => ?_
  have hej : Integrable (e j) (densMeasure ρ) := ((hb.memH1 j).2.1).integrable one_le_two
  have i1 : Integrable (fun z => h₁ z * e j z) (densMeasure ρ) :=
    hej.bdd_mul (c := B₁) h₁m (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB₁ z)
  have i2 : Integrable (fun z => h₂ z * e j z) (densMeasure ρ) :=
    hej.bdd_mul (c := B₂) h₂m (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hB₂ z)
  simp_rw [sub_mul]
  rw [integral_sub i1 i2]
  ring

section facts

variable (hd : 1 ≤ d) (hK0 : 0 ≤ K) {t : ℝ} (ht : 0 < t) {Kf : Torus d → Torus d → ℝ}
    (hKc : Continuous (Function.uncurry Kf)) {BK : ℝ} (hBK : ∀ x y, |Kf x y| ≤ BK) {LK : ℝ}
    (hLK0 : 0 ≤ LK) (hL1 : ∀ y a b, Kf (liftT a) y - Kf (liftT b) y ≤ LK * dE a b)
    (hL2 : ∀ x a b, Kf x (liftT a) - Kf x (liftT b) ≤ LK * dE a b)
include hρc hQ hd hK0 ht hKc hBK hLK0 hL1 hL2

/-- **Facts about `M_t`.** -/
theorem Mt_facts :
    (∀ y a b, Mt (densMeasure ρ) e eC lam t Kf (liftT a) y -
      Mt (densMeasure ρ) e eC lam t Kf (liftT b) y ≤ LK * dE a b) ∧
    (∀ x y, |Mt (densMeasure ρ) e eC lam t Kf x y| ≤ BK) ∧
    (∀ x a b, Mt (densMeasure ρ) e eC lam t Kf x (liftT a) -
      Mt (densMeasure ρ) e eC lam t Kf x (liftT b) ≤ Real.exp (K * t) * LK * dE a b) ∧
    (∀ x j, ∫ y, Mt (densMeasure ρ) e eC lam t Kf x y * e j y ∂densMeasure ρ =
      Real.exp (-t * lam j) * ∫ y, Kf x y * e j y ∂densMeasure ρ) ∧
    (∀ y, Continuous fun x => Mt (densMeasure ρ) e eC lam t Kf x y) := by
  set P := densMeasure ρ
  have hslx : ∀ x, Continuous fun y => Kf x y := fun x =>
    hKc.comp (continuous_const.prodMk continuous_id)
  have hMy := fun x => semi_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht (hslx x) hLK0
    (hL2 x) (hBK x)
  have hMx : ∀ y a b, Mt P e eC lam t Kf (liftT a) y - Mt P e eC lam t Kf (liftT b) y ≤
      LK * dE a b := by
    intro y a b
    have hdiff := semi_sub hρ hb heC1 heCae hM hM' hS ht (hslx (liftT a)).aestronglyMeasurable
      (hslx (liftT b)).aestronglyMeasurable (hBK (liftT a)) (hBK (liftT b)) y
    simp only [Mt]
    rw [hdiff]
    have hbd : ∀ z, |Kf (liftT a) z - Kf (liftT b) z| ≤ LK * dE a b := fun z => by
      rw [abs_le]; have h1 := hL1 z a b; have h2 := hL1 z b a; rw [dE_symm'] at h2
      constructor <;> linarith
    have hl : ∀ u v, (Kf (liftT a) (liftT u) - Kf (liftT b) (liftT u)) -
        (Kf (liftT a) (liftT v) - Kf (liftT b) (liftT v)) ≤ (2 * LK) * dE u v := fun u v => by
      have h1 := hL2 (liftT a) u v; have h2 := hL2 (liftT b) v u; rw [dE_symm'] at h2; linarith
    have := (semi_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht
      ((hslx _).sub (hslx _)) (by positivity) hl hbd).2.2.1 y
    exact (le_abs_self _).trans this
  exact ⟨hMx, fun x y => (hMy x).2.2.1 y, fun x => (hMy x).2.1, fun x => (hMy x).2.2.2,
    fun y => continuous_of_lift_bound hd hLK0 (hMx y)⟩

/-- **Bounds for `K_t`.** -/
theorem Kt_props :
    (∀ x y, |Kt (densMeasure ρ) e eC lam t Kf x y| ≤ BK) ∧
    (∀ y a b, Kt (densMeasure ρ) e eC lam t Kf (liftT a) y -
      Kt (densMeasure ρ) e eC lam t Kf (liftT b) y ≤ Real.exp (K * t) * LK * dE a b) ∧
    (∀ x a b, Kt (densMeasure ρ) e eC lam t Kf x (liftT a) -
      Kt (densMeasure ρ) e eC lam t Kf x (liftT b) ≤ Real.exp (K * t) * LK * dE a b) ∧
    (∀ y, ContDiff ℝ 1 ((fun x => Kt (densMeasure ρ) e eC lam t Kf x y) ∘ liftT)) ∧
    (∀ y i, ∫ x, Kt (densMeasure ρ) e eC lam t Kf x y * e i x ∂densMeasure ρ =
      Real.exp (-t * lam i) * ∫ x, Mt (densMeasure ρ) e eC lam t Kf x y * e i x ∂densMeasure ρ) := by
  set P := densMeasure ρ
  obtain ⟨hMx, hMB, hMy, -, hMc⟩ := Mt_facts hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht hKc hBK
    hLK0 hL1 hL2
  have hE0 : 0 ≤ Real.exp (K * t) * LK := mul_nonneg (Real.exp_pos _).le hLK0
  have hKx := fun y => semi_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht (hMc y) hLK0
    (hMx y) (hMB · y)
  refine ⟨fun x y => (hKx y).2.2.1 x, fun y a b => (hKx y).2.1 a b, fun x a b => ?_,
    fun y => (hKx y).1, fun y i => (hKx y).2.2.2 i⟩
  have hdiff := semi_sub hρ hb heC1 heCae hM hM' hS ht (hMc (liftT a)).aestronglyMeasurable
    (hMc (liftT b)).aestronglyMeasurable (hMB · (liftT a)) (hMB · (liftT b)) x
  simp only [Kt]
  rw [hdiff]
  have hbd : ∀ z, |Mt P e eC lam t Kf z (liftT a) - Mt P e eC lam t Kf z (liftT b)| ≤
      Real.exp (K * t) * LK * dE a b := fun z => by
    rw [abs_le]
    have h1 := hMy z a b; have h2 := hMy z b a; rw [dE_symm'] at h2
    constructor <;> linarith
  have hl : ∀ u v, (Mt P e eC lam t Kf (liftT u) (liftT a) - Mt P e eC lam t Kf (liftT u) (liftT b)) -
      (Mt P e eC lam t Kf (liftT v) (liftT a) - Mt P e eC lam t Kf (liftT v) (liftT b)) ≤
        (2 * LK) * dE u v := fun u v => by
    have h1 := hMx (liftT a) u v; have h2 := hMx (liftT b) v u; rw [dE_symm'] at h2; linarith
  have := (semi_props hρ hρc hQ hb heC1 heCae hM hM' hS hd hK0 ht
    ((hMc _).sub (hMc _)) (by positivity) hl hbd).2.2.1 x
  exact (le_abs_self _).trans this

end facts

end kt

end SharpLSI
