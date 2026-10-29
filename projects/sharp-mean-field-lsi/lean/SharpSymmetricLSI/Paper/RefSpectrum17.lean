import SharpSymmetricLSI.Paper.RefSpectrum16
import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D16_GaussianLimit

/-!
# R23 (6.1), part 17: assembly of `ref_spectrum`

The minimizer is `μ = ρ m` with `ρ = e^{-V-W*μ}/Z` (R13): `c ≤ ρ ≤ C`, `ρ` and `1/ρ` Lipschitz.
Then: existence of a reference eigenbasis (successive Rayleigh minimizers), and for every basis:
`λⱼ > 0` (`j ≥ 1`), the Weyl bound, `W^{2,p}` and the `C^{1,α}` representatives with polynomial
`C¹` bounds (`ref_spectrum_aux`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real NNReal

namespace SharpLSI

variable {d : ℕ}

theorem dist_liftT_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) : dist (liftT x) (liftT y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).mpr fun i => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h1 : liftT x i - liftT y i = ((x i - y i : ℝ) : UnitAddCircle) := by simp [liftT]
  rw [h1]
  refine (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))).trans ?_
  exact norm_le_pi_norm (x - y) i

/-- The reference density and its properties. -/
theorem refSetup {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} (hyp : Hyp V W KV KW)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    ∃ (ρ : Torus d → ℝ) (c C : ℝ) (Lσ : ℝ≥0), (μ : Measure (Torus d)) = densMeasure ρ ∧
      GoodDens ρ c C ∧ Continuous ρ ∧ LipschitzWith Lσ (recipD ρ ∘ liftT) := by
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  set ρ := elDens V W (μ : Measure (Torus d))
  obtain ⟨hbd, hL⟩ := hb (μ : Measure (Torus d)) inferInstance
  have hμρ := minimizer_eq_elDensity hyp hμ
  have hρc : Continuous ρ := hL.continuous
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => hc.le.trans (hbd x).1
  have hone : ∫ x, ρ x ∂haar d = 1 := by
    have h1 : (μ : Measure (Torus d)) Set.univ = 1 := measure_univ
    rw [hμρ, densMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (Eventually.of_forall hρ0)] at h1
    have := congrArg ENNReal.toReal h1
    rwa [ENNReal.toReal_ofReal (integral_nonneg hρ0), ENNReal.toReal_one] at this
  have hρ : GoodDens ρ c C := ⟨hρc.measurable, hc, fun x => (hbd x).1, fun x => (hbd x).2, hone⟩
  refine ⟨ρ, c, C, Real.toNNReal (L / c ^ 2), hμρ, hρ, hρc, ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hx := hc.trans_le (hbd (liftT x)).1
  have hy := hc.trans_le (hbd (liftT y)).1
  simp only [Function.comp, recipD, Real.dist_eq]
  rw [Real.coe_toNNReal _ (by positivity)]
  have e : 1 / ρ (liftT x) - 1 / ρ (liftT y) = (ρ (liftT y) - ρ (liftT x)) / (ρ (liftT x) * ρ (liftT y)) := by
    rw [div_sub_div _ _ hx.ne' hy.ne']; ring
  rw [e, abs_div, abs_of_pos (mul_pos hx hy)]
  have hd := hL.dist_le_mul (liftT y) (liftT x)
  rw [Real.dist_eq] at hd
  have hcc : c ^ 2 ≤ ρ (liftT x) * ρ (liftT y) := by
    have := mul_le_mul (hbd (liftT x)).1 (hbd (liftT y)).1 hc.le hx.le
    nlinarith
  rw [div_le_iff₀ (mul_pos hx hy)]
  calc |ρ (liftT y) - ρ (liftT x)| ≤ L * dist (liftT y) (liftT x) := hd
    _ ≤ L * dist x y := by rw [dist_comm]; exact mul_le_mul_of_nonneg_left (dist_liftT_le x y) L.2
    _ = L / c ^ 2 * dist x y * c ^ 2 := by field_simp
    _ ≤ L / c ^ 2 * dist x y * (ρ (liftT x) * ρ (liftT y)) :=
        mul_le_mul_of_nonneg_left hcc (by positivity)

theorem isEig_of_basis {P : Measure (Torus d)} {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (hb : IsRefEigenbasis P e lam) (j : ℕ) : IsEig P (e j) (lam j) := by
  refine ⟨hb.memH1 j, ?_, fun φ hφ => hb.eigen j φ hφ⟩
  have := hb.orthonormal j j
  rw [if_pos rfl] at this
  simp_rw [sq]; exact this

/-- **(6.1).** -/
theorem ref_spectrum_aux {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) :
    (∃ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam) ∧
    ∀ e lam, IsRefEigenbasis (μ : Measure (Torus d)) e lam →
      (∀ j, 1 ≤ j → 0 < lam j) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → c * (j : ℝ) ^ (2 / (d : ℝ)) ≤ lam j) ∧
      (∀ j (p : ℝ≥0∞), p ≠ ⊤ → ∀ k, HasWeakGrad (fun x => weakGrad (e j) x k) ∧
        ∀ l, MemLp (fun x => weakGrad (fun y => weakGrad (e j) y k) x l) p (haar d)) ∧
      ∃ (C : ℝ) (q : ℕ), ∀ j, ∃ eC : Torus d → ℝ,
        ContDiff ℝ 1 (eC ∘ liftT) ∧ eC =ᵐ[(μ : Measure (Torus d))] e j ∧
        (∀ x, |eC x| + Real.sqrt (sqNorm fun k => cpartial eC k x) ≤ C * (1 + lam j) ^ q) ∧
        ∀ α : NNReal, α < 1 → ∃ H : NNReal, ∀ k, HolderWith H α (fun x => cpartial eC k x) := by
  obtain ⟨ρ, c, C, Lσ, hμρ, hρ, hρc, hσ⟩ := refSetup hyp hμ
  rw [hμρ]
  refine ⟨⟨_, _, isRefEigenbasis_eSeq hρ hd⟩, fun e lam hb => ⟨fun j hj => refLam_pos hρ hb hd hj,
    weyl hρ hb hd, fun j p hp k => ?_, ?_⟩⟩
  · obtain ⟨h1, h2⟩ := w2p hρ hρc hσ hd (isEig_of_basis hb j) k
    exact ⟨h1, fun l => h2 l p hp⟩
  · obtain ⟨Cc, q, hc1⟩ := c1rep hρ hρc hσ hd
    exact ⟨Cc, q, fun j => hc1 (e j) (lam j) (isEig_of_basis hb j)⟩

end SharpLSI
