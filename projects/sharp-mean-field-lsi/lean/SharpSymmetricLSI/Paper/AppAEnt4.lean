import SharpSymmetricLSI.Paper.AppAEnt3

/-!
# The entropy (4): integration by parts at level `ε`

For smooth periodic `φ, ψⱼ`, `G' ∈ C¹` and `f ∈ H¹` with weak gradient `g` (all in `L²`):
`∫ (G'(φ) + f) ∑ⱼ ∂ⱼ(∂ⱼφ + ψⱼ) = -∑ⱼ ∫ (G''(φ) ∂ⱼφ + gⱼ)(∂ⱼφ + ψⱼ)` (`integral_mul_div_eq`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Periodic integration by parts between a weakly and a classically differentiable function. -/
theorem integral_mul_dpart_eq {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (hfg : IsWeakGrad f g) (hf : Integrable f) (hg : ∀ k, Integrable (fun y => g y k))
    {h : UnitAddTorus ι → ℝ} (hh : IsSmoothT h) (k : ι) :
    ∫ y, f y * dpart_appA h k y = -∫ y, g y k * h y := by
  have := integral_mul_Dk_eq hfg hf hg (Θ := h ∘ liftT) hh (isPer_lift h) k
  have e1 : ∀ y, Dk (h ∘ liftT) k (secT y) = dpart_appA h k y := fun y => rfl
  have e2 : ∀ y, (h ∘ liftT) (secT y) = h y := fun y => by simp [liftT_secT]
  simp only [e1, e2] at this
  exact this

theorem dpart_add {a b : UnitAddTorus ι → ℝ} (ha : IsSmoothT a) (hb : IsSmoothT b) (j : ι)
    (y : UnitAddTorus ι) : dpart_appA (fun x => a x + b x) j y = dpart_appA a j y + dpart_appA b j y := by
  unfold dpart_appA
  have e : (fun x => a x + b x) ∘ liftT = fun z => (a ∘ liftT) z + (b ∘ liftT) z := rfl
  rw [e, fderiv_fun_add ((ha.differentiable (by simp)) _) ((hb.differentiable (by simp)) _)]
  rfl

/-- **Integration by parts** against the chemical potential `G'(φ) + f`. -/
theorem integral_mul_div_eq {Gp Gpp : ℝ → ℝ} (hGp : ∀ r, HasDerivAt Gp (Gpp r) r)
    (hGpp : Continuous Gpp) {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ)
    {ψ : ι → UnitAddTorus ι → ℝ} (hψ : ∀ j, IsSmoothT (ψ j))
    {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ} (hfg : IsWeakGrad f g)
    (hf2 : MemLp f 2 volume) (hg2 : ∀ j, MemLp (fun y => g y j) 2 volume) :
    ∫ x, (Gp (φ x) + f x) * ∑ j, (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) =
      -∑ j, ∫ x, (Gpp (φ x) * dpart_appA φ j x + g x j) * (dpart_appA φ j x + ψ j x) := by
  have hGpc : Continuous Gp := continuous_iff_continuousAt.2 fun r => (hGp r).continuousAt
  have hc : ∀ {v : UnitAddTorus ι → ℝ}, IsSmoothT v → Continuous v := fun hv => continuous_of_isSmoothT hv
  have hL2 : ∀ {v : UnitAddTorus ι → ℝ}, Continuous v → MemLp v 2 volume := fun hv => memLp_of_continuous hv 2
  have hsj := fun j => isSmoothT_dpart hφ j
  have hsjj := fun j => isSmoothT_dpart (hsj j) j
  have hψj := fun j => isSmoothT_dpart (hψ j) j
  have hX : ∀ j, IsSmoothT (fun x => dpart_appA φ j x + ψ j x) := fun j => (hsj j).add (hψ j)
  have hGφ : MemLp (fun x => Gp (φ x)) 2 volume := hL2 (hGpc.comp (hc hφ))
  have hGppφ : Continuous fun x => Gpp (φ x) := hGpp.comp (hc hφ)
  have hXj : ∀ j, MemLp (fun x => dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) 2 volume := fun j =>
    hL2 ((hc (hsjj j)).add (hc (hψj j)))
  have hYj : ∀ j, MemLp (fun x => dpart_appA φ j x + ψ j x) 2 volume := fun j => hL2 (hc (hX j))
  rw [← Finset.sum_neg_distrib]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum (f := fun j x => (Gp (φ x) + f x) * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x))
    _ fun j _ => (hGφ.add hf2).integrable_mul (hXj j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := ibp_energy hGp hGpp hφ (hψ j) j
  have h2 := integral_mul_dpart_eq hfg (hf2.integrable one_le_two)
    (fun k => (hg2 k).integrable one_le_two) (hX j) j
  simp_rw [dpart_add (hsj j) (hψ j) j] at h2
  have i1 : Integrable fun x => Gp (φ x) * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) :=
    hGφ.integrable_mul (hXj j)
  have i2 : Integrable fun x => f x * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) :=
    hf2.integrable_mul (hXj j)
  have i3 : Integrable fun x => Gpp (φ x) * (dpart_appA φ j x * (dpart_appA φ j x + ψ j x)) :=
    (hL2 (hGppφ.mul ((hc (hsj j)).mul (hc (hX j))))).integrable one_le_two
  have i4 : Integrable fun x => g x j * (dpart_appA φ j x + ψ j x) := (hg2 j).integrable_mul (hYj j)
  have eL : ∫ x, (Gp (φ x) + f x) * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) =
      (∫ x, Gp (φ x) * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x)) +
        ∫ x, f x * (dpart_appA (dpart_appA φ j) j x + dpart_appA (ψ j) j x) := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have eR : ∫ x, (Gpp (φ x) * dpart_appA φ j x + g x j) * (dpart_appA φ j x + ψ j x) =
      (∫ x, Gpp (φ x) * (dpart_appA φ j x * (dpart_appA φ j x + ψ j x))) +
        ∫ x, g x j * (dpart_appA φ j x + ψ j x) := by
    rw [← integral_add i3 i4]; congr 1; funext x; ring
  rw [eL, eR, h1, h2]; ring

end SharpLSI
