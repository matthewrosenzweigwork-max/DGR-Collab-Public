import FullLabeledLSI.Paper.HybridGroundAltA
import FullLabeledLSI.Infra.GaussianIBPPoly

/-!
# Hybrid inequality (7.17), alternative route, part B: Gaussian integration by parts (GS2)

For the quadratic exponent `u(g) = ½ gᵀ S g`: `∂_k u = (S g)_k`, `∂_k ∂_k u = S_kk`, and for the
polynomial-growth amplitude `a`
`∫ a (∂_k a) (S g)_k dγ = ½ (∫ g_k a² (S g)_k dγ - S_kk ∫ a² dγ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

section quad
variable {M : ℕ} (S : Matrix (Fin M) (Fin M) ℝ)

/-- the derivative of `g ↦ (S g)_k`. -/
def Lrow (k : Fin M) : (Fin M → ℝ) →L[ℝ] ℝ :=
  ∑ j, S k j • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) j)

theorem mulVec_apply_eq (k : Fin M) (g : Fin M → ℝ) : (S *ᵥ g) k = ∑ j, S k j * g j := rfl

theorem hasFDerivAt_mulVec (k : Fin M) (g : Fin M → ℝ) :
    HasFDerivAt (fun g' : Fin M → ℝ => (S *ᵥ g') k) (Lrow S k) g := by
  have : (fun g' : Fin M → ℝ => (S *ᵥ g') k) = fun g' => ∑ j, S k j * g' j := by
    funext g'; rfl
  rw [this]
  unfold Lrow
  refine HasFDerivAt.fun_sum fun j _ => ?_
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) j).hasFDerivAt).const_mul (S k j)

theorem Lrow_single (k l : Fin M) : Lrow S k (Pi.single l 1) = S k l := by
  unfold Lrow
  simp [Pi.single_apply]

theorem contDiff_mulVec (k : Fin M) : ContDiff ℝ ∞ (fun g' : Fin M → ℝ => (S *ᵥ g') k) := by
  have : (fun g' : Fin M → ℝ => (S *ᵥ g') k) = fun g' => ∑ j, S k j * g' j := by
    funext g'; rfl
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℝ j)

theorem fderiv_mulVec_single (k l : Fin M) (g : Fin M → ℝ) :
    fderiv ℝ (fun g' : Fin M → ℝ => (S *ᵥ g') k) g (Pi.single l 1) = S k l := by
  rw [(hasFDerivAt_mulVec S k g).fderiv, Lrow_single]

theorem hasFDerivAt_quad (g : Fin M → ℝ) :
    HasFDerivAt (fun g' : Fin M → ℝ => (g' ⬝ᵥ (S *ᵥ g')) / 2)
      ((1 / 2 : ℝ) • ∑ k, (g k • Lrow S k + (S *ᵥ g) k • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) k))) g := by
  have h0 : (fun g' : Fin M → ℝ => (g' ⬝ᵥ (S *ᵥ g')) / 2) = fun g' => (1 / 2 : ℝ) * ∑ k, g' k * (S *ᵥ g') k := by
    funext g'; simp only [dotProduct]; ring
  rw [h0]
  refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun k _ => ?_) (1 / 2 : ℝ)
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) k).hasFDerivAt).mul (hasFDerivAt_mulVec S k g)

theorem fderiv_quad_single (hS : Sᵀ = S) (l : Fin M) (g : Fin M → ℝ) :
    fderiv ℝ (fun g' : Fin M → ℝ => (g' ⬝ᵥ (S *ᵥ g')) / 2) g (Pi.single l 1) = (S *ᵥ g) l := by
  rw [(hasFDerivAt_quad S g).fderiv]
  simp only [_root_.smul_apply, _root_.sum_apply, _root_.add_apply,
    Lrow_single, smul_eq_mul, ContinuousLinearMap.proj_apply, Pi.single_apply]
  have h1 : ∑ k, (g k * S k l + (S *ᵥ g) k * (if k = l then (1:ℝ) else 0)) =
      ∑ k, g k * S k l + (S *ᵥ g) l := by
    simp [Finset.sum_add_distrib]
  rw [h1]
  have h2 : ∑ k, g k * S k l = (S *ᵥ g) l := by
    have := congrFun (congrArg (fun T => T *ᵥ g) hS) l
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
    simp only [Matrix.mulVec, dotProduct]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2]; ring
end quad

section ibp
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ}
  (S : Matrix (Fin M) (Fin M) ℝ)

theorem PBu.polyGrowth {α : Type*} {f : α → (Fin M → ℝ) → ℝ} (hf : PBu f) (x : α) :
    PolyGrowth (f x) := by
  obtain ⟨k, C, hC, h⟩ := hf
  exact ⟨C, hC, k, h x⟩

theorem tg_mulVec (k : Fin M) : (fun g : Fin M → ℝ => (S *ᵥ g) k).HasTemperateGrowth := by
  have : (fun g : Fin M → ℝ => (S *ᵥ g) k) = fun g => ∑ j, S k j * g j := by
    funext g; rfl
  rw [this]
  exact tg_sum _ fun j _ => tg_mul (tg_const _) (tg_proj j)

theorem tg_g (k : Fin M) : (fun g : Fin M → ℝ => g k).HasTemperateGrowth := tg_proj k

theorem contDiff_aF (hY : ∀ i, (Y i).HasTemperateGrowth) (x : Config N d) :
    ContDiff ℝ ∞ (fun g : Fin M → ℝ => aF c Y Xj x g) := by
  unfold aF
  exact ContDiff.sum fun i _ => (contDiff_const.mul (hY i).1).mul contDiff_const

theorem continuous_daF (hY : ∀ i, (Y i).HasTemperateGrowth) (x : Config N d) (k : Fin M) :
    Continuous fun g : Fin M → ℝ => daF c Y Xj x g k := by
  unfold daF
  refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
  exact ((hY i).1.continuous_fderiv (by simp)).clm_apply continuous_const

/-- **Gaussian integration by parts** for the cross term, on each `x`-slice. -/
theorem ibp_slice (hY : ∀ i, (Y i).HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))
    (x : Config N d) (k : Fin M) :
    ∫ g, g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k) ∂gpi M =
      2 * ∫ g, aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k ∂gpi M +
        S k k * ∫ g, aF c Y Xj x g ^ 2 ∂gpi M := by
  set φ : (Fin M → ℝ) → ℝ := fun g => aF c Y Xj x g ^ 2 * (S *ᵥ g) k with hφ
  have hcd : ContDiff ℝ ∞ φ := ((contDiff_aF hY x).pow 2).mul (contDiff_mulVec S k)
  have hder : ∀ g, fderiv ℝ φ g (Pi.single k 1) =
      2 * (aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k) + aF c Y Xj x g ^ 2 * S k k := by
    intro g
    have hA : HasFDerivAt (fun g' => aF c Y Xj x g') (fderiv ℝ (fun g' => aF c Y Xj x g') g) g :=
      (((contDiff_aF hY x).differentiable (by simp)) g).hasFDerivAt
    have hL := hasFDerivAt_mulVec S k g
    have h := ((hA.fun_mul hA).fun_mul hL)
    have hφ' : φ = fun g' => (aF c Y Xj x g' * aF c Y Xj x g') * (S *ᵥ g') k := by
      funext g'; simp only [hφ]; ring
    rw [hφ', h.fderiv]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    rw [fderiv_aF hY x g k, Lrow_single]
    ring
  -- polynomial growth
  have hPφ : PolyGrowth φ :=
    PBu.polyGrowth (f := fun (x : Config N d) g => aF c Y Xj x g ^ 2 * (S *ᵥ g) k)
      (((pbu_aF hY hX).sq).mul (PBu.of_tg (tg_mulVec S k))) x
  have hPφ' : PolyGrowth fun g => fderiv ℝ φ g (Pi.single k 1) := by
    have : (fun g => fderiv ℝ φ g (Pi.single k 1)) =
        fun g => 2 * (aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k) + aF c Y Xj x g ^ 2 * S k k :=
      funext hder
    rw [this]
    have hp : PBu (fun (x : Config N d) (g : Fin M → ℝ) =>
        2 * (aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k) + aF c Y Xj x g ^ 2 * S k k) :=
      (((((pbu_aF hY hX).mul (pbu_daF hY hX k)).mul (PBu.of_tg (tg_mulVec S k))).const_mul 2).add
        (((pbu_aF hY hX).sq).mul (PBu.const (S k k))))
    exact PBu.polyGrowth hp x
  have key := gauss_ibp_poly (hcd.differentiable (by simp)) (hcd.continuous_fderiv (by simp)) hPφ k hPφ'
  simp only [hder] at key
  have cA : Continuous fun g : Fin M → ℝ => aF c Y Xj x g := (contDiff_aF hY x).continuous
  have cD : Continuous fun g : Fin M → ℝ => daF c Y Xj x g k := continuous_daF hY x k
  have cL : Continuous fun g : Fin M → ℝ => (S *ᵥ g) k := (contDiff_mulVec S k).continuous
  have i1 : Integrable (fun g => aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k) (gpi M) :=
    integrable_slice_PBu (f := fun (x : Config N d) g => aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k)
      (fun x => ((contDiff_aF hY x).continuous.mul (continuous_daF hY x k)
        |>.mul cL).aestronglyMeasurable)
      (((pbu_aF hY hX).mul (pbu_daF hY hX k)).mul (PBu.of_tg (tg_mulVec S k))) x
  have i2 : Integrable (fun g => aF c Y Xj x g ^ 2 * S k k) (gpi M) :=
    integrable_slice_PBu (f := fun (x : Config N d) g => aF c Y Xj x g ^ 2 * S k k)
      (fun x => (((contDiff_aF hY x).continuous.pow 2).mul continuous_const).aestronglyMeasurable)
      (((pbu_aF hY hX).sq).mul (PBu.const (S k k))) x
  rw [integral_add (i1.const_mul 2) i2, integral_const_mul, integral_mul_const] at key
  rw [mul_comm (S k k)]
  exact key

end ibp

section energy
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ}
  (S : Matrix (Fin M) (Fin M) ℝ) (lam' : Fin M → ℝ)

/-- `v` in flat form: `∑_k λ_k (½ g_k (Sg)_k - ½ S_kk + ¼ (Sg)_k²)`. -/
def vflat (g : Fin M → ℝ) : ℝ :=
  ∑ k, lam' k * ((1 / 2) * (g k * (S *ᵥ g) k) - (1 / 2) * S k k +
    (1 / 4) * ((S *ᵥ g) k * (S *ᵥ g) k))

theorem pbu_vflat {α : Type*} : PBu (fun (_ : α) (g : Fin M → ℝ) => vflat S lam' g) := by
  unfold vflat
  refine PBu.sum _ fun k _ => ?_
  have h1 : PBu (fun (_ : α) (g : Fin M → ℝ) => g k * (S *ᵥ g) k) :=
    (PBu.of_tg (tg_g k)).mul (PBu.of_tg (tg_mulVec S k))
  have h2 : PBu (fun (_ : α) (g : Fin M → ℝ) => (S *ᵥ g) k * (S *ᵥ g) k) :=
    (PBu.of_tg (tg_mulVec S k)).mul (PBu.of_tg (tg_mulVec S k))
  exact ((((h1.const_mul (1 / 2)).sub (PBu.const ((1 / 2) * S k k))).add
    (h2.const_mul (1 / 4))).const_mul (lam' k))

theorem continuous_vflat : Continuous (vflat S lam') := by
  unfold vflat
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  have hk : Continuous fun g : Fin M → ℝ => (S *ᵥ g) k := (contDiff_mulVec S k).continuous
  have hg : Continuous fun g : Fin M → ℝ => g k := continuous_apply k
  exact (((continuous_const.mul (hg.mul hk)).sub continuous_const).add (continuous_const.mul (hk.mul hk)))

theorem intgSlice {f : Config N d → (Fin M → ℝ) → ℝ} (hf : PBu f)
    (hc : ∀ x, Continuous (f x)) (x : Config N d) : Integrable (f x) (gpi M) :=
  integrable_slice_PBu (fun x => (hc x).aestronglyMeasurable) hf x

theorem duF_quad (hS : Sᵀ = S) (hu_eq : ∀ g, u g = (g ⬝ᵥ (S *ᵥ g)) / 2) (g : Fin M → ℝ)
    (k : Fin M) : duF u g k = (S *ᵥ g) k := by
  unfold duF
  have : u = fun g => (g ⬝ᵥ (S *ᵥ g)) / 2 := funext hu_eq
  rw [this]
  exact fderiv_quad_single S hS k g

end energy

section energy2
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ}
  (S : Matrix (Fin M) (Fin M) ℝ) (lam' : Fin M → ℝ)
  (hY : ∀ i, (Y i).HasTemperateGrowth) (hX : ∀ i, C1C (Xj i))

include hY hX in
/-- Integrability of the three basic slice integrands. -/
theorem intg_basic (x : Config N d) (k : Fin M) :
    Integrable (fun g => aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k) (gpi M) ∧
    Integrable (fun g => g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k)) (gpi M) ∧
    Integrable (fun g => aF c Y Xj x g ^ 2) (gpi M) ∧
    Integrable (fun g => aF c Y Xj x g ^ 2 * (S *ᵥ g) k ^ 2) (gpi M) ∧
    Integrable (fun g => daF c Y Xj x g k ^ 2) (gpi M) := by
  have cL : ∀ k, Continuous fun g : Fin M → ℝ => (S *ᵥ g) k := fun k => (contDiff_mulVec S k).continuous
  have cA : ∀ x, Continuous fun g : Fin M → ℝ => aF c Y Xj x g := fun x => (contDiff_aF hY x).continuous
  have cD : ∀ x k, Continuous fun g : Fin M → ℝ => daF c Y Xj x g k := fun x k => continuous_daF hY x k
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact intgSlice (f := fun (x : Config N d) g => aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k)
      (((pbu_aF hY hX).mul (pbu_daF hY hX k)).mul (PBu.of_tg (tg_mulVec S k)))
      (fun x => ((cA x).mul (cD x k)).mul (cL k)) x
  · exact intgSlice (f := fun (x : Config N d) g => g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k))
      ((PBu.of_tg (tg_g k)).mul (((pbu_aF hY hX).sq).mul (PBu.of_tg (tg_mulVec S k))))
      (fun x => (continuous_apply k).mul (((cA x).pow 2).mul (cL k))) x
  · exact intgSlice (f := fun (x : Config N d) g => aF c Y Xj x g ^ 2) (pbu_aF hY hX).sq
      (fun x => (cA x).pow 2) x
  · exact intgSlice (f := fun (x : Config N d) g => aF c Y Xj x g ^ 2 * (S *ᵥ g) k ^ 2)
      (((pbu_aF hY hX).sq).mul ((PBu.of_tg (tg_mulVec S k)).sq))
      (fun x => ((cA x).pow 2).mul ((cL k).pow 2)) x
  · exact intgSlice (f := fun (x : Config N d) g => daF c Y Xj x g k ^ 2) (pbu_daF hY hX k).sq
      (fun x => (cD x k).pow 2) x

include hY hX in
theorem ibp_energy_slice (hS : Sᵀ = S)
    (hu_eq : ∀ g, u g = (g ⬝ᵥ (S *ᵥ g)) / 2) (x : Config N d) :
    ∫ g, Ey0 c Y Xj u lam' x g ∂gpi M =
      ∫ g, ∑ k, lam' k * daF c Y Xj x g k ^ 2 ∂gpi M +
        ∫ g, aF c Y Xj x g ^ 2 * vflat S lam' g ∂gpi M := by
  have hb := fun k => intg_basic (c := c) (Xj := Xj) S hY hX x k
  -- the pointwise decomposition
  set Dk : Fin M → (Fin M → ℝ) → ℝ := fun k g => lam' k * (aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k
      - (1 / 2) * (g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k)) + (1 / 2) * (aF c Y Xj x g ^ 2 * S k k))
    with hDk
  have hpt : ∀ g, Ey0 c Y Xj u lam' x g = ∑ k, lam' k * daF c Y Xj x g k ^ 2 +
      aF c Y Xj x g ^ 2 * vflat S lam' g + ∑ k, Dk k g := by
    intro g
    unfold Ey0 vflat
    simp only [hDk, duF_quad S hS hu_eq]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have iD : ∀ k, Integrable (Dk k) (gpi M) := by
    intro k
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb k
    exact ((b1.sub (b2.const_mul (1 / 2))).add (b3.mul_const (S k k) |>.const_mul (1 / 2))).const_mul (lam' k)
  have i1 : Integrable (fun g => ∑ k, lam' k * daF c Y Xj x g k ^ 2) (gpi M) :=
    integrable_finsetSum _ fun k _ => (hb k).2.2.2.2.const_mul (lam' k)
  have i2 : Integrable (fun g => aF c Y Xj x g ^ 2 * vflat S lam' g) (gpi M) := by
    have : (fun g => aF c Y Xj x g ^ 2 * vflat S lam' g) = fun g => ∑ k, lam' k *
        ((1 / 2) * (g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k)) - (1 / 2) * (aF c Y Xj x g ^ 2 * S k k) +
          (1 / 4) * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k ^ 2)) := by
      funext g
      unfold vflat
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    refine integrable_finsetSum _ fun k _ => ?_
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb k
    exact ((((b2.const_mul (1 / 2)).sub ((b3.mul_const (S k k)).const_mul (1 / 2))).add
      (b4.const_mul (1 / 4)))).const_mul (lam' k)
  have i3 : Integrable (fun g => ∑ k, Dk k g) (gpi M) := integrable_finsetSum _ fun k _ => iD k
  have h0 : ∫ g, ∑ k, Dk k g ∂gpi M = 0 := by
    rw [integral_finsetSum _ fun k _ => iD k]
    refine Finset.sum_eq_zero fun k _ => ?_
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb k
    have hI := ibp_slice (c := c) (Y := Y) (Xj := Xj) S hY hX x k
    simp only [hDk]
    have t1 : Integrable (fun g => aF c Y Xj x g * daF c Y Xj x g k * (S *ᵥ g) k -
        1 / 2 * (g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k))) (gpi M) := b1.sub (b2.const_mul (1 / 2))
    have t2 : Integrable (fun g => 1 / 2 * (aF c Y Xj x g ^ 2 * S k k)) (gpi M) :=
      (b3.mul_const (S k k)).const_mul (1 / 2)
    have t3 : Integrable (fun g => 1 / 2 * (g k * (aF c Y Xj x g ^ 2 * (S *ᵥ g) k))) (gpi M) :=
      b2.const_mul (1 / 2)
    rw [integral_const_mul, integral_add t1 t2, integral_sub b1 t3, integral_const_mul,
      integral_const_mul, integral_mul_const]
    rw [hI]; ring
  have i12 : Integrable (fun g => ∑ k, lam' k * daF c Y Xj x g k ^ 2 +
      aF c Y Xj x g ^ 2 * vflat S lam' g) (gpi M) := i1.add i2
  simp_rw [hpt]
  rw [integral_add i12 i3, integral_add i1 i2, h0]
  ring

end energy2

section energy3
variable {N d M : ℕ} {ι : Type*} [Fintype ι]
  {c : ι → ℝ} {Y : ι → (Fin M → ℝ) → ℝ} {Xj : ι → Config N d → ℝ} {u : (Fin M → ℝ) → ℝ}
  (S : Matrix (Fin M) (Fin M) ℝ) (lam' : Fin M → ℝ)
  (hY : ∀ i, (Y i).HasTemperateGrowth) (hX : ∀ i, C1C (Xj i)) (hu : u.HasTemperateGrowth)
  (P : Measure (Config N d)) [IsProbabilityMeasure P]

include hY hX in
theorem integrable_sumDaF :
    Integrable (fun z : Config N d × (Fin M → ℝ) => ∑ k, lam' k * daF c Y Xj z.1 z.2 k ^ 2)
      (P.prod (gpi M)) := by
  refine integrable_prod_PBu (P := P) (f := fun x g => ∑ k, lam' k * daF c Y Xj x g k ^ 2) ?_ ?_
  · exact (Finset.measurable_sum _ fun k _ => measurable_const.mul
      ((meas_daF hY hX k).pow_const 2)).aestronglyMeasurable
  · exact PBu.sum _ fun k _ => ((pbu_daF hY hX k).sq).const_mul (lam' k)

include hY hX in
theorem integrable_aF_vflat :
    Integrable (fun z : Config N d × (Fin M → ℝ) => aF c Y Xj z.1 z.2 ^ 2 * vflat S lam' z.2)
      (P.prod (gpi M)) := by
  refine integrable_prod_PBu (P := P) (f := fun x g => aF c Y Xj x g ^ 2 * vflat S lam' g) ?_ ?_
  · exact (((meas_aF hY hX).pow_const 2).mul
      ((continuous_vflat S lam').measurable.comp measurable_snd)).aestronglyMeasurable
  · exact ((pbu_aF hY hX).sq).mul (pbu_vflat S lam')

include hY hX hu in
/-- **(GS2) Gaussian integration by parts** on the flat space. -/
theorem ibp_energy (hS : Sᵀ = S) (hu_eq : ∀ g, u g = (g ⬝ᵥ (S *ᵥ g)) / 2) :
    ∫ z, Ey0 c Y Xj u lam' z.1 z.2 ∂(P.prod (gpi M)) =
      ∫ z, ∑ k, lam' k * daF c Y Xj z.1 z.2 k ^ 2 ∂(P.prod (gpi M)) +
        ∫ z, aF c Y Xj z.1 z.2 ^ 2 * vflat S lam' z.2 ∂(P.prod (gpi M)) := by
  have hE : Integrable (fun z : Config N d × (Fin M → ℝ) => Ey0 c Y Xj u lam' z.1 z.2)
      (P.prod (gpi M)) :=
    integrable_prod_PBu (P := P) (f := fun x g => Ey0 c Y Xj u lam' x g)
      (meas_Ey0 hY hu hX lam').aestronglyMeasurable (pbu_Ey0 hY hu hX lam')
  have h1 := integrable_sumDaF (c := c) (Y := Y) (Xj := Xj) lam' hY hX P
  have h2 := integrable_aF_vflat (c := c) (Y := Y) (Xj := Xj) S lam' hY hX P
  rw [integral_prod _ hE, integral_prod _ h1, integral_prod _ h2, ← integral_add h1.integral_prod_left h2.integral_prod_left]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact ibp_energy_slice S lam' hY hX hS hu_eq x

end energy3

end SharpLSI.FL.HLA

end
