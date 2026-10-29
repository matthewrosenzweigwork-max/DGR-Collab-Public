/- UNCHECKED. Actual bounded diagonal operator on an infinite Hilbert basis.
Uses pinned Mathlib lp.mapCLM with uniformly bounded scalar multipliers;
no finite-dimensional diagonalization or assumed inverse is used. -/
import DGRHS.Gaussian.SpectralPowerMargin
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.InnerProductSpace.l2Space
noncomputable section
open scoped InnerProductSpace
namespace DGRHS.Kernel
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def spectralMultiplier (b : HilbertBasis ι ℝ H) (c : ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i, |c i| ≤ K) : H →L[ℝ] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lp.mapCLM 2 (fun i => c i • ContinuousLinearMap.id ℝ ℝ) hK
      (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs] using hc i)).comp
      b.repr.toLinearIsometry.toContinuousLinearMap)

lemma repr_spectralMultiplier (b : HilbertBasis ι ℝ H) (c : ι → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i, |c i| ≤ K) (v : H) (i : ι) :
    b.repr (spectralMultiplier b c K hK hc v) i = c i * b.repr v i := by
  change b.repr (b.repr.symm
    ((lp.mapCLM 2 (fun i => c i • ContinuousLinearMap.id ℝ ℝ) hK
      (fun i => by simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs] using hc i)) (b.repr v))) i = _
  rw [b.repr.apply_symm_apply]
  rfl

lemma repr_symmetric_eigenoperator (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (hb : ∀ i, T (b i) = a i • b i) (v : H) (i : ι) :
    b.repr (T v) i = a i * b.repr v i := by
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have he := hT (b i) v
  change inner ℝ (T (b i)) v = inner ℝ (b i) (T v) at he
  rw [hb, real_inner_smul_left] at he
  exact he.symm

lemma spectralMultiplier_inverse (T : H →L[ℝ] H) (hT : T.toLinearMap.IsSymmetric)
    (b : HilbertBasis ι ℝ H) (a : ι → ℝ)
    (hb : ∀ i, T (b i) = a i • b i) (β δ : ℝ) (hδ : 0 < δ)
    (hm : ∀ i, δ ≤ 1+β*a i) :
    ∃ R : H →L[ℝ] H,
      (∀ v, (R v)+β • T (R v) = v) ∧
      (∀ v, R (v+β • T v) = v) ∧
      (∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i) := by
  have hp : ∀ i, 0 < 1+β*a i := fun i => hδ.trans_le (hm i)
  have hc : ∀ i, |(1+β*a i)⁻¹| ≤ δ⁻¹ := by
    intro i
    rw [abs_of_pos (inv_pos.mpr (hp i))]
    exact (inv_le_inv₀ (hp i) hδ).mpr (hm i)
  let R := spectralMultiplier b (fun i => (1+β*a i)⁻¹) δ⁻¹
    (inv_pos.mpr hδ).le hc
  have hr : ∀ v i, b.repr (R v) i = (1+β*a i)⁻¹*b.repr v i :=
    fun v i => repr_spectralMultiplier b _ _ _ hc v i
  refine ⟨R, ?_, ?_, hr⟩
  · intro v
    apply b.repr.injective
    ext i
    simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [repr_symmetric_eigenoperator T hT b a hb, hr]
    have hn := (hp i).ne'
    field_simp
    <;> ring
  · intro v
    apply b.repr.injective
    ext i
    rw [hr]
    simp only [map_add, map_smul, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [repr_symmetric_eigenoperator T hT b a hb]
    have hn := (hp i).ne'
    field_simp
    <;> ring

/-- The strict threshold and HS coefficient sum derive a uniform denominator
margin; no uniform coercivity premise is added at the final interface. -/
lemma exists_uniform_spectral_margin (β : ℝ) (a : ι → ℝ)
    (ha : Summable (fun i => (a i)^2)) (hm : ∀ i, 0 < 1+β*a i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ 1+β*a i := by
  obtain ⟨p,hp,_,hpm⟩ := DGRHS.Gaussian.exists_spectral_power_above_one β a ha hm
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  refine ⟨1-p⁻¹, by have := (inv_lt_one₀ hp0).mpr hp; linarith, ?_⟩
  intro i
  have hi := hpm i
  have hmul := mul_pos (inv_pos.mpr hp0) hi
  have he : p⁻¹*(1+p*β*a i) = p⁻¹+β*a i := by
    field_simp
    <;> ring
  rw [he] at hmul
  linarith

end DGRHS.Kernel
#print axioms DGRHS.Kernel.repr_spectralMultiplier
#print axioms DGRHS.Kernel.spectralMultiplier_inverse
#print axioms DGRHS.Kernel.exists_uniform_spectral_margin
