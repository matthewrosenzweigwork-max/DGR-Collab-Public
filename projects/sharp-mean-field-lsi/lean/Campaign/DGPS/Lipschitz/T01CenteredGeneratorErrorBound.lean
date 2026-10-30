import DGPS.Lipschitz.T01CenteredGeneratorAlgebra
import FullLabeledLSI.Paper.Sec5ForceJensen
import SharpSymmetricLSI.Paper.FormLiminfS14d

/-!
# Integrability and the native centered-generator cross error

The finite-particle bounded measurable drift input is discharged for the genuine `Gpart`
representative. No desired generator limit, legacy potential hypothesis, or finite-rank
replacement bound is assumed in the three-error inequality.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL

/-- The true bounded measurable particle force makes every native drift coefficient bounded
measurable at fixed particle number. The resulting bound may depend on that number and mode. -/
theorem t01_Gpart_dualD_bddMeas {d : ℕ} {e : ℕ → Torus d → ℝ}
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    {bF : Torus d → Torus d → Fin d → ℝ} {bΔ : Torus d → Fin d → ℝ} {Bb : ℝ}
    (hRep : ForceRep bF bΔ Bb) (N : ℕ+) {n : ℕ} (i : Fin n) :
    BddMeas (fun X : ParticleSpace d N =>
      dualD N (fun k : Fin n => e (k.val + 1))
        (fun X l => WithLp.toLp 2 (fun k => Gpart bF bΔ N X l k)) i X) := by
  obtain ⟨Ci, hCi⟩ := exists_bound_cgrad (hφ (i.val + 1))
  unfold dualD
  simp only [dg_inner, smoothGrad_apply]
  change BddMeas (fun X : ParticleSpace d N => (Real.sqrt (N : ℝ))⁻¹ *
    ∑ l, ∑ k, Gpart bF bΔ N X l k * cgrad (e (i.val + 1)) (X l) k)
  refine (BddMeas.const _).mul (BddMeas.sum _ fun l _ => BddMeas.sum _ fun k _ => ?_)
  exact BddMeas.mul
    ⟨measurable_Gpart hRep l k, (N : ℝ)⁻¹ * ((N : ℝ) * Bb + Bb),
      fun X => abs_Gpart_le hRep X l k⟩
    ⟨(measurable_cgrad (hφ (i.val + 1)) k).comp (measurable_pi_apply l),
      Ci, fun X => hCi (X l) k⟩

/-- A native generator with genuine finite-particle bounded measurable drift coefficients is
itself bounded measurable. This assertion has no probability or limiting-form premise. -/
theorem t01_centered_dualGen_bddMeas {d : ℕ} (N : ℕ+)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (c : Cyl)
    (gU : ParticleSpace d N → Fin N → Tangent d)
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (hD : ∀ i : Fin c.J, BddMeas (fun X =>
      dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X)) :
    BddMeas (fun X => dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun i : Fin c.J => e (i.val + 1)) c.φ gU X) := by
  let z := fun X : ParticleSpace d N => zC e N c.J X
  have bψ : ∀ i : Fin c.J, BddMeas (fun X => cylD c i (z X)) := fun i =>
    bddMeas_comp_zC hφ N (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  have bdψ : ∀ i j : Fin c.J, BddMeas (fun X =>
      fderiv ℝ (cylD c i) (z X) (Pi.single j 1)) := fun i j =>
    bddMeas_comp_zC hφ N
      (((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hasCompactSupport_cylD c i).fderiv_apply (𝕜 := ℝ) _)
  have bZ : ∀ q, BddMeas (fun X : ParticleSpace d N => fluct e N q X) :=
    fun q => bddMeas_eCsum hφ N q
  have bA : ∀ i j, BddMeas (fun X : ParticleSpace d N => mobA e N X i j) :=
    fun i j => bddMeas_mobA hφ N i j
  have hb := ((BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      ((BddMeas.const (lam (i.val + 1))).mul (bZ i)).mul (bψ i)).sub
    (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun j _ =>
        (bA i j).mul (bdψ i j))).add
    (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ => (hD i).mul (bψ i))
  have hZ : ∀ X, dualZ N (fun i : Fin c.J => e (i.val + 1)) X = z X := by
    intro X
    funext i
    exact t01_dualZ_eq_fluct e N i X
  have heq : (fun X => dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun i : Fin c.J => e (i.val + 1)) c.φ gU X) =
      (fun X => (∑ i : Fin c.J, lam (i.val + 1) * fluct e N i X * cylD c i (z X)) -
        (∑ i : Fin c.J, ∑ j : Fin c.J,
          mobA e N X i j * fderiv ℝ (cylD c i) (z X) (Pi.single j 1)) +
        ∑ i : Fin c.J, dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X * cylD c i (z X)) := by
    funext X
    unfold dualGen
    rw [hZ X]
    simp only [t01_dualA_eq_mobA, dc2, dc, cylD] <;> rfl
  rw [heq]
  exact hb

/-- Native generator pairings with every actual L2 particle test are genuine integrals. -/
theorem t01_centered_dualGen_integrable {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (c : Cyl)
    (gU : ParticleSpace d N → Fin N → Tangent d)
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (hD : ∀ i : Fin c.J, BddMeas (fun X =>
      dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X))
    (f : ParticleSpace d N → ℝ) (hfL : MemLp f 2 (particleLaw A N)) :
    Integrable (fun X => f X * dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun i : Fin c.J => e (i.val + 1)) c.φ gU X) (particleLaw A N) :=
  integrable_mul_of_bddMeas hfL (t01_centered_dualGen_bddMeas N e lam c gU hφ hD)

/-- The actual finite-rank force-error pairing is genuinely integrable. This discharges
the integrability premise of the force AM-GM bound without an integral-default branch. -/
theorem t01_centered_force_pairing_integrable {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (e : ℕ → Torus d → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    (gU : ParticleSpace d N → Fin N → Tangent d)
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (hD : ∀ i : Fin c.J, BddMeas (fun X =>
      dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X))
    (f : ParticleSpace d N → ℝ) (hfL : MemLp f 2 (particleLaw A N)) (i : Fin c.J) :
    Integrable (fun X => |f X * cylD c i (zC e N c.J X) *
      (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X -
        ∑ p ∈ s, ∑ q ∈ s, a p q * fluct e N q X * mobA e N X p i)|)
      (particleLaw A N) := by
  have bψ : BddMeas (fun X : ParticleSpace d N => cylD c i (zC e N c.J X)) :=
    bddMeas_comp_zC hφ N (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  have bZ : ∀ q, BddMeas (fun X : ParticleSpace d N => fluct e N q X) :=
    fun q => bddMeas_eCsum hφ N q
  have bA : ∀ p, BddMeas (fun X : ParticleSpace d N => mobA e N X p i) :=
    fun p => bddMeas_mobA hφ N p i
  have hint := integrable_mul_of_bddMeas hfL (bψ.mul ((hD i).sub
    (BddMeas.sum s fun p _ => BddMeas.sum s fun q _ =>
      ((BddMeas.const (a p q)).mul (bZ q)).mul (bA p))))
  exact (hint.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs

/-- Three explicit current Gibbs integral errors control the native generator/main-part
pairing. The primitive bounded-drift premise is supplied by the genuine Gpart helper above. -/
theorem t01_centered_cross_err_le {d : ℕ} (A : InteractionData d) (N : ℕ+)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    {J' : ℕ} (hJ : c.J ≤ J') (hsJ : ∀ q ∈ s, q < J')
    (gU : ParticleSpace d N → Fin N → Tangent d)
    (hφ : ∀ j, ContDiff ℝ 1 (e j ∘ liftT))
    (hD : ∀ i : Fin c.J, BddMeas (fun X =>
      dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X))
    (f : ParticleSpace d N → ℝ) (hfL : MemLp f 2 (particleLaw A N)) :
    |∫ X, f X * dualGen N (fun i : Fin c.J => lam (i.val + 1)) (fun k : Fin c.J => e (k.val + 1)) c.φ gU X ∂particleLaw A N -
        ∫ X, f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) ∂particleLaw A N| ≤
      (∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, |f X * fderiv ℝ (cylD c i) (zC e N c.J X) (Pi.single j 1) *
          (mobA e N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂particleLaw A N) +
      (∑ i : Fin c.J, ∫ X, |f X * cylD c i (zC e N c.J X) *
          (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
            ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (q + 1) (X l)) * mobA e N X p i)| ∂particleLaw A N) +
      (∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * ∫ X, |f X * (cylD c i (zC e N c.J X) *
          ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (q + 1) (X l))) *
          (mobA e N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂particleLaw A N) := by
  set P := particleLaw A N
  set z : Config N d → Fin c.J → ℝ := fun X => zC e N c.J X
  set Zq : ℕ → Config N d → ℝ := fun q X => (N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l, e (q + 1) (X l)
  -- bounded measurable building blocks
  have bψ : ∀ i : Fin c.J, BddMeas fun X => cylD c i (z X) := fun i =>
    bddMeas_comp_zC hφ N (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  have bdψ : ∀ i j : Fin c.J, BddMeas fun X => fderiv ℝ (cylD c i) (z X) (Pi.single j 1) :=
    fun i j => bddMeas_comp_zC hφ N
      (((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hasCompactSupport_cylD c i).fderiv_apply (𝕜 := ℝ) _)
  have bZ : ∀ q, BddMeas (Zq q) := fun q => bddMeas_eCsum hφ N q
  have bA : ∀ i j, BddMeas fun X => mobA e N X i j := fun i j => bddMeas_mobA hφ N i j
  have bD : ∀ i : Fin c.J, BddMeas (fun X =>
      dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X) := hD
  -- the three error terms
  set e3 : Config N d → ℝ := fun X => ∑ i : Fin c.J, ∑ j : Fin c.J,
    fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
      (mobA e N X j i - if (j : ℕ) = i then lam ((i : ℕ) + 1) else 0)
  set e4 : Config N d → ℝ := fun X => ∑ i : Fin c.J, cylD c i (z X) *
    (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X - ∑ p ∈ s, ∑ q ∈ s, a p q * Zq q X * mobA e N X p i)
  set e5 : Config N d → ℝ := fun X => ∑ i : Fin c.J, cylD c i (z X) * ∑ p ∈ s, ∑ q ∈ s,
    a p q * Zq q X * (mobA e N X p i - if p = (i : ℕ) then lam ((i : ℕ) + 1) else 0)
  have b3 : BddMeas e3 := BddMeas.sum _ fun i _ => BddMeas.sum _ fun j _ =>
    (bdψ i j).mul ((bA _ _).sub (BddMeas.const _))
  have b4 : BddMeas e4 := BddMeas.sum _ fun i _ => (bψ i).mul ((bD _).sub
    (BddMeas.sum _ fun p _ => BddMeas.sum _ fun q _ => ((BddMeas.const _).mul (bZ q)).mul (bA _ _)))
  have b5 : BddMeas e5 := BddMeas.sum _ fun i _ => (bψ i).mul (BddMeas.sum _ fun p _ =>
    BddMeas.sum _ fun q _ => ((BddMeas.const _).mul (bZ q)).mul ((bA _ _).sub (BddMeas.const _)))
  set m : Config N d → ℝ := fun X => crossH1 lam c (z X) + crossH2 lam c s a (z X) (fun q => Zq q X)
  have bm : BddMeas m := by
    refine (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ =>
      (BddMeas.const _).mul (((bZ (i : ℕ)).mul (bψ i)).sub (bdψ i i))).add
      (BddMeas.sum (Finset.univ : Finset (Fin c.J)) fun i _ => (bψ i).mul (BddMeas.sum _ fun p _ => BddMeas.sum _ fun q _ =>
        ((BddMeas.const _).mul (bZ q)).mul (BddMeas.const _)))
  have hm : ∀ X : ParticleSpace d N,
      crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) = m X := by
    intro X
    have hp : projJ hJ (fun n : Fin J' => fluct e N n X) = z X := rfl
    unfold crossH
    rw [hp]
    congr 1
    refine crossH2_congr lam c s a _ fun q hq => ?_
    rw [extN, dif_pos (hsJ q hq)]
    rfl
  have hgen : ∀ X : ParticleSpace d N,
      dualGen N (fun i : Fin c.J => lam (i.val + 1))
        (fun k : Fin c.J => e (k.val + 1)) c.φ gU X = m X - e3 X + e4 X + e5 X := by
    intro X
    have hh := t01_centered_dualGen_split e lam N c s a hJ hsJ gU X
    rw [hm X] at hh
    simpa only [m, e3, e4, e5, Zq, z, fluct] using hh
  have i1 : Integrable (fun X => f X * dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun k : Fin c.J => e (k.val + 1)) c.φ gU X) P :=
    t01_centered_dualGen_integrable A N e lam c gU hφ hD f hfL
  have i2 : Integrable (fun X => f X *
      crossH lam c s a hJ (fun n : Fin J' => fluct e N n X)) P :=
    (integrable_mul_of_bddMeas hfL bm).congr
      (Eventually.of_forall fun X => by
        change f X * m X = f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X)
        rw [hm X])
  have i3 := integrable_mul_of_bddMeas hfL b3
  have i4 := integrable_mul_of_bddMeas hfL b4
  have i5 := integrable_mul_of_bddMeas hfL b5
  have hdiff : ∫ X, f X * dualGen N (fun i : Fin c.J => lam (i.val + 1)) (fun k : Fin c.J => e (k.val + 1)) c.φ gU X ∂P -
      ∫ X, f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) ∂P =
      ∫ X, (-(f X * e3 X) + f X * e4 X + f X * e5 X) ∂P := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    change f X * dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun k : Fin c.J => e (k.val + 1)) c.φ gU X -
      f X * crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) =
        -(f X * e3 X) + f X * e4 X + f X * e5 X
    rw [hgen X, hm X]
    ring
  rw [hdiff]
  refine (abs_integral_le_integral_abs).trans ?_
  have hpt : ∀ X, |-(f X * e3 X) + f X * e4 X + f X * e5 X| ≤
      |f X * e3 X| + |f X * e4 X| + |f X * e5 X| := fun X => by
    calc _ ≤ |-(f X * e3 X) + f X * e4 X| + |f X * e5 X| := abs_add_le _ _
      _ ≤ |-(f X * e3 X)| + |f X * e4 X| + |f X * e5 X| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_neg]
  refine (integral_mono ((i3.neg.add i4).add i5).abs ((i3.abs.add i4.abs).add i5.abs) hpt).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (f := fun X => |f X * e3 X| + |f X * e4 X|) (g := fun X => |f X * e5 X|)
      (i3.abs.add i4.abs) i5.abs,
    integral_add (f := fun X => |f X * e3 X|) (g := fun X => |f X * e4 X|) i3.abs i4.abs]
  -- each error term
  have hb3 : ∫ X, |f X * e3 X| ∂P ≤ ∑ i : Fin c.J, ∑ j : Fin c.J, ∫ X, |f X *
      fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
        (mobA e N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂P := by
    have hint : ∀ i j : Fin c.J, Integrable (fun X => |f X *
        fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
          (mobA e N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)|) P := fun i j => by
      have := integrable_mul_of_bddMeas hfL ((bdψ i j).mul ((bA (j : ℕ) i).sub
        (BddMeas.const (if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0))))
      exact (this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs
    calc ∫ X, |f X * e3 X| ∂P ≤ ∫ X, ∑ i : Fin c.J, ∑ j : Fin c.J, |f X *
          fderiv ℝ (cylD c i) (z X) (Pi.single j 1) *
            (mobA e N X j i - if (j : ℕ) = i then lam ((j : ℕ) + 1) else 0)| ∂P := by
          refine integral_mono i3.abs (integrable_finset_sum _ fun i _ =>
            integrable_finset_sum _ fun j _ => hint i j) fun X => ?_
          simp only [e3, Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => le_of_eq ?_))
          rw [ite_lam_eq lam (i : ℕ) (j : ℕ), mul_assoc]
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
          exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun j _ => hint i j
  have hb4 : ∫ X, |f X * e4 X| ∂P ≤ ∑ i : Fin c.J, ∫ X, |f X * cylD c i (z X) *
      (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
        Zq q X * mobA e N X p i)| ∂P := by
    have hint : ∀ i : Fin c.J, Integrable (fun X => |f X * cylD c i (z X) *
        (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X - ∑ p ∈ s, ∑ q ∈ s, a p q *
          Zq q X * mobA e N X p i)|) P := fun i => by
      have := integrable_mul_of_bddMeas hfL ((bψ i).mul ((bD i).sub
        (BddMeas.sum s fun p _ => BddMeas.sum s fun q _ =>
          ((BddMeas.const (a p q)).mul (bZ q)).mul (bA p i))))
      exact (this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs
    rw [← integral_finset_sum _ fun i _ => hint i]
    refine integral_mono i4.abs (integrable_finset_sum _ fun i _ => hint i) fun X => ?_
    simp only [e4, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    rw [mul_assoc]
  have hb5 : ∫ X, |f X * e5 X| ∂P ≤ ∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * ∫ X,
      |f X * (cylD c i (z X) * Zq q X) *
        (mobA e N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂P := by
    have hint : ∀ (i : Fin c.J) (p q : ℕ), Integrable (fun X => |a p q| * |f X *
        (cylD c i (z X) * Zq q X) *
        (mobA e N X p i - if p = (i : ℕ) then lam (p + 1) else 0)|) P := fun i p q => by
      have := integrable_mul_of_bddMeas hfL (((bψ i).mul (bZ q)).mul ((bA p i).sub
        (BddMeas.const (if p = (i : ℕ) then lam (p + 1) else 0))))
      exact ((this.congr (Eventually.of_forall fun X => by simp only [mul_assoc])).abs).const_mul _
    calc ∫ X, |f X * e5 X| ∂P ≤ ∫ X, ∑ i : Fin c.J, ∑ p ∈ s, ∑ q ∈ s, |a p q| * |f X *
          (cylD c i (z X) * Zq q X) *
          (mobA e N X p i - if p = (i : ℕ) then lam (p + 1) else 0)| ∂P := by
          refine integral_mono i5.abs (integrable_finset_sum _ fun i _ => integrable_finset_sum _
            fun p _ => integrable_finset_sum _ fun q _ => hint i p q) fun X => ?_
          simp only [e5, Finset.mul_sum]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ =>
              (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => le_of_eq ?_)))
          rw [ite_lam_eq lam (i : ℕ) p, ← abs_mul]
          congr 1
          ring
      _ = _ := by
          rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun p _ =>
            integrable_finset_sum _ fun q _ => hint i p q]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hint i p q]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [integral_finset_sum _ fun q _ => hint i p q]
          exact Finset.sum_congr rfl fun q _ => integral_const_mul _ _
  linarith


end DGPS.Lipschitz
