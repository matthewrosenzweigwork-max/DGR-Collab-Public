import DGPS.Lipschitz.T01MobilityLimit
import DGPS.Lipschitz.T01FluctuationFourthMoment
import SharpSymmetricLSI.Paper.FormLiminfS14b

/-!
# The native centered generator and its finite-rank five-term split

This is finite pointwise algebra. The drift is the actual native `dualD`; no legacy
potential hypotheses, eigen-equations, probability laws, or convergence inputs are used.
The finite-rank diagonal coefficient is the row eigenvalue, preserving the order ΛT.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

open SharpLSI

private theorem finite_generator_split (lam : ℕ → ℝ) (c : Cyl)
    (s : Finset ℕ) (a B : ℕ → ℕ → ℝ) (z : Fin c.J → ℝ) (Z : ℕ → ℝ)
    (D : Fin c.J → ℝ) :
    (∑ i : Fin c.J, (lam (i.val + 1) * z i * cylD c i z -
      ∑ j : Fin c.J, fderiv ℝ (cylD c i) z (Pi.single j 1) * B j i + cylD c i z * D i)) =
      (∑ i : Fin c.J, lam (i.val + 1) *
        (z i * cylD c i z - fderiv ℝ (cylD c i) z (Pi.single i 1))) +
      (∑ i : Fin c.J, cylD c i z * ∑ p ∈ s, ∑ q ∈ s,
        a p q * Z q * (if p = i.val then lam (i.val + 1) else 0)) -
      (∑ i : Fin c.J, ∑ j : Fin c.J, fderiv ℝ (cylD c i) z (Pi.single j 1) *
        (B j i - if j.val = i.val then lam (i.val + 1) else 0)) +
      (∑ i : Fin c.J, cylD c i z * (D i -
        ∑ p ∈ s, ∑ q ∈ s, a p q * Z q * B p i)) +
      (∑ i : Fin c.J, cylD c i z * ∑ p ∈ s, ∑ q ∈ s,
        a p q * Z q * (B p i - if p = i.val then lam (i.val + 1) else 0)) := by
  have hdiag : ∀ i : Fin c.J, (∑ j : Fin c.J,
      fderiv ℝ (cylD c i) z (Pi.single j 1) *
        (if j.val = i.val then lam (i.val + 1) else 0)) =
      fderiv ℝ (cylD c i) z (Pi.single i 1) * lam (i.val + 1) := fun i => by
    rw [Finset.sum_eq_single i (fun j _ hj => by
      rw [if_neg (fun h => hj (Fin.ext h)), mul_zero]) (by simp), if_pos rfl]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, hdiag]
  have e1 : (∑ i : Fin c.J, lam (i.val + 1) * z i * cylD c i z) =
      ∑ i : Fin c.J, lam (i.val + 1) * (z i * cylD c i z) :=
    Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  have e2 : (∑ i : Fin c.J, fderiv ℝ (cylD c i) z (Pi.single i 1) * lam (i.val + 1)) =
      ∑ i : Fin c.J, lam (i.val + 1) * fderiv ℝ (cylD c i) z (Pi.single i 1) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, e2]
  ring

/-- The native generator equals its finite-dimensional main part and three explicit errors.
The drift coefficient remains `dualD` of the supplied actual centered force. -/
theorem t01_centered_dualGen_split {d : ℕ} (e : ℕ → Torus d → ℝ)
    (lam : ℕ → ℝ) (N : ℕ+) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    {J' : ℕ} (hJ : c.J ≤ J') (hsJ : ∀ q ∈ s, q < J')
    (gU : ParticleSpace d N → Fin N → Tangent d) (X : ParticleSpace d N) :
    dualGen N (fun i : Fin c.J => lam (i.val + 1))
      (fun i : Fin c.J => e (i.val + 1)) c.φ gU X =
      crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) -
      (∑ i : Fin c.J, ∑ j : Fin c.J,
        fderiv ℝ (cylD c i) (zC e N c.J X) (Pi.single j 1) *
          (mobA e N X j i - if j.val = i.val then lam (i.val + 1) else 0)) +
      (∑ i : Fin c.J, cylD c i (zC e N c.J X) *
        (dualD N (fun k : Fin c.J => e (k.val + 1)) gU i X -
          ∑ p ∈ s, ∑ q ∈ s, a p q * fluct e N q X * mobA e N X p i)) +
      (∑ i : Fin c.J, cylD c i (zC e N c.J X) * ∑ p ∈ s, ∑ q ∈ s,
        a p q * fluct e N q X *
          (mobA e N X p i - if p = i.val then lam (i.val + 1) else 0)) := by
  let v : Fin c.J → Torus d → ℝ := fun i => e (i.val + 1)
  have hZ : dualZ N v X = zC e N c.J X := by
    funext i
    exact t01_dualZ_eq_fluct e N i X
  have hA : ∀ i j : Fin c.J, dualA N v i j X = mobA e N X j i := by
    intro i j
    rw [t01_dualA_eq_mobA]
    unfold mobA
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  have hnative : dualGen N (fun i : Fin c.J => lam (i.val + 1)) v c.φ gU X =
      ∑ i : Fin c.J, (lam (i.val + 1) * zC e N c.J X i * cylD c i (zC e N c.J X) -
        ∑ j : Fin c.J, fderiv ℝ (cylD c i) (zC e N c.J X) (Pi.single j 1) * mobA e N X j i +
        cylD c i (zC e N c.J X) * dualD N v gU i X) := by
    unfold dualGen
    rw [hZ]
    simp only [hA, dc2, dc, cylD, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hb : (∑ i : Fin c.J, ∑ j : Fin c.J,
        mobA e N X j i * fderiv ℝ (dc c.φ i)
          (zC e N c.J X) (Pi.single j 1)) =
        ∑ i : Fin c.J, ∑ j : Fin c.J,
          fderiv ℝ (cylD c i)
            (zC e N c.J X) (Pi.single j 1) * mobA e N X j i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hb]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hmain : crossH lam c s a hJ (fun n : Fin J' => fluct e N n X) =
      crossH1 lam c (zC e N c.J X) +
        crossH2 lam c s a (zC e N c.J X) (fun q => fluct e N q X) := by
    have hp : projJ hJ (fun n : Fin J' => fluct e N n X) = zC e N c.J X := by
      funext i
      rfl
    unfold crossH
    rw [hp]
    congr 1
    unfold crossH2
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [extN, dif_pos (hsJ q hq)]
  have hs := finite_generator_split lam c s a (mobA e N X) (zC e N c.J X)
    (fun q => fluct e N q X) (fun i => dualD N v gU i X)
  simp only [crossH1, crossH2, lamShift] at hmain
  rw [hnative, hs, ← hmain]

end DGPS.Lipschitz
