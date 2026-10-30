import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarLogEuler

/-! The strong logarithmic score equation supplies derivatives two and three
from derivatives zero and one. Only one spatial derivative of the actual
feedback is needed. This is a calculus step, not a minimizer-capture premise. -/

noncomputable section
open Filter Topology Function
open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem product_difference_small
    {F G : ℕ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hF : USmall (fun n t => F n t-f t)) (hG : USmall (fun n t => G n t-g t))
    (hf : Bdd f) (hg : Bdd g) : USmall (fun n t => F n t*G n t-f t*g t) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  have hGb : ∀ᶠ n in atTop, ∀ t, |G n t| ≤ B+1 := by
    filter_upwards [hG.bdd] with n hn t
    calc
      _ = |(G n t-g t)+g t| := by congr 1; ring
      _ ≤ |G n t-g t|+|g t| := abs_add_le _ _
      _ ≤ 1+B := add_le_add (hn t) (hB t)
      _ = B+1 := by ring
  have h1 := hF.mul_bdd (B+1) hGb
  have h2 := hG.mul_bdd A (Eventually.of_forall fun _ => hA)
  have he : (fun n t => F n t*G n t-f t*g t) =
      fun n t => (F n t-f t)*G n t+(G n t-g t)*f t := by funext n t; ring
  rw [he]
  exact h1.add h2

private theorem constant_difference_small (f : ℝ → ℝ) :
    USmall (fun (_ : ℕ) t => f t-f t) := by
  intro e he
  exact Eventually.of_forall fun _ t => by simpa using he.le

/-- Differentiating the actual physical logarithmic equation once. The
normalization multiplier is spatially constant and therefore disappears. -/
theorem logScoreODE_third_derivative (f q s : ℝ → ℝ) (r lam : ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : ContDiff ℝ ∞ s) (hq : Differentiable ℝ q)
    (he : ∀ t, -2*deriv (deriv f) t-(deriv f t)^2-2*s t*deriv f t-2*r*f t+q t-lam=0) :
    ∀ t, deriv (deriv (deriv f)) t =
      -(deriv f t*deriv (deriv f) t)-deriv s t*deriv f t-
        s t*deriv (deriv f) t-r*deriv f t+deriv q t/2 := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hfun : deriv (deriv f) = fun t =>
      (-1/2 : ℝ)*(deriv f t)^2-s t*deriv f t-r*f t+(1/2 : ℝ)*q t-(1/2 : ℝ)*lam := by
    funext t
    linarith [he t]
  intro t
  have h0 := (hf.differentiable (by simp) t).hasDerivAt
  have h1 := (hf1.differentiable (by simp) t).hasDerivAt
  have hsig := (hs.differentiable (by simp) t).hasDerivAt
  have hq1 := (hq t).hasDerivAt
  have hd := (((((h1.pow 2).const_mul (-1/2 : ℝ)).sub (hsig.mul h1)).sub
    (h0.const_mul r)).add (hq1.const_mul (1/2 : ℝ))).sub_const ((1/2 : ℝ)*lam)
  calc
    _ = deriv (fun t => (-1/2 : ℝ)*(deriv f t)^2-s t*deriv f t-r*f t+
        (1/2 : ℝ)*q t-(1/2 : ℝ)*lam) t := congrArg (fun F : ℝ → ℝ => deriv F t) hfun
    _ = _ := hd.deriv.trans (by ring)

/-- For a fixed smooth periodic baseline and fixed smooth periodic reference
score, the genuine strong equation upgrades uniform convergence of profiles
and first derivatives to uniform convergence through the third derivative.
Feedback and its first spatial derivative vanish; no second feedback derivative
or third-root-derivative estimate is assumed. -/
theorem logScoreODE_second_third_small
    (f : ℕ → ℝ → ℝ) (f0 s : ℝ → ℝ) (q : ℕ → ℝ → ℝ) (r lam : ℕ → ℝ) (a : ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n)) (hf0 : ContDiff ℝ ∞ f0) (hs : ContDiff ℝ ∞ s)
    (hp0 : Periodic f0 1) (hps : Periodic s 1)
    (hq : ∀ n, Differentiable ℝ (q n))
    (he : ∀ n t, -2*deriv (deriv (f n)) t-(deriv (f n) t)^2-
      2*s t*deriv (f n) t-2*r n*f n t+q n t-lam n=0)
    (he0 : ∀ t, -2*deriv (deriv f0) t-(deriv f0 t)^2-2*s t*deriv f0 t-2*a*f0 t=0)
    (h0 : USmall (fun n t => f n t-f0 t))
    (h1 : USmall (fun n t => deriv (f n) t-deriv f0 t))
    (hr : Tendsto r atTop (𝓝 a)) (hlam : Tendsto lam atTop (𝓝 0))
    (hqq : USmall q) (hqd : USmall (fun n t => deriv (q n) t)) :
    USmall (fun n t => deriv (deriv (f n)) t-deriv (deriv f0) t) ∧
      USmall (fun n t => deriv (deriv (deriv (f n))) t-deriv (deriv (deriv f0)) t) := by
  have hf01 := (contDiff_infty_iff_deriv.mp hf0).2
  have hf02 := (contDiff_infty_iff_deriv.mp hf01).2
  have hs1 := (contDiff_infty_iff_deriv.mp hs).2
  have b0 := periodic_bdd hp0 hf0.continuous
  have b1 := periodic_bdd (DGPS.Analysis.PeriodicHolder.periodic_deriv hp0) hf01.continuous
  have b2 := periodic_bdd (DGPS.Analysis.PeriodicHolder.periodic_deriv
    (DGPS.Analysis.PeriodicHolder.periodic_deriv hp0)) hf02.continuous
  have bs := periodic_bdd hps hs.continuous
  have bsd := periodic_bdd (DGPS.Analysis.PeriodicHolder.periodic_deriv hps) hs1.continuous
  have ba : Bdd (fun _ : ℝ => a) := ⟨|a|, fun _ => le_rfl⟩
  have hra : USmall (fun n (_ : ℝ) => r n-a) := by
    apply USmall.of_seq
    simpa using hr.sub_const a
  have hla := USmall.of_seq hlam
  have hp := product_difference_small h1 h1 b1 b1
  have hsp := product_difference_small (constant_difference_small s) h1 bs b1
  have hrp := product_difference_small hra h0 ba b0
  have h2 : USmall (fun n t => deriv (deriv (f n)) t-deriv (deriv f0) t) := by
    have ht := ((((hp.const_mul (-1/2 : ℝ)).sub hsp).sub hrp).add
      (hqq.const_mul (1/2 : ℝ))).sub (hla.const_mul (1/2 : ℝ))
    have heq : (fun n t => deriv (deriv (f n)) t-deriv (deriv f0) t) =
        fun n t => (-1/2 : ℝ)*((deriv (f n) t)^2-(deriv f0 t)^2)-
          (s t*deriv (f n) t-s t*deriv f0 t)-(r n*f n t-a*f0 t)+
            (1/2 : ℝ)*q n t-(1/2 : ℝ)*lam n := by
      funext n t
      linarith [he n t, he0 t]
    rw [heq]
    simpa only [pow_two] using ht
  refine ⟨h2, ?_⟩
  have hprod := product_difference_small h1 h2 b1 b2
  have hsd := product_difference_small (constant_difference_small (deriv s)) h1 bsd b1
  have hsf := product_difference_small (constant_difference_small s) h2 bs b2
  have hrf := product_difference_small hra h1 ba b1
  have ht := ((((hprod.neg).sub hsd).sub hsf).sub hrf).add (hqd.const_mul (1/2 : ℝ))
  have h3 := fun n => logScoreODE_third_derivative (f n) (q n) s (r n) (lam n)
    (hf n) hs (hq n) (he n)
  have h30 := logScoreODE_third_derivative f0 (fun _ => 0) s a 0 hf0 hs
    (differentiable_const 0) (fun t => by simpa using he0 t)
  have heq : (fun n t => deriv (deriv (deriv (f n))) t-deriv (deriv (deriv f0)) t) =
      fun n t => -(deriv (f n) t*deriv (deriv (f n)) t-deriv f0 t*deriv (deriv f0) t)-
        (deriv s t*deriv (f n) t-deriv s t*deriv f0 t)-
        (s t*deriv (deriv (f n)) t-s t*deriv (deriv f0) t)-
        (r n*deriv (f n) t-a*deriv f0 t)+(1/2 : ℝ)*deriv (q n) t := by
    funext n t
    rw [h3 n t, h30 t]
    simp only [deriv_const]
    ring
  rw [heq]
  exact ht

end DGPS.Examples.ThreeSpeciesCircle
