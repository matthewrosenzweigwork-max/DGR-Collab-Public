import DGPS.Circle.AngularNormalization
import DGPS.Lipschitz.WeightedGenerator
import DGPS.Lipschitz.WeightedSpectrum
import DGPS.Circle.FirstClusterFourierEX009
import DGPS.Foundations.SobolevEmbedding

/-!
# EX009: the first weighted spectral cluster

Explicit complementary trigonometric correctors give two transported quasimodes
with a uniform cubic residual.  Weak integration by parts against the canonical
weighted eigenbasis, Fourier counting and Parseval identify the genuine first pair.
A projected Gram and Rayleigh comparison handles coincident model eigenvalues.

All derivatives use the real periodic angular lift.  The public theorem quantifies
constants before the compact coefficient choice, smooth probability family and
parameter window.  Probability-to-log transport retains the scalar normalization.
-/

namespace DGPS.Circle.FirstClusterPerturbation

open MeasureTheory Real
open scoped InnerProductSpace ContDiff

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Lipschitz.WeightedSpectrum DGPS.Circle.AngularNormalization

/-- Multiplication by the square root of the (possibly unnormalised) density. -/
noncomputable def groundTransform_EX009 (ell f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (ell x / 2) * f x

/-- The negative angular weighted diffusion differential expression. -/
noncomputable def negativeGenerator_EX009 (ell f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv f) x - deriv ell x * deriv f x

/-- The potential after conjugation by the square root of the density. -/
noncomputable def schrodingerPotential_EX009 (ell : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv ell) x / 2 + (deriv ell x) ^ 2 / 4


/-- Additive normalizing constants in the logarithm do not change the potential. -/
theorem potential_add_const_EX009 (ell : ℝ → ℝ) (k x : ℝ) :
    schrodingerPotential_EX009 (fun y => ell y + k) x =
      schrodingerPotential_EX009 ell x := by
  simp only [schrodingerPotential_EX009, deriv_add_const', deriv_add_const]

/-- The conjugated angular differential expression. -/
noncomputable def schrodingerOperator_EX009 (ell u : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (deriv u) x + schrodingerPotential_EX009 ell x * u x

theorem deriv_groundTransform_EX009 {ell f : ℝ → ℝ}
    (hell : Differentiable ℝ ell) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (groundTransform_EX009 ell f) x =
      Real.exp (ell x / 2) * (deriv f x + deriv ell x / 2 * f x) := by
  have he := ((hell x).hasDerivAt.div_const 2).exp
  have h := (he.mul (hf x).hasDerivAt).deriv
  change deriv (fun y => Real.exp (ell y / 2) * f y) x = _ at h ⊢
  rw [h]
  ring

theorem deriv2_groundTransform_EX009 {ell f : ℝ → ℝ}
    (hell : Differentiable ℝ ell) (hell' : Differentiable ℝ (deriv ell))
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    deriv (deriv (groundTransform_EX009 ell f)) x =
      Real.exp (ell x / 2) *
        (deriv (deriv f) x + deriv ell x * deriv f x +
          (deriv (deriv ell) x / 2 + (deriv ell x) ^ 2 / 4) * f x) := by
  have he := ((hell x).hasDerivAt.div_const 2).exp
  have hi := (hf' x).hasDerivAt.add
    (((hell' x).hasDerivAt.div_const 2).mul (hf x).hasDerivAt)
  have h := (he.mul hi).deriv
  rw [show deriv (groundTransform_EX009 ell f) =
    (fun y => Real.exp (ell y / 2) * (deriv f y + deriv ell y / 2 * f y)) from
      funext (deriv_groundTransform_EX009 hell hf)]
  change deriv (fun y => Real.exp (ell y / 2) *
    (deriv f y + deriv ell y / 2 * f y)) x = _ at h
  rw [h]
  simp only [Pi.add_apply, Pi.mul_apply]
  ring

/-- Genuine conjugation of the two differential expressions, before the closed-domain bridge. -/
theorem differential_conjugation_EX009 {ell f : ℝ → ℝ}
    (hell : Differentiable ℝ ell) (hell' : Differentiable ℝ (deriv ell))
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) (x : ℝ) :
    schrodingerOperator_EX009 ell (groundTransform_EX009 ell f) x =
      Real.exp (ell x / 2) * negativeGenerator_EX009 ell f x := by
  unfold schrodingerOperator_EX009
  rw [deriv2_groundTransform_EX009 hell hell' hf hf']
  unfold schrodingerPotential_EX009 groundTransform_EX009 negativeGenerator_EX009
  ring

/-- The pointwise eigenfunction equation is transported with the same eigenvalue. -/
theorem differential_eigenvalue_iff_EX009 {ell f : ℝ → ℝ}
    (hell : Differentiable ℝ ell) (hell' : Differentiable ℝ (deriv ell))
    (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) (lam x : ℝ) :
    schrodingerOperator_EX009 ell (groundTransform_EX009 ell f) x =
      lam * groundTransform_EX009 ell f x ↔
    negativeGenerator_EX009 ell f x = lam * f x := by
  rw [differential_conjugation_EX009 hell hell' hf hf']
  unfold groundTransform_EX009
  constructor
  · intro h
    have h' : Real.exp (ell x / 2) * negativeGenerator_EX009 ell f x =
        Real.exp (ell x / 2) * (lam * f x) := by nlinarith [h]
    exact (mul_left_cancel₀ (Real.exp_ne_zero _) h')
  · intro h
    rw [h]
    ring

/-- Nonzero eigenfunctions stay nonzero under the actual conjugating multiplier. -/
theorem groundTransform_nonzero_iff_EX009 (ell f : ℝ → ℝ) :
    groundTransform_EX009 ell f ≠ 0 ↔ f ≠ 0 := by
  have hz : groundTransform_EX009 ell f = 0 ↔ f = 0 := by
    constructor
    · intro h
      funext x
      have hx := congrFun h x
      simpa [groundTransform_EX009, Real.exp_ne_zero] using hx
    · intro h
      subst f
      ext x
      simp [groundTransform_EX009]
  exact not_congr hz

/-- The exact scalar third-order remainder of the conjugated potential. -/
noncomputable def potentialRemainder_EX009 (h u v r s : ℝ) : ℝ :=
  s / 2 + u * v / 2 + h * (v ^ 2 / 4 + u * r / 2) +
    h ^ 2 * v * r / 2 + h ^ 3 * r ^ 2 / 4

theorem potential_jet_expansion_EX009 (h u v r a b s : ℝ) :
    (h * a + h ^ 2 * b + h ^ 3 * s) / 2 +
        (h * u + h ^ 2 * v + h ^ 3 * r) ^ 2 / 4 =
      h * (a / 2) + h ^ 2 * (b / 2 + u ^ 2 / 4) +
        h ^ 3 * potentialRemainder_EX009 h u v r s := by
  unfold potentialRemainder_EX009
  ring

/-- Uniform coefficient bound; the second derivative remainder is bounded independently. -/
theorem potentialRemainder_bound_EX009 {h u v r s M R : ℝ}
    (hh : |h| ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hu : |u| ≤ M) (hv : |v| ≤ M) (hr : |r| ≤ R) (hs : |s| ≤ R) :
    |potentialRemainder_EX009 h u v r s| ≤
      R / 2 + 3 * M ^ 2 / 4 + M * R + R ^ 2 / 4 := by
  have hh2 : |h ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg h) hh 2
  have hh3 : |h ^ 3| ≤ 1 := by
    rw [pow_succ, abs_mul]
    calc |h ^ 2| * |h| ≤ 1 * 1 := mul_le_mul hh2 hh (abs_nonneg _) (by norm_num)
         _ = 1 := by ring
  have huv : |u * v| ≤ M ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul hu hv (abs_nonneg _) hM
  have hv2 : |v ^ 2| ≤ M ^ 2 := by
    rw [pow_two, abs_mul, pow_two]
    exact mul_le_mul hv hv (abs_nonneg _) hM
  have hur : |u * r| ≤ M * R := by
    rw [abs_mul]
    exact mul_le_mul hu hr (abs_nonneg _) hM
  have hvr : |v * r| ≤ M * R := by
    rw [abs_mul]
    exact mul_le_mul hv hr (abs_nonneg _) hM
  have hr2 : |r ^ 2| ≤ R ^ 2 := by
    rw [pow_two, abs_mul, pow_two]
    exact mul_le_mul hr hr (abs_nonneg _) hR
  have hi : |v ^ 2 / 4 + u * r / 2| ≤ M ^ 2 / 4 + M * R / 2 := by
    calc |v ^ 2 / 4 + u * r / 2| ≤ |v ^ 2 / 4| + |u * r / 2| := abs_add_le _ _
         _ ≤ M ^ 2 / 4 + M * R / 2 := by
           simp only [abs_div, show |(2 : ℝ)| = 2 by norm_num, show |(4 : ℝ)| = 4 by norm_num]
           gcongr
  have ht : |h * (v ^ 2 / 4 + u * r / 2)| ≤ M ^ 2 / 4 + M * R / 2 := by
    rw [abs_mul]
    calc |h| * |v ^ 2 / 4 + u * r / 2| ≤ 1 * (M ^ 2 / 4 + M * R / 2) :=
           mul_le_mul hh hi (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _
  have ht2 : |h ^ 2 * v * r / 2| ≤ M * R / 2 := by
    rw [abs_div, abs_mul, abs_mul]
    calc |h ^ 2| * |v| * |r| / |2| ≤ 1 * M * R / |2| := by gcongr
         _ = M * R / 2 := by norm_num
  have ht3 : |h ^ 3 * r ^ 2 / 4| ≤ R ^ 2 / 4 := by
    rw [abs_div, abs_mul]
    calc |h ^ 3| * |r ^ 2| / |4| ≤ 1 * R ^ 2 / |4| := by gcongr
         _ = R ^ 2 / 4 := by norm_num
  unfold potentialRemainder_EX009
  calc
    |s / 2 + u * v / 2 + h * (v ^ 2 / 4 + u * r / 2) +
        h ^ 2 * v * r / 2 + h ^ 3 * r ^ 2 / 4| ≤
        |s / 2| + |u * v / 2| + |h * (v ^ 2 / 4 + u * r / 2)| +
          |h ^ 2 * v * r / 2| + |h ^ 3 * r ^ 2 / 4| := by
      have h1 := abs_add_le (s / 2) (u * v / 2)
      have h2 := abs_add_le (s / 2 + u * v / 2)
        (h * (v ^ 2 / 4 + u * r / 2))
      have h3 := abs_add_le
        (s / 2 + u * v / 2 + h * (v ^ 2 / 4 + u * r / 2))
        (h ^ 2 * v * r / 2)
      have h4 := abs_add_le
        (s / 2 + u * v / 2 + h * (v ^ 2 / 4 + u * r / 2) + h ^ 2 * v * r / 2)
        (h ^ 3 * r ^ 2 / 4)
      linarith
    _ ≤ R / 2 + M ^ 2 / 2 + (M ^ 2 / 4 + M * R / 2) +
          M * R / 2 + R ^ 2 / 4 := by
      have hs2 : |s / 2| ≤ R / 2 := by
        simpa only [abs_div, show |(2 : ℝ)| = 2 by norm_num] using
          div_le_div_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2)
      have huv2 : |u * v / 2| ≤ M ^ 2 / 2 := by
        simpa only [abs_div, show |(2 : ℝ)| = 2 by norm_num] using
          div_le_div_of_nonneg_right huv (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add (add_le_add (add_le_add (add_le_add hs2 huv2) ht) ht2) ht3
    _ = _ := by ring

/-- Pointwise, hence uniform in the angular coordinate, third-order potential error. -/
theorem potential_expansion_bound_EX009 {ell : ℝ → ℝ} {h M R : ℝ}
    (u v r a b s : ℝ → ℝ)
    (hfirst : ∀ x, deriv ell x = h * u x + h ^ 2 * v x + h ^ 3 * r x)
    (hsecond : ∀ x, deriv (deriv ell) x = h * a x + h ^ 2 * b x + h ^ 3 * s x)
    (hh : |h| ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hu : ∀ x, |u x| ≤ M) (hv : ∀ x, |v x| ≤ M)
    (hr : ∀ x, |r x| ≤ R) (hs : ∀ x, |s x| ≤ R) (x : ℝ) :
    |schrodingerPotential_EX009 ell x - (h * (a x / 2) +
        h ^ 2 * (b x / 2 + (u x) ^ 2 / 4))| ≤
      |h| ^ 3 * (R / 2 + 3 * M ^ 2 / 4 + M * R + R ^ 2 / 4) := by
  unfold schrodingerPotential_EX009
  rw [hfirst, hsecond, potential_jet_expansion_EX009]
  have he : h * (a x / 2) + h ^ 2 * (b x / 2 + u x ^ 2 / 4) +
      h ^ 3 * potentialRemainder_EX009 h (u x) (v x) (r x) (s x) -
      (h * (a x / 2) + h ^ 2 * (b x / 2 + u x ^ 2 / 4)) =
      h ^ 3 * potentialRemainder_EX009 h (u x) (v x) (r x) (s x) := by ring
  rw [he, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (potentialRemainder_bound_EX009 hh hM hR (hu x) (hv x) (hr x) (hs x))
    (by positivity)



/-- The nonconstant first and second harmonics in the canonical logarithmic jet. -/
noncomputable def harmonicLog_EX009 (h A B C D : ℝ) (x : ℝ) : ℝ :=
  h * (A * Real.cos x + B * Real.sin x) +
    h ^ 2 * (C * Real.cos (2 * x) + D * Real.sin (2 * x))

theorem hasDerivAt_harmonicLog_EX009 (h A B C D x : ℝ) :
    HasDerivAt (harmonicLog_EX009 h A B C D)
      (h * (-A * Real.sin x + B * Real.cos x) +
        h ^ 2 * (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x))) x := by
  have ht : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hc := (hasDerivAt_cos (2 * x)).comp x ht
  have hs := (hasDerivAt_sin (2 * x)).comp x ht
  convert ((((hasDerivAt_cos x).const_mul A).add
    ((hasDerivAt_sin x).const_mul B)).const_mul h).add
    (((hc.const_mul C).add (hs.const_mul D)).const_mul (h ^ 2)) using 1
  · ext y
    rfl
  · ring

theorem deriv_harmonicLog_EX009 (h A B C D x : ℝ) :
    deriv (harmonicLog_EX009 h A B C D) x =
      h * (-A * Real.sin x + B * Real.cos x) +
        h ^ 2 * (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)) :=
  (hasDerivAt_harmonicLog_EX009 h A B C D x).deriv

theorem deriv2_harmonicLog_EX009 (h A B C D x : ℝ) :
    deriv (deriv (harmonicLog_EX009 h A B C D)) x =
      h * (-A * Real.cos x - B * Real.sin x) +
        h ^ 2 * (-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x)) := by
  have ht : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hc := (hasDerivAt_cos (2 * x)).comp x ht
  have hs := (hasDerivAt_sin (2 * x)).comp x ht
  have hd := ((((hasDerivAt_sin x).const_mul (-A)).add
    ((hasDerivAt_cos x).const_mul B)).const_mul h).add
    (((hs.const_mul (-2 * C)).add (hc.const_mul (2 * D))).const_mul (h ^ 2))
  have hder : HasDerivAt
      (fun y => h * (-A * Real.sin y + B * Real.cos y) +
        h ^ 2 * (-2 * C * Real.sin (2 * y) + 2 * D * Real.cos (2 * y)))
      (h * (-A * Real.cos x - B * Real.sin x) +
        h ^ 2 * (-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x))) x := by
    convert hd using 1
    · ext y
      rfl
    · ring
  rw [show deriv (harmonicLog_EX009 h A B C D) = _ from
    funext (deriv_harmonicLog_EX009 h A B C D)]
  exact hder.deriv

/-- Exact potential jet for the canonical first and second logarithmic harmonics. -/
theorem harmonic_potential_jet_EX009 (h A B C D x : ℝ) :
    schrodingerPotential_EX009 (harmonicLog_EX009 h A B C D) x =
      h * ((-A * Real.cos x - B * Real.sin x) / 2) +
      h ^ 2 * ((-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x)) / 2 +
        (-A * Real.sin x + B * Real.cos x) ^ 2 / 4) +
      h ^ 3 * potentialRemainder_EX009 h
        (-A * Real.sin x + B * Real.cos x)
        (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)) 0 0 := by
  unfold schrodingerPotential_EX009
  rw [deriv_harmonicLog_EX009, deriv2_harmonicLog_EX009]
  convert potential_jet_expansion_EX009 h
    (-A * Real.sin x + B * Real.cos x)
    (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)) 0
    (-A * Real.cos x - B * Real.sin x)
    (-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x)) 0 using 1
  ring



theorem harmonic_first_derivative_bound_EX009 (A B x : ℝ) :
    |-A * Real.sin x + B * Real.cos x| ≤ |A| + |B| := by
  calc
    |-A * Real.sin x + B * Real.cos x| ≤
        |-A * Real.sin x| + |B * Real.cos x| := abs_add_le _ _
    _ = |A| * |Real.sin x| + |B| * |Real.cos x| := by simp [abs_mul]
    _ ≤ |A| * 1 + |B| * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one x) (abs_nonneg A))
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg B))
    _ = |A| + |B| := by ring

theorem harmonic_second_derivative_bound_EX009 (C D x : ℝ) :
    |-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)| ≤
      2 * (|C| + |D|) := by
  have he : -2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x) =
      2 * (-C * Real.sin (2 * x) + D * Real.cos (2 * x)) := by ring
  rw [he, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  exact mul_le_mul_of_nonneg_left (harmonic_first_derivative_bound_EX009 C D (2 * x))
    (by norm_num)

/-- Uniform cubic potential error on every fixed bounded set of the four
harmonic coefficients.  The additional C2 logarithmic remainder is controlled
separately by potential_expansion_bound_EX009. -/
theorem harmonic_potential_expansion_bound_EX009 {h A B C D M : ℝ}
    (hh : |h| ≤ 1) (hM : 0 ≤ M)
    (hAB : |A| + |B| ≤ M) (hCD : 2 * (|C| + |D|) ≤ M) (x : ℝ) :
    |schrodingerPotential_EX009 (harmonicLog_EX009 h A B C D) x -
      (h * ((-A * Real.cos x - B * Real.sin x) / 2) +
      h ^ 2 * ((-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x)) / 2 +
        (-A * Real.sin x + B * Real.cos x) ^ 2 / 4))| ≤
      |h| ^ 3 * (3 * M ^ 2 / 4) := by
  have he := potential_expansion_bound_EX009
    (ell := harmonicLog_EX009 h A B C D) (h := h) (M := M) (R := 0)
    (fun y => -A * Real.sin y + B * Real.cos y)
    (fun y => -2 * C * Real.sin (2 * y) + 2 * D * Real.cos (2 * y))
    (fun _ => 0)
    (fun y => -A * Real.cos y - B * Real.sin y)
    (fun y => -4 * C * Real.cos (2 * y) - 4 * D * Real.sin (2 * y))
    (fun _ => 0)
    (fun y => by rw [deriv_harmonicLog_EX009]; ring)
    (fun y => by rw [deriv2_harmonicLog_EX009]; ring)
    hh hM le_rfl
    (fun y => (harmonic_first_derivative_bound_EX009 A B y).trans hAB)
    (fun y => (harmonic_second_derivative_bound_EX009 C D y).trans hCD)
    (by intro y; simp) (by intro y; simp) x
  simpa using he




/-- Integrality improves the complement gap from N squared to (N+1) squared. -/
theorem complement_frequency_gap_EX009 {d N : ℕ} {k : Fin d → ℤ}
    (hk : k ∉ freqBox d N) :
    4 * π ^ 2 * ((N : ℝ) + 1) ^ 2 ≤ gradWeight k := by
  rw [mem_freqBox] at hk
  push Not at hk
  obtain ⟨j, hj⟩ := hk
  have hInt : (N : ℤ) + 1 ≤ |k j| := by omega
  have hReal : (N : ℝ) + 1 ≤ |((k j : ℤ) : ℝ)| := by
    exact_mod_cast hInt
  have hsq : ((N : ℝ) + 1) ^ 2 ≤ ((k j : ℤ) : ℝ) ^ 2 := by
    rw [← sq_abs ((k j : ℤ) : ℝ)]
    exact pow_le_pow_left₀ (by positivity) hReal 2
  have hsum : ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  unfold gradWeight
  exact mul_le_mul_of_nonneg_left (hsq.trans hsum) (by positivity)

/-- A sharp Fourier counting barrier for the actual weak weighted spectrum on the
unit circle.  This uses the canonical energy identity on its entire weak form domain. -/
theorem frequency_barrier_EX009 {w : Torus 1 → ℝ} {c C : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C)
    {e : HilbertBasis ℕ ℝ (Hw 1 w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1}
    (hsd : SpectralData w e lam G) (hmono : Monotone lam) (N : ℕ) :
    4 * π ^ 2 * ((N : ℝ) + 1) ^ 2 * c / C ≤ lam (2 * N + 1) := by
  classical
  obtain ⟨x, hx⟩ := hwb.exists
  have hC : 0 < C := hc.trans_le (hx.1.trans hx.2)
  by_contra h
  have hlt : lam (2 * N + 1) < 4 * π ^ 2 * ((N : ℝ) + 1) ^ 2 * c / C :=
    lt_of_not_ge h
  have hscale : C * lam (2 * N + 1) / c <
      4 * π ^ 2 * ((N : ℝ) + 1) ^ 2 := by
    rw [lt_div_iff₀ hC] at hlt
    rw [div_lt_iff₀ hc]
    nlinarith
  have hcount := card_le_of_lam_le hw hc hwb hsd
    (Finset.range (2 * N + 2)) (lam (2 * N + 1)) (hsd.nonneg _) (fun i hi => by
      exact hmono (by have := Finset.mem_range.mp hi; omega))
    (freqBox 1 N) (fun k hk => neg_mem_freqBox hk) (fun k hk => by
      exact hscale.trans_le (complement_frequency_gap_EX009 hk))
  rw [Finset.card_range, card_freqBox] at hcount
  simp only [pow_one] at hcount
  omega

/-- The ground state and all modes after the first pair are separated from the
first Haar level whenever the density ratio is sufficiently close to one.
Eigenvalues here are in the physical unit-period normalization. -/
theorem spectral_separation_EX009 {w : Torus 1 → ℝ} {c C : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C)
    {e : HilbertBasis ℕ ℝ (Hw 1 w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1}
    (hsd : SpectralData w e lam G) (hmono : Monotone lam)
    (hclose : 3 * C < 4 * c) :
    a0 / 2 < lam 1 ∧ 3 * a0 < lam 3 := by
  obtain ⟨x, hx⟩ := hwb.exists
  have hC : 0 < C := hc.trans_le (hx.1.trans hx.2)
  have hfirst := frequency_barrier_EX009 hw hc hwb hsd hmono 0
  have hthird := frequency_barrier_EX009 hw hc hwb hsd hmono 1
  norm_num at hfirst hthird
  change 4 * π ^ 2 / 2 < lam 1 ∧ 3 * (4 * π ^ 2) < lam 3
  constructor
  · have hcoef : C < 2 * c := by linarith
    have hstrict : 4 * π ^ 2 / 2 < 4 * π ^ 2 * c / C := by
      rw [lt_div_iff₀ hC]
      have hm := mul_lt_mul_of_pos_left hcoef (by positivity : 0 < 4 * π ^ 2)
      nlinarith
    exact hstrict.trans_le hfirst
  · have hstrict : 3 * (4 * π ^ 2) < 4 * π ^ 2 * 4 * c / C := by
      rw [lt_div_iff₀ hC]
      have hm := mul_lt_mul_of_pos_left hclose (by positivity : 0 < 4 * π ^ 2)
      nlinarith
    exact hstrict.trans_le hthird



/-- A genuine weighted eigenbasis with separated ground and higher modes.  The
existence of two eigenvalues inside the intervening window and their second-order
asymptotics are not consequences of this lower counting estimate. -/
theorem exists_separated_eigenbasis_EX009 {w : Torus 1 → ℝ} {c C : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C)
    (hint : ∫ x, w x ∂haar 1 = 1) (hclose : 3 * C < 4 * c) :
    ∃ (e : HilbertBasis ℕ ℝ (Hw 1 w)) (lam : ℕ → ℝ)
      (G : ℕ → Torus 1 → Tangent 1),
      SpectralData w e lam G ∧
      (((e 0 : Hw 1 w) : Torus 1 → ℝ) =ᵐ[wMeasure 1 w] fun _ => 1) ∧
      lam 0 = 0 ∧ Monotone lam ∧ Filter.Tendsto lam Filter.atTop Filter.atTop ∧
      a0 / 2 < lam 1 ∧ 3 * a0 < lam 3 := by
  obtain ⟨e, lam, G, he0, h0, _, hmono, htop, hgrad, heig, henergy, _⟩ :=
    weighted_eigenbasis_and_growth (by norm_num : 0 < (1 : ℕ)) hw hc hwb hint
  have hnonneg : ∀ n, 0 ≤ lam n := fun n => by
    have := hmono (Nat.zero_le n)
    rwa [h0] at this
  have hsd : SpectralData w e lam G := ⟨hnonneg, hgrad, heig, henergy⟩
  obtain ⟨hfirst, hthird⟩ := spectral_separation_EX009 hw hc hwb hsd hmono hclose
  exact ⟨e, lam, G, hsd, he0, h0, hmono, htop, hfirst, hthird⟩



/-- The actual weak eigenbasis sees the differential generator of every H2 test.
This is the integration-by-parts bridge used for transported quasimodes. -/
theorem weak_eigen_coefficient_EX009 {d : ℕ} {w : Torus d → ℝ}
    {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData d w b c C)
    {e : HilbertBasis ℕ ℝ (Hw d w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus d → Tangent d} (hsd : SpectralData w e lam G)
    (f Af : Hw d w) (F : Torus d → Tangent d)
    (H : Fin d → Fin d → Torus d → ℝ)
    (hH : IsWeakHessian (f : Torus d → ℝ) F H)
    (hAf : (Af : Torus d → ℝ) =ᵐ[haar d]
      fun x => -(∑ i, H i i x + ⟪b x, F x⟫_ℝ)) (j : ℕ) :
    lam j * ⟪e j, f⟫_ℝ = ⟪e j, Af⟫_ℝ := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C :=
    Filter.Eventually.of_forall hwd.bound
  calc
    lam j * ⟪e j, f⟫_ℝ = weightedForm w (G j) F :=
      (hsd.eig j f F hH.grad).symm
    _ = ∫ x, ⟪F x, G j x⟫_ℝ * w x ∂haar d := by
      unfold weightedForm
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change ⟪G j x, F x⟫_ℝ * w x = ⟪F x, G j x⟫_ℝ * w x
        rw [real_inner_comm]
    _ = -∫ x, (∑ i, H i i x + ⟪b x, F x⟫_ℝ) *
        (e j : Torus d → ℝ) x * w x ∂haar d :=
      DGPS.Lipschitz.WeightedGenerator.forward_identity hwd hH (hsd.grad j)
    _ = ⟪e j, Af⟫_ℝ := by
      rw [inner_Lp_wMeasure hwd.meas hwd.pos hwb, ← integral_neg]
      apply integral_congr_ae
      filter_upwards [hAf] with x hx
      rw [hx]
      simp only [RCLike.inner_apply, conj_trivial]
      ring

theorem weak_residual_coefficient_EX009 {d : ℕ} {w : Torus d → ℝ}
    {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData d w b c C)
    {e : HilbertBasis ℕ ℝ (Hw d w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus d → Tangent d} (hsd : SpectralData w e lam G)
    (f Af : Hw d w) (F : Torus d → Tangent d)
    (H : Fin d → Fin d → Torus d → ℝ)
    (hH : IsWeakHessian (f : Torus d → ℝ) F H)
    (hAf : (Af : Torus d → ℝ) =ᵐ[haar d]
      fun x => -(∑ i, H i i x + ⟪b x, F x⟫_ℝ)) (mu : ℝ) (j : ℕ) :
    (lam j - mu) * ⟪e j, f⟫_ℝ = ⟪e j, Af - mu • f⟫_ℝ := by
  rw [inner_sub_right, inner_smul_right,
    ← weak_eigen_coefficient_EX009 hwd hsd f Af F H hH hAf j]
  ring



section ResidualProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal projection onto the two canonical first positive spectral indices. -/
noncomputable def pairProjection_EX009 (e : HilbertBasis ℕ ℝ E) (f : E) : E :=
  ⟪e 1, f⟫_ℝ • e 1 + ⟪e 2, f⟫_ℝ • e 2

theorem hasSum_inner_sq_EX009 (e : HilbertBasis ℕ ℝ E) (f : E) :
    HasSum (fun j => ⟪e j, f⟫_ℝ ^ 2) (‖f‖ ^ 2) := by
  have he := e.hasSum_inner_mul_inner f f
  rw [real_inner_self_eq_norm_sq] at he
  convert he using 1
  ext j
  rw [real_inner_comm f (e j), sq]

/-- Parseval turns a residual coefficient identity and a gap outside indices 1,2
into a quantitative bound on the missing spectral projection.  No simplicity of
the two cluster eigenvalues is assumed. -/
theorem spectral_projection_error_EX009 (e : HilbertBasis ℕ ℝ E)
    (lam : ℕ → ℝ) (mu delta : ℝ) (hdelta : 0 ≤ delta)
    (hgap : ∀ j, j ≠ 1 → j ≠ 2 → delta ≤ |lam j - mu|)
    (f r : E)
    (hres : ∀ j, (lam j - mu) * ⟪e j, f⟫_ℝ = ⟪e j, r⟫_ℝ) :
    delta ^ 2 * ‖f - pairProjection_EX009 e f‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have hinner := orthonormal_iff_ite.mp e.orthonormal
  have hterm : ∀ j,
      delta ^ 2 * ⟪e j, f - pairProjection_EX009 e f⟫_ℝ ^ 2 ≤
        ⟪e j, r⟫_ℝ ^ 2 := by
    intro j
    by_cases h1 : j = 1
    · subst j
      have hz : ⟪e 1, f - pairProjection_EX009 e f⟫_ℝ = 0 := by
        simp [pairProjection_EX009, inner_sub_right, inner_add_right,
          inner_smul_right, hinner, e.orthonormal.norm_eq_one]
      rw [hz]
      simpa using sq_nonneg ⟪e 1, r⟫_ℝ
    by_cases h2 : j = 2
    · subst j
      have hz : ⟪e 2, f - pairProjection_EX009 e f⟫_ℝ = 0 := by
        simp [pairProjection_EX009, inner_sub_right, inner_add_right,
          inner_smul_right, hinner, e.orthonormal.norm_eq_one]
      rw [hz]
      simpa using sq_nonneg ⟪e 2, r⟫_ℝ
    have hp : ⟪e j, pairProjection_EX009 e f⟫_ℝ = 0 := by
      simp [pairProjection_EX009, inner_add_right, inner_smul_right, hinner, h1, h2]
    rw [inner_sub_right, hp, sub_zero, ← hres j, mul_pow]
    have hm := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hdelta (hgap j h1 h2) 2) (sq_nonneg ⟪e j, f⟫_ℝ)
    simpa only [sq_abs] using hm
  exact hasSum_le hterm
    ((hasSum_inner_sq_EX009 e (f - pairProjection_EX009 e f)).mul_left (delta ^ 2))
    (hasSum_inner_sq_EX009 e r)

end ResidualProjection



/-- First two coefficients of the angular conjugated potential. -/
noncomputable def firstPotential_EX009 (A B x : ℝ) : ℝ :=
  -(A * Real.cos x + B * Real.sin x) / 2

noncomputable def secondPotential_EX009 (A B C D x : ℝ) : ℝ :=
  -2 * (C * Real.cos (2 * x) + D * Real.sin (2 * x)) +
    (-A * Real.sin x + B * Real.cos x) ^ 2 / 4

noncomputable def firstCorrectorCos_EX009 (A B x : ℝ) : ℝ :=
  -A / 4 + (A * Real.cos (2 * x) + B * Real.sin (2 * x)) / 12

noncomputable def firstCorrectorSin_EX009 (A B x : ℝ) : ℝ :=
  -B / 4 + (A * Real.sin (2 * x) - B * Real.cos (2 * x)) / 12

noncomputable def secondCorrectorCos_EX009 (A B C D x : ℝ) : ℝ :=
  ((A ^ 2 - B ^ 2) / 96 + C / 8) * Real.cos (3 * x) +
    (A * B / 48 + D / 8) * Real.sin (3 * x)

noncomputable def secondCorrectorSin_EX009 (A B C D x : ℝ) : ℝ :=
  -(A * B / 48 + D / 8) * Real.cos (3 * x) +
    ((A ^ 2 - B ^ 2) / 96 + C / 8) * Real.sin (3 * x)

/-- The order-h off-cluster equation for the cosine column. -/
theorem first_cancellation_cos_EX009 (A B x : ℝ) :
    (A * Real.cos (2 * x) + B * Real.sin (2 * x)) / 3 -
      firstCorrectorCos_EX009 A B x +
      firstPotential_EX009 A B x * Real.cos x = 0 := by
  simp only [firstCorrectorCos_EX009, firstPotential_EX009,
    Real.cos_two_mul, Real.sin_two_mul]
  ring

theorem first_cancellation_sin_EX009 (A B x : ℝ) :
    (A * Real.sin (2 * x) - B * Real.cos (2 * x)) / 3 -
      firstCorrectorSin_EX009 A B x +
      firstPotential_EX009 A B x * Real.sin x = 0 := by
  simp only [firstCorrectorSin_EX009, firstPotential_EX009,
    Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (-B / 2) * Real.sin_sq_add_cos_sq x

/-- The full order-h² cosine equation, including its complementary frequency3
corrector and the actual two first-harmonic matrix coefficients. -/
theorem second_cancellation_cos_EX009 (A B C D x : ℝ) :
    8 * secondCorrectorCos_EX009 A B C D x +
      firstPotential_EX009 A B x * firstCorrectorCos_EX009 A B x +
      secondPotential_EX009 A B C D x * Real.cos x -
      ((A ^ 2 + B ^ 2) / 6 - C) * Real.cos x + D * Real.sin x = 0 := by
  unfold secondCorrectorCos_EX009 firstPotential_EX009 firstCorrectorCos_EX009
    secondPotential_EX009
  rw [show 3 * x = 2 * x + x by ring, Real.cos_add, Real.sin_add]
  simp only [Real.cos_two_mul, Real.sin_two_mul]
  linear_combination
    (Real.cos x * (A ^ 2 + B ^ 2 - 24 * C) / 12) * Real.sin_sq_add_cos_sq x

theorem second_cancellation_sin_EX009 (A B C D x : ℝ) :
    8 * secondCorrectorSin_EX009 A B C D x +
      firstPotential_EX009 A B x * firstCorrectorSin_EX009 A B x +
      secondPotential_EX009 A B C D x * Real.sin x + D * Real.cos x -
      ((A ^ 2 + B ^ 2) / 6 + C) * Real.sin x = 0 := by
  unfold secondCorrectorSin_EX009 firstPotential_EX009 firstCorrectorSin_EX009
    secondPotential_EX009
  rw [show 3 * x = 2 * x + x by ring, Real.cos_add, Real.sin_add]
  simp only [Real.cos_two_mul, Real.sin_two_mul]
  linear_combination
    ((A ^ 2 * Real.sin x - A * B * Real.cos x - 8 * D * Real.cos x) / 4) *
      Real.sin_sq_add_cos_sq x



/-- Every smooth periodic test has its classical second derivatives in the full
weak H2 domain used by the canonical generator. -/
theorem smooth_weak_hessian_EX009 {d : ℕ} {f : Torus d → ℝ}
    (hf : IsSmoothPeriodic f) :
    IsWeakHessian f (smoothGrad f) (fun i j => coordPartial i (coordPartial j f)) where
  grad := hf.isWeakGradient
  memLp_hess i j :=
    ((hf.isSmoothPeriodic_coordPartial j).memLp_top_coordPartial i).mono_exponent le_top
  ibp i j phi hphi := by
    simpa only [smoothGrad_apply] using
      integral_mul_coordPartial_of_smooth (hf.isSmoothPeriodic_coordPartial j) hphi i

/-- Exact density normalization in the inverse ground-state transport. -/
theorem inverse_sqrt_pair_EX009 {w : ℝ} (hw : 0 < w) (q r : ℝ) :
    (q / Real.sqrt w) * (r / Real.sqrt w) * w = q * r := by
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt hw.le, div_mul_cancel₀ _ hw.ne']

/-- The actual inverse square root of the probability density gives an isometry;
no zeroth Fourier coefficient or normalizing scalar is discarded. -/
theorem inverse_ground_inner_EX009 {d : ℕ} {w : Torus d → ℝ} {c C : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (f g : Hw d w) (q r : Torus d → ℝ)
    (hf : (f : Torus d → ℝ) =ᵐ[haar d] fun x => q x / Real.sqrt (w x))
    (hg : (g : Torus d → ℝ) =ᵐ[haar d] fun x => r x / Real.sqrt (w x)) :
    ⟪f, g⟫_ℝ = ∫ x, q x * r x ∂haar d := by
  rw [inner_Lp_wMeasure hw hc hwb]
  apply integral_congr_ae
  filter_upwards [hf, hg, hwb] with x hfx hgx hx
  rw [hfx, hgx]
  simp only [RCLike.inner_apply, conj_trivial]
  convert inverse_sqrt_pair_EX009 (hc.trans_le hx.1) (q x) (r x) using 1
  ring



theorem outside_cluster_gap_EX009 (lam : ℕ → ℝ) (hzero : lam 0 = 0)
    (hmono : Monotone lam) (hthird : 3 * a0 < lam 3)
    (j : ℕ) (h1 : j ≠ 1) (h2 : j ≠ 2) :
    a0 ≤ |lam j - a0| := by
  by_cases h0 : j = 0
  · subst j
    simp [hzero, abs_of_pos DGPS.Circle.AngularNormalization.a0_pos]
  have hj : 3 ≤ j := by omega
  have hlarge : 3 * a0 < lam j := hthird.trans_le (hmono hj)
  rw [abs_of_nonneg (by linarith [DGPS.Circle.AngularNormalization.a0_pos] : 0 ≤ lam j - a0)]
  linarith [DGPS.Circle.AngularNormalization.a0_pos]

/-- Quantitative projection onto the genuine first pair of weak weighted
eigenfunctions, using the differential residual of an H2 test. -/
theorem weighted_projection_error_EX009 {d : ℕ} {w : Torus d → ℝ}
    {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData d w b c C)
    {e : HilbertBasis ℕ ℝ (Hw d w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus d → Tangent d} (hsd : SpectralData w e lam G)
    (hzero : lam 0 = 0) (hmono : Monotone lam) (hthird : 3 * a0 < lam 3)
    (f Af : Hw d w) (F : Torus d → Tangent d)
    (H : Fin d → Fin d → Torus d → ℝ)
    (hH : IsWeakHessian (f : Torus d → ℝ) F H)
    (hAf : (Af : Torus d → ℝ) =ᵐ[haar d]
      fun x => -(∑ i, H i i x + ⟪b x, F x⟫_ℝ)) :
    a0 ^ 2 * ‖f - pairProjection_EX009 e f‖ ^ 2 ≤ ‖Af - a0 • f‖ ^ 2 :=
  spectral_projection_error_EX009 e lam a0 a0 DGPS.Circle.AngularNormalization.a0_pos.le
    (outside_cluster_gap_EX009 lam hzero hmono hthird) f (Af - a0 • f)
    (weak_residual_coefficient_EX009 hwd hsd f Af F H hH hAf a0)



/-- The traceless part of the canonical second-order cluster quadratic form. -/
def clusterQuadratic_EX009 (C D u v : ℝ) : ℝ :=
  -C * u ^ 2 - 2 * D * u * v + C * v ^ 2

theorem cluster_quadratic_bounds_EX009 (C D u v : ℝ) :
    -Real.sqrt (C ^ 2 + D ^ 2) * (u ^ 2 + v ^ 2) ≤
      clusterQuadratic_EX009 C D u v ∧
    clusterQuadratic_EX009 C D u v ≤
      Real.sqrt (C ^ 2 + D ^ 2) * (u ^ 2 + v ^ 2) := by
  have hr : (Real.sqrt (C ^ 2 + D ^ 2)) ^ 2 = C ^ 2 + D ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hid :
      (clusterQuadratic_EX009 C D u v) ^ 2 +
        (D * (v ^ 2 - u ^ 2) + 2 * C * u * v) ^ 2 =
      (C ^ 2 + D ^ 2) * (u ^ 2 + v ^ 2) ^ 2 := by
    unfold clusterQuadratic_EX009
    ring
  have hs : (clusterQuadratic_EX009 C D u v) ^ 2 ≤
      (Real.sqrt (C ^ 2 + D ^ 2) * (u ^ 2 + v ^ 2)) ^ 2 := by
    rw [mul_pow, hr]
    nlinarith [sq_nonneg (D * (v ^ 2 - u ^ 2) + 2 * C * u * v)]
  have habs : |clusterQuadratic_EX009 C D u v| ≤
      Real.sqrt (C ^ 2 + D ^ 2) * (u ^ 2 + v ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  simpa only [neg_mul] using abs_le.mp habs

/-- Extremizers are used homogeneously.  Neither the spectral error constant
nor any smallness threshold divides by the cluster splitting. -/
theorem cluster_quadratic_extremizers_EX009 (C D : ℝ) :
    ∃ umin vmin umax vmax : ℝ,
      0 < umin ^ 2 + vmin ^ 2 ∧ 0 < umax ^ 2 + vmax ^ 2 ∧
      clusterQuadratic_EX009 C D umin vmin =
        -Real.sqrt (C ^ 2 + D ^ 2) * (umin ^ 2 + vmin ^ 2) ∧
      clusterQuadratic_EX009 C D umax vmax =
        Real.sqrt (C ^ 2 + D ^ 2) * (umax ^ 2 + vmax ^ 2) := by
  by_cases hD : D = 0
  · subst D
    by_cases hC : 0 ≤ C
    · refine ⟨1, 0, 0, 1, by norm_num, by norm_num, ?_, ?_⟩
      · simp [clusterQuadratic_EX009, Real.sqrt_sq_eq_abs, abs_of_nonneg hC]
      · simp [clusterQuadratic_EX009, Real.sqrt_sq_eq_abs, abs_of_nonneg hC]
    · have hC' : C ≤ 0 := (lt_of_not_ge hC).le
      refine ⟨0, 1, 1, 0, by norm_num, by norm_num, ?_, ?_⟩
      · simp [clusterQuadratic_EX009, Real.sqrt_sq_eq_abs, abs_of_nonpos hC']
      · simp [clusterQuadratic_EX009, Real.sqrt_sq_eq_abs, abs_of_nonpos hC']
  · let r := Real.sqrt (C ^ 2 + D ^ 2)
    have hr : r ^ 2 = C ^ 2 + D ^ 2 := Real.sq_sqrt (by positivity)
    refine ⟨D, r - C, D, -r - C, ?_, ?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_ne_zero hD, sq_nonneg (r - C)]
    · nlinarith [sq_pos_of_ne_zero hD, sq_nonneg (-r - C)]
    · change clusterQuadratic_EX009 C D D (r - C) = -r * (D ^ 2 + (r - C) ^ 2)
      unfold clusterQuadratic_EX009
      linear_combination (r - C) * hr
    · change clusterQuadratic_EX009 C D D (-r - C) = r * (D ^ 2 + (-r - C) ^ 2)
      unfold clusterQuadratic_EX009
      linear_combination (-r - C) * hr



noncomputable def realMode_EX009 (n A B x : ℝ) : ℝ :=
  A * Real.cos (n * x) + B * Real.sin (n * x)

theorem hasDerivAt_realMode_EX009 (n A B x : ℝ) :
    HasDerivAt (realMode_EX009 n A B)
      (realMode_EX009 n (n * B) (-n * A) x) x := by
  have ht : HasDerivAt (fun y : ℝ => n * y) n x := by
    simpa using (hasDerivAt_id x).const_mul n
  have hh := (((hasDerivAt_cos (n * x)).comp x ht).const_mul A).add
    (((hasDerivAt_sin (n * x)).comp x ht).const_mul B)
  convert hh using 1
  · ext y
    rfl
  · unfold realMode_EX009
    ring

theorem deriv_realMode_EX009 (n A B x : ℝ) :
    deriv (realMode_EX009 n A B) x =
      realMode_EX009 n (n * B) (-n * A) x :=
  (hasDerivAt_realMode_EX009 n A B x).deriv

theorem deriv2_realMode_EX009 (n A B x : ℝ) :
    deriv (deriv (realMode_EX009 n A B)) x = -n ^ 2 * realMode_EX009 n A B x := by
  rw [show deriv (realMode_EX009 n A B) = realMode_EX009 n (n * B) (-n * A) from
    funext (deriv_realMode_EX009 n A B), deriv_realMode_EX009]
  unfold realMode_EX009
  ring

theorem deriv2_add_EX009 {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    deriv (deriv (fun y => f y + g y)) x =
      deriv (deriv f) x + deriv (deriv g) x := by
  have hfun : deriv (fun y => f y + g y) = fun y => deriv f y + deriv g y :=
    funext fun y => deriv_fun_add ((hf.differentiable (by norm_num)) y)
      ((hg.differentiable (by norm_num)) y)
  rw [hfun]
  exact deriv_fun_add (hf.differentiable_deriv_two x) (hg.differentiable_deriv_two x)

theorem deriv2_const_mul_EX009 (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv (deriv (fun y => c * f y)) x = c * deriv (deriv f) x := by
  rw [deriv_const_mul_field', deriv_const_mul_field]

theorem deriv2_firstCorrectorCos_EX009 (A B x : ℝ) :
    deriv (deriv (firstCorrectorCos_EX009 A B)) x =
      -(A * Real.cos (2 * x) + B * Real.sin (2 * x)) / 3 := by
  have he : firstCorrectorCos_EX009 A B =
      fun y => realMode_EX009 2 (A / 12) (B / 12) y + (-A / 4) := by
    ext y
    unfold firstCorrectorCos_EX009 realMode_EX009
    ring
  rw [he]
  simp only [deriv_add_const']
  rw [deriv2_realMode_EX009]
  unfold realMode_EX009
  ring

theorem deriv2_firstCorrectorSin_EX009 (A B x : ℝ) :
    deriv (deriv (firstCorrectorSin_EX009 A B)) x =
      -(A * Real.sin (2 * x) - B * Real.cos (2 * x)) / 3 := by
  have he : firstCorrectorSin_EX009 A B =
      fun y => realMode_EX009 2 (-B / 12) (A / 12) y + (-B / 4) := by
    ext y
    unfold firstCorrectorSin_EX009 realMode_EX009
    ring
  rw [he]
  simp only [deriv_add_const']
  rw [deriv2_realMode_EX009]
  unfold realMode_EX009
  ring

theorem deriv2_secondCorrectorCos_EX009 (A B C D x : ℝ) :
    deriv (deriv (secondCorrectorCos_EX009 A B C D)) x =
      -9 * secondCorrectorCos_EX009 A B C D x := by
  change deriv (deriv (realMode_EX009 3
    ((A ^ 2 - B ^ 2) / 96 + C / 8) (A * B / 48 + D / 8))) x = _
  rw [deriv2_realMode_EX009]
  norm_num [realMode_EX009, secondCorrectorCos_EX009]

theorem deriv2_secondCorrectorSin_EX009 (A B C D x : ℝ) :
    deriv (deriv (secondCorrectorSin_EX009 A B C D)) x =
      -9 * secondCorrectorSin_EX009 A B C D x := by
  change deriv (deriv (realMode_EX009 3
    (-(A * B / 48 + D / 8)) ((A ^ 2 - B ^ 2) / 96 + C / 8))) x = _
  rw [deriv2_realMode_EX009]
  norm_num [realMode_EX009, secondCorrectorSin_EX009]

noncomputable def quasiCosLift_EX009 (h A B C D x : ℝ) : ℝ :=
  Real.cos x + h * firstCorrectorCos_EX009 A B x +
    h ^ 2 * secondCorrectorCos_EX009 A B C D x

noncomputable def quasiSinLift_EX009 (h A B C D x : ℝ) : ℝ :=
  Real.sin x + h * firstCorrectorSin_EX009 A B x +
    h ^ 2 * secondCorrectorSin_EX009 A B C D x

theorem deriv2_quasiCos_EX009 (h A B C D x : ℝ) :
    deriv (deriv (quasiCosLift_EX009 h A B C D)) x =
      -Real.cos x - h * (A * Real.cos (2 * x) + B * Real.sin (2 * x)) / 3 -
        9 * h ^ 2 * secondCorrectorCos_EX009 A B C D x := by
  have hf : ContDiff ℝ 2 (fun y => Real.cos y + h * firstCorrectorCos_EX009 A B y) := by
    unfold firstCorrectorCos_EX009
    fun_prop
  have hg : ContDiff ℝ 2 (fun y => h ^ 2 * secondCorrectorCos_EX009 A B C D y) := by
    unfold secondCorrectorCos_EX009
    fun_prop
  unfold quasiCosLift_EX009
  rw [deriv2_add_EX009 hf hg,
    deriv2_add_EX009 (by fun_prop : ContDiff ℝ 2 Real.cos)
      (by unfold firstCorrectorCos_EX009; fun_prop),
    deriv2_const_mul_EX009, deriv2_const_mul_EX009,
    deriv2_firstCorrectorCos_EX009, deriv2_secondCorrectorCos_EX009]
  have he : deriv (deriv Real.cos) x = -Real.cos x := by
    simp
  rw [he]
  ring

theorem deriv2_quasiSin_EX009 (h A B C D x : ℝ) :
    deriv (deriv (quasiSinLift_EX009 h A B C D)) x =
      -Real.sin x - h * (A * Real.sin (2 * x) - B * Real.cos (2 * x)) / 3 -
        9 * h ^ 2 * secondCorrectorSin_EX009 A B C D x := by
  have hf : ContDiff ℝ 2 (fun y => Real.sin y + h * firstCorrectorSin_EX009 A B y) := by
    unfold firstCorrectorSin_EX009
    fun_prop
  have hg : ContDiff ℝ 2 (fun y => h ^ 2 * secondCorrectorSin_EX009 A B C D y) := by
    unfold secondCorrectorSin_EX009
    fun_prop
  unfold quasiSinLift_EX009
  rw [deriv2_add_EX009 hf hg,
    deriv2_add_EX009 (by fun_prop : ContDiff ℝ 2 Real.sin)
      (by unfold firstCorrectorSin_EX009; fun_prop),
    deriv2_const_mul_EX009, deriv2_const_mul_EX009,
    deriv2_firstCorrectorSin_EX009, deriv2_secondCorrectorSin_EX009]
  have he : deriv (deriv Real.sin) x = -Real.sin x := by
    simp
  rw [he]
  ring

theorem quasi_cos_residual_EX009 (ell R : ℝ → ℝ) (h A B C D : ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 ell x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x + h ^ 3 * R x)
    (x : ℝ) :
    schrodingerOperator_EX009 ell (quasiCosLift_EX009 h A B C D) x -
      ((1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 - C)) * quasiCosLift_EX009 h A B C D x -
        h ^ 2 * D * quasiSinLift_EX009 h A B C D x) =
      h ^ 3 * (R x * quasiCosLift_EX009 h A B C D x +
        firstPotential_EX009 A B x * secondCorrectorCos_EX009 A B C D x +
        secondPotential_EX009 A B C D x * firstCorrectorCos_EX009 A B x -
        ((A ^ 2 + B ^ 2) / 6 - C) * firstCorrectorCos_EX009 A B x +
        D * firstCorrectorSin_EX009 A B x) +
      h ^ 4 * (secondPotential_EX009 A B C D x * secondCorrectorCos_EX009 A B C D x -
        ((A ^ 2 + B ^ 2) / 6 - C) * secondCorrectorCos_EX009 A B C D x +
        D * secondCorrectorSin_EX009 A B C D x) := by
  have hfirst := first_cancellation_cos_EX009 A B x
  have hsecond := second_cancellation_cos_EX009 A B C D x
  unfold schrodingerOperator_EX009
  rw [deriv2_quasiCos_EX009, hpot]
  unfold quasiCosLift_EX009 quasiSinLift_EX009
  linear_combination h * hfirst + h ^ 2 * hsecond

theorem quasi_sin_residual_EX009 (ell R : ℝ → ℝ) (h A B C D : ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 ell x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x + h ^ 3 * R x)
    (x : ℝ) :
    schrodingerOperator_EX009 ell (quasiSinLift_EX009 h A B C D) x -
      (-h ^ 2 * D * quasiCosLift_EX009 h A B C D x +
        (1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 + C)) * quasiSinLift_EX009 h A B C D x) =
      h ^ 3 * (R x * quasiSinLift_EX009 h A B C D x +
        firstPotential_EX009 A B x * secondCorrectorSin_EX009 A B C D x +
        secondPotential_EX009 A B C D x * firstCorrectorSin_EX009 A B x +
        D * firstCorrectorCos_EX009 A B x -
        ((A ^ 2 + B ^ 2) / 6 + C) * firstCorrectorSin_EX009 A B x) +
      h ^ 4 * (secondPotential_EX009 A B C D x * secondCorrectorSin_EX009 A B C D x +
        D * secondCorrectorCos_EX009 A B C D x -
        ((A ^ 2 + B ^ 2) / 6 + C) * secondCorrectorSin_EX009 A B C D x) := by
  have hfirst := first_cancellation_sin_EX009 A B x
  have hsecond := second_cancellation_sin_EX009 A B C D x
  unfold schrodingerOperator_EX009
  rw [deriv2_quasiSin_EX009, hpot]
  unfold quasiCosLift_EX009 quasiSinLift_EX009
  linear_combination h * hfirst + h ^ 2 * hsecond



noncomputable def inverseGround_EX009 (ell q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-ell x / 2) * q x

theorem ground_inverse_EX009 (ell q : ℝ → ℝ) :
    groundTransform_EX009 ell (inverseGround_EX009 ell q) = q := by
  ext x
  unfold groundTransform_EX009 inverseGround_EX009
  rw [← mul_assoc, ← Real.exp_add]
  rw [show ell x / 2 + -ell x / 2 = 0 by ring, Real.exp_zero, one_mul]

theorem negative_generator_inverse_EX009 {ell q : ℝ → ℝ}
    (hell : ContDiff ℝ 2 ell) (hq : ContDiff ℝ 2 q) (x : ℝ) :
    negativeGenerator_EX009 ell (inverseGround_EX009 ell q) x =
      Real.exp (-ell x / 2) * schrodingerOperator_EX009 ell q x := by
  have hf : ContDiff ℝ 2 (inverseGround_EX009 ell q) := by
    unfold inverseGround_EX009
    fun_prop
  have hc := differential_conjugation_EX009
    (hell.differentiable (by norm_num)) hell.differentiable_deriv_two
    (hf.differentiable (by norm_num)) hf.differentiable_deriv_two x
  rw [ground_inverse_EX009] at hc
  have he : Real.exp (-ell x / 2) * Real.exp (ell x / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -ell x / 2 + ell x / 2 = 0 by ring, Real.exp_zero]
  calc
    negativeGenerator_EX009 ell (inverseGround_EX009 ell q) x =
        Real.exp (-ell x / 2) * (Real.exp (ell x / 2) *
          negativeGenerator_EX009 ell (inverseGround_EX009 ell q) x) := by
      rw [← mul_assoc, he, one_mul]
    _ = _ := by rw [← hc]

theorem negativeGenerator_const_mul_EX009 (c : ℝ) (ell f : ℝ → ℝ) (x : ℝ) :
    negativeGenerator_EX009 ell (fun y => c * f y) x =
      c * negativeGenerator_EX009 ell f x := by
  unfold negativeGenerator_EX009
  rw [deriv2_const_mul_EX009, deriv_const_mul_field]
  ring

theorem normalized_ground_pair_EX009 {Z : ℝ} (hZ : 0 < Z) (ell q r : ℝ) :
    (Real.sqrt Z * Real.exp (-ell / 2) * q) *
      (Real.sqrt Z * Real.exp (-ell / 2) * r) * (Real.exp ell / Z) = q * r := by
  have he : Real.exp (-ell / 2) * Real.exp (-ell / 2) * Real.exp ell = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    rw [show -ell / 2 + -ell / 2 + ell = 0 by ring, Real.exp_zero]
  calc
    (Real.sqrt Z * Real.exp (-ell / 2) * q) *
        (Real.sqrt Z * Real.exp (-ell / 2) * r) * (Real.exp ell / Z) =
        ((Real.sqrt Z) ^ 2 / Z) *
          (Real.exp (-ell / 2) * Real.exp (-ell / 2) * Real.exp ell) * (q * r) := by ring
    _ = q * r := by rw [Real.sq_sqrt hZ.le, div_self hZ.ne', he]; ring

theorem physical_first_derivative_EX009 (psi : AngCircle → ℝ)
    (hpsi : IsSmoothAngular psi) (t : ℝ) :
    coordPartial 0 (psi ∘ angEquiv) (torusLift (fun _ : Fin 1 => t)) =
      (2 * π) * deriv (fun s : ℝ => psi (s : AngCircle)) (2 * π * t) := by
  have hphys := (isSmoothPeriodic_comp_iff psi).2 hpsi
  have hleft := DGPS.hasDerivAt_smooth_one hphys t
  have hfun : (fun s : ℝ => (psi ∘ angEquiv) (torusLift (fun _ : Fin 1 => s))) =
      (fun s : ℝ => psi ((2 * π * s : ℝ) : AngCircle)) := by
    ext s
    exact comp_angEquiv_liftT psi (fun _ : Fin 1 => s)
  rw [hfun] at hleft
  have ht : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hright :=
    (((hpsi.differentiable (by simp)) (2 * π * t)).hasDerivAt).comp t ht
  have he := hleft.unique hright
  calc
    coordPartial 0 (psi ∘ angEquiv) (torusLift (fun _ : Fin 1 => t)) =
        deriv (fun s : ℝ => psi (s : AngCircle)) (2 * π * t) * (2 * π) := he
    _ = _ := by ring

theorem physical_second_derivative_EX009 (psi : AngCircle → ℝ)
    (hpsi : IsSmoothAngular psi) (t : ℝ) :
    coordPartial 0 (coordPartial 0 (psi ∘ angEquiv))
        (torusLift (fun _ : Fin 1 => t)) =
      a0 * deriv (deriv (fun s : ℝ => psi (s : AngCircle))) (2 * π * t) := by
  have hphys := (isSmoothPeriodic_comp_iff psi).2 hpsi
  have hleft := DGPS.hasDerivAt_smooth_one (hphys.isSmoothPeriodic_coordPartial 0) t
  have hfun :
      (fun s : ℝ => coordPartial 0 (psi ∘ angEquiv) (torusLift (fun _ : Fin 1 => s))) =
      (fun s : ℝ => 2 * π * deriv (fun y : ℝ => psi (y : AngCircle)) (2 * π * s)) :=
    funext (physical_first_derivative_EX009 psi hpsi)
  rw [hfun] at hleft
  have ht : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hpsi2 : ContDiff ℝ 2 (fun s : ℝ => psi (s : AngCircle)) := hpsi.of_le (by simp)
  have hright := ((hpsi2.differentiable_deriv_two (2 * π * t)).hasDerivAt.comp t ht).const_mul
    (2 * π)
  have he := hleft.unique hright
  unfold DGPS.Circle.AngularNormalization.a0
  calc
    coordPartial 0 (coordPartial 0 (psi ∘ angEquiv)) (torusLift (fun _ : Fin 1 => t)) =
        (2 * π) * (deriv (deriv (fun s : ℝ => psi (s : AngCircle))) (2 * π * t) *
          (2 * π)) := he
    _ = _ := by ring



/-- Uniform bounds are taken on a finite coefficient box and independent bounded
remainder values.  This does not impose any continuity in h on a remainder family. -/
theorem compact_polynomial_bound_EX009
    (F : ((Fin 4 → ℝ) × ℝ × AngCircle × ℝ) → ℝ) (hF : Continuous F) (M R : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (p : Fin 4 → ℝ) (h : ℝ) (theta : AngCircle) (r : ℝ),
      (∀ i, |p i| ≤ M) → |h| ≤ 1 → |r| ≤ R → |F (p, h, theta, r)| ≤ K := by
  let S : Set ((Fin 4 → ℝ) × ℝ × AngCircle × ℝ) :=
    (Set.pi Set.univ (fun _ => Set.Icc (-M) M)) ×ˢ
      (Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ ×ˢ Set.Icc (-R) R))
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_Icc.prod (isCompact_univ.prod isCompact_Icc))
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p h theta r hp hh hr
  have hx : (p, h, theta, r) ∈ S := by
    refine ⟨?_, abs_le.mp hh, Set.mem_univ theta, abs_le.mp hr⟩
    intro i _
    exact abs_le.mp (hp i)
  have hk := hK (p, h, theta, r) hx
  have hk' : |F (p, h, theta, r)| ≤ K := by
    simpa only [Real.norm_eq_abs] using hk
  exact hk'.trans (le_max_left _ _)

theorem perturbed_potential_jet_EX009 (h A B C D : ℝ) (psi : ℝ → ℝ)
    (hpsi : ContDiff ℝ 2 psi) (x : ℝ) :
    schrodingerPotential_EX009
      (fun y => harmonicLog_EX009 h A B C D y + h ^ 3 * psi y) x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x +
      h ^ 3 * potentialRemainder_EX009 h
        (-A * Real.sin x + B * Real.cos x)
        (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x))
        (deriv psi x) (deriv (deriv psi) x) := by
  have hlog : ContDiff ℝ 2 (harmonicLog_EX009 h A B C D) := by
    unfold harmonicLog_EX009
    fun_prop
  have hconst : ContDiff ℝ 2 (fun y => h ^ 3 * psi y) := by fun_prop
  unfold schrodingerPotential_EX009
  rw [deriv_fun_add ((hlog.differentiable (by norm_num)) x)
      ((hconst.differentiable (by norm_num)) x),
    deriv_const_mul_field, deriv_harmonicLog_EX009,
    deriv2_add_EX009 hlog hconst, deriv2_const_mul_EX009,
    deriv2_harmonicLog_EX009]
  rw [potential_jet_expansion_EX009]
  unfold firstPotential_EX009 secondPotential_EX009
  ring



def twoNormSq_EX009 (y : Fin 2 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- Elementary projected-Gram/Rayleigh comparison.  It applies also when the
two model coefficients coincide, and uses no inverse splitting factor. -/
theorem finite_rayleigh_comparison_EX009
    (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) (Q : (Fin 2 → ℝ) → ℝ)
    (lam1 lam2 a t eps eta Km mlo mhi : ℝ)
    (ht : 0 ≤ t) (heps : 0 ≤ eps) (heta : 0 ≤ eta) (hKm : 0 ≤ Km)
    (hsort : lam1 ≤ lam2)
    (hlo : |mlo| ≤ Km) (hhi : |mhi| ≤ Km)
    (hQ : ∀ y, mlo * twoNormSq_EX009 y ≤ Q y ∧ Q y ≤ mhi * twoNormSq_EX009 y)
    (vlo vhi : Fin 2 → ℝ)
    (hvlo : 0 < twoNormSq_EX009 vlo) (hvhi : 0 < twoNormSq_EX009 vhi)
    (hQlo : Q vlo = mlo * twoNormSq_EX009 vlo)
    (hQhi : Q vhi = mhi * twoNormSq_EX009 vhi)
    (hGramLow : ∀ y, twoNormSq_EX009 y / 4 ≤ twoNormSq_EX009 (T y))
    (hGram : ∀ y,
      |twoNormSq_EX009 (T y) - twoNormSq_EX009 y / 2| ≤ eta * twoNormSq_EX009 y)
    (hEnergy : ∀ y,
      |lam1 * (T y) 0 ^ 2 + lam2 * (T y) 1 ^ 2 -
        a * twoNormSq_EX009 (T y) - t * Q y / 2| ≤ eps * twoNormSq_EX009 y) :
    |lam1 - (a + t * mlo)| ≤ 4 * (eps + t * Km * eta) ∧
      |lam2 - (a + t * mhi)| ≤ 4 * (eps + t * Km * eta) := by
  let N (y : Fin 2 → ℝ) := twoNormSq_EX009 (T y)
  let E (y : Fin 2 → ℝ) := lam1 * (T y) 0 ^ 2 + lam2 * (T y) 1 ^ 2
  let S := eps + t * Km * eta
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hmuGram (mu : ℝ) (hmu : |mu| ≤ Km) (y : Fin 2 → ℝ) :
      |mu * (N y - twoNormSq_EX009 y / 2)| ≤
        Km * (eta * twoNormSq_EX009 y) := by
    rw [abs_mul]
    exact mul_le_mul hmu (hGram y) (abs_nonneg _) hKm
  have hlower (mu : ℝ) (hmu : |mu| ≤ Km) (y : Fin 2 → ℝ)
      (hq : mu * twoNormSq_EX009 y ≤ Q y) :
      (a + t * mu - 4 * S) * N y ≤ E y := by
    have herr := (abs_le.mp (hEnergy y)).1
    have hq' := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ t / 2)
    have hmu' := mul_le_mul_of_nonneg_left (abs_le.mp (hmuGram mu hmu y)).2 ht
    have hn : twoNormSq_EX009 y ≤ 4 * N y := by have := hGramLow y; dsimp [N]; linarith
    have hn' := mul_le_mul_of_nonneg_left hn hS
    dsimp [N, E, S] at *
    nlinarith
  have hupper (mu : ℝ) (hmu : |mu| ≤ Km) (y : Fin 2 → ℝ)
      (hq : Q y ≤ mu * twoNormSq_EX009 y) :
      E y ≤ (a + t * mu + 4 * S) * N y := by
    have herr := (abs_le.mp (hEnergy y)).2
    have hq' := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ t / 2)
    have hmu' := mul_le_mul_of_nonneg_left (abs_le.mp (hmuGram mu hmu y)).1 ht
    have hn : twoNormSq_EX009 y ≤ 4 * N y := by have := hGramLow y; dsimp [N]; linarith
    have hn' := mul_le_mul_of_nonneg_left hn hS
    dsimp [N, E, S] at *
    nlinarith
  have hker (y : Fin 2 → ℝ) (hy : T y = 0) : y = 0 := by
    have hh := hGramLow y
    rw [hy] at hh
    have hy0 : y 0 = 0 := by
      dsimp [twoNormSq_EX009] at hh
      nlinarith [sq_nonneg (y 1)]
    have hy1 : y 1 = 0 := by
      dsimp [twoNormSq_EX009] at hh
      nlinarith [sq_nonneg (y 0)]
    ext i
    fin_cases i
    · exact hy0
    · exact hy1
  have hinj : Function.Injective T := by
    intro y z hyz
    have he : T (y - z) = 0 := by rw [map_sub, hyz, sub_self]
    exact sub_eq_zero.mp (hker (y - z) he)
  have hsurj := LinearMap.surjective_of_injective hinj
  obtain ⟨y0, hy0⟩ := hsurj (Pi.single (0 : Fin 2) (1 : ℝ))
  obtain ⟨y1, hy1⟩ := hsurj (Pi.single (1 : Fin 2) (1 : ℝ))
  have hLam1Low : a + t * mlo - 4 * S ≤ lam1 := by
    simpa [N, E, twoNormSq_EX009, hy0] using hlower mlo hlo y0 (hQ y0).1
  have hLam2High : lam2 ≤ a + t * mhi + 4 * S := by
    simpa [N, E, twoNormSq_EX009, hy1] using hupper mhi hhi y1 (hQ y1).2
  have hnlo : 0 < N vlo := (div_pos hvlo (by norm_num : (0 : ℝ) < 4)).trans_le (hGramLow vlo)
  have hnhi : 0 < N vhi := (div_pos hvhi (by norm_num : (0 : ℝ) < 4)).trans_le (hGramLow vhi)
  have hRayLo : lam1 * N vlo ≤ E vlo := by
    dsimp [N, E, twoNormSq_EX009]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsort) (sq_nonneg ((T vlo) 1))]
  have hRayHi : E vhi ≤ lam2 * N vhi := by
    dsimp [N, E, twoNormSq_EX009]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsort) (sq_nonneg ((T vhi) 0))]
  have hLam1High : lam1 ≤ a + t * mlo + 4 * S := by
    have he := hupper mlo hlo vlo hQlo.le
    by_contra hh
    have hpos := mul_pos (by linarith : 0 < lam1 - (a + t * mlo + 4 * S)) hnlo
    nlinarith
  have hLam2Low : a + t * mhi - 4 * S ≤ lam2 := by
    have he := hlower mhi hhi vhi hQhi.ge
    by_contra hh
    have hpos := mul_pos (by linarith : 0 < a + t * mhi - 4 * S - lam2) hnhi
    nlinarith
  change |lam1 - (a + t * mlo)| ≤ 4 * S ∧ |lam2 - (a + t * mhi)| ≤ 4 * S
  constructor
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> linarith



section ProjectionAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pairProjection_inner_left_EX009 (e : HilbertBasis ℕ ℝ E) (f g : E) :
    ⟪pairProjection_EX009 e f, g⟫_ℝ =
      ⟪e 1, f⟫_ℝ * ⟪e 1, g⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, g⟫_ℝ := by
  simp only [pairProjection_EX009, inner_add_left, real_inner_smul_left]

theorem pairProjection_inner_right_EX009 (e : HilbertBasis ℕ ℝ E) (f g : E) :
    ⟪f, pairProjection_EX009 e g⟫_ℝ =
      ⟪e 1, f⟫_ℝ * ⟪e 1, g⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, g⟫_ℝ := by
  calc
    ⟪f, pairProjection_EX009 e g⟫_ℝ = ⟪pairProjection_EX009 e g, f⟫_ℝ :=
      real_inner_comm _ _
    _ = _ := by rw [pairProjection_inner_left_EX009]; ring

theorem pairProjection_inner_EX009 (e : HilbertBasis ℕ ℝ E) (f g : E) :
    ⟪pairProjection_EX009 e f, pairProjection_EX009 e g⟫_ℝ =
      ⟪e 1, f⟫_ℝ * ⟪e 1, g⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, g⟫_ℝ := by
  have hinner := orthonormal_iff_ite.mp e.orthonormal
  simp only [pairProjection_EX009, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, hinner]
  norm_num
  ring

theorem pairProjection_pythagoras_EX009 (e : HilbertBasis ℕ ℝ E) (f : E) :
    ‖f‖ ^ 2 = ‖pairProjection_EX009 e f‖ ^ 2 +
      ‖f - pairProjection_EX009 e f‖ ^ 2 := by
  have hp : ‖pairProjection_EX009 e f‖ ^ 2 =
      ⟪e 1, f⟫_ℝ * ⟪e 1, f⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, f⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    exact pairProjection_inner_EX009 e f f
  have hr :
      ‖f - pairProjection_EX009 e f‖ ^ 2 = ‖f‖ ^ 2 -
        (⟪e 1, f⟫_ℝ * ⟪e 1, f⟫_ℝ + ⟪e 2, f⟫_ℝ * ⟪e 2, f⟫_ℝ) := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      pairProjection_inner_EX009, pairProjection_inner_left_EX009,
      pairProjection_inner_right_EX009, real_inner_self_eq_norm_sq]
    ring
  linarith

theorem pairProjection_norm_le_EX009 (e : HilbertBasis ℕ ℝ E) (f : E) :
    ‖pairProjection_EX009 e f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have he := pairProjection_pythagoras_EX009 e f
  nlinarith [sq_nonneg ‖f - pairProjection_EX009 e f‖]

theorem pairProjection_inner_error_EX009 (e : HilbertBasis ℕ ℝ E) (f g : E) :
    ⟪pairProjection_EX009 e f, pairProjection_EX009 e g⟫_ℝ =
      ⟪f, g⟫_ℝ - ⟪f - pairProjection_EX009 e f, g - pairProjection_EX009 e g⟫_ℝ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    pairProjection_inner_EX009, pairProjection_inner_left_EX009,
    pairProjection_inner_right_EX009]
  ring

end ProjectionAlgebra



noncomputable def physicalGenerator_EX009 (ell psi : AngCircle → ℝ) (x : Torus 1) : ℝ :=
  -(coordPartial 0 (coordPartial 0 (psi ∘ angEquiv)) x +
    coordPartial 0 (ell ∘ angEquiv) x * coordPartial 0 (psi ∘ angEquiv) x)

theorem physical_generator_trace_EX009 (ell psi : AngCircle → ℝ) :
    physicalGenerator_EX009 ell psi =
      fun x => -(∑ i : Fin 1, coordPartial i (coordPartial i (psi ∘ angEquiv)) x +
        ⟪smoothGrad (ell ∘ angEquiv) x, smoothGrad (psi ∘ angEquiv) x⟫_ℝ) := by
  ext x
  simp [physicalGenerator_EX009, PiLp.inner_apply, smoothGrad_apply, RCLike.inner_apply, mul_comm]

theorem physical_generator_formula_EX009 (ell psi : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (hpsi : IsSmoothAngular psi) (t : ℝ) :
    physicalGenerator_EX009 ell psi (torusLift (fun _ : Fin 1 => t)) =
      a0 * negativeGenerator_EX009 (fun s : ℝ => ell (s : AngCircle))
        (fun s : ℝ => psi (s : AngCircle)) (2 * π * t) := by
  unfold physicalGenerator_EX009
  rw [physical_second_derivative_EX009 psi hpsi,
    physical_first_derivative_EX009 ell hell, physical_first_derivative_EX009 psi hpsi]
  unfold DGPS.Circle.AngularNormalization.a0 negativeGenerator_EX009
  ring

theorem smooth_test_spectral_coefficients_EX009 {w : Torus 1 → ℝ} {c C : ℝ}
    (ell psi : AngCircle → ℝ) (hell : IsSmoothAngular ell) (hpsi : IsSmoothAngular psi)
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData 1 w (smoothGrad (ell ∘ angEquiv)) c C)
    {e : HilbertBasis ℕ ℝ (Hw 1 w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1} (hsd : SpectralData w e lam G) :
    ∃ f Af : Hw 1 w,
      ((f : Hw 1 w) : Torus 1 → ℝ) =ᵐ[haar 1] psi ∘ angEquiv ∧
      ((Af : Hw 1 w) : Torus 1 → ℝ) =ᵐ[haar 1] physicalGenerator_EX009 ell psi ∧
      ∀ j, lam j * ⟪e j, f⟫_ℝ = ⟪e j, Af⟫_ℝ := by
  have hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C :=
    Filter.Eventually.of_forall hwd.bound
  have hphys := (isSmoothPeriodic_comp_iff psi).2 hpsi
  have hellphys := (isSmoothPeriodic_comp_iff ell).2 hell
  have hgen : IsSmoothPeriodic (physicalGenerator_EX009 ell psi) := by
    have h2 := (hphys.isSmoothPeriodic_coordPartial 0).isSmoothPeriodic_coordPartial 0
    have hl1 := hellphys.isSmoothPeriodic_coordPartial 0
    have hp1 := hphys.isSmoothPeriodic_coordPartial 0
    unfold physicalGenerator_EX009
    exact (ContDiff.add h2 (ContDiff.mul hl1 hp1)).neg
  have hfH : MemLp (psi ∘ angEquiv) 2 (haar 1) := hphys.memLp_top.mono_exponent le_top
  have hAfH : MemLp (physicalGenerator_EX009 ell psi) 2 (haar 1) :=
    hgen.memLp_top.mono_exponent le_top
  have hfW := (memLp_wMeasure_iff hwd.pos hwb).mpr hfH
  have hAfW := (memLp_wMeasure_iff hwd.pos hwb).mpr hAfH
  let f : Hw 1 w := hfW.toLp (psi ∘ angEquiv)
  let Af : Hw 1 w := hAfW.toLp (physicalGenerator_EX009 ell psi)
  have hfAE : (f : Torus 1 → ℝ) =ᵐ[haar 1] psi ∘ angEquiv :=
    ae_eq_haar hwd.pos hwb hfW.coeFn_toLp
  have hAfAE : (Af : Torus 1 → ℝ) =ᵐ[haar 1] physicalGenerator_EX009 ell psi :=
    ae_eq_haar hwd.pos hwb hAfW.coeFn_toLp
  let H : Fin 1 → Fin 1 → Torus 1 → ℝ :=
    fun i j => coordPartial i (coordPartial j (psi ∘ angEquiv))
  have hH0 := smooth_weak_hessian_EX009 hphys
  have hH : IsWeakHessian (f : Torus 1 → ℝ) (smoothGrad (psi ∘ angEquiv)) H := {
    grad := hH0.grad.congr_ae hfAE.symm (Filter.EventuallyEq.refl _ _)
    memLp_hess := hH0.memLp_hess
    ibp := hH0.ibp
  }
  have hAf : (Af : Torus 1 → ℝ) =ᵐ[haar 1]
      fun x => -(∑ i, H i i x + ⟪smoothGrad (ell ∘ angEquiv) x,
        smoothGrad (psi ∘ angEquiv) x⟫_ℝ) :=
    hAfAE.trans (Filter.Eventually.of_forall fun x =>
      congrFun (physical_generator_trace_EX009 ell psi) x)
  exact ⟨f, Af, hfAE, hAfAE,
    weak_eigen_coefficient_EX009 hwd hsd f Af (smoothGrad (psi ∘ angEquiv)) H hH hAf⟩



noncomputable def angularGibbs_EX009 (ell : AngCircle → ℝ) : Torus 1 → ℝ :=
  DGPS.Lipschitz.WeightedGenerator.gibbsW (fun x => -ell (angEquiv x))

theorem angular_gibbs_data_EX009 (ell : AngCircle → ℝ) (hell : IsSmoothAngular ell)
    (M : ℝ) (hbound : ∀ theta, |ell theta| ≤ M) :
    ∃ Z : ℝ, 0 < Z ∧
      (∀ x, angularGibbs_EX009 ell x = Real.exp (ell (angEquiv x)) / Z) ∧
      (∫ x, angularGibbs_EX009 ell x ∂haar 1 = 1) ∧
      DGPS.Lipschitz.WeightedGenerator.WData 1 (angularGibbs_EX009 ell)
        (smoothGrad (ell ∘ angEquiv)) (Real.exp (-(2 * M))) (Real.exp (2 * M)) := by
  let Phi : Torus 1 → ℝ := fun x => -ell (angEquiv x)
  let Z := ∫ x, Real.exp (ell (angEquiv x)) ∂haar 1
  have hellphys := (isSmoothPeriodic_comp_iff ell).2 hell
  have hPhi : IsSmoothPeriodic Phi := by
    exact ContDiff.neg hellphys
  have hPhiBound : ∀ x, |Phi x| ≤ M := fun x => by
    simpa only [Phi, abs_neg] using hbound (angEquiv x)
  have hnorm := DGPS.Lipschitz.WeightedGenerator.normConst_bounds
    hPhi.continuous_torus hPhiBound
  have hnorm' : Real.exp (-M) ≤ Z ∧ Z ≤ Real.exp M := by
    simpa only [Phi, neg_neg] using hnorm
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hnorm'.1
  have hw (x : Torus 1) :
      angularGibbs_EX009 ell x = Real.exp (ell (angEquiv x)) / Z := by
    simp only [angularGibbs_EX009, DGPS.Lipschitz.WeightedGenerator.gibbsW, neg_neg, Z]
  obtain ⟨L, hL, hLip⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hPhi
  obtain ⟨c0, C0, hwd0⟩ := DGPS.Lipschitz.WeightedGenerator.gibbs_wdata hL hLip
  have hb : (fun x => -smoothGrad Phi x) = smoothGrad (ell ∘ angEquiv) := by
    ext x j
    simp only [PiLp.neg_apply, smoothGrad_apply]
    unfold coordPartial Phi
    change -(fderiv ℝ (-(ell ∘ angEquiv ∘ torusLift))
      (SharpLSI.secT x) (Pi.single j 1)) =
      fderiv ℝ (ell ∘ angEquiv ∘ torusLift) (SharpLSI.secT x) (Pi.single j 1)
    rw [fderiv_neg]
    simp
  have hwd1 := DGPS.Lipschitz.WeightedGenerator.wdata_congr_b hwd0
    (Filter.Eventually.of_forall fun x => congrFun hb x)
  have hquant (x : Torus 1) :
      Real.exp (-(2 * M)) ≤ angularGibbs_EX009 ell x ∧
        angularGibbs_EX009 ell x ≤ Real.exp (2 * M) := by
    have hlo : Real.exp (-M) ≤ Real.exp (ell (angEquiv x)) :=
      Real.exp_le_exp.mpr (abs_le.mp (hbound (angEquiv x))).1
    have hhi : Real.exp (ell (angEquiv x)) ≤ Real.exp M :=
      Real.exp_le_exp.mpr (abs_le.mp (hbound (angEquiv x))).2
    rw [hw x]
    constructor
    · calc
        Real.exp (-(2 * M)) = Real.exp (-M) / Real.exp M := by
          rw [← Real.exp_sub]
          congr 1
          ring
        _ ≤ Real.exp (ell (angEquiv x)) / Real.exp M :=
          div_le_div_of_nonneg_right hlo (Real.exp_pos _).le
        _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hZ hnorm'.2
    · calc
        Real.exp (ell (angEquiv x)) / Z ≤ Real.exp M / Z :=
          div_le_div_of_nonneg_right hhi hZ.le
        _ ≤ Real.exp M / Real.exp (-M) :=
          div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) hnorm'.1
        _ = Real.exp (2 * M) := by
          rw [← Real.exp_sub]
          congr 1
          ring
  have hwd :
      DGPS.Lipschitz.WeightedGenerator.WData 1 (angularGibbs_EX009 ell)
        (smoothGrad (ell ∘ angEquiv)) (Real.exp (-(2 * M))) (Real.exp (2 * M)) := {
    meas := hwd1.meas
    pos := Real.exp_pos _
    bound := hquant
    grad_w := hwd1.grad_w
    grad_inv := hwd1.grad_inv
    b_bdd := hwd1.b_bdd
  }
  refine ⟨Z, hZ, hw, ?_, hwd⟩
  have he : angularGibbs_EX009 ell = fun x => Real.exp (ell (angEquiv x)) / Z := funext hw
  rw [he, integral_div]
  exact div_self hZ.ne'



open DGPS.Circle.FirstClusterFourierEX009

theorem normalized_tests_inner_EX009 {w : Torus 1 → ℝ} {c C Z : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) (hZ : 0 < Z)
    (ell q r : AngCircle → ℝ)
    (hwexp : ∀ x, w x = Real.exp (ell (angEquiv x)) / Z)
    (f g : Hw 1 w)
    (hf : (f : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) * q (angEquiv x))
    (hg : (g : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) * r (angEquiv x)) :
    ⟪f, g⟫_ℝ = ∫ theta, q theta * r theta ∂angHaar := by
  calc
    ⟪f, g⟫_ℝ = ∫ x, q (angEquiv x) * r (angEquiv x) ∂haar 1 := by
      rw [inner_Lp_wMeasure hw hc hwb]
      apply integral_congr_ae
      filter_upwards [hf, hg] with x hfx hgx
      rw [hfx, hgx, hwexp x]
      simp only [RCLike.inner_apply, conj_trivial]
      convert normalized_ground_pair_EX009 hZ
        (ell (angEquiv x)) (q (angEquiv x)) (r (angEquiv x)) using 1
      ring
    _ = _ := integral_comp_angEquiv (fun theta => q theta * r theta)

theorem quasiCos_coe_EX009 (h A B C D x : ℝ) :
    quasiCos_EX009 h A B C D (x : AngCircle) = quasiCosLift_EX009 h A B C D x := by
  norm_num [quasiCos_EX009, angularPolynomial_EX009, quasiCosCoefficients_EX009,
    basis_EX009, cosMode_coe_EX009, sinMode_coe_EX009, Fin.sum_univ_succ,
    secondCosCoefficient_EX009, secondSinCoefficient_EX009,
    quasiCosLift_EX009, firstCorrectorCos_EX009, secondCorrectorCos_EX009]
  ring

theorem quasiSin_coe_EX009 (h A B C D x : ℝ) :
    quasiSin_EX009 h A B C D (x : AngCircle) = quasiSinLift_EX009 h A B C D x := by
  norm_num [quasiSin_EX009, angularPolynomial_EX009, quasiSinCoefficients_EX009,
    basis_EX009, cosMode_coe_EX009, sinMode_coe_EX009, Fin.sum_univ_succ,
    secondCosCoefficient_EX009, secondSinCoefficient_EX009,
    quasiSinLift_EX009, firstCorrectorSin_EX009, secondCorrectorSin_EX009]
  ring

theorem smooth_quasiCos_EX009 (h A B C D : ℝ) :
    IsSmoothAngular (quasiCos_EX009 h A B C D) := by
  have hf : (fun x : ℝ => quasiCos_EX009 h A B C D (x : AngCircle)) =
      quasiCosLift_EX009 h A B C D := funext (quasiCos_coe_EX009 h A B C D)
  unfold IsSmoothAngular
  rw [hf]
  unfold quasiCosLift_EX009 firstCorrectorCos_EX009 secondCorrectorCos_EX009
  fun_prop

theorem smooth_quasiSin_EX009 (h A B C D : ℝ) :
    IsSmoothAngular (quasiSin_EX009 h A B C D) := by
  have hf : (fun x : ℝ => quasiSin_EX009 h A B C D (x : AngCircle)) =
      quasiSinLift_EX009 h A B C D := funext (quasiSin_coe_EX009 h A B C D)
  unfold IsSmoothAngular
  rw [hf]
  unfold quasiSinLift_EX009 firstCorrectorSin_EX009 secondCorrectorSin_EX009
  fun_prop

noncomputable def normalizedGroundAngular_EX009 (Z : ℝ) (ell q : AngCircle → ℝ)
    (theta : AngCircle) : ℝ :=
  Real.sqrt Z * Real.exp (-ell theta / 2) * q theta

theorem smooth_normalized_ground_EX009 (Z : ℝ) {ell q : AngCircle → ℝ}
    (hell : IsSmoothAngular ell) (hq : IsSmoothAngular q) :
    IsSmoothAngular (normalizedGroundAngular_EX009 Z ell q) := by
  unfold IsSmoothAngular at *
  change ContDiff ℝ ∞ (fun s : ℝ => Real.sqrt Z * Real.exp (-ell (s : AngCircle) / 2) * q (s : AngCircle))
  exact ContDiff.mul (ContDiff.mul contDiff_const
    (ContDiff.exp (ContDiff.div_const (ContDiff.neg hell) 2))) hq

theorem normalized_generator_transport_EX009 (Z : ℝ) (ell q : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (hq : IsSmoothAngular q) (t : ℝ) :
    physicalGenerator_EX009 ell (normalizedGroundAngular_EX009 Z ell q)
      (torusLift (fun _ : Fin 1 => t)) =
      a0 * Real.sqrt Z * Real.exp (-ell ((2 * π * t : ℝ) : AngCircle) / 2) *
        schrodingerOperator_EX009 (fun s : ℝ => ell (s : AngCircle))
          (fun s : ℝ => q (s : AngCircle)) (2 * π * t) := by
  rw [physical_generator_formula_EX009 ell _
    hell (smooth_normalized_ground_EX009 Z hell hq)]
  have hf : (fun s : ℝ => normalizedGroundAngular_EX009 Z ell q (s : AngCircle)) =
      fun s : ℝ => Real.sqrt Z *
        inverseGround_EX009 (fun y : ℝ => ell (y : AngCircle))
          (fun y : ℝ => q (y : AngCircle)) s := by
    ext s
    unfold normalizedGroundAngular_EX009 inverseGround_EX009
    ring
  rw [hf, negativeGenerator_const_mul_EX009,
    negative_generator_inverse_EX009 (hell.of_le (by simp)) (hq.of_le (by simp))]
  ring



noncomputable def normalizedLogDensity_EX009 (rho : AngCircle → ℝ) (theta : AngCircle) : ℝ :=
  Real.log (rho theta) - ∫ phi, Real.log (rho phi) ∂angHaar

theorem integrable_smoothAngular_EX009 (f : AngCircle → ℝ) (hf : IsSmoothAngular f) :
    Integrable f angHaar := by
  have hp : MemLp (f ∘ angEquiv) 2 (haar 1) :=
    ((isSmoothPeriodic_comp_iff f).2 hf).memLp_top.mono_exponent le_top
  have ha : MemLp f 2 angHaar := (memLp_comp_angEquiv_iff f).mp hp
  exact ha.integrable one_le_two

theorem smooth_normalized_log_EX009 (rho : AngCircle → ℝ)
    (hrho : IsSmoothAngular rho) (hpos : ∀ theta, 0 < rho theta) :
    IsSmoothAngular (normalizedLogDensity_EX009 rho) := by
  unfold normalizedLogDensity_EX009 IsSmoothAngular
  exact (ContDiff.log hrho (fun x => (hpos (x : AngCircle)).ne')).sub contDiff_const

theorem normalized_log_mean_EX009 (rho : AngCircle → ℝ)
    (hrho : IsSmoothAngular rho) (hpos : ∀ theta, 0 < rho theta) :
    ∫ theta, normalizedLogDensity_EX009 rho theta ∂angHaar = 0 := by
  have hlog : IsSmoothAngular (fun theta => Real.log (rho theta)) :=
    ContDiff.log hrho (fun x => (hpos (x : AngCircle)).ne')
  have hi := integrable_smoothAngular_EX009 _ hlog
  unfold normalizedLogDensity_EX009
  rw [integral_sub hi (integrable_const _)]
  simp

/-- The physical weighted Hilbert measure pushes forward to the original angular
probability.  This is an equality of measures, not only an equality of total masses. -/
theorem probability_physical_pushforward_EX009 (P : ProbabilityMeasure AngCircle)
    (rho : AngCircle → ℝ)
    (hP : (P : Measure AngCircle) =
      angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta))) :
    Measure.map angEquiv (wMeasure 1 (rho ∘ angEquiv)) = (P : Measure AngCircle) := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply angEquiv.measurable hs, hP]
  unfold wMeasure
  rw [withDensity_apply _ (angEquiv.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (angEquiv.measurable hs), ← lintegral_indicator hs]
  calc
    (∫⁻ x, (angEquiv ⁻¹' s).indicator
        (fun x => ENNReal.ofReal ((rho ∘ angEquiv) x)) x ∂haar 1) =
      ∫⁻ x, (s.indicator (fun theta => ENNReal.ofReal (rho theta))) (angEquiv x) ∂haar 1 := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : angEquiv x ∈ s
          · simp [hx]
          · simp [hx]
    _ = _ := lintegral_comp_angEquiv (s.indicator (fun theta => ENNReal.ofReal (rho theta)))

theorem probability_density_mass_EX009 (P : ProbabilityMeasure AngCircle)
    (rho : AngCircle → ℝ) (hrho : IsSmoothAngular rho)
    (hpos : ∀ theta, 0 < rho theta)
    (hP : (P : Measure AngCircle) = angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta))) :
    ∫ theta, rho theta ∂angHaar = 1 := by
  have hi := integrable_smoothAngular_EX009 rho hrho
  have hm : (angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta))) Set.univ = 1 := by
    rw [← hP]
    exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun theta => (hpos theta).le)] at hm
  have ht := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_ofReal (integral_nonneg fun theta => (hpos theta).le)] at ht
  simpa using ht

theorem density_probability_EX009 (rho : AngCircle → ℝ)
    (hrho : IsSmoothAngular rho) (hpos : ∀ theta, 0 < rho theta)
    (hmass : ∫ theta, rho theta ∂angHaar = 1) :
    IsProbabilityMeasure (angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_smoothAngular_EX009 rho hrho)
      (Filter.Eventually.of_forall fun theta => (hpos theta).le),
    hmass, ENNReal.ofReal_one]

/-- Exact probability-to-chart transport, including its scalar normalization. -/
theorem normalized_log_density_EX009 (rho : AngCircle → ℝ)
    (hpos : ∀ theta, 0 < rho theta) (hmass : ∫ theta, rho theta ∂angHaar = 1) :
    angularGibbs_EX009 (normalizedLogDensity_EX009 rho) = rho ∘ angEquiv := by
  let m := ∫ theta, Real.log (rho theta) ∂angHaar
  have he (theta : AngCircle) :
      Real.exp (normalizedLogDensity_EX009 rho theta) = rho theta / Real.exp m := by
    unfold normalizedLogDensity_EX009
    rw [Real.exp_sub, Real.exp_log (hpos theta)]
  ext x
  unfold angularGibbs_EX009 DGPS.Lipschitz.WeightedGenerator.gibbsW
  simp only [neg_neg]
  simp_rw [he]
  rw [integral_div, integral_comp_angEquiv rho, hmass]
  field_simp [Real.exp_ne_zero m]
  rfl

/-- The reverse chart transport is exact for the Haar-mean-zero logarithm. -/
theorem chart_normalized_log_EX009 (ell : AngCircle → ℝ) (hell : IsSmoothAngular ell)
    (hmean : ∫ theta, ell theta ∂angHaar = 0) {Z : ℝ} (hZ : 0 < Z) :
    normalizedLogDensity_EX009 (fun theta => Real.exp (ell theta) / Z) = ell := by
  have he (theta : AngCircle) :
      Real.log (Real.exp (ell theta) / Z) = ell theta - Real.log Z := by
    rw [Real.log_div (Real.exp_ne_zero _) hZ.ne', Real.log_exp]
  have hi := integrable_smoothAngular_EX009 ell hell
  ext theta
  unfold normalizedLogDensity_EX009
  simp_rw [he]
  rw [integral_sub hi (integrable_const _)]
  simp [hmean]




/-- The max C2 error of the real periodic angular lift, in the canonical angular units. -/
def c2JetError_EX009 (ell : AngCircle → ℝ) (h A B C D R : ℝ) : Prop :=
  ∀ x : ℝ,
    |ell (x : AngCircle) - harmonicLog_EX009 h A B C D x| ≤ R * |h| ^ 3 ∧
    |deriv (fun y : ℝ => ell (y : AngCircle)) x -
      deriv (harmonicLog_EX009 h A B C D) x| ≤ R * |h| ^ 3 ∧
    |deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x -
      deriv (deriv (harmonicLog_EX009 h A B C D)) x| ≤ R * |h| ^ 3

theorem potential_jet_factor_EX009 (ell : AngCircle → ℝ) {h A B C D M R : ℝ}
    (hh : |h| ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) (hD : |D| ≤ M)
    (hjet : c2JetError_EX009 ell h A B C D R) :
    ∃ Vrem : ℝ → ℝ,
      (∀ x, schrodingerPotential_EX009 (fun y : ℝ => ell (y : AngCircle)) x =
        h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x +
          h ^ 3 * Vrem x) ∧
      (∀ x, |Vrem x| ≤ R / 2 + 3 * (4 * M) ^ 2 / 4 +
        (4 * M) * R + R ^ 2 / 4) := by
  let r : ℝ → ℝ := fun x =>
    (deriv (fun y : ℝ => ell (y : AngCircle)) x -
      deriv (harmonicLog_EX009 h A B C D) x) / h ^ 3
  let s : ℝ → ℝ := fun x =>
    (deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x -
      deriv (deriv (harmonicLog_EX009 h A B C D)) x) / h ^ 3
  have hr (x : ℝ) : |r x| ≤ R := by
    by_cases hz : h = 0
    · simpa [r, hz] using hR
    · have hp : 0 < |h| ^ 3 := pow_pos (abs_pos.mpr hz) 3
      dsimp [r]
      rw [abs_div, abs_pow, div_le_iff₀ hp]
      exact (hjet x).2.1
  have hs (x : ℝ) : |s x| ≤ R := by
    by_cases hz : h = 0
    · simpa [s, hz] using hR
    · have hp : 0 < |h| ^ 3 := pow_pos (abs_pos.mpr hz) 3
      dsimp [s]
      rw [abs_div, abs_pow, div_le_iff₀ hp]
      exact (hjet x).2.2
  have hfirst (x : ℝ) :
      deriv (fun y : ℝ => ell (y : AngCircle)) x =
        h * (-A * Real.sin x + B * Real.cos x) +
        h ^ 2 * (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)) + h ^ 3 * r x := by
    by_cases hz : h = 0
    · have hb : |deriv (fun y : ℝ => ell (y : AngCircle)) x| ≤ 0 := by
        simpa [hz, deriv_harmonicLog_EX009] using (hjet x).2.1
      have he : deriv (fun y : ℝ => ell (y : AngCircle)) x = 0 :=
        abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      simp [hz, he]
    · have he : r x * h ^ 3 =
          deriv (fun y : ℝ => ell (y : AngCircle)) x -
            deriv (harmonicLog_EX009 h A B C D) x :=
        div_mul_cancel₀ _ (pow_ne_zero 3 hz)
      rw [deriv_harmonicLog_EX009] at he
      nlinarith
  have hsecond (x : ℝ) :
      deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x =
        h * (-A * Real.cos x - B * Real.sin x) +
        h ^ 2 * (-4 * C * Real.cos (2 * x) - 4 * D * Real.sin (2 * x)) + h ^ 3 * s x := by
    by_cases hz : h = 0
    · have hb : |deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x| ≤ 0 := by
        simpa [hz, deriv2_harmonicLog_EX009] using (hjet x).2.2
      have he : deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x = 0 :=
        abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
      simp [hz, he]
    · have he : s x * h ^ 3 =
          deriv (deriv (fun y : ℝ => ell (y : AngCircle))) x -
            deriv (deriv (harmonicLog_EX009 h A B C D)) x :=
        div_mul_cancel₀ _ (pow_ne_zero 3 hz)
      rw [deriv2_harmonicLog_EX009] at he
      nlinarith
  let Vrem : ℝ → ℝ := fun x => potentialRemainder_EX009 h
    (-A * Real.sin x + B * Real.cos x)
    (-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)) (r x) (s x)
  refine ⟨Vrem, ?_, ?_⟩
  · intro x
    unfold schrodingerPotential_EX009
    rw [hfirst, hsecond, potential_jet_expansion_EX009]
    unfold firstPotential_EX009 secondPotential_EX009 Vrem
    ring
  · intro x
    have hu : |-A * Real.sin x + B * Real.cos x| ≤ 4 * M := by
      have he := harmonic_first_derivative_bound_EX009 A B x
      linarith
    have hv : |-2 * C * Real.sin (2 * x) + 2 * D * Real.cos (2 * x)| ≤ 4 * M := by
      have he := harmonic_second_derivative_bound_EX009 C D x
      linarith
    exact potentialRemainder_bound_EX009 hh (by positivity) hR hu hv (hr x) (hs x)




/-- Both universal residual coefficients, before substituting a bounded potential remainder. -/
noncomputable def residualCoefficients_EX009 (p : Fin 4 → ℝ) (h : ℝ)
    (theta : AngCircle) (r : ℝ) : Fin 2 → ℝ :=
  let A := p 0
  let B := p 1
  let C := p 2
  let D := p 3
  let c1 := cosMode_EX009 1 theta
  let s1 := sinMode_EX009 1 theta
  let c2 := cosMode_EX009 2 theta
  let s2 := sinMode_EX009 2 theta
  let c3 := cosMode_EX009 3 theta
  let s3 := sinMode_EX009 3 theta
  let pc := -A / 4 + (A * c2 + B * s2) / 12
  let ps := -B / 4 + (A * s2 - B * c2) / 12
  let rc := secondCosCoefficient_EX009 A B C * c3 + secondSinCoefficient_EX009 A B D * s3
  let rs := -secondSinCoefficient_EX009 A B D * c3 + secondCosCoefficient_EX009 A B C * s3
  let qc := c1 + h * pc + h ^ 2 * rc
  let qs := s1 + h * ps + h ^ 2 * rs
  let V1 := -(A * c1 + B * s1) / 2
  let V2 := -2 * (C * c2 + D * s2) + (-A * s1 + B * c1) ^ 2 / 4
  let m11 := (A ^ 2 + B ^ 2) / 6 - C
  let m22 := (A ^ 2 + B ^ 2) / 6 + C
  ![r * qc + V1 * rc + V2 * pc - m11 * pc + D * ps +
      h * (V2 * rc - m11 * rc + D * rs),
    r * qs + V1 * rs + V2 * ps + D * pc - m22 * ps +
      h * (V2 * rs + D * rc - m22 * rs)]

theorem continuous_residualCoefficients_EX009 (i : Fin 2) :
    Continuous (fun x : ((Fin 4 → ℝ) × ℝ × AngCircle × ℝ) =>
      residualCoefficients_EX009 x.1 x.2.1 x.2.2.1 x.2.2.2 i) := by
  have hc1 := continuous_cosMode_EX009 1
  have hs1 := continuous_sinMode_EX009 1
  have hc2 := continuous_cosMode_EX009 2
  have hs2 := continuous_sinMode_EX009 2
  have hc3 := continuous_cosMode_EX009 3
  have hs3 := continuous_sinMode_EX009 3
  fin_cases i
  · dsimp [residualCoefficients_EX009, secondCosCoefficient_EX009, secondSinCoefficient_EX009]
    fun_prop
  · dsimp [residualCoefficients_EX009, secondCosCoefficient_EX009, secondSinCoefficient_EX009]
    fun_prop

theorem quasi_cos_residual_factor_EX009 (ell R : ℝ → ℝ) (h A B C D : ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 ell x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x + h ^ 3 * R x)
    (x : ℝ) :
    schrodingerOperator_EX009 ell (quasiCosLift_EX009 h A B C D) x -
      ((1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 - C)) * quasiCosLift_EX009 h A B C D x -
        h ^ 2 * D * quasiSinLift_EX009 h A B C D x) =
      h ^ 3 * residualCoefficients_EX009 ![A, B, C, D] h (x : AngCircle) (R x) 0 := by
  rw [quasi_cos_residual_EX009 ell R h A B C D hpot x]
  norm_num [residualCoefficients_EX009, cosMode_coe_EX009, sinMode_coe_EX009,
    secondCosCoefficient_EX009, secondSinCoefficient_EX009,
    quasiCosLift_EX009, quasiSinLift_EX009,
    firstCorrectorCos_EX009, firstCorrectorSin_EX009,
    secondCorrectorCos_EX009, secondCorrectorSin_EX009,
    firstPotential_EX009, secondPotential_EX009]
  ring

theorem quasi_sin_residual_factor_EX009 (ell R : ℝ → ℝ) (h A B C D : ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 ell x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x + h ^ 3 * R x)
    (x : ℝ) :
    schrodingerOperator_EX009 ell (quasiSinLift_EX009 h A B C D) x -
      (-h ^ 2 * D * quasiCosLift_EX009 h A B C D x +
        (1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 + C)) * quasiSinLift_EX009 h A B C D x) =
      h ^ 3 * residualCoefficients_EX009 ![A, B, C, D] h (x : AngCircle) (R x) 1 := by
  rw [quasi_sin_residual_EX009 ell R h A B C D hpot x]
  norm_num [residualCoefficients_EX009, cosMode_coe_EX009, sinMode_coe_EX009,
    secondCosCoefficient_EX009, secondSinCoefficient_EX009,
    quasiCosLift_EX009, quasiSinLift_EX009,
    firstCorrectorCos_EX009, firstCorrectorSin_EX009,
    secondCorrectorCos_EX009, secondCorrectorSin_EX009,
    firstPotential_EX009, secondPotential_EX009]
  ring



noncomputable def dotTwo_EX009 (y z : Fin 2 → ℝ) : ℝ :=
  y 0 * z 0 + y 1 * z 1

theorem projected_gram_bilinear_EX009
    (T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)) {eta : ℝ}
    (hGram : ∀ y,
      |twoNormSq_EX009 (T y) - twoNormSq_EX009 y / 2| ≤ eta * twoNormSq_EX009 y)
    (y z : Fin 2 → ℝ) :
    |dotTwo_EX009 (T y) (T z) - dotTwo_EX009 y z / 2| ≤
      eta * (twoNormSq_EX009 y + twoNormSq_EX009 z) / 2 := by
  have hp := hGram (y + z)
  have hm := hGram (y - z)
  rw [map_add] at hp
  rw [map_sub] at hm
  have he :
      4 * (dotTwo_EX009 (T y) (T z) - dotTwo_EX009 y z / 2) =
        (twoNormSq_EX009 (T y + T z) - twoNormSq_EX009 (y + z) / 2) -
          (twoNormSq_EX009 (T y - T z) - twoNormSq_EX009 (y - z) / 2) := by
    simp only [dotTwo_EX009, twoNormSq_EX009, Pi.add_apply, Pi.sub_apply]
    ring
  have htri : |(twoNormSq_EX009 (T y + T z) - twoNormSq_EX009 (y + z) / 2) -
      (twoNormSq_EX009 (T y - T z) - twoNormSq_EX009 (y - z) / 2)| ≤
      |twoNormSq_EX009 (T y + T z) - twoNormSq_EX009 (y + z) / 2| +
        |twoNormSq_EX009 (T y - T z) - twoNormSq_EX009 (y - z) / 2| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
      (twoNormSq_EX009 (T y + T z) - twoNormSq_EX009 (y + z) / 2)
      (-(twoNormSq_EX009 (T y - T z) - twoNormSq_EX009 (y - z) / 2))
  have hp' := htri.trans (add_le_add hp hm)
  rw [← he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hp'
  have hn :
      twoNormSq_EX009 (y + z) + twoNormSq_EX009 (y - z) =
        2 * (twoNormSq_EX009 y + twoNormSq_EX009 z) := by
    simp only [twoNormSq_EX009, Pi.add_apply, Pi.sub_apply]
    ring
  rw [← mul_add, hn] at hp'
  nlinarith only [hp']

theorem norm_le_sqrt_coordinate_EX009 {E : Type*} [NormedAddCommGroup E]
    (f : E) (y : Fin 2 → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ‖f‖ ^ 2 ≤ K ^ 2 * twoNormSq_EX009 y) :
    ‖f‖ ≤ K * Real.sqrt (twoNormSq_EX009 y) := by
  have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
  have hs := Real.sq_sqrt hn
  have hs0 := Real.sqrt_nonneg (twoNormSq_EX009 y)
  have he : (K * Real.sqrt (twoNormSq_EX009 y)) ^ 2 = K ^ 2 * twoNormSq_EX009 y := by
    rw [mul_pow, hs]
  apply (sq_le_sq₀ (norm_nonneg f) (mul_nonneg hK hs0)).mp
  rw [he]
  exact hbound

theorem sqrt_coordinate_map_EX009 (M : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ y, twoNormSq_EX009 (M y) ≤ K ^ 2 * twoNormSq_EX009 y)
    (y : Fin 2 → ℝ) :
    Real.sqrt (twoNormSq_EX009 (M y)) ≤ K * Real.sqrt (twoNormSq_EX009 y) := by
  have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
  have hm : 0 ≤ twoNormSq_EX009 (M y) := by unfold twoNormSq_EX009; positivity
  have hs := Real.sq_sqrt hn
  have hsM := Real.sq_sqrt hm
  have he : (K * Real.sqrt (twoNormSq_EX009 y)) ^ 2 = K ^ 2 * twoNormSq_EX009 y := by
    rw [mul_pow, hs]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).mp
  rw [hsM, he]
  exact hbound y


noncomputable def clusterMatrix_EX009 (A B C D : ℝ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun y := ![((A ^ 2 + B ^ 2) / 6 - C) * y 0 - D * y 1,
    -D * y 0 + ((A ^ 2 + B ^ 2) / 6 + C) * y 1]
  map_add' y z := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c y := by
    ext i
    fin_cases i <;> simp <;> ring

noncomputable def gramControl_EX009 (p : Fin 4 → ℝ) : ℝ :=
  19 * (p 0 ^ 2 + p 1 ^ 2) / 288 +
    ((secondCosCoefficient_EX009 (p 0) (p 1) (p 2)) ^ 2 +
      (secondSinCoefficient_EX009 (p 0) (p 1) (p 3)) ^ 2) / 2

noncomputable def matrixControl_EX009 (p : Fin 4 → ℝ) : ℝ :=
  ((p 0 ^ 2 + p 1 ^ 2) / 6 - p 2) ^ 2 +
    ((p 0 ^ 2 + p 1 ^ 2) / 6 + p 2) ^ 2 + 2 * p 3 ^ 2

noncomputable def modelMinimum_EX009 (p : Fin 4 → ℝ) : ℝ :=
  (p 0 ^ 2 + p 1 ^ 2) / 6 - Real.sqrt (p 2 ^ 2 + p 3 ^ 2)

noncomputable def modelMaximum_EX009 (p : Fin 4 → ℝ) : ℝ :=
  (p 0 ^ 2 + p 1 ^ 2) / 6 + Real.sqrt (p 2 ^ 2 + p 3 ^ 2)

theorem cluster_matrix_norm_EX009 (A B C D : ℝ) (y : Fin 2 → ℝ) :
    twoNormSq_EX009 (clusterMatrix_EX009 A B C D y) ≤
      matrixControl_EX009 ![A, B, C, D] * twoNormSq_EX009 y := by
  dsimp [twoNormSq_EX009, clusterMatrix_EX009, matrixControl_EX009]
  nlinarith [sq_nonneg ((((A ^ 2 + B ^ 2) / 6 - C) * y 1 + D * y 0)),
    sq_nonneg (D * y 1 + ((A ^ 2 + B ^ 2) / 6 + C) * y 0)]

theorem cluster_matrix_quadratic_EX009 (A B C D : ℝ) (y : Fin 2 → ℝ) :
    dotTwo_EX009 y (clusterMatrix_EX009 A B C D y) =
      (A ^ 2 + B ^ 2) / 6 * twoNormSq_EX009 y +
        clusterQuadratic_EX009 C D (y 0) (y 1) := by
  dsimp [dotTwo_EX009, clusterMatrix_EX009, twoNormSq_EX009, clusterQuadratic_EX009]
  ring

theorem uniform_quasimode_control_EX009 {M R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ p : Fin 4 → ℝ, (∀ i, |p i| ≤ M) →
        gramControl_EX009 p ≤ K ∧ matrixControl_EX009 p ≤ K ^ 2 ∧
        |modelMinimum_EX009 p| ≤ K ∧ |modelMaximum_EX009 p| ≤ K ∧
        (∀ (h : ℝ) (theta : AngCircle) (r : ℝ) (i : Fin 2),
          |h| ≤ 1 → |r| ≤ R →
            |residualCoefficients_EX009 p h theta r i| ≤ K) := by
  let F : ((Fin 4 → ℝ) × ℝ × AngCircle × ℝ) → ℝ := fun x =>
    |residualCoefficients_EX009 x.1 x.2.1 x.2.2.1 x.2.2.2 0| +
    |residualCoefficients_EX009 x.1 x.2.1 x.2.2.1 x.2.2.2 1| +
    |gramControl_EX009 x.1| + |matrixControl_EX009 x.1| +
    |modelMinimum_EX009 x.1| + |modelMaximum_EX009 x.1|
  have hF : Continuous F := by
    have h0 := continuous_residualCoefficients_EX009 0
    have h1 := continuous_residualCoefficients_EX009 1
    unfold F gramControl_EX009 matrixControl_EX009 modelMinimum_EX009 modelMaximum_EX009
      secondCosCoefficient_EX009 secondSinCoefficient_EX009
    fun_prop
  obtain ⟨K0, _hK0, hbound⟩ := compact_polynomial_bound_EX009 F hF M R
  let K := max K0 1
  have hK : 1 ≤ K := le_max_right _ _
  have hK0K : K0 ≤ K := le_max_left _ _
  refine ⟨K, hK, ?_⟩
  intro p hp
  have hbase := (le_abs_self (F (p, 0, (0 : AngCircle), 0))).trans
    (hbound p 0 0 0 hp (by norm_num) (by simpa using hR))
  have hg : |gramControl_EX009 p| ≤ K := by
    dsimp [F] at hbase
    linarith [abs_nonneg (residualCoefficients_EX009 p 0 0 0 0),
      abs_nonneg (residualCoefficients_EX009 p 0 0 0 1),
      abs_nonneg (matrixControl_EX009 p), abs_nonneg (modelMinimum_EX009 p),
      abs_nonneg (modelMaximum_EX009 p)]
  have hm : |matrixControl_EX009 p| ≤ K := by
    dsimp [F] at hbase
    linarith [abs_nonneg (residualCoefficients_EX009 p 0 0 0 0),
      abs_nonneg (residualCoefficients_EX009 p 0 0 0 1),
      abs_nonneg (gramControl_EX009 p), abs_nonneg (modelMinimum_EX009 p),
      abs_nonneg (modelMaximum_EX009 p)]
  refine ⟨(le_abs_self _).trans hg, ?_, ?_, ?_, ?_⟩
  · exact (le_abs_self _).trans (hm.trans (by nlinarith))
  · dsimp [F] at hbase
    linarith [abs_nonneg (residualCoefficients_EX009 p 0 0 0 0),
      abs_nonneg (residualCoefficients_EX009 p 0 0 0 1),
      abs_nonneg (gramControl_EX009 p), abs_nonneg (matrixControl_EX009 p),
      abs_nonneg (modelMaximum_EX009 p)]
  · dsimp [F] at hbase
    linarith [abs_nonneg (residualCoefficients_EX009 p 0 0 0 0),
      abs_nonneg (residualCoefficients_EX009 p 0 0 0 1),
      abs_nonneg (gramControl_EX009 p), abs_nonneg (matrixControl_EX009 p),
      abs_nonneg (modelMinimum_EX009 p)]
  · intro h theta r i hh hr
    have hb := (le_abs_self (F (p, h, theta, r))).trans (hbound p h theta r hp hh hr)
    dsimp [F] at hb
    fin_cases i
    · change |residualCoefficients_EX009 p h theta r 0| ≤ K
      linarith [abs_nonneg (residualCoefficients_EX009 p h theta r 1),
        abs_nonneg (gramControl_EX009 p), abs_nonneg (matrixControl_EX009 p),
        abs_nonneg (modelMinimum_EX009 p), abs_nonneg (modelMaximum_EX009 p)]
    · change |residualCoefficients_EX009 p h theta r 1| ≤ K
      linarith [abs_nonneg (residualCoefficients_EX009 p h theta r 0),
        abs_nonneg (gramControl_EX009 p), abs_nonneg (matrixControl_EX009 p),
        abs_nonneg (modelMinimum_EX009 p), abs_nonneg (modelMaximum_EX009 p)]


section HilbertClusterBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def spectralCoordinates_EX009 (e : HilbertBasis ℕ ℝ E)
    (X : (Fin 2 → ℝ) →ₗ[ℝ] E) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun y := ![⟪e 1, X y⟫_ℝ, ⟪e 2, X y⟫_ℝ]
  map_add' y z := by
    ext i
    fin_cases i <;> simp [map_add, inner_add_right]
  map_smul' c y := by
    ext i
    fin_cases i <;> simp [map_smul, inner_smul_right]

theorem projected_coordinate_norm_EX009 (e : HilbertBasis ℕ ℝ E)
    (X : (Fin 2 → ℝ) →ₗ[ℝ] E) (y : Fin 2 → ℝ) :
    twoNormSq_EX009 (spectralCoordinates_EX009 e X y) =
      ‖pairProjection_EX009 e (X y)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, pairProjection_inner_EX009]
  simp [twoNormSq_EX009, spectralCoordinates_EX009, sq]

/-- The weak coefficient identity, Parseval and an outside gap give the complete
projected Gram and energy comparison.  All columns here belong to the actual Hilbert space. -/
theorem projected_cluster_data_EX009 (e : HilbertBasis ℕ ℝ E) (lam : ℕ → ℝ)
    (X : (Fin 2 → ℝ) →ₗ[ℝ] E)
    (M : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
    (R B : (Fin 2 → ℝ) →ₗ[ℝ] E)
    {a t delta g p L Km r : ℝ}
    (hdelta : 0 < delta) (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hL : 0 ≤ L)
    (hgap : ∀ j, j ≠ 1 → j ≠ 2 → delta ≤ |lam j - a|)
    (hres : ∀ y j, lam j * ⟪e j, X y⟫_ℝ =
      a * ⟪e j, X y⟫_ℝ + t * ⟪e j, X (M y)⟫_ℝ + ⟪e j, R y⟫_ℝ)
    (hbase : ∀ y j, (lam j - a) * ⟪e j, X y⟫_ℝ = ⟪e j, B y⟫_ℝ)
    (hbaseNorm : ∀ y, ‖B y‖ ≤ delta * p * Real.sqrt (twoNormSq_EX009 y))
    (hGramLow : ∀ y, twoNormSq_EX009 y / 2 ≤ ‖X y‖ ^ 2)
    (hGram : ∀ y, |‖X y‖ ^ 2 - twoNormSq_EX009 y / 2| ≤ g * twoNormSq_EX009 y)
    (hX : ∀ y, ‖X y‖ ≤ L * Real.sqrt (twoNormSq_EX009 y))
    (hM : ∀ y, twoNormSq_EX009 (M y) ≤ Km ^ 2 * twoNormSq_EX009 y)
    (hR : ∀ y, ‖R y‖ ≤ r * Real.sqrt (twoNormSq_EX009 y)) :
    let T := spectralCoordinates_EX009 e X
    (∀ y, (1 / 2 - p ^ 2) * twoNormSq_EX009 y ≤ twoNormSq_EX009 (T y)) ∧
    (∀ y, |twoNormSq_EX009 (T y) - twoNormSq_EX009 y / 2| ≤
      (g + p ^ 2) * twoNormSq_EX009 y) ∧
    (∀ y, |lam 1 * (T y) 0 ^ 2 + lam 2 * (T y) 1 ^ 2 -
        a * twoNormSq_EX009 (T y) - t * dotTwo_EX009 y (M y) / 2| ≤
      (L * r + t * (g + p ^ 2) * (1 + Km ^ 2) / 2) * twoNormSq_EX009 y) := by
  let T := spectralCoordinates_EX009 e X
  have hout (y : Fin 2 → ℝ) :
      ‖X y - pairProjection_EX009 e (X y)‖ ^ 2 ≤ p ^ 2 * twoNormSq_EX009 y := by
    have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
    have hs := Real.sq_sqrt hn
    have hproj := spectral_projection_error_EX009 e lam a delta hdelta.le hgap
      (X y) (B y) (hbase y)
    have hsq := pow_le_pow_left₀ (norm_nonneg (B y)) (hbaseNorm y) 2
    have hb : ‖B y‖ ^ 2 ≤ delta ^ 2 * (p ^ 2 * twoNormSq_EX009 y) := by
      calc
        ‖B y‖ ^ 2 ≤ (delta * p * Real.sqrt (twoNormSq_EX009 y)) ^ 2 := hsq
        _ = _ := by simp only [mul_pow, hs]; ring
    exact le_of_mul_le_mul_left (hproj.trans hb) (sq_pos_of_pos hdelta)
  have hGramP (y : Fin 2 → ℝ) :
      |twoNormSq_EX009 (T y) - twoNormSq_EX009 y / 2| ≤
        (g + p ^ 2) * twoNormSq_EX009 y := by
    have he := pairProjection_pythagoras_EX009 e (X y)
    have hnorm := projected_coordinate_norm_EX009 e X y
    have hgr := abs_le.mp (hGram y)
    have ho := hout y
    dsimp [T] at *
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ‖X y - pairProjection_EX009 e (X y)‖]
  refine ⟨?_, hGramP, ?_⟩
  · intro y
    have he := pairProjection_pythagoras_EX009 e (X y)
    have hnorm := projected_coordinate_norm_EX009 e X y
    have hgr := abs_le.mp (hGram y)
    have ho := hout y
    have hl := hGramLow y
    dsimp [T] at *
    nlinarith
  · intro y
    have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
    have hs := Real.sq_sqrt hn
    have hinner : |⟪pairProjection_EX009 e (X y), R y⟫_ℝ| ≤ L * r * twoNormSq_EX009 y := by
      have hpNorm := (pairProjection_norm_le_EX009 e (X y)).trans (hX y)
      calc
        |⟪pairProjection_EX009 e (X y), R y⟫_ℝ| ≤
            ‖pairProjection_EX009 e (X y)‖ * ‖R y‖ := abs_real_inner_le_norm _ _
        _ ≤ (L * Real.sqrt (twoNormSq_EX009 y)) *
            (r * Real.sqrt (twoNormSq_EX009 y)) :=
          mul_le_mul hpNorm (hR y) (norm_nonneg _) (by positivity)
        _ = _ := by
          calc
            _ = L * r * (Real.sqrt (twoNormSq_EX009 y)) ^ 2 := by ring
            _ = _ := by rw [hs]
    have hbil := projected_gram_bilinear_EX009 T hGramP y (M y)
    have hbil' :
        |dotTwo_EX009 (T y) (T (M y)) - dotTwo_EX009 y (M y) / 2| ≤
          (g + p ^ 2) * (1 + Km ^ 2) / 2 * twoNormSq_EX009 y := by
      have hm := mul_le_mul_of_nonneg_left (hM y) (by positivity : 0 ≤ (g + p ^ 2) / 2)
      nlinarith
    have he :
        lam 1 * (T y) 0 ^ 2 + lam 2 * (T y) 1 ^ 2 -
          a * twoNormSq_EX009 (T y) - t * dotTwo_EX009 (T y) (T (M y)) =
          ⟪pairProjection_EX009 e (X y), R y⟫_ℝ := by
      rw [pairProjection_inner_left_EX009]
      have h1 := hres y 1
      have h2 := hres y 2
      dsimp [T, spectralCoordinates_EX009, dotTwo_EX009, twoNormSq_EX009]
      linear_combination ⟪e 1, X y⟫_ℝ * h1 + ⟪e 2, X y⟫_ℝ * h2
    have hdecomp :
        lam 1 * (T y) 0 ^ 2 + lam 2 * (T y) 1 ^ 2 -
          a * twoNormSq_EX009 (T y) - t * dotTwo_EX009 y (M y) / 2 =
          ⟪pairProjection_EX009 e (X y), R y⟫_ℝ +
            t * (dotTwo_EX009 (T y) (T (M y)) - dotTwo_EX009 y (M y) / 2) := by
      linarith only [he]
    rw [hdecomp]
    calc
      _ ≤ |⟪pairProjection_EX009 e (X y), R y⟫_ℝ| +
          |t * (dotTwo_EX009 (T y) (T (M y)) - dotTwo_EX009 y (M y) / 2)| := abs_add_le _ _
      _ ≤ L * r * twoNormSq_EX009 y +
          t * ((g + p ^ 2) * (1 + Km ^ 2) / 2 * twoNormSq_EX009 y) := by
        rw [abs_mul, abs_of_nonneg ht]
        exact add_le_add hinner (mul_le_mul_of_nonneg_left hbil' ht)
      _ = _ := by ring

end HilbertClusterBridge


section TwoColumnMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def twoColumnMap_EX009 (f g : E) : (Fin 2 → ℝ) →ₗ[ℝ] E where
  toFun y := y 0 • f + y 1 • g
  map_add' y z := by simp [add_smul]; abel
  map_smul' c y := by simp [smul_add, mul_smul]

end TwoColumnMap

theorem two_column_coe_EX009 {w : Torus 1 → ℝ} {c C : ℝ} (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C)
    (f g : Hw 1 w) (F G : Torus 1 → ℝ)
    (hf : (f : Torus 1 → ℝ) =ᵐ[haar 1] F)
    (hg : (g : Torus 1 → ℝ) =ᵐ[haar 1] G) (y : Fin 2 → ℝ) :
    ((twoColumnMap_EX009 f g y : Hw 1 w) : Torus 1 → ℝ) =ᵐ[haar 1]
      fun x => y 0 * F x + y 1 * G x := by
  filter_upwards [ae_eq_haar hc hwb (Lp.coeFn_add (y 0 • f) (y 1 • g)),
    ae_eq_haar hc hwb (Lp.coeFn_smul (y 0) f),
    ae_eq_haar hc hwb (Lp.coeFn_smul (y 1) g), hf, hg] with x hsum h0 h1 hfx hgx
  change ((y 0 • f + y 1 • g : Hw 1 w) : Torus 1 → ℝ) x = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsum h0 h1
  rw [hsum, h0, h1, hfx, hgx]

theorem normalized_test_norm_bound_EX009 {w : Torus 1 → ℝ} {c C Z K : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) (hZ : 0 < Z)
    (ell q : AngCircle → ℝ) (hK : 0 ≤ K)
    (hwexp : ∀ x, w x = Real.exp (ell (angEquiv x)) / Z)
    (f : Hw 1 w)
    (hf : (f : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) * q (angEquiv x))
    (hq : ∀ theta, |q theta| ≤ K) : ‖f‖ ≤ K := by
  have he := normalized_tests_inner_EX009 hw hc hwb hZ ell q q hwexp f f hf hf
  rw [real_inner_self_eq_norm_sq] at he
  have hi : (∫ theta, q theta * q theta ∂angHaar) ≤ K ^ 2 := by
    calc
      _ ≤ ∫ _ : AngCircle, K ^ 2 ∂angHaar :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun theta => mul_self_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall fun theta => by
            have hs := pow_le_pow_left₀ (abs_nonneg (q theta)) (hq theta) 2
            rw [sq_abs] at hs
            simpa only [pow_two] using hs)
      _ = _ := by simp
  nlinarith [norm_nonneg f]

theorem physical_generator_transport_all_EX009 (Z : ℝ) (ell q : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (hq : IsSmoothAngular q) (x : Torus 1) :
    physicalGenerator_EX009 ell (normalizedGroundAngular_EX009 Z ell q) x =
      a0 * Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        schrodingerOperator_EX009 (fun s : ℝ => ell (s : AngCircle))
          (fun s : ℝ => q (s : AngCircle)) (angSec (angEquiv x)) := by
  have hx : torusLift (fun _ : Fin 1 => SharpLSI.secT x 0) = x := by
    have he : (fun _ : Fin 1 => SharpLSI.secT x 0) = SharpLSI.secT x := by
      ext i
      fin_cases i
      rfl
    rw [he]
    exact SharpLSI.liftT_secT x
  have he := normalized_generator_transport_EX009 Z ell q hell hq (SharpLSI.secT x 0)
  rw [hx, ← angSec_angEquiv x] at he
  have hc : ((angSec (angEquiv x) : ℝ) : AngCircle) = angEquiv x := by
    exact AddCircle.coe_equivIoc
  rw [hc] at he
  exact he

theorem physical_quasi_residual_EX009 (Z : ℝ) (ell : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (Vrem : ℝ → ℝ) (h A B C D : ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 (fun y : ℝ => ell (y : AngCircle)) x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B C D x +
        h ^ 3 * Vrem x) (x : Torus 1) :
    let qc := quasiCos_EX009 h A B C D
    let qs := quasiSin_EX009 h A B C D
    let pc := normalizedGroundAngular_EX009 Z ell qc
    let ps := normalizedGroundAngular_EX009 Z ell qs
    (physicalGenerator_EX009 ell pc x -
        a0 * (1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 - C)) * pc (angEquiv x) +
        a0 * h ^ 2 * D * ps (angEquiv x) =
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (a0 * h ^ 3 * residualCoefficients_EX009 ![A, B, C, D] h (angEquiv x)
          (Vrem (angSec (angEquiv x))) 0)) ∧
    (physicalGenerator_EX009 ell ps x +
        a0 * h ^ 2 * D * pc (angEquiv x) -
        a0 * (1 + h ^ 2 * ((A ^ 2 + B ^ 2) / 6 + C)) * ps (angEquiv x) =
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (a0 * h ^ 3 * residualCoefficients_EX009 ![A, B, C, D] h (angEquiv x)
          (Vrem (angSec (angEquiv x))) 1)) := by
  dsimp only
  have hc : ((angSec (angEquiv x) : ℝ) : AngCircle) = angEquiv x :=
    AddCircle.coe_equivIoc
  have hqc : (fun s : ℝ => quasiCos_EX009 h A B C D (s : AngCircle)) =
      quasiCosLift_EX009 h A B C D := funext (quasiCos_coe_EX009 h A B C D)
  have hqs : (fun s : ℝ => quasiSin_EX009 h A B C D (s : AngCircle)) =
      quasiSinLift_EX009 h A B C D := funext (quasiSin_coe_EX009 h A B C D)
  have hcos := quasi_cos_residual_factor_EX009 (fun y : ℝ => ell (y : AngCircle))
    Vrem h A B C D hpot (angSec (angEquiv x))
  have hsin := quasi_sin_residual_factor_EX009 (fun y : ℝ => ell (y : AngCircle))
    Vrem h A B C D hpot (angSec (angEquiv x))
  rw [hc] at hcos hsin
  have hcosval := quasiCos_coe_EX009 h A B C D (angSec (angEquiv x))
  have hsinval := quasiSin_coe_EX009 h A B C D (angSec (angEquiv x))
  rw [hc] at hcosval hsinval
  constructor
  · rw [physical_generator_transport_all_EX009 Z ell _ hell (smooth_quasiCos_EX009 h A B C D),
      hqc]
    unfold normalizedGroundAngular_EX009
    rw [hcosval, hsinval]
    linear_combination (a0 * Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2)) * hcos
  · rw [physical_generator_transport_all_EX009 Z ell _ hell (smooth_quasiSin_EX009 h A B C D),
      hqs]
    unfold normalizedGroundAngular_EX009
    rw [hcosval, hsinval]
    linear_combination (a0 * Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2)) * hsin


theorem two_column_norm_bound_EX009 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f g : E) {K : ℝ} (hK : 0 ≤ K)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K) (y : Fin 2 → ℝ) :
    ‖twoColumnMap_EX009 f g y‖ ≤ 2 * K * Real.sqrt (twoNormSq_EX009 y) := by
  have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
  have hs := Real.sq_sqrt hn
  have h0 : |y 0| ≤ Real.sqrt (twoNormSq_EX009 y) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, hs]
    unfold twoNormSq_EX009
    nlinarith [sq_nonneg (y 1)]
  have h1 : |y 1| ≤ Real.sqrt (twoNormSq_EX009 y) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, hs]
    unfold twoNormSq_EX009
    nlinarith [sq_nonneg (y 0)]
  calc
    _ ≤ ‖y 0 • f‖ + ‖y 1 • g‖ := norm_add_le _ _
    _ = |y 0| * ‖f‖ + |y 1| * ‖g‖ := by rw [norm_smul, norm_smul]; rfl
    _ ≤ |y 0| * K + |y 1| * K := add_le_add
      (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
    _ ≤ _ := by nlinarith

theorem normalized_column_gram_EX009 {w : Torus 1 → ℝ} {c C Z : ℝ}
    (hw : Measurable w) (hc : 0 < c)
    (hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C) (hZ : 0 < Z)
    (ell : AngCircle → ℝ) (h A B Cc D : ℝ)
    (hwexp : ∀ x, w x = Real.exp (ell (angEquiv x)) / Z)
    (f g : Hw 1 w)
    (hf : (f : Torus 1 → ℝ) =ᵐ[haar 1]
      normalizedGroundAngular_EX009 Z ell (quasiCos_EX009 h A B Cc D) ∘ angEquiv)
    (hg : (g : Torus 1 → ℝ) =ᵐ[haar 1]
      normalizedGroundAngular_EX009 Z ell (quasiSin_EX009 h A B Cc D) ∘ angEquiv)
    (y : Fin 2 → ℝ) :
    ‖twoColumnMap_EX009 f g y‖ ^ 2 =
      ∫ theta, (y 0 * quasiCos_EX009 h A B Cc D theta +
        y 1 * quasiSin_EX009 h A B Cc D theta) ^ 2 ∂angHaar := by
  have hxy := two_column_coe_EX009 hc hwb f g _ _ hf hg y
  have hx : ((twoColumnMap_EX009 f g y : Hw 1 w) : Torus 1 → ℝ) =ᵐ[haar 1]
      fun x => Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (y 0 * quasiCos_EX009 h A B Cc D (angEquiv x) +
          y 1 * quasiSin_EX009 h A B Cc D (angEquiv x)) := by
    filter_upwards [hxy] with x hxx
    rw [hxx]
    unfold Function.comp normalizedGroundAngular_EX009
    ring
  have he := normalized_tests_inner_EX009 hw hc hwb hZ ell
    (fun theta => y 0 * quasiCos_EX009 h A B Cc D theta +
      y 1 * quasiSin_EX009 h A B Cc D theta)
    (fun theta => y 0 * quasiCos_EX009 h A B Cc D theta +
      y 1 * quasiSin_EX009 h A B Cc D theta)
    hwexp (twoColumnMap_EX009 f g y) (twoColumnMap_EX009 f g y) hx hx
  rw [real_inner_self_eq_norm_sq] at he
  simpa only [pow_two] using he


theorem actual_quasimode_columns_EX009 {w : Torus 1 → ℝ} {c C Z : ℝ}
    (ell : AngCircle → ℝ) (hell : IsSmoothAngular ell) (hZ : 0 < Z)
    (hwexp : ∀ x, w x = Real.exp (ell (angEquiv x)) / Z)
    (hwd : DGPS.Lipschitz.WeightedGenerator.WData 1 w (smoothGrad (ell ∘ angEquiv)) c C)
    {e : HilbertBasis ℕ ℝ (Hw 1 w)} {lam : ℕ → ℝ}
    {G : ℕ → Torus 1 → Tangent 1} (hsd : SpectralData w e lam G)
    {h A B Cc D K : ℝ} (hh : |h| ≤ 1) (hK : 1 ≤ K)
    (hGram : gramControl_EX009 ![A, B, Cc, D] ≤ K)
    (Vrem : ℝ → ℝ)
    (hpot : ∀ x, schrodingerPotential_EX009 (fun y : ℝ => ell (y : AngCircle)) x =
      h * firstPotential_EX009 A B x + h ^ 2 * secondPotential_EX009 A B Cc D x +
        h ^ 3 * Vrem x)
    (hresBound : ∀ (theta : AngCircle) (i : Fin 2),
      |residualCoefficients_EX009 ![A, B, Cc, D] h theta (Vrem (angSec theta)) i| ≤ K) :
    ∃ X R : (Fin 2 → ℝ) →ₗ[ℝ] Hw 1 w,
      (∀ y, twoNormSq_EX009 y / 2 ≤ ‖X y‖ ^ 2) ∧
      (∀ y, |‖X y‖ ^ 2 - twoNormSq_EX009 y / 2| ≤ K * h ^ 2 * twoNormSq_EX009 y) ∧
      (∀ y, ‖X y‖ ≤ (K + 1) * Real.sqrt (twoNormSq_EX009 y)) ∧
      (∀ y, ‖R y‖ ≤ (2 * a0 * K * |h| ^ 3) * Real.sqrt (twoNormSq_EX009 y)) ∧
      (∀ y j, lam j * ⟪e j, X y⟫_ℝ = a0 * ⟪e j, X y⟫_ℝ +
        (a0 * h ^ 2) * ⟪e j, X (clusterMatrix_EX009 A B Cc D y)⟫_ℝ +
          ⟪e j, R y⟫_ℝ) := by
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  let pc := normalizedGroundAngular_EX009 Z ell (quasiCos_EX009 h A B Cc D)
  let ps := normalizedGroundAngular_EX009 Z ell (quasiSin_EX009 h A B Cc D)
  have hpc := smooth_normalized_ground_EX009 Z hell (smooth_quasiCos_EX009 h A B Cc D)
  have hps := smooth_normalized_ground_EX009 Z hell (smooth_quasiSin_EX009 h A B Cc D)
  obtain ⟨fc, Ac, hfc, hAc, hcoeffC⟩ :=
    smooth_test_spectral_coefficients_EX009 ell pc hell hpc hwd hsd
  obtain ⟨fs, As, hfs, hAs, hcoeffS⟩ :=
    smooth_test_spectral_coefficients_EX009 ell ps hell hps hwd hsd
  let m11 := (A ^ 2 + B ^ 2) / 6 - Cc
  let m22 := (A ^ 2 + B ^ 2) / 6 + Cc
  let rc := Ac - (a0 * (1 + h ^ 2 * m11)) • fc + (a0 * h ^ 2 * D) • fs
  let rs := As + (a0 * h ^ 2 * D) • fc - (a0 * (1 + h ^ 2 * m22)) • fs
  let X := twoColumnMap_EX009 fc fs
  let R := twoColumnMap_EX009 rc rs
  have hwb : ∀ᵐ x ∂haar 1, c ≤ w x ∧ w x ≤ C :=
    Filter.Eventually.of_forall hwd.bound
  have hrcAE : (rc : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (a0 * h ^ 3 * residualCoefficients_EX009 ![A, B, Cc, D] h (angEquiv x)
          (Vrem (angSec (angEquiv x))) 0) := by
    filter_upwards [ae_eq_haar hwd.pos hwb (Lp.coeFn_add
      (Ac - (a0 * (1 + h ^ 2 * m11)) • fc) ((a0 * h ^ 2 * D) • fs)),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_sub Ac ((a0 * (1 + h ^ 2 * m11)) • fc)),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_smul (a0 * (1 + h ^ 2 * m11)) fc),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_smul (a0 * h ^ 2 * D) fs),
      hfc, hfs, hAc] with x ha hb hc hd hfx hgx hAx
    change ((Ac - (a0 * (1 + h ^ 2 * m11)) • fc + (a0 * h ^ 2 * D) • fs :
      Hw 1 w) : Torus 1 → ℝ) x = _
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha hb hc hd
    rw [ha, hb, hc, hd, hfx, hgx, hAx]
    simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, pc, ps, m11] using
      (physical_quasi_residual_EX009 Z ell hell Vrem h A B Cc D hpot x).1
  have hrsAE : (rs : Torus 1 → ℝ) =ᵐ[haar 1] fun x =>
      Real.sqrt Z * Real.exp (-ell (angEquiv x) / 2) *
        (a0 * h ^ 3 * residualCoefficients_EX009 ![A, B, Cc, D] h (angEquiv x)
          (Vrem (angSec (angEquiv x))) 1) := by
    filter_upwards [ae_eq_haar hwd.pos hwb (Lp.coeFn_sub
      (As + (a0 * h ^ 2 * D) • fc) ((a0 * (1 + h ^ 2 * m22)) • fs)),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_add As ((a0 * h ^ 2 * D) • fc)),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_smul (a0 * h ^ 2 * D) fc),
      ae_eq_haar hwd.pos hwb (Lp.coeFn_smul (a0 * (1 + h ^ 2 * m22)) fs),
      hfc, hfs, hAs] with x ha hb hc hd hfx hgx hAx
    change ((As + (a0 * h ^ 2 * D) • fc - (a0 * (1 + h ^ 2 * m22)) • fs :
      Hw 1 w) : Torus 1 → ℝ) x = _
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha hb hc hd
    rw [ha, hb, hc, hd, hfx, hgx, hAx]
    simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, pc, ps, m22] using
      (physical_quasi_residual_EX009 Z ell hell Vrem h A B Cc D hpot x).2
  have hqbound (theta : AngCircle) (i : Fin 2) :
      |a0 * h ^ 3 * residualCoefficients_EX009 ![A, B, Cc, D] h theta
        (Vrem (angSec theta)) i| ≤ a0 * K * |h| ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_pos DGPS.Circle.AngularNormalization.a0_pos, abs_pow]
    have he := mul_le_mul_of_nonneg_left (hresBound theta i)
      (by positivity : 0 ≤ a0 * |h| ^ 3)
    nlinarith only [he]
  have hrc : ‖rc‖ ≤ a0 * K * |h| ^ 3 :=
    normalized_test_norm_bound_EX009 hwd.meas hwd.pos hwb hZ ell _ (by positivity)
      hwexp rc hrcAE (fun theta => hqbound theta 0)
  have hrs : ‖rs‖ ≤ a0 * K * |h| ^ 3 :=
    normalized_test_norm_bound_EX009 hwd.meas hwd.pos hwb hZ ell _ (by positivity)
      hwexp rs hrsAE (fun theta => hqbound theta 1)
  have hgram (y : Fin 2 → ℝ) :
      ‖X y‖ ^ 2 = ∫ theta, (y 0 * quasiCos_EX009 h A B Cc D theta +
        y 1 * quasiSin_EX009 h A B Cc D theta) ^ 2 ∂angHaar :=
    normalized_column_gram_EX009 hwd.meas hwd.pos hwb hZ ell h A B Cc D hwexp
      fc fs hfc hfs y
  have hlow (y : Fin 2 → ℝ) : twoNormSq_EX009 y / 2 ≤ ‖X y‖ ^ 2 := by
    rw [hgram]
    exact quasi_gram_lower_EX009 h A B Cc D (y 0) (y 1)
  have herror (y : Fin 2 → ℝ) :
      |‖X y‖ ^ 2 - twoNormSq_EX009 y / 2| ≤ K * h ^ 2 * twoNormSq_EX009 y := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hlow y)), hgram]
    have he := quasi_gram_upper_error_EX009 hh A B Cc D (y 0) (y 1)
    have hm := mul_le_mul_of_nonneg_left hGram
      (by unfold twoNormSq_EX009; positivity : 0 ≤ h ^ 2 * twoNormSq_EX009 y)
    dsimp [gramControl_EX009, twoNormSq_EX009] at hm ⊢
    nlinarith
  refine ⟨X, R, hlow, herror, ?_, ?_, ?_⟩
  · intro y
    apply norm_le_sqrt_coordinate_EX009 _ y (by linarith : 0 ≤ K + 1)
    have hh2 : h ^ 2 ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
    have he := (abs_le.mp (herror y)).2
    have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
    have hmul := mul_le_mul_of_nonneg_right hh2 (mul_nonneg (by linarith) hn)
    have hcoef : K + 1 / 2 ≤ (K + 1) ^ 2 := by nlinarith
    have hc := mul_le_mul_of_nonneg_right hcoef hn
    nlinarith
  · intro y
    have he := two_column_norm_bound_EX009 rc rs (by positivity) hrc hrs y
    dsimp [R]
    convert he using 1
    ring
  · intro y j
    have hc := hcoeffC j
    have hs := hcoeffS j
    dsimp [X, R, twoColumnMap_EX009, clusterMatrix_EX009, rc, rs]
    simp only [inner_add_right, inner_sub_right, inner_smul_right]
    dsimp [m11, m22] at *
    linear_combination (y 0) * hc + (y 1) * hs


set_option maxHeartbeats 1000000 in
theorem pointwise_cluster_estimate_EX009 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : HilbertBasis ℕ ℝ E) (lam : ℕ → ℝ)
    (X R : (Fin 2 → ℝ) →ₗ[ℝ] E)
    (A B C D : ℝ) {h K : ℝ} (hh : |h| ≤ 1) (hK : 1 ≤ K)
    (hzero : lam 0 = 0) (hmono : Monotone lam) (hthird : 3 * a0 < lam 3)
    (hmatrix : matrixControl_EX009 ![A, B, C, D] ≤ K ^ 2)
    (hminimum : |modelMinimum_EX009 ![A, B, C, D]| ≤ K)
    (hmaximum : |modelMaximum_EX009 ![A, B, C, D]| ≤ K)
    (hlow : ∀ y, twoNormSq_EX009 y / 2 ≤ ‖X y‖ ^ 2)
    (hgram : ∀ y, |‖X y‖ ^ 2 - twoNormSq_EX009 y / 2| ≤ K * h ^ 2 * twoNormSq_EX009 y)
    (hX : ∀ y, ‖X y‖ ≤ (K + 1) * Real.sqrt (twoNormSq_EX009 y))
    (hR : ∀ y, ‖R y‖ ≤ (2 * a0 * K * |h| ^ 3) * Real.sqrt (twoNormSq_EX009 y))
    (hres : ∀ y j, lam j * ⟪e j, X y⟫_ℝ = a0 * ⟪e j, X y⟫_ℝ +
      (a0 * h ^ 2) * ⟪e j, X (clusterMatrix_EX009 A B C D y)⟫_ℝ + ⟪e j, R y⟫_ℝ)
    (hsmall : (K * (K + 3)) ^ 2 * h ^ 4 ≤ 1 / 4) :
    let Kg := K + (K * (K + 3)) ^ 2
    let F := 4 * (2 * (K + 1) * K + Kg * (1 + K ^ 2) / 2 + K * Kg)
    |lam 1 - a0 * (1 + h ^ 2 * modelMinimum_EX009 ![A, B, C, D])| ≤
        a0 * F * |h| ^ 3 ∧
    |lam 2 - a0 * (1 + h ^ 2 * modelMaximum_EX009 ![A, B, C, D])| ≤
        a0 * F * |h| ^ 3 := by
  let M := clusterMatrix_EX009 A B C D
  let L := K + 1
  let B0 := K * (K + 3)
  let Kg := K + B0 ^ 2
  let E0 := 2 * L * K + Kg * (1 + K ^ 2) / 2
  let F := 4 * (E0 + K * Kg)
  let t := a0 * h ^ 2
  let Base : (Fin 2 → ℝ) →ₗ[ℝ] E := t • (X.comp M) + R
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  have hK0 : 0 ≤ K := by linarith
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hKg : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hE0 : 0 ≤ E0 := by dsimp [E0]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hh2 : h ^ 2 ≤ 1 := by nlinarith [sq_abs h, abs_nonneg h]
  have hh3 : |h| ^ 3 ≤ h ^ 2 := by nlinarith [sq_abs h, abs_nonneg h]
  have hh4 : h ^ 4 ≤ |h| ^ 3 := by nlinarith [sq_abs h, abs_nonneg h]
  have hM (y : Fin 2 → ℝ) : twoNormSq_EX009 (M y) ≤ K ^ 2 * twoNormSq_EX009 y := by
    exact (cluster_matrix_norm_EX009 A B C D y).trans
      (mul_le_mul_of_nonneg_right hmatrix (by unfold twoNormSq_EX009; positivity))
  have hbase (y : Fin 2 → ℝ) (j : ℕ) :
      (lam j - a0) * ⟪e j, X y⟫_ℝ = ⟪e j, Base y⟫_ℝ := by
    simp only [Base, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, inner_add_right, inner_smul_right]
    have he := hres y j
    dsimp [t, M] at *
    linarith
  have hbaseNorm (y : Fin 2 → ℝ) :
      ‖Base y‖ ≤ a0 * (B0 * h ^ 2) * Real.sqrt (twoNormSq_EX009 y) := by
    have hXM : ‖X (M y)‖ ≤ L * K * Real.sqrt (twoNormSq_EX009 y) := by
      calc
        _ ≤ L * Real.sqrt (twoNormSq_EX009 (M y)) := hX (M y)
        _ ≤ L * (K * Real.sqrt (twoNormSq_EX009 y)) :=
          mul_le_mul_of_nonneg_left (sqrt_coordinate_map_EX009 M hK0 hM y) hL
        _ = _ := by ring
    calc
      _ ≤ ‖t • X (M y)‖ + ‖R y‖ := norm_add_le _ _
      _ ≤ t * (L * K * Real.sqrt (twoNormSq_EX009 y)) +
          (2 * a0 * K * |h| ^ 3) * Real.sqrt (twoNormSq_EX009 y) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
        exact add_le_add (mul_le_mul_of_nonneg_left hXM ht) (hR y)
      _ ≤ a0 * (B0 * h ^ 2) * Real.sqrt (twoNormSq_EX009 y) := by
        have hm := mul_le_mul_of_nonneg_right hh3
          (by positivity : 0 ≤ 2 * a0 * K * Real.sqrt (twoNormSq_EX009 y))
        dsimp [t, L, B0]
        nlinarith only [hm]
  obtain ⟨hprojLow, hprojGram, henergy⟩ :=
    projected_cluster_data_EX009 e lam X M R Base ha ht (by positivity)
      hL (outside_cluster_gap_EX009 lam hzero hmono hthird) hres hbase hbaseNorm
      hlow hgram hX hM hR
  let T := spectralCoordinates_EX009 e X
  have hGramLow (y : Fin 2 → ℝ) :
      twoNormSq_EX009 y / 4 ≤ twoNormSq_EX009 (T y) := by
    have he := hprojLow y
    have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
    have hm := mul_le_mul_of_nonneg_right hsmall hn
    dsimp [B0] at he
    nlinarith
  have hGram (y : Fin 2 → ℝ) :
      |twoNormSq_EX009 (T y) - twoNormSq_EX009 y / 2| ≤
        (Kg * h ^ 2) * twoNormSq_EX009 y := by
    have he := hprojGram y
    have hh4' : h ^ 4 ≤ h ^ 2 := by nlinarith [sq_nonneg h]
    have hm := mul_le_mul_of_nonneg_right hh4'
      (by unfold twoNormSq_EX009; positivity : 0 ≤ B0 ^ 2 * twoNormSq_EX009 y)
    dsimp [Kg] at *
    nlinarith
  have hEnergy (y : Fin 2 → ℝ) :
      |lam 1 * (T y) 0 ^ 2 + lam 2 * (T y) 1 ^ 2 -
        a0 * twoNormSq_EX009 (T y) - t * dotTwo_EX009 y (M y) / 2| ≤
          (a0 * E0 * |h| ^ 3) * twoNormSq_EX009 y := by
    have he := henergy y
    have hn : 0 ≤ twoNormSq_EX009 y := by unfold twoNormSq_EX009; positivity
    have heta : K * h ^ 2 + (B0 * h ^ 2) ^ 2 ≤ Kg * h ^ 2 := by
      have hh4' : h ^ 4 ≤ h ^ 2 := by nlinarith [sq_nonneg h]
      have hm := mul_le_mul_of_nonneg_left hh4' (sq_nonneg B0)
      dsimp [Kg]
      nlinarith
    have h1 := mul_le_mul_of_nonneg_left heta
      (by positivity : 0 ≤ a0 * h ^ 2 * (1 + K ^ 2) / 2 * twoNormSq_EX009 y)
    have h2 := mul_le_mul_of_nonneg_right hh4
      (by positivity : 0 ≤ a0 * Kg * (1 + K ^ 2) / 2 * twoNormSq_EX009 y)
    dsimp [t, E0, L] at *
    nlinarith
  let p : Fin 4 → ℝ := ![A, B, C, D]
  have hQ (y : Fin 2 → ℝ) :
      modelMinimum_EX009 p * twoNormSq_EX009 y ≤ dotTwo_EX009 y (M y) ∧
      dotTwo_EX009 y (M y) ≤ modelMaximum_EX009 p * twoNormSq_EX009 y := by
    rw [cluster_matrix_quadratic_EX009]
    have he := cluster_quadratic_bounds_EX009 C D (y 0) (y 1)
    dsimp [modelMinimum_EX009, modelMaximum_EX009, p, twoNormSq_EX009] at *
    constructor <;> nlinarith
  obtain ⟨u0, v0, u1, v1, hv0, hv1, hq0, hq1⟩ :=
    cluster_quadratic_extremizers_EX009 C D
  let vlo : Fin 2 → ℝ := ![u0, v0]
  let vhi : Fin 2 → ℝ := ![u1, v1]
  have hQlo : dotTwo_EX009 vlo (M vlo) = modelMinimum_EX009 p * twoNormSq_EX009 vlo := by
    rw [cluster_matrix_quadratic_EX009]
    dsimp [vlo, p, modelMinimum_EX009, twoNormSq_EX009]
    nlinarith only [hq0]
  have hQhi : dotTwo_EX009 vhi (M vhi) = modelMaximum_EX009 p * twoNormSq_EX009 vhi := by
    rw [cluster_matrix_quadratic_EX009]
    dsimp [vhi, p, modelMaximum_EX009, twoNormSq_EX009]
    nlinarith only [hq1]
  have he := finite_rayleigh_comparison_EX009 T (fun y => dotTwo_EX009 y (M y))
    (lam 1) (lam 2) a0 t (a0 * E0 * |h| ^ 3) (Kg * h ^ 2) K
    (modelMinimum_EX009 p) (modelMaximum_EX009 p)
    ht (by positivity) (by positivity) hK0 (hmono (by norm_num))
    hminimum hmaximum hQ vlo vhi hv0 hv1 hQlo hQhi hGramLow hGram hEnergy
  have hlast :
      4 * (a0 * E0 * |h| ^ 3 + t * K * (Kg * h ^ 2)) ≤ a0 * F * |h| ^ 3 := by
    have hm := mul_le_mul_of_nonneg_right hh4 (by positivity : 0 ≤ 4 * a0 * K * Kg)
    dsimp [t, F]
    nlinarith only [hm]
  dsimp only
  constructor
  · have hb := he.1.trans hlast
    have hc : a0 + t * modelMinimum_EX009 p =
        a0 * (1 + h ^ 2 * modelMinimum_EX009 p) := by dsimp [t]; ring
    rw [hc] at hb
    simpa only [p, F, E0, Kg, B0, L] using hb
  · have hb := he.2.trans hlast
    have hc : a0 + t * modelMaximum_EX009 p =
        a0 * (1 + h ^ 2 * modelMaximum_EX009 p) := by dsimp [t]; ring
    rw [hc] at hb
    simpa only [p, F, E0, Kg, B0, L] using hb


theorem jet_log_height_EX009 (ell : AngCircle → ℝ) {h A B C D M R : ℝ}
    (hh : |h| ≤ 1) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hA : |A| ≤ M) (hB : |B| ≤ M) (hC : |C| ≤ M) (hD : |D| ≤ M)
    (hjet : c2JetError_EX009 ell h A B C D R) (theta : AngCircle) :
    |ell theta| ≤ (4 * M + R) * |h| := by
  let x := angSec theta
  have hco : ((x : ℝ) : AngCircle) = theta := AddCircle.coe_equivIoc
  have hlin (a b y : ℝ) (ha : |a| ≤ M) (hb : |b| ≤ M) :
      |a * Real.cos y + b * Real.sin y| ≤ 2 * M := by
    calc
      _ ≤ |a * Real.cos y| + |b * Real.sin y| := abs_add_le _ _
      _ ≤ M * 1 + M * 1 := add_le_add
        (by rw [abs_mul]; exact mul_le_mul ha (Real.abs_cos_le_one _) (abs_nonneg _) hM)
        (by rw [abs_mul]; exact mul_le_mul hb (Real.abs_sin_le_one _) (abs_nonneg _) hM)
      _ = _ := by ring
  have hh2 : h ^ 2 ≤ |h| := by nlinarith [sq_abs h, abs_nonneg h]
  have hh3 : |h| ^ 3 ≤ |h| := by nlinarith [sq_abs h, abs_nonneg h]
  have hlog : |harmonicLog_EX009 h A B C D x| ≤ 4 * M * |h| := by
    unfold harmonicLog_EX009
    calc
      _ ≤ |h * (A * Real.cos x + B * Real.sin x)| +
        |h ^ 2 * (C * Real.cos (2 * x) + D * Real.sin (2 * x))| := abs_add_le _ _
      _ ≤ |h| * (2 * M) + h ^ 2 * (2 * M) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg h)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hlin A B x hA hB) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hlin C D (2 * x) hC hD) (sq_nonneg h))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hh2 (by positivity : 0 ≤ 2 * M)]
  have herr := (hjet x).1
  rw [hco] at herr
  have he : |ell theta| ≤ |ell theta - harmonicLog_EX009 h A B C D x| +
      |harmonicLog_EX009 h A B C D x| := by
    calc
      |ell theta| = |(ell theta - harmonicLog_EX009 h A B C D x) +
          harmonicLog_EX009 h A B C D x| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hm := mul_le_mul_of_nonneg_left hh3 hR
  linarith

noncomputable def logHeightThreshold_EX009 : ℝ := Real.log (4 / 3 : ℝ) / 8

theorem log_height_threshold_pos_EX009 : 0 < logHeightThreshold_EX009 := by
  unfold logHeightThreshold_EX009
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem log_height_density_close_EX009 :
    3 * Real.exp (2 * logHeightThreshold_EX009) <
      4 * Real.exp (-(2 * logHeightThreshold_EX009)) := by
  have hp : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have he : Real.exp (4 * logHeightThreshold_EX009) < 4 / 3 := by
    calc
      _ < Real.exp (Real.log (4 / 3 : ℝ)) := Real.exp_lt_exp.mpr (by
        unfold logHeightThreshold_EX009
        linarith)
      _ = _ := Real.exp_log (by norm_num)
  have hratio : Real.exp (2 * logHeightThreshold_EX009) /
      Real.exp (-(2 * logHeightThreshold_EX009)) < 4 / 3 := by
    rw [← Real.exp_sub]
    have hexp : 2 * logHeightThreshold_EX009 - -(2 * logHeightThreshold_EX009) =
        4 * logHeightThreshold_EX009 := by ring
    rw [hexp]
    exact he
  have hm := (div_lt_iff₀ (Real.exp_pos (-(2 * logHeightThreshold_EX009)))).mp hratio
  nlinarith


/-- Every smooth Haar-mean-zero chart gives a native smooth probability with
exactly that normalized logarithm and the same weighted density. -/
theorem chart_probability_equivalence_EX009 (ell : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (hmean : ∫ theta, ell theta ∂angHaar = 0) :
    ∃ (Z : ℝ) (rho : AngCircle → ℝ) (P : ProbabilityMeasure AngCircle),
      0 < Z ∧ IsSmoothAngular rho ∧ (∀ theta, 0 < rho theta) ∧
      (∀ theta, rho theta = Real.exp (ell theta) / Z) ∧
      ((P : ProbabilityMeasure AngCircle) : Measure AngCircle) =
        angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta)) ∧
      angularGibbs_EX009 ell = rho ∘ angEquiv ∧
      normalizedLogDensity_EX009 rho = ell := by
  have hc := ((isSmoothPeriodic_comp_iff ell).2 hell).continuous_torus
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  have hbound (theta : AngCircle) : |ell theta| ≤ M := by
    have hb := hM (angEquiv.symm theta) (Set.mem_univ _)
    simpa only [Function.comp_apply, angEquiv.apply_symm_apply, Real.norm_eq_abs] using hb
  obtain ⟨Z, hZ, hwexp, hmass, _hwd⟩ := angular_gibbs_data_EX009 ell hell M hbound
  let rho : AngCircle → ℝ := fun theta => Real.exp (ell theta) / Z
  have hrho : IsSmoothAngular rho := hell.exp.div_const Z
  have hpos (theta : AngCircle) : 0 < rho theta := div_pos (Real.exp_pos _) hZ
  have hint : ∫ theta, rho theta ∂angHaar = 1 := by
    calc
      _ = ∫ x, rho (angEquiv x) ∂haar 1 := (integral_comp_angEquiv rho).symm
      _ = ∫ x, angularGibbs_EX009 ell x ∂haar 1 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => (hwexp x).symm
      _ = 1 := hmass
  let P : ProbabilityMeasure AngCircle :=
    ⟨angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta)),
      density_probability_EX009 rho hrho hpos hint⟩
  refine ⟨Z, rho, P, hZ, hrho, hpos, (fun _ => rfl), rfl, ?_, ?_⟩
  · exact funext hwexp
  · exact chart_normalized_log_EX009 ell hell hmean hZ

theorem normalized_log_jet_transport_EX009 (ell : AngCircle → ℝ)
    (hell : IsSmoothAngular ell) (hmean : ∫ theta, ell theta ∂angHaar = 0)
    {Z : ℝ} (hZ : 0 < Z) (h A B C D R : ℝ) :
    c2JetError_EX009
      (normalizedLogDensity_EX009 (fun theta => Real.exp (ell theta) / Z))
      h A B C D R ↔ c2JetError_EX009 ell h A B C D R := by
  rw [chart_normalized_log_EX009 ell hell hmean hZ]

def FirstClusterConclusion_EX009 (w : Torus 1 → ℝ)
    (p : Fin 4 → ℝ) (h F : ℝ) : Prop :=
  ∃ (e : HilbertBasis ℕ ℝ (Hw 1 w)) (lam : ℕ → ℝ)
      (G : ℕ → Torus 1 → Tangent 1),
    SpectralData w e lam G ∧
    (((e 0 : Hw 1 w) : Torus 1 → ℝ) =ᵐ[wMeasure 1 w] fun _ => 1) ∧
    lam 0 = 0 ∧ Monotone lam ∧ Filter.Tendsto lam Filter.atTop Filter.atTop ∧
    a0 / 2 < lam 1 ∧ lam 2 < 2 * a0 ∧ 3 * a0 < lam 3 ∧
    |lam 1 / a0 - (1 + h ^ 2 * modelMinimum_EX009 p)| ≤ F * |h| ^ 3 ∧
    |lam 2 / a0 - (1 + h ^ 2 * modelMaximum_EX009 p)| ≤ F * |h| ^ 3

set_option maxHeartbeats 1000000 in
/-- Uniform auxiliary theorem on coefficient boxes.  The constants are fixed before
the log chart and the parameter; only an angular C2 error bound is used. -/
theorem uniform_box_cluster_EX009 {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ delta F : ℝ, 0 < delta ∧ 0 < F ∧
      ∀ (p : Fin 4 → ℝ) (ell : AngCircle → ℝ) (h : ℝ),
      (∀ i, |p i| ≤ M) → IsSmoothAngular ell →
      |h| ≤ delta → c2JetError_EX009 ell h (p 0) (p 1) (p 2) (p 3) R →
      FirstClusterConclusion_EX009 (angularGibbs_EX009 ell) p h F := by
  have ha := DGPS.Circle.AngularNormalization.a0_pos
  let Rp := R / 2 + 3 * (4 * M) ^ 2 / 4 + (4 * M) * R + R ^ 2 / 4
  have hRp : 0 ≤ Rp := by dsimp [Rp]; positivity
  obtain ⟨K, hK, hcontrol⟩ := uniform_quasimode_control_EX009 (M := M) hRp
  let B0 := K * (K + 3)
  let Kg := K + B0 ^ 2
  let F := 4 * (2 * (K + 1) * K + Kg * (1 + K ^ 2) / 2 + K * Kg)
  let delta := min 1 (min (logHeightThreshold_EX009 / (4 * M + R + 1))
    (min (1 / (2 * (B0 + 1))) (1 / (2 * (K + F + 1)))))
  have hK0 : 0 ≤ K := by linarith
  have hB0 : 0 ≤ B0 := by dsimp [B0]; positivity
  have hKg : 0 ≤ Kg := by dsimp [Kg]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (lt_min
      (div_pos log_height_threshold_pos_EX009 (by positivity))
      (lt_min (by positivity) (by positivity)))
  refine ⟨delta, F, hdelta, hF, ?_⟩
  intro p ell h hp hell hhd hjet
  have hh : |h| ≤ 1 := hhd.trans (min_le_left _ _)
  have hhHeight : |h| ≤ logHeightThreshold_EX009 / (4 * M + R + 1) :=
    hhd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhRank : |h| ≤ 1 / (2 * (B0 + 1)) :=
    hhd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhCluster : |h| ≤ 1 / (2 * (K + F + 1)) :=
    hhd.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hheight (theta : AngCircle) : |ell theta| ≤ logHeightThreshold_EX009 := by
    have he := jet_log_height_EX009 ell hh hM hR (hp 0) (hp 1) (hp 2) (hp 3) hjet theta
    have hm := (le_div_iff₀ (by positivity : 0 < 4 * M + R + 1)).mp hhHeight
    nlinarith [abs_nonneg h]
  obtain ⟨Z, hZ, hwexp, hmass, hwd⟩ :=
    angular_gibbs_data_EX009 ell hell logHeightThreshold_EX009 hheight
  have hwb : ∀ᵐ x ∂haar 1,
      Real.exp (-(2 * logHeightThreshold_EX009)) ≤ angularGibbs_EX009 ell x ∧
        angularGibbs_EX009 ell x ≤ Real.exp (2 * logHeightThreshold_EX009) :=
    Filter.Eventually.of_forall hwd.bound
  obtain ⟨e, lam, G, hsd, he0, hzero, hmono, htop, hfirst, hthird⟩ :=
    exists_separated_eigenbasis_EX009 hwd.meas hwd.pos hwb hmass log_height_density_close_EX009
  obtain ⟨Vrem, hpot, hVrem⟩ :=
    potential_jet_factor_EX009 ell hh hM hR (hp 0) (hp 1) (hp 2) (hp 3) hjet
  obtain ⟨hGram, hMatrix, hMin, hMax, hRes⟩ := hcontrol p hp
  have hpvec : ![p 0, p 1, p 2, p 3] = p := by
    ext i
    fin_cases i <;> rfl
  obtain ⟨X, Res, hlow, hgram, hX, hResidual, hcoeff⟩ :=
    actual_quasimode_columns_EX009 ell hell hZ hwexp hwd hsd hh hK
      (by simpa only [hpvec] using hGram) Vrem hpot (fun theta i => by
        simpa only [hpvec] using hRes h theta (Vrem (angSec theta)) i hh (hVrem _))
  have hh2 : h ^ 2 ≤ |h| := by nlinarith [sq_abs h, abs_nonneg h]
  have hsmall : (K * (K + 3)) ^ 2 * h ^ 4 ≤ 1 / 4 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (B0 + 1))).mp hhRank
    have hprod : 0 ≤ B0 * h ^ 2 ∧ B0 * h ^ 2 ≤ 1 / 2 := by
      constructor
      · positivity
      · have he := mul_le_mul_of_nonneg_left hh2 hB0
        nlinarith [abs_nonneg h]
    have hs := pow_le_pow_left₀ hprod.1 hprod.2 2
    dsimp [B0] at *
    nlinarith
  have he := pointwise_cluster_estimate_EX009 e lam X Res (p 0) (p 1) (p 2) (p 3)
    hh hK hzero hmono hthird
    (by simpa only [hpvec] using hMatrix)
    (by simpa only [hpvec] using hMin)
    (by simpa only [hpvec] using hMax)
    hlow hgram hX hResidual hcoeff hsmall
  have herrors :
      |lam 1 - a0 * (1 + h ^ 2 * modelMinimum_EX009 p)| ≤ a0 * F * |h| ^ 3 ∧
      |lam 2 - a0 * (1 + h ^ 2 * modelMaximum_EX009 p)| ≤ a0 * F * |h| ^ 3 := by
    simpa only [hpvec, F, Kg, B0] using he
  have hsecond : lam 2 < 2 * a0 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (K + F + 1))).mp hhCluster
    have hh3 : |h| ^ 3 ≤ |h| := by nlinarith [sq_abs h, abs_nonneg h]
    have hm0 : modelMaximum_EX009 p ≤ K := (le_abs_self _).trans hMax
    have he0 := (abs_le.mp herrors.2).2
    have he1 := mul_le_mul_of_nonneg_left hm0
      (by positivity : 0 ≤ a0 * h ^ 2)
    have he2 := mul_le_mul_of_nonneg_left hh2
      (by positivity : 0 ≤ a0 * K)
    have he3 := mul_le_mul_of_nonneg_left hh3
      (by positivity : 0 ≤ a0 * F)
    have he4 := mul_le_mul_of_nonneg_left hm DGPS.Circle.AngularNormalization.a0_pos.le
    have hp : 0 ≤ a0 * |h| := mul_nonneg ha.le (abs_nonneg h)
    nlinarith only [he0, he1, he2, he3, he4, ha, hp]
  refine ⟨e, lam, G, hsd, he0, hzero, hmono, htop, hfirst, hsecond, hthird, ?_, ?_⟩
  · have hd : lam 1 / a0 - (1 + h ^ 2 * modelMinimum_EX009 p) =
        (lam 1 - a0 * (1 + h ^ 2 * modelMinimum_EX009 p)) / a0 := by
      rw [sub_div, mul_div_cancel_left₀ _ ha.ne']
    rw [hd, abs_div, abs_of_pos DGPS.Circle.AngularNormalization.a0_pos,
      div_le_iff₀ DGPS.Circle.AngularNormalization.a0_pos]
    nlinarith only [herrors.1]
  · have hd : lam 2 / a0 - (1 + h ^ 2 * modelMaximum_EX009 p) =
        (lam 2 - a0 * (1 + h ^ 2 * modelMaximum_EX009 p)) / a0 := by
      rw [sub_div, mul_div_cancel_left₀ _ ha.ne']
    rw [hd, abs_div, abs_of_pos DGPS.Circle.AngularNormalization.a0_pos,
      div_le_iff₀ DGPS.Circle.AngularNormalization.a0_pos]
    nlinarith only [herrors.2]


theorem compact_coefficient_box_EX009 (S : Set (Fin 4 → ℝ)) (hS : IsCompact S) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ S, ∀ i, |p i| ≤ M := by
  have hf : Continuous (fun p : Fin 4 → ℝ => ∑ i, |p i|) := by fun_prop
  obtain ⟨M0, hbound⟩ := hS.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M0 0, le_max_right _ _, ?_⟩
  intro p hp i
  have hs : |p i| ≤ ∑ j, |p j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (p j)) (Finset.mem_univ i)
  have hb : |(∑ j, |p j|)| ≤ M0 := by
    simpa only [Real.norm_eq_abs] using hbound p hp
  exact hs.trans ((le_abs_self _).trans (hb.trans (le_max_left _ _)))

/-- Pointwise native-probability form of the same uniform estimate. -/
theorem uniform_probability_pointwise_EX009
    (S : Set (Fin 4 → ℝ)) (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R) :
    ∃ delta F : ℝ, 0 < delta ∧ 0 < F ∧
      ∀ p ∈ S, ∀ (P : ProbabilityMeasure AngCircle) (rho : AngCircle → ℝ) (h : ℝ),
      IsSmoothAngular rho → (∀ theta, 0 < rho theta) →
      ((P : ProbabilityMeasure AngCircle) : Measure AngCircle) =
        angHaar.withDensity (fun theta => ENNReal.ofReal (rho theta)) →
      |h| ≤ delta →
      c2JetError_EX009 (normalizedLogDensity_EX009 rho) h (p 0) (p 1) (p 2) (p 3) R →
      FirstClusterConclusion_EX009 (rho ∘ angEquiv) p h F := by
  obtain ⟨M, hM, hbox⟩ := compact_coefficient_box_EX009 S hS
  obtain ⟨delta, F, hdelta, hF, hcluster⟩ := uniform_box_cluster_EX009 hM hR
  refine ⟨delta, F, hdelta, hF, ?_⟩
  intro p hp P rho h hrho hpos hmeasure hh hjet
  have hmass := probability_density_mass_EX009 P rho hrho hpos hmeasure
  have he := hcluster p (normalizedLogDensity_EX009 rho) h (hbox p hp)
    (smooth_normalized_log_EX009 rho hrho hpos) hh hjet
  rwa [normalized_log_density_EX009 rho hpos hmass] at he

end DGPS.Circle.FirstClusterPerturbation

namespace DGPS.Examples

open MeasureTheory
open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent
open DGPS.Circle.AngularNormalization DGPS.Circle.FirstClusterPerturbation

/-- The canonical first-cluster expansion for smooth angular probabilities.
The constants are uniform on the compact coefficient set and the fixed angular
C2 remainder bound, and precede every probability family and its parameter window.
No regularity in the parameter is assumed.  The logarithm is Haar-mean-zero;
the conclusion concerns the original probability density. -/
theorem first_harmonic_spectral_cluster_expansion
    (S : Set (Fin 4 → ℝ)) (hS : IsCompact S) {R : ℝ} (hR : 0 ≤ R) :
    ∃ delta F : ℝ, 0 < delta ∧ 0 < F ∧
      ∀ (p : Fin 4 → ℝ), p ∈ S →
      ∀ (P : ℝ → ProbabilityMeasure AngCircle) (rho : ℝ → AngCircle → ℝ)
        (hwin : ℝ), 0 < hwin →
      (∀ h, |h| ≤ hwin →
        IsSmoothAngular (rho h) ∧ (∀ theta, 0 < rho h theta) ∧
        ((P h : ProbabilityMeasure AngCircle) : Measure AngCircle) =
          angHaar.withDensity (fun theta => ENNReal.ofReal (rho h theta))) →
      (∀ h, |h| ≤ hwin →
        c2JetError_EX009 (normalizedLogDensity_EX009 (rho h)) h
          (p 0) (p 1) (p 2) (p 3) R) →
      ∀ h, |h| ≤ min delta hwin →
        FirstClusterConclusion_EX009 (rho h ∘ angEquiv) p h F := by
  obtain ⟨M, hM, hbox⟩ := compact_coefficient_box_EX009 S hS
  obtain ⟨delta, F, hdelta, hF, hcluster⟩ := uniform_box_cluster_EX009 hM hR
  refine ⟨delta, F, hdelta, hF, ?_⟩
  intro p hp P rho hwin _hwin hprob hjet h hh
  have hwindow : |h| ≤ hwin := hh.trans (min_le_right _ _)
  obtain ⟨hsmooth, hpos, hmeasure⟩ := hprob h hwindow
  have hmass := probability_density_mass_EX009 (P h) (rho h) hsmooth hpos hmeasure
  have hell := smooth_normalized_log_EX009 (rho h) hsmooth hpos
  have he := hcluster p (normalizedLogDensity_EX009 (rho h)) h
    (hbox p hp) hell (hh.trans (min_le_left _ _)) (hjet h hwindow)
  rwa [normalized_log_density_EX009 (rho h) hpos hmass] at he

end DGPS.Examples
