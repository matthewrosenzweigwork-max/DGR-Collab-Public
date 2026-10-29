import FullLabeledLSI.Examples.E01h3_Conv

/-!
# Lane D, Task B3 (part 3): the cross term `σ(C'(· - x) · (C' * σ))` as a double series
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

variable (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β] (x : Torus 1)

theorem cI_dist (j k : ℕ) :
    cI α β x (2 * (k : ℤ) - 2 * (j : ℤ)) = cI α β x (2 * ((Nat.dist j k : ℕ) : ℤ)) := by
  rcases le_total j k with h | h
  · rw [Nat.dist_eq_sub_of_le h]; push_cast [Nat.cast_sub h]; ring_nf
  · rw [Nat.dist_eq_sub_of_le_right h]
    have : 2 * (k : ℤ) - 2 * (j : ℤ) = -(2 * ((j - k : ℕ) : ℤ)) := by push_cast [Nat.cast_sub h]; ring
    rw [this, cI_neg]

theorem sI_dist (j k : ℕ) :
    sI α β x (2 * (k : ℤ) - 2 * (j : ℤ)) = sgnk j k * sI α β x (2 * ((Nat.dist j k : ℕ) : ℤ)) := by
  rcases lt_trichotomy j k with h | h | h
  · have h' := h.le
    rw [Nat.dist_eq_sub_of_le h']
    unfold sgnk; rw [if_pos h]
    push_cast [Nat.cast_sub h']; ring_nf
  · subst h; unfold sgnk; simp [sI_zero]
  · have h' := h.le
    rw [Nat.dist_eq_sub_of_le_right h']
    unfold sgnk; rw [if_neg (not_lt.2 h'), if_pos h]
    have : 2 * (k : ℤ) - 2 * (j : ℤ) = -(2 * ((j - k : ℕ) : ℤ)) := by push_cast [Nat.cast_sub h']; ring
    rw [this, sI_neg]; ring

theorem cI_add' (j k : ℕ) :
    cI α β x (2 * (k : ℤ) + 2 * (j : ℤ)) = cI α β x (2 * (((j + k : ℕ)) : ℤ)) := by
  congr 1; push_cast; ring

theorem sI_add' (j k : ℕ) :
    sI α β x (2 * (k : ℤ) + 2 * (j : ℤ)) = sI α β x (2 * (((j + k : ℕ)) : ℤ)) := by
  congr 1; push_cast; ring

/-- The cross term. `c n = σ(cos(4πn(· - x)))`, `d n = σ(sin(4πn(· - x)))`. -/
theorem cross_hasSum {g : Torus 1 → ℝ} {b : ℕ → ℝ} (hb : Summable fun m => |b m|)
    (hg : ∀ u, HasSum (fun m : ℕ => b m * sm (2 * (m : ℤ)) u) (g u)) :
    HasSum (fun p : ℕ × ℕ => b p.1 * b p.2 / 2 *
      (cI α β x (2 * (p.1 : ℤ)) * (cI α β x (2 * ((Nat.dist p.1 p.2 : ℕ) : ℤ)) -
          cI α β x (2 * ((p.1 + p.2 : ℕ) : ℤ))) -
        sI α β x (2 * (p.1 : ℤ)) * (sI α β x (2 * ((p.1 + p.2 : ℕ) : ℤ)) +
          sgnk p.1 p.2 * sI α β x (2 * ((Nat.dist p.1 p.2 : ℕ) : ℤ)))))
      (intS (fun z => g (z - x) * convS g α β z) α β) := by
  have hg0 : ∀ u, HasSum (fun m : ℕ => (fun _ => (0 : ℝ)) m * cm (2 * (m : ℤ)) u + b m * sm (2 * (m : ℤ)) u) (g u) := by
    intro u; simpa using hg u
  have ha0 : Summable fun m : ℕ => |(fun _ => (0 : ℝ)) m| := by simp
  set c : ℕ → ℝ := fun n => cI α β x (2 * (n : ℤ)) with hc
  set d : ℕ → ℝ := fun n => sI α β x (2 * (n : ℤ)) with hd
  set u : ℕ → Torus 1 → ℝ := fun k z => b k * sm (2 * (k : ℤ)) (z - x) with hu
  set v : ℕ → Torus 1 → ℝ := fun j z =>
    (0 * c j - b j * d j) * cm (2 * (j : ℤ)) (z - x) + (0 * d j + b j * c j) * sm (2 * (j : ℤ)) (z - x) with hv
  set F : ℕ × ℕ → Torus 1 → ℝ := fun p z => v p.1 z * u p.2 z with hF
  have hmass := mass_nonneg α β
  have hub : ∀ k z, |u k z| ≤ |b k| := by
    intro k z
    simp only [hu]; rw [abs_mul]
    calc |b k| * |sm (2 * (k : ℤ)) (z - x)| ≤ |b k| * 1 := mul_le_mul_of_nonneg_left (abs_sm_le _ _) (abs_nonneg _)
      _ = _ := mul_one _
  have hvb : ∀ j z, |v j z| ≤ 2 * mass α β * |b j| := by
    intro j z
    have h1 : |0 * c j - b j * d j| ≤ |b j| * mass α β := by
      have := abs_lin_le (a := 0) (b := b j) (c := c j) (d := d j) (M := mass α β)
        (abs_cI_le α β x _) (abs_sI_le α β x _)
      simpa using this
    have h2 : |0 * d j + b j * c j| ≤ |b j| * mass α β := by
      have := abs_lin_le' (a := 0) (b := b j) (c := c j) (d := d j) (M := mass α β)
        (abs_cI_le α β x _) (abs_sI_le α β x _)
      simpa using this
    calc |v j z| ≤ |(0 * c j - b j * d j) * cm (2 * (j : ℤ)) (z - x)| +
          |(0 * d j + b j * c j) * sm (2 * (j : ℤ)) (z - x)| := abs_add_le _ _
      _ = |0 * c j - b j * d j| * |cm (2 * (j : ℤ)) (z - x)| +
          |0 * d j + b j * c j| * |sm (2 * (j : ℤ)) (z - x)| := by rw [abs_mul, abs_mul]
      _ ≤ |0 * c j - b j * d j| * 1 + |0 * d j + b j * c j| * 1 := add_le_add
          (mul_le_mul_of_nonneg_left (abs_cm_le _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (abs_sm_le _ _) (abs_nonneg _))
      _ ≤ 2 * mass α β * |b j| := by linarith
  have hsu : ∀ z, HasSum (fun k => u k z) (g (z - x)) := fun z => hg (z - x)
  have hsv : ∀ z, HasSum (fun j => v j z) (convS g α β z) := fun z =>
    convS_hasSum α β x ha0 hb hg0 z
  have hn1 : Summable fun j => ‖2 * mass α β * |b j|‖ :=
    (hb.mul_left (2 * mass α β)).congr (fun j => by
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hmass) (abs_nonneg _))])
  have hn2 : Summable fun k => ‖|b k|‖ :=
    hb.congr (fun k => by rw [Real.norm_of_nonneg (abs_nonneg _)])
  have hprodsum : Summable fun p : ℕ × ℕ => (2 * mass α β * |b p.1|) * |b p.2| :=
    summable_mul_of_summable_norm (f := fun j => 2 * mass α β * |b j|) (g := fun k => |b k|) hn1 hn2
  have hFb : ∀ p z, |F p z| ≤ (2 * mass α β * |b p.1|) * |b p.2| := by
    intro p z
    simp only [hF]; rw [abs_mul]
    exact mul_le_mul (hvb _ _) (hub _ _) (abs_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hmass) (abs_nonneg _))
  have hFc : ∀ p, Continuous (F p) := by
    intro p
    simp only [hF, hv, hu]
    exact (((continuous_const.mul (cont_cm_sub x _)).add (continuous_const.mul (cont_sm_sub x _))).mul
      (continuous_const.mul (cont_sm_sub x _)))
  have h := intS_tsum α β hFc hprodsum hFb
  -- the pointwise product
  have hprod : ∀ z, ∑' p, F p z = g (z - x) * convS g α β z := by
    intro z
    have hs1 : Summable fun j => ‖v j z‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _)
        (fun j => by simpa [Real.norm_eq_abs] using hvb j z) (hb.mul_left (2 * mass α β))
    have hs2 : Summable fun k => ‖u k z‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _)
        (fun j => by simpa [Real.norm_eq_abs] using hub j z) hb
    have := tsum_mul_tsum_of_summable_norm hs1 hs2
    rw [(hsv z).tsum_eq, (hsu z).tsum_eq] at this
    simp only [hF]
    rw [← this, mul_comm]
  have hfun : (fun z => ∑' p, F p z) = fun z => g (z - x) * convS g α β z := funext hprod
  rw [hfun] at h
  have key : ∀ p : ℕ × ℕ, intS (F p) α β = b p.1 * b p.2 / 2 *
      (c p.1 * (cI α β x (2 * ((Nat.dist p.1 p.2 : ℕ) : ℤ)) - cI α β x (2 * ((p.1 + p.2 : ℕ) : ℤ))) -
        d p.1 * (sI α β x (2 * ((p.1 + p.2 : ℕ) : ℤ)) +
          sgnk p.1 p.2 * sI α β x (2 * ((Nat.dist p.1 p.2 : ℕ) : ℤ)))) := by
    intro p
    obtain ⟨j, k⟩ := p
    simp only
    -- F p z = (b_j c_j b_k) sm_k sm_j - (b_j d_j b_k) sm_k cm_j
    have hz : ∀ z : Torus 1, F (j, k) z =
        (b j * c j * b k) * (sm (2 * (k : ℤ)) (z - x) * sm (2 * (j : ℤ)) (z - x)) +
        (-(b j * d j * b k)) * (sm (2 * (k : ℤ)) (z - x) * cm (2 * (j : ℤ)) (z - x)) := by
      intro z; simp only [hF, hv, hu]; ring
    have hz' : F (j, k) = fun z =>
        (b j * c j * b k) * (sm (2 * (k : ℤ)) (z - x) * sm (2 * (j : ℤ)) (z - x)) +
        (-(b j * d j * b k)) * (sm (2 * (k : ℤ)) (z - x) * cm (2 * (j : ℤ)) (z - x)) := funext hz
    rw [hz']
    have e1 : ∀ z : Torus 1, sm (2 * (k : ℤ)) (z - x) * sm (2 * (j : ℤ)) (z - x) =
        (cm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x) - cm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x)) / 2 :=
      fun z => sm_mul_sm _ _ _
    have e2 : ∀ z : Torus 1, sm (2 * (k : ℤ)) (z - x) * cm (2 * (j : ℤ)) (z - x) =
        (sm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x) + sm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x)) / 2 :=
      fun z => sm_mul_cm _ _ _
    have ec1 : (fun z : Torus 1 => sm (2 * (k : ℤ)) (z - x) * sm (2 * (j : ℤ)) (z - x)) = fun z =>
        (1 / 2 : ℝ) * cm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x) +
          (-(1 / 2 : ℝ)) * cm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x) := by
      funext z; rw [e1]; ring
    have ec2 : (fun z : Torus 1 => sm (2 * (k : ℤ)) (z - x) * cm (2 * (j : ℤ)) (z - x)) = fun z =>
        (1 / 2 : ℝ) * sm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x) +
          (1 / 2 : ℝ) * sm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x) := by
      funext z; rw [e2]; ring
    have L := linC_intS α β
    have i1 := L.add (fun z => (b j * c j * b k) * (sm (2 * (k : ℤ)) (z - x) * sm (2 * (j : ℤ)) (z - x)))
      (fun z => (-(b j * d j * b k)) * (sm (2 * (k : ℤ)) (z - x) * cm (2 * (j : ℤ)) (z - x)))
      (continuous_const.mul ((cont_sm_sub x _).mul (cont_sm_sub x _)))
      (continuous_const.mul ((cont_sm_sub x _).mul (cont_cm_sub x _)))
    rw [i1, L.smul, L.smul, ec1, ec2]
    have i2 := L.add (fun z => (1 / 2 : ℝ) * cm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x))
      (fun z => (-(1 / 2 : ℝ)) * cm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x))
      (continuous_const.mul (cont_cm_sub x _)) (continuous_const.mul (cont_cm_sub x _))
    have i3 := L.add (fun z => (1 / 2 : ℝ) * sm (2 * (k : ℤ) + 2 * (j : ℤ)) (z - x))
      (fun z => (1 / 2 : ℝ) * sm (2 * (k : ℤ) - 2 * (j : ℤ)) (z - x))
      (continuous_const.mul (cont_sm_sub x _)) (continuous_const.mul (cont_sm_sub x _))
    rw [i2, i3, L.smul, L.smul, L.smul, L.smul]
    show _ = _
    have q1 := cI_dist α β x j k
    have q2 := cI_add' α β x j k
    have q3 := sI_dist α β x j k
    have q4 := sI_add' α β x j k
    simp only [cI, sI] at q1 q2 q3 q4 ⊢
    rw [q1, q2, q3, q4]
    simp only [hc, hd, cI, sI]
    ring
  convert h using 1
  funext p
  exact (key p).symm

end SharpLSI.FL.Ex.LaneD
