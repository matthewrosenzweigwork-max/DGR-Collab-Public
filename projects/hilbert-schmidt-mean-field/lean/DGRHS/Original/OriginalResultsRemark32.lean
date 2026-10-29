import Batteries.Tactic.Alias
import DGRHS.Concentration.Remark32Inequality

/-! Source-facing export for Remark 3.2 (`rem:Ustattail`, TeX lines 1084-1095 of
`source/extracted/DGR_PFunc_Current_20260902_145019_UTC.tex`) in the owner-approved corrected
form (owner decision 1.2, `OWNER_DECISIONS_20261006.md`: Remark 3.2 as an inequality with
equality for `N >= 2`).

The printed equalities `A = ‖h‖∞`, `B² = (N-1)‖h‖²_{L∞L²(μ)}`, `C² = N(N-1)‖h‖²_{L²(μ⊗²)}`,
`D ≤ N‖T_h‖_op` hold for the actual source quantities `A, B, C, D` of Proposition 3.1
(`DGRHS.Concentration.iidSourceA/B/C/D`, built from the masked array `h_ij = h (i ≠ j)`,
`h_ii = 0`) in the following corrected form, for the iid single symmetric kernel:

* `A = ‖h‖_∞` for `N ≥ 2`; `A = 0` for `N ≤ 1`; hence `A ≤ ‖h‖_∞` always (the printed equality
  fails at `N = 1`, see `DGRHS.Original.sourceRemark32_equality_fails_at_one`);
* `B² = (N-1)‖h‖²_{L∞L²(μ)}` for all `N` with the *essential* supremum in `x` (an inequality
  `≤ (N-1) sup_x ∫ h(x,y)² dμ(y)` for the printed pointwise supremum);
* `C² = N(N-1)‖h‖²_{L²(μ⊗²)}` for all `N`, with `‖h‖²_{L²(μ⊗²)} = ∫ h² d(μ⊗μ)`;
* `D ≤ (N-1)‖T_h‖_op ≤ N‖T_h‖_op`.

The aliases carry exactly the types of the underlying declarations. -/

/-- rem:Ustattail (source 1084-1095), corrected inequality form: `A ≤ ‖h‖_∞` (equality for
`N ≥ 2`), `B² = (N-1)‖h‖²_{L∞L²}` (ess. sup; `≤` for the pointwise sup), `C² = N(N-1)‖h‖²_{L²}`,
`D ≤ (N-1)‖T_h‖ ≤ N‖T_h‖`. -/
alias DGRHS.Original.rem_Ustattail.inequality_form := DGRHS.Concentration.remark32_inequality_form

/-- rem:Ustattail (source 1084-1095): exact value of `A`, namely `1_{N ≥ 2} ‖h‖_∞`. -/
alias DGRHS.Original.rem_Ustattail.A_eq := DGRHS.Concentration.remark32_A_eq

/-- rem:Ustattail (source 1084-1095): `A ≤ ‖h‖_∞` for all `N`. -/
alias DGRHS.Original.rem_Ustattail.A_le := DGRHS.Concentration.remark32_A_le

/-- rem:Ustattail (source 1084-1095): `A = ‖h‖_∞` for `N ≥ 2`. -/
alias DGRHS.Original.rem_Ustattail.A_eq_of_two_le := DGRHS.Concentration.remark32_A_eq_of_two_le

/-- rem:Ustattail (source 1084-1095): `B² = (N-1)‖h‖²_{L∞L²(μ)}`, essential supremum. -/
alias DGRHS.Original.rem_Ustattail.B_sq_eq := DGRHS.Concentration.remark32_B_sq_eq

/-- rem:Ustattail (source 1084-1095): `B² ≤ (N-1) sup_x ∫ h(x,y)² dμ(y)`, pointwise supremum. -/
alias DGRHS.Original.rem_Ustattail.B_sq_le_pointwise := DGRHS.Concentration.remark32_B_sq_le_pointwise

/-- rem:Ustattail (source 1084-1095): `C² = N(N-1)‖h‖²_{L²(μ⊗μ)}`. -/
alias DGRHS.Original.rem_Ustattail.C_sq_eq := DGRHS.Concentration.remark32_C_sq_eq

/-- rem:Ustattail (source 1084-1095): `D ≤ N‖T_h‖_op` as printed. -/
alias DGRHS.Original.rem_Ustattail.D_le := DGRHS.Concentration.remark32_D_le

/-- rem:Ustattail (source 1084-1095): sharper `D ≤ (N-1)‖T_h‖_op`. -/
alias DGRHS.Original.rem_Ustattail.D_le_pred := DGRHS.Concentration.remark32_D_le_pred

/-- rem:Ustattail (source 1084-1095): the coarse forms consumed by the master layer-cake
estimate (via `iidSourceABC_le`, `iidSourceD_le_integralOperator`, `iid_master_tail`). -/
alias DGRHS.Original.rem_Ustattail.consumed_forms := DGRHS.Concentration.remark32_consumed_forms

#print axioms DGRHS.Original.rem_Ustattail.inequality_form
#print axioms DGRHS.Original.rem_Ustattail.A_eq
#print axioms DGRHS.Original.rem_Ustattail.A_le
#print axioms DGRHS.Original.rem_Ustattail.A_eq_of_two_le
#print axioms DGRHS.Original.rem_Ustattail.B_sq_eq
#print axioms DGRHS.Original.rem_Ustattail.B_sq_le_pointwise
#print axioms DGRHS.Original.rem_Ustattail.C_sq_eq
#print axioms DGRHS.Original.rem_Ustattail.D_le
#print axioms DGRHS.Original.rem_Ustattail.D_le_pred
#print axioms DGRHS.Original.rem_Ustattail.consumed_forms
