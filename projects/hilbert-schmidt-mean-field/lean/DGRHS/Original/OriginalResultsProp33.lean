import Batteries.Tactic.Alias
import DGRHS.Decoupling.Prop33GeneralK

/-! Source-facing export for Proposition 3.3 (`prop:decoup`, TeX lines 1095-1104 of
`source/extracted/DGR_PFunc_Current_20260902_145019_UTC.tex`), general `k ≥ 2`, Banach values.

Each `alias` has exactly the type of the underlying declaration. Qualification relative to
the printed statement (see the module docstring of `DGRHS.Decoupling.Prop33GeneralK`): the target
space carries `[MeasurableAdd₂ E] [OpensMeasurableSpace E]` (automatic for separable `E`) so that
the probability events are measurable; completeness of `E` is not used. The constant is the
explicit `DGRHS.Decoupling.Prop33.tailConst k`, depending only on `k`. The printed proposition
contains the tail form only; the moment form `Φ(x) = x^p` is a consequence by the layer-cake
formula (the printed Remark 3.4 is the separate `k = 2` canonical-kernel statement with the
constant `4`, recorded elsewhere). -/

/-- prop:decoup (source 1097-1104), tail form, general `k ≥ 2`, Banach-valued ordered
tuple-dependent kernels, independent copies as random variables. -/
alias DGRHS.Original.prop_decoup.banach_tail_general_k := DGRHS.Decoupling.Prop33.prop33_banach_tail

/-- prop:decoup (source 1097-1104), moment form `Φ(x) = x^p` derived from the tail form. -/
alias DGRHS.Original.prop_decoup.banach_moment_general_k := DGRHS.Decoupling.Prop33.prop33_banach_moment

/-- prop:decoup (source 1097-1104), tail form on product laws. -/
alias DGRHS.Original.prop_decoup.banach_tail_general_k_product := DGRHS.Decoupling.Prop33.prop33_banach_tail_product

/-- prop:decoup (source 1097-1104), moment form on product laws. -/
alias DGRHS.Original.prop_decoup.banach_moment_general_k_product := DGRHS.Decoupling.Prop33.prop33_banach_moment_product

#print axioms DGRHS.Original.prop_decoup.banach_tail_general_k
#print axioms DGRHS.Original.prop_decoup.banach_moment_general_k
#print axioms DGRHS.Original.prop_decoup.banach_tail_general_k_product
#print axioms DGRHS.Original.prop_decoup.banach_moment_general_k_product
