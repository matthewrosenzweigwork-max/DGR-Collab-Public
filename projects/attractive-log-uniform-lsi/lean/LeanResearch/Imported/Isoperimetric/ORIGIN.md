# Public isoperimetric dependency port

Status: source inspected; compatibility feedback pending. Outside the aggregate.
This is an input toward manuscript lem:iso, not a proof of the torus lemma.

Original repository: https://github.com/hojonathanho/isoperimetric
Commit: 29768f8beeaf17295cdf3853d37da35d7e2b0a5f
Commit tree: 85b649aa6d309f0b54036ac0a43aebac88b14408
Saved commit response: research/discovery/references/geometry-reuse-20260928_194526_UTC/isoperimetry-commit-response-v111.json, SHA256 de99cf7505f3da17090f74f4b34f1f88c2396d4c623d704bdd4c47c29ea274c6.
Original source and exact Git blob retrieval records are in research/discovery/references/geometry-reuse-20260928_194526_UTC.
The original resolver-labelled tree record is retained; the commit response gives its exact interpretation.

All four original files,1153lines, were read completely by root.
The original theorem is a Euclidean outer-volume expansion bound for arbitrary nonempty measurable finite-volume sets.
The proof constructs one-dimensional Brunn–Minkowski, layer cake, normalized/bounded/general Prekopa–Leindler, dimension induction, Brunn–Minkowski and the explicit finite-radius expansion estimate.
This does not identify Minkowski expansion with Hausdorff boundary length or prove any torus topology claim.

Apache2.0 LICENSE copied byte-for-byte SHA256 cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30. Original code attribution is the repository owner hojonathanho; no new authorship is inferred.
Initial local changes are only project import paths and a shared namespace LeanResearch.Imported.Isoperimetric to avoid collisions with generic original declaration names.
No theorem statement or proof is altered in the initial port. Later compatibility edits must be recorded.
Original Lean4.26.0-rc2 and pinned upstream dependency metadata are provenance only, not installed. Accepted project toolchain/pins unchanged.
No independent semantic or Comparator/Nanoda verdict. No installation, private upload or remote mission.

Initial copies:
- {"name": "Basic", "source_sha256": "29a29704257aaa78d0fd5146c23e01ec88ff1ee6408275e0f306bb60fcd2dc65", "local_sha256": "a5ca76c6ee9747d5d3ec6c2ac5bbe7502aa54bbd6b1afc029bc4a2a7ee3e24e9", "lines": 57}
- {"name": "PrekopaLeindler", "source_sha256": "8a9d39059ec365fa0c91e49b199b535c2f7c361298bc2cde16fed2ac46dbeb83", "local_sha256": "8ff3a1eebb4a53c979c30069ca7a99573d09e96caa2b0e249746954308c97aae", "lines": 793}
- {"name": "BrunnMinkowski", "source_sha256": "5a46c3f09012877e2ca3b2044f170cac7bb8d82707628b482bb9c053b909e50d", "local_sha256": "f1ae076becfb94482731399a5eb6c7786f85bc0151ba35a36db64ecf4123fdf4", "lines": 248}
- {"name": "Isoperimetric", "source_sha256": "94b980030014e2344f0a459e0bdab9fc614fff5151f6744568a08f0e7d9ad4bb", "local_sha256": "cfea2ae45136a3b49bdee03d190d2c608baf9ef02f4abaef40bf21a428a070c0", "lines": 83}

Compatibility addendum, 2026-09-28 UTC.

All theorem statements are unchanged. The four proof-level adaptations in PrekopaLeindler are: use ae_restrict_mem for the actual restricted almost-everywhere inequality; use MeasurePreserving.lintegral_map_equiv for the Fin1 coordinate equivalence; update the generated e_f case labels; and replace three removed marginal-composition proofs by the actual Measurable.lmarginal theorem with explicit marginal measure, coordinate set and append function. The other three bodies are unchanged. The header now points explicitly to these repairs.

Root fully read all original1153 lines and all changed proof bodies. Exact upstream recursive tree lists15 entries, is not truncated, and contains LICENSE but no NOTICE. The license bytes above remain unchanged. No additional package is installed.

Development feedback records feedback-isoperimetric-port-001 and feedback-prekopa-leindler-port-001 through004 preserve the dependency failure and subsequent actual Lean errors. PL004 completed successfully in1.389s with6 original deprecation warnings and no errors; its closure had2sources/6pins/48protected. Isoperimetric002 completed cleanly in7.504s with4sources/6pins/48protected. Those exact-hash observations preceded the attribution-comment update and are not transferred silently to its changed bytes. A new exact-hash check follows. No resource limit changed.

The endpoint controls a finite-radius Euclidean volume expansion. Its connection to physical Hausdorff boundary length, planar Jordan domains, and the two topological cases of the sharp torus isoperimetric lemma remains OPEN. Selected axiom inspection, integrated build and separate semantic review are still pending at this addendum.
