# Clean release-package build — 29 October 2026

The cleaned DGPS source package was compiled on fp80 with its pinned Lean 4.35.0-rc3 toolchain and dependency revisions. The following checks succeeded:

| Package directory | Command | Result |
|---|---|---|
| `lean/` | `lake build SharpSymmetricLSI FullLabeledLSI FullLabeledLSIVerified` | Exit 0; 10022 Lake jobs |
| `lean/Campaign/` | `lake build DGPS` | Exit 0; 9778 Lake jobs |
| `lean/Campaign/` | `lake build DGPS.SingularCounterexample.Main` | Exit 0; 9917 Lake jobs; completed 2026-10-29 20:22:46 UTC |

Lake job counts include reused dependencies and are not theorem or newly compiled module counts.

The original build driver stopped after the first two successful phases because it checked for the singular extension's `Main.olean` without having explicitly built that entrypoint. The Campaign library root does not import this extension. The omitted explicit target was subsequently built successfully, reusing the existing dependency outputs. The resulting `Main.olean` was present, and a post-build source-identity check passed for all 1808 distributed files. No Lean source or pinned dependency was changed to obtain this result. Build instructions now include the explicit extension target.

The original failed driver receipt was preserved; the later successful scoped check supplements rather than overwrites that record. The preparatory `DGPS.Wave0.LegacyProbe` is not part of either production entrypoint's import closure and was not checked by these commands.

This establishes compilation of the stated release targets. It does not constitute a new independent proof replay, a manuscript-correspondence audit, or certification of the unfinished expanded T01–T14 manuscript campaign. The original certificates and their scope remain authoritative.
