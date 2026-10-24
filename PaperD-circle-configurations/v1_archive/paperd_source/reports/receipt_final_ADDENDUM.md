# Addendum to receipt_final_{jack,john}.log (2026-10-14)
The receipt script's `mathlib` line is empty because of a grep bug in the script (pattern did not match the
manifest's JSON layout). Recorded separately the same day:
- lake-manifest.json of all eight published repos pins mathlib rev 0df444a360eaa60ab8c11dca51a86af692955474.
- The Mathlib checkout supplied to the builds: jack ~/barbier/.lake/packages/mathlib HEAD = 0df444a360eaa60ab8c11dca51a86af692955474;
  john ~/lean/clifford/.lake/packages/mathlib HEAD = 0df444a360eaa60ab8c11dca51a86af692955474.
Cross-check: all 24 library-file SHA-256 hashes agree between the two logs and with the local published trees (0 mismatches);
all 16 checkouts at the pinned commit with a clean working tree.

## Correction (found by the Astra confirmation review, 2026-10-14)
In receipt_final.sh the cliffordchain *label* had been updated to the new pin ba083b2158e1… but the `git checkout` still used the
previous commit df7d65c85915… (the HEAD line in receipt_final_{jack,john}.log shows df7d65…). The two commits differ only in
GENERAL_REPORT.md (text); all Lean files are identical. cliffordchain was re-run at the correct commit with the fixed script
(receipt_cc.sh, which also records the Mathlib rev): receipt_cc_{jack,john}.log — HEAD ba083b2158e1b96e2360b6e7d8fe04bd278ff5e2,
clean, mathlib 0df444a3…, build rc=0, PASS (32), ALL TAMPERING TESTS REJECTED, on both machines; 7 Lean hashes = published tree.
