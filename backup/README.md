# backup/

Code removed from `src/` to keep the kernel small. None of it is loaded by
any ASDF system, and nothing in `hilbert-library/` or `zf-library/` used it.
Each file starts with what the code did and step-by-step notes for putting
it back, followed by the original code (and its tests) verbatim.

| File | What it was |
|---|---|
| `_backup_inductive.lisp` | `DEFINE-INDUCTIVE-PREDICATE(S)`: inductive predicates over `ZERO`/`S` |
| `_backup_alpha-conversion.lisp` | `ALPHA-RENAME-ENTRY` / `ALPHA-RENAME-FORALL`: re-admitting a theorem with renamed variables |
| `_backup_deduction-transform.lisp` | `@DEDUCTION`: the Deduction Theorem as a proof transformation (no trust needed) |
| `_backup_ith-def-abbrev.lisp` | the `ITH` and `DEF-ABBREV` entry kinds (both checked exactly like `TH`) |
| `_backup_meta-unused.lisp` | the `@PROVEN?`, `@SUBSTN`, `@SUBSTN-OK?` meta operations |

The hardcoded `BOOTSTRAP-KERNEL` (FOL, equality and Peano axioms written
in Lisp) was removed as well but is not kept here: it was an exact copy of
`hilbert-library/00-classical-fol-equality.system` and
`00-peano-arithmetic.system`, which are now the only source. Tests build
that ledger with `FOL-KERNEL` (`tests/framework.lisp`).
