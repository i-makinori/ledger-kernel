# Ledger Kernel — A Hilbert-style Proof Checker Built on an Append-only Ledger

[日本語版 README](README_JP.md)

A Hilbert-style proof checker written in Common Lisp. This is a prototype.
The relation "is provable" (⊢) is recorded as an entry in an append-only ledger,
and each entry is checked line by line to see whether it can be derived from
the existing axioms, inference rules, theorems and derived rules.

The design rests on these core ideas:

- **An append-only ledger**: symbols, formation rules, axioms, inference rules,
  theorems and definitions are all entries in the ledger. Each entry is given a
  number k in order of registration. A proof can (as a rule) cite only entries
  registered before it, so (as a rule) no circularity can arise.
- **Re-verify from scratch, every time**: whenever a theorem is cited, its stored
  proof is instantiated with the substitution and verified again from the beginning
  (a thorough application of the LCF-style "always re-verify" principle). Not even
  the meta-theorem "a substitution instance of a correct proof is correct" is assumed.
- **The system is data**: the logic itself (axioms, inference rules, formation rules)
  is written as a `.system` file and can be swapped out. Propositional logic,
  first-order predicate logic, equality, Peano arithmetic and ZF set theory are all
  defined through this mechanism.
- **Only primitives are trusted; everything else is an abbreviation**: what is trusted
  is the primitive symbols, axioms and inference rules of a `.system` file. For the κ
  they give, the kernel decides x B_κ y (Gödel 1931) by a finite, mechanical procedure.
  The kinds of symbol (variables, terms, formulas, predicate schemas) are fixed in the
  kernel and not extended by `.system` files. A new symbol (∧, ≤, a defined function) is
  an abbreviation that expands into primitive ones, and a theorem is an abbreviation of
  a proof figure; expanded, both give back a primitive proof. (The exception is `th-ded`
  by the deduction theorem, which for now trusts the declared rules.)

- **Bound variables have no names** (machine B): inside the kernel, bound variables
  are represented by de Bruijn indices. `∀v0 ∀v1 (v0 = v1)` becomes
  `(.forall (.forall (.eq (:bv 1) (:bv 0))))`, so formulas that differ only in the
  names of their bound variables (α-equivalent formulas) are literally the same value.
  Free variables carry meaning, so they keep their names. The conversion happens
  exactly once, when a proof enters the ledger; the text as written is kept separately
  for display and storage. Bound variable names are displayed uniformly as
  `?bV₁`, `?bV₂`, … in axioms, rules, definitions and theorems alike (rules are
  renamed at registration time; theorems are numbered at display time).

It also comes with a Web UI for browsing the library in a browser, viewing proofs as
proof trees, and verifying proofs you write on the spot.

> Detailed descriptions of each feature are in [docs/guide.md](docs/guide.md).


## Features

**Logic and systems**
- Propositional logic (Łukasiewicz's three axioms II.1–II.3; proof by cases is derived as
  the theorem `th-case-split`), first-order
  predicate logic (∀, ∃, Gen, existential generalization III.3, existential elimination
  `EXISTS-ELIM`), equality (IV.1–IV.4)
- Connectives ∧ ∨ ↔ ∃! defined as abbreviations (`00-connectives.system`)
- Peano arithmetic (P1–P10) and the orders ≤ and < on top of it (`00-peano-order.system`)
- ZF set theory (extensionality, pairing, union, power set, infinity, regularity,
  separation schema, replacement schema; without the axiom of choice)
- Definite descriptions `(.iota x A)` ("the unique x satisfying A")

**Definition mechanisms**
- `(:abbreviation HEAD BODY)`: defines a new symbol as an abbreviation of an expression
  in earlier symbols. The kernel expands input before checking it, so no axiom is added
- `DEFINE-FUNCTION-BY-DESCRIPTION`: defines a new function symbol, from a property whose
  existence and uniqueness have been proved, as an abbreviation of a ι term, and derives
  its defining formula as a theorem by IOTA (e.g. the empty set ∅)
- Predicate schema variables "A(x)": write `(p v0)` in a theorem to mean "any formula
  containing x", and substitute a concrete formula when citing it (automatically, or
  explicitly with `:inst`)

**On automation**
- Automatic proof of tautologies by Kalmár's completeness construction
  (`PROVE-TAUTOLOGY`) has moved to `backup/`: the completeness theorem is a
  meta-theorem, and generating proofs by relying on it goes beyond what formal
  verification should vouch for. The propositional lemmas live in
  `05-classical-logic.ledger` and `06-connectives.ledger` as checked proofs.

Every proof, whichever tool produced it, is verified by the kernel before it enters the
ledger. The tools themselves need not be trusted.

**Library and Web UI**
- Lemmas for propositional logic, predicate logic, equality, classical logic,
  connectives and quantifiers; the empty set in ZF (existence, uniqueness, definition)
- Number theory: commutativity, associativity, distributivity and cancellation for
  addition and multiplication (`08`); reflexivity, transitivity, antisymmetry and
  totality of the order, and "zero or a successor" (`09`); existence and uniqueness of
  division, and definitions of the quotient `div-s`, the remainder `mod-s` and Gödel's
  β function `beta` (`10`). All proved by induction from P1–P10
- Web UI: browsing the library (formulas in textbook-style notation), proofs as tables
  and proof trees, links to symbols and cited entries, display of the axioms an entry
  depends on and of "the theorems that use this theorem", and in-browser proof checking

Tests: all 333 kernel tests and 50 Web tests pass, with zero compiler warnings.

The kernel (`src/`) is about 2000 lines including comments. The logic itself is not
written in the code; it all lives in `.system` files. Unused features have been moved to
`backup/`, together with the original code and instructions for restoring them
([backup/README.md](backup/README.md)).


## Getting started

### Loading and testing

All you need is SBCL (other Common Lisp implementations should mostly work as well) and
ASDF. Start SBCL at the root of the repository:

```lisp
(require :asdf)
(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))
(asdf:load-system :ledger-kernel)
(asdf:test-system :ledger-kernel)      ; ends with "333/333 self-tests passed."
(in-package :ledger-kernel)
```

If you place the repository under `~/common-lisp/` (or under Quicklisp's
`local-projects/`), `(asdf:load-system :ledger-kernel)` alone is enough, without
`asdf:load-asd`.

### Loading a library

Libraries of theorems (`.ledger`) are stacked in order on top of a system (`.system`).
For ZF set theory:

```lisp
(defun load-chain (files)
  (reduce (lambda (ledger file)
            (if (string= (pathname-type file) "system")
                (bootstrap-kernel-from-spec-file file :ledger ledger)
                (read-ledger-from-file file :ledger ledger)))
          files :initial-value nil))

(defparameter *L*
  (load-chain '("hilbert-library/00-classical-fol-equality.system"
                "hilbert-library/00-connectives.system"
                "zf-library/00-zf.system"
                "hilbert-library/01-propositional-core.ledger"
                "hilbert-library/02-predicate-core.ledger"
                "hilbert-library/03-equality-core.ledger"
                "hilbert-library/05-classical-logic.ledger"
                "hilbert-library/06-connectives.ledger"
                "hilbert-library/07-quantifier-schemas.ledger"
                "zf-library/01-empty-set.ledger")))
```

For Peano arithmetic, stack `01`–`06` and `08`–`10` on top of
`00-classical-fol-equality.system`, `00-connectives.system`,
`00-peano-arithmetic.system` and `00-peano-order.system` (the same order as
"Peano arithmetic" in the Web UI). Every proof is re-verified as it is loaded.

### Citing theorems and checking proofs

Pass a proof to `check-k-proof` and it is checked line by line against the ledger,
returning `T` if it passes.

```lisp
;; Nothing belongs to the empty set: ¬(v0 ∈ ∅)
(check-k-proof '((0 (.neg (.in v0 (empty))) :th (th-zf-not-in-empty))) *L*)
;=> T

;; Apply ∧-elimination (A ∧ B → A) to set-theoretic formulas
(check-k-proof '((0 (.and (.in v0 v1) (.in v0 v2)) :hyp nil)
                 (1 (.to (.and (.in v0 v1) (.in v0 v2)) (.in v0 v1)) :th (th-and-elim-l))
                 (2 (.in v0 v1) :ir (mp 1 0)))
               *L*)
;=> T
```

If a proof fails, it returns `NIL`, with the number of the first rejected line as a
second value.

To register a proof as a theorem, use `check-and-extend` and friends (see "Growing the
ledger" below).

### Web UI

Requires Hunchentoot and yason (with Quicklisp: `(ql:quickload '(:hunchentoot :yason))`;
on Debian/Ubuntu: `apt install cl-hunchentoot cl-yason`). The kernel itself does not
depend on them.

```bash
sbcl --load tools/serve.lisp          # open http://127.0.0.1:8080/
```

You can switch between two worlds, "ZF set theory" and "Peano arithmetic". Proofs can be
shown as tables or proof trees. Clicking a horizontal line in a proof tree folds or
unfolds it, and clicking a symbol or rule name in a formula opens the entry it cites or
was introduced by in a new tab. Each entry's page also shows the axioms it depends on and
the theorems that use it. Proofs written in the editor are checked against the ledger of
the selected world (they are not added to the ledger). See the Web UI section of
[docs/guide.md](docs/guide.md) for details.

To show it without a server, you can export it as a static site:

```bash
sbcl --non-interactive --load tools/export-static.lisp    # writes to site/ (change with OUT=...)
```

`site/index.html` can be opened directly in a browser (it works even over file://), and
the whole folder can be placed on static hosting such as GitHub Pages. The screens are the
same as the server version; every answer the server would return has been written out to
`site/data/*.js`. All proofs are re-verified at export time, so only what the kernel has
accepted is published. Since it is read-only, proofs cannot be checked in the editor
(the S-expressions of proofs can be copied).

To publish the server version, which can also check proofs, on a VPS or similar, put it
behind nginx. Example systemd units, nginx configuration and instructions are collected
in [deploy/](deploy/README.md). Submitted proofs are parsed without Lisp's `read` (only
existing symbols are accepted; no new symbols are created), and there are limits on the
time for a single check, the number of concurrent checks, and the size of a request.


## Writing proofs

### The shape of a line

A proof is a list of lines. Each line is a 4-tuple `(number formula role justification)`.

| Role | Form of justification | Meaning |
|---|---|---|
| `:hyp` | `nil` | Introduce a hypothesis |
| `:axiom` | `(axiom-name extra-args...)` | An instance of an axiom. e.g. `(III.1 t)`, `(III.3 x A t)` |
| `:ir` | `(rule-name line-numbers... extra-args...)` | Application of an inference rule. e.g. `(mp 1 0)`, `(gen 3 v0)`, `(exists-elim 2 7 v3)` |
| `:th`, `:th-ded` | `(theorem-name line-numbers... [:inst bindings])` | Citation of a theorem. The line numbers are the lines proving the premises the theorem requires |

`(mp 1 0)` means "from `A → B` on line 1 and `A` on line 0, conclude `B`". When citing a
theorem, what to substitute for the atomic symbols A, B, … and predicate schemas P(x) in
the theorem is usually determined automatically. When it cannot be determined, or when
you want to replace variables in the theorem, specify it explicitly with `:inst`.

```lisp
(th-forall-elim :inst ((v1 (empty))))          ; replace variable v1 with the term (empty)
(th-forall-mono :inst ((p (v3) (.in v3 v1))))  ; substitute λv3. v3 ∈ v1 for the predicate schema P
(th-and-elim-l  :inst ((a (.in v0 v1))))       ; substitute a formula for the atomic symbol A
```

### Writing formulas

Formulas are written as S-expressions. Symbols are upcased when read, so `a` and `A` are
the same.

| S-expression | Meaning | S-expression | Meaning |
|---|---|---|---|
| `(.to A B)` | A → B | `(.forall x A)` | ∀x A |
| `(.neg A)` | ¬A | `(.exists x A)` | ∃x A |
| `(.and A B)` | A ∧ B | `(.exists1 x A)` | ∃!x A |
| `(.or A B)` | A ∨ B | `(.iota x A)` | ιx A (the unique x satisfying A) |
| `(.iff A B)` | A ↔ B | `(.eq s t)` | s = t |
| `(.in s t)` | s ∈ t (ZF) | `(empty)` | ∅ (ZF) |
| `zero`, `(S t)`, `(+ s t)`, `(* s t)` | 0, S(t), s+t, s·t (Peano arithmetic) | `(p t)` | predicate schema P(t) |
| `a`, `b`, `c`, … | propositional symbols (stand for any formula) | `v0`, `v1`, … | individual variables |

You may choose any names for bound variables. `(.forall v0 (.eq v0 v0))` and
`(.forall v3 (.eq v3 v3))` are the same formula inside the kernel, so either one matches
the same theorems and rules (see section 13 of [docs/guide.md](docs/guide.md) for details).

`.and`, `.or`, `.iff` and `.exists1` are abbreviations defined in `00-connectives.system`.
The kernel expands written formulas before checking them, so A ∧ B and ¬(A → ¬B) are the
same formula: either matches the same theorems and rules, and no axiom is needed to move
between them.


## Growing the ledger

| Function | What it registers |
|---|---|
| `check-and-extend` | A closed proof, as a theorem (`th`) |
| `check-and-extend-by-deduction-direct` | A proof Γ, H ⊢ Φ containing hypothesis H, registered as Γ ⊢ H → Φ via the deduction theorem (`th-ded`) |
| `define-function-by-description` | A function symbol (an abbreviation of a ι term) and the theorem `NAME-DEF` stating its defining formula, from existence and uniqueness theorems |
| `declare-atomic-wff-symbol`, `declare-variable-symbol`, `declare-predicate-schema-symbol` | Declarations of new symbols |

A ledger can be saved as a sequence of commands with `write-ledger-to-file` and read back
with `read-ledger-from-file`. A `.ledger` file is exactly this command sequence, and can
also be written by hand. When it is read, every command goes through the functions above
and is re-verified.


## Library

| File | Contents |
|---|---|
| `hilbert-library/00-classical-fol-equality.system` | The system of first-order predicate logic with equality (formation rules, MP, Gen, IOTA, EXISTS-ELIM, II.1–3, III.1–3, IV.1–4) |
| `hilbert-library/00-connectives.system` | Abbreviations ∧ ∨ ↔ ∃! (no axioms) |
| `hilbert-library/00-peano-arithmetic.system` | The vocabulary and axioms P1–P10 of Peano arithmetic |
| `hilbert-library/00-peano-order.system` | The orders ≤ and < as abbreviations (s ≤ t :⇔ ∃z s + z = t, s < t :⇔ S s ≤ t; no axioms) |
| `hilbert-library/01-propositional-core.ledger` | Identity, hypothetical syllogism, exchange of antecedents |
| `hilbert-library/02-predicate-core.ledger` | Exchanging the order of ∀ |
| `hilbert-library/03-equality-core.ledger` | Reflexivity and transitivity of equality |
| `hilbert-library/04-peano-arithmetic.ledger` | 0 + x = x (proved by induction) |
| `hilbert-library/05-classical-logic.ledger` | Ex falso, double negation introduction and elimination, modus tollens, proof by cases (`th-case-split`), proof by contradiction, etc., from II.1–II.3 only |
| `hilbert-library/06-connectives.ledger` | Basic lemmas for ∧ ∨ ↔ (introduction, elimination, symmetry, transitivity, De Morgan, excluded middle, etc.; originally generated by `PROVE-TAUTOLOGY`, now in `backup/`) |
| `hilbert-library/07-quantifier-schemas.ledger` | Quantifier lemmas about P(x) (∀-elimination, ∃-introduction, monotonicity, ∃! → ∃, uniqueness for ∃!) |
| `hilbert-library/08-arithmetic.ledger` | Commutativity, associativity, distributivity and cancellation for addition and multiplication; properties of 0 and 1 (generated by `tools/generate-arithmetic-ledger.lisp`) |
| `hilbert-library/09-order.ledger` | Reflexivity, transitivity, antisymmetry and totality of ≤; x ≤ Sx; zero or a successor; x + y = 0 → y = 0 (same as above) |
| `hilbert-library/10-division.ledger` | Existence and uniqueness of division by S b; definitions of the quotient `div-s(a,b)`, the remainder `mod-s(a,b)` and the β function `beta(c,d,i)` = c mod (1+(i+1)d) (same as above) |
| `zf-library/00-zf.system` | The axioms of ZF |
| `zf-library/01-empty-set.ledger` | Existence and uniqueness of the empty set, the definition of ∅, ¬(x ∈ ∅) |

The loading order is `.system` → `01`, `02`, `03`, `05`, `06`, `07` → `zf-library/01`
(as in the example in "Loading a library").

The laws in `08`–`10` are registered in universally closed form using the variables
x1, x2, x3, which are reserved for binding (e.g. `th-add-comm` is
∀x1 ∀x2 (x1 + x2 = x2 + x1)). To use one, cite it and then substitute any term with
III.1. Since x1–x3 do not appear in the substituted terms, no variable capture occurs.


## What is trusted (the trust model)

To believe the result of formal verification, you need to know "what is verified, and
what is trusted unconditionally".

**What is verified**
- Every theorem is verified when registered, and each time it is cited, the whole proof
  after substitution is verified again. When citing, the kernel also confirms that the
  hypotheses and conclusion of the substituted proof exactly match the citing line and its
  premises. As a result, even if the matching procedure that searches for substitutions is
  wrong, an incorrect citation cannot pass (this is confirmed by tests that deliberately
  break the matcher).
- A proof can cite only axioms, rules and theorems registered before it. Only symbols and
  formation rules (what counts as a formula) are visible even when added later. This lets
  logical lemmas be used for symbols defined afterwards (such as ∅). Formation rules prove
  nothing, so this does not affect soundness.
- `.ledger` / `.system` files are read purely as data (code execution via `#.(...)` is not
  possible). Even if a `.ledger` file is corrupted or tampered with, the only possible
  outcome is "loading fails".
- Proofs produced by tools are always verified before registration.

**What is trusted unconditionally**
- **The kernel code**: matching, the judgements of free variables and substitutability
  (meta-predicates), the re-verification logic, and the conversion of written formulas
  into de Bruijn form (`src/debruijn.lisp`). The list of binders (`.forall` `.exists`
  `.iota`) and the expansion of abbreviations (`src/abbreviation.lisp`) are also part of
  the kernel. Substitution is performed in a way that
  cannot capture bound variables, but `@subst-ok?` is kept, so that any error in the
  conversion or in unfolding binders is detected and rejected there.
- **The contents of `.system` files**: axioms, inference rules and formation rules are
  trusted as-is once loaded (`:PRIMITIVE`); abbreviations assert nothing and are not
  trusted. The propositional axioms are II.1–II.3 only;
  proof by cases and the rest are derived from them. The consistency of an axiom system cannot be confirmed from within
  the system (Gödel's second incompleteness theorem).
- **The deduction theorem**: it is a meta-theorem of a system, not an assumption of the
  kernel. `th-ded` entries can be registered only if the `.system` file declares it with
  `(:meta-theorem deduction ...)`: matching rules, one per inference rule and with type
  and side conditions, over `(@vdash ?H ?A)` ("line ?A, depending on ?H, becomes
  Γ ⊢ ?H → ?A"). Gen's, for example, requires ?x not free in ?H. The kernel checks that
  every line of a `th-ded` proof that depends on ?H is covered by one of them, recursing
  into cited theorems. What is trusted is each declared rule (one textbook induction step)
  and the final step from a fully covered proof to Γ ⊢ H → Φ. The Web UI's "foundations
  depended on" shows whether this trust was used.
- **Definitions**: not trusted. `DEFINE-FUNCTION-BY-DESCRIPTION` adds only an
  abbreviation (the function symbol stands for a ι term); its defining formula `NAME-DEF`
  is an ordinary theorem proved by the IOTA rule.

**What is not guaranteed**
- There is no protection within the same Lisp image. `ledger-append` is public, and
  functions can be redefined. The basis for trust is that "when reloaded from files,
  everything is verified again".
- There is not yet any means of independently verifying the kernel code itself (an
  independent checker implementation or a specification).


## File layout

```
ledger-kernel.asd        ASDF system definitions (ledger-kernel / ledger-kernel/tests /
                         ledger-kernel/web / ledger-kernel/web/tests)
src/                     The kernel
  package.lisp           Package definition and design policy
  pattern.lisp           Pattern matching and theorem substitution (including predicate schemas)
  treap.lisp             Persistent treap used to index the ledger
  ledger.lisp            The ledger, symbol declarations, list of binders
  debruijn.lisp          de Bruijn representation of bound variables (conversion,
                         opening and closing binders, fresh variables)
  abbreviation.lisp      Abbreviations declared by a .system file, and their expansion
  side-conditions.lisp   Side conditions
  meta.lisp              Meta-predicates and meta-constructors (free variables, substitution, etc.)
  judgement.lisp         Judging formation rules (JUDGEMENT?)
  k-proof.lisp           Proof checking (CHECK-K-PROOF) and registration (CHECK-AND-EXTEND)
  persistence.lisp       Saving and loading ledgers
  meta-theorem.lisp      Meta-theorems declared by a .system file (the deduction theorem's @vdash rules)
  deduction.lisp         Registration via the deduction theorem (th-ded)
  system-spec.lisp       Loading .system files
  function-definition.lisp  DEFINE-FUNCTION-BY-DESCRIPTION (a ι-term abbreviation and NAME-DEF)
tests/                   Kernel tests (ledger-kernel/tests)
hilbert-library/         Systems and libraries for logic and Peano arithmetic
zf-library/              Systems and libraries for ZF set theory
web/                     Web UI (ledger-kernel/web; outside the kernel)
  render.lisp            Displaying formulas in textbook-style notation
  worlds.lisp            Worlds to display (ZF, Peano arithmetic)
  deps.lisp              Citation relations (axioms depended on, theorems using an entry)
  api.lisp, server.lisp  JSON API and Hunchentoot routing
  safe-read.lisp         Reading submitted proofs (without creating new symbols)
  static-export.lisp     Exporting as a static site
  static/                Screens (HTML / JS / CSS)
  tests.lisp             Tests for display and the API
tools/
  serve.lisp                        Starts the Web UI
  export-static.lisp                Exports the Web UI as a static site
  generate-arithmetic-ledger.lisp   Regenerates 08-arithmetic / 09-order / 10-division
docs/guide.md            Detailed description of each feature
backup/                  Features removed from the kernel (original code and restore
                         instructions; not loaded)
deploy/                  Example systemd / nginx configurations for publishing the server version
```


## Tests

```bash
sbcl --non-interactive \
     --eval '(require :asdf)' \
     --eval '(asdf:load-asd (merge-pathnames "ledger-kernel.asd"))' \
     --eval '(asdf:test-system :ledger-kernel)'        # kernel (333 tests)
```

The Web UI tests are run with `(asdf:test-system :ledger-kernel/web)` (50 tests; no HTTP
is used). Each check prints `[pass]` / `[FAIL]`, and a summary is shown at the end. If
there is even one `[FAIL]`, `asdf:test-system` signals an error.

The tests include many "attack" tests that confirm incorrect proofs are rejected
(variable capture, side-condition violations, misuse of the deduction theorem, code
embedded in files, a broken matcher, etc.). When you change the code, confirm
**zero `[FAIL]`** and **zero compiler warnings**. Individual test groups can be run as,
for example, `(run-zf-self-tests)` after `(asdf:load-system :ledger-kernel/tests)`
(see `tests/run.lisp` for the list).


## Known limitations and future work

A major revision of the language design and implementation is planned. Its contents,
with the reasons, include for example:

- **Human verification of the implementation**:
  This was developed in an AI-driven way, so a person needs to check everything carefully,
  one piece at a time — at both the language level and the meta-language level.
- **Making it possible to define the behavior of meta-theorems within `.system`**:
  because the handling and meaning of symbols differ from system to system. The deduction
  theorem can now be declared with `(:meta-theorem deduction ...)`; the grammar of side
  conditions such as those for Subst is still to come.
- **Making it possible to define contradiction per system, and to detect contradictions**
- **The library is small**: ZF only goes as far as the empty set. Pairs, unions, ordered
  pairs, natural numbers and so on are still to come. There is also no class notation
  (`{x ∣ φ}`) to make set theory easier to write.
- **The effort of writing proofs**: raw Hilbert proofs get long. Variable clashes must be
  renamed by hand with `:inst`. The witness variable for `EXISTS-ELIM` is also chosen by hand.
  A higher-level proof language and infix input are future work.
- **Automation**: automatic proof of tautologies is kept in `backup/` and not used by the
  kernel; propositional lemmas are written (or generated by a tool) as ordinary proofs.
- **Definite descriptions**: there is no convention (junk value) for the value of `.iota`
  when the description is not unique.
- **Atomic symbols cannot depend on bound variables**: an atomic symbol A in a theorem can
  only stand for formulas that do not contain variables bound around it (since bound
  variables have no names, capture cannot occur). Formulas that depend on bound variables
  are written with predicate schemas `(p x)`. The current library is written entirely in
  this form and passes unchanged.
- **Speed**: because the formula is traversed each time a binder is opened, loading the
  Peano arithmetic library takes about 1.5 times as long as the named-variable version.
- **Scope of trust**: as described in "What is trusted" above. An independent checker
  (or export to the Metamath format) is future work.
- **Web UI**: proofs can be checked, but there is not yet a feature for registering a proof
  as a theorem.


## License

MIT License. See [LICENSE.txt](LICENSE.txt).
