# Agent coordination

This file is the shared reference for every AI agent working in this repository. Read it before starting a task and again before opening a pull request.

Last updated 2026-11-26 against `main` at `76c2a0d`. Only the lead edits this file. Everyone else proposes changes to it in a PR description.

## Roles

| Who | Role | Lane |
|---|---|---|
| Matt Azar | Owner | Sets direction, merges to `main`, resolves disputes. |
| Claude | Project lead and principal researcher | The hardest open mathematics (R tasks), the proof audit, review of every PR for mathematical correctness, task assignment, this file. |
| Cursor agent | Formalization | Everything under `lean/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and CI. |
| ChatGPT Astra 6.2 agent | Computation and verification | Running and replaying computations under `scripts/`, surveys, citation checks, integration of the shared docs, and independent review of the lead's research PRs. |

Stay in your lane's files. If a task needs a change in another lane, describe it in your PR and the lead will route it.

## What the repository claims

The general Beal conjecture is open, and this repository does not prove it. No reduction of the general conjecture to the computations here is known. Every agent must keep that distinction intact in code comments, docs, commit messages and PR titles.

The claimed results on `main` are:

1. For $A\in\{167,263,2471\}$, no positive primitive solution of $A^x+B^y=C^z$ with $x,y,z\geq3$ and $4\mid y$. Computer-assisted, see [`docs/fixed-bases.md`](docs/fixed-bases.md).
2. $167^x+U^2=c^{11}$ has no primitive solution. See [`docs/frey-167.md`](docs/frey-167.md).
3. The smooth-summand, class-number and varying-first-summand restrictions listed in the [README](README.md).

Lean checks only selected finite steps of the descent. Class-group input (on `main`), level lowering and all modular-form calculations sit outside Lean. None of these results has had external review, and the lead's independent audit (task P1) is not yet done, so treat them as claimed, not established.

## Task board

Status values: `open`, `active`, `review`, `done`, `blocked`.

### Formalization (Cursor)

| ID | Task | Done when | Status |
|---|---|---|---|
| L1 | Land PR #2 (`cursor/mathlib-ideal-descent-c7c4`): Mathlib `v4.19.0` and `IdealDescent.lean`. | Owner has approved the Mathlib dependency (see Decisions). `lake build` passes from a clean clone. The `#print axioms` output for each headline theorem is pasted in the PR, and the docs state that `class_number_167` and `class_number_2471` use `native_decide`. | review |
| L2 | Instantiate `IdealAPI` for Mathlib ideals of $\mathcal O_K$ and fill `DedekindGap` for 167 and 2471. | `no_integral_twist167_of_gap` and `no_integral_twist2471_of_gap` are restated with no `api` or `gap` hypothesis, starting from a primitive solution. No `sorry`, no new `axiom`. | open, after L1 |
| L3 | Formalize the period of the cubic residue certificate and the passage from the ideal factorization to the input of `CubicTwists.no_local_cubes`. | A theorem whose hypothesis is the equation with right exponent 3, not a residue table. | open |
| L4 | Continuous integration. | A workflow runs `lake build` and the pure-Python replays (`check_twists.py --exponents`, `check_cubic_twists.py`, `check_aux_traces.py` for 167 and 2471, `check_residual_form.py`) on every PR. | open |

### Research (Claude)

| ID | Task | Done when | Status |
|---|---|---|---|
| R1 | Sixth-power case at the second base: $2471^x+B^6=C^{31}$ with $x$ odd and $C$ odd. Derive the twist with $b^2$ replaced by $B^3$, the exponent-and-twist sieve, both signs of the multiplicative traces, the Frey curve and its lowered level, and the admissible $T_5$ eigenvalues. Plan in [`docs/research-plan.md`](docs/research-plan.md#the-next-arithmetic-target). | `docs/sixth-power-2471.md` contains the full derivation and an exact specification of each finite computation (space, operators, residue prime, expected control). Astra runs them under C1. The result is either a complete exclusion or the exact surviving twist pairs and eigensystems. | active |
| R2 | Level-stability criterion for a varying first summand: conditions on discriminant valuations and local residues under which new prime factors vanish under level lowering, so one Hecke computation covers an infinite family with fewer multiplier restrictions than [`docs/varying-base.md`](docs/varying-base.md) and [`docs/frey-167.md`](docs/frey-167.md#varying-the-first-summand). | A stated and proved criterion, with the two existing families recovered as special cases and at least one new family tested. | open |
| R3 | Feasibility study for removing $4\mid y$. Identify what replaces the quadratic descent and the parity argument when $y$ is odd or $y\equiv2\pmod4$, and which signatures are covered by published results. | `docs/beyond-fourth-powers.md` states, for each residue of $y$, either a concrete route with its first test or the specific obstruction. This is open research and may end with obstructions only. | open |
| P1 | Independent audit of [`docs/fixed-bases.md`](docs/fixed-bases.md). Check that the case split is exhaustive, that the hypotheses of each cited theorem (Bennett–Ellenberg–Ng Theorem 1, Bilu–Hanrot–Voutier, level lowering including irreducibility and conductor computation) are met, and that sign and orientation conventions agree between the docs and the scripts. | `docs/audit.md` lists every step as checked, checked with caveat, or gap. Gaps become tasks on this board. | active |
| P3 | Review every PR for mathematical correctness, including whether each Lean statement says what the docs claim it says. | Ongoing. | active |

### Computation and verification (Astra)

| ID | Task | Done when | Status |
|---|---|---|---|
| C1 | Execute the computations specified by R1 (and later R2). | A replay script per computation with pinned versions, a positive control, and the raw output committed in the doc. Report the output as found, including survivors. Do not change the specification. If it looks wrong, say so in the PR. | open, after R1 spec |
| C2 | Clean-environment replay of every script listed in the README with the pinned versions. | Outputs match the expected results table in [`docs/collaborating.md`](docs/collaborating.md#verification), or mismatches are filed. | open |
| C3 | Breadth survey over squarefree $d\equiv7\pmod{16}$. | The list of $d$ (bounded by discriminant) and the initial trace primes are committed in a first PR, before any Hecke computation is run. A second PR reports, for every $d$ on the list, class number, residual primes, Frey levels, dimensions before and after each filter, and the outcome. Unresolved bases are listed with their eigensystems. | open |
| C4 | Citation check: open every external source cited in `docs/` and confirm the theorem number and statement match the use. | A table in the PR with one row per citation. Feeds P1. | open |
| C5 | Rank-one denominator test on a second residual cubic, following [`docs/transfer-263.md`](docs/transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve). | Lower priority. Start after C1 to C3. | open |
| C6 | Integrate the shared docs (`README.md`, `docs/collaborating.md`, `docs/research-plan.md`) after each merge, using the wording proposed in the PR. | Ongoing. | active |
| C7 | Independent review of the lead's research PRs (R1 to R3, P1). | A written review per PR that tries to break the argument. See Working rules. | ongoing |

## Working rules

**Branches and PRs.** Never commit to `main`. One task per branch, named `<agent>/<task-id>-<slug>`, for example `astra/C3-breadth-survey`. Put the task ID in the PR title. Rebase on `main` before requesting review. The lead reviews and Matt merges. The lead's own research PRs are reviewed by Astra, never by the lead.

**Shared files.** `README.md`, `docs/collaborating.md`, `docs/research-plan.md` and this file are edited by several lanes and have already produced merge conflicts. Do not rewrite them. In your PR, either add a single self-contained line or paragraph, or leave them untouched and put the proposed wording in the PR description. Astra updates them after the merge under C6. In `lakefile.toml`, add your module to `roots` and change nothing else on that line.

**Claims.** State exactly what was shown and under which hypotheses. Keep every quantifier explicit. A Lean theorem that takes a conclusion as a hypothesis verifies an implication only, and its docstring must say so. Do not write "proves Beal", "resolves", or similar about any partial result. Do not weaken or delete a caveat in existing docs without flagging it in the PR.

**Negative results.** A surviving newform, a failed sieve or a counterexample to a lemma is a result. Commit it with the same care as an exclusion. Do not add auxiliary primes or change parameters after seeing an output without recording the earlier attempt.

**Computations.** Every numerical claim in `docs/` needs a script in `scripts/` that reproduces it from a clean clone, with tool versions pinned and the expected output written in the doc. Use exact arithmetic. Include a positive control for every Hecke or rank computation. Commit no generated binaries or caches.

**Lean.** No `sorry` and no `axiom` on `main`. End each file with `#print axioms` for its headline theorems. Flag any use of `native_decide`.

**Citations.** Cite the theorem number and a stable link for every external result, and state how its hypotheses are met. Do not cite from memory. If you cannot open the source, say so in the PR.

**Disagreement.** If you believe another agent's argument or the lead's review is wrong, say so in the PR with a specific counterexample or failing check. The lead has no authority over mathematical truth. Unresolved disputes go to Matt.

## Handoff template

Put this in every PR description.

```
Task: <ID>
Claim: <one precise statement, with hypotheses>
Depends on: <external theorems, other tasks, unmerged branches>
Verified by: <commands run and their output>
Not verified: <anything assumed, skipped or uncertain>
Shared-file wording: <proposed text for README / collaborating / research-plan, if any>
Next step: <what should happen after merge>
```

## Open pull requests

| PR | Branch | Owner | Summary | Needs |
|---|---|---|---|---|
| #2 | `cursor/mathlib-ideal-descent-c7c4` | Cursor | Adds Mathlib and `IdealDescent.lean` (units $\{\pm1\}$, no norm-two element, class numbers 11 and 62 by reduced-form count, `DedekindGap` to `IdealFrontDoor`). | Decision D1, then lead review under L1. It edits three shared docs, so rebase after any doc change on `main`. |

## Decisions for the owner

| ID | Question | Context |
|---|---|---|
| D1 | Accept Mathlib as a dependency? | The README on `main` says the project uses only the Lean standard library. PR #2 adds Mathlib `v4.19.0`, which L2 needs for ideals of $\mathcal O_K$. Cost: much longer first build and a `lake exe cache get` step. |
| D2 | Is `native_decide` acceptable for the class-number counts? | It adds trust in the Lean compiler beyond the kernel. The alternative is a slower `decide` or a certificate-checking proof. |
| D3 | Confirm or change the lane assignments above. | Per the owner's instruction, the lead takes the most demanding research tasks and routine execution goes to the other agents. The specific split is the lead's proposal. |
