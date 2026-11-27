# Agent coordination

This file is the shared reference for every AI agent working in this repository. Read it before starting a task and again before opening a pull request.

Last updated 2026-11-26 (evening) against `main` at `45942fb`. Only the lead edits this file. Everyone else proposes changes to it in a PR description.

## Roles

| Who | Role | Lane |
|---|---|---|
| Matt Azar | Owner | Sets direction, resolves disputes, can revert anything. |
| Claude | Project lead and principal researcher | The hardest open mathematics (R tasks), the proof audit, review of every PR for mathematical correctness, merging, task assignment, this file. |
| Cursor agent | Formalization | Everything under `lean/`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, and CI. |
| ChatGPT Astra 6.2 agent | Computation and verification | Running and replaying computations under `scripts/`, surveys, citation checks, integration of the shared docs, and independent review of the lead's research PRs. |

Stay in your lane's files. If a task needs a change in another lane, describe it in your PR and the lead will route it.

More than one Claude session commits here under the author name "Claude" (PR #4 came from a second session). Every session follows this file. Only the lead session edits it.

## Start here

The owner delegates a lane by giving an agent the matching brief below. Each brief is complete without further context.

### Brief for the formalization agent

```
You are the formalization agent for github.com/matt-azar/beal-conjecture.
1. Read AGENTS.md in full. Then read the "Formalization" section again, including "Lean map" and "Notes for the formalization agent", and the section "Verification" of docs/collaborating.md. For the mathematics behind a task, read the note its row links to.
2. Your files: lean/, lakefile.toml, lake-manifest.json, lean-toolchain, .github/workflows/. Touch nothing else. Put any wording for README.md or docs/ in the PR description.
3. Take tasks from the "Formalization" table in the order given in its "Order" column. Skip a task only if its prerequisite is not merged.
4. One task per branch, named cursor/<ID>-<slug>. Open a PR titled "<ID>: <summary>" using the handoff template. Do not merge and do not edit AGENTS.md. After opening a PR, start the next task from main plus your open branches. Do not wait for review.
5. A task is done only when the theorem's hypotheses match its "Done when" cell. No sorry, no new axiom. A theorem that assumes part of its conclusion must say so in its docstring.
6. If a statement in docs/ or an existing Lean statement is false, unprovable as written, or stronger than the mathematics supports, stop and report it in the PR with the smallest counterexample or the missing hypothesis. That is a finding and counts as progress.
7. Every PR description includes the output of `lake build` and of `#print axioms` for each new headline theorem.
Environment: Lean 4.19.0 via elan, Mathlib v4.19.0. Run `lake exe cache get` before `lake build`. 16 GB RAM or more.
```

### Brief for the computation and verification agent

```
You are the computation and verification agent for github.com/matt-azar/beal-conjecture.
1. Read AGENTS.md in full, then README.md ("Reproduce the calculations") and docs/collaborating.md ("Verification").
2. Your files: scripts/, and the result sections of the per-topic notes in docs/. For README.md, docs/collaborating.md and docs/research-plan.md follow the "Shared files" rule and task C6.
3. Take tasks from the "Computation and verification" table of AGENTS.md in this order: C7 and C1 (whenever a lead research result is unreviewed or has one implementation), C8, C5. C6 runs after every merge. C2, C3 and C4 are done.
4. Branch astra/<ID>-<slug>. Open a PR titled "<ID>: <summary>" using the handoff template. Do not merge and do not edit AGENTS.md.
5. Report every output exactly as produced, including mismatches, survivors and failures. Never adjust a specification, a prime list or a parameter to change an outcome. If a specification looks wrong, say so in the PR and run it as written.
6. For C7, your job is to break the argument: look for a missed case, an unmet hypothesis of a cited theorem, or a sign or orientation error. "No objection found" must list what you checked.
Environment: PARI/GP 2.17.2, Python 3.11 or later with numpy 2.3.5 and python-flint 0.9.0, a C++17 compiler, and for the eclib replay the libraries listed in docs/collaborating.md.
```

## What the repository claims

The general Beal conjecture is open, and this repository does not prove it. No reduction of the general conjecture to the computations here is known. Every agent must keep that distinction intact in code comments, docs, commit messages and PR titles.

The claimed results on `main` are:

1. For $A\in\{167,263,2471\}$, no positive primitive solution of $A^x+B^y=C^z$ with $x,y,z\geq3$ and $4\mid y$. Computer-assisted, see [`docs/fixed-bases.md`](docs/fixed-bases.md).
2. $167^x+U^2=c^{11}$ has no primitive solution. See [`docs/frey-167.md`](docs/frey-167.md).
3. $2471^x+U^2=c^{31}$ has no primitive solution. Reviewed by Astra in PR #21 with no gap found, and replayed with eclib in PR #22. See [`docs/square-summand-2471.md`](docs/square-summand-2471.md).
4. The smooth-summand, class-number and varying-first-summand restrictions listed in the [README](README.md).
5. A twelve-base survey with exclusions at $(151,7)$ and $(167,11)$ and surviving eigensystems at 71, 103 and 119. See [`docs/breadth-survey-results.md`](docs/breadth-survey-results.md).

**Relation to the literature.** With $b=B^{y/4}$, result 1 is the Lebesgue–Nagell equation $X^2+d^x=C^z$ restricted to $X=b^2$ a perfect square. Bennett and Siksek solved $X^2+q^\alpha=y^n$ completely for primes $q<100$, and $X^2+q^{2k}=y^n$ for primes $q<1000$, by the same combination of primitive divisors and Frey curves used here. [Prime power gaps](https://arxiv.org/abs/2110.05553) The bases 167 and 263 are primes above 100 and 2471 is composite, so results 1 to 3 are not contained in those theorems as a whole. Their even-exponent theorem does contain the cases of results 1 and 2 with $x$ even at 167 and 263, so only the cases with $x$ odd may be called new. They are new instances of a known method and not a new method. The table in [`docs/audit.md`](docs/audit.md#what-is-new) gives one row per result. The smooth-summand row in the README is a corollary of their published table. Describe the results this way and no more strongly. Task R4 will pin this down.

Lean checks selected finite steps of the descent and, in `IdealDescent.lean`, the class-number counts for 167 and 2471 (by `native_decide`). The passage from a primitive solution to the ideal factorization (`IdealAPI`, `DedekindGap`), level lowering and all modular-form calculations sit outside Lean. None of these results has had external review. The cited statements have been checked against their sources (PR #9) and the computations replayed from clean checkouts ([`docs/clean-replay.md`](docs/clean-replay.md)). The lead's audit (task P1) has covered only the elementary skeleton of the fixed-base proof so far, see [`docs/audit.md`](docs/audit.md). Treat the results as claimed, not established.

## Task board

Status values: `open`, `active`, `review`, `done`, `blocked`.

### Formalization (Cursor)

No Lean file states or proves the Beal conjecture or any complete theorem of this project. The Lean development checks finite steps and implications inside the quadratic descent for $d=167$ and $d=2471$. The goal of this lane is to close the gap between a primitive integer solution and the principalized twist identity, so that the descent half of the fixed-base proof is machine-checked from the equation to the finite certificate. Level lowering and the Hecke computations stay outside Lean for now.

#### Lean map

Elements of $\mathbb Z[\omega]$, $\omega=(1+\sqrt{-d})/2$, are pairs `(a, b) : Int × Int` meaning $a+b\omega$, with $\omega^2=\omega-D$ and $4D=d+1$. So $D=42$ for 167 and $D=618$ for 2471.

| File | What it proves | What it assumes |
|---|---|---|
| `Twist167.lean`, `Twist2471.lean` | The finite local sieve on the twist index $k$ for left exponent $x=3$. | Nothing. Pure `decide`. |
| `QuadraticBridge.lean` | `right_base_is_odd`. `no_integral_twist167` and `no_integral_twist2471`: no $\beta,k$ with $\beta^p=\eta^k\gamma$ for $x=3$. | The twist identity itself is a hypothesis. |
| `Forced683.lean` | $683\mid c$ for both surviving classes at 2471. | The twist identity and the equation. |
| `TwistIdentity.lean` | The norm identity for odd $x$, the encodings of $\eta$, absorption of a unit sign. Defines `IdealFrontDoor`. | `IdealFrontDoor.signed_twist` is the outstanding input. |
| `CubicTwists.lean` | `no_local_cubes`: the twelve oriented residue checks at right exponent 3. | Takes residue data, not the equation. |
| `IdealDescent.lean` | Units are $\pm1$, no element of norm 2, reduced-form counts 11 and 62 (by `native_decide`), and `idealFrontDoor_of_gap`: `DedekindGap` implies `IdealFrontDoor`. Defines `IdealAPI` and `DedekindGap`. | `DedekindGap` has three unproved fields. |
| `OmegaRing.lean` | `OmegaRing D` is a commutative domain. `idealAPI167`, `idealAPI2471` realize `IdealAPI` with Mathlib ideals. Conjugation and `span_mul_conjugate`. | `no_integral_twist*_of_mathlib_gap` still take a `DedekindGap`. |

The three unproved fields of `DedekindGap` are `gamma_perfect_power` ($(\gamma)=I^p$), `eta_is_P_pow` ($P^p=(\eta)$ for a chosen $P\mid2$), and `principalizer` (some $IP^k$ is principal). Mathematics: [`docs/descent.md`](docs/descent.md#from-an-integer-solution-to-a-twist).

#### Tasks

| ID | Order | Task | Done when | Status |
|---|---:|---|---|---|
| L1 | | Mathlib `v4.19.0` and `IdealDescent.lean`. | Merged in PR #2. Axiom output and the `native_decide` note are recorded in `docs/clean-replay.md`. | done |
| L4 | 1 | Continuous integration. There is no `.github/workflows` directory yet. | A workflow on every PR runs `lake exe cache get`, `lake build`, and the standard-library replays `check_twists.py --exponents`, `check_cubic_twists.py`, `check_aux_traces.py --base 167`, `check_aux_traces.py --base 2471`, `check_residual_form.py`, `audit_skeleton.py`, `check_square_2471.py verify`. It fails if any Lean file contains `sorry` or a new `axiom`. | open |
| L2a | 2 | Repair the statements. `DedekindGap.gamma_perfect_power` and `IdealFrontDoor.signed_twist` quantify over all integers $b,c$ with $d^x+b^4=c^p$ and $x$ odd. The mathematics needs $\gcd(b,d)=1$: without it the ideals $(\gamma)$ and $(\bar\gamma)$ need not be coprime. Add the hypothesis, or prove it is automatic. | Both fields carry the coprimality hypothesis. The $x=3$ theorems keep their present statements, with coprimality derived inside the proof from valuations ($v_q(d^3)=3$ is not a multiple of $p$ for $q\mid d$). If you find the hypothesis is not needed, say why in the PR. | open |
| L2b | 3 | `IsDedekindDomain (OmegaRing D)` for $D=42$ and $D=618$. | An instance for each, or one theorem for every $D$ with $4D-1$ squarefree. Either prove integral closure directly, or build a ring isomorphism with `NumberField.RingOfIntegers` of $\mathbb Q(\sqrt{-d})$. | open |
| L2c | 4 | Prove `gamma_perfect_power` for `idealAPI167` and `idealAPI2471`. | From the equation, $x$ odd and $\gcd(b,d)=1$: $c$ is odd (`right_base_is_odd`), $(\gamma)$ and $(\bar\gamma)$ are coprime, their product is $(c)^p$, hence $(\gamma)=I^p$. Uses unique factorization of ideals from L2b. | open, after L2b |
| L2d | 5 | Define $P$ and prove `eta_is_P_pow` for both bases. | An explicit ideal `P` above 2 with `P ^ p = Ideal.span {η}` in `OmegaRing D`, $p=11$ and $31$. | open, after L2b |
| L5 | 6 | Elementary lemmas of the arbitrary-square note at 2471, in a new file `SquareSummand.lean`. See [`docs/square-summand-2471.md`](docs/square-summand-2471.md). | (i) For $x$ odd and $U$ even, $2471^x+U^2\equiv7$ or $11\pmod{16}$, and for $U$ odd it is even. (ii) With $W=U^2+2471^x$ and $U$ even: $3+4U+W\equiv2\pmod4$, $(1+U)^2+2471^x\equiv0\pmod8$, and the resulting $b_8'$ has 2-adic valuation exactly 2. (iii) In an additive commutative group of order 62, if $31q=0$ and $2q=31j$ then $q=0$. Each docstring names the case of the note it serves. | open |
| L3 | 7 | The period of the cubic residue certificate and the passage from the ideal factorization to the input of `CubicTwists.no_local_cubes`. | A theorem whose hypothesis is the equation with right exponent 3 and $c$ even, not a residue table. It may assume a cubic analogue of `DedekindGap`, stated explicitly. | open |
| L2e | 8 | Prove `principalizer` for both bases. This is the hardest task: it needs the $p$-part of `ClassGroup (OmegaRing D)` to be generated by the class of $P$. | Either a full proof, or the single remaining assumption isolated as one named proposition about Mathlib's `ClassGroup` (for example: the class group has order 11, respectively 62), with everything else derived. Report which. The reduced-form counts in `IdealDescent.lean` are not yet connected to `ClassGroup`. | open, after L2d |
| L2f | 9 | Remove the gap hypothesis. | `no_integral_twist167` and `no_integral_twist2471` restated from the equation alone for $x=3$, and a general statement for odd $x$ with $\gcd(b,d)=1$ producing the signed twist identity. Any remaining assumption from L2e appears as an explicit hypothesis. | open, after L2c to L2e |
| L6 | 10 | Certificate check for the 2471 arbitrary-square class test. Embed the three $42\times42$ matrices over $\mathbb F_{31}$ at 61, 683, 1117 from `docs/replays/square-2471/` and the 961 class sets as literals. | A theorem that the five triples in [`docs/square-summand-2471-review.md`](docs/square-summand-2471-review.md) are the only simultaneous eigenvalue triples, and that no class set product contains one. `native_decide` is acceptable here and must be flagged. The class sets and matrices are inputs, so the docstring must say the theorem checks the final linear algebra only. | open, optional |
| L7 | 11 | Scouting report, no code: what in `github.com/anthropics/fermats-last-theorem` could be reused for the modular half. | A section in the PR description listing the exact declarations for modularity, Galois representations of elliptic curves, level lowering and Mazur's isogeny theorem, their generality (any elliptic curve over $\mathbb Q$, or only the Fermat Frey curve), and the Lean and Mathlib versions. State what an upgrade from Lean 4.19.0 would cost this project. | open |

#### Notes for the formalization agent

- **Coprimality of conjugates (L2c).** A prime ideal dividing both $(\gamma)$ and $(\bar\gamma)$ contains $\gamma+\bar\gamma=2b^2$ and $\gamma\bar\gamma=c^p$. With $c$ odd and $\gcd(b,c)=1$ this is impossible. $\gcd(b,c)=1$ follows from $\gcd(b,d)=1$ and the equation.
- **From a product to a power (L2c).** In a Dedekind domain the nonzero ideals form a unique factorization monoid. Mathlib has a lemma of the shape "coprime $a,b$ with $ab=c^k$ implies $a$ is associated to a $k$th power" for such monoids. Search for `exists_associated_pow_of_mul_eq_pow` and confirm the name and hypotheses in `v4.19.0` before relying on it.
- **The ideal $P$ (L2d).** $\eta$ has norm $2^p$ and odd trace, so exactly one prime above 2 divides it. `Ideal.span {2, η}` is a natural candidate for $P$. A proof by norms is likely easier than expanding a $p$th power of a two-generator ideal.
- **Class group (L2e).** The Minkowski bound for $d=167$ is below 9 and for $d=2471$ below 32, so in principle the class group is generated by primes above 2, 3, 5, 7 (respectively up to 31). This is long. Do not start it before L2a to L2d are merged.
- **`native_decide`.** Allowed for finite counts and matrix checks until the owner decides D2. Prefer `decide` whenever it terminates in reasonable time. List every use in the PR.
- **Base 263.** There is no Lean development for 263. Its proof uses a Mordell curve at right exponent 3 and is not a formalization target yet.
- **Do not formalize** level lowering, modularity or Hecke operators from scratch. L7 decides whether existing work can supply them.

### Research (Claude)

| ID | Task | Done when | Status |
|---|---|---|---|
| R1 | Sixth-power case at the second base: $2471^x+B^6=C^{31}$ with $x$ odd and $C$ odd. Derive the twist with $b^2$ replaced by $B^3$, the exponent-and-twist sieve, both signs of the multiplicative traces, the Frey curve and its lowered level, and the admissible $T_5$ eigenvalues. Plan in [`docs/research-plan.md`](docs/research-plan.md#the-next-arithmetic-target). | `docs/sixth-power-2471.md` contains the full derivation and an exact specification of each finite computation (space, operators, residue prime, expected control). Astra runs them under C1. The result is either a complete exclusion or the exact surviving twist pairs and eigensystems. | done. Merged in PR #18 as the stronger statement $2471^x+U^2=c^{31}$, reviewed in PR #21 |
| R2 | Level-stability criterion for a varying first summand: conditions on discriminant valuations and local residues under which new prime factors vanish under level lowering, so one Hecke computation covers an infinite family with fewer multiplier restrictions than [`docs/varying-base.md`](docs/varying-base.md) and [`docs/frey-167.md`](docs/frey-167.md#varying-the-first-summand). | A stated and proved criterion, with the two existing families recovered as special cases and at least one new family tested. | open |
| R3 | Remove $4\mid y$ for one base. For even $y$ the equation is $d^x+U^2=c^z$. Done or claimed: right exponents divisible by the class-number prime, at all three bases. For other primes $p\ge5$ the primitive-divisor step works only when $c$ is odd. An earlier version of this row overlooked that the fourth power was what forced $c$ odd. With an arbitrary square, $U$ odd and $c$ even is locally possible, and when $p\nmid h$ the class group gives no obstruction. That branch is the Lebesgue–Nagell equation with $y$ even at $q\equiv7\pmod8$, which Bennett–Siksek describe as the hard case and solve only for $q<100$. Also remaining: $z$ even, and $3\mid z$ (points on $Y^2=X^3-d^r$ integral outside the primes of $d$). | A note that either proves "no primitive solution with $y$ even" for one base or states exactly which branches remain. First step: the Frey curve for $c$ even, whose level is $2d$, and which newforms at level 334 survive for all $p$. | open |
| P1 | Independent audit of [`docs/fixed-bases.md`](docs/fixed-bases.md). Check that the case split is exhaustive, that the hypotheses of each cited theorem (Bennett–Ellenberg–Ng Theorem 1, Bilu–Hanrot–Voutier, level lowering including irreducibility and conductor computation) are met, and that sign and orientation conventions agree between the docs and the scripts. | [`docs/audit.md`](docs/audit.md) lists every step as checked, checked with caveat, or gap. Gaps become tasks on this board. | active. First pass merged in PR #6 and its two source caveats are closed by PR #9. The nine items under "Not yet audited" in `docs/audit.md` remain, starting with the Frey conductors and irreducibility |
| R4 | Literature positioning. For each claimed result, find the closest published theorem and state exactly what is and is not new. Start from Bennett–Siksek and the Lebesgue–Nagell literature for $d\equiv7\pmod 8$. | A section in `docs/audit.md` with one row per result and a citation checked against the source. | done. Survey in `docs/literature-survey.md` (PR #12, source-checked in PR #16) and the per-result table in `docs/audit.md` |
| R5 | Arbitrary-square test at the third base: $263^x+U^2=c^{13}$ at level 8416 modulo 13, by the method of `docs/square-summand-2471.md`. | A note with either a complete exclusion or the exact surviving classes and eigensystems. | review. Claimed in PR #27: no primitive solution, all 169 classes eliminated. Do not build on it before C7 and C1 |
| R6 | Read the two closest published methods in full and decide whether to use them: the Frey $\mathbb Q$-curve for $a^4+du^2=c^p$ (survey lead 1) and the modular method for $Ax^2+By^r=Cz^p$ (lead 2). | A short note per paper: hypotheses, the level or field for $d=167$, what it would prove here, and the first computation. | open |
| P3 | Review every PR for mathematical correctness, including whether each Lean statement says what the docs claim it says. | Ongoing. | active |

### Computation and verification (Astra)

| ID | Task | Done when | Status |
|---|---|---|---|
| C1 | Independent replay for R1 (PR #18): recompute the Hecke operators at 61, 683 and 1117 on the 42-dimensional retained space at level 79072 modulo 31 with a second implementation (eclib or PARI), and rerun `scripts/check_square_2471.py verify` on the result. Later, the computations specified by R2. | A replay script per computation with pinned versions, a positive control, and the raw output committed in the doc. Report the output as found, including survivors. Do not change the specification. If it looks wrong, say so in the PR. | open for R5 (PR #27): eclib replay at level 8416 modulo 13. Done for R1 (PR #22) |
| C2 | Clean-environment replay of every script listed in the README with the pinned versions, including `check_modsym_hecke.cpp` from PR #4 and `audit_skeleton.py` from PR #6. The lead has run only the Python replays listed in `docs/audit.md`. | Outputs match the expected results table in [`docs/collaborating.md`](docs/collaborating.md#verification), or mismatches are filed. | done. PR #15, `docs/clean-replay.md` |
| C3 | Breadth survey over squarefree $d\equiv7\pmod{16}$. | The list of $d$ (bounded by discriminant) and the initial trace primes are committed in a first PR, before any Hecke computation is run. A second PR reports, for every $d$ on the list, class number, residual primes, Frey levels, dimensions before and after each filter, and the outcome. Unresolved bases are listed with their eigensystems. | done. Protocol in PR #7, results in PR #14, `docs/breadth-survey-results.md`. Follow-up on the surviving eigensystems is unassigned |
| C4 | Citation check: open every external source cited in `docs/` and confirm the theorem number and statement match the use. Do these two first, since the audit marks them as recalled rather than read: Bennett–Ellenberg–Ng Theorem 1 (does it cover $b^4+(d^{x/2})^2=C^z$ for every $z\geq4$?) and the Bilu–Hanrot–Voutier table of defective Lucas pairs at indices 5, 7, 13. | A table in the PR with one row per citation. Feeds P1. | done. PRs #9 and #16 |
| C5 | Rank-one denominator test on a second residual cubic, following [`docs/transfer-263.md`](docs/transfer-263.md#a-denominator-obstruction-on-the-remaining-mordell-curve). | Lower priority. Start after C1 to C3. | open |
| C6 | Integrate the shared docs (`README.md`, `docs/collaborating.md`, `docs/research-plan.md`) after each merge, using the wording proposed in the PR. | Ongoing. | active |
| C7 | Independent review of the lead's research results (R1, R3, R5, P1). First: `docs/square-summand-2471.md`, which is already on `main`. | A written review per result that tries to break the argument, filed as a PR or an issue. See Working rules. | open for R5 (PR #27). Done for R1 (PR #21) |
| C8 | Mordell computations for R3, once specified: all points on $Y^2=X^3-d^r$ integral outside the primes of $d$, for the $d$ and $r$ named in the specification, with certified ranks and generators. | Replay script, pinned versions, raw output, and a positive control on a curve with known points. | open, after R3 specification |

## Working rules

**Branches and PRs.** Never commit to `main`. One task per branch, named `<agent>/<task-id>-<slug>`, for example `astra/C3-breadth-survey`. Put the task ID in the PR title. Rebase on `main` before requesting review. The lead reviews and merges. A PR that makes a mathematical claim merges only after a written review by an agent other than its author. The lead's own research PRs are reviewed by Astra, never by the lead. Coordination and wording-only PRs may merge without that review. The owner may merge anything directly. A claim that reaches `main` before review keeps a status line saying so at the top of its note until the review lands, and other work must not build on it in the meantime.

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

See the repository's pull-request list. PRs #1 to #26 are merged. PR #27 is open for review.

## Decisions for the owner

| ID | Question | Context |
|---|---|---|
| D1 | Mathlib as a dependency. | Settled: accepted with the merge of PR #2. First build now needs `lake exe cache get`. |
| D2 | Is `native_decide` acceptable for the class-number counts and for certificate checks? | It adds trust in the Lean compiler beyond the kernel. The alternative is a slower `decide` or a certificate-checking proof. Open. Until decided, it is allowed if flagged. |
| D3 | Lane assignments and merging. | Settled 2026-11-26: the lead takes the research tasks, the other agents take formalization and computation, and the lead merges. |
