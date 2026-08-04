# learn-lean

An interactive, puzzle-driven course in Lean 4 — programming first, proofs
second, with the punchline that they were the same thing all along.

73 exercises across 8 chapters, each with a test that goes red until you
solve it, plus three browser applets for the things that are hard to see
from inside a text editor.

---

## Setup

Already done on this machine. For the record:

- **Lean 4.32.2** via `elan`, installed at `~/.elan`
- `~/.config/fish/conf.d/elan.fish` puts `lean`/`lake` on your fish PATH
- The `leanprover.lean4` VS Code extension is installed and configured
  (see `.vscode/settings.json`)

Sanity check:

```bash
lake build
```

It will report a pile of unsolved exercises. That is the correct output on
day one.

---

## The loop

1. Open a chapter file in VS Code, e.g. `LearnLean/Ch01_Values.lean`.
2. Make sure the **InfoView** is open — `Cmd+Shift+Enter`, or it should
   open on its own. This is not optional; it is where Lean talks to you.
3. Read down the file. Put your cursor on any `#eval` or `#check` line and
   the answer appears on the right.
4. When you hit an exercise, replace `sorry` with real code.
5. The `#guard` lines underneath are the test. **Red squiggle = wrong.
   Silence = correct.** For proof exercises, the signal is the yellow
   *"declaration uses `sorry`"* warning — make it go away.

Check your progress at any time:

```bash
./progress.sh
```

Example output — *not* real numbers, just the shape of it (green = chapter
complete, amber = in progress):

```
Ch01_Values                   6/6   ██████
Ch02_Inductive                5/8   █████░░░
Ch03_Recursion                0/10  ░░░░░░░░░░
...
total: 11/73
```

It also surfaces any *real* error, as opposed to a merely unfinished
exercise.

---

## The chapters

| # | File | What lands |
|---|------|-----------|
| 1 | `Ch01_Values.lean` | The editor as REPL. Types, functions, currying, `·` notation. |
| 2 | `Ch02_Inductive.lean` | Inductive types. Rebuild `Bool` and `Nat` from nothing; write your first interpreter. |
| 3 | `Ch03_Recursion.lean` | Lists, structural recursion, folds — and why Lean refuses to let you loop forever. |
| 4 | `Ch04_Structures.lean` | Structures, polymorphism, type classes. How `+` actually finds its meaning. |
| 5 | `Ch05_Monads.lean` | `Option`, `Except`, `IO`, `do`-notation. Effects as values. |
| 6 | `Ch06_Propositions.lean` | **The hinge.** Propositions are types; proofs are programs. Term-mode proofs only. |
| 7 | `Ch07_Tactics.lean` | Tactics, goal states, `induction`, `simp`, `omega`. |
| 8 | `Ch08_Verified.lean` | Prove your own code correct. Ends with a verified insertion sort and length-indexed vectors. |

`LearnLean/Playground.lean` is a scratch file — not graded, not imported.

**Chapter 6 is the one that matters.** Everything before it is a
well-designed functional language you could have learned elsewhere.
Chapter 6 is where it becomes Lean.

---

## The applets

```bash
open applets/index.html
```

Self-contained HTML, no server, no dependencies, works offline.

- **The Reduction Machine** (Ch. 2–3) — step through a recursive function
  as it rewrites itself to a value, redex highlighted. Then race naive
  `reverse` against the accumulator version and watch n² pull away from n.
  The rewriting engine underneath is real, about 60 lines of JS.
- **Proofs Are Programs** (Ch. 6) — a miniature proof assistant. Click
  term constructors to build a proof; solve one and it hands you Lean code
  you can paste into the chapter.
- **Reading the Goal State** (Ch. 7) — four real proofs stepped through
  tactic by tactic. Every state was captured from Lean itself with
  `trace_state`, so it is exactly what your InfoView will show.

---

## Solutions

`Solutions/Ch01.lean` … `Solutions/Ch08.lean`. Every one type-checks:

```bash
lake build Solutions
```

Use them the way you'd use the back of a textbook — after a real attempt,
and preferably to check an answer rather than to find one. The proof
chapters especially: being stuck for twenty minutes and then seeing it is
how the skill is built. Being stuck for an hour is not, so don't be
precious about looking.

---

## Getting unstuck

Inside a `by` block, Lean will help you if you ask:

| Tactic | Does |
|--------|------|
| `exact?` | Searches the library for a term that closes the goal |
| `apply?` | Same, for backwards steps |
| `simp?` | Runs `simp` and tells you which lemmas it used |
| `omega` | Decides linear arithmetic over `Nat`/`Int` |
| `decide` | Runs the decision procedure, for anything finite |
| `grind` | Strong general-purpose finisher — worth a try on anything |
| `sorry` | Admit it and move on. Come back later. |

Outside a proof, `#check`, `#print`, and `#print axioms` are your
microscope. Hovering anything shows its type. Typing `List.` and pausing
gets you autocomplete over the whole library, which is a surprisingly good
way to browse.

Unicode: type `\to` `\and` `\or` `\forall` `\exists` `\<>` `\.` `\l` and
press space. Hovering a symbol tells you its escape sequence.

---

## Adding Mathlib

Not needed for this course, and it costs you a large download plus much
slower builds — so it's deliberately left out. When you want it (real
mathematics, `ring`, `linarith`, `field_simp`):

```bash
lake update -R
```

after adding to `lakefile.toml`:

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

Match your `lean-toolchain` to Mathlib's, or let `lake update` do it.

---

## Where to go after Chapter 8

- **A verified compiler.** Extend Chapter 2's `Expr`, compile it to a stack
  machine, prove `run (compile e) = eval e`. ~150 lines, and a rite of
  passage.
- **Verified data structures.** Red-black trees with the balance invariant
  in the type.
- **Metaprogramming.** `macro`, `elab`, custom syntax. Lean is written in
  Lean; you can extend the parser from inside your own file.
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) — the programming book, free.
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) — the proving book, free.
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) — Mathlib-based, for real maths.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) — browser-based proof drilling, genuinely fun.
- [Lean Zulip](https://leanprover.zulipchat.com/) — the community lives here and is famously welcoming to beginners.
