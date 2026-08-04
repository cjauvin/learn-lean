/-!
# Playground

Nothing in here is graded, imported, or checked by `./progress.sh`.
It is a scratch file. Break things.

A few things worth trying at least once:
-/

-- 1. Ask Lean what something is.
#check @List.foldl
#print Nat.add

-- 2. Ask Lean to find a proof for you.
example (n : Nat) : 0 ≤ n := by exact?

-- 3. Watch `simp` show its work.
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp?

-- 4. Run an IO action right here.
#eval do
  IO.println "the editor is a REPL"
  IO.println s!"2^10 = {2^10}"

-- 5. Leave a hole and hover it. `_` means "you figure it out";
--    the error message tells you the type Lean expected.
-- #check (fun (n : Nat) => _ : Nat → String)

-- 6. See how big a tactic proof really is.
theorem small : 2 + 2 = 4 := by decide
#print small
