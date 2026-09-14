import Mathlib

namespace DAGRestrictionUpdate

/-- Small algebraic expression language used to isolate the semantic core of
recursive coordinate restriction. The production evaluator may hash-cons these
nodes into a DAG; this theorem concerns the denotation, independent of storage. -/
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, DecidableEq

/-- Evaluate an expression under a natural-valued coordinate environment. -/
def eval (ρ : Nat → Nat) : Expr → Nat
  | .const c => c
  | .var x => ρ x
  | .add a b => eval ρ a + eval ρ b
  | .mul a b => eval ρ a * eval ρ b

/-- Override one coordinate of an environment. -/
def assign (ρ : Nat → Nat) (v b : Nat) : Nat → Nat :=
  fun x => if x = v then b else ρ x

/-- Structural coordinate restriction, with no distributive expansion. -/
def restrict (v b : Nat) : Expr → Expr
  | .const c => .const c
  | .var x => if x = v then .const b else .var x
  | .add a c => .add (restrict v b a) (restrict v b c)
  | .mul a c => .mul (restrict v b a) (restrict v b c)

/-- Recursive restriction is semantically exact coordinate substitution. -/
theorem eval_restrict
    (ρ : Nat → Nat) (v b : Nat) (e : Expr) :
    eval ρ (restrict v b e) = eval (assign ρ v b) e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · subst x
        simp [restrict, eval, assign]
      · simp [restrict, eval, assign, h]
  | add a c iha ihc =>
      simp [restrict, eval, iha, ihc]
  | mul a c iha ihc =>
      simp [restrict, eval, iha, ihc]

/-- Exact two-cofactor update. -/
def update (v : Nat) (e : Expr) : Expr :=
  .add (restrict v 0 e) (restrict v 1 e)

/-- Semantic two-point marginalization of coordinate `v`. -/
def marginalize (ρ : Nat → Nat) (v : Nat) (e : Expr) : Nat :=
  eval (assign ρ v 0) e + eval (assign ρ v 1) e

/-- Headline theorem: structural update implements exact marginalization. -/
theorem eval_update_eq_marginalize
    (ρ : Nat → Nat) (v : Nat) (e : Expr) :
    eval ρ (update v e) = marginalize ρ v e := by
  simp [update, marginalize, eval, eval_restrict]

/-- Tree-syntax node count. This deliberately does not claim the stronger
support-sensitive hash-consed DAG bound. -/
def treeSize : Expr → Nat
  | .const _ => 1
  | .var _ => 1
  | .add a b => 1 + treeSize a + treeSize b
  | .mul a b => 1 + treeSize a + treeSize b

/-- Restriction preserves tree shape exactly. -/
theorem treeSize_restrict (v b : Nat) (e : Expr) :
    treeSize (restrict v b e) = treeSize e := by
  induction e with
  | const c =>
      rfl
  | var x =>
      by_cases h : x = v
      · simp [restrict, treeSize, h]
      · simp [restrict, treeSize, h]
  | add a c iha ihc =>
      simp [restrict, treeSize, iha, ihc]
  | mul a c iha ihc =>
      simp [restrict, treeSize, iha, ihc]

/-- The familiar duplication bound is a tree representation fact. -/
theorem treeSize_update (v : Nat) (e : Expr) :
    treeSize (update v e) = 1 + treeSize e + treeSize e := by
  simp [update, treeSize, treeSize_restrict]

#print axioms eval_restrict
#print axioms eval_update_eq_marginalize
#print axioms treeSize_restrict
#print axioms treeSize_update

end DAGRestrictionUpdate
