import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime

namespace Erdos970

namespace Mathlib.Tactic.LinearCombinationPrime
open _root_.Mathlib.Tactic.LinearCombinationPrime
open Lean
open Elab Meta Term

variable {α β : Type*}

theorem pf_smul_c [SMul α β] {a b : α} (p : a = b) (c : β) : a • c = b • c := p ▸ rfl
theorem c_smul_pf [SMul α β] {b c : β} (p : b = c) (a : α) : a • b = a • c := p ▸ rfl
theorem smul_pf [SMul α β] {a₁ b₁ : α} (p₁ : (a₁ : α) = b₁) {a₂ b₂ : β} (p₂ : a₂ = b₂) :
    a₁ • a₂ = b₁ • b₂ := p₁ ▸ p₂ ▸ rfl

partial def expandAdditiveCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandLinearCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_add_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_add_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(add_pf $p₁ $p₂)
  | `($e₁ - $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_sub_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_sub_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandAdditiveCombo ty e with
    | .const c => .const <$> `(-$c)
    | .proof p => .proof <$> ``(neg_pf $p)
  | `(← $e:term) => do
    match ← expandAdditiveCombo ty e with
    | .const c => return .const c
    | .proof p => .proof <$> ``(Eq.symm $p)
  | `($e₁ • $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ • $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_smul_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_smul_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(smul_pf $p₁ $p₂)
  | e =>
                                                                                          
    withSynthesize do

      let c ← withSynthesizeLight <| Term.elabTerm e ty
      if (← whnfR (← inferType c)).isEq then
        .proof <$> c.toSyntax
      else
        .const <$> c.toSyntax

def elabAdditiveCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (exp? : Option Syntax.NumLit) (input : Option Syntax.Term)
    (twoGoals := false) : Tactic.TacticM Unit := Tactic.withMainContext do
  let some (ty, _) := (← (← Tactic.getMainGoal).getType').eq? |
    throwError "'additive_combination' only proves equalities"
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e =>
    match ← expandAdditiveCombo ty e with
    | .const c => `(Eq.refl $c)
    | .proof p => pure p
  let norm := norm?.getD (Unhygienic.run <| withRef tk `(tactic| ((try simp only [smul_add, smul_sub]); abel)))
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
  if twoGoals then
    `(tactic| (
      refine eq_trans₃ $p ?a ?b
      case' a => $norm:tactic
      case' b => $norm:tactic))
  else
    match exp? with
    | some n =>
      if n.getNat = 1 then `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))
      else `(tactic| (refine eq_of_add_pow $n $p ?a; case' a => $norm:tactic))
    | _ => `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))

syntax (name := AdditiveCombination) "additive_combination"
  (normStx)? (expStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| additive_combination%$tk $[(norm := $tac)]? $[(exp := $n)]? $(e)?) =>
    elabAdditiveCombination tk tac n e

end Mathlib.Tactic.LinearCombinationPrime

end Erdos970
