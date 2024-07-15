import Mathlib.Data.Multiset.Basic

/- Language for FOL/IFOL. We use ℕ to repersent both predicate, function and variable symbol -/

namespace FOL

inductive Term : Type
| atom (n : ℕ)
| ap (f : Term) (v : Term)
deriving DecidableEq

instance Term.atom_coe : Coe ℕ Term where
  coe n := atom n

def Term.subst (t : Term) (x : ℕ) (y : Term) := match t with
| atom n => if n = x then y else atom n
| ap f v => ap (f.subst x y) (v.subst x y)

def Term.fresh (t : Term) : ℕ := match t with
| atom n => n + 1
| ap f v => max f.fresh v.fresh

notation p:60 "[" var:10 "//" t:10 "]ₜ" => Term.subst p var t

inductive Proposition : Type
| bot
| pred (pred : ℕ) (terms : List Term)
| disj (l : Proposition) (r : Proposition)
| conj (l : Proposition) (r : Proposition)
| imp (l : Proposition) (r : Proposition)
| fa (v : ℕ) (bounded : Proposition)
| ex (v : ℕ) (bounded : Proposition)
deriving DecidableEq

notation "⊥'" => Proposition.bot
infixl:30 "∨" => Proposition.disj
infixl:40 "∧" => Proposition.conj
infixl:20 "→" => Proposition.imp
notation:15 "∀'" "[" var:15 "]" bounded:15 => Proposition.fa var bounded
notation:15 "∃'" "[" var:15 "]" bounded:15 => Proposition.ex var bounded

abbrev neg (p: Proposition) := p → ⊥'
prefix:50 "¬" => neg

def Proposition.subst (p : Proposition) (x : ℕ) (y : Term) := match p with
| bot => bot
| pred p t => pred p (t.map (fun (t : Term) => t[x//y]ₜ))
| disj l r => disj (l.subst x y) (r.subst x y)
| conj l r => conj (l.subst x y) (r.subst x y)
| imp l r => imp (l.subst x y) (r.subst x y)
| fa v bounded => if v == x then fa v bounded else fa v (bounded.subst x y)
| ex v bounded => if v == x then ex v bounded else ex v (bounded.subst x y)

notation p:60 "[" var:10 "//" t:10 "]" => Proposition.subst p var t

/- Sequent, G1/2/3,C/I/M proofs -/

inductive LogicFlavor : Type
| M
| I
| C

def LogicFlavor.RSeqCond (l: LogicFlavor) : Multiset Proposition -> Prop := match l with
| M => fun k => Multiset.card k <= 1
| I => fun k => Multiset.card k <= 1
| C => fun _ => True

def LogicFlavor.bot_constructor (l : LogicFlavor) : Prop := match l with
| M => False
| I => True
| C => True

structure Sequent {l: LogicFlavor} where
  mk ::
  left : Multiset Proposition
  right : Multiset Proposition
  -- { cond : l.RSeqCond right } -- FIXME: figure out how to do this

infix:10 "=>" => Sequent.mk

inductive G1 : (logic : LogicFlavor) -> (@Sequent logic) -> Type
| Ax (p : Proposition) : G1 logic ([p] => [p])
| Lbot : G1 logic ([⊥'] => 0)
| LW (p : Proposition) (prev : G1 logic (Γ => Δ)) : G1 logic (p ::ₘ Γ => Δ)
| RW (p : Proposition) (prev : G1 logic (Γ => Δ)) : G1 logic (Γ => p ::ₘ Δ)
| LC (p : Proposition) (prev : G1 logic (Γ => Δ))
    {h : Γ.count p > 1} : G1 logic (Γ.erase p => Δ)
| RC (p : Proposition) (prev : G1 logic (Γ => Δ))
    {h : Δ.count p > 1} : G1 logic (Γ => Δ.erase p)
| Lconjₗ (l r : Proposition) (prev : G1 logic (l ::ₘ Γ => Δ))
  : G1 logic ((l ∧ r) ::ₘ Γ => Δ)
| Lconjᵣ (l r : Proposition) (prev : G1 logic (r ::ₘ Γ => Δ))
  : G1 logic ((l ∧ r) ::ₘ Γ => Δ)
| Rconj (l r : Proposition)
  (pl : G1 logic (Γ => l ::ₘ Δ)) (pr : G1 logic (Γ => r ::ₘ Δ))
  : G1 logic (Γ => (l ∧ r) ::ₘ Δ)
| Ldisj (l r : Proposition)
  (pl : G1 logic (l ::ₘ Γ => Δ)) (pr : G1 logic (r ::ₘ Γ => Δ))
  : G1 logic ((l ∨ r) ::ₘ Γ => Δ)
| Rconjₗ (l r : Proposition) (prev : G1 logic (Γ => l ::ₘ Δ))
  : G1 logic (Γ => (l ∨ r) ::ₘ Δ)
| Rconjᵣ (l r : Proposition) (prev : G1 logic (Γ => r ::ₘ Δ))
  : G1 logic (Γ => (l ∨ r) ::ₘ Δ)
| Limp (l r : Proposition)
  (pl : G1 logic (Γ => l ::ₘ Δ)) (pr : G1 logic (r ::ₘ Γ => Δ))
  : G1 logic ((l → r) ::ₘ Γ => Δ)
| Rimp (l r : Proposition) (prev : G1 logic (l ::ₘ Γ => r ::ₘ Δ))
  : G1 logic (Γ => (l → r) ::ₘ Δ)
| Lfa (x : ℕ) (y : Term) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ => Δ)) : G1 logic ((∀'[x] p) ::ₘ Γ => Δ)
| Rfa (x y : ℕ) (p : Proposition) (prev : G1 logic (Γ => p[x//y] ::ₘ Δ)) : G1 logic (Γ => (∀'[x] p) ::ₘ Δ)
| Lex (x y : ℕ) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ => Δ)) : G1 logic ((∃'[x] p) ::ₘ Γ => Δ)
| Rex (x : ℕ) (y : Term) (p : Proposition) (prev : G1 logic (Γ => p[x//y] ::ₘ Δ)) : G1 logic (Γ => (∃'[x] p) ::ₘ Δ)

end FOL
