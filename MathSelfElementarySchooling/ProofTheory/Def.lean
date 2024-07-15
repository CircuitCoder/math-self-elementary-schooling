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

-- Atomic proposition (but not bottom)
structure Atomic where
  mk ::
  pred : ℕ
  terms : List Term
deriving DecidableEq

inductive Proposition : Type
| bot
| atom (a : Atomic)
| disj (l : Proposition) (r : Proposition)
| conj (l : Proposition) (r : Proposition)
| imp (l : Proposition) (r : Proposition)
| fa (v : ℕ) (bounded : Proposition)
| ex (v : ℕ) (bounded : Proposition)
deriving DecidableEq

instance Atomic.coe : Coe Atomic Proposition where
  coe := Proposition.atom

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
| atom (Atomic.mk p t) => atom (Atomic.mk p (t.map (fun (t : Term) => t[x//y]ₜ)))
| disj l r => disj (l.subst x y) (r.subst x y)
| conj l r => conj (l.subst x y) (r.subst x y)
| imp l r => imp (l.subst x y) (r.subst x y)
| fa v bounded => if v == x then fa v bounded else fa v (bounded.subst x y)
| ex v bounded => if v == x then ex v bounded else ex v (bounded.subst x y)

notation p:60 "[" var:10 "//" t:10 "]" => Proposition.subst p var t

theorem Proposition.subst_eq (p : Proposition) (x y : ℕ)
  : x = y -> p = p [x // y] := by {
    intros x
    sorry
    -- induction p
  }

lemma Proposition.subst_id (p : Proposition) (x : ℕ)
  : p = p [x // x] := Proposition.subst_eq p x x rfl

/- Sequent, G1/2/3,C/I/M proofs -/

inductive LogicFlavor : Type
| M
| I
| C

def LogicFlavor.RSeq (l: LogicFlavor) : Type := match l with
| M => Option Proposition
| I => Option Proposition
| C => Multiset Proposition

def LogicFlavor.bot_constructor (l : LogicFlavor) : Prop := match l with
| M => False
| I => True
| C => True

structure Sequent {l: LogicFlavor} where
  mk ::
  left : Multiset Proposition
  right : l.RSeq

infix:10 "⇒" => Sequent.mk

def r_empty {logic : LogicFlavor} : logic.RSeq := match logic with
| LogicFlavor.M => none
| LogicFlavor.I => none
| LogicFlavor.C => (0 : Multiset Proposition)

def r_singleton {logic : LogicFlavor} (p : Proposition) : logic.RSeq := match logic with
| LogicFlavor.M => some p
| LogicFlavor.I => some p
| LogicFlavor.C => ([p] : Multiset Proposition)

def LogicFlavor.RSeq.r_spacious {logic : LogicFlavor} (seq : logic.RSeq) : Prop := match logic with
| LogicFlavor.M => seq = none
| LogicFlavor.I => seq = none
| LogicFlavor.C => True

def r_concat {logic : LogicFlavor} (p : Proposition) (seq : logic.RSeq) : logic.RSeq := match logic with
| LogicFlavor.M => some p
| LogicFlavor.I => some p
| LogicFlavor.C => p ::ₘ seq

def LogicFlavor.RSeq.r_erase {logic : LogicFlavor} (seq : logic.RSeq) (p : Proposition) : logic.RSeq := match logic with
| LogicFlavor.M => if (Option.instDecidableEq seq (some p)).decide then none else seq
| LogicFlavor.I => if (Option.instDecidableEq seq (some p)).decide then none else seq
| LogicFlavor.C => seq.erase p

def LogicFlavor.RSeq.r_multiple {logic : LogicFlavor} (seq : logic.RSeq) (p : Proposition) : Prop := match logic with
| LogicFlavor.M => False
| LogicFlavor.I => False
| LogicFlavor.C => seq.count p > 1

notation "[" p:10 "]ᵣ" => r_singleton p
notation "[]ᵣ" => r_empty
infixl:15 "::ᵣ" => r_concat

inductive G1 : (logic : LogicFlavor) -> (@Sequent logic) -> Type
| Ax (p : Atomic) : G1 logic ([(p : Proposition)] ⇒ [p]ᵣ)
| Axbot : G1 logic ([⊥'] ⇒ [⊥']ᵣ)
| Lbot : G1 logic ([⊥'] ⇒ []ᵣ)
| LW (p : Proposition) (prev : G1 logic (Γ ⇒ Δ)) : G1 logic (p ::ₘ Γ ⇒ Δ)
| RW (p : Proposition) (prev : G1 logic (Γ ⇒ Δ)) { cond: Δ.r_spacious } : G1 logic (Γ ⇒ p ::ᵣ Δ)
| LC (p : Proposition) (prev : G1 logic (Γ ⇒ Δ))
    {h : Γ.count p > 1} : G1 logic (Γ.erase p ⇒ Δ)
| RC (p : Proposition) (prev : G1 logic (Γ ⇒ Δ))
    {h : Δ.r_multiple p} : G1 logic (Γ ⇒ Δ.r_erase p)
| Lconjₗ {l r : Proposition} (prev : G1 logic (l ::ₘ Γ ⇒ Δ))
  : G1 logic ((l ∧ r) ::ₘ Γ ⇒ Δ)
| Lconjᵣ (l r : Proposition) (prev : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l ∧ r) ::ₘ Γ ⇒ Δ)
| Rconj (l r : Proposition) { cond : Δ.r_spacious }
  (pl : G1 logic (Γ ⇒ l ::ᵣ Δ)) (pr : G1 logic (Γ ⇒ r ::ᵣ Δ))
  : G1 logic (Γ ⇒ (l ∧ r) ::ᵣ Δ)
| Ldisj (l r : Proposition)
  (pl : G1 logic (l ::ₘ Γ ⇒ Δ)) (pr : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l ∨ r) ::ₘ Γ ⇒ Δ)
| Rconjₗ (l r : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ l ::ᵣ Δ)) : G1 logic (Γ ⇒ (l ∨ r) ::ᵣ Δ)
| Rconjᵣ (l r : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ r ::ᵣ Δ)) : G1 logic (Γ ⇒ (l ∨ r) ::ᵣ Δ)

| Limp (l r : Proposition) -- Spacious condition is *NOT* required here, because for G1[mi], left branch drops all additional right propositions
  (pl : G1 logic (Γ ⇒ l ::ᵣ Δ)) (pr : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l → r) ::ₘ Γ ⇒ Δ)

| Rimp (l r : Proposition) { cond : Δ.r_spacious } (prev : G1 logic (l ::ₘ Γ ⇒ r ::ᵣ Δ))
  : G1 logic (Γ ⇒ (l → r) ::ᵣ Δ)
| Lfa (x : ℕ) (y : Term) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ ⇒ Δ)) : G1 logic ((∀'[x] p) ::ₘ Γ ⇒ Δ)
| Rfa (x y : ℕ) (p : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ p[x//y] ::ᵣ Δ)) : G1 logic (Γ ⇒ (∀'[x] p) ::ᵣ Δ)
| Lex (x y : ℕ) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ ⇒ Δ)) : G1 logic ((∃'[x] p) ::ₘ Γ ⇒ Δ)
| Rex (x : ℕ) (y : Term) (p : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ p[x//y] ::ᵣ Δ)) : G1 logic (Γ ⇒ (∃'[x] p) ::ᵣ Δ)

def ax_any { logic : LogicFlavor } (p : Proposition) : G1 logic ([p] ⇒ [p]ᵣ) := match p with
| ⊥' => G1.Axbot
| Proposition.atom a => G1.Ax a
| Proposition.conj l r => by {
  let l_proof : G1 logic ([l] ⇒ [l]ᵣ) := ax_any l
  let r_proof : G1 logic ([r] ⇒ [r]ᵣ) := ax_any r
  let l_strenghtened : G1 logic ([l ∧ r] ⇒ [l]ᵣ) := sorry
  let r_strenghtened : G1 logic ([l ∧ r] ⇒ [r]ᵣ) := sorry
  -- TODO: add helper constructors for singletons
  sorry
}
| Proposition.disj l r => sorry
| Proposition.imp l r => sorry
| Proposition.fa x p => sorry
| Proposition.ex x p => sorry

end FOL
