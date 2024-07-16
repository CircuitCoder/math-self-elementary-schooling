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

notation p:60 "[" var:10 "//" t:10 "]ₜ" => Term.subst p var t

theorem Term.subst_eq (t : Term) (x y : ℕ) (Heq : x = y)
  : t = t [x // y]ₜ := by {
    induction t with
    | atom n =>
      simp [Term.subst]
      split
      · rename_i IH; rw [← Heq, IH]
      · rfl
    | ap f v IHf IHv => simp [Term.subst]; trivial
  }

def Term.fresh (t : Term) : ℕ := match t with
| atom n => n + 1
| ap f v => max f.fresh v.fresh

-- Atomic proposition (but not bottom)
@[ext]
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

theorem Proposition.subst_eq (p : Proposition) (x y : ℕ) (Heq : x = y)
  : p = p [x // y] := match p with
    | bot => by simp [subst]
    | atom p => by {
      simp [subst]
      ext; repeat simp
      rename_i n a
      constructor
      · intros Heq'
        exact ⟨ a, Heq', Eq.symm (a.subst_eq x y Heq) ⟩
      · rintro ⟨ a', Heq', Heq'' ⟩
        rw [← Heq'', ← (a'.subst_eq x y Heq)]
        trivial
    }
    | disj l r => by simp [subst]; rw [← l.subst_eq x y Heq, ← r.subst_eq x y Heq]; exact ⟨ rfl, rfl ⟩;
    | conj l r => by simp [subst]; rw [← l.subst_eq x y Heq, ← r.subst_eq x y Heq]; exact ⟨ rfl, rfl ⟩;
    | imp l r => by simp [subst]; rw [← l.subst_eq x y Heq, ← r.subst_eq x y Heq]; exact ⟨ rfl, rfl ⟩;
    | fa v bounded => by simp [subst]; split; rfl; rw [← bounded.subst_eq x y Heq]
    | ex v bounded => by simp [subst]; split; rfl; rw [← bounded.subst_eq x y Heq]

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

theorem r_empty_spacious { logic : LogicFlavor } : (@r_empty logic).r_spacious := match logic with
| LogicFlavor.M => by simp [r_empty, LogicFlavor.RSeq.r_spacious]
| LogicFlavor.I => by simp [r_empty, LogicFlavor.RSeq.r_spacious]
| LogicFlavor.C => by trivial

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
infixr:15 "::ᵣ" => r_concat

theorem r_concat_empty_singleton { logic : LogicFlavor } { p : Proposition }
  : @Eq logic.RSeq (p ::ᵣ []ᵣ) [p]ᵣ := match logic with
| LogicFlavor.M => by simp [r_concat, r_singleton]
| LogicFlavor.I => by simp [r_concat, r_singleton]
| LogicFlavor.C => by simp [r_concat, r_singleton]; rfl

theorem l_concat_empty_singleton { p : Proposition }
  : (p ::ₘ {}) = [p] := by rfl

/- Proof systems -/

instance { logic : LogicFlavor } : Coe Proposition (@Sequent logic) where
  coe p := {} ⇒ [p]ᵣ

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
| Lconjᵣ {l r : Proposition} (prev : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l ∧ r) ::ₘ Γ ⇒ Δ)
| Rconj {l r : Proposition} { cond : Δ.r_spacious }
  (pl : G1 logic (Γ ⇒ l ::ᵣ Δ)) (pr : G1 logic (Γ ⇒ r ::ᵣ Δ))
  : G1 logic (Γ ⇒ (l ∧ r) ::ᵣ Δ)
| Ldisj {l r : Proposition}
  (pl : G1 logic (l ::ₘ Γ ⇒ Δ)) (pr : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l ∨ r) ::ₘ Γ ⇒ Δ)
| Rdisjₗ {l r : Proposition} { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ l ::ᵣ Δ)) : G1 logic (Γ ⇒ (l ∨ r) ::ᵣ Δ)
| Rdisjᵣ {l r : Proposition} { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ r ::ᵣ Δ)) : G1 logic (Γ ⇒ (l ∨ r) ::ᵣ Δ)

| Limp {l r : Proposition} -- Spacious condition is *NOT* required here, because for G1[mi], left branch drops all additional right propositions
  (pl : G1 logic (Γ ⇒ l ::ᵣ Δ)) (pr : G1 logic (r ::ₘ Γ ⇒ Δ))
  : G1 logic ((l → r) ::ₘ Γ ⇒ Δ)

| Rimp {l r : Proposition} { cond : Δ.r_spacious } (prev : G1 logic (l ::ₘ Γ ⇒ r ::ᵣ Δ))
  : G1 logic (Γ ⇒ (l → r) ::ᵣ Δ)
| Lfa (x : ℕ) (y : Term) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ ⇒ Δ)) : G1 logic ((∀'[x] p) ::ₘ Γ ⇒ Δ)
| Rfa (x y : ℕ) (p : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ p[x//y] ::ᵣ Δ)) : G1 logic (Γ ⇒ (∀'[x] p) ::ᵣ Δ)
| Lex (x y : ℕ) (p : Proposition) (prev : G1 logic (p[x//y] ::ₘ Γ ⇒ Δ)) : G1 logic ((∃'[x] p) ::ₘ Γ ⇒ Δ)
| Rex (x : ℕ) (y : Term) (p : Proposition) { cond : Δ.r_spacious }
  (prev : G1 logic (Γ ⇒ p[x//y] ::ᵣ Δ)) : G1 logic (Γ ⇒ (∃'[x] p) ::ᵣ Δ)

def G1.ax_any' { logic : LogicFlavor } (p : Proposition) : G1 logic (p ::ₘ {} ⇒ p ::ᵣ []ᵣ) := match p with
| ⊥' => l_concat_empty_singleton ▸ r_concat_empty_singleton ▸ G1.Axbot
| Proposition.atom a => l_concat_empty_singleton ▸ r_concat_empty_singleton ▸ G1.Ax a
| Proposition.conj l r => by {
  let l_proof : G1 logic (l ::ₘ {} ⇒ l ::ᵣ []ᵣ) := ax_any' l
  let r_proof : G1 logic (r ::ₘ {} ⇒ r ::ᵣ []ᵣ) := ax_any' r
  let l_str : G1 logic ((l ∧ r) ::ₘ {} ⇒ l ::ᵣ []ᵣ) := G1.Lconjₗ l_proof
  let r_str : G1 logic ((l ∧ r) ::ₘ {} ⇒ r ::ᵣ []ᵣ) := G1.Lconjᵣ r_proof
  exact @G1.Rconj _ _ _ _ _ r_empty_spacious l_str r_str
}
| Proposition.disj l r => by {
  let l_proof : G1 logic (l ::ₘ {} ⇒ l ::ᵣ []ᵣ) := ax_any' l
  let r_proof : G1 logic (r ::ₘ {} ⇒ r ::ᵣ []ᵣ) := ax_any' r
  let l_str : G1 logic (l ::ₘ {} ⇒ l ∨ r ::ᵣ []ᵣ) := @G1.Rdisjₗ _ _ _ _ _ r_empty_spacious l_proof
  let r_str : G1 logic (r ::ₘ {} ⇒ l ∨ r ::ᵣ []ᵣ) := @G1.Rdisjᵣ _ _ _ _ _ r_empty_spacious r_proof
  exact G1.Ldisj l_str r_str
}
| Proposition.imp l r => by {
  let l_proof : G1 logic ({l} ⇒ l ::ᵣ []ᵣ) := ax_any' l
  let l_weak : G1 logic ({l} ⇒ l ::ᵣ r ::ᵣ []ᵣ) := by {
    simp [r_concat]
    exact match Heq : logic with
    | LogicFlavor.M => by {
      simp; rw [Heq] at l_proof; simp [r_concat] at l_proof
      exact l_proof
    }
    | LogicFlavor.I => by {
      simp; rw [Heq] at l_proof; simp [r_concat] at l_proof
      exact l_proof
    }
    | LogicFlavor.C => by {
      let l_weak' := @G1.RW logic _ _ r l_proof (by {
        simp [LogicFlavor.RSeq.r_spacious]
        rw [Heq]; simp
      })
      simp [r_singleton]; rw [Heq] at l_weak'; simp [r_concat, r_empty] at l_weak'

      let l_swap : (l ::ₘ {r}) = (r ::ₘ l ::ₘ {}) := by {
        rw [Multiset.cons_swap]
        rfl
      }
      exact l_swap ▸ l_weak'
    }
  }
  let r_proof : G1 logic (r ::ₘ {} ⇒ r ::ᵣ []ᵣ) := ax_any' r
  let r_swap : l ::ₘ r ::ₘ ∅ = r ::ₘ {l} := by rw [Multiset.cons_swap]; rfl
  let r_weak : G1 logic (r ::ₘ {l} ⇒ r ::ᵣ []ᵣ) := r_swap ▸ G1.LW l r_proof
  let imp_proof : G1 logic ((l → r) ::ₘ {l} ⇒ r ::ᵣ []ᵣ) := G1.Limp l_weak r_weak
  let imp_proof : G1 logic (l ::ₘ {l → r} ⇒ r ::ᵣ []ᵣ) := (Multiset.cons_swap _ _ _) ▸ imp_proof
  exact @G1.Rimp _ _ _ _ _ r_empty_spacious imp_proof
}
| Proposition.fa x pb => by {
  let p_proof : G1 logic (pb ::ₘ 0 ⇒ pb ::ᵣ []ᵣ) := r_concat_empty_singleton ▸ ax_any' pb
  let p_proof' : G1 logic ((∀'[x] pb) ::ₘ 0 ⇒ pb ::ᵣ []ᵣ) := G1.Lfa x x _
    (Proposition.subst_eq _ _ _ rfl ▸ p_proof)
  let p_proof'' : G1 logic ((∀'[x] pb) ::ₘ 0 ⇒ (∀'[x] pb) ::ᵣ []ᵣ) := @G1.Rfa _ _ _ x x _
    r_empty_spacious (Proposition.subst_eq _ _ _ rfl ▸ p_proof')
  exact r_concat_empty_singleton ▸ p_proof''
}
| Proposition.ex x pb => by {
  let p_proof : G1 logic (pb ::ₘ 0 ⇒ pb ::ᵣ []ᵣ) := r_concat_empty_singleton ▸ ax_any' pb
  let p_proof' : G1 logic ((∃'[x] pb) ::ₘ 0 ⇒ pb ::ᵣ []ᵣ) := G1.Lex x x _
    (Proposition.subst_eq _ _ _ rfl ▸ p_proof)
  let p_proof'' : G1 logic ((∃'[x] pb) ::ₘ 0 ⇒ (∃'[x] pb) ::ᵣ []ᵣ) := @G1.Rex _ _ _ x x _
    r_empty_spacious (Proposition.subst_eq _ _ _ rfl ▸ p_proof')
  exact r_concat_empty_singleton ▸ p_proof''
}

def G1.ax_any { logic : LogicFlavor } (p : Proposition) : G1 logic ([p] ⇒ [p]ᵣ) :=
  r_concat_empty_singleton ▸ G1.ax_any' p

def G1.bot_any { logic : LogicFlavor } (r : logic.RSeq) : G1 logic ([⊥'] ⇒ r) := match Heq : logic, r with
| LogicFlavor.M, none => G1.Lbot
| LogicFlavor.I, none => G1.Lbot
| LogicFlavor.M, some p => @G1.RW _ _ _ p G1.Lbot r_empty_spacious
| LogicFlavor.I, some p => @G1.RW _ _ _ p G1.Lbot r_empty_spacious
| LogicFlavor.C, _ => by {
  simp [Heq, LogicFlavor.RSeq] at r
  sorry
  -- FIXME: This is no longer constructive! we cannot use multiset
}

abbrev G1m := G1 LogicFlavor.M
abbrev G1i := G1 LogicFlavor.I
abbrev G1c := G1 LogicFlavor.C

namespace G1.Examples

def G1c_dne (p : Proposition) : G1c (¬¬p → p) := by {
  let P1 : G1c ({p} ⇒ [p]ᵣ) := G1.ax_any _
  let P1 : G1c ({p} ⇒ ⊥' ::ᵣ [p]ᵣ) := @G1.RW _ _ _ _ P1 (by simp [LogicFlavor.RSeq.r_spacious])
  let P1 : G1c ({} ⇒ ¬p ::ᵣ [p]ᵣ) := @G1.Rimp _ _ _ _ _ (by simp [LogicFlavor.RSeq.r_spacious]) P1
  let P2 : G1c ({⊥'} ⇒ [p]ᵣ) := G1.bot_any _
  let P : G1c ({¬¬p} ⇒ [p]ᵣ) := G1.Limp P1 P2
  exact @G1.Rimp _ _ _ _ _ r_empty_spacious (r_concat_empty_singleton ▸ P)
}

end G1.Examples

end FOL
