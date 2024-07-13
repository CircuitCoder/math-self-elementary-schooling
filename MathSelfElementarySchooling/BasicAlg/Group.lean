import Mathlib.Init.Function
import Aesop
open Classical

universe u

class Group (G: Type u) where
  id: G
  mul: G -> G -> G
  inv: G -> G

  id_abs_l: ∀ { g: G }, mul id g = g
  id_abs_r: ∀ { g: G }, mul g id = g
  inv_l: ∀ { g : G }, mul (inv g) g = id
  inv_r: ∀ { g : G }, mul g (inv g) = id

  assoc: ∀ { a b c : G }, mul (mul a b) c = mul a (mul b c)

infixl:100 "⬝" => Group.mul
postfix:100 "⁻¹" => Group.inv

lemma double_inv {G: Type u} [Group G] { g: G } : (g⁻¹)⁻¹ = g := calc
  g⁻¹⁻¹ = g⁻¹⁻¹ ⬝ Group.id := by rw [Group.id_abs_r]
  _ = g⁻¹⁻¹ ⬝ ((g⁻¹) ⬝ g) := by rw [Group.inv_l]
  _ = g⁻¹⁻¹ ⬝ (g⁻¹) ⬝ g := by rw [Group.assoc]
  _ = Group.id ⬝ g := by rw [Group.inv_l]
  _ = g := Group.id_abs_l

lemma inv_uniq_l {G: Type u} [Group G] ( g h : G )
  : g ⬝ h = Group.id -> g = h⁻¹ := by {
    intros Heq
    exact calc
      g = g ⬝ Group.id := by rw [@Group.id_abs_r]
      _ = g ⬝ (h ⬝ (h⁻¹)) := by rw [@Group.inv_r]
      _ = g ⬝ h ⬝ (h⁻¹) := by rw [@Group.assoc]
      _ = h⁻¹ := by rw [Heq, Group.id_abs_l]
  }

lemma inv_uniq_r {G: Type u} [Group G] ( g h : G )
  : g ⬝ h = Group.id -> h = g⁻¹ := by {
    intros Heq
    exact calc
      h =  Group.id ⬝ h := by rw [@Group.id_abs_l]
      _ = g⁻¹ ⬝ g ⬝ h := by rw [@Group.inv_l]
      _ = g⁻¹ ⬝ (g ⬝ h) := by rw [@Group.assoc]
      _ = g⁻¹ := by rw [Heq, Group.id_abs_r]
  }

lemma inv_dist {G: Type u} [Group G] ( g h : G )
  : (g ⬝ h)⁻¹ = h⁻¹ ⬝ (g⁻¹) := by {
    exact calc
      (g ⬝ h)⁻¹ = (g ⬝ h)⁻¹ ⬝ Group.id := by rw [@Group.id_abs_r]
      _ = (g ⬝ h)⁻¹ ⬝ (g ⬝ (g⁻¹)) := by rw [@Group.inv_r]
      _ = (g ⬝ h)⁻¹ ⬝ (g ⬝ Group.id ⬝ (g⁻¹)) := by rw [@Group.id_abs_r]
      _ = (g ⬝ h)⁻¹ ⬝ (g ⬝ (h ⬝ (h⁻¹)) ⬝ (g⁻¹)) := by rw [@Group.inv_r]
      _ = (g ⬝ h)⁻¹ ⬝ ((g ⬝ h ⬝ (h⁻¹)) ⬝ (g⁻¹)) := by {
        have Htmp : g ⬝ (h ⬝ (h⁻¹)) = g ⬝ h ⬝ (h⁻¹) := Eq.symm Group.assoc
        rw [Htmp]
      }
      _ = (g ⬝ h)⁻¹ ⬝ (g ⬝ h ⬝ (h⁻¹)) ⬝ (g⁻¹) := by rw [← @Group.assoc]
      _ = ((g ⬝ h)⁻¹ ⬝ (g ⬝ h)) ⬝ (h⁻¹) ⬝ (g⁻¹) := by rw [← @Group.assoc]
      _ = Group.id ⬝ (h⁻¹) ⬝ (g⁻¹) := by rw [@Group.inv_l]
      _ = _ := by rw [@Group.id_abs_l]
  }

structure Subgroup (G: Type u) [Group G] where
  pred: G -> Prop
  id_mem: pred Group.id
  mul_mem: ∀ { a b: G }, pred a -> pred b -> pred (a ⬝ b)
  inv_mem: ∀ { g: G }, pred g -> pred (g⁻¹)

def subgroup_carrier {G: Type u} [Group G] (s: Subgroup G) := Σ' (g: G), s.pred g

instance {G: Type u} [G_structure: Group G] {H: Subgroup G} : Group (subgroup_carrier H) where
  id := PSigma.mk G_structure.id H.id_mem
  mul a b := PSigma.mk (G_structure.mul a.fst b.fst) (H.mul_mem a.snd b.snd)
  inv h := PSigma.mk (G_structure.inv h.fst) (H.inv_mem h.snd)

  id_abs_l {g} := by { simp [G_structure.id_abs_l]; rfl }
  id_abs_r {g} := by { simp [G_structure.id_abs_r]; rfl }
  inv_l {g} := by simp [G_structure.inv_l]
  inv_r {g} := by simp [G_structure.inv_r]
  assoc { a b c } := by simp [G_structure.assoc]


/- Normal subgroup and quotient groups -/
structure NormalSubgroup (G: Type u) [Group G] extends Subgroup G where
  conj_mem: ∀ { h g : G }, pred h -> pred (g ⬝ h ⬝ (g⁻¹))

def NormalSubgroup.conj_mem_symm {G: Type u} [Group G] (self: NormalSubgroup G) :
  ∀ { h g : G }, self.pred h -> self.pred (g⁻¹ ⬝ h ⬝ g) := by {
    intros h g Hh
    let Htmp : self.pred (g⁻¹ ⬝ h ⬝ (g⁻¹⁻¹)):= self.conj_mem Hh
    rw [double_inv] at Htmp
    exact Htmp
  }

lemma normal_comm_l {G: Type u} [Group G] {N: NormalSubgroup G} ( g n: G )
  : N.pred n -> ∃ n', N.pred n' ∧ n ⬝ g = g ⬝ n' := by {
    intros Hn
    let n' := g⁻¹ ⬝ n ⬝ g
    let H1 : N.pred n' := by {
      let H: N.pred (g⁻¹ ⬝ n ⬝ _) := N.conj_mem Hn
      rw [@double_inv] at H
      exact H
    }
    let H2 := calc
      n ⬝ g = Group.id ⬝ n ⬝ g := by rw [@Group.id_abs_l]
      _     = g ⬝ (g⁻¹) ⬝ n ⬝ g := by rw [@Group.inv_r]
      _     = g ⬝ ((g⁻¹) ⬝ n ⬝ g) := by rw [← @Group.assoc, ← @Group.assoc]
      _     = g ⬝ n' := by rfl
    exact ⟨ n' , ⟨ H1, H2 ⟩ ⟩
  }

lemma normal_comm_r {G: Type u} [Group G] {N: NormalSubgroup G} ( g n: G )
  : N.pred n -> ∃ n', N.pred n' ∧ g ⬝ n = n' ⬝ g := by {
    intros Hn
    let n' := g ⬝ n ⬝ (g⁻¹)
    let H1 : N.pred n' := N.conj_mem Hn
    let H2 := calc
      g ⬝ n = g ⬝ n ⬝ Group.id := by rw [@Group.id_abs_r]
      _     = g ⬝ n ⬝ (g⁻¹ ⬝ g) := by rw [@Group.inv_l]
      _     = g ⬝ n ⬝ (g⁻¹) ⬝ g := by rw [← @Group.assoc]
      _     = n' ⬝ g := by rfl
    exact ⟨ n' , ⟨ H1, H2 ⟩ ⟩
  }

@[ext]
structure QuotientGroup {G: Type u} [Group G] (N: NormalSubgroup G) where
  classes: G -> Prop
  cong: ∀ { g n: G }, N.pred n -> classes g -> classes (g ⬝ n)
  cong_inv: ∀ { g h: G }, classes g -> classes h -> N.pred (g⁻¹ ⬝ h)
  inh: ∃ g, classes g

def QuotientGroup.cong_symm {G: Type u} [Group G] {N: NormalSubgroup G} (self : QuotientGroup N) : ∀ { g n: G }, N.pred n -> self.classes g -> self.classes (n ⬝ g) := by {
  intros g n Hn Hg
  rcases (normal_comm_l g n Hn) with ⟨ n', Hn', Heq ⟩
  rw [Heq]
  exact self.cong Hn' Hg
}

def QuotientGroup.cong_inv_symm {G: Type u} [Group G] {N: NormalSubgroup G} (self : QuotientGroup N) : ∀ { g h: G }, self.classes g -> self.classes h -> N.pred (g ⬝ (h⁻¹)) := by {
  intros g h Hg Hh
  let Htmp := self.cong_inv Hg Hh
  let n := g⁻¹ ⬝ h
  let Heq1 : h = g ⬝ n := calc
    h = g ⬝ ((g⁻¹) ⬝ h) := by rw [← Group.assoc, Group.inv_r, Group.id_abs_l]
    _ = g ⬝ n := rfl
  let Heq2 := calc
    g ⬝ (h⁻¹) = g ⬝ ((g ⬝ n)⁻¹) := by rw [Heq1]
    _ = g ⬝ (n⁻¹ ⬝ (g⁻¹)) := by rw [inv_dist]
    _ = g ⬝ (n⁻¹ ) ⬝ (g⁻¹) := by rw [Group.assoc]
  rw [Heq2]
  apply N.conj_mem
  apply N.inv_mem
  exact Htmp
}

def quotient_proj {G: Type u} [Group G] (N: NormalSubgroup G) (g: G) : QuotientGroup N := {
  classes := fun h => ∃ n, N.pred n ∧ g ⬝ n = h
  cong := by {
    simp
    intros h n Hn
    intros n₁ Hn₁ Heq₁
    let Carrier := (subgroup_carrier N.toSubgroup)
    let nc : Carrier := ⟨ n, Hn ⟩
    let n₁c : Carrier := ⟨ n₁, Hn₁ ⟩
    let n₂c : Carrier := n₁c ⬝ nc
    constructor
    constructor
    · exact n₂c.snd
    · rw [← Heq₁]
      have Heq₂ : n₂c.fst = n₁ ⬝ n := by {
        dsimp [n₂c]
        simp [Group.mul]
      }
      rw [Heq₂]
      rw [← @Group.assoc G]
  }
  cong_inv := by {
    simp
    intros a b n Hn Heq n' Hn' Heq'
    rw [← Heq, inv_dist, ← Heq']
    let Htmp := calc n⁻¹ ⬝ (g⁻¹) ⬝ (g ⬝ n')
        = n⁻¹ ⬝ (g⁻¹ ⬝ (g ⬝ n')) := by rw [@Group.assoc]
      _ = n⁻¹ ⬝ ((g⁻¹ ⬝ g) ⬝ n') := by rw [@Group.assoc]
      _ = n⁻¹ ⬝ n' := by rw [Group.inv_l, Group.id_abs_l]
    rw [Htmp]
    exact N.mul_mem (N.inv_mem Hn) Hn'
  }
  inh := by {
    simp
    exact ⟨ g, Group.id, N.id_mem, Group.id_abs_r ⟩
  }
}

def quotient_mul {G: Type u} [Group G] {N: NormalSubgroup G} (A B : QuotientGroup N) : QuotientGroup N := {
  classes := fun h => ∃ a, A.classes a ∧ ∃ b, B.classes b ∧ a ⬝ b = h
  cong := by {
    simp
    intros h n Hn a Ha b Hb Heq
    constructor
    constructor
    · exact Ha

    let b' := b ⬝ n
    have Hb' : B.classes b' := QuotientGroup.cong _ Hn Hb
    have Heq' : a ⬝ b' = h ⬝ n := by {
      dsimp [b']
      rw [← Group.assoc, Heq]
    }
    exact ⟨ b', ⟨ Hb', Heq' ⟩ ⟩
  }
  cong_inv := by {
    simp
    intros ab ab' a Ha b Hb Heq a' Ha' b' Hb' Heq'
    rw [← Heq, ← Heq', inv_dist]
    let Htmp := calc b⁻¹ ⬝ (a⁻¹) ⬝ (a' ⬝ b')
        = b⁻¹ ⬝ (a⁻¹ ⬝ (a' ⬝ b')) := by rw [@Group.assoc]
      _ = b⁻¹ ⬝ ((a⁻¹ ⬝ a') ⬝ b') := by rw [@Group.assoc]
      _ = b⁻¹ ⬝ (a⁻¹ ⬝ a') ⬝ b' := by rw [← @Group.assoc]
    rw [Htmp]
    let Hn := A.cong_inv Ha Ha'
    rcases (normal_comm_r (b⁻¹) (a⁻¹ ⬝ a') Hn) with ⟨ n₁, Hn₁, Heq₁ ⟩
    rw [Heq₁, Group.assoc]
    apply N.mul_mem Hn₁
    exact B.cong_inv Hb Hb'
  }
  inh := by {
    simp
    rcases A.inh with ⟨ a, Ha ⟩
    rcases B.inh with ⟨ b, Hb ⟩
    exact ⟨ a ⬝ b, a, Ha, b, Hb, rfl ⟩
  }
}

def quotient_inv {G: Type u} [Group G] {N: NormalSubgroup G} (A : QuotientGroup N) : QuotientGroup N := {
  classes := fun h => ∃ a, A.classes a ∧ a ⬝ h = Group.id
  cong := by {
    simp
    intros h n Hn a Ha Heq
    let a' := n⁻¹ ⬝ a
    have Ha' : A.classes a' := by {
      let Haina : N.pred (a⁻¹ ⬝ (n⁻¹) ⬝ a) := by {
        let Htmp : N.pred (a⁻¹ ⬝ (n⁻¹) ⬝ _) := N.conj_mem (N.inv_mem Hn)
        rw [double_inv] at Htmp
        exact Htmp
      }

      let Htmp := A.cong Haina Ha
      have Htmp2 := calc
        a ⬝ (a⁻¹ ⬝ (n⁻¹) ⬝ a) = a ⬝ (a⁻¹ ⬝ (n⁻¹)) ⬝ a := by rw [← @Group.assoc]
        _ = n⁻¹ ⬝ a := by rw [← @Group.assoc, @Group.inv_r, @Group.id_abs_l]
      rw [Htmp2] at Htmp
      exact Htmp
    }
    constructor
    constructor
    · exact Ha'
    · exact calc
        a' ⬝ (h ⬝ n) = n⁻¹ ⬝ a ⬝ h ⬝ n := by rw [← @Group.assoc]
        _ = n⁻¹ ⬝ (a ⬝ h) ⬝ n := by rw [← @Group.assoc]
        _ = Group.id := by rw [Heq, Group.id_abs_r, Group.inv_l]
  }
  cong_inv := by {
    simp
    intros ai bi a Ha Hainv b Hb Hbinv
    rw [inv_uniq_r _ _ Hainv, inv_uniq_r _ _ Hbinv, double_inv]
    exact A.cong_inv_symm Ha Hb
  }
  inh := by {
    simp
    rcases A.inh with ⟨ a, Ha ⟩
    exact ⟨ a⁻¹, a, Ha, Group.inv_r ⟩
  }
}

instance {G: Type u} [Group G] {N: NormalSubgroup G} : Group (QuotientGroup N) where
  id := quotient_proj N Group.id
  mul := quotient_mul
  inv := quotient_inv

  assoc := by {
    intros A B C
    ext g
    unfold quotient_mul
    simp
    constructor
    · intros h
      rcases h with ⟨ h, ⟨ a, Ha, b, Hb, Heq1 ⟩, ⟨ c, Hc, Heq2 ⟩⟩
      rw [← Heq1] at Heq2
      rw [← Heq2]
      exact ⟨ a, Ha, b ⬝ c, ⟨ b, Hb, c, Hc, rfl ⟩, Eq.symm Group.assoc ⟩
    · intros h
      rcases h with ⟨ a, Ha, h, ⟨ b, Hb, c, Hc, Heq1⟩, Heq2 ⟩
      rw [← Heq2, ← Heq1]
      exact ⟨ a ⬝ b, ⟨ a, Ha, b, Hb, rfl ⟩, ⟨ c, Hc, Group.assoc ⟩⟩
  }

  id_abs_l := by {
    intros A
    ext g
    simp [quotient_mul, quotient_proj]
    constructor
    · intros Ha
      rcases Ha with ⟨ a, ⟨ n, Hn, Ha ⟩ , b, Hb, Heq ⟩
      rw [@Group.id_abs_l] at Ha
      rcases (normal_comm_l b n Hn) with ⟨ n', ⟨ Hl, Hr ⟩ ⟩
      rw [← Heq, ← Ha, Hr]
      exact A.cong Hl Hb
    · intros Hg
      exact ⟨ Group.id, ⟨ Group.id, ⟨ N.id_mem , Group.id_abs_l ⟩ ⟩, ⟨ g, ⟨ Hg, Group.id_abs_l ⟩  ⟩ ⟩
  }

  id_abs_r := by {
    intros A
    ext g
    simp [quotient_mul, quotient_proj]
    constructor
    · intros Ha
      rcases Ha with ⟨ a, Ha, b, ⟨ n, Hn, Hb ⟩ , Heq ⟩
      rw [← Heq, ← Hb, Group.id_abs_l]
      exact A.cong Hn Ha
    · intros Hg
      exact ⟨ g, Hg, Group.id, ⟨ Group.id, N.id_mem, Group.id_abs_l ⟩, Group.id_abs_r ⟩
  }

  inv_l := by {
    intros A
    ext g
    simp [quotient_mul, quotient_inv, quotient_proj]
    constructor
    · rintro ⟨ h, ⟨ a, Ha, Hinv ⟩, b, Hb, Heq ⟩
      rw [inv_uniq_r a h Hinv] at Heq
      have Htmp : Group.id ⬝ (a⁻¹ ⬝ b) = g := by rw [Heq, Group.id_abs_l]
      exact ⟨ a⁻¹ ⬝ b, QuotientGroup.cong_inv _ Ha Hb, Htmp ⟩
    · rintro ⟨ n, Hn, Heq ⟩
      rw [@Group.id_abs_l] at Heq
      rw [Heq] at Hn
      rcases A.inh with ⟨ a, Ha ⟩
      let Htmp : a⁻¹⬝ (a ⬝ g) = g := by rw [← @Group.assoc, @Group.inv_l, @Group.id_abs_l]
      exact ⟨ a⁻¹, ⟨ a, Ha, Group.inv_r ⟩, a ⬝ g, QuotientGroup.cong _ Hn Ha, Htmp ⟩
  }

  inv_r := by {
    intros A
    ext g
    simp [quotient_mul, quotient_inv, quotient_proj]
    constructor
    · rintro ⟨ a, Ha, h, ⟨ b, Hb, Hinv ⟩, Heq ⟩
      rw [inv_uniq_r b h Hinv] at Heq
      have Htmp : Group.id ⬝ (a ⬝ (b⁻¹)) = g := by rw [Heq, Group.id_abs_l]
      exact ⟨ a ⬝ (b⁻¹), QuotientGroup.cong_inv_symm _ Ha Hb, Htmp ⟩
    · rintro ⟨ n, Hn, Heq ⟩
      rw [@Group.id_abs_l] at Heq
      rw [Heq] at Hn
      rcases A.inh with ⟨ a, Ha ⟩
      let Htmp : g ⬝ a ⬝ (a⁻¹) = g := by rw [@Group.assoc, @Group.inv_r, @Group.id_abs_r]
      exact ⟨ g ⬝ a, QuotientGroup.cong_symm _ Hn Ha, a⁻¹, ⟨ a, Ha, Group.inv_r ⟩, Htmp ⟩
  }
namespace Hom

open Group

structure Hom (G H : Type u) [Group G] [Group H] where
  ap: G -> H
  hom_cond: ∀ { g h : G }, ap (g ⬝ h) = ((ap g) ⬝ (ap h))

structure Iso (G H: Type u) [Group G] [Group H] extends Hom G H where
  bij: Function.Bijective ap

def kernel_has {G H : Type u} [Group G] [H_s : Group H] (f: Hom G H)
  := fun (g: G) => (f.ap g) = H_s.id

lemma hom_id_to_id {G H : Type u} [Group G] [Group H] (f: Hom G H) : (f.ap id) = Group.id :=
  calc f.ap id = (f.ap id) ⬝ id := by rw [@id_abs_r]
  _ = (f.ap id) ⬝ ((f.ap id) ⬝ ((f.ap id)⁻¹)) := by rw [@inv_r]
  _ = (f.ap id) ⬝ (f.ap id) ⬝ ((f.ap id)⁻¹) := by rw [← @assoc]
  _ = (f.ap (id ⬝ id)) ⬝ ((f.ap id)⁻¹) := by rw [@Hom.hom_cond]
  _ = (f.ap id) ⬝ ((f.ap id)⁻¹) := by rw [@id_abs_r]
  _ = Group.id := by rw [@inv_r]

theorem kernel_has_id {G H : Type u} [Group G] [Group H] (f: Hom G H) : kernel_has f id := by {
  unfold kernel_has
  exact hom_id_to_id f
}

theorem kernel_has_inv {G H : Type u} [Group G] [Group H] (f: Hom G H) : ∀ {g : G}, kernel_has f g -> kernel_has f (g⁻¹):= by {
  unfold kernel_has
  intros g Hg
  calc f.ap (g⁻¹) = Group.id ⬝ (f.ap (g⁻¹)) := by rw [id_abs_l]
  _ = (f.ap g) ⬝ (f.ap (g⁻¹)) := by rw [Hg]
  _ = f.ap (g ⬝ (g⁻¹)) := by rw [Hom.hom_cond]
  _ = f.ap id := by rw [inv_r]
  _ = Group.id := hom_id_to_id f
}

def kernel_subgroup {G H : Type u} [Group G] [Group H] (f: Hom G H) : Subgroup G :=
  {
    pred := kernel_has f
    id_mem := kernel_has_id f
    mul_mem := by {
      unfold kernel_has
      intros _ _ Ha Hb
      rw [@Hom.hom_cond, Ha, Hb, id_abs_r]
    }
    inv_mem := fun {g} a => kernel_has_inv f a
  }

end Hom
