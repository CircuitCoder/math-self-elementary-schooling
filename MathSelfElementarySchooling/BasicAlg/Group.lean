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

lemma double_inv {G: Type u} [Group G] { g: G } : (g⁻¹)⁻¹ = g := calc
  g⁻¹⁻¹ = g⁻¹⁻¹ ⬝ Group.id := by rw [Group.id_abs_r]
  _ = g⁻¹⁻¹ ⬝ ((g⁻¹) ⬝ g) := by rw [Group.inv_l]
  _ = g⁻¹⁻¹ ⬝ (g⁻¹) ⬝ g := by rw [Group.assoc]
  _ = Group.id ⬝ g := by rw [Group.inv_l]
  _ = g := Group.id_abs_l

/- Normal subgroup and quotient groups -/
structure NormalSubgroup (G: Type u) [Group G] extends Subgroup G where
  conj_mem: ∀ { h g : G }, pred h -> pred (g ⬝ h ⬝ (g⁻¹))

@[ext]
structure QuotientGroup {G: Type u} [Group G] (N: NormalSubgroup G) where
  classes: G -> Prop
  cong: ∀ { g n: G }, N.pred n -> classes g -> classes (g ⬝ n)

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
}

instance {G: Type u} [Group G] {N: NormalSubgroup G} : Group (QuotientGroup N) where
  id := quotient_proj N Group.id
  mul := quotient_mul
  inv := quotient_inv

  assoc := by {
    intros a b c
    ext g
    unfold quotient_mul
    simp
    sorry -- TODO
  }

  id_abs_l := by {
    intros A
    ext g
    simp [quotient_mul, quotient_proj]
    constructor
    · intros Ha
      rcases Ha with ⟨ a, ⟨ n, Hn, Ha ⟩ , b, Hb, Heq ⟩
      rw [@Group.id_abs_l] at Ha
      rcases (normal_comm_l b n _) with ⟨ n', ⟨ Hl, Hr ⟩ ⟩
      rw [← Ha, Hr] at Heq
      rw [← Heq]
      exact A.cong Hl Hb
    · intros Hg
      exact ⟨ Group.id, ⟨ Group.id, _ ⟩, ⟨ g, _ ⟩ ⟩
  }

  id_abs_r := by {
    intros A
    ext g
    simp [quotient_mul, quotient_proj]
    constructor
    · intros Ha
      rcases Ha with ⟨ a, Ha, b, ⟨ n, Hn, Hb ⟩ , Heq ⟩
      rw [@Group.id_abs_l] at Hb
      rw [← Hb] at Heq
      rw [← Heq]
      exact A.cong _ Ha
    · intros Hg
      exact ⟨ _, _, _ ⟩
  }

  inv_l := sorry -- TODO
  inv_r := sorry -- TODO

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
