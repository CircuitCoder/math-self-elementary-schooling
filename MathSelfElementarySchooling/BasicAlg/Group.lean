import Mathlib.Init.Function
import Mathlib.Data.Quot
-- import Aesop
-- open Classical

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

infixl:90 "⬝" => Group.mul
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

lemma Group.mul_flip_left {G : Type u} [Group G] { a b c : G }
  : a ⬝ b = c -> b = a⁻¹ ⬝ c := by {
    intros H
    calc
      b = a⁻¹ ⬝ a ⬝ b := by rw [Group.inv_l, Group.id_abs_l]
      _ = a⁻¹ ⬝ (a ⬝ b) := by rw [Group.assoc]
      _ = a⁻¹ ⬝ c := by rw [H]
  }

lemma Group.mul_flip_right {G : Type u} [Group G] { a b c : G }
  : a ⬝ b = c -> a = c ⬝ (b⁻¹) := by {
    intros H
    calc
      a = a ⬝ (b ⬝ (b⁻¹)) := by rw [Group.inv_r, Group.id_abs_r]
      _ = a ⬝ b ⬝ (b⁻¹) := by rw [Group.assoc]
      _ = c ⬝ (b⁻¹) := by rw [H]
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

instance NormalSubgroup.coset_congr {G: Type u} [Group G] (self: NormalSubgroup G) : Setoid G where
  r g₁ g₂ := ∃ (h : G), self.pred h ∧ g₁ ⬝ h = g₂
  iseqv := {
    refl := fun g => ⟨ Group.id, ⟨ self.id_mem, Group.id_abs_r ⟩  ⟩
    symm := by {
      intros x y
      rintro ⟨ h, Hmem, Heq ⟩
      refine ⟨ h⁻¹, self.inv_mem Hmem, ?_ ⟩
      apply Eq.symm
      apply Group.mul_flip_right
      assumption
    }
    trans := by {
      intros x y z
      rintro ⟨ h₁, Hmem₁, Heq₁ ⟩
      rintro ⟨ h₂, Hmem₂, Heq₂ ⟩
      refine ⟨ h₁ ⬝ h₂, self.mul_mem Hmem₁ Hmem₂, ?_ ⟩
      rw [← Group.assoc, Heq₁, Heq₂]
    }
  }

def QuotientGroup {G : Type u} [Group G] (N: NormalSubgroup G) := Quotient N.coset_congr
def QuotientGroup.mk (G : Type u) [Group G] (N : NormalSubgroup G) := QuotientGroup N
infixl:80 "/" => QuotientGroup.mk

abbrev coset_modulo { G : Type u } [Group G] (g : G) (N : NormalSubgroup G) : G / N := Quotient.mk N.coset_congr g
infixl:80 "%%" => coset_modulo
theorem quotient_mul_functoriality { G : Type u } [Group G] {N : NormalSubgroup G}
  (a₁ b₁ a₂ b₂ : G) (Ha : N.coset_congr.r a₁ a₂) (Hb : N.coset_congr.r b₁ b₂) : a₁ ⬝ b₁ %% N = a₂ ⬝ b₂ %% N
  := by {
    simp [Setoid.r] at Ha Hb
    rcases Ha with ⟨ ha, Hha, Heqa ⟩
    rcases Hb with ⟨ hb, Hhb, Heqb ⟩
    rw [← Heqa, ← Heqb]
    apply Quotient.sound
    rcases normal_comm_l b₁ ha Hha with ⟨ ha', Hha', Heqa' ⟩
    have Heq : a₁⬝b₁⬝(ha'⬝hb) = a₁⬝ha⬝(b₁⬝hb) := calc
      _ = a₁ ⬝ (b₁ ⬝ ha' ⬝ hb) := by repeat rw [Group.assoc]
      _ = a₁ ⬝ (ha ⬝ b₁ ⬝ hb) := by rw [Heqa']
      _ = _ := by repeat rw [Group.assoc]
    exact ⟨ ha' ⬝ hb, N.mul_mem Hha' Hhb, Heq ⟩
  }

theorem quotient_inv_functoriality { G : Type u } [Group G] {N : NormalSubgroup G}
  (a₁ a₂ : G) (Heq : N.coset_congr.r a₁ a₂) : a₁⁻¹ %% N = a₂⁻¹ %% N
  := by {
    simp [Setoid.r] at Heq
    rcases Heq with ⟨ h, Hh, Heq ⟩
    apply Quotient.sound
    rw [← Heq, inv_dist]
    rcases normal_comm_l (a₁⁻¹) (h⁻¹) (N.inv_mem Hh) with ⟨ h', Hh', Heq' ⟩
    rw [Heq']
    exact ⟨ h', Hh', rfl ⟩
  }

instance {G: Type u} [Group G] {N: NormalSubgroup G} : Group (G / N) where
  id := Group.id %% N
  mul := Quotient.lift₂ (fun (a b : G) => a ⬝ b %% N) quotient_mul_functoriality
  inv := Quotient.lift (fun a => a⁻¹ %% N) quotient_inv_functoriality

  assoc := by {
    apply Quotient.ind₂
    intros a b
    apply Quotient.ind
    intros c
    repeat rw [@Quotient.lift₂_mk]
    rw [Group.assoc]
  }

  id_abs_l := by {
    apply Quotient.ind
    intros a
    rw [@Quotient.lift₂_mk, Group.id_abs_l]
  }
  id_abs_r := by {
    apply Quotient.ind
    intros a
    rw [@Quotient.lift₂_mk, Group.id_abs_r]
  }
  inv_l := by {
    apply Quotient.ind
    intros a
    rw [@Quotient.lift_mk, @Quotient.lift₂_mk, Group.inv_l]
  }
  inv_r := by {
    apply Quotient.ind
    intros a
    rw [@Quotient.lift_mk, @Quotient.lift₂_mk, Group.inv_r]
  }

lemma quotient_mul_functoriality' { G : Type u } [Group G] {N : NormalSubgroup G}
  (a b : G) : (a %% N) ⬝ (b %% N) = a ⬝ b %% N := by rfl

lemma quotient_inv_functoriality' { G : Type u } [Group G] {N : NormalSubgroup G}
  (a : G) : a⁻¹ %% N = a⁻¹ %% N := by rfl

namespace Hom

open Group

structure Hom (G H : Type u) [Group G] [Group H] where
  ap: G -> H
  hom_cond: ∀ { g h : G }, ap (g ⬝ h) = ((ap g) ⬝ (ap h))

instance (G H : Type u) [Group G] [Group H] : CoeFun (Hom G H) (fun _ => G -> H) where
  coe m := m.ap

structure SurHom (G H: Type u) [Group G] [Group H] extends Hom G H where
  sur: Function.Surjective ap

structure InjHom (G H: Type u) [Group G] [Group H] extends Hom G H where
  inj: Function.Injective ap

structure Iso (G H: Type u) [Group G] [Group H] extends SurHom G H, InjHom G H

def kernel_has {G H : Type u} [Group G] [H_s : Group H] (f: Hom G H)
  := fun (g: G) => (f g) = H_s.id

lemma Hom.hom_id {G H : Type u} [Group G] [Group H] (f: Hom G H) : (f id) = Group.id :=
  calc f id = (f id) ⬝ id := by rw [@id_abs_r]
  _ = (f id) ⬝ ((f id) ⬝ ((f id)⁻¹)) := by rw [@inv_r]
  _ = (f id) ⬝ (f id) ⬝ ((f id)⁻¹) := by rw [← @assoc]
  _ = (f (id ⬝ id)) ⬝ ((f id)⁻¹) := by rw [@Hom.hom_cond]
  _ = (f id) ⬝ ((f id)⁻¹) := by rw [@id_abs_r]
  _ = Group.id := by rw [@inv_r]

lemma Hom.hom_inv {G H : Type u} [Group G] [Group H] { f : Hom G H } (g : G)
  : f (g⁻¹) = (f g)⁻¹ := by {
    apply inv_uniq_l
    rw [← f.hom_cond, Group.inv_l, Hom.hom_id]
  }

theorem Kernel.ker_id {G H : Type u} [Group G] [Group H] (f: Hom G H) : kernel_has f id := by {
  unfold kernel_has
  exact Hom.hom_id f
}

theorem Kernel.ker_inv {G H : Type u} [Group G] [Group H] (f: Hom G H) : ∀ {g : G}, kernel_has f g -> kernel_has f (g⁻¹):= by {
  unfold kernel_has
  intros g Hg
  calc f (g⁻¹) = Group.id ⬝ (f (g⁻¹)) := by rw [id_abs_l]
  _ = (f g) ⬝ (f (g⁻¹)) := by rw [Hg]
  _ = f (g ⬝ (g⁻¹)) := by rw [Hom.hom_cond]
  _ = f id := by rw [inv_r]
  _ = Group.id := Hom.hom_id f
}

def Kernel {G H : Type u} [Group G] [Group H] (f: Hom G H) : NormalSubgroup G :=
  {
    pred := kernel_has f
    id_mem := Kernel.ker_id f
    mul_mem := by {
      unfold kernel_has
      intros _ _ Ha Hb
      rw [@Hom.hom_cond, Ha, Hb, id_abs_r]
    }
    inv_mem := fun {g} a => Kernel.ker_inv f a
    conj_mem := fun { h g } => by {
      unfold kernel_has
      simp
      intros Hk
      rw [Hom.hom_cond, Hom.hom_cond, Hk, Group.id_abs_r, ← Hom.hom_cond, Group.inv_r, Kernel.ker_id]
    }
  }

theorem injective_hom { G H : Type u } [Group G] [Group H] (f : InjHom G H) : ∀ (g : G), kernel_has f.toHom g <-> g = Group.id := by {
  intros g
  constructor
  · unfold kernel_has
    rw [← Kernel.ker_id f.toHom]
    intros Heq
    exact f.inj Heq
  · intros Heq
    rw [Heq]
    exact Kernel.ker_id f.toHom
}

lemma kernel_congr { G H : Type u } [Group G] [Group H] { f : Hom G H }
  (g₁ g₂ : G) : (Kernel f).coset_congr.r g₁ g₂ -> f g₁ = f g₂ := by {
    simp [Setoid.r, Kernel, kernel_has]
    intros k Hkid Heq
    rw [← Heq, Hom.hom_cond, Hkid, Group.id_abs_r]
  }

def surjective_hom_iso_quot { G H : Type u } [Group G] [Group H] (f : SurHom G H) : Iso (G / (Kernel f.toHom)) H := {
  ap := Quotient.lift f.ap kernel_congr
  hom_cond := by {
    apply Quotient.ind₂
    simp
    intros a b
    rw [quotient_mul_functoriality', @Quotient.lift_mk]
    exact f.hom_cond
  }
  sur := by {
    unfold Function.Surjective; simp; intros b
    rcases (f.sur b) with ⟨ h, Hh ⟩
    exact ⟨ h %% (Kernel f.toHom), Hh ⟩
  }
  inj := by {
    unfold Function.Injective; simp
    apply Quotient.ind₂; simp; intros a b Heq
    apply Quotient.sound
    simp [HasEquiv.Equiv, Setoid.r]
    refine ⟨ a⁻¹ ⬝ b, ?_ ,?_ ⟩
    · simp [Kernel, kernel_has]
      rw [Hom.hom_cond, Hom.hom_inv, Heq, inv_l]
    · rw [← assoc, inv_r, id_abs_l]
  }
}

end Hom
