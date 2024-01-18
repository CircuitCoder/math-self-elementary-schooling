import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Real.Basic

open Classical

/-
Basic definitions for a metric space
-/

universe u

class Metric (X: Type u) where
  dist: (a b: X) -> ℝ
  dist_pos: ∀ { a b : X }, dist a b >= 0
  dist_strict: ∀ { a b : X }, dist a b = 0 ↔ a = b
  dist_sym: ∀ { a b : X }, dist a b = dist b a
  dist_trig: forall { a b c : X }, dist a b + dist b c ≥ dist a c

def open_ball { X: Type u } [ m : Metric X ] (x : X) (d: ℝ) : Set X :=
  { y : X | m.dist x y < d }

def closed_ball { X: Type u } [ m : Metric X ] (x : X) (d: ℝ) : Set X :=
  { y : X | m.dist x y ≤ d }

def sphere { X: Type u } [ m : Metric X ] (x : X) (d: ℝ) : Set X :=
  { y : X | m.dist x y = d }

def IsInternalPt { X : Type u } [ Metric X ] (M : Set X) (x : X) : Prop :=
  ∃ r > 0, open_ball x r ⊆ M

def internal { X : Type u } [ Metric X ] (M : Set X) : Set X :=
  { x : X | IsInternalPt M x }

def IsOpen { X : Type u } [ Metric X ] (M : Set X) : Prop :=
  internal M = M

def IsClosed { X : Type u } [ Metric X ] (M : Set X) : Prop :=
  IsOpen Mᶜ

lemma positive_ball_contains { X : Type u } [ Metric X ] (x : X) (r : ℝ)
  : r > 0 -> x ∈ open_ball x r := by {
    intros rpos
    unfold open_ball
    refine Set.mem_setOf.mpr ?_
    have heq : Metric.dist x x = 0
    · rw [Metric.dist_strict]
    rw [heq]
    exact rpos
  }

lemma all_internal_open { X : Type u } [ Metric X ] (M : Set X)
  : (∀ x ∈ M, IsInternalPt M x) -> IsOpen M := by {
    intros h
    unfold IsOpen
    refine Set.Subset.antisymm ?h₁ h
    unfold internal
    have h2: ∀ x : X, IsInternalPt M x -> x ∈ M
    · intros x
      unfold IsInternalPt
      intros h3
      rcases h3 with ⟨r, rpos, inside⟩
      apply Set.mem_of_subset_of_mem inside
      exact positive_ball_contains x r rpos
    exact h2
  }

theorem open_pt_to_ball { X : Type u } [ Metric X ] ( M : Set X ) (x : X) :
  IsOpen M -> x ∈ M -> ∃ r > 0, open_ball x r ⊆ M := by {
    intros ho hx
    unfold IsOpen at ho
    rw [← ho] at hx
    unfold internal at hx
    rw [@Set.mem_setOf] at hx
    exact hx
  }

lemma univ_internal { X : Type u } [ Metric X ] (x : X)
  : IsInternalPt Set.univ x := by {
    unfold IsInternalPt
    have h : open_ball x 1 ⊆ Set.univ
    · exact Set.subset_univ _
    exact ⟨1, ⟨Real.zero_lt_one, h⟩⟩
  }

theorem empty_open { X : Type u } [ Metric X ] : @IsOpen X _ ∅ := by {
  apply all_internal_open
  intros x xinempty
  exact xinempty.elim
}

theorem univ_open { X : Type u } [ Metric X ] : @IsOpen X _ Set.univ := by {
  apply all_internal_open
  intros x _
  exact univ_internal x
}

theorem empty_close { X : Type u } [ Metric X ] : @IsClosed X _ ∅ := by {
  unfold IsClosed
  rw [@Set.compl_empty]
  exact univ_open
}

theorem univ_close { X : Type u } [ Metric X ] : @IsClosed X _ Set.univ := by {
  unfold IsClosed
  rw [@Set.compl_univ]
  exact empty_open
}

theorem open_union { X : Type u } [ Metric X ] { Ms : Set (Set X) }
  : (∀ M ∈ Ms, IsOpen M) -> IsOpen (⋃₀ Ms) := by {
    intros hopen
    apply all_internal_open
    intros x hx
    rw [@Set.mem_sUnion] at hx
    rcases hx with ⟨M, ⟨hMin, hxin⟩⟩

    unfold IsInternalPt

    let Mopen := hopen M hMin
    unfold IsOpen at Mopen
    rw [← Mopen] at hxin
    unfold internal at hxin
    rw [@Set.mem_setOf] at hxin
    unfold IsInternalPt at hxin
    rcases hxin with ⟨r, ⟨rgtz, ballin⟩⟩
    constructor
    constructor
    · exact rgtz
    · exact Set.subset_sUnion_of_subset Ms M ballin hMin
  }

lemma ball_inclusion { X : Type u } [ Metric X ] { x : X } { a b : ℝ }
  : a ≤ b -> open_ball x a ⊆ open_ball x b := by {
    intros alessb
    unfold open_ball
    refine Set.setOf_subset_setOf.mpr ?_
    intros _
    exact fun a_1 => lt_of_lt_of_le a_1 alessb
  }

theorem open_finite_sect { X : Type u } [ Metric X ] { Ms : Set (Set X) }
  : Set.Finite Ms -> (∀ M ∈ Ms, IsOpen M) -> IsOpen (⋂₀ Ms) := by {
    intros hfi hopen
    cases Set.eq_empty_or_nonempty (⋂₀ Ms) with
    | inl hempty => {
      rw [hempty]
      exact empty_open
    }
    | inr hne => {
      apply all_internal_open
      intros x xin
      rw [@Set.mem_sInter] at xin

      have hr : ∃ r > 0, ∀ M ∈ Ms, open_ball x r ⊆ M
      · apply @Set.Finite.induction_on' _ (fun S => ∃ r > 0, ∀ M ∈ S, open_ball x r ⊆ M) _ hfi
        · constructor
          exact ⟨ Real.zero_lt_one, fun M a => a.elim ⟩
        · intros a Mss hainMs _ _ hi
          rcases hi with ⟨ r, ⟨ rgtz, hrball ⟩ ⟩
          let cur := open_pt_to_ball a x (hopen a hainMs) (xin _ hainMs)
          rcases cur with ⟨ rc, ⟨ rcgtz, hrcball ⟩ ⟩
          constructor
          constructor
          · exact lt_min rgtz rcgtz
          · intros b hbin
            rw [Set.mem_insert_iff]at hbin
            cases hbin with
            | inl hbisa => {
              rw [hbisa]
              have hinc : open_ball x (min r rc) ⊆ open_ball x rc
              · apply ball_inclusion
                exact min_le_right r rc
              apply subset_trans hinc
              assumption
            }
            | inr hbinMss => {
              have hinc : open_ball x (min r rc) ⊆ open_ball x r
              · apply ball_inclusion
                exact min_le_left r rc
              apply subset_trans hinc
              exact hrball b hbinMss
            }
      rcases hr with ⟨ r, hr ⟩
      constructor
      constructor
      · exact hr.1
      · refine Set.subset_sInter ?inr.a.h.right.h
        exact hr.2
    }
  }

theorem closed_sect { X : Type u } [ m : Metric X ] { Ms : Set (Set X) }
  : (∀ M ∈ Ms, IsClosed M) -> IsClosed (⋂₀ Ms) := by {
    intros hcl
    have hcop : ∀ M ∈ Ms, IsOpen Mᶜ
    · intros M hMC
      exact hcl M hMC

    let Mcomp := Set.compl '' Ms

    unfold IsClosed
    rw [Set.compl_sInter]

    apply @open_union X m Mcomp
    intros M hMin
    rw [@Set.mem_image] at hMin
    rcases hMin with ⟨ M', ⟨ hM'in, hMC ⟩⟩
    rw [← hMC]
    apply hcop
    assumption
  }

theorem closed_finite_union { X : Type u } [ m : Metric X ] { Ms : Set (Set X) }
  : Set.Finite Ms -> (∀ M ∈ Ms, IsClosed M) -> IsClosed (⋃₀ Ms) := by {
    intros hfi hop
    have hcop : ∀ M ∈ Ms, IsOpen Mᶜ
    · intros M hMC
      exact hop M hMC

    let Mcomp := Set.compl '' Ms

    unfold IsClosed
    rw [Set.compl_sUnion]
    have HfiMcomp : Set.Finite (Set.compl '' Ms)
    · exact Set.Finite.image Set.compl hfi

    apply @open_finite_sect X m Mcomp HfiMcomp
    intros M hMin
    rw [@Set.mem_image] at hMin
    rcases hMin with ⟨ M', ⟨ hM'in, hMC ⟩⟩
    rw [← hMC]
    apply hcop
    assumption
  }

def IsClusterPt { X: Type u } [ Metric X ] ( M : Set X ) ( x : X ) : Prop
  := ∀ r > 0, Set.Nonempty (M ∩ ((open_ball x r) \ { x }))

def derived_set { X : Type u } [ Metric X ] ( M : Set X ) : Set X
  := { x | IsClusterPt M x }

def closure { X : Type u } [ Metric X ] ( M : Set X ) : Set X
  := M ∪ derived_set M

def closure' { X : Type u } [ Metric X ] ( M : Set X ) : Set X
  := { x | ∀ r > 0, Set.Nonempty (M ∩ (open_ball x r))}

lemma self_distance_zero { X : Type u } [ Metric X ] { x : X } : Metric.dist x x = 0 := by {
  rw [Metric.dist_strict]
}

lemma ball_contains_center { X : Type u } [ Metric X ] { x : X } { r : ℝ }
  : r > 0 -> x ∈ open_ball x r := by {
    intros Hrgtz
    unfold open_ball
    apply Set.mem_setOf.mpr
    rw [self_distance_zero]
    assumption
  }

theorem closure_def_equiv { X : Type u } [ Metric X ] : ∀ M : Set X, closure M = closure' M
  := by {
    intros M
    apply Set.ext
    intros x
    constructor
    · intros HinC
      unfold closure at HinC
      rw [Set.mem_union] at HinC
      cases HinC with
      | inl HinM => {
        unfold closure'
        apply Set.mem_setOf.mpr
        intros r Hrgtz
        constructor
        apply Set.mem_inter
        · exact HinM
        · apply ball_contains_center
          assumption
      }
      | inr HinD => {
        apply Set.mem_setOf.mpr
        intros r Hrgtz
        unfold derived_set at HinD
        rw [Set.mem_setOf] at HinD
        unfold IsClusterPt at HinD
        have Hdne : Set.Nonempty (M ∩ (open_ball x r \ {x}))
        · apply HinD
          assumption
        apply Set.inter_nonempty.mpr
        rw [Set.inter_nonempty] at Hdne
        rcases Hdne with ⟨ x', ⟨ Hx'inD, Hx'inB ⟩ ⟩
        rw [Set.mem_diff_singleton] at Hx'inB
        rcases Hx'inB with ⟨ Hx'inB ⟩
        constructor
        constructor
        · exact Hx'inD
        · exact Hx'inB
      }
    · intros HinC
      unfold closure
      unfold closure' at HinC
      rw [Set.mem_setOf] at HinC
      rw [Set.mem_union]
      cases Classical.em (x ∈ M) with
      | inl HxinM => exact Or.inl HxinM
      | inr HxninM => {
        apply Or.inr
        unfold derived_set
        rw [Set.mem_setOf]
        intros _ Hrgtz
        apply HinC at Hrgtz
        rcases Hrgtz with ⟨ x', Hx'in ⟩
        rw [Set.mem_inter_iff] at Hx'in
        constructor
        apply Set.mem_inter
        · exact Hx'in.left
        · rw [Set.mem_diff_singleton]
          have Hx'neqx : x' ≠ x
          · intros Heq
            rw [← Heq] at HxninM
            exact HxninM Hx'in.left
          exact ⟨ Hx'in.right, Hx'neqx ⟩
      }
  }

lemma closed_exterior { X : Type u } [ Metric X ] { M : Set X } { HMcl : IsClosed M }
  : ∀ x ∉ M, ∃ r > 0, ((open_ball x r) ∩ M) = ∅ := by {
    intros x Hxnin
    unfold IsClosed at HMcl
    unfold IsOpen at HMcl
    have Hxnin' : x ∈ Mᶜ
    · assumption

    rw [← HMcl] at Hxnin'
    unfold internal at Hxnin'
    rw [Set.mem_setOf] at Hxnin'
    rcases Hxnin' with ⟨ r, ⟨ Hrgtz, Hrbc ⟩ ⟩
    constructor
    constructor
    · exact Hrgtz
    · rw [← Set.not_nonempty_iff_eq_empty]
      by_contra Hnempty
      rcases Hnempty with ⟨ x', Hx' ⟩
      rw [Set.mem_inter_iff] at Hx'
      let Hx'inc := Set.mem_of_subset_of_mem Hrbc Hx'.left
      have Hx'nin : x' ∉ M
      · exact Hx'inc
      exact Hx'nin Hx'.right
  }

theorem closure_minimal { X : Type u } [ Metric X ] { M : Set X }
  : ∀ N : Set X, M ⊆ N ∧ IsClosed N -> (closure M) ⊆ N := by {
    intros N H
    rcases H with ⟨ HNsup, HNcl ⟩
    unfold closure
    apply Set.union_subset
    · assumption
    · unfold derived_set
      rw [Set.subset_def]
      intros x Hx
      rw [Set.mem_setOf] at Hx
      by_contra Hxnin
      have Hxbni : ∃ r > 0, ((open_ball x r) ∩ N) = ∅
      · apply closed_exterior
        assumption
        assumption
      unfold IsClusterPt at Hx
      rcases Hxbni with ⟨ r, ⟨ Hrgtz, Hbni ⟩ ⟩
      rcases Hx r Hrgtz with ⟨ x', Hx' ⟩
      rw [Set.mem_inter_iff, Set.mem_diff] at Hx'
      have Hx'in : x' ∈ (open_ball x r) ∩ N
      · apply Set.mem_inter
        · exact Hx'.right.left
        · exact Set.mem_of_subset_of_mem HNsup Hx'.left
      rw [Hbni] at Hx'in
      exact (Set.mem_empty_iff_false _).mp Hx'in
  }

lemma internal_supset_open { X : Type u } [ Metric X ] { M : Set X } : internal M ⊇ M -> IsOpen M := by {
  intros Hsup
  unfold IsOpen
  apply Set.Subset.antisymm
  · unfold internal
    rw [Set.subset_def]
    intros x Hx
    rw [Set.mem_setOf] at Hx
    unfold IsInternalPt at Hx
    rcases Hx with ⟨ r, Hrgtz, Hbin ⟩
    rw [Set.subset_def] at Hbin
    exact Hbin x (ball_contains_center Hrgtz)
  · assumption
}

theorem closure_closed { X : Type u } [ Metric X ] { M : Set X } : IsClosed (closure M) := by {
  unfold IsClosed
  apply internal_supset_open
  unfold internal
  unfold Superset
  rw [Set.subset_def]
  intros x Hxin
  rw [Set.mem_setOf]
  unfold IsInternalPt
  rw [closure_def_equiv] at Hxin
  unfold closure' at Hxin
  rw [Set.mem_compl_iff, Set.nmem_setOf_iff, not_forall] at Hxin
  rcases Hxin with ⟨ r, Hr ⟩
  rw [not_imp] at Hr

  constructor
  constructor
  · exact half_pos Hr.left
  · rw [Set.subset_def]
    intros y Hyin
    apply Set.mem_compl
    unfold closure
    intros Hyfalse
    rw [Set.mem_union] at Hyfalse
    cases Hyfalse with
    | inl HyinM => {
      have Hrgth : r ≥ r / 2
      · apply half_le_self
        exact le_of_lt Hr.left

      have Hyinb : y ∈ M ∩ open_ball x r
      · apply Set.mem_inter
        · assumption
        · apply Set.mem_of_subset_of_mem (ball_inclusion Hrgth)
          exact Hyin

      let Hempty : M ∩ open_ball x r = ∅ := Set.not_nonempty_iff_eq_empty.mp Hr.right
      exact Set.eq_empty_iff_forall_not_mem.mp Hempty y Hyinb
    }
    | inr HyinDM => {
      unfold derived_set at HyinDM
      rw [Set.mem_setOf] at HyinDM
      unfold IsClusterPt at HyinDM
      rcases (HyinDM (r / 2) (half_pos Hr.left)) with ⟨ z, HzinM, HzinB ⟩
      have HzinBB : Set.Nonempty (M ∩ open_ball x r)
      · constructor
        apply Set.mem_inter
        · exact HzinM
        · rw [Set.mem_diff] at HzinB
          unfold open_ball
          rw [Set.mem_setOf]
          have Hlt : Metric.dist x y + Metric.dist y z < r
          · unfold open_ball at Hyin HzinB
            rw [Set.mem_setOf] at Hyin HzinB
            rw [← add_halves r]
            apply add_lt_add
            assumption
            exact HzinB.left
          apply lt_of_le_of_lt Metric.dist_trig Hlt
      exact Hr.right HzinBB
    }
}

theorem closed_eq_closure { X : Type u } [ Metric X ] { M : Set X }
  : M = closure M -> IsClosed M := by {
    intros Heq
    rw [Heq]
    exact closure_closed
  }

theorem eq_closure_closed { X : Type u } [ Metric X ] { M : Set X }
  : IsClosed M -> M = closure M := by {
    intros Hcl
    have Hclin : closure M ⊆ M
    · apply closure_minimal
      exact ⟨ Eq.subset rfl, Hcl ⟩

    have Hincl : M ⊆ closure M
    · unfold closure
      exact Set.subset_union_left _ _

    exact Set.Subset.antisymm Hincl Hclin
  }

theorem closed_iff_eq_closure { X : Type u } [ Metric X ] { M : Set X }
  : M = closure M <-> IsClosed M := ⟨ closed_eq_closure, eq_closure_closed ⟩

def ContinousAt { X Y : Type u} [ Metric X ] [ Metric Y ] (f : X -> Y) (x₀ : X)
  := ∀ ε > 0, ∃ d > 0, ∀ x, Metric.dist x x₀ < d -> Metric.dist (f x) (f x₀) < ε

def Continous { X Y : Type u } [ Metric X ] [ Metric Y ] (f : X -> Y)
  := ∀ x : X, ContinousAt f x
