--import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.GroupTheory.Coset
--import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Data.Set.Finite

open Fintype
open Coset
open Subgroup


variable (G : Type ) [Group G] [Fintype G]
variable (H : Subgroup G) [Fintype H]
variable (V : Type ) [AddCommMonoid V][Module ℂ V]
variable (W : Type ) [AddCommMonoid W][Module ℂ W]

variable (ρV : Representation ℂ G V)
variable (ρW : Representation ℂ G W)

#check (1 : G) -- Identity element
#check ∀ (a b : G), a * b = b * a -- Commutativity
#check ∀ (a : G), a * a⁻¹ = 1 -- Inverse element
#check ∀ (g h : G), (ρV g) • (ρV h) = ρV (g*h)


theorem Lagrange  : (card H) ∣ (card G) := by
  classical simp [card_eq_card_quotient_mul_card_subgroup H]

theorem Frobenius_repocity
