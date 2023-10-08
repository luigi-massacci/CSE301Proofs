import Mathlib.Tactic 

#check BinTree
namespace Lab5

inductive BinTree (α : Type _) where
| leaf (a : α)
| node (left : BinTree α) (right : BinTree α) 
deriving Repr, BEq

open BinTree

def mapBin {α β : Type _} (f : α → β) (t : BinTree α) : BinTree β :=
  match t with
  | (leaf a) => leaf (f a)
  | (node tL tR) => node (mapBin f tL) (mapBin f tR)

theorem mapId : mapBin (id : α → α) = id := by
  ext x 
  induction' x with val nL nR IHpL IHpR
  · simp only [mapBin]
    simp only [id]
  · simp only [mapBin]
    rw [IHpL, IHpR]
    simp only [id]



end Lab5