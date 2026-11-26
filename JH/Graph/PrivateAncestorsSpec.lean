/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.MengerSpec

/-!
# Private ancestors for a minimal cover

Private ancestors in a minimal cover and bounds on their number.
-/

@[expose] public section

namespace JH.Graph

/-- A subfamily of at most `k` targets preserves the union of ancestors in `A`.
Each retained target has an ancestor in `A` that reaches no other retained
target. Reflexive reachability includes the zero-edge path at a common vertex. -/
def PrivateAncestorSubcover (V : Type*) [Finite V] : Prop :=
  ∀ (E : V → V → Prop) (A : Set V) (B : Finset V) (k : ℕ),
    (¬ HasDisjointPaths E A (↑B : Set V) (k + 1)) →
      ∃ C : Finset V, C ⊆ B ∧ C.card ≤ k ∧
        (∀ a ∈ A, (∃ b ∈ C, Relation.ReflTransGen E a b) ↔
          (∃ b ∈ B, Relation.ReflTransGen E a b)) ∧
        ∀ b ∈ C, ∃ a ∈ A, Relation.ReflTransGen E a b ∧
          ∀ c ∈ C, c ≠ b → ¬ Relation.ReflTransGen E a c

end JH.Graph
