/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Coupling.ReplySpec
public import JH.Oracle.TrialProgram

/-!
# The separation hazard at a common fresh query

Marginals, support, and separation bounds for a coupled fresh query.
-/

@[expose] public section

namespace JH

open scoped ENNReal

namespace Transcript

variable {n : ℕ}

theorem forward_miss (old : Transcript n) (address : State n)
    (miss : old.cachedReply ⟨.forward, address⟩ = none) :
    address ∉ old.observedInputs := by
  intro seen
  obtain ⟨label, same⟩ := seen
  have cached := (old.cachedReply_eq_none_iff ⟨.forward, address⟩).mp miss
  have hit : old.any (Query.hasAddress ⟨.forward, address⟩) = true :=
    List.any_eq_true.mpr ⟨old.get label, List.getElem_mem label.isLt, decide_eq_true same⟩
  rw [cached] at hit
  contradiction

@[deprecated (since := "2026-11-25")] alias forwardFresh := forward_miss

theorem backward_miss (old : Transcript n) (address : State n)
    (miss : old.cachedReply ⟨.backward, address⟩ = none) :
    address ∉ old.observedOutputs := by
  intro seen
  obtain ⟨label, same⟩ := seen
  have cached := (old.cachedReply_eq_none_iff ⟨.backward, address⟩).mp miss
  have hit : old.any (Query.hasAddress ⟨.backward, address⟩) = true :=
    List.any_eq_true.mpr ⟨old.get label, List.getElem_mem label.isLt, decide_eq_true same⟩
  rw [cached] at hit
  contradiction

@[deprecated (since := "2026-11-25")] alias backwardFresh := backward_miss

/-- On a common history, couple the fresh permutation reply and independent proposal. -/
noncomputable def coupleFresh (old : Transcript n) (witness : Permutation n)
    (consistent : old.Consistent witness) (request : Query n)
      (miss : old.cachedReply request = none) :
    PMF (State n × State n) :=
  match request with
  | ⟨.forward, address⟩ =>
      (old.partialPermutation witness consistent).coupleForward
        ⟨address, old.forward_miss address miss⟩
  | ⟨.backward, address⟩ =>
      (old.partialPermutation witness consistent).coupleBackward
        ⟨address, old.backward_miss address miss⟩

/-- A fresh reply avoids the observed outputs for a forward request and the observed inputs for
an inverse request. -/
def ReplyUnused (old : Transcript n) (request : Query n) (reply : State n) : Prop :=
  match request.direction with
  | .forward => reply ∉ old.observedOutputs
  | .backward => reply ∉ old.observedInputs

end Transcript

namespace FreshStepSpec

/-- The two components of a fresh coupling have the conditional permutation and independent reply
laws. -/
def Marginals : Prop :=
  ∀ {n : ℕ} (old : Transcript n) (witness : Permutation n) (consistent : old.Consistent witness)
    (request : Query n) (miss : old.cachedReply request = none),
    let coupled := old.coupleFresh witness consistent request miss
    coupled.map Prod.fst =
        (old.partialPermutation witness consistent).conditionedUniform.map request.reply ∧
      coupled.map Prod.snd = PartialPermutation.uniformFinite (State n)

/-- On the support of the coupling, the permutation reply is unused and an unused independent
reply is shared. -/
def CoupledSupport : Prop :=
  ∀ {n : ℕ} (old : Transcript n) (witness : Permutation n) (consistent : old.Consistent witness)
    (request : Query n) (miss : old.cachedReply request = none) (replies : State n × State n),
    replies ∈ (old.coupleFresh witness consistent request miss).support →
      old.ReplyUnused request replies.1 ∧
        (replies.1 = replies.2 ↔ old.ReplyUnused request replies.2)

/-- The per-fresh-query hazard of separation in (8). -/
def Hazard : Prop :=
  ∀ {n : ℕ} (old : Transcript n) (witness : Permutation n) (consistent : old.Consistent witness)
    (request : Query n) (miss : old.cachedReply request = none),
    (old.coupleFresh witness consistent request miss).toOuterMeasure {pair | pair.1 ≠ pair.2} ≤
      (old.length : ℝ≥0∞) / (((2 ^ n) ^ 2 : ℕ) : ℝ≥0∞)

end FreshStepSpec

end JH
