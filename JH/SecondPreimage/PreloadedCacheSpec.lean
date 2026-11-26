/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.TrialSpec

/-!
# Separating the fixed cache from subsequent records

Compile a fixed older transcript into a program while keeping later records explicit.
-/

@[expose] public section

namespace JH

variable {n : ℕ}

/-- Answer requests already in the fixed cache before consulting any later records. -/
def TrialProgram.preloadCache (old : Transcript n) (program : TrialProgram n) : TrialProgram n :=
  match program with
  | .done terminal => .done terminal
  | .query request resume =>
      match old.cachedReply request with
      | some answer => preloadCache old (resume answer)
      | none => .query request (fun answer ↦ preloadCache old (resume answer))
termination_by structural program

/-- Keep the frontier request and compile the fixed cache into its continuations. -/
def FreshFrontier.preloadCache (old : Transcript n) : FreshFrontier n → FreshFrontier n
  | .done terminal => .done terminal
  | .query request resume =>
      .query request (fun answer ↦ TrialProgram.preloadCache old (resume answer))

namespace PreloadedCacheSpec

/-- The fixed prefix keeps priority whenever both parts contain matching records. -/
def CachedReplyAppend : Prop :=
  ∀ {n : ℕ} (old suffix : Transcript n) (request : Query n),
    (old ++ suffix).cachedReply request = (old.cachedReply request).or (suffix.cachedReply request)

/-- Preloading the original cache yields the same fresh frontier as starting with the original
records followed by the new records. -/
def FrontierLaw : Prop :=
  ∀ {n : ℕ} (program : TrialProgram n) (old suffix : Transcript n),
    (TrialProgram.preloadCache old program).nextFresh suffix =
      FreshFrontier.preloadCache old (program.nextFresh (old ++ suffix))

/-- After the run, put the fixed prefix back into each completed result. -/
def BoundedLaw : Prop :=
  ∀ {n : ℕ} (fuel : ℕ) (program : TrialProgram n) (old suffix : Transcript n),
    TrialProgram.independentBounded fuel program (old ++ suffix) =
      (TrialProgram.independentBounded fuel (TrialProgram.preloadCache old program) suffix).map
        (Option.map fun result ↦ {result with records := old ++ result.records})

end PreloadedCacheSpec

end JH
