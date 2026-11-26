/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Independent.Trial
public import JH.SecondPreimage.PreloadedCacheSpec

/-!
# Separating the fixed cache from subsequent records

`TrialProgram.preloadCache` turns a fixed prefix of the log into deterministic replies in the
program. Earliest-match lookup gives that prefix priority even when both parts contain a
matching address. The independent trial can then keep just the later records for graph
analysis.
-/

@[expose] public section

namespace JH

/-- Lookup in a concatenated transcript consults the older prefix first. -/
theorem Transcript.cachedReply_append : PreloadedCacheSpec.CachedReplyAppend := by
  intro n old suffix request
  unfold Transcript.cachedReply
  rw [List.find?_append]
  cases old.find? request.hasAddress <;> rfl

namespace TrialProgram

variable {n : ℕ}

/-- Preloading the original cache yields the same fresh frontier as starting with the original
records followed by the new records. -/
theorem nextFresh_preloadCache : PreloadedCacheSpec.FrontierLaw := by
  intro n program old suffix
  induction program with
  | done terminal => rfl
  | query request resume ih =>
    cases earlier : old.cachedReply request with
    | some answer =>
      have combined : (old ++ suffix).cachedReply request = some answer := by
        rw [Transcript.cachedReply_append, earlier]
        rfl
      simpa only [preloadCache, earlier, nextFresh, combined] using ih answer
    | none =>
      have combined : (old ++ suffix).cachedReply request = suffix.cachedReply request := by
        rw [Transcript.cachedReply_append, earlier]
        rfl
      cases later : suffix.cachedReply request with
      | some answer =>
        simpa only [preloadCache, earlier, nextFresh, combined, later] using ih answer
      | none =>
        simp only [preloadCache, earlier, nextFresh, combined, later, FreshFrontier.preloadCache]

private theorem preloadCache_bounded_done (fuel : ℕ) (program : TrialProgram n)
    (old suffix : Transcript n) {terminal : Option (State n)}
    (reached : program.nextFresh (old ++ suffix) = .done terminal) :
    independentBounded fuel program (old ++ suffix) =
      (independentBounded fuel (preloadCache old program) suffix).map
        (Option.map fun result ↦ {result with records := old ++ result.records}) := by
  have trimmed : (preloadCache old program).nextFresh suffix = .done terminal := by
    simp only [nextFresh_preloadCache program old suffix, reached, FreshFrontier.preloadCache]
  simp only [independentBounded_of_done fuel program (old ++ suffix) reached,
    independentBounded_of_done fuel (preloadCache old program) suffix trimmed,
      PMF.pure_map, Option.map_some]

/-- Compiling the fixed cache into the program preserves the bounded outcome after restoring
that prefix to every completed transcript. -/
theorem independentBounded_preloadCache : PreloadedCacheSpec.BoundedLaw := by
  intro n fuel
  induction fuel with
  | zero =>
    intro program old suffix
    cases reached : program.nextFresh (old ++ suffix) with
    | done terminal => exact preloadCache_bounded_done 0 program old suffix reached
    | query request resume =>
      have trimmed : (preloadCache old program).nextFresh suffix =
          .query request (fun answer ↦ preloadCache old (resume answer)) := by
        simp only [nextFresh_preloadCache program old suffix, reached, FreshFrontier.preloadCache]
      simp only [independentBounded_zero_of_query program (old ++ suffix) reached,
        independentBounded_zero_of_query (preloadCache old program) suffix trimmed,
          PMF.pure_map, Option.map_none]
  | succ fuel ih =>
    intro program old suffix
    cases reached : program.nextFresh (old ++ suffix) with
    | done terminal => exact preloadCache_bounded_done (fuel + 1) program old suffix reached
    | query request resume =>
      have trimmed : (preloadCache old program).nextFresh suffix =
          .query request (fun answer ↦ preloadCache old (resume answer)) := by
        simp only [nextFresh_preloadCache program old suffix, reached, FreshFrontier.preloadCache]
      -- Both frontiers have the same miss, so append the same drawn pair to the explicit suffix.
      rw [independentBounded_succ_of_query fuel program (old ++ suffix) reached,
        independentBounded_succ_of_query fuel (preloadCache old program)
          suffix trimmed, PMF.map_bind]
      congr 1
      funext answer
      simpa only [Transcript.appendReply, List.append_assoc] using
        ih (resume answer) old (suffix.appendReply request answer)

end TrialProgram

end JH
