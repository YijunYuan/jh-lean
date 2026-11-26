/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.FreshFrontier
public import JH.Oracle.Lazy.BoundedSpec
public import JH.Oracle.Lazy.Trial

/-!
# The law of lazy sampling with a fresh-access budget

The adaptive lazy law persists when both experiments stop on an attempt to exceed the fresh
record budget. The proof splits the current posterior by the next fresh answer and resumes with
one unit less fuel. Starting from an empty transcript gives the budget-restricted real trial
law.
-/

@[expose] public section

namespace JH.TrialProgram

/-- The bounded lazy sampler has the law of the bounded run against one posterior permutation. -/
theorem lazyBounded_eq_map : BoundedLazySpec.BoundedLaw := by
  intro n fuel program old possible
  induction fuel generalizing program old with
  | zero =>
    cases reached : program.nextFresh old <;>
      simp only [lazyBounded, runFreshBounded, reached] <;>
      exact (PMF.map_const _ _).symm
  | succ fuel ih =>
    cases reached : program.nextFresh old with
    | done terminal =>
      simp only [lazyBounded, runFreshBounded, reached]
      exact (PMF.map_const _ _).symm
    | query request resume =>
      rw [lazyBounded, reached]
      refine Eq.trans ?_
        (Probability.map_bindOnSupport_filter (old.posterior possible) request.reply _)
      apply congrArg ((old.posterior possible).map request.reply).bindOnSupport
      funext answer supported
      rw [ih (resume answer), ← Transcript.posterior_update old possible request answer supported]
      let fiber := (old.posterior possible).filter (request.reply ⁻¹' {answer})
        (Probability.fiber_witness _ _ supported)
      -- Within this fiber, the fixed permutation takes the same branch and writes the same pair.
      change fiber.map _ = fiber.map _
      classical
      apply PMF.ext
      intro outcome
      simp only [PMF.map_apply]
      refine tsum_congr fun π ↦ ?_
      by_cases present : π ∈ fiber.support
      · have answered : request.reply π = answer := ((PMF.mem_support_filter_iff _).mp present).1
        have sameRecord : request.record π = request.recordOfReply answer :=
          (request.record_eq_recordOfReply π).trans (congrArg request.recordOfReply answered)
        have step : runFreshBounded π (fuel + 1) program old =
            runFreshBounded π fuel (resume (request.reply π)) (old ++ [request.record π]) := by
          simp only [runFreshBounded.eq_1 π (fuel + 1) program old, reached]
        rw [step, answered, sameRecord]
        rfl
      · have zero : fiber π = 0 := (PMF.apply_eq_zero_iff fiber π).mpr present
        simp [zero]

/-- With no initial records, lazy sampling reproduces the actual fixed-target trial law,
returning `none` precisely on runs that exceed the record budget. -/
theorem lazyBounded_fixedTarget : BoundedLazySpec.FixedTrialLaw := by
  intro α n strategy initial padding fuel
  rw [lazyBounded_eq_map fuel (ofStrategy strategy initial padding) []
    (Transcript.empty_possible n),
    Transcript.posterior_empty]
  apply congrArg (uniformPermutation n).map
  funext π
  simpa only [ofStrategy_run strategy π initial padding, List.length_nil, Nat.zero_add] using
    runFreshBounded_eq_by_budget π fuel (ofStrategy strategy initial padding) []
      (fun i ↦ Fin.elim0 i)

end JH.TrialProgram
