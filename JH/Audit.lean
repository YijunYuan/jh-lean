/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH

/-!
# Type and axiom checks for the formalization

Checks the types of the exported proofs against their specifications and prints their
transitive axiom dependencies.
-/

@[expose] public section

example : JH.ModelSpec.WordCard := JH.word_card
example : JH.ModelSpec.RecordEdge := JH.record_edge_iff_compress
example : JH.ModelSpec.RecordEdges := JH.record_edges
example : JH.ModelSpec.RealWalk := JH.real_walk_iff_covered_run
example : JH.ModelSpec.VirtualWalk := JH.virtual_walk_iff_nonempty_covered_run
example : JH.ModelSpec.FixedTargetSuccessWitness := JH.fixed_target_success_witness

example : JH.ExperimentSpec.CacheReply := JH.cache_reply
example : JH.ExperimentSpec.Verification := JH.verify_blocks
example : JH.ExperimentSpec.TrialWitness := JH.trial_witness
example : JH.LazyPermutationSpec.TranscriptCompletions :=
    JH.Transcript.partialPermutation_extends_iff
example : JH.LazyPermutationSpec.ForwardFibers := JH.PartialPermutation.forward_fibers
example : JH.LazyPermutationSpec.BackwardFibers := JH.PartialPermutation.backward_fibers
example : JH.LazyPermutationSpec.ForwardUniform := JH.PartialPermutation.forward_uniform
example : JH.LazyPermutationSpec.BackwardUniform := JH.PartialPermutation.backward_uniform

example : JH.Graph.EvolutionSpec.Inheritance := JH.Graph.Boundary.inheritance
example : JH.Graph.EvolutionSpec.Graft := JH.Graph.Boundary.graft_invariants
example : JH.Graph.EvolutionSpec.GraftTermination := JH.Graph.Boundary.graft_termination
example : JH.Graph.RecordEvolutionSpec.InitialBoundary := JH.Graph.initial_boundary_invariants
example : JH.Graph.RecordEvolutionSpec.GraftThresholds := JH.Graph.record_graft_thresholds
example : JH.Graph.RoundSpec.RecordIndices := JH.Graph.appended_record_indices
example : JH.Graph.RoundSpec.Existence := JH.Graph.round_exists
example : JH.Graph.RoundSpec.Continuation := JH.Graph.round_continuation
example (V : Type*) [Finite V] : JH.Graph.DirectedVertexMenger V :=
  JH.Graph.directed_vertex_menger V
example : JH.Graph.EndpointsSpec.SupportBounds := JH.Graph.endpoint_support_bounds
example : JH.Graph.EndpointsSpec.TotalBounds := JH.Graph.endpoint_total_bounds
example : JH.Graph.AddedPathSpec.LastNewSplit := JH.Graph.last_new_split
example : JH.Graph.AddedPathSpec.LastTwoNewSplit := JH.Graph.last_two_new_split
example : JH.Graph.AddedPathSpec.LastNewSegments := JH.Graph.last_new_segments
example : JH.Graph.AddedPathSpec.AtMostOneAncestors := JH.Graph.at_most_one_new_ancestors
example : JH.Graph.AddedPathSpec.NoReuseAncestors := JH.Graph.no_reuse_ancestors
example : JH.Graph.ShiftTestSpec.NecessaryShift := JH.Graph.necessary_shift
example : JH.Graph.ShiftTestSpec.CandidateCard := JH.Graph.shift_candidate_card
example : JH.Graph.ShiftTestSpec.UniformCandidateProbability :=
    JH.Graph.uniform_candidate_probability
example : JH.Graph.ShiftTestSpec.UniformNewPathProbability := JH.Graph.uniform_new_path_probability
example (V : Type*) [Finite V] : JH.Graph.PrivateAncestorSubcover V :=
  JH.Graph.private_ancestor_subcover V

example : JH.Probability.VilleBound := JH.Probability.ville_bound
example : JH.Probability.CompensatedExpSupermartingale :=
  JH.Probability.compensated_exp_supermartingale
example : JH.Probability.SingleBarrierTail := JH.Probability.single_barrier_tail_spec

example : JH.Analysis.TwoConvex := JH.Analysis.two_convex
example : JH.Analysis.WeightedConvex := JH.Analysis.weighted_convex
example : JH.Analysis.ThetaOptimal := JH.Analysis.theta_optimal
example : JH.Analysis.ThetaOptimalValue := JH.Analysis.theta_optimal_value

-- The verification script reads the axiom report printed for each audited declaration.
set_option linter.hashCommand false

#print axioms JH.word_card
#print axioms JH.record_edge_iff_compress
#print axioms JH.record_edges
#print axioms JH.real_walk_iff_covered_run
#print axioms JH.virtual_walk_iff_nonempty_covered_run
#print axioms JH.fixed_target_success_witness
#print axioms JH.cache_reply
#print axioms JH.verify_blocks
#print axioms JH.trial_witness
#print axioms JH.PartialPermutation.complete
#print axioms JH.Transcript.partialPermutation_extends_iff
#print axioms JH.PartialPermutation.forward_fibers
#print axioms JH.PartialPermutation.backward_fibers
#print axioms JH.PartialPermutation.forward_uniform
#print axioms JH.PartialPermutation.backward_uniform

#print axioms JH.Graph.walk_iff_reaches
#print axioms JH.Graph.Boundary.inheritance
#print axioms JH.Graph.Boundary.graft_invariants
#print axioms JH.Graph.Boundary.graft_termination
#print axioms JH.Graph.initial_boundary_invariants
#print axioms JH.Graph.record_graft_thresholds
#print axioms JH.Graph.appended_record_indices
#print axioms JH.Graph.round_exists
#print axioms JH.Graph.round_continuation
#print axioms JH.Graph.reaches_iff_exists_isPath
#print axioms JH.Graph.directed_vertex_menger
#print axioms JH.Graph.endpoint_support_bounds
#print axioms JH.Graph.endpoint_total_bounds
#print axioms JH.Graph.last_new_split
#print axioms JH.Graph.last_two_new_split
#print axioms JH.Graph.last_new_segments
#print axioms JH.Graph.at_most_one_new_ancestors
#print axioms JH.Graph.no_reuse_ancestors
#print axioms JH.Graph.necessary_shift
#print axioms JH.Graph.shift_candidate_card
#print axioms JH.Graph.uniform_candidate_probability
#print axioms JH.Graph.uniform_new_path_probability
#print axioms JH.Graph.private_ancestor_subcover

#print axioms JH.Probability.ville_bound
#print axioms JH.Probability.compensated_exp_supermartingale
#print axioms JH.Probability.single_barrier_tail_spec
#print axioms JH.Analysis.two_convex
#print axioms JH.Analysis.weighted_convex
#print axioms JH.Analysis.theta_optimal
#print axioms JH.Analysis.theta_optimal_value
#print axioms JH.Parameters.Params.PreCertificate
#print axioms JH.Parameters.Params.SPRCertificate
#print axioms JH.Parameters.Params.WeightedPreCertificate
#print axioms JH.Parameters.Params.CommonCertificate.flow_tail_le
#print axioms JH.Parameters.Params.NuChoice.barrier_tail_le
#print axioms JH.Parameters.Params.IntersectionCondition.tail_le
#print axioms JH.Parameters.Params.PreCertificate.separation_tail_le
#print axioms JH.Parameters.Params.PreCertificate.occupancy_tail_le
#print axioms JH.Parameters.Params.PreCertificate.cumulative_drift_le
#print axioms JH.Parameters.Params.SPRCertificate.separation_tail_le
#print axioms JH.Parameters.Params.SPRCertificate.occupancy_tail_le
#print axioms JH.Parameters.Params.SPRCertificate.collision_tail_le
#print axioms JH.Parameters.Params.WeightedPreCertificate.cumulative_drift_le
#print axioms JH.PreimageSpec.FiniteBound
#print axioms JH.PreimageSpec.WeightedFiniteBound
#print axioms JH.PreimageSpec.ExplicitSqrtBound

/-!
# Type and axiom checks for the formalization

Checks the types of the exported proofs against their specifications and prints their
transitive axiom dependencies.
-/

example : JH.TrialProgramSpec.FixedTrial :=
  JH.TrialProgram.ofStrategy_run
example : JH.TrialProgramSpec.ReplayCylinder :=
  JH.TrialProgram.run_consistent_replay_iff

example : JH.LazyTrialSpec.PosteriorUpdate :=
  JH.Transcript.posterior_update
example : JH.LazyTrialSpec.FreshUniform :=
  JH.Transcript.fresh_uniform
example : JH.LazyTrialSpec.RecursiveLaw :=
  JH.TrialProgram.lazyRun_eq_map
example : JH.LazyTrialSpec.FixedTrialLaw :=
  JH.TrialProgram.lazyRun_fixedTarget

example : JH.FreshFrontierSpec.QueryIsFresh :=
  JH.TrialProgram.nextFresh_miss
example : JH.FreshFrontierSpec.PreservesRun :=
  JH.TrialProgram.nextFresh_run
example : JH.FreshFrontierSpec.BoundedRun :=
  JH.TrialProgram.runFreshBounded_eq_by_budget

example : JH.BoundedLazySpec.BoundedLaw :=
  JH.TrialProgram.lazyBounded_eq_map
example : JH.BoundedLazySpec.FixedTrialLaw :=
  JH.TrialProgram.lazyBounded_fixedTarget

example : JH.ReplyCouplingSpec.ConditionalReplacement :=
  JH.ReplyCoupling.sample_eq_conditional_replacement
example : JH.ReplyCouplingSpec.FirstMarginal :=
  JH.ReplyCoupling.sample_map_fst
example : JH.ReplyCouplingSpec.SecondMarginal :=
  JH.ReplyCoupling.sample_map_snd
example : JH.ReplyCouplingSpec.SupportedReplies :=
  JH.ReplyCoupling.sample_support
example : JH.ReplyCouplingSpec.Disagreement :=
  JH.ReplyCoupling.sample_disagreement
example : JH.ReplyCouplingSpec.ForwardPermutationMarginal :=
  JH.PartialPermutation.coupleForward_permutation_marginal
example : JH.ReplyCouplingSpec.BackwardPermutationMarginal :=
  JH.PartialPermutation.coupleBackward_permutation_marginal
example : JH.ReplyCouplingSpec.IndependentCoordinates :=
  JH.Query.uniform_reply_coords
example : JH.ReplyCouplingSpec.IndependentCoordinatesMass :=
  JH.Query.uniform_reply_coords_mass
example : JH.ReplyCouplingSpec.UniformReplyFromCoordinates :=
  JH.Query.uniform_reply_from_coords

example : JH.FreshStepSpec.Marginals :=
  JH.fresh_step_marginals
example : JH.FreshStepSpec.CoupledSupport :=
  JH.fresh_step_support
example : JH.FreshStepSpec.Hazard :=
  JH.fresh_step_hazard

example : JH.IndependentTrialSpec.CoordinateLaw :=
  JH.TrialProgram.independentCoordinatesBounded_eq
example : JH.IndependentTrialSpec.BudgetSupport :=
  JH.TrialProgram.independentBounded_support

example : JH.CoupledTrialSpec.Marginals :=
  JH.TrialProgram.coupledBounded_marginals
example : JH.CoupledTrialSpec.Agreement :=
  JH.TrialProgram.coupledBounded_agreement
example : JH.CoupledTrialSpec.ShiftedBound :=
  JH.TrialProgram.coupledBounded_shifted_bound
example : JH.CoupledTrialSpec.SeparationBound :=
  JH.TrialProgram.coupledBounded_separation_bound

example : JH.SuccessTransferSpec.BoundedAcceptance :=
  JH.TrialProgram.bounded_acceptance_le
example : JH.SuccessTransferSpec.StrategyTransfer :=
  JH.strategy_success_le_independent
example : JH.SuccessTransferSpec.Transfer :=
  JH.fixedTarget_success_le_independent
example : JH.SuccessTransferSpec.ParameterTransfer :=
  JH.fixedTarget_success_le_independent_params
example : JH.SuccessTransferSpec.IndependentTrace :=
  JH.TrialProgram.independent_success_trace

example : JH.CoordinateTapeSpec.SplitLaw :=
  JH.CoordinateTape.split_law
example : JH.CoordinateTapeSpec.RunLaw :=
  JH.TapeState.run_law
example : JH.CoordinateTapeSpec.PrefixAgreement :=
  JH.TapeState.prefix_agreement
example : JH.CoordinateTapeSpec.LiveRound :=
  JH.TapeState.live_round
example : JH.CoordinateTapeSpec.TerminalRound :=
  JH.TapeState.terminal_round

example : JH.Separation.OneStep :=
  JH.Separation.mass_bind_le
example : JH.Separation.FiniteTime :=
  JH.Separation.mass_states_le
example : JH.Separation.AllowanceSum :=
  JH.Separation.sum_hazards
example : JH.Separation.Formula4 :=
  JH.Separation.mass_states_le_formula4
example : JH.Separation.Formula4Real :=
  JH.Separation.mass_states_le_formula4_real

example : JH.Probability.DisintegrationSpec.MapBindFilter :=
  JH.Probability.map_bindOnSupport_filter
example : JH.Probability.DisintegrationSpec.FilterFilter :=
  JH.Probability.filter_filter

example : JH.Probability.TapeTestsSpec.AdaptedProduct :=
  JH.Probability.TapeTests.adapted_product_bound

example : JH.Graph.PatternsSpec.InputIdentification :=
  JH.Graph.input_pattern_identification
example : JH.Graph.PatternsSpec.TwoGroups :=
  JH.Graph.pattern_two_groups
example : JH.Graph.PatternsSpec.TranslationCounts :=
  JH.Graph.translation_counts

example : JH.Graph.PotentialSpec.SingletonMode :=
  JH.Graph.singleton_mode_is_point_column
example : JH.Graph.PotentialSpec.InitialPotential :=
  JH.Graph.initial_translated_potential
example : JH.Graph.PotentialSpec.GraftPointWeight :=
  JH.Graph.graft_point_weight
example : JH.Graph.PotentialSpec.DeletionPayment :=
  JH.Graph.deletion_pays_column

example : JH.Graph.GraftLedgerSpec.RoundPayment :=
  JH.Graph.round_graft_payment
example : JH.Graph.GraftLedgerSpec.RoundModeDecrease :=
  JH.Graph.round_mode_decrease_after_deletion

example : JH.Graph.DriftEventsSpec.AncestorRowProbability :=
  JH.Graph.ancestor_row_probability
example : JH.Graph.DriftEventsSpec.ReuseProbability :=
  JH.Graph.reuse_probability
example : JH.Graph.DriftEventsSpec.EmptySupportNoGrowth :=
  JH.Graph.empty_support_no_growth

example : JH.Graph.DriftChargeSpec.Pointwise :=
  JH.Graph.pattern_increment_pointwise
example : JH.Graph.DriftChargeSpec.BoundedIncrement :=
  JH.Graph.translated_increment_bounded

example : JH.Graph.DriftMeanSpec.PatternParts :=
  JH.Graph.pattern_charge_means
example : JH.Graph.DriftMeanSpec.EqualMean :=
  JH.Graph.translated_eq_mean
example : JH.Graph.DriftMeanSpec.WeightedMean :=
  JH.Graph.translated_weighted_mean
example : JH.Graph.DriftMeanSpec.WeightedTotalPointMean :=
  JH.Graph.total_point_weighted_mean

example : JH.Graph.FlowWitnessSpec.FirstOccurrence :=
  JH.Walk.first_occurrence
example : JH.Graph.FlowWitnessSpec.LastOccurrence :=
  JH.Walk.last_occurrence
example : JH.Graph.FlowWitnessSpec.Extract :=
  JH.Graph.extract_flow_witness
example : JH.Graph.FlowWitnessSpec.RecordCount :=
  JH.Graph.flow_witness_record_count
example : JH.Graph.FlowWitnessSpec.PrefixTest :=
  JH.Graph.flow_test_on_prefix

example : JH.Graph.BoundaryEventsSpec.ForwardTrim :=
  JH.Graph.BoundaryEvents.forward_trim
example : JH.Graph.BoundaryEventsSpec.ForwardInheritanceWitness :=
  JH.Graph.BoundaryEvents.forward_inheritance_witness
example : JH.Graph.BoundaryEventsSpec.ForwardIntersectionWitness :=
  JH.Graph.BoundaryEvents.forward_intersection_witness
example : JH.Graph.BoundaryEventsSpec.ForwardInheritedCount :=
  JH.Graph.BoundaryEvents.forward_inherited_count
example : JH.Graph.BoundaryEventsSpec.ForwardInheritanceProbability :=
  JH.Graph.BoundaryEvents.forward_inheritance_probability
example : JH.Graph.BoundaryEventsSpec.ForwardIntersectionProbability :=
  JH.Graph.BoundaryEvents.forward_intersection_probability

example : JH.Graph.StoppedGraphSpec.ThresholdPriority :=
  JH.Graph.graph_threshold_priority
example : JH.Graph.StoppedGraphSpec.ActiveReplay :=
  JH.Graph.graph_active_replay
example : JH.Graph.StoppedGraphSpec.ActiveParameters :=
  JH.Graph.graph_active_parameters
example : JH.Graph.StoppedGraphSpec.InitialParameters :=
  JH.Graph.graph_initial_parameters
example : JH.Graph.StoppedGraphSpec.FixedInitialOccupancy :=
  JH.Graph.graph_fixed_initial_occupancy
example : JH.Graph.StoppedGraphSpec.ResidualMonotone :=
  JH.Graph.graph_residual_monotone
example : JH.Graph.StoppedGraphSpec.SuccessStops :=
  JH.Graph.graph_success_stops

example : JH.Graph.FirstStopSpec.AcceptanceCovered :=
  JH.Graph.independent_acceptance_covered

example : JH.Parameters.UniformSpec.ParameterFeasibility :=
  JH.Parameters.uniform_parameter_feasibility
example : JH.Parameters.UniformSpec.ExplicitCertificate :=
  JH.Parameters.explicit_certificate
example : JH.Parameters.UniformSpec.UnroundedLoss :=
  JH.Parameters.unrounded_loss
example : JH.Parameters.UniformSpec.LossAsymptotic :=
  JH.Parameters.uniform_loss_asymptotic

example : JH.RandomTargetSpec.MessageCard :=
  JH.message_card
example : JH.RandomTargetSpec.TargetOnlySPR :=
  JH.secondPreimageTrial_target_only
example : JH.RandomTargetSpec.AveragingFixedTarget :=
  JH.RandomTarget.average_fixed_target
example : JH.RandomTargetSpec.AveragedReduction :=
  JH.RandomTarget.randomTarget_reduction_of_average
example : JH.RandomTargetSpec.Reduction :=
  JH.RandomTarget.randomTarget_reduction

#print axioms JH.TrialProgram.ofStrategy_run
#print axioms JH.TrialProgram.run_consistent_replay_iff
#print axioms JH.Transcript.posterior_update
#print axioms JH.Transcript.fresh_uniform
#print axioms JH.TrialProgram.lazyRun_eq_map
#print axioms JH.TrialProgram.lazyRun_fixedTarget
#print axioms JH.TrialProgram.nextFresh_miss
#print axioms JH.TrialProgram.nextFresh_run
#print axioms JH.TrialProgram.runFreshBounded_eq_by_budget
#print axioms JH.TrialProgram.lazyBounded_eq_map
#print axioms JH.TrialProgram.lazyBounded_fixedTarget
#print axioms JH.ReplyCoupling.sample_eq_conditional_replacement
#print axioms JH.ReplyCoupling.sample_map_fst
#print axioms JH.ReplyCoupling.sample_map_snd
#print axioms JH.ReplyCoupling.sample_support
#print axioms JH.ReplyCoupling.sample_disagreement
#print axioms JH.PartialPermutation.coupleForward_permutation_marginal
#print axioms JH.PartialPermutation.coupleBackward_permutation_marginal
#print axioms JH.Query.uniform_reply_coords
#print axioms JH.Query.uniform_reply_coords_mass
#print axioms JH.Query.uniform_reply_from_coords
#print axioms JH.fresh_step_marginals
#print axioms JH.fresh_step_support
#print axioms JH.fresh_step_hazard
#print axioms JH.TrialProgram.independentCoordinatesBounded_eq
#print axioms JH.TrialProgram.independentBounded_support
#print axioms JH.TrialProgram.coupledBounded_marginals
#print axioms JH.TrialProgram.coupledBounded_agreement
#print axioms JH.TrialProgram.coupledBounded_shifted_bound
#print axioms JH.TrialProgram.coupledBounded_separation_bound
#print axioms JH.TrialProgram.bounded_acceptance_le
#print axioms JH.strategy_success_le_independent
#print axioms JH.fixedTarget_success_le_independent
#print axioms JH.fixedTarget_success_le_independent_params
#print axioms JH.TrialProgram.independent_success_trace
#print axioms JH.CoordinateTape.split_law
#print axioms JH.TapeState.run_law
#print axioms JH.TapeState.prefix_agreement
#print axioms JH.TapeState.live_round
#print axioms JH.TapeState.terminal_round
#print axioms JH.Separation.mass_bind_le
#print axioms JH.Separation.mass_states_le
#print axioms JH.Separation.sum_hazards
#print axioms JH.Separation.mass_states_le_formula4
#print axioms JH.Separation.mass_states_le_formula4_real
#print axioms JH.Probability.map_bindOnSupport_filter
#print axioms JH.Probability.filter_filter
#print axioms JH.Probability.TapeTests.adapted_product_bound
#print axioms JH.Graph.input_pattern_identification
#print axioms JH.Graph.pattern_two_groups
#print axioms JH.Graph.translation_counts
#print axioms JH.Graph.singleton_mode_is_point_column
#print axioms JH.Graph.initial_translated_potential
#print axioms JH.Graph.graft_point_weight
#print axioms JH.Graph.deletion_pays_column
#print axioms JH.Graph.round_graft_payment
#print axioms JH.Graph.round_mode_decrease_after_deletion
#print axioms JH.Graph.ancestor_row_probability
#print axioms JH.Graph.reuse_probability
#print axioms JH.Graph.empty_support_no_growth
#print axioms JH.Graph.pattern_increment_pointwise
#print axioms JH.Graph.translated_increment_bounded
#print axioms JH.Graph.pattern_charge_means
#print axioms JH.Graph.translated_eq_mean
#print axioms JH.Graph.translated_weighted_mean
#print axioms JH.Graph.total_point_weighted_mean
#print axioms JH.Walk.first_occurrence
#print axioms JH.Walk.last_occurrence
#print axioms JH.Graph.extract_flow_witness
#print axioms JH.Graph.flow_witness_record_count
#print axioms JH.Graph.flow_test_on_prefix
#print axioms JH.Graph.BoundaryEvents.forward_trim
#print axioms JH.Graph.BoundaryEvents.forward_inheritance_witness
#print axioms JH.Graph.BoundaryEvents.forward_intersection_witness
#print axioms JH.Graph.BoundaryEvents.forward_inherited_count
#print axioms JH.Graph.BoundaryEvents.forward_inheritance_probability
#print axioms JH.Graph.BoundaryEvents.forward_intersection_probability
#print axioms JH.Graph.graph_threshold_priority
#print axioms JH.Graph.graph_active_replay
#print axioms JH.Graph.graph_active_parameters
#print axioms JH.Graph.graph_initial_parameters
#print axioms JH.Graph.graph_fixed_initial_occupancy
#print axioms JH.Graph.graph_residual_monotone
#print axioms JH.Graph.graph_success_stops
#print axioms JH.Graph.independent_acceptance_covered
#print axioms JH.Parameters.uniform_parameter_feasibility
#print axioms JH.Parameters.explicit_certificate
#print axioms JH.Parameters.unrounded_loss
#print axioms JH.Parameters.uniform_loss_asymptotic
#print axioms JH.message_card
#print axioms JH.secondPreimageTrial_target_only
#print axioms JH.RandomTarget.average_fixed_target
#print axioms JH.RandomTarget.randomTarget_reduction_of_average
#print axioms JH.RandomTarget.randomTarget_reduction

#print axioms JH.TapeState.records_prefix
#print axioms JH.TapeState.records_length_of_live
#print axioms JH.TapeState.recorded_round
#print axioms JH.Graph.transposeStateEdge_realRecordRelation
#print axioms JH.fixedTarget_bound_of_first_stops
#print axioms JH.preimage_finite_from_first_stops
#print axioms JH.weighted_preimage_finite_from_first_stops
#print axioms JH.explicit_sqrt_from_finite

example : JH.Graph.StoppedGraphSpec.EarliestRecord :=
  JH.Graph.graph_earliest_record
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardTrim :=
  JH.Graph.BackwardBoundaryEvents.backward_trim
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardInheritanceWitness :=
  JH.Graph.BackwardBoundaryEvents.backward_inheritance_witness
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardIntersectionWitness :=
  JH.Graph.BackwardBoundaryEvents.backward_intersection_witness
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardInheritedCount :=
  JH.Graph.BackwardBoundaryEvents.backward_inherited_count
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardInheritanceProbability :=
  JH.Graph.BackwardBoundaryEvents.backward_inheritance_probability
example : JH.Graph.BackwardBoundaryEventsSpec.BackwardIntersectionProbability :=
  JH.Graph.BackwardBoundaryEvents.backward_intersection_probability
example : JH.Graph.StoppedChargeSpec.LedgerGrowth :=
  JH.Graph.afterGrafting_ledger_le
example : JH.Graph.StoppedChargeSpec.ActiveChargeRange :=
  JH.Graph.active_charge_range
example : JH.Graph.StoppedChargeSpec.ActiveChargeMean :=
  JH.Graph.active_charge_mean
example : JH.Graph.StoppedChargeSpec.ActiveChargeWeightedMean :=
  JH.Graph.active_charge_weighted_mean
example : JH.Graph.StoppedChargeSpec.ActiveTotalPointWeightedMean :=
  JH.Graph.active_total_point_weighted_mean

#print axioms JH.Graph.graph_earliest_record
#print axioms JH.Graph.BackwardBoundaryEvents.backward_trim
#print axioms JH.Graph.BackwardBoundaryEvents.backward_inheritance_witness
#print axioms JH.Graph.BackwardBoundaryEvents.backward_intersection_witness
#print axioms JH.Graph.BackwardBoundaryEvents.backward_inherited_count
#print axioms JH.Graph.BackwardBoundaryEvents.backward_inheritance_probability
#print axioms JH.Graph.BackwardBoundaryEvents.backward_intersection_probability
#print axioms JH.Graph.afterGrafting_ledger_le
#print axioms JH.Graph.active_charge_range
#print axioms JH.Graph.active_charge_mean
#print axioms JH.Graph.active_charge_weighted_mean
#print axioms JH.Graph.active_total_point_weighted_mean

example : JH.Probability.AdaptiveMeanSpec.ProductBound :=
  JH.Probability.AdaptiveMean.adapted_product
example : JH.Probability.AdaptiveMeanSpec.FiniteBarrier :=
  JH.Probability.AdaptiveMean.finite_barrier
example : JH.Graph.BarrierModesSpec.LedgerCount :=
  JH.Graph.ledger_count
example : JH.Graph.BarrierModesSpec.TailExponent :=
  JH.Graph.ledger_tail_exponent

#print axioms JH.Probability.AdaptiveMean.adapted_product
#print axioms JH.Probability.AdaptiveMean.finite_barrier
#print axioms JH.Probability.AdaptiveMean.expect_adapted_round
#print axioms JH.Probability.AdaptiveMean.uniform_pair_tape
#print axioms JH.Probability.AdaptiveMean.probability_iUnion_le_card_mul
#print axioms JH.Graph.ledger_count
#print axioms JH.Graph.ledger_tail_exponent

example : JH.Graph.BoundaryMeanSpec.OccupancyTotals :=
  JH.Graph.BoundaryMean.occupancy_totals
example : JH.Graph.BoundaryMeanSpec.ForwardInheritanceMean :=
  JH.Graph.BoundaryMean.forward_inheritance_mean
example : JH.Graph.BoundaryMeanSpec.BackwardInheritanceMean :=
  JH.Graph.BoundaryMean.backward_inheritance_mean
example : JH.Graph.BoundaryMeanSpec.ForwardIntersectionMean :=
  JH.Graph.BoundaryMean.forward_intersection_mean
example : JH.Graph.BoundaryMeanSpec.BackwardIntersectionMean :=
  JH.Graph.BoundaryMean.backward_intersection_mean
example : JH.Graph.FlowTailSpec.EncodingCard :=
  JH.Graph.FlowTail.encoding_card
example : JH.Graph.FlowTailSpec.ConditionalTest :=
  JH.Graph.FlowTail.conditional_test
example : JH.Graph.FlowTailSpec.EncodedUnion :=
  JH.Graph.FlowTail.encoded_union
example : JH.Graph.FlowTailSpec.WitnessCovered :=
  JH.Graph.FlowTail.witness_covered
example : JH.Graph.FlowTailSpec.FirstStopBound :=
  JH.Graph.FlowTail.first_stop_bound

#print axioms JH.Graph.BoundaryMean.occupancy_totals
#print axioms JH.Graph.BoundaryMean.forward_inheritance_mean
#print axioms JH.Graph.BoundaryMean.backward_inheritance_mean
#print axioms JH.Graph.BoundaryMean.forward_intersection_mean
#print axioms JH.Graph.BoundaryMean.backward_intersection_mean
#print axioms JH.Graph.FlowTail.encoding_card
#print axioms JH.Graph.FlowTail.conditional_test
#print axioms JH.Graph.FlowTail.encoded_union
#print axioms JH.Graph.FlowTail.witness_covered
#print axioms JH.Graph.FlowTail.first_stop_bound

example : JH.Probability.BarrierReplaySpec.StopCovered :=
  JH.Probability.BarrierReplay.barrier_stop_covered
example : JH.Probability.BarrierReplaySpec.LocalRange :=
  JH.Probability.BarrierReplay.ledger_cost_range
example : JH.Probability.BarrierReplaySpec.LocalMean :=
  JH.Probability.BarrierReplay.ledger_cost_mean
example : JH.Probability.BarrierReplaySpec.WeightedLocalMean :=
  JH.Probability.BarrierReplay.ledger_cost_weighted_mean

#print axioms JH.Probability.BarrierReplay.barrier_stop_covered
#print axioms JH.Probability.BarrierReplay.ledger_cost_range
#print axioms JH.Probability.BarrierReplay.ledger_cost_mean
#print axioms JH.Probability.BarrierReplay.ledger_cost_weighted_mean

example : JH.Graph.BarrierTailSpec.EqualTail := JH.Graph.barrier_equal_tail
example : JH.Graph.BarrierTailSpec.WeightedTail := JH.Graph.barrier_weighted_tail

#print axioms JH.Graph.barrier_equal_tail
#print axioms JH.Graph.barrier_weighted_tail

example : JH.Probability.OccupancyTailSpec.EncodingCard :=
  JH.Probability.OccupancyTail.encoding_card
example : JH.Probability.OccupancyTailSpec.ConditionalTest :=
  JH.Probability.OccupancyTail.conditional_test
example : JH.Probability.OccupancyTailSpec.WitnessCovered :=
  JH.Probability.OccupancyTail.witness_covered
example : JH.Probability.OccupancyTailSpec.FirstStopBound :=
  JH.Probability.OccupancyTail.first_stop_bound
example : JH.SecondPreimageSpec.ObserveOriginal :=
  JH.TrialProgram.observe_original_run
example : JH.SecondPreimageSpec.ProgramLaw :=
  JH.TrialProgram.second_preimage_program
example : JH.SecondPreimageTraceSpec.DepartureAndReturn :=
  JH.SecondPreimageTrace.departure_and_return
example : JH.SecondPreimageTraceSpec.VerifiedOriginal :=
  JH.SecondPreimageTrace.verified_original
example : JH.SecondPreimageTraceSpec.VerifiedCoverage :=
  JH.SecondPreimageTrace.verified_coverage
example : JH.SecondPreimageTraceSpec.VerifiedMessages :=
  JH.SecondPreimageTrace.verified_messages

#print axioms JH.Probability.OccupancyTail.encoding_card
#print axioms JH.Probability.OccupancyTail.conditional_test
#print axioms JH.Probability.OccupancyTail.witness_covered
#print axioms JH.Probability.OccupancyTail.first_stop_bound
#print axioms JH.TrialProgram.observe_original_run
#print axioms JH.TrialProgram.second_preimage_program
#print axioms JH.SecondPreimageTrace.departure_and_return
#print axioms JH.SecondPreimageTrace.verified_original
#print axioms JH.SecondPreimageTrace.verified_coverage
#print axioms JH.SecondPreimageTrace.verified_messages

#print axioms JH.SecondPreimageSpec.FiniteBound

example : JH.Probability.IntersectionTailSpec.LocalIntersectionMean :=
  JH.Probability.IntersectionTail.local_intersection_mean
example : JH.Probability.IntersectionTailSpec.ActivePopulationMean :=
  JH.Probability.IntersectionTail.active_population_mean
example : JH.Probability.IntersectionTailSpec.Tail :=
  JH.Probability.IntersectionTail.first_stop_bound
example : JH.PreimageSpec.FiniteBound :=
  JH.preimage_finite
example : JH.PreimageSpec.WeightedFiniteBound :=
  JH.preimage_weighted_finite
example : JH.PreimageSpec.ExplicitSqrtBound :=
  JH.preimage_explicit_sqrt
example : JH.OriginalPhaseSpec.ContinuationLaw :=
  JH.OriginalPhase.continuation_law
example : JH.OriginalPhaseSpec.Budget :=
  JH.OriginalPhase.sample_budget
example : JH.OriginalPhaseSpec.CollisionTail :=
  JH.OriginalPhase.collision_tail
example : JH.OriginalPhaseSpec.CollisionFreeLength :=
  JH.OriginalPhase.sample_collision_free_length
example : JH.SecondPreimageCoverageSpec.OriginalReplay :=
  JH.SecondPreimageCoverage.original_replay
example : JH.SecondPreimageCoverageSpec.AcceptedCandidate :=
  JH.SecondPreimageCoverage.accepted_candidate
example : JH.SecondPreimageCoverageSpec.AcceptedPath :=
  JH.SecondPreimageCoverage.accepted_path
example : JH.PreloadedCacheSpec.CachedReplyAppend :=
  JH.Transcript.cachedReply_append
example : JH.PreloadedCacheSpec.FrontierLaw :=
  JH.TrialProgram.nextFresh_preloadCache
example : JH.PreloadedCacheSpec.BoundedLaw :=
  JH.TrialProgram.independentBounded_preloadCache
example : JH.Analysis.WeightedConstantSpec.Balance :=
  JH.Analysis.WeightedConstant.balance
example : JH.Analysis.WeightedConstantSpec.Attainment :=
  JH.Analysis.WeightedConstant.attainment
example : JH.Analysis.WeightedConstantSpec.UniqueMinimizer :=
  JH.Analysis.WeightedConstant.unique_minimizer
example : JH.Analysis.WeightedConstantSpec.MinMaxLowerBound :=
  JH.Analysis.WeightedConstant.minmax_lower_bound
example : JH.Analysis.WeightedConstantSpec.CriticalPoint :=
  JH.Analysis.WeightedConstant.critical_point
example : JH.Analysis.WeightedConstantSpec.FlowSlack :=
  JH.Analysis.WeightedConstant.flow_slack

#print axioms JH.Probability.IntersectionTail.local_intersection_mean
#print axioms JH.Probability.IntersectionTail.active_population_mean
#print axioms JH.Probability.IntersectionTail.first_stop_bound
#print axioms JH.preimage_finite
#print axioms JH.preimage_weighted_finite
#print axioms JH.preimage_explicit_sqrt
#print axioms JH.OriginalPhase.continuation_law
#print axioms JH.OriginalPhase.sample_budget
#print axioms JH.OriginalPhase.collision_tail
#print axioms JH.OriginalPhase.sample_collision_free_length
#print axioms JH.SecondPreimageCoverage.original_replay
#print axioms JH.SecondPreimageCoverage.accepted_candidate
#print axioms JH.SecondPreimageCoverage.accepted_path
#print axioms JH.Transcript.cachedReply_append
#print axioms JH.TrialProgram.nextFresh_preloadCache
#print axioms JH.TrialProgram.independentBounded_preloadCache
#print axioms JH.Analysis.WeightedConstant.balance
#print axioms JH.Analysis.WeightedConstant.attainment
#print axioms JH.Analysis.WeightedConstant.unique_minimizer
#print axioms JH.Analysis.WeightedConstant.minmax_lower_bound
#print axioms JH.Analysis.WeightedConstant.critical_point
#print axioms JH.Analysis.WeightedConstant.flow_slack

example : JH.SecondPreimageCouplingSpec.Transfer :=
  JH.second_preimage_transfer
example : JH.SecondPreimageSpec.FiniteBound :=
  JH.second_preimage_finite
example : JH.Parameters.WeightedLowerSpec.PowerRequirements :=
  JH.Parameters.WeightedLower.power_requirements
example : JH.Parameters.WeightedLowerSpec.Necessary :=
  JH.Parameters.WeightedLower.necessary
example : JH.Parameters.WeightedLowerSpec.UniformLower :=
  JH.Parameters.WeightedLower.uniform_lower
example : JH.Parameters.WeightedLimitsSpec.ParameterLimits :=
  JH.Parameters.rounded_weighted_parameter_limits
example : JH.Parameters.WeightedOptimalitySpec.FixedTargetQueryBound :=
  JH.Parameters.WeightedOptimality.fixed_target_query_bound

#print axioms JH.second_preimage_transfer
#print axioms JH.second_preimage_finite
#print axioms JH.Parameters.WeightedLower.power_requirements
#print axioms JH.Parameters.WeightedLower.necessary
#print axioms JH.Parameters.WeightedLower.uniform_lower
#print axioms JH.Parameters.rounded_weighted_parameter_limits
#print axioms JH.Parameters.WeightedOptimality.fixed_target_query_bound

example : JH.Parameters.WeightedUpperSpec.LossBound :=
  JH.Parameters.WeightedUpper.rounded_loss_bound
example : JH.Parameters.WeightedUpperSpec.CertificateFromGrowth :=
  JH.Parameters.WeightedUpper.certificate_from_growth
example : JH.Parameters.WeightedUpperSpec.EventualGrowth :=
  JH.Parameters.WeightedUpper.eventual_growth
example : JH.Parameters.WeightedUpperSpec.EventualConstruction :=
  JH.Parameters.WeightedUpper.eventual_construction
example : JH.Parameters.WeightedUpperSpec.OptimalUpper :=
  JH.Parameters.WeightedUpper.optimal_upper
example : JH.Parameters.WeightedUpperSpec.BudgetTransfer :=
  JH.Parameters.WeightedUpper.budget_transfer
example : JH.Parameters.WeightedOptimalitySpec.EventualFeasibility :=
  JH.Parameters.WeightedOptimality.eventual_feasibility
example : JH.Parameters.WeightedOptimalitySpec.LossAsymptotic :=
  JH.Parameters.WeightedOptimality.loss_asymptotic
example : JH.Parameters.WeightedOptimalitySpec.QueryLowerBound :=
  JH.Parameters.WeightedOptimality.query_lower_bound

#print axioms JH.Parameters.WeightedUpper.rounded_loss_bound
#print axioms JH.Parameters.WeightedUpper.certificate_from_growth
#print axioms JH.Parameters.WeightedUpper.eventual_growth
#print axioms JH.Parameters.WeightedUpper.eventual_construction
#print axioms JH.Parameters.WeightedUpper.optimal_upper
#print axioms JH.Parameters.WeightedUpper.budget_transfer
#print axioms JH.Parameters.WeightedOptimality.eventual_feasibility
#print axioms JH.Parameters.WeightedOptimality.loss_asymptotic
#print axioms JH.Parameters.WeightedOptimality.query_lower_bound
