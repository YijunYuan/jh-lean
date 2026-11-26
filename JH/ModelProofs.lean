/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.ModelSpec

/-!
# From transcript edges to message blocks

A consistent oracle record gives a compression edge for each source rate in its input capacity
column. The queried input determines the unique block for each source. These facts establish
the relation between the compression function (3) and the record edges (6).

The walk equivalences translate records back to covered block sequences. A virtual starting
vertex enforces the nonempty sequence supplied by valid padding.
-/

@[expose] public section

namespace JH

/-- The state-coordinate space has exactly N = 2^n elements. -/
theorem word_card : ModelSpec.WordCard := by
  intro n
  exact (Fintype.card_congr (BitVec.equivFin (m := n)).toEquiv).trans (Fintype.card_fin _)

private theorem xor_cancel {n : ℕ} (a b : Word n) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem block_eq_of_input_eq {n : ℕ} {source address : State n} {block : Word n}
    (h : permInput source block = address) : block = source.2 ^^^ address.2 := by
  calc
    block = source.2 ^^^ (permInput source block).2 := (xor_cancel _ _).symm
    _ = source.2 ^^^ address.2 := by rw [h]

private theorem compress_eq_of_record {n : ℕ} (permutation : Permutation n) (record : Record n)
    (consistent : record.Consistent permutation) {source : State n} {block : Word n}
    (input_eq : permInput source block = record.input) :
    compress permutation source block = (source.2 ^^^ record.shift, record.output.2) := by
  have output_eq : permutation record.input = record.output := consistent
  unfold compress
  rw [input_eq, output_eq]
  apply Prod.ext
  · change record.output.1 ^^^ block = source.2 ^^^ (record.input.2 ^^^ record.output.1)
    rw [block_eq_of_input_eq input_eq, BitVec.xor_comm record.output.1, BitVec.xor_assoc]
  · rfl

/-- Each edge of a consistent record is realized by a unique block at its source. -/
theorem record_edge_iff_compress : ModelSpec.RecordEdge := by
  intro n permutation record consistent source target
  constructor
  · rintro ⟨capacity_eq, target_eq⟩
    -- XOR with the source rate recovers the block from the recorded address.
    let block := source.2 ^^^ record.input.2
    have input_eq : permInput source block = record.input :=
      Prod.ext capacity_eq (xor_cancel _ _)
    have output_eq := compress_eq_of_record permutation record consistent input_eq
    exact ⟨block, ⟨input_eq, output_eq.trans target_eq.symm⟩,
      fun _ h ↦ block_eq_of_input_eq h.1⟩
  · rintro ⟨block, ⟨input_eq, target_eq⟩, _⟩
    have capacity_eq : (permInput source block).1 = record.input.1 := congrArg Prod.fst input_eq
    exact ⟨capacity_eq,
      target_eq.symm.trans (compress_eq_of_record permutation record consistent input_eq)⟩

/-- The edges of a record are indexed by the source rate, so there are exactly `2 ^ n` edges. -/
theorem record_edges : ModelSpec.RecordEdges := by
  intro n record
  constructor
  · intro source target
    rw [Record.edges, Finset.mem_map]
    constructor
    · rintro ⟨rate, _, pair_eq⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj pair_eq
      exact ⟨rfl, rfl⟩
    · rintro ⟨capacity_eq, target_eq⟩
      exact ⟨source.2, Finset.mem_univ _, Prod.ext (Prod.ext capacity_eq.symm rfl) target_eq.symm⟩
  · simpa [Record.edges] using word_card n

private theorem covers_of_walk {n : ℕ} (permutation : Permutation n) (transcript : Transcript n)
    (consistent : transcript.Consistent permutation) {source target : State n}
    (path : Walk transcript.realEdge source target) :
    ∃ blocks : List (Word n), transcript.Covers permutation source blocks ∧
      run permutation source blocks = target := by
  induction path with
  | nil _ => exact ⟨[], trivial, rfl⟩
  | @cons source middle _ label edge _ ih =>
      obtain ⟨block, ⟨input_eq, rfl⟩, _⟩ :=
        (record_edge_iff_compress permutation (transcript.get label) (consistent label)
          source middle).mp edge
      obtain ⟨blocks, covers, run_eq⟩ := ih
      exact ⟨block :: blocks, ⟨⟨label, input_eq.symm⟩, covers⟩, run_eq⟩

private theorem walk_of_covers {n : ℕ} (permutation : Permutation n) (transcript : Transcript n)
    (consistent : transcript.Consistent permutation) (source : State n) (blocks : List (Word n))
    (covers : transcript.Covers permutation source blocks) :
    Nonempty (Walk transcript.realEdge source (run permutation source blocks)) := by
  induction blocks generalizing source with
  | nil => exact ⟨.nil source⟩
  | cons block blocks ih =>
      obtain ⟨⟨label, input_eq⟩, coversRest⟩ := covers
      have capacity_eq : (permInput source block).1 = (transcript.get label).input.1 :=
        congrArg Prod.fst input_eq.symm
      have edge : transcript.realEdge label source (compress permutation source block) :=
        ⟨capacity_eq,
          compress_eq_of_record permutation (transcript.get label) (consistent label)
            input_eq.symm⟩
      obtain ⟨rest⟩ := ih (compress permutation source block) coversRest
      exact ⟨.cons label edge rest⟩

/-- A walk between real states corresponds to a block sequence covered by the transcript. The
zero-edge walk corresponds to the empty sequence. -/
theorem real_walk_iff_covered_run : ModelSpec.RealWalk := by
  intro n permutation transcript consistent source target
  constructor
  · rintro ⟨path⟩
    exact covers_of_walk permutation transcript consistent path
  · rintro ⟨blocks, covers, rfl⟩
    exact walk_of_covers permutation transcript consistent source blocks covers

private theorem real_edge_of_edge {n : ℕ} {transcript : Transcript n}
    {initials : Finset (State n)} {label : transcript.Label} {source target : Vertex initials}
    (edge : transcript.edge initials label source target) :
    transcript.realEdge label source.state target.state := by
  cases target with
  | inl _ => exact edge
  | inr _ => exact False.elim edge

/-- A walk from a virtual start to a real state corresponds to a nonempty covered block sequence
from the underlying initial state. -/
theorem virtual_walk_iff_nonempty_covered_run : ModelSpec.VirtualWalk := by
  intro n permutation transcript consistent initials initial target
  constructor
  · rintro ⟨path⟩
    cases path with
    | cons label edge rest =>
        rename_i middle
        obtain ⟨block, ⟨input_eq, output_eq⟩, _⟩ :=
          (record_edge_iff_compress permutation (transcript.get label) (consistent label)
            initial.val (Vertex.state (initials := initials) middle)).mp (real_edge_of_edge edge)
        -- Every edge lands at a real vertex. After the first edge the rest is an ordinary state
        -- walk.
        have restReal : Walk transcript.realEdge (Vertex.state (initials := initials) middle)
            target :=
          rest.map Vertex.state (fun {_ _ _} step ↦ real_edge_of_edge step)
        obtain ⟨blocks, covers, run_eq⟩ := covers_of_walk permutation transcript consistent
          restReal
        rw [← output_eq] at covers run_eq
        exact ⟨block :: blocks, List.cons_ne_nil _ _, ⟨⟨label, input_eq.symm⟩, covers⟩, run_eq⟩
  · rintro ⟨blocks, nonemptyBlocks, covers, rfl⟩
    cases blocks with
    | nil => exact (nonemptyBlocks rfl).elim
    | cons block blocks =>
        obtain ⟨⟨label, input_eq⟩, coversRest⟩ := covers
        have capacity_eq : (permInput initial.val block).1 = (transcript.get label).input.1 :=
          congrArg Prod.fst input_eq.symm
        have step : transcript.edge initials label (.inr initial)
            (.inl (compress permutation initial.val block)) :=
          ⟨capacity_eq,
            compress_eq_of_record permutation (transcript.get label) (consistent label)
              input_eq.symm⟩
        obtain ⟨rest⟩ :=
          walk_of_covers permutation transcript consistent (compress permutation initial.val block)
            blocks coversRest
        exact ⟨.cons label step (rest.map Sum.inl (fun {_ _ _} edge ↦ edge))⟩

/-- Successful verification of a padded message reaches the target capacity column from the
virtual start. -/
theorem fixed_target_success_witness : ModelSpec.FixedTargetSuccessWitness := by
  intro α n permutation transcript consistent initial padding message target covers success
  let terminal := run permutation initial (padding.encode message)
  have capacity_eq : terminal.1 = target := success
  refine ⟨terminal.2, ?_⟩
  rw [← capacity_eq]
  exact (virtual_walk_iff_nonempty_covered_run permutation transcript consistent {initial}
    ⟨initial, Finset.mem_singleton_self initial⟩ terminal).mpr
    ⟨padding.encode message, padding.nonempty message, covers, rfl⟩

end JH
