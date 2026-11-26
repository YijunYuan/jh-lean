/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Oracle.Experiment
public import JH.SecondPreimage.TraceSpec

/-!
# First departure and return in a second-preimage trace

With distinct capacities along the original trajectory, a successful distinct candidate must
leave the common prefix by a later record and then reach an original capacity column.
`JH.SecondPreimageTrace.departure_and_return` gives a nonempty walk labeled entirely by later
records, as required in Section 3.2.

The proof uses `Covers` for an arbitrary reply function so the trace argument also applies to
the independent-reply experiment.
-/

@[expose] public section

namespace JH.SecondPreimageTrace

variable {n : ℕ}

@[simp] theorem runWith_cons (reply : State n → State n) (source : State n)
    (block : Word n) (rest : List (Word n)) :
    runWith reply source (block :: rest) =
      runWith reply (compressWith reply source block) rest := rfl

theorem runWith_append (reply : State n → State n) (source : State n) (first rest : List (Word n)) :
    runWith reply source (first ++ rest) = runWith reply (runWith reply source first) rest :=
  List.foldl_append

private theorem sources_append (reply : State n → State n) (source : State n)
    (first rest : List (Word n)) :
    sources reply source (first ++ rest) = sources reply source first ++
      sources reply (runWith reply source first) rest := by
  induction first generalizing source with
  | nil => rfl
  | cons block first ih => simp only [List.cons_append, sources, runWith_cons, ih]

private theorem states_append (reply : State n → State n) (source : State n)
    (first rest : List (Word n)) :
    states reply source (first ++ rest) = sources reply source first ++
      states reply (runWith reply source first) rest := by
  simp only [states, sources_append, runWith_append, List.append_assoc]

private theorem states_cons (reply : State n → State n) (source : State n) (block : Word n)
    (rest : List (Word n)) :
    states reply source (block :: rest) =
      source :: states reply (compressWith reply source block) rest := rfl

private theorem source_mem_states (reply : State n → State n) (source : State n)
    (blocks : List (Word n)) :
    source ∈ states reply source blocks := by
  cases blocks with
  | nil => exact List.mem_singleton_self _
  | cons => exact List.mem_cons_self

private theorem terminal_mem_states (reply : State n → State n) (source : State n)
    (blocks : List (Word n)) : runWith reply source blocks ∈ states reply source blocks :=
  List.mem_append_right _ (List.mem_singleton_self _)

private theorem originalRecords_append (reply : State n → State n) (source : State n)
    (first rest : List (Word n)) :
    originalRecords reply source (first ++ rest) = originalRecords reply source first ++
      originalRecords reply (runWith reply source first) rest := by
  induction first generalizing source with
  | nil => rfl
  | cons block first ih => simp only [List.cons_append, originalRecords, runWith_cons, ih]

private theorem original_input_capacities (reply : State n → State n) (source : State n)
    (blocks : List (Word n)) :
      (originalRecords reply source blocks).map (fun record ↦ record.input.1) =
      (sources reply source blocks).map Prod.fst := by
  induction blocks generalizing source with
  | nil => rfl
  | cons block rest ih => simp only [originalRecords, sources, List.map_cons, permInput, ih]

private theorem original_record_column (reply : State n → State n) (source : State n)
    (blocks : List (Word n)) {record : Record n}
      (member : record ∈ originalRecords reply source blocks) :
    record.input.1 ∈ capacityColumns reply source blocks := by
  change _ ∈ (states reply source blocks).map Prod.fst
  rw [states, List.map_append, ← original_input_capacities]
  exact List.mem_append_left _ (List.mem_map_of_mem member)

private theorem xor_cancel (a b : Word n) : a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem address_injective (source : State n) : Function.Injective (permInput source) := by
  intro first second equal
  have rate : source.2 ^^^ first = source.2 ^^^ second := congrArg Prod.snd equal
  simpa only [xor_cancel] using congrArg (source.2 ^^^ ·) rate

private theorem edge_of_record (reply : State n → State n) (source : State n) (block : Word n)
    (record : Record n) (input : record.input = permInput source block)
    (output : record.output = reply (permInput source block)) :
    record.edge source (compressWith reply source block) := by
  refine ⟨(congrArg Prod.fst input).symm, ?_⟩
  apply Prod.ext
  · simp only [compressWith, feedForward, Record.shift, input, output, permInput]
    rw [← BitVec.xor_assoc, xor_cancel, BitVec.xor_comm]
  · simp only [compressWith, feedForward, output]

/-- Coverage of a block sequence gives coverage of its suffix from the state reached after its
prefix. -/
theorem covers_after_blocks (reply : State n → State n) (records : Transcript n) (source : State n)
    (before rest : List (Word n)) (covered : Covers reply records source (before ++ rest)) :
    Covers reply records (runWith reply source before) rest := by
  induction before generalizing source with
  | nil => exact covered
  | cons block before ih => exact ih (compressWith reply source block) covered.2

private theorem next_later_edge (reply : State n → State n) (old later : Transcript n)
    (source : State n) (block : Word n) (rest : List (Word n))
    (covered : Covers reply (old ++ later) source (block :: rest))
    (fresh : ∀ record ∈ old, record.input ≠ permInput source block) :
    ∃ label : later.Label, later.realEdge label source (compressWith reply source block) := by
  obtain ⟨record, present, input, output⟩ := covered.1
  rcases List.mem_append.mp present with oldRecord | laterRecord
  · exact (fresh record oldRecord input).elim
  · obtain ⟨i, within, get_eq⟩ := List.mem_iff_getElem.mp laterRecord
    refine ⟨⟨i, within⟩, ?_⟩
    change (later[i]'within).edge source (compressWith reply source block)
    rw [get_eq]
    exact edge_of_record reply source block record input output

private theorem split_at_difference {α : Type*} (original candidate : List α)
    (different : original ≠ candidate) :
    ∃ common oldTail newTail : List α, original = common ++ oldTail ∧
      candidate = common ++ newTail ∧ oldTail.head? ≠ newTail.head? := by
  classical
  induction original generalizing candidate with
  | nil =>
    cases candidate with
    | nil => exact (different rfl).elim
    | cons block rest => exact ⟨[], [], block :: rest, rfl, rfl, by simp⟩
  | cons old first ih =>
    cases candidate with
    | nil => exact ⟨[], old :: first, [], rfl, rfl, by simp⟩
    | cons new rest =>
      by_cases same : old = new
      · subst new
        have diff : first ≠ rest := fun equal ↦ different (congrArg (old :: ·) equal)
        obtain ⟨common, oldTail, newTail, origEq, candEq, heads⟩ := ih rest diff
        exact ⟨old :: common, oldTail, newTail, congrArg (old :: ·) origEq,
          congrArg (old :: ·) candEq, heads⟩
      · exact ⟨[], old :: first, new :: rest, rfl, rfl, fun eq ↦ same (Option.some.inj eq)⟩

private theorem first_return (reply : State n → State n) (old later : Transcript n)
    (columns : Set (Word n))
    (oldColumns : ∀ record ∈ old, record.input.1 ∈ columns) (source : State n)
      (blocks : List (Word n))
    (outside : source.1 ∉ columns) (covered : Covers reply (old ++ later) source blocks)
    (returns : (runWith reply source blocks).1 ∈ columns) :
    ∃ used : List (Word n), used <+: blocks ∧
      ∃ path : Walk later.realEdge source (runWith reply source used),
        (runWith reply source used).1 ∈ columns ∧
        (∀ state ∈ sources reply source used, state.1 ∉ columns) ∧
        path.vertices = states reply source used := by
  classical
  induction blocks generalizing source with
  | nil => exact (outside returns).elim
  | cons block rest ih =>
    -- Outside the original capacity columns, the address of a forward compression step misses
    -- every original record.
    have fresh (record : Record n) (present : record ∈ old) :
        record.input ≠ permInput source block := by
      intro equal
      exact outside ((congrArg Prod.fst equal) ▸ oldColumns record present)
    obtain ⟨label, step⟩ := next_later_edge reply old later source block rest covered fresh
    let next := compressWith reply source block
    by_cases arrived : next.1 ∈ columns
    · refine ⟨[block], List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩,
        .cons label step (.nil next), arrived, ?_, rfl⟩
      intro state present
      have same : state = source := List.mem_singleton.mp present
      exact same.symm ▸ outside
    · obtain ⟨used, usedPrefix, path, endCol, beforeCols, vertices⟩ :=
        ih next arrived covered.2 returns
      refine ⟨block :: used, List.cons_prefix_cons.mpr ⟨rfl, usedPrefix⟩,
        .cons label step path, endCol, ?_, ?_⟩
      · intro state present
        rcases List.mem_cons.mp present with rfl | inTail
        · exact outside
        · exact beforeCols state inTail
      · exact congrArg (source :: ·) vertices

private theorem walk_vertices_map {V W L : Type*} {edge : L → V → V → Prop}
    {nextEdge : L → W → W → Prop} (f : V → W)
    (mapEdge : ∀ ⦃label a b⦄, edge label a b → nextEdge label (f a) (f b))
    {a b : V} (path : Walk edge a b) : (path.map f mapEdge).vertices = path.vertices.map f := by
  induction path with
  | nil => rfl
  | cons label step rest ih => simp only [Walk.map, Walk.vertices, List.map_cons, ih]

/-- Under distinct original capacities, extract the walk from the first differing block to the
first return to an original capacity column. Its interior real vertices lie outside those
columns. -/
theorem departure_and_return : SecondPreimageTraceSpec.DepartureAndReturn := by
  classical
  intro n reply initial original candidate later distinct capacities sameDigest covered
  obtain ⟨common, oldTail, newTail, origEq, candEq, different⟩ :=
    split_at_difference original candidate distinct
  let source := runWith reply initial common
  have splitCaps : (((sources reply initial common).map Prod.fst) ++
      ((states reply source oldTail).map Prod.fst)).Nodup := by
    rw [← List.map_append, ← states_append]
    simpa only [DistinctCapacities, origEq] using capacities
  obtain ⟨_, tailNodup, differentCaps⟩ := List.nodup_append.mp splitCaps
  cases newTail with
  | nil =>
    -- If the candidate ends at the common prefix, a matching digest would repeat an original
    -- capacity.
    cases oldTail with
    | nil => exact (different rfl).elim
    | cons block rest =>
      have equal : source.1 = (runWith reply (compressWith reply source block) rest).1 := by
        simpa only [origEq, candEq, List.append_nil, runWith_append, runWith_cons,
          source] using sameDigest
      have without :=
        (List.nodup_cons.mp (by simpa only [states_cons, List.map_cons] using tailNodup)).1
      exact (without (equal.symm ▸ List.mem_map_of_mem (f := Prod.fst)
        (terminal_mem_states reply (compressWith reply source block) rest))).elim
  | cons block rest =>
    let old := originalRecords reply initial original
    have following : Covers reply (old ++ later) source (block :: rest) :=
      covers_after_blocks reply (old ++ later) initial common (block :: rest) (candEq ▸ covered)
    -- The departure column identifies the only possible original record. Address injectivity then
    -- rules out its use with a different block.
    have fresh (record : Record n) (present : record ∈ old) :
        record.input ≠ permInput source block := by
      intro inputEq
      have projected := congrArg (fun state : State n ↦ state.1) inputEq
      have capEq : record.input.1 = source.1 := projected
      have divided : old =
          originalRecords reply initial common ++ originalRecords reply source oldTail := by
        simp only [old, origEq, originalRecords_append, source]
      rw [divided] at present
      rcases List.mem_append.mp present with oldPrefix | oldSuffix
      · have capPresent : record.input.1 ∈ (sources reply initial common).map Prod.fst := by
          rw [← original_input_capacities]
          exact List.mem_map_of_mem oldPrefix
        exact differentCaps _ capPresent _
          (List.mem_map_of_mem (source_mem_states reply source oldTail)) capEq
      · cases oldTail with
        | nil => simp only [originalRecords, List.not_mem_nil] at oldSuffix
        | cons oldBlock oldRest =>
          rcases List.mem_cons.mp oldSuffix with recordEq | older
          · have addresses : permInput source oldBlock = permInput source block := by
              rw [recordEq] at inputEq
              exact inputEq
            exact different (congrArg some (address_injective source addresses))
          · have absent := (List.nodup_cons.mp
              (by simpa only [states_cons, List.map_cons] using tailNodup)).1
            exact absent (capEq ▸ original_record_column reply
              (compressWith reply source oldBlock) oldRest older)
    obtain ⟨label, first⟩ := next_later_edge reply old later source block rest following fresh
    let next := compressWith reply source block
    let columns := capacityColumns reply initial original
    have hit : (runWith reply next rest).1 ∈ columns := by
      have equal : (runWith reply next rest).1 = (runWith reply initial original).1 := by
        simpa only [candEq, runWith_append, runWith_cons, source, next] using sameDigest
      rw [equal]
      exact List.mem_map_of_mem (terminal_mem_states reply initial original)
    have finish : ∃ used : List (Word n), used <+: rest ∧
        ∃ path : Walk later.realEdge next (runWith reply next used),
          (runWith reply next used).1 ∈ columns ∧
          (∀ state ∈ sources reply next used, state.1 ∉ columns) ∧
          path.vertices = states reply next used := by
      -- A return may occur on the departure edge itself. In that case its remaining walk has
      -- length zero.
      by_cases immediate : next.1 ∈ columns
      · exact ⟨[], List.nil_prefix, .nil next, immediate, by simp [sources], rfl⟩
      · exact first_return reply old later columns (fun _ record ↦ original_record_column reply
          initial original record)
          next rest immediate following.2 hit
    obtain ⟨used, returnPrefix, tail, arrived, avoids, trace⟩ := finish
    have startMem : source ∈ states reply initial original := by
      rw [origEq, states_append]
      exact List.mem_append_right _ (source_mem_states reply source oldTail)
    -- Lift the departure to its virtual start and keep the rest of the walk on real states.
    let start : ↥(initialStates reply initial original) := ⟨source, List.mem_toFinset.mpr startMem⟩
    let lifted := Walk.map (edge := later.realEdge) (otherEdge :=
      later.edge (initialStates reply initial original))
      (Sum.inl : State n → Vertex (initialStates reply initial original))
      (fun {_ _ _} edge ↦ edge)
      tail
    have firstVirtual : later.edge (initialStates reply initial original) label (.inr start)
        (.inl next) := first
    refine ⟨⟨common, oldTail, block, rest, used, origEq, candEq, different, returnPrefix,
      start, rfl, .cons label firstVirtual lifted, List.cons_ne_nil _ _, arrived, ?_⟩⟩
    intro vertex present
    change vertex ∈ lifted.vertices.dropLast at present
    have lift_eq : lifted.vertices = tail.vertices.map Sum.inl := walk_vertices_map _ _ tail
    rw [lift_eq, ← List.map_dropLast, trace, states, List.dropLast_concat] at present
    obtain ⟨state, startOfStep, rfl⟩ := List.mem_map.mp present
    exact avoids state startOfStep

private theorem covers_of_consistent {permutation : Permutation n} {records : Transcript n}
    (consistent : records.Consistent permutation) (source : State n) (blocks : List (Word n))
    (covered : records.Covers permutation source blocks) :
      Covers permutation records source blocks := by
  induction blocks generalizing source with
  | nil => trivial
  | cons block rest ih =>
    obtain ⟨⟨label, input⟩, coversRest⟩ := covered
    exact ⟨⟨records.get label, List.getElem_mem label.isLt, input,
      (consistent label).symm.trans (congrArg permutation input)⟩,
      ih (compress permutation source block) coversRest⟩

/-- Actual verification supplies the per-compression input and reply witnesses. -/
theorem verified_coverage : SecondPreimageTraceSpec.VerifiedCoverage := by
  intro n permutation initial blocks old consistent
  obtain ⟨_, _, final, covered⟩ := verify_blocks permutation initial blocks old consistent
  exact covers_of_consistent final initial blocks covered

private theorem verify_original_with_old (permutation : Permutation n) (initial : State n)
    (blocks : List (Word n)) (old : Transcript n)
      (distinct : DistinctCapacities permutation initial blocks)
    (avoids : ∀ record ∈ old, record.input.1 ∉ (sources permutation initial blocks).map Prod.fst) :
    (verifyBlocks permutation initial blocks old).2 =
      old ++ originalRecords permutation initial blocks := by
  induction blocks generalizing initial old with
  | nil => simp only [verifyBlocks, originalRecords, List.append_nil]
  | cons block rest ih =>
    let request : Query n := ⟨.forward, permInput initial block⟩
    let record := request.record permutation
    let next := compressWith permutation initial block
    have miss : old.any request.hasAddress = false := by
      apply List.any_eq_false.mpr
      intro entry present found
      have eq : entry.input = permInput initial block := of_decide_eq_true found
      exact (avoids entry present) ((congrArg Prod.fst eq).symm ▸
        (show initial.1 ∈
          (sources permutation initial (block :: rest)).map Prod.fst from List.mem_cons_self))
    have logs : old.logAccess permutation request = old ++ [record] := by
      simp only [Transcript.logAccess, miss, Bool.false_eq_true, ite_false, record]
    have tailNodup : (initial.1 :: (states permutation next rest).map Prod.fst).Nodup := distinct
    have avoidTail (entry : Record n) (present : entry ∈ old ++ [record]) :
        entry.input.1 ∉ (sources permutation next rest).map Prod.fst := by
      intro input
      rcases List.mem_append.mp present with before | added
      · exact avoids entry before (List.mem_cons_of_mem _ input)
      · have eq := List.mem_singleton.mp added
        subst entry
        have cap : record.input.1 = initial.1 := rfl
        rw [cap] at input
        exact (List.nodup_cons.mp tailNodup).1 (by
          rw [states, List.map_append]
          exact List.mem_append_left _ input)
    change (verifyBlocks permutation next rest (old.logAccess permutation request)).2 = _
    rw [logs, ih next (old ++ [record])
      (List.nodup_cons.mp tailNodup).2 avoidTail, List.append_assoc]
    rfl

/-- With distinct capacities, every block of the original trace contributes its own record to
the verification transcript. -/
theorem verified_original : SecondPreimageTraceSpec.VerifiedOriginal := by
  intro n permutation initial original distinct
  exact verify_original_with_old permutation initial original [] distinct
    (fun record present ↦ (List.not_mem_nil present).elim)

/-- A successful distinct candidate gives a departure-and-return witness using the records
appended after original verification. -/
theorem verified_messages : SecondPreimageTraceSpec.VerifiedMessages := by
  intro α n permutation initial padding original candidate accesses distinct capacities sameDigest
  dsimp only
  intro consistent
  let old := (verifyBlocks permutation initial (padding.encode original) []).2
  let final := (verifyBlocks permutation initial (padding.encode candidate) (old ++ accesses)).2
  have traced := verify_blocks permutation initial (padding.encode candidate)
      (old ++ accesses) consistent
  -- The log grows by appending, so dropping the old prefix keeps labels only for the later
  -- records.
  have before : old <+: final := List.IsPrefix.trans ⟨accesses, rfl⟩ traced.2.1
  have split : old ++ final.drop old.length = final := by
    calc
      _ = final.take old.length ++ final.drop old.length :=
        congrArg (· ++ final.drop old.length) (List.prefix_iff_eq_take.mp before)
      _ = final := List.take_append_drop _ _
  have originalEq : old = originalRecords permutation initial (padding.encode original) :=
    verified_original permutation initial (padding.encode original) capacities
  have covered : Covers permutation
      (originalRecords permutation initial (padding.encode original) ++
      final.drop old.length) initial (padding.encode candidate) := by
    rw [← originalEq, split]
    exact verified_coverage permutation initial (padding.encode candidate)
      (old ++ accesses) consistent
  exact departure_and_return permutation initial (padding.encode original)
    (padding.encode candidate)
    (final.drop old.length) (fun equal ↦
      distinct (padding.injective equal)) capacities sameDigest covered

end JH.SecondPreimageTrace
