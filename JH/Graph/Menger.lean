/-
Copyright (c) 2026 Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Changlun Li, Hongli Li, Yijun Yuan, Fengmei Liu, Shanwen Wang, Honggang Hu
-/
module

public import JH.Graph.MengerSpec
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Prod

/-!
# Finite directed vertex Menger

The alternatives are a packing of `k + 1` vertex-disjoint paths and a separator of size at most
`k`. Endpoints count toward disjointness, and a vertex in both endpoint sets gives a zero-edge
path. The proof inducts on the edge set and matches two families of partial paths across the
old separator and the inserted edge.
-/

@[expose] public section

open List

namespace JH.Graph

variable {V : Type*} {E : V → V → Prop} {A B : Set V}

theorem IsPath.mono {E' : V → V → Prop} {A' B' : Set V} {vertices : List V}
    (hp : IsPath E A B vertices) (hE : ∀ ⦃u v⦄, E u v → E' u v)
    (hA : A ⊆ A') (hB : B ⊆ B') : IsPath E' A' B' vertices := by
  obtain ⟨a, ha, hfirst⟩ := hp.starts
  obtain ⟨b, hb, hlast⟩ := hp.ends
  exact ⟨hp.chain.imp hE, hp.nodup, ⟨a, hA ha, hfirst⟩, ⟨b, hB hb, hlast⟩⟩

theorem IsPath.singleton {v : V} (ha : v ∈ A) (hb : v ∈ B) :
    IsPath E A B [v] :=
  ⟨.singleton v, by simp, ⟨v, ha, rfl⟩, ⟨v, hb, rfl⟩⟩

theorem IsSeparator.mem_of_common_endpoint {S : Finset V} (hS : IsSeparator E A B S)
    {v : V} (ha : v ∈ A) (hb : v ∈ B) : v ∈ S := by
  obtain ⟨w, hw, hwv⟩ := hS [v] (IsPath.singleton ha hb)
  simpa only [List.mem_singleton.mp hwv] using hw

/-- Erase cycles from a vertex walk while preserving both endpoints and keeping
a sublist of its vertices. This also applies to a zero-edge walk. -/
theorem exists_nodup_chain_sublist {vertices : List V} (h : vertices.IsChain E) :
    ∃ path, path <+ vertices ∧ path.IsChain E ∧ path.Nodup ∧
      path.head? = vertices.head? ∧ path.getLast? = vertices.getLast? := by
  classical
  induction vertices with
  | nil => exact ⟨[], .slnil, .nil, .nil, rfl, rfl⟩
  | cons v vertices ih =>
    obtain ⟨path, hsub, hchain, hnodup, hfirst, hlast⟩ := ih h.tail
    by_cases hv : v ∈ path
    · obtain ⟨pre, post, rfl⟩ := List.append_of_mem hv
      have hsuffix := List.suffix_append pre (v :: post)
      refine ⟨v :: post, (hsuffix.sublist.trans hsub).cons v,
        hchain.suffix hsuffix, hnodup.sublist hsuffix.sublist, rfl, ?_⟩
      have hget : (v :: post).getLast? = vertices.getLast? := by
        simpa [List.getLast?_eq_some_getLast (List.cons_ne_nil v post)] using hlast
      calc
        _ = vertices.getLast? := hget
        _ = (v :: vertices).getLast? := by
          simp only [List.getLast?_cons]
          rw [← hget]
          simp [List.getLast?_cons]
    · exact ⟨v :: path, hsub.cons_cons v,
        hchain.cons (by simpa only [hfirst] using h.rel_head?), .cons hv hnodup,
        rfl, by simp only [List.getLast?_cons, hlast]⟩

theorem exists_isPath_sublist_of_isChain {vertices : List V} (h : vertices.IsChain E)
    (hs : ∃ a ∈ A, vertices.head? = some a)
    (ht : ∃ b ∈ B, vertices.getLast? = some b) :
    ∃ path, path <+ vertices ∧ IsPath E A B path := by
  obtain ⟨path, hsub, hchain, hnodup, hfirst, hlast⟩ := exists_nodup_chain_sublist h
  exact ⟨path, hsub, ⟨hchain, hnodup, hfirst ▸ hs, hlast ▸ ht⟩⟩

/-- Choose a meeting vertex for each path. Disjointness makes these choices
an injection from the path indices into any separator. -/
theorem HasDisjointPaths.le_card_separator {n : ℕ} (h : HasDisjointPaths E A B n)
    {S : Finset V} (hS : IsSeparator E A B S) : n ≤ S.card := by
  classical
  obtain ⟨paths, hpaths, hdisjoint⟩ := h
  choose hit hhit hvertex using fun i ↦ hS (paths i) (hpaths i)
  let f : Fin n → S := fun i ↦ ⟨hit i, hhit i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : hit i = hit j := congrArg Subtype.val hij
    exact hdisjoint hne (hit i) (hvertex i) (heq ▸ hvertex j)
  simpa using Fintype.card_le_of_injective f hinj

theorem not_hasDisjointPaths_of_small_separator {S : Finset V} {k : ℕ}
    (hS : IsSeparator E A B S) (hsize : S.card ≤ k) :
    ¬ HasDisjointPaths E A B (k + 1) := by
  intro h
  have hle := h.le_card_separator hS
  omega

/-- Cut a path at any of its vertices to obtain a path to that vertex. -/
theorem IsPath.prefix_of_mem {vertices : List V} (p : IsPath E A B vertices)
    {v : V} (hv : v ∈ vertices) :
    ∃ pre, pre <+: vertices ∧ IsPath E A ({v} : Set V) pre := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hv
  have hprefix : pre ++ [v] <+: pre ++ v :: post :=
    ⟨post, by simp [List.append_assoc]⟩
  exact ⟨pre ++ [v], hprefix,
    ⟨p.chain.prefix hprefix, p.nodup.sublist hprefix.sublist, by simpa using p.starts,
      ⟨v, rfl, by simp⟩⟩⟩

theorem IsPath.reverse {vertices : List V} (p : IsPath E A B vertices) :
    IsPath (fun u v ↦ E v u) B A vertices.reverse :=
  ⟨List.isChain_reverse.mpr p.chain, List.nodup_reverse.mpr p.nodup,
    by simpa using p.ends, by simpa using p.starts⟩

theorem IsSeparator.reverse {S : Finset V} (hS : IsSeparator E A B S) :
    IsSeparator (fun u v ↦ E v u) B A S := by
  intro vertices p
  obtain ⟨v, hv, hmem⟩ := hS vertices.reverse p.reverse
  exact ⟨v, hv, by simpa using hmem⟩

private theorem chain_or_prefix_to {E' : V → V → Prop} {x : V}
    (hstep : ∀ ⦃u v⦄, E' u v → E u v ∨ u = x)
    {vertices : List V} (hchain : vertices.IsChain E') :
    vertices.IsChain E ∨
      ∃ pre, pre <+: vertices ∧ pre.IsChain E ∧ pre.getLast? = some x := by
  induction vertices using List.twoStepInduction with
  | nil => exact Or.inl .nil
  | singleton a => exact Or.inl (.singleton a)
  | cons_cons a b rest _ ih =>
    rcases List.isChain_cons_cons.mp hchain with ⟨hab, htail⟩
    rcases hstep hab with he | ha
    · rcases ih b htail with hc | ⟨p, hp, hc, hlast⟩
      · exact Or.inl (.cons_cons he hc)
      · obtain ⟨suffix, hsuffix⟩ := hp
        cases p with
        | nil => simp at hlast
        | cons v p =>
          have hbv : v = b := by simpa using congrArg List.head? hsuffix
          subst v
          exact Or.inr ⟨a :: b :: p, ⟨suffix, by simpa using congrArg (a :: ·) hsuffix⟩,
            .cons_cons he hc, by simpa using hlast⟩
    · subst a
      exact Or.inr ⟨[x], ⟨b :: rest, rfl⟩, .singleton x, rfl⟩

/-- On adding edges out of `x`, any cut between `A` and `S ∪ {x}` in the
old graph separates `A` from `B` in the augmented graph. -/
private theorem lift_left_separator {E' : V → V → Prop} {x : V} [DecidableEq V]
    (hstep : ∀ ⦃u v⦄, E' u v → E u v ∨ u = x) {S C : Finset V}
    (hS : IsSeparator E A B S)
    (hC : IsSeparator E A (↑(insert x S) : Set V) C) : IsSeparator E' A B C := by
  intro vertices p
  rcases chain_or_prefix_to hstep p.chain with hc | ⟨pre, hpre, hc, hlast⟩
  · have hp : IsPath E A B vertices := ⟨hc, p.nodup, p.starts, p.ends⟩
    obtain ⟨v, hvS, hvl⟩ := hS vertices hp
    obtain ⟨pre, hpre, hp⟩ := hp.prefix_of_mem hvl
    have hsingleton : ({v} : Set V) ⊆ ↑(insert x S) := by
      intro w hw
      have hwv : w = v := hw
      subst w
      exact Finset.mem_insert_of_mem hvS
    obtain ⟨w, hwC, hwp⟩ := hC pre (hp.mono (fun {_ _} h ↦ h) (fun _ h ↦ h) hsingleton)
    exact ⟨w, hwC, hpre.sublist.subset hwp⟩
  · have hs : ∃ a ∈ A, pre.head? = some a := by
      obtain ⟨post, hpost⟩ := hpre
      have hn : pre ≠ [] := by
        rintro rfl
        simp at hlast
      have hstarts := p.starts
      rw [← hpost, List.head?_append_of_ne_nil _ hn] at hstarts
      exact hstarts
    have hp : IsPath E A (↑(insert x S) : Set V) pre :=
      ⟨hc, p.nodup.sublist hpre.sublist, hs, ⟨x, Finset.mem_insert_self x S, hlast⟩⟩
    obtain ⟨v, hvC, hvp⟩ := hC pre hp
    exact ⟨v, hvC, hpre.sublist.subset hvp⟩

private theorem lift_right_separator {E' : V → V → Prop} {y : V} [DecidableEq V]
    (hstep : ∀ ⦃u v⦄, E' u v → E u v ∨ v = y) {S C : Finset V}
    (hS : IsSeparator E A B S)
    (hC : IsSeparator E (↑(insert y S) : Set V) B C) : IsSeparator E' A B C := by
  exact (lift_left_separator (fun {u v} h ↦ hstep (u := v) (v := u) h)
    hS.reverse hC.reverse).reverse

private theorem indexed_by_last {n : ℕ} {S : Finset V}
    (h : HasDisjointPaths E A (↑S : Set V) n) (hcard : S.card = n) :
    ∃ paths : S → List V, (∀ v : S, IsPath E A ({v.val} : Set V) (paths v)) ∧
      Pairwise (fun i j ↦ ∀ v ∈ paths i, v ∉ paths j) := by
  classical
  obtain ⟨paths, hpaths, hdisjoint⟩ := h
  choose last hmem hlast using fun i ↦ (hpaths i).ends
  let f : Fin n → S := fun i ↦ ⟨last i, hmem i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : last i = last j := congrArg Subtype.val hij
    exact hdisjoint hne (last j) (heq ▸ List.mem_of_getLast? (hlast i))
      (List.mem_of_getLast? (hlast j))
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, by simpa using hcard.symm⟩
  let e := Equiv.ofBijective f hbij
  refine ⟨fun v ↦ paths (e.symm v), ?_, ?_⟩
  · intro v
    have p := hpaths (e.symm v)
    have hlast_eq : last (e.symm v) = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    exact ⟨p.chain, p.nodup, p.starts, ⟨v.val, rfl, hlast_eq ▸ hlast (e.symm v)⟩⟩
  · intro i j hne
    exact hdisjoint (fun h' ↦ hne (e.symm.injective h'))

private theorem indexed_by_first {n : ℕ} {S : Finset V}
    (h : HasDisjointPaths E (↑S : Set V) B n) (hcard : S.card = n) :
    ∃ paths : S → List V, (∀ v : S, IsPath E ({v.val} : Set V) B (paths v)) ∧
      Pairwise (fun i j ↦ ∀ v ∈ paths i, v ∉ paths j) := by
  have hrev : HasDisjointPaths (fun u v ↦ E v u) B (↑S : Set V) n := by
    obtain ⟨paths, hp, hd⟩ := h
    refine ⟨fun i ↦ (paths i).reverse, fun i ↦ (hp i).reverse, ?_⟩
    intro i j hne v hv
    simpa using hd hne v (List.mem_reverse.mp hv)
  obtain ⟨paths, hp, hd⟩ := indexed_by_last hrev hcard
  refine ⟨fun i ↦ (paths i).reverse, fun i ↦ (hp i).reverse, ?_⟩
  intro i j hne v hv
  simpa using hd hne v (List.mem_reverse.mp hv)

private theorem terminal_alone {S : Finset V} {paths : S → List V}
    (hd : Pairwise (fun i j ↦ ∀ v ∈ paths i, v ∉ paths j))
    (ht : ∀ i : S, i.val ∈ paths i) (i : S)
    {v : V} (hvp : v ∈ paths i) (hvS : v ∈ S) : v = i.val := by
  by_contra hne
  let j : S := ⟨v, hvS⟩
  exact hd (fun (h : i = j) ↦ hne (congrArg Subtype.val h).symm) v hvp (ht j)

private theorem IsPath.last_eq_of_singleton {vertices : List V} {a : V}
    (p : IsPath E A ({a} : Set V) vertices) : vertices.getLast? = some a := by
  obtain ⟨b, hb, hlast⟩ := p.ends
  exact (Set.mem_singleton_iff.mp hb) ▸ hlast

private theorem IsPath.first_eq_of_singleton {vertices : List V} {a : V}
    (p : IsPath E ({a} : Set V) B vertices) : vertices.head? = some a := by
  obtain ⟨b, hb, hfirst⟩ := p.starts
  exact (Set.mem_singleton_iff.mp hb) ▸ hfirst

/-- Reflexive transitive reachability is equivalent to the existence of a simple
path with the same endpoints. The forward implication erases cycles. -/
theorem reaches_iff_exists_isPath {a b : V} :
    Relation.ReflTransGen E a b ↔
      ∃ path, IsPath E ({a} : Set V) ({b} : Set V) path := by
  constructor
  · intro h
    obtain ⟨tail, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    have hlast' : (a :: tail).getLast? = some b :=
      (List.getLast?_eq_some_getLast (List.cons_ne_nil a tail)).trans (congrArg some hlast)
    obtain ⟨path, _, hp⟩ := exists_isPath_sublist_of_isChain (A := {a}) (B := {b}) hchain
      ⟨a, rfl, rfl⟩ ⟨b, rfl, hlast'⟩
    exact ⟨path, hp⟩
  · rintro ⟨path, hp⟩
    have hn : path ≠ [] := by
      intro he
      have hfirst := hp.first_eq_of_singleton
      simp [he] at hfirst
    have hfirst : path.head hn = a :=
      Option.some.inj ((List.head?_eq_some_head hn).symm.trans hp.first_eq_of_singleton)
    have hlast : path.getLast hn = b :=
      Option.some.inj ((List.getLast?_eq_some_getLast hn).symm.trans hp.last_eq_of_singleton)
    simpa only [hfirst, hlast] using List.relationReflTransGen_of_exists_isChain path hp.chain hn

/-- A common vertex outside the cut would splice a path through the deleted
graph that avoids the cut. Loop erasure makes the splice simple. -/
private theorem shared_vertex_mem_separator {S : Finset V} (hS : IsSeparator E A B S)
    {left right : List V} {a b : V}
    (hl : IsPath E A ({a} : Set V) left) (hr : IsPath E ({b} : Set V) B right)
    (hlS : ∀ v ∈ left, v ∈ S → v = a) (hrS : ∀ v ∈ right, v ∈ S → v = b)
    {v : V} (hvl : v ∈ left) (hvr : v ∈ right) : v ∈ S := by
  by_contra hvS
  obtain ⟨lp, ls, rfl⟩ := List.append_of_mem hvl
  obtain ⟨rp, rs, rfl⟩ := List.append_of_mem hvr
  have hlprefix : (lp ++ [v]).IsChain E :=
    hl.chain.prefix ⟨ls, by simp [List.append_assoc]⟩
  have hchain : (lp ++ v :: rs).IsChain E := by
    simpa [List.append_assoc] using
      hlprefix.append_overlap hr.chain.right_of_append (by simp : [v] ≠ [])
  obtain ⟨p, hsub, hp⟩ := exists_isPath_sublist_of_isChain (A := A) (B := B) hchain
    (by simpa using hl.starts) (by simpa using hr.ends)
  obtain ⟨w, hwS, hwp⟩ := hS p hp
  rcases List.mem_append.mp (hsub.subset hwp) with hwl | hwr
  · have hwa := hlS w (List.mem_append_left _ hwl) hwS
    have hwlast : (v :: ls).getLast? = some w := by
      simpa [hwa] using hl.last_eq_of_singleton
    exact (List.nodup_append.mp hl.nodup).2.2 w hwl w (List.mem_of_getLast? hwlast) rfl
  · rcases List.mem_cons.mp hwr with rfl | hws
    · exact hvS hwS
    · have hwb := hrS w (List.mem_append_right _ (List.mem_cons_of_mem _ hws)) hwS
      have hwfirst : (rp ++ [v]).head? = some w := by
        simpa [hwb] using hr.first_eq_of_singleton
      have hnodup : ((rp ++ [v]) ++ rs).Nodup := by
        simpa [List.append_assoc] using hr.nodup
      exact (List.nodup_append.mp hnodup).2.2 w (List.mem_of_head? hwfirst) w hws rfl

private theorem glue_at_vertex {left right : List V} {a : V}
    (hl : IsPath E A ({a} : Set V) left) (hr : IsPath E ({a} : Set V) B right)
    (hshared : ∀ v ∈ left, v ∈ right → v = a) :
    IsPath E A B (left ++ right.tail) := by
  have hfirst := hr.first_eq_of_singleton
  cases right with
  | nil => simp at hfirst
  | cons b rest =>
    have hba : b = a := by simpa using hfirst
    subst b
    have hn := List.nodup_cons.mp hr.nodup
    refine ⟨hl.chain.append hr.chain.tail ?_, List.nodup_append.mpr ⟨hl.nodup, hn.2, ?_⟩,
      ?_, ?_⟩
    · intro v hv w hw
      have hva : a = v := by simpa [hl.last_eq_of_singleton] using hv
      subst v
      exact hr.chain.rel_head? hw
    · intro v hv w hw hvw
      subst w
      have hva := hshared v hv (List.mem_cons_of_mem _ hw)
      exact hn.1 (hva ▸ hw)
    · obtain ⟨u, hu, hfirst⟩ := hl.starts
      exact ⟨u, hu, by simp [hfirst]⟩
    · have hlast : (left ++ rest).getLast? = (a :: rest).getLast? := by
        simp only [List.getLast?_append, hl.last_eq_of_singleton, List.getLast?_cons]
        cases rest.getLast? <;> rfl
      obtain ⟨u, hu, hlast_right⟩ := hr.ends
      exact ⟨u, hu, hlast.trans hlast_right⟩

private theorem glue_across_edge {left right : List V} {a b : V}
    (hl : IsPath E A ({a} : Set V) left) (hr : IsPath E ({b} : Set V) B right)
    (hab : E a b) (hdisjoint : ∀ v ∈ left, v ∉ right) :
    IsPath E A B (left ++ right) := by
  refine ⟨hl.chain.append hr.chain ?_, List.nodup_append.mpr ⟨hl.nodup, hr.nodup, ?_⟩, ?_, ?_⟩
  · intro v hv w hw
    have hva : a = v := by simpa [hl.last_eq_of_singleton] using hv
    have hwb : b = w := by simpa [hr.first_eq_of_singleton] using hw
    exact hva ▸ hwb ▸ hab
  · intro v hv w hw hvw
    exact hdisjoint v hv (hvw.symm ▸ hw)
  · obtain ⟨u, hu, hfirst⟩ := hl.starts
    exact ⟨u, hu, by simp [hfirst]⟩
  · obtain ⟨u, hu, hlast⟩ := hr.ends
    exact ⟨u, hu, by simp [hlast]⟩

/-- The left and right path families use every vertex of their respective cuts
as an endpoint. Match the paths at vertices of `S`, and match the two remaining
paths by the new edge `x → y`. -/
private theorem augment_families [DecidableEq V] {E' : V → V → Prop} {x y : V}
    (hE : ∀ ⦃u v⦄, E u v → E' u v) (hxy : E' x y) {S : Finset V} {n : ℕ}
    (hS : IsSeparator E A B S) (hxS : x ∉ S) (hyS : y ∉ S)
    (hleft : HasDisjointPaths E A (↑(insert x S) : Set V) n)
    (hright : HasDisjointPaths E (↑(insert y S) : Set V) B n)
    (hcard_left : (insert x S).card = n) (hcard_right : (insert y S).card = n) :
    HasDisjointPaths E' A B n := by
  classical
  obtain ⟨left, hl, hdl⟩ := indexed_by_last hleft hcard_left
  obtain ⟨right, hr, hdr⟩ := indexed_by_first hright hcard_right
  let leftCut : Finset V := insert x S
  let rightCut : Finset V := insert y S
  let partner (i : leftCut) : rightCut :=
    if hi : i.val ∈ S then ⟨i.val, Finset.mem_insert_of_mem hi⟩ else ⟨y, Finset.mem_insert_self y S⟩
  have hpartner : Function.Injective partner := by
    intro i j hij
    have hval : (partner i).val = (partner j).val := congrArg Subtype.val hij
    apply Subtype.ext
    by_cases hi : i.val ∈ S <;> by_cases hj : j.val ∈ S
    · simpa [partner, hi, hj] using hval
    · have heq : i.val = y := by simpa [partner, hi, hj] using hval
      exact (hyS (heq ▸ hi)).elim
    · have heq : j.val = y := by simpa [partner, hi, hj, eq_comm] using hval
      exact (hyS (heq ▸ hj)).elim
    · exact ((Finset.mem_insert.mp i.property).resolve_right hi).trans
        ((Finset.mem_insert.mp j.property).resolve_right hj).symm
  -- Every cut vertex is the endpoint of its own path. Disjointness then rules out
  -- any other occurrence of that cut vertex within the same family.
  have hleft_only (i : leftCut) (v : V) (hv : v ∈ left i) (hvS : v ∈ leftCut) :
      v = i.val :=
    terminal_alone hdl (fun j ↦ List.mem_of_getLast? (hl j).last_eq_of_singleton) i hv hvS
  have hright_only (j : rightCut) (v : V) (hv : v ∈ right j) (hvS : v ∈ rightCut) :
      v = j.val :=
    terminal_alone hdr (fun i ↦ List.mem_of_head? (hr i).first_eq_of_singleton) j hv hvS
  -- The old separator forces any cross-family intersection to lie on the cut.
  -- The terminal-vertex property then makes it an intersection of matched paths.
  have hshared (i : leftCut) (j : rightCut) (v : V)
      (hvl : v ∈ left i) (hvr : v ∈ right j) : v ∈ S :=
    shared_vertex_mem_separator hS (hl i) (hr j)
      (fun w hw hws ↦ hleft_only i w hw (Finset.mem_insert_of_mem hws))
      (fun w hw hws ↦ hright_only j w hw (Finset.mem_insert_of_mem hws)) hvl hvr
  have hmatch (i j : leftCut) (v : V) (hvl : v ∈ left i) (hvr : v ∈ right (partner j)) :
      i = j := by
    have hvS := hshared i (partner j) v hvl hvr
    have hvi := hleft_only i v hvl (Finset.mem_insert_of_mem hvS)
    have hvj := hright_only (partner j) v hvr (Finset.mem_insert_of_mem hvS)
    apply Subtype.ext
    by_cases hj : j.val ∈ S
    · exact hvi.symm.trans (by simpa [partner, hj] using hvj)
    · have hvy : v = y := by simpa [partner, hj] using hvj
      exact (hyS (hvy ▸ hvS)).elim
  have hglue (i : leftCut) :
      ∃ p, IsPath E' A B p ∧ ∀ v ∈ p, v ∈ left i ∨ v ∈ right (partner i) := by
    by_cases hi : i.val ∈ S
    · have hpartner_eq : (partner i).val = i.val := by simp [partner, hi]
      have hr' : IsPath E ({i.val} : Set V) B (right (partner i)) := by
        simpa only [hpartner_eq] using hr (partner i)
      have hp := glue_at_vertex (hl i) hr' fun v hvl hvr ↦
        hleft_only i v hvl (Finset.mem_insert_of_mem (hshared i (partner i) v hvl hvr))
      refine ⟨left i ++ (right (partner i)).tail, hp.mono hE (fun _ h ↦ h) (fun _ h ↦ h), ?_⟩
      intro v hv
      exact (List.mem_append.mp hv).imp id List.mem_of_mem_tail
    · have hix := (Finset.mem_insert.mp i.property).resolve_right hi
      have hjy : (partner i).val = y := by simp [partner, hi]
      have hd (v : V) (hvl : v ∈ left i) (hvr : v ∈ right (partner i)) : False := by
        have hvS := hshared i (partner i) v hvl hvr
        have hvi := hleft_only i v hvl (Finset.mem_insert_of_mem hvS)
        exact hxS ((hvi.trans hix) ▸ hvS)
      refine ⟨left i ++ right (partner i), ?_, fun _ h ↦ List.mem_append.mp h⟩
      exact glue_across_edge ((hl i).mono hE (fun _ h ↦ h) (fun _ h ↦ h))
        ((hr (partner i)).mono hE (fun _ h ↦ h) (fun _ h ↦ h))
        (hix.symm ▸ hjy.symm ▸ hxy) hd
  choose paths hpaths hsubset using hglue
  let index := (Finset.equivFinOfCardEq hcard_left).symm
  refine ⟨fun i ↦ paths (index i), fun i ↦ hpaths (index i), ?_⟩
  intro i j hij v hvi hvj
  have hne : index i ≠ index j := fun h ↦ hij (index.injective h)
  rcases hsubset (index i) v hvi with hvl | hvr <;>
    rcases hsubset (index j) v hvj with hwl | hwr
  · exact hdl hne v hvl hwl
  · exact hne (hmatch _ _ v hvl hwr)
  · exact hne ((hmatch _ _ v hwl hvr).symm)
  · exact hdr (fun h ↦ hne (hpartner h)) v hvr hwr

/-- The adjacency relation represented by a finite set of directed edges. -/
private def edgeRel (edges : Finset (V × V)) (u v : V) : Prop :=
  (u, v) ∈ edges

private theorem packing_or_separator_empty [Finite V] (A B : Set V) (k : ℕ) :
    HasDisjointPaths (edgeRel ∅) A B (k + 1) ∨
      ∃ S : Finset V, IsSeparator (edgeRel ∅) A B S ∧ S.card ≤ k := by
  classical
  let := Fintype.ofFinite V
  -- With no edges, the only paths are singleton vertices in the common endpoint set.
  let S : Finset V := Finset.univ.filter fun v ↦ v ∈ A ∧ v ∈ B
  by_cases hcard : k + 1 ≤ S.card
  · let vertex (i : Fin (k + 1)) : S :=
      S.equivFin.symm ⟨i.val, i.isLt.trans_le hcard⟩
    have hmem (i : Fin (k + 1)) : (vertex i).val ∈ A ∧ (vertex i).val ∈ B :=
      (Finset.mem_filter.mp (vertex i).property).2
    refine Or.inl ⟨fun i ↦ [(vertex i).val],
      fun i ↦ IsPath.singleton (hmem i).1 (hmem i).2, ?_⟩
    intro i j hij v hvi hvj
    have heq := (List.mem_singleton.mp hvi).symm.trans (List.mem_singleton.mp hvj)
    have hindex := S.equivFin.symm.injective (Subtype.ext heq : vertex i = vertex j)
    exact hij (Fin.ext (congrArg (fun f : Fin S.card ↦ f.val) hindex))
  · refine Or.inr ⟨S, ?_, by omega⟩
    intro vertices hp
    cases vertices with
    | nil =>
      have hs := hp.starts
      simp at hs
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : a ∈ A := by simpa using hp.starts
        have hb : a ∈ B := by simpa using hp.ends
        exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha, hb⟩, by simp⟩
      | cons b rest =>
        have hab := (List.isChain_cons_cons.mp hp.chain).1
        simp [edgeRel] at hab

private theorem packing_or_separator_edges [Finite V]
    (edges : Finset (V × V)) (A B : Set V) (k : ℕ) :
    HasDisjointPaths (edgeRel edges) A B (k + 1) ∨
      ∃ S : Finset V, IsSeparator (edgeRel edges) A B S ∧ S.card ≤ k := by
  classical
  induction edges using Finset.induction_on generalizing A B with
  | empty => exact packing_or_separator_empty A B k
  | @insert edge edges _ ih =>
    obtain ⟨x, y⟩ := edge
    let E := edgeRel edges
    let E' := edgeRel (insert (x, y) edges)
    have hE : ∀ ⦃u v⦄, E u v → E' u v :=
      fun {_ _} he ↦ Finset.mem_insert_of_mem he
    have hadded ⦃u v⦄ (he : E' u v) : E u v ∨ u = x ∧ v = y := by
      rcases Finset.mem_insert.mp he with hxy | he
      · exact Or.inr ⟨congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
      · exact Or.inl he
    have hstep_left ⦃u v⦄ (he : E' u v) : E u v ∨ u = x := (hadded he).imp id And.left
    have hstep_right ⦃u v⦄ (he : E' u v) : E u v ∨ v = y := (hadded he).imp id And.right
    by_cases hsmall : ∃ S : Finset V, IsSeparator E' A B S ∧ S.card ≤ k
    · exact Or.inr hsmall
    left
    rcases ih A B with ⟨paths, hp, hd⟩ | ⟨S, hS, hsize⟩
    · exact ⟨paths, fun i ↦ (hp i).mono hE (fun _ h ↦ h) (fun _ h ↦ h), hd⟩
    -- Enlarge the old separator on each side by the appropriate endpoint of the new edge.
    -- A small cut for either modified problem would lift to a small cut in the new graph.
    have hleft : HasDisjointPaths E A (↑(insert x S) : Set V) (k + 1) := by
      rcases ih A (↑(insert x S) : Set V) with hp | ⟨C, hC, hcard⟩
      · exact hp
      · exact (hsmall ⟨C, lift_left_separator hstep_left hS hC, hcard⟩).elim
    have hright : HasDisjointPaths E (↑(insert y S) : Set V) B (k + 1) := by
      rcases ih (↑(insert y S) : Set V) B with hp | ⟨C, hC, hcard⟩
      · exact hp
      · exact (hsmall ⟨C, lift_right_separator hstep_right hS hC, hcard⟩).elim
    -- The cut bounds force both enlarged cuts to have exactly one vertex per path.
    have hleft_min : k + 1 ≤ (insert x S).card := hleft.le_card_separator fun _ p ↦ by
      obtain ⟨v, hv, hlast⟩ := p.ends
      exact ⟨v, hv, List.mem_of_getLast? hlast⟩
    have hright_min : k + 1 ≤ (insert y S).card := hright.le_card_separator fun _ p ↦ by
      obtain ⟨v, hv, hfirst⟩ := p.starts
      exact ⟨v, hv, List.mem_of_head? hfirst⟩
    have hxS : x ∉ S := by
      intro hx
      rw [Finset.insert_eq_of_mem hx] at hleft_min
      omega
    have hyS : y ∉ S := by
      intro hy
      rw [Finset.insert_eq_of_mem hy] at hright_min
      omega
    have hleft_card : (insert x S).card = k + 1 := by
      have hle := Finset.card_insert_le x S
      omega
    have hright_card : (insert y S).card = k + 1 := by
      have hle := Finset.card_insert_le y S
      omega
    exact augment_families hE (Finset.mem_insert_self (x, y) edges) hS hxS hyS hleft hright
      hleft_card hright_card

/-- Finite directed vertex Menger, by induction on the edge set. -/
theorem directed_vertex_menger (V : Type*) [Finite V] : DirectedVertexMenger V := by
  classical
  let := Fintype.ofFinite V
  intro E A B k
  refine ⟨?_, ?_⟩
  · intro hno
    let edges : Finset (V × V) := Finset.univ.filter fun p ↦ E p.1 p.2
    have hE : edgeRel edges = E := by
      funext u v
      simp [edgeRel, edges]
    rcases hE ▸ packing_or_separator_edges edges A B k with hp | hs
    · exact (hno hp).elim
    · exact hs
  · rintro ⟨S, hS, hcard⟩
    exact not_hasDisjointPaths_of_small_separator hS hcard

@[deprecated (since := "2026-11-25")] alias directedVertexMenger := directed_vertex_menger

end JH.Graph
