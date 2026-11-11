/-
Private formal disproof of Erdős problem 566.

Main unconditional theorem
  Erdos566.original_statement_false : ¬Erdos566.OriginalStatement

The theorem PrizeStatement.original_problem_false at the end transfers the
result to the literal ordinary-Ramsey formulation used in the problem source.
The fixed forbidden graph satisfies every required induced-edge inequality.
The proof uses Bernoulli samples of Hamming cubes, retuned entropy bounds,
Krawtchouk/Walsh estimates, and deterministic independent-set containers.

The graph, finite-profile enumeration, elementary entropy infrastructure and
parts of the Bernoulli calculation are adapted from OpenAI et al., Chapter 10
of Ten Advances in Mathematics and Theoretical Computer Science, with the
source blob and license identified below. The one-cube Ramsey construction
and parameter choices follow the private Erdős 566 proposal of 2026-11-11.
The container argument is the maximum-degree encoding method of
Kleitman and Winston. Attribution is retained throughout the file.

This source has been prepared locally for private review. Verification
records identify the exact source hash, toolchain and dependency revisions.
-/
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Ring
import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Bounds

/-
The layered graph construction is adapted from OpenAI et al.,
CompactnessAndDegeneracy.lean, git blob
0e973d50014e8c800af597ef699ef29b81e42fc6, namespace TwoDegenerateGraphs.
The source accompanies Chapter 10 of Ten Advances in Mathematics and
Theoretical Computer Science. The local-sparsity proof is added separately.
-/

open Finset SimpleGraph

namespace Erdos566

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

abbrev IsTwoDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 2 G

theorem isTwoDegenerate_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsTwoDegenerate G) :
    IsTwoDegenerate H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    refine ⟨e.symm w, ?_⟩
    exact Finset.mem_map.mpr ⟨w, hw, rfl⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · change v ∈ s.map e.symm.toEquiv.toEmbedding at hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by
      apply e.symm.toEquiv.injective
      simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        change e.symm w ∈ s.map e.symm.toEquiv.toEmbedding ↔ w ∈ s
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember
          exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency :
          G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard

theorem isBipartite_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : G.IsBipartite) : H.IsBipartite := by
  obtain ⟨coloring⟩ := hG
  exact ⟨coloring.comp e.symm.toHom⟩

structure ParentSystem (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 2

namespace ParentSystem

def graph {V : Type*} (P : ParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

theorem graph_adj_iff {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by
  rfl

theorem graph_isBipartite {V : Type*} (P : ParentSystem V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega

theorem graph_isTwoDegenerate {V : Type*} (P : ParentSystem V) :
    IsTwoDegenerate P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)

end ParentSystem

def PairLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (PairLayer baseSize i) // parents.card = 2}

noncomputable instance pairLayerFintype (baseSize i : ℕ) :
    Fintype (PairLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (PairLayer baseSize i) // parents.card = 2}
      infer_instance

theorem pairLayer_card_zero (baseSize : ℕ) :
    Fintype.card (PairLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem pairLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (PairLayer baseSize (i + 1)) =
      (Fintype.card (PairLayer baseSize i)).choose 2 := by
  classical
  let layerPairs : Finset (Finset (PairLayer baseSize i)) :=
    (Finset.univ : Finset (PairLayer baseSize i)).powersetCard 2
  let equivalence : PairLayer baseSize (i + 1) ≃ layerPairs :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (PairLayer baseSize (i + 1)) = Fintype.card layerPairs :=
      Fintype.card_congr equivalence
    _ = layerPairs.card := Fintype.card_coe layerPairs
    _ = (Fintype.card (PairLayer baseSize i)).choose 2 := by
      simp [layerPairs]

theorem le_choose_two_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 2 := by
  have hreal : (4 : ℝ) ≤ (size : ℝ) := by
    exact_mod_cast hsize
  have hchoose :
      (size.choose 2 : ℝ) =
        (size : ℝ) * ((size : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ size
  have hbound : (size : ℝ) ≤ (size.choose 2 : ℝ) := by
    rw [hchoose]
    nlinarith [sq_nonneg ((size : ℝ) - 2)]
  exact_mod_cast hbound

theorem pairLayer_card_ge_base
    (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (PairLayer baseSize i) := by
  induction i with
  | zero =>
      rw [pairLayer_card_zero]
  | succ i ih =>
      rw [pairLayer_card_succ]
      exact ih.trans
        (le_choose_two_of_four (hbase.trans ih))

noncomputable def pairLayerFinEquiv (baseSize layer : ℕ) :
    PairLayer baseSize layer ≃
      Fin (Fintype.card (PairLayer baseSize layer)) :=
  Fintype.equivFin (PairLayer baseSize layer)

noncomputable def pairLayerPairEquiv (baseSize layer : ℕ) :
    PairLayer (Fintype.card (PairLayer baseSize layer)) 1 ≃
      PairLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset
      (Fin (Fintype.card (PairLayer baseSize layer))) //
        parents.card = 2} ≃
      {parents : Finset (PairLayer baseSize layer) //
        parents.card = 2}
  exact
    (pairLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by
        simp [Equiv.finsetCongr_apply])

theorem pairLayerPair_nonempty
    {parentCount : ℕ}
    (hparents : 2 ≤ parentCount) :
    Nonempty (PairLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [pairLayer_card_succ parentCount 0,
    pairLayer_card_zero]
  exact Nat.choose_pos hparents

abbrev PairVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), PairLayer baseSize i.val

def pairLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    PairLayer baseSize i ↪ PairVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by
    intro v w heq
    cases heq
    rfl

noncomputable def pairParents (baseSize depth : ℕ) :
    PairVertex baseSize depth → Finset (PairVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (pairLayerEmbedding baseSize depth i (by omega))

noncomputable def pairParentSystem (baseSize depth : ℕ) :
    ParentSystem (PairVertex baseSize depth) where
  level v := v.1.val
  parents := pairParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero =>
        simp [pairParents] at hparent
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp only [pairParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero =>
        simp [pairParents]
    | succ i =>
        change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
        simp [pairParents, v.property]

theorem pairGraph_parent_child_adj
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (ParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val)
      hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        pairParents baseSize depth
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer child)
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        child.val.map
          (pairLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩

theorem pairGraph_isBipartite (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph.IsBipartite :=
  ParentSystem.graph_isBipartite (pairParentSystem baseSize depth)

theorem pairGraph_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairParentSystem baseSize depth).graph :=
  ParentSystem.graph_isTwoDegenerate (pairParentSystem baseSize depth)

def pairBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    PairVertex baseSize depth :=
  pairLayerEmbedding baseSize depth 0 (by omega) a

theorem pairLayer_reaches_base (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : PairLayer baseSize i),
      ∃ a : Fin baseSize,
        (pairParentSystem baseSize depth).graph.Reachable
          (pairLayerEmbedding baseSize depth i hi v)
          (pairBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero =>
      intro hi v
      exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (PairLayer baseSize i) // parents.card = 2} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp
        omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := pairLayerEmbedding baseSize depth i (by omega) parent
      let upper := pairLayerEmbedding baseSize depth (i + 1) hi v
      have hedge :
          (pairParentSystem baseSize depth).graph.Adj upper lower := by
        apply (ParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : PairVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ pairParents baseSize depth upper
          change lower ∈
            v.val.map (pairLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      refine ⟨a, hedge.reachable.trans ?_⟩
      exact ha

theorem pairBaseVertices_reachable (baseSize depth : ℕ)
    (hdepth : 0 < depth) (a b : Fin baseSize) :
    (pairParentSystem baseSize depth).graph.Reachable
      (pairBaseVertex baseSize depth a)
      (pairBaseVertex baseSize depth b) := by
  classical
  letI pairDecidableEq : DecidableEq (PairLayer baseSize 0) := Classical.decEq _
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.rfl
  · let pair : PairLayer baseSize 1 :=
      ⟨{a, b}, Finset.card_pair hab⟩
    let bridge := pairLayerEmbedding baseSize depth 1 (by omega) pair
    have hadj (x : Fin baseSize) (hx : x = a ∨ x = b) :
        (pairParentSystem baseSize depth).graph.Adj
          bridge (pairBaseVertex baseSize depth x) := by
      apply (ParentSystem.graph_adj_iff _ bridge _).mpr
      constructor
      · intro heq
        have hlevels := congrArg
          (fun z : PairVertex baseSize depth => z.1.val) heq
        change 1 = 0 at hlevels
        omega
      · left
        change pairBaseVertex baseSize depth x ∈
          pairParents baseSize depth bridge
        have hxmem : x ∈ ({a, b} : Finset (PairLayer baseSize 0)) := by
          rcases hx with hxa | hxb
          · rw [hxa]
            exact @Finset.mem_insert_self (PairLayer baseSize 0)
              pairDecidableEq a ({b} : Finset (PairLayer baseSize 0))
          · rw [hxb]
            exact @Finset.mem_insert_of_mem (PairLayer baseSize 0)
              pairDecidableEq ({b} : Finset (PairLayer baseSize 0)) b a
              (Finset.mem_singleton_self b)
        change
          pairLayerEmbedding baseSize depth 0 (by omega) x ∈
            ({a, b} : Finset (PairLayer baseSize 0)).map
              (pairLayerEmbedding baseSize depth 0 (by omega))
        exact Finset.mem_map.mpr ⟨x, hxmem, rfl⟩
    exact (hadj a (Or.inl rfl)).symm.reachable.trans
      (hadj b (Or.inr rfl)).reachable

theorem pairGraph_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairParentSystem baseSize depth).graph.Connected := by
  let root : Fin baseSize := ⟨0, hbase⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨pairBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := pairLayer_reaches_base baseSize depth i hi v
  exact (pairBaseVertices_reachable baseSize depth hdepth root a).trans ha.symm

noncomputable def pairGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (PairVertex baseSize depth))) :=
  (pairParentSystem baseSize depth).graph.overFin rfl

noncomputable def pairGraphOverFinIso (baseSize depth : ℕ) :
    (pairParentSystem baseSize depth).graph ≃g
      pairGraphOverFin baseSize depth :=
  (pairParentSystem baseSize depth).graph.overFinIso rfl

theorem pairGraphOverFin_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected :=
  (pairGraphOverFinIso baseSize depth).connected_iff.mp
    (pairGraph_connected baseSize depth hbase hdepth)

theorem pairGraphOverFin_isBipartite (baseSize depth : ℕ) :
    (pairGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isBipartite baseSize depth)

theorem pairGraphOverFin_isTwoDegenerate (baseSize depth : ℕ) :
    IsTwoDegenerate (pairGraphOverFin baseSize depth) :=
  isTwoDegenerate_of_iso (pairGraphOverFinIso baseSize depth)
    (pairGraph_isTwoDegenerate baseSize depth)


end Erdos566

open Finset SimpleGraph

namespace Erdos566

noncomputable def edgesOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => e.toFinset ⊆ S)

theorem card_edgesOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :
    (edgesOn G S).card = (G.induce (S : Set V)).edgeSet.ncard := by
  classical
  rw [edgesOn, G.card_filter_edgeFinset_toFinset_subset]
  exact SimpleGraph.edgeFinset_card.trans (Set.fintypeCard_eq_ncard _)

open Classical in
theorem edgesOn_insert {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (v : V) :
    edgesOn G (insert v S) = edgesOn G S ∪
      (neighborsWithin G S v).image (fun w => s(v, w)) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [edgesOn, mem_filter, SimpleGraph.mem_edgeFinset,
        Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff, mem_insert, mem_union,
        mem_image, neighborsWithin, mem_filter, Sym2.eq_iff]
      constructor
      · rintro ⟨hxy, (hx | hx), (hy | hy)⟩
        · subst x
          subst y
          exact (G.irrefl hxy).elim
        · subst x
          exact Or.inr ⟨y, ⟨hy, hxy⟩, Or.inl ⟨rfl, rfl⟩⟩
        · subst y
          exact Or.inr ⟨x, ⟨hx, hxy.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
        · exact Or.inl ⟨hxy, hx, hy⟩
      · rintro (⟨hxy, hx, hy⟩ | ⟨w, ⟨hw, hvw⟩, heq⟩)
        · exact ⟨hxy, Or.inr hx, Or.inr hy⟩
        · rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hvw, Or.inl rfl, Or.inr hw⟩
          · exact ⟨hvw.symm, Or.inr hw, Or.inl rfl⟩

open Classical in
theorem card_edgesOn_insert {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) (v : V) (hv : v ∉ S) :
    (edgesOn G (insert v S)).card =
      (edgesOn G S).card + (neighborsWithin G S v).card := by
  classical
  rw [edgesOn_insert, card_union_of_disjoint]
  · congr 1
    apply card_image_of_injective
    intro x y hxy
    rcases Sym2.eq_iff.mp hxy with h | h
    · exact h.2
    · exact h.2.trans h.1
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hf
    have hs := (mem_filter.mp he).2
    exact hv (hs (by simp))

theorem edgesOn_empty {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgesOn G ∅ = ∅ := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [edgesOn]

theorem edgesOn_singleton {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : edgesOn G {v} = ∅ := by
  classical
  rw [← insert_empty_eq, edgesOn_insert, edgesOn_empty]
  simp [neighborsWithin]

/-- Every finite 2-degenerate graph satisfies the exact local edge bound. -/
theorem local_sparsity_of_two_degenerate {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG : IsTwoDegenerate G) :
    ∀ S : Finset V, 2 ≤ S.card →
      (G.induce (S : Set V)).edgeSet.ncard ≤ 2 * S.card - 3 := by
  classical
  suffices hs : ∀ S : Finset V, (edgesOn G S).card ≤ 2 * S.card - 3 by
    intro S hS
    rw [← card_edgesOn]
    exact hs S
  intro S
  induction S using Finset.strongInductionOn
  rename_i S ih
  ·
      by_cases hsmall : S.card ≤ 1
      · have hc : S.card = 0 ∨ S.card = 1 := by omega
        rcases hc with hc | hc
        · have heq := card_eq_zero.mp hc
          simp [heq, edgesOn_empty]
        · obtain ⟨v, rfl⟩ := card_eq_one.mp hc
          simp [edgesOn_singleton]
      · have hS : S.Nonempty := card_pos.mp (by omega)
        obtain ⟨v, hv, hdegree⟩ := hG S hS
        have hsub : S.erase v ⊂ S := erase_ssubset hv
        have hrec := ih (S.erase v) hsub
        have hne : v ∉ S.erase v := notMem_erase v S
        have heq := card_edgesOn_insert G (S.erase v) v hne
        rw [insert_erase hv] at heq
        have hn : (neighborsWithin G (S.erase v) v).card ≤ 2 := by
          apply le_trans _ hdegree
          apply card_le_card
          intro w hw
          simp only [neighborsWithin, mem_filter] at hw ⊢
          exact ⟨mem_of_mem_erase hw.1, hw.2⟩
        by_cases htwo : S.card = 2
        · have herase : (S.erase v).card = 1 := by
            rw [card_erase_of_mem hv, htwo]
          obtain ⟨w, hw⟩ := card_eq_one.mp herase
          rw [hw, edgesOn_singleton] at heq
          have hnb : (neighborsWithin G (S.erase v) v).card ≤ 1 := by
            calc
              _ ≤ (S.erase v).card := card_filter_le _ _
              _ = 1 := herase
          rw [hw] at hnb
          simpa [htwo, heq] using hnb
        · have hcard := card_erase_add_one hv
          omega

theorem pairGraph_local_sparsity (baseSize depth : ℕ) :
    ∀ S : Finset (PairVertex baseSize depth), 2 ≤ S.card →
      ((pairParentSystem baseSize depth).graph.induce (S : Set _)).edgeSet.ncard
        ≤ 2 * S.card - 3 :=
  local_sparsity_of_two_degenerate _ (pairGraph_isTwoDegenerate baseSize depth)

theorem pairGraphOverFin_local_sparsity (baseSize depth : ℕ) :
    ∀ S : Finset (Fin (Fintype.card (PairVertex baseSize depth))), 2 ≤ S.card →
      ((pairGraphOverFin baseSize depth).induce (S : Set _)).edgeSet.ncard
        ≤ 2 * S.card - 3 :=
  local_sparsity_of_two_degenerate _ (pairGraphOverFin_isTwoDegenerate baseSize depth)

end Erdos566

open Finset SimpleGraph

namespace Erdos566

/-- The complete-host, two-colour Ramsey property. -/
def RamseyProperty {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (N : ℕ) : Prop :=
  ∀ C : SimpleGraph (Fin N), G.IsContained C ∨ H.IsContained Cᶜ

/-- The ordinary Ramsey number, measured in host vertices. -/
noncomputable def graphRamsey {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | RamseyProperty G H N}

/-- This matches the current original problem, including the no-isolates premise. -/
def IsRamseySizeLinear {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) → (graphRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

theorem finite_ramsey_cliques {V : Type*} (C : SimpleGraph V) :
    ∀ a b : ℕ, ∀ S : Finset V, (a + b).choose a ≤ S.card →
      (∃ A ⊆ S, C.IsNClique a A) ∨ (∃ B ⊆ S, Cᶜ.IsNClique b B) := by
  classical
  intro a
  induction a with
  | zero =>
      intro b S hS
      exact Or.inl ⟨∅, empty_subset _, by simp⟩
  | succ a iha =>
      intro b
      induction b with
      | zero =>
          intro S hS
          exact Or.inr ⟨∅, empty_subset _, by simp⟩
      | succ b ihb =>
          intro S hS
          have hpos : 0 < S.card :=
            (Nat.choose_pos (by omega : a + 1 ≤ a + 1 + (b + 1))).trans_le hS
          obtain ⟨v, hv⟩ := card_pos.mp hpos
          let R := (S.erase v).filter (C.Adj v)
          let B := (S.erase v).filter (fun w => ¬C.Adj v w)
          have hsplit : R.card + B.card + 1 = S.card := by
            have h := card_filter_add_card_filter_not (s := S.erase v) (C.Adj v)
            have he := card_erase_add_one hv
            exact h ▸ he
          have hchoose : (a + 1 + (b + 1)).choose (a + 1) =
              (a + (b + 1)).choose a + (a + 1 + b).choose (a + 1) := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              Nat.choose_succ_succ' (a + b + 1) a
          have hRsub : R ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
          have hBsub : B ⊆ S := (filter_subset _ _).trans (erase_subset _ _)
          by_cases hR : (a + (b + 1)).choose a ≤ R.card
          · rcases iha (b + 1) R hR with ⟨A, hA, hclique⟩ | ⟨A, hA, hclique⟩
            · refine Or.inl ⟨insert v A, insert_subset hv (hA.trans hRsub), ?_⟩
              apply hclique.insert
              intro w hw
              exact (mem_filter.mp (hA hw)).2
            · exact Or.inr ⟨A, hA.trans hRsub, hclique⟩
          · have hB : (a + 1 + b).choose (a + 1) ≤ B.card := by omega
            rcases ihb B hB with ⟨A, hA, hclique⟩ | ⟨A, hA, hclique⟩
            · exact Or.inl ⟨A, hA.trans hBsub, hclique⟩
            · refine Or.inr ⟨insert v A, insert_subset hv (hA.trans hBsub), ?_⟩
              apply hclique.insert
              intro w hw
              have hm := mem_filter.mp (hA hw)
              exact ⟨(ne_of_mem_erase hm.1).symm, hm.2⟩

theorem ramseyProperty_exists (p q : ℕ) (G : SimpleGraph (Fin p))
    (H : SimpleGraph (Fin q)) : ∃ N, RamseyProperty G H N := by
  classical
  refine ⟨(p + q).choose p, ?_⟩
  intro C
  have hc := finite_ramsey_cliques C p q univ (by simp)
  rcases hc with ⟨A, _, hA⟩ | ⟨B, _, hB⟩
  · have htop : (⊤ : SimpleGraph (Fin p)).IsContained C :=
      (C.not_cliqueFree_iff_top_isContained p).mp hA.not_cliqueFree
    exact Or.inl ((SimpleGraph.IsContained.of_le le_top).trans htop)
  · have htop : (⊤ : SimpleGraph (Fin q)).IsContained Cᶜ :=
      (Cᶜ.not_cliqueFree_iff_top_isContained q).mp hB.not_cliqueFree
    exact Or.inr ((SimpleGraph.IsContained.of_le le_top).trans htop)

theorem ramseyProperty_graphRamsey (p q : ℕ) (G : SimpleGraph (Fin p))
    (H : SimpleGraph (Fin q)) : RamseyProperty G H (graphRamsey G H) := by
  exact Nat.sInf_mem (ramseyProperty_exists p q G H)

theorem ramseyProperty_mono {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {n N : ℕ} (hn : n ≤ N) (h : RamseyProperty G H n) : RamseyProperty G H N := by
  intro C
  let f : Fin n ↪ Fin N := Fin.castLEEmb hn
  let D := C.comap f
  have hc := h D
  have hd : D.IsContained C := ⟨⟨⟨f, fun hxy => hxy⟩, f.injective⟩⟩
  have hdc : Dᶜ.IsContained Cᶜ := by
    refine ⟨⟨⟨f, ?_⟩, f.injective⟩⟩
    intro x y hxy
    exact ⟨f.injective.ne hxy.1, hxy.2⟩
  exact hc.elim (fun hg => Or.inl (hg.trans hd)) (fun hh => Or.inr (hh.trans hdc))

theorem host_order_lt_graphRamsey {p q N : ℕ} {G : SimpleGraph (Fin p)}
    {H : SimpleGraph (Fin q)} (C : SimpleGraph (Fin N))
    (hG : G.Free C) (hH : H.Free Cᶜ) : N < graphRamsey G H := by
  by_contra h
  have hr := ramseyProperty_mono (Nat.le_of_not_gt h)
    (ramseyProperty_graphRamsey p q G H) C
  exact hr.elim hG hH

theorem completeGraph_has_no_isolates {n : ℕ} (hn : 2 ≤ n) :
    ∀ v, 0 < (⊤ : SimpleGraph (Fin n)).degree v := by
  intro v
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_top, card_compl]
  simp only [Fintype.card_fin, card_singleton]
  omega

theorem completeGraph_edge_count (n : ℕ) :
    (⊤ : SimpleGraph (Fin n)).edgeSet.ncard = n.choose 2 := by
  classical
  calc
    (⊤ : SimpleGraph (Fin n)).edgeSet.ncard =
        (⊤ : SimpleGraph (Fin n)).edgeFinset.card := by
      exact (SimpleGraph.edgeFinset_card.trans (Set.fintypeCard_eq_ncard _)).symm
    _ = n.choose 2 := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

/-- A graph-avoidance witness with more than `c * e(K_n)` vertices defeats `c`. -/
theorem not_ramseySizeLinear_of_clique_witnesses {p : ℕ}
    (G : SimpleGraph (Fin p))
    (witnesses : ∀ c : ℝ, 0 < c → ∃ n N : ℕ, 2 ≤ n ∧
      c * (n.choose 2 : ℝ) < N ∧ ∃ C : SimpleGraph (Fin N),
      G.Free C ∧ (⊤ : SimpleGraph (Fin n)).Free Cᶜ) :
    ¬IsRamseySizeLinear G := by
  classical
  rintro ⟨c, hc, hbound⟩
  obtain ⟨n, N, hn, hN, C, hG, hK⟩ := witnesses c hc
  have hupper := hbound n (⊤ : SimpleGraph (Fin n))
    (completeGraph_has_no_isolates hn)
  rw [completeGraph_edge_count] at hupper
  have hlower := host_order_lt_graphRamsey C hG hK
  have hlower' : (N : ℝ) < graphRamsey G (⊤ : SimpleGraph (Fin n)) := by
    exact_mod_cast hlower
  linarith

end Erdos566

open Finset

namespace Erdos566

noncomputable section

noncomputable def binaryEntropy (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2
def tau : ℝ := 43 / 100
def beta : ℝ := 4857 / 5000
def entropySlack : ℝ := 1 / 100000
noncomputable def entropyThreshold : ℝ := (1 + binaryEntropy (9 / 25)) / 2
def baseSize : ℕ := 10000000
def layerDepth : ℕ := 20000

theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem reduced_log_bounds {y lo hi : ℝ}
    (ht : |(y - 1) / (y + 1)| < 1)
    (hlo : lo < 2 * ((∑ i ∈ range 12,
        ((y - 1) / (y + 1)) ^ (2 * i + 1) / (2 * i + 1)) -
      |(y - 1) / (y + 1)| ^ 25 / (1 - ((y - 1) / (y + 1)) ^ 2)))
    (hhi : 2 * ((∑ i ∈ range 12,
        ((y - 1) / (y + 1)) ^ (2 * i + 1) / (2 * i + 1)) +
      |(y - 1) / (y + 1)| ^ 25 / (1 - ((y - 1) / (y + 1)) ^ 2)) < hi)
    (hy : y + 1 ≠ 0) : lo < Real.log y ∧ Real.log y < hi := by
  have h := Real.sum_range_sub_log_div_le ht 12
  have hid : (1 + (y - 1) / (y + 1)) / (1 - (y - 1) / (y + 1)) = y := by
    field_simp
    <;> ring
  rw [hid] at h
  have hb := abs_le.mp h
  norm_num at hb
  constructor <;> linarith

theorem log_scaled_div (y : ℝ) (k : ℕ) (hy : y ≠ 0) :
    Real.log (y / 2 ^ k) = Real.log y - (k : ℝ) * Real.log 2 := by
  rw [Real.log_div hy (pow_ne_zero _ (by norm_num)), Real.log_pow]


set_option maxHeartbeats 2000000 in
theorem log_two_bounds :
    (6931471804 : ℝ) / 10000000000 < Real.log (2 : ℝ) ∧
    Real.log (2 : ℝ) < (6931471807 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_36_bounds :
    (3646431134 : ℝ) / 10000000000 < Real.log (36 / 25 : ℝ) ∧
    Real.log (36 / 25 : ℝ) < (3646431137 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_64_bounds :
    (2468600778 : ℝ) / 10000000000 < Real.log (32 / 25 : ℝ) ∧
    Real.log (32 / 25 : ℝ) < (2468600781 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_43_bounds :
    (5423242907 : ℝ) / 10000000000 < Real.log (43 / 25 : ℝ) ∧
    Real.log (43 / 25 : ℝ) < (5423242910 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_57_bounds :
    (1310282623 : ℝ) / 10000000000 < Real.log (57 / 50 : ℝ) ∧
    Real.log (57 / 50 : ℝ) < (1310282626 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_0049_bounds :
    (2266573705 : ℝ) / 10000000000 < Real.log (784 / 625 : ℝ) ∧
    Real.log (784 / 625 : ℝ) < (2266573708 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

set_option maxHeartbeats 2000000 in
theorem log_scaled_9951_bounds :
    (6882351360 : ℝ) / 10000000000 < Real.log (9951 / 5000 : ℝ) ∧
    Real.log (9951 / 5000 : ℝ) < (6882351363 : ℝ) / 10000000000 := by
  apply reduced_log_bounds
  all_goals norm_num [Finset.sum_range_succ]

theorem entropy_36_bounds :
    (94268 : ℝ) / 100000 < binaryEntropy (9 / 25) ∧
    binaryEntropy (9 / 25) < (94270 : ℝ) / 100000 := by
  have hq : Real.log (9 / 25 : ℝ) =
      Real.log (36 / 25 : ℝ) - 2 * Real.log 2 := by
    convert log_scaled_div (36 / 25) 2 (by norm_num) using 1 <;> norm_num
  have hc : Real.log (16 / 25 : ℝ) =
      Real.log (32 / 25 : ℝ) - Real.log 2 := by
    convert log_scaled_div (32 / 25) 1 (by norm_num) using 1 <;> norm_num
  have hform : Real.binEntropy (9 / 25) =
      -(9 / 25 : ℝ) * Real.log (9 / 25) - (16 / 25) * Real.log (16 / 25) := by
    simp only [Real.binEntropy, Real.log_inv]
    norm_num
    <;> ring
  unfold binaryEntropy
  rw [hform, hq, hc]
  constructor
  · apply (lt_div_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_36_bounds.1, log_scaled_36_bounds.2,
      log_scaled_64_bounds.1, log_scaled_64_bounds.2]
  · apply (div_lt_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_36_bounds.1, log_scaled_36_bounds.2,
      log_scaled_64_bounds.1, log_scaled_64_bounds.2]

theorem entropy_43_bounds :
    (98581 : ℝ) / 100000 < binaryEntropy (43 / 100) ∧
    binaryEntropy (43 / 100) < (98582 : ℝ) / 100000 := by
  have hq : Real.log (43 / 100 : ℝ) =
      Real.log (43 / 25 : ℝ) - 2 * Real.log 2 := by
    convert log_scaled_div (43 / 25) 2 (by norm_num) using 1 <;> norm_num
  have hc : Real.log (57 / 100 : ℝ) =
      Real.log (57 / 50 : ℝ) - Real.log 2 := by
    convert log_scaled_div (57 / 50) 1 (by norm_num) using 1 <;> norm_num
  have hform : Real.binEntropy (43 / 100) =
      -(43 / 100 : ℝ) * Real.log (43 / 100) -
        (57 / 100) * Real.log (57 / 100) := by
    simp only [Real.binEntropy, Real.log_inv]
    norm_num
    <;> ring
  unfold binaryEntropy
  rw [hform, hq, hc]
  constructor
  · apply (lt_div_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_43_bounds.1, log_scaled_43_bounds.2,
      log_scaled_57_bounds.1, log_scaled_57_bounds.2]
  · apply (div_lt_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_43_bounds.1, log_scaled_43_bounds.2,
      log_scaled_57_bounds.1, log_scaled_57_bounds.2]

theorem entropy_0049_bounds :
    (4464 : ℝ) / 100000 < binaryEntropy (49 / 10000) ∧
    binaryEntropy (49 / 10000) < (4465 : ℝ) / 100000 := by
  have hq : Real.log (49 / 10000 : ℝ) =
      Real.log (784 / 625 : ℝ) - 8 * Real.log 2 := by
    convert log_scaled_div (784 / 625) 8 (by norm_num) using 1 <;> norm_num
  have hc : Real.log (9951 / 10000 : ℝ) =
      Real.log (9951 / 5000 : ℝ) - Real.log 2 := by
    convert log_scaled_div (9951 / 5000) 1 (by norm_num) using 1 <;> norm_num
  have hform : Real.binEntropy (49 / 10000) =
      -(49 / 10000 : ℝ) * Real.log (49 / 10000) -
        (9951 / 10000) * Real.log (9951 / 10000) := by
    simp only [Real.binEntropy, Real.log_inv]
    norm_num
    <;> ring
  unfold binaryEntropy
  rw [hform, hq, hc]
  constructor
  · apply (lt_div_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_0049_bounds.1, log_scaled_0049_bounds.2,
      log_scaled_9951_bounds.1, log_scaled_9951_bounds.2]
  · apply (div_lt_iff₀ log_two_pos).mpr
    linarith [log_two_bounds.1, log_two_bounds.2,
      log_scaled_0049_bounds.1, log_scaled_0049_bounds.2,
      log_scaled_9951_bounds.1, log_scaled_9951_bounds.2]

theorem entropyThreshold_lt : entropyThreshold < (97135 : ℝ) / 100000 := by
  have h := entropy_36_bounds.2
  unfold entropyThreshold
  linarith

theorem spectral_gap_margin :
    (19 : ℝ) / 1250 < (binaryEntropy tau + binaryEntropy (49 / 10000) - 1) / 2 := by
  have h := entropy_43_bounds.1
  have h' := entropy_0049_bounds.1
  unfold tau
  linarith

theorem fingerprint_exponent_margin :
    1 - binaryEntropy tau < (71 : ℝ) / 5000 := by
  have h := entropy_43_bounds.1
  unfold tau
  linarith

theorem growth_rate_margin :
    1 - beta - 2 * ((57 : ℝ) / 4000) = 1 / 10000 := by
  norm_num [beta]

theorem ramsey_exponent :
    (1 - beta) / ((57 : ℝ) / 4000) = 572 / 285 := by
  norm_num [beta]

theorem residual_sample_exponent :
    (197 : ℝ) / 200 - beta = 17 / 1250 := by
  norm_num [beta]

theorem krawtchouk_edge_margin :
    (49 : ℝ) / 10000 < 1 / 2 - Real.sqrt (tau * (1 - tau)) := by
  have hs := Real.sq_sqrt (show 0 ≤ tau * (1 - tau) by norm_num [tau])
  have hn := Real.sqrt_nonneg (tau * (1 - tau))
  norm_num [tau] at hs hn ⊢
  nlinarith

theorem potential_increment {before after conditional error : ℝ}
    (he : error < entropySlack)
    (hl : beta - entropySlack < conditional)
    (hu : conditional ≤ entropyThreshold + (after - before) / 2 + error) :
    (3 : ℝ) / 50000 < after - before := by
  have ht := entropyThreshold_lt
  norm_num [beta, entropySlack] at he hl
  linarith

theorem potential_steps_impossible (potential : ℕ → ℝ)
    (hrange : ∀ i ≤ layerDepth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hsteps : ∀ i < layerDepth, (3 : ℝ) / 50000 < potential (i + 1) - potential i) :
    False := by
  have htotal : ∀ n : ℕ, n ≤ layerDepth →
      (n : ℝ) * (3 / 50000) ≤ potential n - potential 0 := by
    intro n
    induction n with
    | zero => intro hn; simp
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hstep := hsteps n (by omega)
        push_cast
        linarith
  have hs := (hrange 0 (Nat.zero_le _)).1
  have hf := (hrange layerDepth le_rfl).2
  have ht := htotal layerDepth le_rfl
  norm_num [layerDepth] at ht hf
  linarith

theorem entropy_layers_impossible
    (potential conditional error : ℕ → ℝ)
    (hrange : ∀ i ≤ layerDepth, 0 ≤ potential i ∧ potential i ≤ 1)
    (he : ∀ i < layerDepth, error i < entropySlack)
    (hl : ∀ i < layerDepth, beta - entropySlack < conditional i)
    (hu : ∀ i < layerDepth, conditional i ≤ entropyThreshold +
      (potential (i + 1) - potential i) / 2 + error i) : False := by
  apply potential_steps_impossible potential hrange
  intro i hi
  exact potential_increment (he i hi) (hl i hi) (hu i hi)

end

end Erdos566

open Finset SimpleGraph

namespace Erdos566

noncomputable def counterexampleOrder : ℕ :=
  Fintype.card (PairVertex baseSize layerDepth)

noncomputable def counterexampleGraph : SimpleGraph (Fin counterexampleOrder) :=
  pairGraphOverFin baseSize layerDepth

/-- The original universal statement, with ordinary complete-host Ramsey numbers. -/
def OriginalStatement : Prop :=
  ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
    (∀ S : Finset (Fin p), 2 ≤ S.card →
      (G.induce (S : Set _)).edgeSet.ncard ≤ 2 * S.card - 3) →
    IsRamseySizeLinear G

theorem counterexampleGraph_satisfies_local_premise :
    ∀ S : Finset (Fin counterexampleOrder), 2 ≤ S.card →
      (counterexampleGraph.induce (S : Set _)).edgeSet.ncard ≤ 2 * S.card - 3 :=
  pairGraphOverFin_local_sparsity baseSize layerDepth

theorem counterexampleGraph_bipartite : counterexampleGraph.IsBipartite :=
  pairGraphOverFin_isBipartite baseSize layerDepth

theorem counterexampleGraph_two_degenerate : IsTwoDegenerate counterexampleGraph :=
  pairGraphOverFin_isTwoDegenerate baseSize layerDepth

abbrev Cube (dimension : ℕ) := Fin dimension → Bool

/-- The cutoff is even. Adjacency includes both odd and even positive distances. -/
def cubeCutoff (dimension : ℕ) : ℕ := 2 * (43 * dimension / 200)

def cubeGraph (dimension : ℕ) : SimpleGraph (Cube dimension) :=
  SimpleGraph.fromRel (fun x y => hammingDist x y ≤ cubeCutoff dimension)

theorem cubeGraph_adj_iff {dimension : ℕ} (x y : Cube dimension) :
    (cubeGraph dimension).Adj x y ↔
      x ≠ y ∧ hammingDist x y ≤ cubeCutoff dimension := by
  simp only [cubeGraph, SimpleGraph.fromRel_adj, hammingDist_comm, or_self]

theorem cubeCutoff_even (dimension : ℕ) : Even (cubeCutoff dimension) := by
  exact even_two_mul _

theorem cubeCutoff_multiple (m : ℕ) : cubeCutoff (40000 * m) = 17200 * m := by
  unfold cubeCutoff
  omega

/--
The sampling conclusion. Dimensions are restricted to multiples of 40000
to make the exponential scales integer powers of two. The theorem
Spectrum.sampled_cube_statement below proves this proposition.
-/
def SampledCubeStatement : Prop :=
  ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ S : Finset (Cube (40000 * m)),
    2 ^ (1144 * m) ≤ 2 * S.card ∧
    counterexampleGraph.Free ((cubeGraph (40000 * m)).induce (S : Set _)) ∧
    (⊤ : SimpleGraph (Fin (2 ^ (570 * m)))).Free
      (((cubeGraph (40000 * m)).induce (S : Set _))ᶜ)

def FiniteWitnessStatement : Prop :=
  ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ N : ℕ, ∃ C : SimpleGraph (Fin N),
    2 ^ (1144 * m) ≤ 2 * N ∧ counterexampleGraph.Free C ∧
      (⊤ : SimpleGraph (Fin (2 ^ (570 * m)))).Free Cᶜ

theorem finite_witnesses_of_sampled_cube (h : SampledCubeStatement) :
    FiniteWitnessStatement := by
  classical
  obtain ⟨m₀, hm₀⟩ := h
  refine ⟨m₀, ?_⟩
  intro m hm
  obtain ⟨S, hS, hG, hK⟩ := hm₀ m hm
  let P := (cubeGraph (40000 * m)).induce (S : Set _)
  let C := P.overFin rfl
  let e : P ≃g C := P.overFinIso rfl
  refine ⟨Fintype.card S, C, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using hS
  · intro hc
    apply hG
    exact hc.trans e.symm.isContained
  · intro hc
    apply hK
    have hcompl : Cᶜ.IsContained Pᶜ := by
      refine ⟨⟨⟨e.symm, ?_⟩, e.symm.injective⟩⟩
      intro x y hxy
      refine ⟨e.symm.injective.ne hxy.1, ?_⟩
      intro hp
      exact hxy.2 (by simpa using e.toHom.map_adj hp)
    exact hc.trans hcompl

theorem not_original_of_finite_witnesses (h : FiniteWitnessStatement) :
    ¬OriginalStatement := by
  classical
  obtain ⟨m₀, hm₀⟩ := h
  have hbad : ¬IsRamseySizeLinear counterexampleGraph := by
    apply not_ramseySizeLinear_of_clique_witnesses
    intro c hc
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * c)
    let m := max k (m₀ + 1)
    have hkm : k ≤ m := le_max_left _ _
    have hmm : m₀ + 1 ≤ m := le_max_right _ _
    have hmpos : 0 < m := by omega
    obtain ⟨N, C, hN, hG, hK⟩ := hm₀ m (by omega)
    have hB : 2 ≤ 2 ^ (570 * m) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (570 * m) := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨2 ^ (570 * m), N, hB, ?_, C, hG, hK⟩
    have hcm : 2 * c < (m : ℝ) := hk.trans_le (by exact_mod_cast hkm)
    have hpow : (m : ℝ) < (2 : ℝ) ^ (4 * m) := by
      have hn : m < 2 ^ m := Nat.lt_two_pow_self
      have hn' : m < 2 ^ (4 * m) := hn.trans_le
        (Nat.pow_le_pow_right (by omega) (by omega))
      exact_mod_cast hn'
    have hscale : (2 : ℝ) ^ (1144 * m) =
        (2 : ℝ) ^ (4 * m) * ((2 : ℝ) ^ (570 * m)) ^ 2 := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hNR : (2 : ℝ) ^ (1144 * m) ≤ 2 * (N : ℝ) := by
      exact_mod_cast hN
    have hBpos : 0 < (2 : ℝ) ^ (570 * m) := by positivity
    have hchoose : ((2 ^ (570 * m)).choose 2 : ℝ) =
        ((2 : ℝ) ^ (570 * m)) * ((2 : ℝ) ^ (570 * m) - 1) / 2 := by
      rw [Nat.cast_choose_two]
      norm_num
    rw [hchoose]
    have hcscale : 2 * c < (2 : ℝ) ^ (4 * m) := hcm.trans hpow
    have hproduct := mul_lt_mul_of_pos_right hcscale (sq_pos_of_pos hBpos)
    rw [hscale] at hNR
    nlinarith [mul_pos hc hBpos]
  intro hOriginal
  exact hbad (hOriginal counterexampleOrder counterexampleGraph
    counterexampleGraph_satisfies_local_premise)

/-- This reduction converts the sampling conclusion into the original negation. -/
theorem not_original_of_sampled_cube (h : SampledCubeStatement) :
    ¬OriginalStatement :=
  not_original_of_finite_witnesses (finite_witnesses_of_sampled_cube h)

end Erdos566

/-
Reusable binary entropy and probability lemmas from OpenAI et al.,
CompactnessAndDegeneracy.lean, git blob
0e973d50014e8c800af597ef699ef29b81e42fc6.
The accompanying LICENSE-OpenAI contains the original Apache-2.0 license.
This extraction preserves the mathematical definitions and proofs.
-/

open Finset Filter
open scoped Topology

namespace Erdos566.Retuned

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

theorem log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

theorem binaryEntropy_nonneg {x : ℝ} (hzero : 0 ≤ x)
    (hone : x ≤ 1) : 0 ≤ binaryEntropy x := by
  exact div_nonneg (Real.binEntropy_nonneg hzero hone) log_two_pos.le

theorem binaryEntropy_le_one (x : ℝ) : binaryEntropy x ≤ 1 := by
  unfold binaryEntropy
  apply (div_le_iff₀ log_two_pos).2
  simpa using (Real.binEntropy_le_log_two (p := x))

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] theorem binaryEntropy_one_sub (x : ℝ) :
    binaryEntropy (1 - x) = binaryEntropy x := by
  simp [binaryEntropy]

@[fun_prop] theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _

theorem binaryEntropy_scale_le (probability scale : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hscale_zero : 0 ≤ scale)
    (hscale_one : scale ≤ 1) :
    scale * binaryEntropy probability ≤
      binaryEntropy (scale * probability) := by
  have hconcavity := Real.strictConcave_binEntropy.concaveOn.2
    (show probability ∈ Set.Icc (0 : ℝ) 1 from
      ⟨hprobability_zero, hprobability_one⟩)
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
    hscale_zero (sub_nonneg.mpr hscale_one)
    (show scale + (1 - scale) = 1 by ring)
  have hnatural :
      scale * Real.binEntropy probability ≤
        Real.binEntropy (scale * probability) := by
    simpa [smul_eq_mul] using hconcavity
  unfold binaryEntropy
  calc
    scale * (Real.binEntropy probability / Real.log 2) =
      (scale * Real.binEntropy probability) / Real.log 2 := by ring
    _ ≤ Real.binEntropy (scale * probability) / Real.log 2 :=
      (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

theorem binaryEntropy_subadditive (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y ≤ 1) :
    binaryEntropy (x + y) ≤ binaryEntropy x + binaryEntropy y := by
  by_cases hzero : x + y = 0
  · have hxzero : x = 0 := by linarith
    have hyzero : y = 0 := by linarith
    simp [hxzero, hyzero]
  have hpositive : 0 < x + y :=
    lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hzero)
  have hxscale : 0 ≤ x / (x + y) :=
    div_nonneg hx hpositive.le
  have hyscale : 0 ≤ y / (x + y) :=
    div_nonneg hy hpositive.le
  have hxscale_one : x / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hyscale_one : y / (x + y) ≤ 1 := by
    apply (div_le_one hpositive).mpr
    linarith
  have hxentropy := binaryEntropy_scale_le (x + y) (x / (x + y))
    (add_nonneg hx hy) hsum hxscale hxscale_one
  have hyentropy := binaryEntropy_scale_le (x + y) (y / (x + y))
    (add_nonneg hx hy) hsum hyscale hyscale_one
  have hxidentity : x / (x + y) * (x + y) = x := by
    field_simp [hpositive.ne']
  have hyidentity : y / (x + y) * (x + y) = y := by
    field_simp [hpositive.ne']
  rw [hxidentity] at hxentropy
  rw [hyidentity] at hyentropy
  have hcombined := add_le_add hxentropy hyentropy
  have hleft :
      x / (x + y) * binaryEntropy (x + y) +
          y / (x + y) * binaryEntropy (x + y) =
        binaryEntropy (x + y) := by
    field_simp [hpositive.ne']
  rw [hleft] at hcombined
  exact hcombined

theorem abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (x y : ℝ)
    (hxzero : 0 ≤ x) (hxone : x ≤ 1)
    (hyzero : 0 ≤ y) (hyone : y ≤ 1) :
    |binaryEntropy x - binaryEntropy y| ≤
      binaryEntropy |x - y| := by
  have hordered :
      ∀ x y : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → x ≤ y →
        |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| := by
    intro a b hazero haone hbzero hbone hab
    have hdifference : 0 ≤ b - a := sub_nonneg.mpr hab
    have hforward :
        binaryEntropy b ≤ binaryEntropy a + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive a (b - a)
        hazero hdifference (by linarith)
      have hargument : a + (b - a) = b := by ring
      rwa [hargument] at h
    have hbackward :
        binaryEntropy a ≤ binaryEntropy b + binaryEntropy (b - a) := by
      have h := binaryEntropy_subadditive (1 - b) (b - a)
        (sub_nonneg.mpr hbone) hdifference (by linarith)
      have hargument : 1 - b + (b - a) = 1 - a := by ring
      rw [hargument, binaryEntropy_one_sub, binaryEntropy_one_sub] at h
      exact h
    rw [abs_of_nonpos (sub_nonpos.mpr hab), abs_le]
    have hneg : -(a - b) = b - a := by ring
    rw [hneg]
    constructor <;> linarith
  by_cases hxy : x ≤ y
  · exact hordered x y hxzero hxone hyzero hyone hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    have h := hordered y x hyzero hyone hxzero hxone hyx
    simpa [abs_sub_comm] using h

theorem binaryEntropy_mono_on_half
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyhalf : y ≤ (2 : ℝ)⁻¹) :
    binaryEntropy x ≤ binaryEntropy y := by
  have hy : 0 ≤ y := hx.trans hxy
  have hxhalf : x ≤ (2 : ℝ)⁻¹ := hxy.trans hyhalf
  have hnatural := Real.binEntropy_strictMonoOn.monotoneOn
    (show x ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hx, hxhalf⟩)
    (show y ∈ Set.Icc (0 : ℝ) ((2 : ℝ)⁻¹) from ⟨hy, hyhalf⟩)
    hxy
  unfold binaryEntropy
  exact (div_le_div_iff_of_pos_right log_two_pos).mpr hnatural

noncomputable def binaryPinskerGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2

noncomputable def binaryPinskerGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1)

noncomputable def binaryPinskerGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4

theorem binaryPinskerGap_continuous : Continuous binaryPinskerGap := by
  unfold binaryPinskerGap
  fun_prop

theorem binaryPinskerGap_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGap (binaryPinskerGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    ((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGap, binaryPinskerGapDeriv]; ring)

theorem binaryPinskerGapDeriv_hasDerivAt {q : ℝ}
    (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt binaryPinskerGapDeriv (binaryPinskerGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    ((Real.hasDerivAt_log hqzero).sub
      (hcomplement.log hcomplement_ne)).sub (hlinear.const_mul 2)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [binaryPinskerGapDeriv, binaryPinskerGapDerivTwo]; ring)

theorem binaryPinskerGapDerivTwo_nonneg {q : ℝ}
    (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ binaryPinskerGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      binaryPinskerGapDerivTwo q =
        (2 * q - 1) ^ 2 / (q * (1 - q)) := by
    unfold binaryPinskerGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (sq_nonneg _) (mul_pos hqzero hcomplement).le

theorem binaryPinskerGap_convex :
    ConvexOn ℝ (Set.Icc 0 1) binaryPinskerGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := binaryPinskerGapDeriv)
    (f'' := binaryPinskerGapDerivTwo)
    (convex_Icc (0 : ℝ) 1)
    binaryPinskerGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact (binaryPinskerGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact
      (binaryPinskerGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa only [interior_Icc] using hq
    exact binaryPinskerGapDerivTwo_nonneg hq'.1 hq'.2

@[simp] theorem binaryPinskerGap_half :
    binaryPinskerGap ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGap
  rw [Real.binEntropy_two_inv]
  norm_num

@[simp] theorem binaryPinskerGapDeriv_half :
    binaryPinskerGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold binaryPinskerGapDeriv
  norm_num

theorem binary_pinsker (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x →
        0 ≤ binaryPinskerGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x :=
        lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid :
          HasDerivAt binaryPinskerGap 0 ((2 : ℝ)⁻¹) := by
        convert binaryPinskerGap_hasDerivAt
          (q := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1
        exact binaryPinskerGapDeriv_half.symm
      have hslope := binaryPinskerGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩)
        hxstrict hmid
      rw [slope_def_field, binaryPinskerGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold binaryPinskerGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone)
      (by linarith) hcomplement
    unfold binaryPinskerGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith

theorem log_le_tangent {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hc)
  rw [Real.log_div hx.ne' hc.ne'] at hlog
  linarith

theorem log_four_thirds_lt_one_third :
    Real.log ((4 : ℝ) / 3) < (1 : ℝ) / 3 := by
  have hlog := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 : ℝ) / 3 ≠ 1 by norm_num)
  norm_num at hlog ⊢
  linarith

theorem sqrt_one_add_le (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (1 + x) ≤ 1 + x / 2 := by
  have hroot := Real.sqrt_nonneg (1 + x)
  have hsquare := Real.sq_sqrt (show 0 ≤ 1 + x by linarith)
  nlinarith [sq_nonneg x]

theorem normalized_binary_cauchy (a b x y : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    a * x + b * y ≤ Real.sqrt (x ^ 2 + y ^ 2) := by
  have hrad : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hroot := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hsquare := Real.sq_sqrt hrad
  have hidentity :
      (a * x + b * y) ^ 2 + (a * y - b * x) ^ 2 =
        (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    ring
  rw [hab, one_mul] at hidentity
  nlinarith [sq_nonneg (a * y - b * x)]

theorem binary_log_sum_bound (probability zeroWeight oneWeight : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1)
    (hzeroWeight : 0 < zeroWeight)
    (honeWeight : 0 < oneWeight) :
    Real.binEntropy probability +
        (1 - probability) * Real.log zeroWeight +
        probability * Real.log oneWeight ≤
      Real.log (zeroWeight + oneWeight) := by
  by_cases hzero : probability = 0
  · subst probability
    simpa using Real.log_le_log hzeroWeight
      (le_add_of_nonneg_right honeWeight.le)
  by_cases hone : probability = 1
  · subst probability
    simpa using Real.log_le_log honeWeight
      (le_add_of_nonneg_left hzeroWeight.le)
  have hprobability_pos : 0 < probability :=
    lt_of_le_of_ne hprobability_zero (Ne.symm hzero)
  have hcomplement_pos : 0 < 1 - probability :=
    sub_pos.mpr (lt_of_le_of_ne hprobability_one hone)
  have hnormalize :
      (1 - probability) * (zeroWeight / (1 - probability)) +
          probability * (oneWeight / probability) =
        zeroWeight + oneWeight := by
    field_simp [hprobability_pos.ne', hcomplement_pos.ne']
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.2
    (show zeroWeight / (1 - probability) ∈ Set.Ioi (0 : ℝ) from
      div_pos hzeroWeight hcomplement_pos)
    (show oneWeight / probability ∈ Set.Ioi (0 : ℝ) from
      div_pos honeWeight hprobability_pos)
    hcomplement_pos.le hprobability_pos.le
    (show (1 - probability) + probability = 1 by ring)
  simp only [smul_eq_mul] at hjensen
  rw [hnormalize] at hjensen
  rw [Real.log_div hzeroWeight.ne' hcomplement_pos.ne',
    Real.log_div honeWeight.ne' hprobability_pos.ne'] at hjensen
  have hentropy :
      Real.binEntropy probability =
        -(1 - probability) * Real.log (1 - probability) -
          probability * Real.log probability := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  rw [hentropy]
  linarith

def binaryCoinMass (q : ℝ) (outcome : Bool) : ℝ :=
  if outcome then q else 1 - q

theorem binaryCoinMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (outcome : Bool) :
    0 ≤ binaryCoinMass q outcome := by
  cases outcome <;> simp [binaryCoinMass] <;> linarith

def independentBinaryPairMass (q : ℝ) (left right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q right

theorem independentBinaryPairMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left right : Bool) :
    0 ≤ independentBinaryPairMass q left right := by
  exact mul_nonneg
    (binaryCoinMass_nonneg hqzero hqone left)
    (binaryCoinMass_nonneg hqzero hqone right)

theorem independentBinaryPairMass_sum (q : ℝ) :
    (∑ left : Bool, ∑ right : Bool,
      independentBinaryPairMass q left right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryPairMass, binaryCoinMass]
  ring

structure BinaryPairKernel where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : Bool → Bool → ℝ
  childProbability_nonneg : ∀ left right, 0 ≤ childProbability left right
  childProbability_le_one : ∀ left right, childProbability left right ≤ 1

namespace BinaryPairKernel

noncomputable def childMarginal (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      kernel.childProbability left right

noncomputable def conditionalEntropy (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy (kernel.childProbability left right)

def bitDisagreementProbability (parent : Bool) (childProbability : ℝ) : ℝ :=
  if parent then 1 - childProbability else childProbability

noncomputable def averageDisagreement (kernel : BinaryPairKernel) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      ((bitDisagreementProbability left
          (kernel.childProbability left right) +
        bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem childMarginal_nonneg (kernel : BinaryPairKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (independentBinaryPairMass_nonneg
      kernel.parentProbability_nonneg kernel.parentProbability_le_one
      left right)
    (kernel.childProbability_nonneg left right)

theorem childMarginal_le_one (kernel : BinaryPairKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right *
          kernel.childProbability left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        independentBinaryPairMass kernel.parentProbability left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left
            (kernel.childProbability_le_one left right)
            (independentBinaryPairMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one
              left right)
    _ = 1 := by
      simpa using independentBinaryPairMass_sum kernel.parentProbability

theorem childMarginal_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          kernel.childProbability false true +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          kernel.childProbability true false +
        kernel.parentProbability ^ 2 *
          kernel.childProbability true true := by
  simp [childMarginal, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass]
  ring

theorem conditionalEntropy_mul_log_two (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy * Real.log 2 =
      (1 - kernel.parentProbability) ^ 2 *
          Real.binEntropy (kernel.childProbability false false) +
        (1 - kernel.parentProbability) * kernel.parentProbability *
          Real.binEntropy (kernel.childProbability false true) +
        kernel.parentProbability * (1 - kernel.parentProbability) *
          Real.binEntropy (kernel.childProbability true false) +
        kernel.parentProbability ^ 2 *
          Real.binEntropy (kernel.childProbability true true) := by
  simp [conditionalEntropy, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass, binaryEntropy]
  field_simp [log_two_pos.ne']
  ring

theorem bitDisagreementProbability_mem_Icc (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by
  cases parent <;> simp [bitDisagreementProbability] <;> constructor <;>
    linarith

theorem averageDisagreement_eq_four_outcomes (kernel : BinaryPairKernel) :
    kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 2 *
          kernel.childProbability false false +
        kernel.parentProbability * (1 - kernel.parentProbability) +
        kernel.parentProbability ^ 2 *
          (1 - kernel.childProbability true true) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryPairMass, binaryCoinMass,
    bitDisagreementProbability]
  ring

noncomputable def smoothed (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryPairKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability left right :=
    (1 - mixing) * kernel.childProbability left right + mixing / 2
  childProbability_nonneg := by
    intro left right
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one)
        (kernel.childProbability_nonneg left right))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro left right
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one left right)
      (sub_nonneg.mpr hmixing_one)
    nlinarith

theorem smoothed_childMarginal (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_four_outcomes,
    childMarginal_eq_four_outcomes kernel]
  simp [smoothed]
  ring

theorem smoothed_averageDisagreement (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  rw [averageDisagreement_eq_four_outcomes,
    averageDisagreement_eq_four_outcomes kernel]
  simp [smoothed]
  ring

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryPairKernel) (mixing : ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    independentBinaryPairMass kernel.parentProbability left right *
      binaryEntropy
        ((1 - mixing) * kernel.childProbability left right + mixing / 2)

theorem smoothedConditionalEntropy_continuous (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by
  rfl


end BinaryPairKernel
end Erdos566.Retuned

/-
The new entropy estimate for the proposed Erdős 566 counterexample.
The definitions and elementary entropy lemmas imported from EntropyFoundation
are credited there. The weight 9/16 and the tangent calculation below are the
retuning used in the private proposal.
-/

namespace Erdos566.Retuned

noncomputable section

def weight : ℝ := 9 / 16
def bias : ℝ := 7 / 25
def tangentSame : ℝ := 25 * Real.sqrt 2 / 32
def tangentMixed : ℝ := 3 * Real.sqrt 2 / 4

def entropyConstant : ℝ :=
  (Real.log 2 / 2 + Real.log (25 / 16) / 2 + Real.log (9 / 16) / 4) /
    Real.log 2

def entropySlope : ℝ := -Real.log (9 / 16) / Real.log 2

def logPotential (q a b : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 2 * Real.log (a + weight * b) +
    q ^ 2 * Real.log (weight * a + b) +
    2 * q * (1 - q) * Real.log ((3 / 4) * (a + b))

theorem sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := by positivity

theorem sqrt_two_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
  exact Real.sq_sqrt (by norm_num)

theorem tangentSame_pos : 0 < tangentSame := by
  unfold tangentSame
  positivity

theorem tangentMixed_pos : 0 < tangentMixed := by
  unfold tangentMixed
  positivity

theorem log_tangentSame :
    Real.log tangentSame = Real.log (25 / 16) - Real.log 2 / 2 := by
  have htwo : (Real.sqrt (2 : ℝ)) ≠ 0 := sqrt_two_pos.ne'
  have hid : tangentSame = (25 / 16) / Real.sqrt 2 := by
    unfold tangentSame
    field_simp
    nlinarith [sqrt_two_sq]
  rw [hid, Real.log_div (by norm_num) htwo, Real.log_sqrt (by norm_num)]

theorem log_tangentMixed :
    Real.log tangentMixed = Real.log (9 / 16) / 2 + Real.log 2 / 2 := by
  have hthree : Real.log (9 / 16 : ℝ) = 2 * Real.log (3 / 4 : ℝ) := by
    have hid : (9 / 16 : ℝ) = (3 / 4 : ℝ) ^ 2 := by norm_num
    rw [hid, Real.log_pow]
    norm_num
  unfold tangentMixed
  rw [Real.log_div (mul_ne_zero (by norm_num) sqrt_two_pos.ne') (by norm_num),
    Real.log_mul (by norm_num) sqrt_two_pos.ne', Real.log_sqrt (by norm_num)]
  have hratio := Real.log_div (show (3 : ℝ) ≠ 0 by norm_num)
    (show (4 : ℝ) ≠ 0 by norm_num)
  rw [hratio] at hthree
  linarith

theorem log_tangent_ratio :
    Real.log tangentSame - Real.log tangentMixed = Real.log (25 / 24 : ℝ) := by
  rw [← Real.log_div tangentSame_pos.ne' tangentMixed_pos.ne']
  congr 1
  unfold tangentSame tangentMixed
  field_simp
  ring

theorem tangent_constant (q : ℝ) :
    ((1 - q) ^ 2 + q ^ 2) * Real.log tangentSame +
        2 * q * (1 - q) * Real.log tangentMixed =
      Real.log (25 / 16) / 2 + Real.log (9 / 16) / 4 +
        (2 * q - 1) ^ 2 * Real.log (25 / 24) / 2 := by
  have hratio := log_tangent_ratio
  rw [log_tangentSame, log_tangentMixed] at hratio ⊢
  linear_combination ((2 * q - 1) ^ 2 / 2) * hratio

theorem tangent_linear (q a b : ℝ) :
    (1 - q) ^ 2 * ((a + weight * b) / tangentSame - 1) +
        q ^ 2 * ((weight * a + b) / tangentSame - 1) +
        2 * q * (1 - q) * (((3 / 4) * (a + b)) / tangentMixed - 1) =
      a * ((1 - bias * (2 * q - 1)) / Real.sqrt 2) +
        b * ((1 + bias * (2 * q - 1)) / Real.sqrt 2) - 1 := by
  unfold weight bias tangentSame tangentMixed
  field_simp
  nlinarith [sqrt_two_sq]

theorem tangent_linear_bound (q a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    a * ((1 - bias * (2 * q - 1)) / Real.sqrt 2) +
        b * ((1 + bias * (2 * q - 1)) / Real.sqrt 2) - 1 ≤
      bias ^ 2 * (2 * q - 1) ^ 2 / 2 := by
  have hid :
      ((1 - bias * (2 * q - 1)) / Real.sqrt 2) ^ 2 +
        ((1 + bias * (2 * q - 1)) / Real.sqrt 2) ^ 2 =
      1 + bias ^ 2 * (2 * q - 1) ^ 2 := by
    field_simp
    nlinarith [sqrt_two_sq]
  have hcauchy := normalized_binary_cauchy a b
    ((1 - bias * (2 * q - 1)) / Real.sqrt 2)
    ((1 + bias * (2 * q - 1)) / Real.sqrt 2) hab
  rw [hid] at hcauchy
  have hsqrt := sqrt_one_add_le (bias ^ 2 * (2 * q - 1) ^ 2) (by positivity)
  linarith

theorem logPotential_le (q a b : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    logPotential q a b ≤ entropyConstant * Real.log 2 := by
  have hfirst := log_le_tangent
    (x := a + weight * b) (c := tangentSame) (by unfold weight; positivity)
    tangentSame_pos
  have hsecond := log_le_tangent
    (x := weight * a + b) (c := tangentSame) (by unfold weight; positivity)
    tangentSame_pos
  have hthird := log_le_tangent
    (x := (3 / 4) * (a + b)) (c := tangentMixed) (by positivity)
    tangentMixed_pos
  have hnonneg : 0 ≤ 2 * q * (1 - q) := by positivity
  have hsum := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hfirst (sq_nonneg (1 - q)))
      (mul_le_mul_of_nonneg_left hsecond (sq_nonneg q)))
    (mul_le_mul_of_nonneg_left hthird hnonneg)
  have hcollected :
      (1 - q) ^ 2 * (Real.log tangentSame + (a + weight * b) / tangentSame - 1) +
        q ^ 2 * (Real.log tangentSame + (weight * a + b) / tangentSame - 1) +
        2 * q * (1 - q) *
          (Real.log tangentMixed + ((3 / 4) * (a + b)) / tangentMixed - 1) =
      (((1 - q) ^ 2 + q ^ 2) * Real.log tangentSame +
        2 * q * (1 - q) * Real.log tangentMixed) +
      ((1 - q) ^ 2 * ((a + weight * b) / tangentSame - 1) +
        q ^ 2 * ((weight * a + b) / tangentSame - 1) +
        2 * q * (1 - q) * (((3 / 4) * (a + b)) / tangentMixed - 1)) := by ring
  rw [hcollected, tangent_constant, tangent_linear] at hsum
  have hlinear := tangent_linear_bound q a b hab
  have hpinsker := binary_pinsker q hqzero hqone
  have hlog : Real.log (25 / 24 : ℝ) ≤ (1 : ℝ) / 24 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 25 / 24 by norm_num)
    linarith
  have hlogmul := mul_le_mul_of_nonneg_left hlog (sq_nonneg (2 * q - 1))
  have hconstant : entropyConstant * Real.log 2 =
      Real.log 2 / 2 + Real.log (25 / 16) / 2 + Real.log (9 / 16) / 4 := by
    unfold entropyConstant
    field_simp [log_two_pos.ne']
  rw [hconstant]
  unfold logPotential
  unfold bias at hlinear hsum
  have hcurvature :
      (2 * q - 1) ^ 2 * Real.log (25 / 24) / 2 +
        (7 / 25 : ℝ) ^ 2 * (2 * q - 1) ^ 2 / 2 - (2 * q - 1) ^ 2 / 4 ≤ 0 := by
    nlinarith only [hlogmul, sq_nonneg (2 * q - 1)]
  nlinarith only [hsum, hlinear, hpinsker, hcurvature]

theorem entropySlope_pos : 0 < entropySlope := by
  unfold entropySlope
  apply div_pos
  · exact neg_pos.mpr (Real.log_neg (by norm_num) (by norm_num))
  · exact log_two_pos

theorem entropyConstant_add_radius :
    entropyConstant + entropySlope * Erdos566.tau = Erdos566.entropyThreshold := by
  have hcomplement : Real.log (25 / 16 : ℝ) = -Real.log (16 / 25) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  have hratio : Real.log (9 / 16 : ℝ) = Real.log (9 / 25) - Real.log (16 / 25) := by
    rw [← Real.log_div (by norm_num : (9 / 25 : ℝ) ≠ 0)
      (by norm_num : (16 / 25 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hreciprocal : Real.log (25 / 9 : ℝ) = -Real.log (9 / 25) := by
    rw [← Real.log_inv]
    congr 1
    norm_num
  unfold entropyConstant entropySlope Erdos566.tau
    Erdos566.entropyThreshold Erdos566.binaryEntropy Real.binEntropy
  norm_num only [show (1 - (9 / 25 : ℝ)) = 16 / 25 by norm_num]
  rw [hreciprocal, hcomplement, hratio]
  field_simp [log_two_pos.ne']
  ring

namespace BinaryPairKernel

theorem conditionalEntropy_logsum_reduction (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy * Real.log 2 -
        Real.binEntropy kernel.childMarginal / 2 -
        (-Real.log (9 / 16)) * kernel.averageDisagreement ≤
      logPotential kernel.parentProbability
          (Real.sqrt (1 - kernel.childMarginal))
          (Real.sqrt kernel.childMarginal) -
        Real.binEntropy kernel.parentProbability / 2 := by
  let q : ℝ := kernel.parentProbability
  let v : ℝ := kernel.childMarginal
  let a : ℝ := Real.sqrt (1 - v)
  let b : ℝ := Real.sqrt v
  let z₀₀ : ℝ := kernel.childProbability false false
  let z₀₁ : ℝ := kernel.childProbability false true
  let z₁₀ : ℝ := kernel.childProbability true false
  let z₁₁ : ℝ := kernel.childProbability true true
  have hqzero : 0 ≤ q := kernel.parentProbability_nonneg
  have hqone : q ≤ 1 := kernel.parentProbability_le_one
  have hvzero : 0 < v := hmarginal_zero
  have hvone : v < 1 := hmarginal_one
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.mpr (sub_pos.mpr hvone)
  have hb : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.mpr hvzero
  have hweight : 0 < weight := by norm_num [weight]
  have hrootweight : (0 : ℝ) < 3 / 4 := by norm_num
  have h₀₀ := binary_log_sum_bound z₀₀ a ((weight * b))
    (kernel.childProbability_nonneg false false)
    (kernel.childProbability_le_one false false)
    ha (mul_pos hweight hb)
  have h₀₁ := binary_log_sum_bound z₀₁
    (((3 / 4) * a)) (((3 / 4) * b))
    (kernel.childProbability_nonneg false true)
    (kernel.childProbability_le_one false true)
    (mul_pos hrootweight ha) (mul_pos hrootweight hb)
  have h₁₀ := binary_log_sum_bound z₁₀
    (((3 / 4) * a)) (((3 / 4) * b))
    (kernel.childProbability_nonneg true false)
    (kernel.childProbability_le_one true false)
    (mul_pos hrootweight ha) (mul_pos hrootweight hb)
  have h₁₁ := binary_log_sum_bound z₁₁ ((weight * a)) b
    (kernel.childProbability_nonneg true true)
    (kernel.childProbability_le_one true true)
    (mul_pos hweight ha) hb
  have hcomplement : 0 ≤ 1 - q := sub_nonneg.mpr hqone
  have hscaled₀₀ := mul_le_mul_of_nonneg_left h₀₀
    (sq_nonneg (1 - q))
  have hscaled₀₁ := mul_le_mul_of_nonneg_left h₀₁
    (mul_nonneg hcomplement hqzero)
  have hscaled₁₀ := mul_le_mul_of_nonneg_left h₁₀
    (mul_nonneg hqzero hcomplement)
  have hscaled₁₁ := mul_le_mul_of_nonneg_left h₁₁ (sq_nonneg q)
  have hcombined := add_le_add
    (add_le_add (add_le_add hscaled₀₀ hscaled₀₁) hscaled₁₀)
    hscaled₁₁
  have hmarginal :
      v =
        (1 - q) ^ 2 * z₀₀ +
          (1 - q) * q * z₀₁ +
          q * (1 - q) * z₁₀ +
          q ^ 2 * z₁₁ := by
    simpa [q, v, z₀₀, z₀₁, z₁₀, z₁₁] using
      childMarginal_eq_four_outcomes kernel
  have hentropy :
      kernel.conditionalEntropy * Real.log 2 =
        (1 - q) ^ 2 * Real.binEntropy z₀₀ +
          (1 - q) * q * Real.binEntropy z₀₁ +
          q * (1 - q) * Real.binEntropy z₁₀ +
          q ^ 2 * Real.binEntropy z₁₁ := by
    simpa [q, z₀₀, z₀₁, z₁₀, z₁₁] using
      conditionalEntropy_mul_log_two kernel
  have hdisagreement :
      kernel.averageDisagreement =
        (1 - q) ^ 2 * z₀₀ +
          q * (1 - q) + q ^ 2 * (1 - z₁₁) := by
    simpa [q, z₀₀, z₁₁] using
      averageDisagreement_eq_four_outcomes kernel
  have hloga : Real.log a = Real.log (1 - v) / 2 := by
    dsimp [a]
    exact Real.log_sqrt (sub_pos.mpr hvone).le
  have hlogb : Real.log b = Real.log v / 2 := by
    dsimp [b]
    exact Real.log_sqrt hvzero.le
  have hlogrootweight : Real.log (3 / 4 : ℝ) = Real.log (9 / 16) / 2 := by
    have hid : (9 / 16 : ℝ) = (3 / 4 : ℝ) ^ 2 := by norm_num
    rw [hid, Real.log_pow]
    ring
  have hchildentropy :
      Real.binEntropy v =
        -v * Real.log v - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]
    ring
  have hleft :
      (((1 - q) ^ 2 *
          (Real.binEntropy z₀₀ +
            (1 - z₀₀) * Real.log a + z₀₀ * Real.log ((weight * b))) +
        ((1 - q) * q) *
          (Real.binEntropy z₀₁ +
            (1 - z₀₁) * Real.log (((3 / 4) * a)) +
              z₀₁ * Real.log (((3 / 4) * b)))) +
        (q * (1 - q)) *
          (Real.binEntropy z₁₀ +
            (1 - z₁₀) * Real.log (((3 / 4) * a)) +
              z₁₀ * Real.log (((3 / 4) * b)))) +
        q ^ 2 *
          (Real.binEntropy z₁₁ +
            (1 - z₁₁) * Real.log ((weight * a)) + z₁₁ * Real.log b) =
        kernel.conditionalEntropy * Real.log 2 -
          Real.binEntropy v / 2 -
          (-Real.log (9 / 16)) * kernel.averageDisagreement := by
    rw [hentropy, hdisagreement, hchildentropy,
      Real.log_mul hweight.ne' hb.ne',
      Real.log_mul hrootweight.ne' ha.ne',
      Real.log_mul hrootweight.ne' hb.ne',
      Real.log_mul hweight.ne' ha.ne', hloga, hlogb,
      hlogrootweight]
    unfold weight
    linear_combination
      ((Real.log (1 - v) - Real.log v) / 2) * hmarginal
  have hright :
      (((1 - q) ^ 2 * Real.log (a + (weight * b)) +
        ((1 - q) * q) *
          Real.log (((3 / 4) * a) + ((3 / 4) * b))) +
        (q * (1 - q)) *
          Real.log (((3 / 4) * a) + ((3 / 4) * b))) +
        q ^ 2 * Real.log ((weight * a) + b) =
        logPotential q a b - Real.binEntropy q / 2 := by
    have hmixed : ((3 / 4) * a) + ((3 / 4) * b) = (3 / 4) * (a + b) := by ring
    rw [hmixed]
    unfold logPotential
    ring
  rw [hleft, hright] at hcombined
  simpa [q, v, a, b] using hcombined


theorem conditionalEntropy_bound_of_marginal_interior
    (kernel : BinaryPairKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      entropyConstant + entropySlope * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hzeroAmplitude :
      0 < Real.sqrt (1 - kernel.childMarginal) :=
    Real.sqrt_pos.mpr (sub_pos.mpr hmarginal_one)
  have honeAmplitude : 0 < Real.sqrt kernel.childMarginal :=
    Real.sqrt_pos.mpr hmarginal_zero
  have hamplitudes :
      Real.sqrt (1 - kernel.childMarginal) ^ 2 +
          Real.sqrt kernel.childMarginal ^ 2 = 1 := by
    rw [Real.sq_sqrt (sub_pos.mpr hmarginal_one).le,
      Real.sq_sqrt hmarginal_zero.le]
    ring
  have hpotential := logPotential_le
    kernel.parentProbability
    (Real.sqrt (1 - kernel.childMarginal))
    (Real.sqrt kernel.childMarginal)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hzeroAmplitude honeAmplitude hamplitudes
  have hreduction := conditionalEntropy_logsum_reduction kernel
    hmarginal_zero hmarginal_one
  have hright :
      (entropyConstant + entropySlope * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        entropyConstant * Real.log 2 +
          (-Real.log (9 / 16)) * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy entropySlope
    field_simp [log_two_pos.ne']
  have hscaled :
      kernel.conditionalEntropy * Real.log 2 ≤
        (entropyConstant + entropySlope * kernel.averageDisagreement +
          (binaryEntropy kernel.childMarginal -
            binaryEntropy kernel.parentProbability) / 2) * Real.log 2 := by
    rw [hright]
    linarith
  exact (mul_le_mul_iff_of_pos_right log_two_pos).mp hscaled

theorem conditionalEntropy_bound (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      entropyConstant + entropySlope * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by
    dsimp [mixing]
    positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    apply (div_le_one (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryPairKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto :
      Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have hnonnegative := mul_nonneg
      (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have hpositive := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left
      (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero :
        smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear :=
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
        (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by
      simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := by
    rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          entropyConstant + entropySlope * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (entropyConstant + entropySlope * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hdisagreement_term :=
      (tendsto_const_nhds (x := entropySlope)).mul hdisagreement_tendsto
    have hentropy_term :=
      (hchildentropy_tendsto.sub
        (tendsto_const_nhds (x :=
          binaryEntropy kernel.parentProbability))).div_const 2
    have hsum :=
      (tendsto_const_nhds (x := entropyConstant)).add
        (hdisagreement_term.add hentropy_term)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto'
    hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)

end BinaryPairKernel

end

end Erdos566.Retuned

/-
The without-replacement comparison is adapted from the Apache-2.0 OpenAI
source identified in EntropyFoundation.lean. The entropy constant and slope
are replaced by the retuned, proved values in RetunedEntropy.lean.
-/

open Finset Filter
open scoped Topology

namespace Erdos566.Retuned

def empiricalBinaryOutcomeCount
    (parentCount oneCount : ℕ) (outcome : Bool) : ℝ :=
  if outcome then (oneCount : ℝ)
  else (parentCount : ℝ) - (oneCount : ℝ)

noncomputable def withoutReplacementBinaryPairMass
    (parentCount oneCount : ℕ) (left right : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount left *
      (empiricalBinaryOutcomeCount parentCount oneCount right -
        if left = right then 1 else 0) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1))

theorem withoutReplacementBinaryPairMass_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (left right : Bool) :
    0 ≤ withoutReplacementBinaryPairMass parentCount oneCount left right := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hdenominator :
      0 ≤ (parentCount : ℝ) * ((parentCount : ℝ) - 1) :=
    (mul_pos hparent_real hparent_minus).le
  have hone_nonneg : (0 : ℝ) ≤ (oneCount : ℝ) := by positivity
  have hcount : (oneCount : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hones
  have hzero_nonneg : 0 ≤ (parentCount : ℝ) - (oneCount : ℝ) := by
    linarith
  have hone_diagonal :
      0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) := by
    by_cases hzero : oneCount = 0
    · simp [hzero]
    · have hone : 1 ≤ oneCount := Nat.one_le_iff_ne_zero.mpr hzero
      have hone_real : (1 : ℝ) ≤ (oneCount : ℝ) := by
        exact_mod_cast hone
      positivity
  have hzero_diagonal :
      0 ≤ ((parentCount : ℝ) - (oneCount : ℝ)) *
        ((parentCount : ℝ) - (oneCount : ℝ) - 1) := by
    by_cases hfull : oneCount = parentCount
    · simp [hfull]
    · have hstrict : oneCount < parentCount :=
        lt_of_le_of_ne hones hfull
      have hsucc : oneCount + 1 ≤ parentCount := by omega
      have hsucc_real :
          (oneCount : ℝ) + 1 ≤ (parentCount : ℝ) := by
        exact_mod_cast hsucc
      have hfactor :
          0 ≤ (parentCount : ℝ) - (oneCount : ℝ) - 1 := by
        linarith
      exact mul_nonneg hzero_nonneg hfactor
  cases left <;> cases right
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hzero_diagonal hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hzero_nonneg hone_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg (mul_nonneg hone_nonneg hzero_nonneg) hdenominator
  · simpa [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount] using
        div_nonneg hone_diagonal hdenominator

theorem withoutReplacementBinaryPairMass_sum
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount) :
    (∑ left : Bool, ∑ right : Bool,
      withoutReplacementBinaryPairMass parentCount oneCount left right) = 1 := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

noncomputable def withoutReplacementBinaryPairExpectation
    (parentCount oneCount : ℕ) (f : Bool → Bool → ℝ) : ℝ :=
  ∑ left : Bool, ∑ right : Bool,
    withoutReplacementBinaryPairMass parentCount oneCount left right *
      f left right

theorem withoutReplacementBinaryPairExpectation_sub
    (parentCount oneCount : ℕ) (hparents : 2 ≤ parentCount)
    (f : Bool → Bool → ℝ) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right) =
      (((oneCount : ℝ) / (parentCount : ℝ)) *
        (1 - (oneCount : ℝ) / (parentCount : ℝ)) /
          ((parentCount : ℝ) - 1)) *
        (f false true + f true false - f false false - f true true) := by
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  simp [withoutReplacementBinaryPairExpectation, Fintype.univ_bool,
    withoutReplacementBinaryPairMass, empiricalBinaryOutcomeCount,
    independentBinaryPairMass, binaryCoinMass]
  field_simp [hparent_real.ne', hparent_minus.ne']
  ring

theorem withoutReplacementBinaryPairExpectation_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by
  let q : ℝ := (oneCount : ℝ) / (parentCount : ℝ)
  have hparent_real : (0 : ℝ) < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  have hqzero : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqone : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hparent_real).mpr
    exact_mod_cast hones
  have hvariance : q * (1 - q) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (q - 1 / 2)]
  have hscaledvariance :=
    mul_le_mul_of_nonneg_right hvariance hparent_real.le
  have hdelta_nonneg : 0 ≤ q * (1 - q) / ((parentCount : ℝ) - 1) := by
    exact div_nonneg
      (mul_nonneg hqzero (sub_nonneg.mpr hqone))
      hparent_minus.le
  have hdelta_bound :
      2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) ≤
        1 / (parentCount : ℝ) := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    rw [show 2 * (q * (1 - q) / ((parentCount : ℝ) - 1)) =
      (2 * (q * (1 - q))) / ((parentCount : ℝ) - 1) by ring]
    apply (div_le_div_iff₀ hparent_minus hparent_real).mpr
    nlinarith
  have hbracket :
      |f false true + f true false - f false false - f true true| ≤
        (2 : ℝ) := by
    rw [abs_le]
    have h₀₀ := hf false false
    have h₀₁ := hf false true
    have h₁₀ := hf true false
    have h₁₁ := hf true true
    constructor <;> linarith
  rw [withoutReplacementBinaryPairExpectation_sub
    parentCount oneCount hparents f, abs_mul]
  change
    |q * (1 - q) / ((parentCount : ℝ) - 1)| *
        |f false true + f true false - f false false - f true true| ≤
      1 / (parentCount : ℝ)
  rw [abs_of_nonneg hdelta_nonneg]
  calc
    (q * (1 - q) / ((parentCount : ℝ) - 1)) *
        |f false true + f true false - f false false - f true true| ≤
      (q * (1 - q) / ((parentCount : ℝ) - 1)) * 2 :=
        mul_le_mul_of_nonneg_left hbracket hdelta_nonneg
    _ ≤ 1 / (parentCount : ℝ) := by
      nlinarith

theorem withoutReplacementBinaryPairExpectation_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right) :
    0 ≤ withoutReplacementBinaryPairExpectation parentCount oneCount f := by
  unfold withoutReplacementBinaryPairExpectation
  apply Finset.sum_nonneg
  intro left _
  apply Finset.sum_nonneg
  intro right _
  exact mul_nonneg
    (withoutReplacementBinaryPairMass_nonneg
      parentCount oneCount hparents hones left right)
    (hf left right)

theorem withoutReplacementBinaryPairExpectation_le_one
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, f left right ≤ 1) :
    withoutReplacementBinaryPairExpectation parentCount oneCount f ≤ 1 := by
  unfold withoutReplacementBinaryPairExpectation
  calc
    (∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right *
          f left right) ≤
      ∑ left : Bool, ∑ right : Bool,
        withoutReplacementBinaryPairMass parentCount oneCount left right * 1 := by
          apply Finset.sum_le_sum
          intro left _
          apply Finset.sum_le_sum
          intro right _
          exact mul_le_mul_of_nonneg_left (hf left right)
            (withoutReplacementBinaryPairMass_nonneg
              parentCount oneCount hparents hones left right)
    _ = 1 := by
      simpa using
        withoutReplacementBinaryPairMass_sum parentCount oneCount hparents

noncomputable def empiricalChildMarginal
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    kernel.childProbability

noncomputable def empiricalConditionalEntropy
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right => binaryEntropy (kernel.childProbability left right))

noncomputable def empiricalAverageDisagreement
    (parentCount oneCount : ℕ) (kernel : BinaryPairKernel) : ℝ :=
  withoutReplacementBinaryPairExpectation parentCount oneCount
    (fun left right =>
      (BinaryPairKernel.bitDisagreementProbability left
          (kernel.childProbability left right) +
        BinaryPairKernel.bitDisagreementProbability right
          (kernel.childProbability left right)) / 2)

theorem empiricalChildMarginal_mem_Icc
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel) :
    0 ≤ empiricalChildMarginal parentCount oneCount kernel ∧
      empiricalChildMarginal parentCount oneCount kernel ≤ 1 := by
  constructor
  · exact withoutReplacementBinaryPairExpectation_nonneg
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_nonneg
  · exact withoutReplacementBinaryPairExpectation_le_one
      parentCount oneCount hparents hones kernel.childProbability
      kernel.childProbability_le_one

theorem empiricalChildMarginal_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    kernel.childProbability
    (fun left right =>
      ⟨kernel.childProbability_nonneg left right,
        kernel.childProbability_le_one left right⟩)
  rw [← hparameter] at herror
  simpa [empiricalChildMarginal, BinaryPairKernel.childMarginal] using herror

theorem empiricalConditionalEntropy_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalConditionalEntropy parentCount oneCount kernel -
      kernel.conditionalEntropy| ≤ 1 / (parentCount : ℝ) := by
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones
    (fun left right => binaryEntropy (kernel.childProbability left right))
    (fun left right =>
      ⟨binaryEntropy_nonneg
        (kernel.childProbability_nonneg left right)
        (kernel.childProbability_le_one left right),
        binaryEntropy_le_one (kernel.childProbability left right)⟩)
  rw [← hparameter] at herror
  simpa [empiricalConditionalEntropy,
    BinaryPairKernel.conditionalEntropy] using herror

theorem empiricalAverageDisagreement_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |empiricalAverageDisagreement parentCount oneCount kernel -
      kernel.averageDisagreement| ≤ 1 / (parentCount : ℝ) := by
  let observable : Bool → Bool → ℝ := fun left right =>
    (BinaryPairKernel.bitDisagreementProbability left
        (kernel.childProbability left right) +
      BinaryPairKernel.bitDisagreementProbability right
        (kernel.childProbability left right)) / 2
  have hobservable (left right : Bool) :
      0 ≤ observable left right ∧ observable left right ≤ 1 := by
    have hleft := BinaryPairKernel.bitDisagreementProbability_mem_Icc left
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    have hright := BinaryPairKernel.bitDisagreementProbability_mem_Icc right
      (kernel.childProbability left right)
      (kernel.childProbability_nonneg left right)
      (kernel.childProbability_le_one left right)
    dsimp [observable]
    constructor <;> linarith
  have herror := withoutReplacementBinaryPairExpectation_error
    parentCount oneCount hparents hones observable hobservable
  rw [← hparameter] at herror
  simpa [empiricalAverageDisagreement,
    BinaryPairKernel.averageDisagreement, observable] using herror

noncomputable def empiricalEntropyError (layerSize : ℕ) : ℝ :=
  (1 + entropySlope) / (layerSize : ℝ) +
    binaryEntropy (1 / (layerSize : ℝ)) / 2

theorem empiricalChildMarginal_entropy_error
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    |binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
      binaryEntropy kernel.childMarginal| ≤
        binaryEntropy (1 / (parentCount : ℝ)) := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hempirical := empiricalChildMarginal_mem_Icc
    parentCount oneCount hparents_two hones kernel
  have hchild :
      0 ≤ kernel.childMarginal ∧ kernel.childMarginal ≤ 1 :=
    ⟨BinaryPairKernel.childMarginal_nonneg kernel,
      BinaryPairKernel.childMarginal_le_one kernel⟩
  have hcoupling := empiricalChildMarginal_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmodulus := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    (empiricalChildMarginal parentCount oneCount kernel)
    kernel.childMarginal hempirical.1 hempirical.2 hchild.1 hchild.2
  have hparents_real : (4 : ℝ) ≤ (parentCount : ℝ) := by
    exact_mod_cast hparents
  have hparents_pos : (0 : ℝ) < (parentCount : ℝ) := by
    linarith
  have hhalf : 1 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    apply (div_le_iff₀ hparents_pos).mpr
    norm_num
    linarith
  have hmonotone := binaryEntropy_mono_on_half
    |empiricalChildMarginal parentCount oneCount kernel -
      kernel.childMarginal|
    (1 / (parentCount : ℝ))
    (abs_nonneg _) hcoupling hhalf
  exact hmodulus.trans hmonotone

theorem empiricalConditionalEntropy_bound
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      entropyConstant + entropySlope *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
  have hparents_two : 2 ≤ parentCount := by omega
  have hconditional := empiricalConditionalEntropy_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hdisagreement := empiricalAverageDisagreement_error
    parentCount oneCount hparents_two hones kernel hparameter
  have hmarginal := empiricalChildMarginal_entropy_error
    parentCount oneCount hparents hones kernel hparameter
  have hindependent := BinaryPairKernel.conditionalEntropy_bound kernel
  have hconditional_upper :
      empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hconditional).2
    linarith
  have hdisagreement_upper :
      kernel.averageDisagreement ≤
        empiricalAverageDisagreement parentCount oneCount kernel +
          1 / (parentCount : ℝ) := by
    have h := (abs_le.mp hdisagreement).1
    linarith
  have hdisagreement_scaled := mul_le_mul_of_nonneg_left
    hdisagreement_upper entropySlope_pos.le
  have hmarginal_upper :
      binaryEntropy kernel.childMarginal ≤
        binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) +
          binaryEntropy (1 / (parentCount : ℝ)) := by
    have h := (abs_le.mp hmarginal).1
    linarith
  have herror :
      1 / (parentCount : ℝ) +
          entropySlope * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2 =
        empiricalEntropyError parentCount := by
    unfold empiricalEntropyError
    ring
  calc
    empiricalConditionalEntropy parentCount oneCount kernel ≤
        kernel.conditionalEntropy + 1 / (parentCount : ℝ) :=
      hconditional_upper
    _ ≤ entropyConstant + entropySlope *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        (1 / (parentCount : ℝ) +
          entropySlope * (1 / (parentCount : ℝ)) +
          binaryEntropy (1 / (parentCount : ℝ)) / 2) := by
      nlinarith
    _ = entropyConstant + entropySlope *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by
      rw [herror]

theorem empiricalEntropyError_tendsto_zero :
    Filter.Tendsto empiricalEntropyError Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun L : ℕ => 1 / (L : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hfirst :
      Filter.Tendsto
        (fun L : ℕ => (1 + entropySlope) / (L : ℝ))
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _ : ℕ => 1 + entropySlope)
          Filter.atTop (nhds (1 + entropySlope)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using hconst.mul hinv
  have hentropy :
      Filter.Tendsto
        (fun L : ℕ => binaryEntropy (1 / (L : ℝ)))
        Filter.atTop (nhds 0) := by
    have hcontinuous := binaryEntropy_continuous.continuousAt.tendsto.comp hinv
    rw [binaryEntropy_zero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with L
    rfl
  change Filter.Tendsto
    (fun L : ℕ => (1 + entropySlope) / (L : ℝ) +
      binaryEntropy (1 / (L : ℝ)) / 2)
    Filter.atTop (nhds 0)
  simpa using hfirst.add (hentropy.div_const 2)


theorem empiricalConditionalEntropy_at_radius
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter : kernel.parentProbability = (oneCount : ℝ) / parentCount)
    (hradius : empiricalAverageDisagreement parentCount oneCount kernel ≤ Erdos566.tau) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      Erdos566.entropyThreshold +
        (binaryEntropy (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 + empiricalEntropyError parentCount := by
  have hbound := empiricalConditionalEntropy_bound parentCount oneCount
    hparents hones kernel hparameter
  have hscaled := mul_le_mul_of_nonneg_left hradius entropySlope_pos.le
  have hconstant := entropyConstant_add_radius
  linarith

theorem eventually_empiricalEntropyError_lt_slack :
    ∀ᶠ L : ℕ in atTop, empiricalEntropyError L < Erdos566.entropySlack := by
  have hneighborhood : ∀ᶠ x : ℝ in nhds 0, x < Erdos566.entropySlack :=
    eventually_lt_nhds (show (0 : ℝ) < Erdos566.entropySlack by
      norm_num [Erdos566.entropySlack])
  exact empiricalEntropyError_tendsto_zero.eventually hneighborhood

theorem binEntropy_upper {x : ℝ} (hx : 0 < x) (hxone : x < 1) :
    Real.binEntropy x ≤ -x * Real.log x + x := by
  have hc : 0 < 1 - x := sub_pos.mpr hxone
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hc)
  rw [Real.log_inv] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hc.le
  have hid : (1 - x) * ((1 - x)⁻¹ - 1) = x := by
    field_simp
    ring
  rw [hid] at hscaled
  simp only [Real.binEntropy, Real.log_inv]
  nlinarith only [hscaled]

theorem entropySlope_lt_one : entropySlope < 1 := by
  have hpositive : 0 < Real.log (9 / 8 : ℝ) := Real.log_pos (by norm_num)
  have hidentity : Real.log (9 / 8 : ℝ) = Real.log 2 + Real.log (9 / 16) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (9 / 16 : ℝ) ≠ 0)]
    congr 1
    norm_num
  rw [hidentity] at hpositive
  unfold entropySlope
  apply (div_lt_one log_two_pos).mpr
  linarith

theorem base_entropy_small :
    binaryEntropy (1 / (Erdos566.baseSize : ℝ)) < 26 / (Erdos566.baseSize : ℝ) := by
  have hbound := binEntropy_upper
    (x := 1 / (Erdos566.baseSize : ℝ))
    (by norm_num [Erdos566.baseSize]) (by norm_num [Erdos566.baseSize])
  have hlog := Real.log_lt_log (show (0 : ℝ) < Erdos566.baseSize by
    norm_num [Erdos566.baseSize])
    (show (Erdos566.baseSize : ℝ) < (2 : ℝ) ^ 24 by norm_num [Erdos566.baseSize])
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have htwo := Erdos566.log_two_bounds.1
  have hlogrecip : Real.log (1 / (Erdos566.baseSize : ℝ)) =
      -Real.log (Erdos566.baseSize : ℝ) := by simp
  rw [hlogrecip] at hbound
  unfold binaryEntropy
  apply (div_lt_iff₀ log_two_pos).mpr
  norm_num [Erdos566.baseSize] at hbound hlog ⊢
  linarith

theorem base_empiricalEntropyError_lt_slack :
    empiricalEntropyError Erdos566.baseSize < Erdos566.entropySlack := by
  have hslope := entropySlope_lt_one
  have hentropy := base_entropy_small
  unfold empiricalEntropyError
  norm_num [Erdos566.baseSize, Erdos566.entropySlack] at hentropy ⊢
  linarith

theorem empiricalEntropyError_lt_slack (L : ℕ) (hL : Erdos566.baseSize ≤ L) :
    empiricalEntropyError L < Erdos566.entropySlack := by
  have hreal : (Erdos566.baseSize : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hbasepos : (0 : ℝ) < Erdos566.baseSize := by norm_num [Erdos566.baseSize]
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le hbasepos hreal
  have hreciprocal : 1 / (L : ℝ) ≤ 1 / (Erdos566.baseSize : ℝ) :=
    one_div_le_one_div_of_le hbasepos hreal
  have hentropy := binaryEntropy_mono_on_half
    (1 / (L : ℝ)) (1 / (Erdos566.baseSize : ℝ))
    (by positivity) hreciprocal (by norm_num [Erdos566.baseSize])
  have hscaled := mul_le_mul_of_nonneg_left hreciprocal
    (show 0 ≤ 1 + entropySlope by linarith [entropySlope_pos])
  have hbase := base_empiricalEntropyError_lt_slack
  unfold empiricalEntropyError at hbase ⊢
  have hid (x : ℝ) : (1 + entropySlope) / x = (1 + entropySlope) * (1 / x) := by ring
  rw [hid] at hbase ⊢
  linarith

end Erdos566.Retuned

namespace Erdos566.Krawtchouk

noncomputable section

/-- The monic three-term recurrence. Its index `j` gives the coefficient
between degrees `j + 1` and `j + 2`. -/
def recurrence (coefficient : ℕ → ℝ) (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | j + 2 => x * recurrence coefficient x (j + 1) -
      coefficient j * recurrence coefficient x j

theorem recurrence_positive_above_cap (coefficient : ℕ → ℝ)
    (x c : ℝ) (k : ℕ) (hc : 0 < c) (hx : 2 * c ≤ x)
    (hcoefficient : ∀ j, j + 2 ≤ k → coefficient j ≤ c ^ 2) :
    ∀ m ≤ k, 0 < recurrence coefficient x m := by
  have growth : ∀ m, m + 1 ≤ k →
      0 < recurrence coefficient x m ∧
        c * recurrence coefficient x m ≤ recurrence coefficient x (m + 1) := by
    intro m
    induction m with
    | zero =>
        intro hm
        simp only [recurrence]
        constructor
        · norm_num
        · linarith
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hcurrent : 0 < recurrence coefficient x (m + 1) := by
          exact lt_of_lt_of_le (mul_pos hc hprev.1) hprev.2
        refine ⟨hcurrent, ?_⟩
        change c * recurrence coefficient x (m + 1) ≤
          x * recurrence coefficient x (m + 1) -
            coefficient m * recurrence coefficient x m
        have hfirst := mul_nonneg (sub_nonneg.mpr hx) hcurrent.le
        have hsecond := mul_nonneg hc.le (sub_nonneg.mpr hprev.2)
        have hthird := mul_nonneg
          (sub_nonneg.mpr (hcoefficient m (by omega))) hprev.1.le
        nlinarith only [hfirst, hsecond, hthird]
  intro m hm
  cases m with
  | zero => norm_num [recurrence]
  | succ m =>
      have h := growth m hm
      exact lt_of_lt_of_le (mul_pos hc h.1) h.2

/-- This normalization gives `k!` times the usual degree-`k` Krawtchouk
polynomial at `v`, with the variable `x = n - 2*v`. -/
def monic (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  recurrence (fun j => ((j : ℝ) + 1) * ((n : ℝ) - j)) x k

theorem coefficient_le_cap (n k j : ℕ)
    (hk : 2 * k ≤ n + 1) (hj : j + 1 ≤ k) :
    ((j : ℝ) + 1) * ((n : ℝ) - j) ≤
      (k : ℝ) * ((n : ℝ) - k + 1) := by
  have hkR : 2 * (k : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hk
  have hjR : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hj
  have hfirst : 0 ≤ (k : ℝ) - j - 1 := by linarith
  have hsecond : 0 ≤ (n : ℝ) - k - j := by linarith
  nlinarith only [mul_nonneg hfirst hsecond]

theorem monic_positive (n k : ℕ) (x : ℝ)
    (hkpos : 0 < k) (hk : 2 * k ≤ n + 1)
    (hx : 2 * Real.sqrt ((k : ℝ) * ((n : ℝ) - k + 1)) ≤ x) :
    0 < monic n x k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hnR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show k ≤ n by omega)
  have hcap : 0 < (k : ℝ) * ((n : ℝ) - k + 1) := by positivity
  apply recurrence_positive_above_cap
    (fun j => ((j : ℝ) + 1) * ((n : ℝ) - j)) x
    (Real.sqrt ((k : ℝ) * ((n : ℝ) - k + 1))) k
    (Real.sqrt_pos.mpr hcap) hx ?_ k le_rfl
  intro j hj
  rw [Real.sq_sqrt hcap.le]
  exact coefficient_le_cap n k j hk (by omega)

theorem recurrence_neg (coefficient : ℕ → ℝ) (x : ℝ) (k : ℕ) :
    recurrence coefficient (-x) k = (-1 : ℝ) ^ k * recurrence coefficient x k := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [recurrence]
  | one => norm_num [recurrence]
  | more k ih0 ih1 =>
      simp only [recurrence, ih0, ih1]
      rw [show k + 2 = (k + 1) + 1 by omega]
      simp only [pow_succ]
      ring

theorem monic_neg (n k : ℕ) (x : ℝ) :
    monic n (-x) k = (-1 : ℝ) ^ k * monic n x k :=
  recurrence_neg _ x k

theorem negative_implies_inside (n k : ℕ) (x : ℝ)
    (hkpos : 0 < k) (hk : 2 * k ≤ n + 1) (heven : Even k)
    (hnegative : monic n x k < 0) :
    |x| < 2 * Real.sqrt ((k : ℝ) * ((n : ℝ) - k + 1)) := by
  apply lt_of_not_ge
  intro houtside
  rcases le_abs.mp houtside with hright | hleft
  · exact (not_lt_of_ge (monic_positive n k x hkpos hk hright).le) hnegative
  · have hpositive := monic_positive n k (-x) hkpos hk (by linarith)
    rw [monic_neg, heven.neg_one_pow, one_mul] at hpositive
    linarith

end

end Erdos566.Krawtchouk

/-
The exact finite-profile counting argument from OpenAI et al.,
CompactnessAndDegeneracy.lean, blob 0e973d50014e8c800af597ef699ef29b81e42fc6.
Licensed under the accompanying LICENSE-OpenAI. The entropy estimate is
retuned through the proved constants in EmpiricalEntropy.lean.
-/

open Finset Filter
open scoped Topology

namespace Erdos566.Retuned

noncomputable def binomialProbabilityMass
    (trialCount successCount : ℕ) (probability : ℝ) : ℝ :=
  (trialCount.choose successCount : ℝ) *
    probability ^ successCount *
    (1 - probability) ^ (trialCount - successCount)

theorem binomialProbabilityMass_nonneg
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity

theorem binomialProbabilityMass_succ_mul
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by
  have hc :
      ((trialCount.choose (successCount + 1) : ℕ) : ℝ) *
          ((successCount + 1 : ℕ) : ℝ) =
        ((trialCount.choose successCount : ℕ) : ℝ) *
          ((trialCount - successCount : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq trialCount successCount
  have hs : trialCount - successCount =
      (trialCount - (successCount + 1)) + 1 := by omega
  unfold binomialProbabilityMass
  rw [hs] at hc ⊢
  simp only [pow_succ]
  linear_combination
    (probability ^ successCount *
      (1 - probability) ^ (trialCount - (successCount + 1)) *
      probability * (1 - probability)) * hc

theorem binomialModeRatio_le_of_lt
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith

theorem binomialModeRatio_le_of_ge
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith

theorem binomialProbabilityMass_le_succ_of_lt_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : successCount < mode) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_lt
    trialCount mode successCount hmode.le hcount
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    (show successCount < trialCount by omega)
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hmass
    _ = binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]

theorem binomialProbabilityMass_succ_le_of_ge_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_ge
    trialCount mode successCount htrials hmode.le hcount hsuccess
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ)) hsuccess
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) =
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]
    _ ≤ binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hmass

theorem binomialProbabilityMass_le_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  by_cases htrials : trialCount = 0
  · subst trialCount
    have hmode_zero : mode = 0 := by omega
    have hsuccess_zero : successCount = 0 := by omega
    subst mode
    subst successCount
    exact le_rfl
  by_cases hmode_zero : mode = 0
  · subst mode
    by_cases hsuccess_zero : successCount = 0
    · subst successCount
      exact le_rfl
    · simp [binomialProbabilityMass, hsuccess_zero]
  by_cases hmode_full : mode = trialCount
  · subst mode
    have htrials_real : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast htrials
    rw [div_self htrials_real]
    by_cases hsuccess_full : successCount = trialCount
    · subst successCount
      exact le_rfl
    · have hpositive : 0 < trialCount - successCount := by omega
      simp [binomialProbabilityMass, hpositive.ne']
  have hmode_lt : mode < trialCount := by omega
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hstep_up (index : ℕ) (hindex : index < mode) :
      binomialProbabilityMass trialCount index probability ≤
        binomialProbabilityMass trialCount (index + 1) probability := by
    exact binomialProbabilityMass_le_succ_of_lt_mode
      trialCount mode index hmode_lt hindex
  have hstep_down (index : ℕ)
      (hindex_mode : mode ≤ index)
      (hindex_trials : index < trialCount) :
      binomialProbabilityMass trialCount (index + 1) probability ≤
        binomialProbabilityMass trialCount index probability := by
    exact binomialProbabilityMass_succ_le_of_ge_mode
      trialCount mode index hmode_lt hindex_mode hindex_trials
  by_cases hbelow : successCount ≤ mode
  · have hwalk (index : ℕ) (hindex : successCount ≤ index) :
        index ≤ mode →
          binomialProbabilityMass trialCount successCount probability ≤
            binomialProbabilityMass trialCount index probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hinduction (by omega)).trans
          (hstep_up index (by omega))
    exact hwalk mode hbelow (le_refl mode)
  · have habove : mode ≤ successCount := by omega
    have hwalk (index : ℕ) (hindex : mode ≤ index) :
        index ≤ trialCount →
          binomialProbabilityMass trialCount index probability ≤
            binomialProbabilityMass trialCount mode probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hstep_down index hindex (by omega)).trans
          (hinduction (by omega))
    exact hwalk successCount habove hsuccess

theorem binomialProbabilityMass_sum_eq_one
    (trialCount : ℕ) (probability : ℝ) :
    (∑ successCount ∈ Finset.range (trialCount + 1),
      binomialProbabilityMass trialCount successCount probability) = 1 := by
  unfold binomialProbabilityMass
  calc
    (∑ successCount ∈ Finset.range (trialCount + 1),
      (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount)) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        probability ^ successCount *
          (1 - probability) ^ (trialCount - successCount) *
          (trialCount.choose successCount : ℝ) := by
            apply Finset.sum_congr rfl
            intro successCount _
            ring
    _ = (probability + (1 - probability)) ^ trialCount :=
      (add_pow probability (1 - probability) trialCount).symm
    _ = 1 := by
      rw [show probability + (1 - probability) = 1 by ring]
      simp

theorem binomialProbabilityMass_mode_ge_inverse
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have hdenominator : 0 < ((trialCount + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenominator).mpr
  calc
    (1 : ℝ) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount successCount
          ((mode : ℝ) / (trialCount : ℝ)) :=
      (binomialProbabilityMass_sum_eq_one
        trialCount ((mode : ℝ) / (trialCount : ℝ))).symm
    _ ≤ ∑ _successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) := by
      apply Finset.sum_le_sum
      intro successCount hsuccess
      apply binomialProbabilityMass_le_mode
        trialCount mode successCount hmode
      have hbound := Finset.mem_range.mp hsuccess
      omega
    _ = binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) *
        ((trialCount + 1 : ℕ) : ℝ) := by
      simp [nsmul_eq_mul]
      ring

theorem binomialProbabilityMass_mode_mul_exp_entropy
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by
  by_cases hzero : mode = 0
  · subst mode
    simp [binomialProbabilityMass]
  by_cases hfull : mode = trialCount
  · subst mode
    have htrials : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    simp [binomialProbabilityMass, htrials]
  have hmode_pos : 0 < mode := Nat.pos_of_ne_zero hzero
  have hmode_lt : mode < trialCount :=
    lt_of_le_of_ne hmode hfull
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hprobability : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode_lt
  have hcomplement : 0 < 1 - probability := by
    linarith
  have hproduct :
      0 < probability ^ mode *
        (1 - probability) ^ (trialCount - mode) := by
    positivity
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(mode : ℝ) * Real.log probability -
          ((trialCount - mode : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hmode]
    dsimp [probability]
    field_simp [htrials_real.ne']
    ring
  have hlog :
      Real.log
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode)) +
        (trialCount : ℝ) * Real.binEntropy probability = 0 := by
    rw [Real.log_mul
      (pow_pos hprobability mode).ne'
      (pow_pos hcomplement (trialCount - mode)).ne',
      Real.log_pow, Real.log_pow, hentropy]
    ring
  change
    binomialProbabilityMass trialCount mode probability *
      Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ)
  calc
    binomialProbabilityMass trialCount mode probability *
        Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ) *
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode) *
          Real.exp ((trialCount : ℝ) * Real.binEntropy probability)) := by
        unfold binomialProbabilityMass
        ring
    _ = (trialCount.choose mode : ℝ) *
        Real.exp
          (Real.log
              (probability ^ mode *
                (1 - probability) ^ (trialCount - mode)) +
            (trialCount : ℝ) * Real.binEntropy probability) := by
          rw [Real.exp_add, Real.exp_log hproduct]
    _ = (trialCount.choose mode : ℝ) := by
      rw [hlog]
      simp

theorem exp_binary_entropy_div_le_choose
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by
  have hmode := binomialProbabilityMass_mode_ge_inverse
    trialCount successCount hcount
  have hexponential :
      0 ≤ Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) =
      (1 / ((trialCount + 1 : ℕ) : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) := by
        ring
    _ ≤ binomialProbabilityMass trialCount successCount
          ((successCount : ℝ) / (trialCount : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) :=
      mul_le_mul_of_nonneg_right hmode hexponential
    _ = (trialCount.choose successCount : ℝ) :=
      binomialProbabilityMass_mode_mul_exp_entropy
        trialCount successCount hcount

theorem binomial_probability_term_le_one
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by
  have hcomplement : 0 ≤ 1 - probability :=
    sub_nonneg.mpr hprobability_one
  have hsum :
      (∑ count ∈ Finset.range (trialCount + 1),
        probability ^ count *
          (1 - probability) ^ (trialCount - count) *
          (trialCount.choose count : ℝ)) = 1 := by
    calc
      (∑ count ∈ Finset.range (trialCount + 1),
          probability ^ count *
            (1 - probability) ^ (trialCount - count) *
            (trialCount.choose count : ℝ)) =
          (probability + (1 - probability)) ^ trialCount :=
        (add_pow probability (1 - probability) trialCount).symm
      _ = 1 := by
        rw [show probability + (1 - probability) = 1 by ring]
        simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (trialCount + 1))
    (f := fun count : ℕ =>
      probability ^ count *
        (1 - probability) ^ (trialCount - count) *
        (trialCount.choose count : ℝ))
    (fun count _ => by positivity)
    (show successCount ∈ Finset.range (trialCount + 1) by
      simp; omega)
  rw [hsum] at hterm
  nlinarith

theorem log_choose_le_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.log (trialCount.choose successCount : ℝ) ≤
      (trialCount : ℝ) *
        Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ)) := by
  by_cases hzero : successCount = 0
  · subst successCount
    simp
  by_cases hfull : successCount = trialCount
  · subst successCount
    by_cases htrials : trialCount = 0
    · simp [htrials]
    · have htrials_real : (trialCount : ℝ) ≠ 0 := by
        exact_mod_cast htrials
      simp [htrials_real]
  have hsuccess : 0 < successCount := Nat.pos_of_ne_zero hzero
  have hstrict : successCount < trialCount :=
    lt_of_le_of_ne hcount hfull
  have htrials : 0 < trialCount :=
    lt_of_lt_of_le hsuccess hcount
  let probability : ℝ :=
    (successCount : ℝ) / (trialCount : ℝ)
  have hprobability_pos : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_lt_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one (by exact_mod_cast htrials)).mpr
    exact_mod_cast hstrict
  have hcomplement : 0 < 1 - probability :=
    sub_pos.mpr hprobability_lt_one
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  have hmass := binomial_probability_term_le_one
    trialCount successCount probability hcount
    hprobability_pos.le hprobability_lt_one.le
  have hproduct :
      0 < (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) := by
    positivity
  have hlogmass := Real.log_le_log hproduct hmass
  simp only [Real.log_one] at hlogmass
  rw [Real.log_mul
      (mul_pos hchoose (pow_pos hprobability_pos _)).ne'
      (pow_pos hcomplement _).ne',
    Real.log_mul hchoose.ne' (pow_pos hprobability_pos _).ne',
    Real.log_pow, Real.log_pow] at hlogmass
  have htrials_real : (trialCount : ℝ) ≠ 0 := by
    exact_mod_cast htrials.ne'
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(successCount : ℝ) * Real.log probability -
          ((trialCount - successCount : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hcount]
    dsimp [probability]
    field_simp [htrials_real]
    ring
  change Real.log (trialCount.choose successCount : ℝ) ≤
    (trialCount : ℝ) * Real.binEntropy probability
  rw [hentropy]
  linarith

theorem choose_le_exp_binary_entropy
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    (trialCount.choose successCount : ℝ) ≤
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ))) := by
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  exact (Real.log_le_iff_le_exp hchoose).mp
    (log_choose_le_binary_entropy trialCount successCount hcount)

theorem choose_product_le_exp_binary_entropy
    {ι : Type*} [Fintype ι]
    (population success : ι → ℕ)
    (hcount : ∀ index, success index ≤ population index) :
    (∏ index : ι,
      (population index).choose (success index) : ℝ) ≤
      Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
  calc
    (∏ index : ι,
        (population index).choose (success index) : ℝ) ≤
      ∏ index : ι,
        Real.exp
          ((population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
        apply Finset.prod_le_prod₀
        · intro index _
          positivity
        · intro index _
          exact choose_le_exp_binary_entropy
            (population index) (success index) (hcount index)
    _ = Real.exp
        (∑ index : ι,
          (population index : ℝ) *
            Real.binEntropy
              ((success index : ℝ) / (population index : ℝ))) := by
      rw [Real.exp_sum]



abbrev HammingWord (dimension : ℕ) := Fin dimension → Bool

noncomputable def booleanWordOnes {ι : Type*} [Fintype ι]
    (word : ι → Bool) : Finset ι := by
  classical
  exact Finset.univ.filter (fun index => word index = true)

theorem booleanWordOnes_card_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (equivalence : ι ≃ κ)
    (word : κ → Bool) :
    (booleanWordOnes (fun index : ι => word (equivalence index))).card =
      (booleanWordOnes word).card := by
  classical
  apply Finset.card_bij
    (fun index _ => equivalence index)
  · intro index hindex
    have hone := (Finset.mem_filter.mp hindex).2
    unfold booleanWordOnes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hone⟩
  · intro first _ second _ hequal
    exact equivalence.injective hequal
  · intro index hindex
    refine ⟨equivalence.symm index, ?_, equivalence.apply_symm_apply index⟩
    unfold booleanWordOnes
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hone := (Finset.mem_filter.mp hindex).2
    simpa using hone

noncomputable def booleanWordsOfWeight (ι : Type*) [Fintype ι]
    (weight : ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => (booleanWordOnes word).card = weight)

noncomputable def booleanWordsOfWeightEquiv
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    ↥(booleanWordsOfWeight ι weight) ≃
      ↥((Finset.univ : Finset ι).powersetCard weight) := by
  classical
  refine
    { toFun := fun word => ⟨booleanWordOnes word.val, ?_⟩
      invFun := fun support =>
        ⟨fun index => decide (index ∈ support.val), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    have hword :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              (booleanWordOnes candidate).card = weight)) := by
      simpa only [booleanWordsOfWeight] using word.property
    exact (Finset.mem_filter.mp hword).2
  · have hsupport :=
      (Finset.mem_powersetCard.mp support.property).2
    have hones :
        booleanWordOnes
          (fun index : ι => decide (index ∈ support.val)) = support.val := by
      ext index
      simp [booleanWordOnes]
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hones]
    exact hsupport
  · intro word
    apply Subtype.ext
    funext index
    cases hbit : word.val index <;>
      simp [booleanWordOnes, hbit]
  · intro support
    apply Subtype.ext
    ext index
    simp [booleanWordOnes]

theorem booleanWordsOfWeight_card
    (ι : Type*) [Fintype ι] (weight : ℕ) :
    (booleanWordsOfWeight ι weight).card =
      (Fintype.card ι).choose weight := by
  calc
    (booleanWordsOfWeight ι weight).card =
        Fintype.card ↥(booleanWordsOfWeight ι weight) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥((Finset.univ : Finset ι).powersetCard weight) :=
      Fintype.card_congr (booleanWordsOfWeightEquiv ι weight)
    _ = ((Finset.univ : Finset ι).powersetCard weight).card :=
      Fintype.card_coe _
    _ = (Fintype.card ι).choose weight := by
      simp

abbrev ClassificationFiber
    {ι γ : Type*} (classify : ι → γ) (group : γ) :=
  {index : ι // classify index = group}

noncomputable def classificationGroup
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) : Finset ι :=
  Finset.univ.filter (fun index => classify index = group)

noncomputable def classifiedWordOnes
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) : Finset ι :=
  (classificationGroup classify group).filter
    (fun index => word index = true)

noncomputable def classifiedWordSupportEquiv
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    ↥(booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)) ≃
      ↥(classifiedWordOnes classify group word) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.val, ?_⟩
      invFun := fun index => ⟨⟨index.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hbit : word index.val.val = true := by
      have hmembership :
          index.val ∈
            (Finset.univ.filter
              (fun candidate : ClassificationFiber classify group =>
                word candidate.val = true)) := by
        simpa only [booleanWordOnes] using index.property
      exact (Finset.mem_filter.mp hmembership).2
    simp [classifiedWordOnes, classificationGroup,
      index.val.property, hbit]
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hgroup := (Finset.mem_filter.mp hmembership).1
    exact (Finset.mem_filter.mp hgroup).2
  · have hmembership :
        index.val ∈
          (classificationGroup classify group).filter
            (fun candidate => word candidate = true) := by
      simpa only [classifiedWordOnes] using index.property
    have hbit := (Finset.mem_filter.mp hmembership).2
    simp [booleanWordOnes, hbit]
  · intro index
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro index
    apply Subtype.ext
    rfl

theorem classifiedWordOnes_card
    {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (classify : ι → γ) (group : γ) (word : ι → Bool) :
    (classifiedWordOnes classify group word).card =
      (booleanWordOnes
        (fun index : ClassificationFiber classify group => word index.val)).card := by
  calc
    (classifiedWordOnes classify group word).card =
        Fintype.card ↥(classifiedWordOnes classify group word) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        ↥(booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)) :=
      Fintype.card_congr
        (classifiedWordSupportEquiv classify group word).symm
    _ = (booleanWordOnes
          (fun index : ClassificationFiber classify group => word index.val)).card :=
      Fintype.card_coe _

noncomputable def classifiedBooleanWords
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter
    (fun word => ∀ group,
      (classifiedWordOnes classify group word).card = counts group)

noncomputable def classifiedBooleanWordsEquiv
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    ↥(classifiedBooleanWords classify counts) ≃
      (∀ group : γ,
        ↥(booleanWordsOfWeight
          (ClassificationFiber classify group) (counts group))) := by
  classical
  refine
    { toFun := fun word group =>
        ⟨fun index => word.val index.val, ?_⟩
      invFun := fun pieces =>
        ⟨fun index => (pieces (classify index)).val ⟨index, rfl⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership :
        word.val ∈
          (Finset.univ.filter
            (fun candidate : ι → Bool =>
              ∀ group,
                (classifiedWordOnes classify group candidate).card =
                  counts group)) := by
      simpa only [classifiedBooleanWords] using word.property
    have hprofile := (Finset.mem_filter.mp hmembership).2 group
    simp only [booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact (classifiedWordOnes_card classify group word.val).symm.trans
      hprofile
  · simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro group
    rw [classifiedWordOnes_card]
    have hrestriction :
        (fun index : ClassificationFiber classify group =>
          (pieces (classify index.val)).val
            ⟨index.val, rfl⟩) =
          (pieces group).val := by
      funext index
      rcases index with ⟨index, hindex⟩
      cases hindex
      rfl
    rw [hrestriction]
    have hmembership := (pieces group).property
    unfold booleanWordsOfWeight at hmembership
    exact (Finset.mem_filter.mp hmembership).2
  · intro word
    apply Subtype.ext
    funext index
    rfl
  · intro pieces
    funext group
    apply Subtype.ext
    funext index
    rcases index with ⟨index, hindex⟩
    cases hindex
    rfl

theorem classifiedBooleanWords_card
    {ι γ : Type*} [Fintype ι] [Fintype γ] [DecidableEq γ]
    (classify : ι → γ) (counts : γ → ℕ) :
    (classifiedBooleanWords classify counts).card =
      ∏ group : γ,
        (Fintype.card (ClassificationFiber classify group)).choose
          (counts group) := by
  calc
    (classifiedBooleanWords classify counts).card =
        Fintype.card ↥(classifiedBooleanWords classify counts) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
        (∀ group : γ,
          ↥(booleanWordsOfWeight
            (ClassificationFiber classify group) (counts group))) :=
      Fintype.card_congr (classifiedBooleanWordsEquiv classify counts)
    _ = ∏ group : γ,
          Fintype.card
            ↥(booleanWordsOfWeight
              (ClassificationFiber classify group) (counts group)) := by
      rw [Fintype.card_pi]
    _ = ∏ group : γ,
          (Fintype.card (ClassificationFiber classify group)).choose
            (counts group) := by
      apply Finset.prod_congr rfl
      intro group _
      rw [Fintype.card_coe,
        booleanWordsOfWeight_card]

abbrev PairBitType := Fin 3

abbrev PairTypeCountProfile (parentCount dimension : ℕ) :=
  PairBitType → Fin dimension → Fin (parentCount.choose 2 + 1)

theorem pairTypeCountProfile_card (parentCount dimension : ℕ) :
    Fintype.card (PairTypeCountProfile parentCount dimension) =
      (parentCount.choose 2 + 1) ^ (3 * dimension) := by
  simp [PairTypeCountProfile, pow_mul, Nat.mul_comm]

noncomputable def pairCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : PairBitType := by
  classical
  exact
    if ∀ parent ∈ pair.val, parents parent coordinate = false then 0
    else if ∀ parent ∈ pair.val, parents parent coordinate = true then 1
    else 2

noncomputable def pairTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun pair => pairCoordinateBitType parents coordinate pair = bitType)

noncomputable def pairCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → PairBitType × Fin dimension :=
  fun index =>
    (pairCoordinateBitType parents index.2 index.1, index.2)

noncomputable def pairCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(pairTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun pair => ⟨(pair.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [pairCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [pairTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [pairCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        pair.val ∈
          (Finset.univ.filter
            (fun candidate : PairLayer parentCount 1 =>
              pairCoordinateBitType parents coordinate candidate = bitType)) := by
      simpa only [pairTypeGroup] using pair.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (pairCoordinateBitType parents coordinate pair.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [pairCoordinateClassification] using hcoordinate.symm
  · intro pair
    apply Subtype.ext
    rfl

theorem pairCoordinateClassificationFiber_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (pairCoordinateClassification parents) (bitType, coordinate)) =
      (pairTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (pairCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(pairTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (pairCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (pairTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem sum_pairTypeGroup_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroup parents coordinate bitType).card) =
      parentCount.choose 2 := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hpairs :
      (Finset.univ : Finset (PairLayer parentCount 1)).card =
        parentCount.choose 2 := by
    rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  calc
    (∑ bitType : PairBitType,
        (pairTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        simpa [pairTypeGroup] using hpartition.symm
    _ = parentCount.choose 2 := hpairs

theorem pairTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 2 := by
  classical
  calc
    (pairTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (PairLayer parentCount 1)).card := by
        unfold pairTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 2 := by
      rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
        pairLayer_card_zero]

noncomputable def pairTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) : Finset (PairLayer parentCount 1) := by
  classical
  exact (pairTypeGroup parents coordinate bitType).filter
    (fun pair => children pair coordinate = true)

theorem pairTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroupChildOnes parents children coordinate bitType).card ≤
      (pairTypeGroup parents coordinate bitType).card := by
  classical
  unfold pairTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenPairChildArray
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem pairChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (pairCoordinateClassification parents) (bitType, coordinate)
      (flattenPairChildArray children)).card =
        (pairTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (pairCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenPairChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [pairCoordinateClassification] using hcoordinate
    simp only [pairTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [pairTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [pairCoordinateClassification, hcoord] using htype
    · simpa [flattenPairChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group :=
        (Finset.mem_filter.mp hfirst).1
      have hsecond_group :=
        (Finset.mem_filter.mp hsecond).1
      have hfirst_class :=
        (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class :=
        (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [pairCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro pair hpair
    refine ⟨(pair, coordinate), ?_, rfl⟩
    have hpair_parts := Finset.mem_filter.mp hpair
    have hpair_type := (Finset.mem_filter.mp hpair_parts.1).2
    change
      (pair, coordinate) ∈
        (classificationGroup (pairCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenPairChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hpair_type rfl
    · exact hpair_parts.2

noncomputable def pairChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine ⟨(pairTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := pairTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := pairTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def pairChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildCountProfile parents children = profile)

noncomputable def pairChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    ↥(pairChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenPairChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun pair coordinate => word.val (pair, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold pairChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [pairChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : PairTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [pairChildCountProfile] using hcount
  · simp only [pairChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (pairTypeGroupChildOnes parents
        (fun pair coordinate => word.val (pair, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← pairChildClassificationOnes_card]
    have hflatten :
        flattenPairChildArray
          (fun pair coordinate => word.val (pair, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨pair, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext pair
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨pair, coordinate⟩
    rfl

theorem pairChildArraysOfProfile_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    (pairChildArraysOfProfile parents profile).card =
      ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (pairChildArraysOfProfile parents profile).card =
      Fintype.card ↥(pairChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (pairChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : PairBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (pairCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (pairCoordinateClassification parents)
          (fun index : PairBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [pairCoordinateClassificationFiber_card]

noncomputable def pairCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : PairBitType,
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      binaryEntropy
        (((pairTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def pairChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    pairCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

noncomputable def pairParentCoordinateOneCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun parent => parents parent coordinate)).card

theorem pairParentCoordinateOneCount_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairParentCoordinateOneCount parents coordinate ≤ parentCount := by
  classical
  unfold pairParentCoordinateOneCount booleanWordOnes
  calc
    (Finset.univ.filter
      (fun parent : Fin parentCount =>
        parents parent coordinate = true)).card ≤
        (Finset.univ : Finset (Fin parentCount)).card :=
      Finset.card_filter_le _ _
    _ = parentCount := by simp

noncomputable def pairParentCoordinateSupport
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) : Finset (Fin parentCount) := by
  classical
  exact Finset.univ.filter
    (fun parent => parents parent coordinate = outcome)

theorem pairParentCoordinateSupport_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by
  rfl

theorem pairParentCoordinateSupport_card_add
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card +
      (pairParentCoordinateSupport parents coordinate true).card =
        parentCount := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin parentCount)))
      (fun parent => parents parent coordinate = false)
  simpa [pairParentCoordinateSupport, Bool.not_eq_false] using hpartition

theorem pairParentCoordinateSupport_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card =
      parentCount - pairParentCoordinateOneCount parents coordinate := by
  have hpartition := pairParentCoordinateSupport_card_add parents coordinate
  rw [pairParentCoordinateSupport_true_card] at hpartition
  omega

theorem pairCoordinateBitType_homogeneous_iff
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool) :
    pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0) ↔
      ∀ parent ∈ pair.val, parents parent coordinate = outcome := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp pair.property
  cases outcome <;> cases ha : parents a coordinate <;>
    cases hb : parents b coordinate <;>
    simp_all [pairCoordinateBitType]

noncomputable def pairTypeGroupHomogeneousEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    ↥(pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)) ≃
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) := by
  classical
  refine
    { toFun := fun pair => ⟨pair.val.val, ?_⟩
      invFun := fun support =>
        ⟨⟨support.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := pair.property
    unfold pairTypeGroup at hmembership
    have htype := (Finset.mem_filter.mp hmembership).2
    have hhomogeneous :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair.val outcome).mp htype
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, pair.val.property⟩
    intro parent hparent
    unfold pairParentCoordinateSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hhomogeneous parent hparent⟩
  · exact (Finset.mem_powersetCard.mp support.property).2
  · unfold pairTypeGroup
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (pairCoordinateBitType_homogeneous_iff
      parents coordinate
      ⟨support.val, (Finset.mem_powersetCard.mp support.property).2⟩
      outcome).mpr
    intro parent hparent
    have hsubset :=
      (Finset.mem_powersetCard.mp support.property).1
    have hsupport := hsubset hparent
    unfold pairParentCoordinateSupport at hsupport
    exact (Finset.mem_filter.mp hsupport).2
  · intro pair
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro support
    apply Subtype.ext
    rfl

theorem pairTypeGroup_homogeneous_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 := by
  calc
    (pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)).card =
      Fintype.card
        ↥(pairTypeGroup parents coordinate
          (if outcome then (1 : PairBitType) else 0)) :=
      (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) :=
      Fintype.card_congr
        (pairTypeGroupHomogeneousEquiv parents coordinate outcome)
    _ = ((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2).card :=
      Fintype.card_coe _
    _ = (pairParentCoordinateSupport parents coordinate outcome).card.choose 2 :=
      Finset.card_powersetCard _ _

theorem pairTypeGroup_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_false_card] using
    pairTypeGroup_homogeneous_card parents coordinate false

theorem pairTypeGroup_true_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 1).card =
      (pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_true_card] using
    pairTypeGroup_homogeneous_card parents coordinate true

theorem pairTypeGroup_mixed_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 2).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate) *
        pairParentCoordinateOneCount parents coordinate := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have htotal :
      (pairTypeGroup parents coordinate 0).card +
        (pairTypeGroup parents coordinate 1).card +
          (pairTypeGroup parents coordinate 2).card =
            parentCount.choose 2 := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      sum_pairTypeGroup_card parents coordinate
  rw [pairTypeGroup_false_card,
    pairTypeGroup_true_card] at htotal
  have htotal_real :
      (((parentCount -
          pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        (((pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) =
          (parentCount.choose 2 : ℝ) := by
    exact_mod_cast htotal
  rw [Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_sub hones] at htotal_real
  have hresult :
      ((pairTypeGroup parents coordinate 2).card : ℝ) =
        (((parentCount -
          pairParentCoordinateOneCount parents coordinate) *
            pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hones]
    nlinarith
  exact_mod_cast hresult

def pairBitTypeOfOutcomes (left right : Bool) : PairBitType :=
  if left = false ∧ right = false then 0
  else if left = true ∧ right = true then 1
  else 2

noncomputable def pairCoordinateKernel
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryPairKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) /
      (parentCount : ℝ)
  parentProbability_nonneg := by
    positivity
  parentProbability_le_one := by
    have hpositive : 0 < (parentCount : ℝ) := by
      exact_mod_cast hparents
    apply (div_le_one hpositive).mpr
    exact_mod_cast pairParentCoordinateOneCount_le parents coordinate
  childProbability left right :=
    ((pairTypeGroupChildOnes parents children coordinate
      (pairBitTypeOfOutcomes left right)).card : ℝ) /
        ((pairTypeGroup parents coordinate
          (pairBitTypeOfOutcomes left right)).card : ℝ)
  childProbability_nonneg := by
    intro left right
    positivity
  childProbability_le_one := by
    intro left right
    let bitType := pairBitTypeOfOutcomes left right
    have hle := pairTypeGroupChildOnes_card_le
      parents children coordinate bitType
    by_cases hzero : (pairTypeGroup parents coordinate bitType).card = 0
    · simp [bitType, hzero]
    · have hpositive :
          0 < ((pairTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_one hpositive).mpr
      exact_mod_cast hle

theorem pairCoordinateKernel_parentProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairCoordinateKernel hparents parents children coordinate).parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := by
  rfl

theorem pairCoordinateKernel_childProbability
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    (pairCoordinateKernel hparents parents children coordinate).childProbability
        left right =
      ((pairTypeGroupChildOnes parents children coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
          ((pairTypeGroup parents coordinate
            (pairBitTypeOfOutcomes left right)).card : ℝ) := by
  rfl

noncomputable def pairChildCoordinateOneCount
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun pair => children pair coordinate)).card

theorem sum_pairTypeGroupChildOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      pairChildCoordinateOneCount children coordinate := by
  classical
  let support : Finset (PairLayer parentCount 1) :=
    booleanWordOnes (fun pair => children pair coordinate)
  have hmaps :
      ((support : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1)).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : PairBitType) :
      support.filter
        (fun pair => pairCoordinateBitType parents coordinate pair = bitType) =
      pairTypeGroupChildOnes parents children coordinate bitType := by
    ext pair
    simp [support, booleanWordOnes,
      pairTypeGroupChildOnes, pairTypeGroup, and_comm]
  calc
    (∑ bitType : PairBitType,
      (pairTypeGroupChildOnes parents children coordinate bitType).card) =
      ∑ bitType : PairBitType,
        (support.filter
          (fun pair =>
            pairCoordinateBitType parents coordinate pair = bitType)).card := by
          apply Finset.sum_congr rfl
          intro bitType _
          rw [hfiber]
    _ = support.card := by
      exact hpartition.symm
    _ = pairChildCoordinateOneCount children coordinate := by
      rfl

theorem pairTypeGroup_probability_mul_childRatio
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (pairTypeGroup parents coordinate bitType).card = 0
  · have hchild :
        (pairTypeGroupChildOnes parents children
          coordinate bitType).card = 0 := by
      have hle := pairTypeGroupChildOnes_card_le
        parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((pairTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp [hpair.ne', hgroup_real]

theorem withoutReplacementBinaryPairMass_eq_pairTypeGroup
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  have hparent : 0 < (parentCount : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hparents
  have hparent_minus : 0 < (parentCount : ℝ) - 1 := by
    have htwo : (2 : ℝ) ≤ (parentCount : ℝ) := by
      exact_mod_cast hparents
    linarith
  cases left <;> cases right <;>
    simp [withoutReplacementBinaryPairMass,
      empiricalBinaryOutcomeCount,
      pairBitTypeOfOutcomes,
      pairTypeGroup_false_card,
      pairTypeGroup_true_card,
      pairTypeGroup_mixed_card,
      Nat.cast_choose_two,
      Nat.cast_sub hones] <;>
    field_simp [hparent.ne', hparent_minus.ne']

theorem pairCoordinateKernel_empiricalConditionalEntropy
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      pairCoordinateConditionalEntropy parents children coordinate := by
  unfold empiricalConditionalEntropy
    withoutReplacementBinaryPairExpectation
  simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
    hparents parents coordinate]
  simp [Fintype.univ_bool,
    pairCoordinateKernel_childProbability,
    pairBitTypeOfOutcomes,
    pairCoordinateConditionalEntropy,
    Fin.sum_univ_succ]
  ring

theorem pairCoordinateKernel_empiricalChildMarginal
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ) := by
  have hgroups :
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
    calc
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
        ∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
              (parentCount.choose 2 : ℝ) := by
          apply Finset.sum_congr rfl
          intro bitType _
          exact pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType
      _ =
        (∑ bitType : PairBitType,
          ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ)) /
            (parentCount.choose 2 : ℝ) := by
          rw [Finset.sum_div]
      _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          congr 1
          exact_mod_cast
            sum_pairTypeGroupChildOnes_card parents children coordinate
  calc
    empiricalChildMarginal parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
      unfold empiricalChildMarginal
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        Fin.sum_univ_succ]
      ring
    _ = (pairChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 2 : ℝ) := hgroups

theorem pairTypeGroup_probability_mul_childComplement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
  calc
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (1 -
        ((pairTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        (((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
            (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) := by
          ring
    _ = ((pairTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by
          rw [pairTypeGroup_probability_mul_childRatio
            hparents parents children coordinate bitType]
    _ = (((pairTypeGroup parents coordinate bitType).card : ℝ) -
        ((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ)) /
          (parentCount.choose 2 : ℝ) := by
          ring

theorem pairCoordinateKernel_empiricalAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
  have hzero := pairTypeGroup_probability_mul_childRatio
    hparents parents children coordinate 0
  have hone := pairTypeGroup_probability_mul_childComplement
    hparents parents children coordinate 1
  calc
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((pairTypeGroup parents coordinate 0).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (((pairTypeGroupChildOnes parents children
          coordinate 0).card : ℝ) /
            ((pairTypeGroup parents coordinate 0).card : ℝ)) +
      ((pairTypeGroup parents coordinate 2).card : ℝ) /
          (parentCount.choose 2 : ℝ) * (1 / 2 : ℝ) +
      ((pairTypeGroup parents coordinate 1).card : ℝ) /
          (parentCount.choose 2 : ℝ) *
        (1 -
          ((pairTypeGroupChildOnes parents children
            coordinate 1).card : ℝ) /
              ((pairTypeGroup parents coordinate 1).card : ℝ)) := by
      unfold empiricalAverageDisagreement
        withoutReplacementBinaryPairExpectation
      simp_rw [withoutReplacementBinaryPairMass_eq_pairTypeGroup
        hparents parents coordinate]
      simp [Fintype.univ_bool,
        pairCoordinateKernel_childProbability,
        pairBitTypeOfOutcomes,
        BinaryPairKernel.bitDisagreementProbability]
      ring
    _ =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by
      rw [hzero, hone]
      ring

noncomputable def pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : ℕ := by
  classical
  exact (pair.val.filter
    (fun parent =>
      parents parent coordinate ≠ children pair coordinate)).card

theorem pairCoordinatePairMismatchCount_homogeneous
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool)
    (hgroup :
      pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0)) :
    pairCoordinatePairMismatchCount parents children coordinate pair =
      if children pair coordinate = outcome then 0 else 2 := by
  classical
  have hhomogeneous :=
    (pairCoordinateBitType_homogeneous_iff
      parents coordinate pair outcome).mp hgroup
  by_cases hchild : children pair coordinate = outcome
  · have hempty :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro parent hmember hdisagree
      exact hdisagree
        ((hhomogeneous parent hmember).trans hchild.symm)
    unfold pairCoordinatePairMismatchCount
    rw [hempty]
    simp [hchild]
  · have hfull :
        pair.val.filter
          (fun parent =>
            parents parent coordinate ≠ children pair coordinate) =
          pair.val := by
      ext parent
      constructor
      · intro hmember
        exact (Finset.mem_filter.mp hmember).1
      · intro hmember
        apply Finset.mem_filter.mpr
        refine ⟨hmember, ?_⟩
        intro hequal
        apply hchild
        exact hequal.symm.trans
          (hhomogeneous parent hmember)
    unfold pairCoordinatePairMismatchCount
    rw [hfull, if_neg hchild]
    exact pair.property

theorem pairCoordinatePairMismatchCount_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (hgroup : pairCoordinateBitType parents coordinate pair = 2) :
    pairCoordinatePairMismatchCount parents children coordinate pair = 1 := by
  classical
  have hnotfalse :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = false := by
    intro hfalse
    have hzero :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair false).mpr hfalse
    rw [hgroup] at hzero
    simp at hzero
  have hnottrue :
      ¬ ∀ parent ∈ pair.val, parents parent coordinate = true := by
    intro htrue
    have hone :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair true).mpr htrue
    rw [hgroup] at hone
    simp at hone
  have hexfalse :
      ∃ parent ∈ pair.val, parents parent coordinate = false := by
    by_contra hnone
    push Not at hnone
    apply hnottrue
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  have hextrue :
      ∃ parent ∈ pair.val, parents parent coordinate = true := by
    by_contra hnone
    push Not at hnone
    apply hnotfalse
    intro parent hparent
    have hbit := hnone parent hparent
    cases hvalue : parents parent coordinate <;>
      simp_all
  obtain ⟨falseParent, hfalseParent, hfalseBit⟩ := hexfalse
  obtain ⟨trueParent, htrueParent, htrueBit⟩ := hextrue
  let mismatches : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
  let agreements : Finset (PairLayer parentCount 0) :=
    pair.val.filter
      (fun parent =>
        ¬ parents parent coordinate ≠ children pair coordinate)
  have hmismatch : mismatches.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨trueParent, ?_⟩
      simp [mismatches, htrueParent, htrueBit, hchild]
    · refine ⟨falseParent, ?_⟩
      simp [mismatches, hfalseParent, hfalseBit, hchild]
  have hagreement : agreements.Nonempty := by
    cases hchild : children pair coordinate
    · refine ⟨falseParent, ?_⟩
      simp [agreements, hfalseParent, hfalseBit, hchild]
    · refine ⟨trueParent, ?_⟩
      simp [agreements, htrueParent, htrueBit, hchild]
  have hpartition : mismatches.card + agreements.card = 2 := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pair.val)
      (fun parent =>
        parents parent coordinate ≠ children pair coordinate)
    change mismatches.card + agreements.card = pair.val.card at hfilter
    simpa [pair.property] using hfilter
  have hmismatch_pos := Finset.card_pos.mpr hmismatch
  have hagreement_pos := Finset.card_pos.mpr hagreement
  change mismatches.card = 1
  omega

theorem pairCoordinatePairMismatchCount_sum_false
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 0,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 0,
        if children pair coordinate = true then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 0)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair false hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * (pairTypeGroupChildOnes parents children coordinate 0).card := by
      rw [← Finset.sum_filter]
      simp [pairTypeGroupChildOnes, Nat.mul_comm]

theorem pairCoordinatePairMismatchCount_sum_true
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  let zeroChildren : Finset (PairLayer parentCount 1) :=
    (pairTypeGroup parents coordinate 1).filter
      (fun pair => children pair coordinate = false)
  have hpartition :
      (pairTypeGroupChildOnes parents children coordinate 1).card +
        zeroChildren.card =
          (pairTypeGroup parents coordinate 1).card := by
    have hfilter := Finset.card_filter_add_card_filter_not
      (s := pairTypeGroup parents coordinate 1)
      (fun pair => children pair coordinate = true)
    simpa [pairTypeGroupChildOnes, zeroChildren] using hfilter
  have hzero_card :
      zeroChildren.card =
        (pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card := by
    omega
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ pair ∈ pairTypeGroup parents coordinate 1,
        if children pair coordinate = false then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 1)) := by
          simpa only [pairTypeGroup] using hpair
        have hgroup := (Finset.mem_filter.mp hmembership).2
        have hterm := pairCoordinatePairMismatchCount_homogeneous
          parents children coordinate pair true hgroup
        cases hchild : children pair coordinate <;>
          simpa [hchild] using hterm
    _ = 2 * zeroChildren.card := by
      rw [← Finset.sum_filter]
      simp [zeroChildren, Nat.mul_comm]
    _ = 2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
      rw [hzero_card]

theorem pairCoordinatePairMismatchCount_sum_mixed
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      (pairTypeGroup parents coordinate 2).card := by
  classical
  calc
    (∑ pair ∈ pairTypeGroup parents coordinate 2,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      ∑ _pair ∈ pairTypeGroup parents coordinate 2, 1 := by
        apply Finset.sum_congr rfl
        intro pair hpair
        have hmembership :
            pair ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 =>
                  pairCoordinateBitType parents coordinate candidate = 2)) := by
          simpa only [pairTypeGroup] using hpair
        exact pairCoordinatePairMismatchCount_mixed
          parents children coordinate pair
            (Finset.mem_filter.mp hmembership).2
    _ = (pairTypeGroup parents coordinate 2).card := by
      simp

theorem sum_pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (PairLayer parentCount 1)) :
        Set (PairLayer parentCount 1))).MapsTo
          (pairCoordinateBitType parents coordinate)
          (Finset.univ : Finset PairBitType) := by
    intro pair _
    exact Finset.mem_univ _
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to hmaps
      (fun pair =>
        pairCoordinatePairMismatchCount
          parents children coordinate pair)).symm
  have hpartition :
      (∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
        (∑ pair ∈ pairTypeGroup parents coordinate 0,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) +
        (∑ pair ∈ pairTypeGroup parents coordinate 2,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) := by
    simpa [pairTypeGroup, Fin.sum_univ_succ, add_assoc] using hfiber
  rw [pairCoordinatePairMismatchCount_sum_false,
    pairCoordinatePairMismatchCount_sum_true,
    pairCoordinatePairMismatchCount_sum_mixed] at hpartition
  omega

theorem sum_pairCoordinatePairMismatchCount_eq_hammingDist
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair) =
      ∑ pair : PairLayer parentCount 1,
        ∑ parent ∈ pair.val,
          hammingDist (parents parent) (children pair) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro pair _
  have hcount (coordinate : Fin dimension) :
      pairCoordinatePairMismatchCount parents children coordinate pair =
        ∑ parent ∈ pair.val,
          if parents parent coordinate ≠ children pair coordinate
            then 1 else 0 := by
    change
      (pair.val.filter
        (fun parent =>
          parents parent coordinate ≠ children pair coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _
  change
    (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children pair coordinate
        then 1 else 0) =
      ((Finset.univ : Finset (Fin dimension)).filter
        (fun coordinate =>
          parents parent coordinate ≠ children pair coordinate)).card
  exact Finset.sum_boole _ _

theorem pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      ((∑ pair : PairLayer parentCount 1,
        pairCoordinatePairMismatchCount
          parents children coordinate pair : ℕ) : ℝ) /
        (2 * (parentCount.choose 2 : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hone := pairTypeGroupChildOnes_card_le
    parents children coordinate 1
  rw [pairCoordinateKernel_empiricalAverageDisagreement
    hparents parents children coordinate,
    sum_pairCoordinatePairMismatchCount]
  push_cast [hone]
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairCoordinateConditionalEntropy parents children coordinate ≤
      entropyConstant +
        entropySlope *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount := by
  have hones := pairParentCoordinateOneCount_le parents coordinate
  let kernel : BinaryPairKernel :=
    pairCoordinateKernel (by omega) parents children coordinate
  have hkernel := empiricalConditionalEntropy_bound
    parentCount (pairParentCoordinateOneCount parents coordinate)
      hparents hones kernel
      (pairCoordinateKernel_parentProbability
        (by omega) parents children coordinate)
  change
    empiricalConditionalEntropy parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate) ≤ _ at hkernel
  rw [pairCoordinateKernel_empiricalConditionalEntropy
    (by omega) parents children coordinate] at hkernel
  rw [pairCoordinateKernel_empiricalChildMarginal
    (by omega) parents children coordinate] at hkernel
  change
    pairCoordinateConditionalEntropy parents children coordinate ≤
      entropyConstant +
        entropySlope *
          empiricalAverageDisagreement parentCount
            (pairParentCoordinateOneCount parents coordinate)
            (pairCoordinateKernel (by omega)
              parents children coordinate) +
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
        empiricalEntropyError parentCount at hkernel
  exact hkernel

noncomputable def pairParentArrayEntropyPotential
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayEntropyPotential
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    empiricalAverageDisagreement parentCount
      (pairParentCoordinateOneCount parents coordinate)
      (pairCoordinateKernel (by omega) parents children coordinate)) /
    (dimension : ℝ)

theorem pairChildArrayAverageDisagreement_le_radius
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges :
      ∀ (pair : PairLayer parentCount 1)
        (parent : PairLayer parentCount 0),
        parent ∈ pair.val →
          hammingDist (parents parent) (children pair) ≤ radius) :
    pairChildArrayAverageDisagreement hparents parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : 2 ≤ parentCount)
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) ≤
        2 * parentCount.choose 2 * radius := by
    calc
      (∑ coordinate : Fin dimension,
        ∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair) =
        ∑ pair : PairLayer parentCount 1,
          ∑ parent ∈ pair.val,
            hammingDist (parents parent) (children pair) :=
        sum_pairCoordinatePairMismatchCount_eq_hammingDist
          parents children
      _ ≤ ∑ pair : PairLayer parentCount 1,
          ∑ _parent ∈ pair.val, radius := by
        apply Finset.sum_le_sum
        intro pair _
        apply Finset.sum_le_sum
        intro parent hparent
        exact hedges pair parent hparent
      _ = ∑ _pair : PairLayer parentCount 1, 2 * radius := by
        apply Finset.sum_congr rfl
        intro pair _
        simp [pair.property]
      _ = 2 * parentCount.choose 2 * radius := by
        simp [pairLayer_card_succ, pairLayer_card_zero,
          Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ pair : PairLayer parentCount 1,
          pairCoordinatePairMismatchCount
            parents children coordinate pair : ℕ) : ℝ)) ≤
        2 * (parentCount.choose 2 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  unfold pairChildArrayAverageDisagreement
  simp_rw [pairCoordinateKernel_empiricalAverageDisagreement_eq_mismatches
    (by omega : 2 ≤ parentCount) parents children]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdimension_real).mpr
  apply (div_le_iff₀ (mul_pos (by norm_num) hpair)).mpr
  nlinarith

theorem pairChildArrayEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    pairChildArrayEntropy parents children ≤
      entropyConstant +
        entropySlope *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hsum :
      (∑ coordinate : Fin dimension,
        pairCoordinateConditionalEntropy parents children coordinate) ≤
      ∑ coordinate : Fin dimension,
        (entropyConstant +
          entropySlope *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount) := by
    apply Finset.sum_le_sum
    intro coordinate _
    exact pairCoordinateConditionalEntropy_empirical_bound
      hparents parents children coordinate
  have hnormalized :=
    (div_le_div_iff_of_pos_right hdimension_real).mpr hsum
  change pairChildArrayEntropy parents children ≤ _ at hnormalized
  let disagreementSum : ℝ :=
    ∑ coordinate : Fin dimension,
      empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega)
          parents children coordinate)
  let childEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 2 : ℝ))
  let parentEntropySum : ℝ :=
    ∑ coordinate : Fin dimension,
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ))
  have hentropy_sum :
      (∑ coordinate : Fin dimension,
        (binaryEntropy
            ((pairChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 2 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2) =
        (childEntropySum - parentEntropySum) / 2 := by
    dsimp [childEntropySum, parentEntropySum]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hsum_formula :
      (∑ coordinate : Fin dimension,
        (entropyConstant +
          entropySlope *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (dimension : ℝ) * entropyConstant +
          entropySlope * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
    calc
      (∑ coordinate : Fin dimension,
        (entropyConstant +
          entropySlope *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) =
        (∑ _coordinate : Fin dimension, entropyConstant) +
          (∑ coordinate : Fin dimension,
            entropySlope *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate)) +
          (∑ coordinate : Fin dimension,
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2) +
          (∑ _coordinate : Fin dimension,
            empiricalEntropyError parentCount) := by
            simp only [Finset.sum_add_distrib]
      _ = (dimension : ℝ) * entropyConstant +
          entropySlope * disagreementSum +
          (childEntropySum - parentEntropySum) / 2 +
          (dimension : ℝ) * empiricalEntropyError parentCount := by
        rw [hentropy_sum]
        dsimp [disagreementSum]
        rw [← Finset.mul_sum]
        simp [nsmul_eq_mul]
  calc
    pairChildArrayEntropy parents children ≤
      (∑ coordinate : Fin dimension,
        (entropyConstant +
          entropySlope *
            empiricalAverageDisagreement parentCount
              (pairParentCoordinateOneCount parents coordinate)
              (pairCoordinateKernel (by omega)
                parents children coordinate) +
          (binaryEntropy
              ((pairChildCoordinateOneCount children coordinate : ℝ) /
                (parentCount.choose 2 : ℝ)) -
            binaryEntropy
              ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                (parentCount : ℝ))) / 2 +
          empiricalEntropyError parentCount)) /
            (dimension : ℝ) := hnormalized
    _ = entropyConstant +
        entropySlope *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by
      change
        (∑ coordinate : Fin dimension,
          (entropyConstant +
            entropySlope *
              empiricalAverageDisagreement parentCount
                (pairParentCoordinateOneCount parents coordinate)
                (pairCoordinateKernel (by omega)
                  parents children coordinate) +
            (binaryEntropy
                ((pairChildCoordinateOneCount children coordinate : ℝ) /
                  (parentCount.choose 2 : ℝ)) -
              binaryEntropy
                ((pairParentCoordinateOneCount parents coordinate : ℝ) /
                  (parentCount : ℝ))) / 2 +
            empiricalEntropyError parentCount)) /
              (dimension : ℝ) =
          entropyConstant +
            entropySlope * (disagreementSum / (dimension : ℝ)) +
            (childEntropySum / (dimension : ℝ) -
              parentEntropySum / (dimension : ℝ)) / 2 +
            empiricalEntropyError parentCount
      rw [hsum_formula]
      field_simp [hdimension_real.ne']

theorem pairCoordinateConditionalEntropy_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose 2 : ℝ) *
        pairCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ)) := by
  have hpair : 0 < (parentCount.choose 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold pairCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [hpair.ne']

theorem pairCoordinateConditionalEntropy_log_mass
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : PairBitType,
      ((pairTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((pairTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : PairBitType,
        ((pairTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((pairTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((pairTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [log_two_pos.ne']
    _ = (parentCount.choose 2 : ℝ) * Real.log 2 *
        pairCoordinateConditionalEntropy parents children coordinate := by
      rw [← pairCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem pairChildGroup_choose_product_entropy_bound
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    (∏ index : PairBitType × Fin dimension,
      ((pairTypeGroup parents index.2 index.1).card).choose
        ((pairTypeGroupChildOnes parents children index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := PairBitType × Fin dimension)
    (fun index => (pairTypeGroup parents index.2 index.1).card)
    (fun index =>
      (pairTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => pairTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : PairBitType × Fin dimension,
        ((pairTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((pairTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((pairTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [pairCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

theorem pairChildArraysOfRealizedProfile_card_le
    {parentCount dimension : ℕ} (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate)) := by
  have hcard :
      ((pairChildArraysOfProfile parents
        (pairChildCountProfile parents children)).card : ℝ) =
        ∏ index : PairBitType × Fin dimension,
          (((pairTypeGroup parents index.2 index.1).card).choose
            ((pairTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      pairChildArraysOfProfile_card parents
        (pairChildCountProfile parents children)
  rw [hcard]
  exact pairChildGroup_choose_product_entropy_bound
    hparents parents children

noncomputable def badPairChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildArrayEntropy parents children ≤ threshold)

theorem badPairChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 2 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badPairChildArrays parents threshold :
        Finset (PairLayer parentCount 1 → HammingWord dimension)) :
        Set (PairLayer parentCount 1 → HammingWord dimension)).MapsTo
        (pairChildCountProfile parents)
        (Finset.univ : Finset (PairTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : PairTypeCountProfile parentCount dimension) :
      (((badPairChildArrays parents threshold).filter
        (fun children => pairChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badPairChildArrays parents threshold).filter
          (fun children =>
            pairChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : pairChildCountProfile parents children = profile :=
        hparts.2
      have hbad : pairChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : PairLayer parentCount 1 →
                    HammingWord dimension =>
                  pairChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badPairChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badPairChildArrays parents threshold).filter
              (fun candidate =>
                pairChildCountProfile parents candidate = profile) ⊆
            pairChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold pairChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badPairChildArrays parents threshold).filter
            (fun candidate =>
              pairChildCountProfile parents candidate = profile)).card : ℝ) ≤
            ((pairChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((pairChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact pairChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            pairCoordinateConditionalEntropy parents children coordinate) ≤
              (dimension : ℝ) * threshold := by
        unfold pairChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 2 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _) log_two_pos.le
      have hexponential :
          Real.exp
              ((parentCount.choose 2 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  pairCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badPairChildArrays parents threshold).card : ℝ) =
        ∑ profile : PairTypeCountProfile parentCount dimension,
          (((badPairChildArrays parents threshold).filter
            (fun children =>
              pairChildCountProfile parents children = profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : PairTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 2 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        pairTypeCountProfile_card]


end Erdos566.Retuned

/-
Independent Bernoulli sampling and child-layer union bounds adapted from
OpenAI et al., CompactnessAndDegeneracy.lean, under LICENSE-OpenAI.
The retention exponent is the retuned value Erdos566.beta.
The auxiliary sample has two independent labeled copies of the cube.
-/

open Finset Filter MeasureTheory
open scoped Topology

namespace Erdos566.Retuned

theorem sampling_beta_pos : 0 < Erdos566.beta := by norm_num [Erdos566.beta]
theorem sampling_beta_lt_one : Erdos566.beta < 1 := by norm_num [Erdos566.beta]

noncomputable def hammingRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-(Erdos566.beta * (dimension : ℝ) * Real.log 2))

theorem hammingRetentionProbability_pos (dimension : ℕ) :
    0 < hammingRetentionProbability dimension := by
  unfold hammingRetentionProbability
  exact Real.exp_pos _

theorem hammingRetentionProbability_le_one (dimension : ℕ) :
    hammingRetentionProbability dimension ≤ 1 := by
  unfold hammingRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ Erdos566.beta * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg sampling_beta_pos.le (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith

theorem hammingRetentionProbability_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - Erdos566.beta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_add]
  congr 1
  ring

theorem hammingRetentionProbability_sq_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * Erdos566.beta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem hammingRetentionProbability_mul_wordCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - Erdos566.beta) * Real.log 2 :=
    mul_pos (sub_pos.mpr sampling_beta_lt_one) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - Erdos566.beta) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [hammingRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring

theorem hammingRetentionProbability_mul_wordCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingRetentionProbability_mul_wordCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem exp_mul_div_nat_succ_tendsto_atTop
    (rate : ℝ) (hrate : 0 < rate) :
    Tendsto
      (fun dimension : ℕ =>
        Real.exp (rate * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ))
      atTop atTop := by
  have hquotient :
      Tendsto
        (fun dimension : ℕ =>
          Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ))
        atTop atTop := by
    have htendsto :=
      (tendsto_exp_mul_div_rpow_atTop 1 rate hrate).comp
        tendsto_natCast_atTop_atTop
    refine htendsto.congr' ?_
    filter_upwards [] with dimension
    simp [Function.comp_apply]
  have hhalf :
      Tendsto
        (fun dimension : ℕ =>
          (1 / 2 : ℝ) *
            (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)))
        atTop atTop :=
    hquotient.const_mul_atTop (by norm_num)
  apply tendsto_atTop_mono' atTop _ hhalf
  filter_upwards [Filter.eventually_ge_atTop 1] with dimension hdimension
  have hpositive : 0 < (dimension : ℝ) := by
    exact_mod_cast (show 0 < dimension by omega)
  have hdimension_real : (1 : ℝ) ≤ (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (1 / 2 : ℝ) *
        (Real.exp (rate * (dimension : ℝ)) / (dimension : ℝ)) =
      Real.exp (rate * (dimension : ℝ)) /
        (2 * (dimension : ℝ)) := by
        ring
    _ ≤ Real.exp (rate * (dimension : ℝ)) /
        ((dimension + 1 : ℕ) : ℝ) := by
      gcongr
      push_cast
      nlinarith

noncomputable def hammingRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨hammingRetentionProbability dimension,
    hammingRetentionProbability_pos dimension |>.le,
    hammingRetentionProbability_le_one dimension⟩

noncomputable def hammingRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (hammingRetentionParameter dimension)

theorem hammingRetentionMeasure_isProbability (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) := by
  unfold hammingRetentionMeasure
  infer_instance

theorem hammingRetentionMeasure_integrable
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (hammingRetentionMeasure dimension) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  exact MeasureTheory.Integrable.of_finite

theorem hammingRetentionMeasure_memLp_two
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (hammingRetentionMeasure dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (hammingRetentionMeasure_integrable dimension observable).aestronglyMeasurable).mpr
  exact hammingRetentionMeasure_integrable dimension
    (fun retained => observable retained ^ 2)

theorem hammingRetentionMeasure_integral_eq_sum
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂hammingRetentionMeasure dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (hammingRetentionMeasure dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (hammingRetentionMeasure_integrable dimension observable))

open Classical in
theorem hammingRetentionMeasure_real_event_eq_sum
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (hammingRetentionMeasure dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  let support : Finset (Set (Bool × HammingWord dimension)) :=
    Finset.univ.filter (fun retained => retained ∈ event)
  have hsupport :
      (support : Set (Set (Bool × HammingWord dimension))) = event := by
    ext retained
    simp [support]
  calc
    (hammingRetentionMeasure dimension).real event =
        (hammingRetentionMeasure dimension).real support := by
      rw [hsupport]
    _ = ∑ retained ∈ support,
        (hammingRetentionMeasure dimension).real {retained} := by
      exact (MeasureTheory.sum_measureReal_singleton support).symm
    _ = ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (hammingRetentionMeasure dimension).real {retained}
        else 0 := by
      rw [← Finset.sum_filter]

open Classical in
theorem hammingRetentionMeasure_integral_event_indicator
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (∫ retained,
      (if retained ∈ event then (1 : ℝ) else 0)
        ∂hammingRetentionMeasure dimension) =
      (hammingRetentionMeasure dimension).real event := by
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  split_ifs <;> simp

theorem hammingRetentionMeasure_real_deviation_le
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂hammingRetentionMeasure dimension)|} ≤
      ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (hammingRetentionMeasure_memLp_two dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (hammingRetentionMeasure dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal

theorem hammingRetentionMeasure_real_contains_finset
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      hammingRetentionProbability dimension ^ required.card := by
  classical
  have hpreimage :
      (fun membership : (Bool × HammingWord dimension) → Prop =>
        {vertex | membership vertex}) ⁻¹'
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        Set.pi (required : Set (Bool × HammingWord dimension))
          (fun _ => ({True} : Set Prop)) := by
    ext membership
    simp
  have hmeasure :
      hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        (↑(unitInterval.toNNReal
          (hammingRetentionParameter dimension)) : ENNReal) ^
            required.card := by
    unfold hammingRetentionMeasure
    rw [ProbabilityTheory.setBernoulli_apply']
    rw [hpreimage]
    rw [MeasureTheory.Measure.infinitePi_pi]
    · simp
    · intro vertex _
      measurability
  change
    ENNReal.toReal
        (hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained}) = _
  rw [hmeasure, ENNReal.toReal_pow]
  simp [hammingRetentionParameter]

theorem hammingRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      hammingRetentionProbability dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    hammingRetentionMeasure_real_contains_finset dimension {first, second}

theorem hammingRetentionMeasure_real_contains_vertex
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by
  classical
  simpa using
    hammingRetentionMeasure_real_contains_finset dimension {vertex}

theorem hammingRetentionMeasure_real_contains_edgePair
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      hammingRetentionProbability dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, hammingRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]

theorem hammingRetentionMeasure_real_contains_edgePair_le
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} ≤
      hammingRetentionProbability dimension ^ 4 +
        (if firstLeft = secondLeft then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          hammingRetentionProbability dimension ^ 2 else 0) := by
  rw [hammingRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (hammingRetentionProbability_pos dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity

noncomputable def hammingExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}

theorem hammingExpectedRetainedVertexCount_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexCount dimension =
      2 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold hammingExpectedRetainedVertexCount
  simp_rw [hammingRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem hammingExpectedRetainedVertexCount_pos
    (dimension : ℕ) :
    0 < hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  positivity

theorem hammingExpectedRetainedVertexCount_tendsto_atTop :
    Tendsto hammingExpectedRetainedVertexCount atTop atTop := by
  have hgrowth :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [hammingExpectedRetainedVertexCount_eq]
  ring

theorem hammingExpectedRetainedVertexCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / hammingExpectedRetainedVertexCount dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    hammingExpectedRetainedVertexCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem hammingRetentionMeasure_real_vertexPair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, hammingRetentionMeasure_real_contains_vertex]
    simp
  · rw [hammingRetentionMeasure_real_contains_pair
      dimension first second hequal]
    simp [hequal]

noncomputable def hammingExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}

theorem hammingExpectedRetainedVertexSquare_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        hammingRetentionProbability dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (hammingRetentionProbability dimension -
          hammingRetentionProbability dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2) =
        hammingRetentionProbability dimension ^ 2 +
          (if first = second then
            hammingRetentionProbability dimension -
              hammingRetentionProbability dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold hammingExpectedRetainedVertexSquare
  simp_rw [hammingRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring

theorem hammingExpectedRetainedVertexVariance_eq
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension *
        (1 - hammingRetentionProbability dimension) := by
  rw [hammingExpectedRetainedVertexSquare_eq,
    hammingExpectedRetainedVertexCount_eq]
  push_cast
  ring

theorem hammingExpectedRetainedVertexVariance_le_mean
    (dimension : ℕ) :
    hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingExpectedRetainedVertexVariance_eq,
    hammingExpectedRetainedVertexCount_eq]
  have hprobability := hammingRetentionProbability_pos dimension
  have hupper := hammingRetentionProbability_le_one dimension
  have hfactor :
      0 ≤ (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        hammingRetentionProbability dimension := by
    positivity
  have hle : 1 - hammingRetentionProbability dimension ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hle hfactor
  push_cast at hscaled ⊢
  nlinarith

noncomputable def hammingRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0

open Classical in
theorem hammingRetainedVertexCount_eq_card
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [hammingRetainedVertexCount, Fintype.card_subtype]

theorem hammingRetainedVertexCount_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexCount dimension := by
  classical
  unfold hammingRetainedVertexCount hammingExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact hammingRetentionMeasure_integral_event_indicator dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}

open Classical in
theorem hammingRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold hammingRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]

theorem hammingRetainedVertexCount_sq_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension := by
  classical
  simp_rw [hammingRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold hammingExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => hammingRetentionMeasure_integrable dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [hammingRetentionMeasure_integral_eq_sum,
    hammingRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]

theorem hammingRetainedVertexCount_variance_eq
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  rw [ProbabilityTheory.variance_eq_sub
    (hammingRetentionMeasure_memLp_two dimension
      (hammingRetainedVertexCount dimension))]
  change
    (∫ retained,
      hammingRetainedVertexCount dimension retained ^ 2
        ∂hammingRetentionMeasure dimension) -
      (∫ retained,
        hammingRetainedVertexCount dimension retained
          ∂hammingRetentionMeasure dimension) ^ 2 =
      hammingExpectedRetainedVertexSquare dimension -
        hammingExpectedRetainedVertexCount dimension ^ 2
  rw [hammingRetainedVertexCount_sq_integral_eq,
    hammingRetainedVertexCount_integral_eq]

theorem hammingRetainedVertexCount_variance_le
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedVertexCount dimension)
        (hammingRetentionMeasure dimension) ≤
      hammingExpectedRetainedVertexCount dimension := by
  rw [hammingRetainedVertexCount_variance_eq]
  exact hammingExpectedRetainedVertexVariance_le_mean dimension

theorem hammingRetainedVertexCount_deviation_probability_le
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      hammingExpectedRetainedVertexCount dimension / threshold ^ 2 := by
  have hchebyshev := hammingRetentionMeasure_real_deviation_le
    dimension (hammingRetainedVertexCount dimension)
    threshold hthreshold
  rw [hammingRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} ≤
      ProbabilityTheory.variance
          (hammingRetainedVertexCount dimension)
          (hammingRetentionMeasure dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        threshold ^ 2 := by
      gcongr
      exact hammingRetainedVertexCount_variance_le dimension

theorem hammingRetainedVertexCount_upper_tail_probability_le
    (dimension : ℕ) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      4 / hammingExpectedRetainedVertexCount dimension := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  have hmean := hammingExpectedRetainedVertexCount_pos dimension
  have hthreshold :
      0 < hammingExpectedRetainedVertexCount dimension / 2 := by
    positivity
  have hchebyshev := hammingRetainedVertexCount_deviation_probability_le
    dimension (hammingExpectedRetainedVertexCount dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        hammingExpectedRetainedVertexCount dimension / 2 ≤
          |hammingRetainedVertexCount dimension retained -
            hammingExpectedRetainedVertexCount dimension|} := by
    intro retained hretained
    change
      hammingExpectedRetainedVertexCount dimension / 2 ≤
        |hammingRetainedVertexCount dimension retained -
          hammingExpectedRetainedVertexCount dimension|
    have habsolute := le_abs_self
      (hammingRetainedVertexCount dimension retained -
        hammingExpectedRetainedVertexCount dimension)
    rw [hammingExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          hammingRetainedVertexCount dimension retained} ≤
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          hammingExpectedRetainedVertexCount dimension / 2 ≤
            |hammingRetainedVertexCount dimension retained -
              hammingExpectedRetainedVertexCount dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ hammingExpectedRetainedVertexCount dimension /
        (hammingExpectedRetainedVertexCount dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / hammingExpectedRetainedVertexCount dimension := by
      field_simp [hmean.ne']
      ring

noncomputable def pairChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (PairLayer parentCount 1)).image
    (fun pair => (side, children pair))

theorem pairChildVertexFinset_card
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (pairChildVertexFinset side children).card = parentCount.choose 2 := by
  classical
  unfold pairChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

def pairChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ pair, (side, children pair) ∈ retained}

theorem hammingRetentionMeasure_real_pairChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by
  classical
  have hevent :
      pairChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ pairChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [pairChildRetentionEvent, pairChildVertexFinset]
  rw [hevent, hammingRetentionMeasure_real_contains_finset,
    pairChildVertexFinset_card side children hinjective]

noncomputable def badPairChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badPairChildArrays parents threshold).filter Function.Injective,
      pairChildRetentionEvent side children

theorem badPairChildRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let distinctBad :
      Finset (PairLayer parentCount 1 → HammingWord dimension) :=
    (badPairChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ hammingRetentionProbability dimension ^
        (parentCount.choose 2) :=
    pow_nonneg (hammingRetentionProbability_pos dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badPairChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badPairChildArrays parents threshold) Function.Injective
  calc
    (hammingRetentionMeasure dimension).real
        (badPairChildRetentionEvent parents side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ children ∈ distinctBad,
          pairChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (hammingRetentionMeasure dimension).real
            (pairChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (pairChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badPairChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact hammingRetentionMeasure_real_pairChildren
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badPairChildArrays parents threshold).card : ℝ) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) :=
        mul_le_mul_of_nonneg_right
          (badPairChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

theorem hammingParentTuple_card (parentCount dimension : ℕ) :
    Fintype.card (Fin parentCount → HammingWord dimension) =
      2 ^ (dimension * parentCount) := by
  simp [HammingWord, ← pow_mul]

noncomputable def badPairLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badPairChildRetentionEvent parents side threshold

theorem badPairLayerRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayerRetentionEvent parentCount dimension side threshold) =
      (hammingRetentionMeasure dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badPairChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (hammingRetentionMeasure dimension).real
            (badPairChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badPairChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badPairChildRetentionEvent_real_le
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring

theorem badPairLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 2 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (Erdos566.beta - entropySlack))) *
        hammingRetentionProbability dimension ^
          (parentCount.choose 2)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by
            norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 2 + 1 : ℕ) : ℝ)) ^
            (3 * dimension) := by
              norm_cast
      _ = Real.exp
          (((3 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 2 + 1 : ℕ) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      hammingRetentionProbability dimension ^
          (parentCount.choose 2) =
        Real.exp
          ((parentCount.choose 2 : ℝ) *
            (-(Erdos566.beta * (dimension : ℝ) * Real.log 2))) := by
    unfold hammingRetentionProbability
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [log_two_pos.ne']
  ring

theorem badPairLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * (parentCount.choose 2 : ℝ) < -1)
    (side : Bool) :
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (Erdos566.beta - entropySlack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (hammingRetentionMeasure dimension).real
      (badPairLayerRetentionEvent parentCount dimension side
        (Erdos566.beta - entropySlack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * (Erdos566.beta - entropySlack))) *
          hammingRetentionProbability dimension ^
            (parentCount.choose 2)) :=
        badPairLayerRetentionEvent_real_le
          (by omega) hdimension side (Erdos566.beta - entropySlack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            3 * logTwo ((parentCount.choose 2 + 1 : ℕ) : ℝ) -
              entropySlack * (parentCount.choose 2 : ℝ))) :=
        badPairLayerRetentionBound_eq_exp parentCount dimension
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

noncomputable def badPairLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badPairLayerRetentionEvent (layerSizes layer) dimension side
      (Erdos566.beta - entropySlack)

theorem badPairLayersRetentionEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (hammingRetentionMeasure dimension).real
        (badPairLayersRetentionEvent layerSizes dimension) =
      (hammingRetentionMeasure dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badPairLayerRetentionEvent (layerSizes layer) dimension side
            (Erdos566.beta - entropySlack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (hammingRetentionMeasure dimension).real
          (⋃ layer : Fin depth,
            badPairLayerRetentionEvent (layerSizes layer) dimension side
              (Erdos566.beta - entropySlack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badPairLayerRetentionEvent (layerSizes layer) dimension side
                (Erdos566.beta - entropySlack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (hammingRetentionMeasure dimension).real
            (badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (Erdos566.beta - entropySlack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badPairLayerRetentionEvent
              (layerSizes layer) dimension side
                (Erdos566.beta - entropySlack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badPairLayerRetentionEvent_real_lt_exp_neg
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring

theorem exp_neg_dimension_log_two (dimension : ℕ) :
    Real.exp (-(dimension : ℝ) * Real.log 2) =
      ((1 / 2 : ℝ) ^ dimension) := by
  calc
    Real.exp (-(dimension : ℝ) * Real.log 2) =
        Real.exp (-((dimension : ℝ) * Real.log 2)) := by
          congr 1
          ring
    _ = (Real.exp ((dimension : ℝ) * Real.log 2))⁻¹ :=
      Real.exp_neg _
    _ = ((2 : ℝ) ^ dimension)⁻¹ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ dimension) := by
      rw [← inv_pow]
      norm_num

theorem pairLayerExclusionProbability_tendsto_zero (depth : ℕ) :
    Filter.Tendsto
      (fun dimension : ℕ =>
        (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hgeometric :
      Filter.Tendsto
        (fun dimension : ℕ => (1 / 2 : ℝ) ^ dimension)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp_rw [exp_neg_dimension_log_two]
  simpa only [mul_zero] using
    hgeometric.const_mul (((2 * depth : ℕ) : ℝ))

theorem exists_hammingRetention_outside_event
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (hammingRetentionMeasure dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  letI : MeasureTheory.IsProbabilityMeasure
      (hammingRetentionMeasure dimension) :=
    hammingRetentionMeasure_isProbability dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall


end Erdos566.Retuned

/-
Single-cube transfer of the layered exclusion argument. Array bookkeeping
is adapted from the OpenAI source credited in ChildArrayCounting.lean.
-/

open Finset Filter SimpleGraph
open scoped Topology

namespace Erdos566.Retuned

def ballGraph (dimension radius : ℕ) : SimpleGraph (HammingWord dimension) :=
  SimpleGraph.fromRel (fun x y => hammingDist x y ≤ radius)

def singleCubeHost (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) (side : Bool) :
    SimpleGraph {word : HammingWord dimension // (side, word) ∈ retained} :=
  (ballGraph dimension radius).induce {word | (side, word) ∈ retained}

theorem singleCubeHost_adj_iff {dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (x y : {word : HammingWord dimension // (side, word) ∈ retained}) :
    (singleCubeHost dimension radius retained side).Adj x y ↔
      x.val ≠ y.val ∧ hammingDist x.val y.val ≤ radius := by
  simp only [singleCubeHost, SimpleGraph.induce_adj, ballGraph,
    SimpleGraph.fromRel_adj, hammingDist_comm, or_self]

noncomputable def pairGraphCopyParentWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    Fin (Fintype.card (PairLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy
      (pairLayerEmbedding baseSize depth layer.val (by omega)
        ((pairLayerFinEquiv baseSize layer.val).symm parent))).val

noncomputable def pairGraphCopyChildWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun pair =>
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).val

noncomputable def pairGraphCopyLayerPotential
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : PairLayer baseSize layer.val =>
          (copy
            (pairLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val coordinate)).card : ℝ) /
        (Fintype.card (PairLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)

theorem pairGraphCopy_parentPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    pairParentArrayEntropyPotential
        (pairGraphCopyParentWords retained side copy layer) =
      pairGraphCopyLayerPotential retained side copy
        ⟨layer.val, by omega⟩ := by
  unfold pairParentArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount pairGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (pairLayerFinEquiv baseSize layer.val).symm
    (fun vertex : PairLayer baseSize layer.val =>
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          vertex)).val coordinate)]

theorem pairGraphCopy_childPotential_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    pairChildArrayEntropyPotential
        (pairGraphCopyChildWords retained side copy layer) =
      pairGraphCopyLayerPotential retained side copy
        ⟨layer.val + 1, by omega⟩ := by
  unfold pairChildArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairChildCoordinateOneCount pairGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (pairLayerPairEquiv baseSize layer.val)
    (fun vertex : PairLayer baseSize (layer.val + 1) =>
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          vertex)).val coordinate)]
  rw [pairLayer_card_succ]

theorem pairGraphCopyLayerPotential_mem_Icc
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin (depth + 1)) :
    0 ≤ pairGraphCopyLayerPotential retained side copy layer ∧
      pairGraphCopyLayerPotential retained side copy layer ≤ 1 := by
  classical
  have hlayer :
      0 < Fintype.card (PairLayer baseSize layer.val) := by
    have hcard := pairLayer_card_ge_base
      baseSize layer.val hbase
    omega
  have hlayer_real :
      0 < (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val coordinate)).card ≤
          Fintype.card (PairLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (PairLayer baseSize layer.val))
          (fun vertex =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val coordinate = true))
    have hzero :
        0 ≤
          ((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) := by
      positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : PairLayer baseSize layer.val =>
            (copy
              (pairLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val coordinate)).card : ℝ) /
            (Fintype.card (PairLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone,
      binaryEntropy_le_one _⟩
  unfold pairGraphCopyLayerPotential
  constructor
  · apply div_nonneg
    · exact Finset.sum_nonneg
        (fun coordinate _ => (hterm coordinate).1)
    · exact hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc
      (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : PairLayer baseSize layer.val =>
              (copy
                (pairLayerEmbedding baseSize depth layer.val layer.isLt
                  vertex)).val coordinate)).card : ℝ) /
              (Fintype.card (PairLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) := by
          exact Finset.sum_le_sum
            (fun coordinate _ => (hterm coordinate).2)
      _ = (dimension : ℝ) := by
        simp

theorem pairGraphCopy_layer_entropy_upper_of_disagreement
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (side : Bool)
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained side copy layer)
        (pairGraphCopyChildWords retained side copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained side copy layer)
      (pairGraphCopyChildWords retained side copy layer) ≤
        Erdos566.entropyThreshold +
          (pairGraphCopyLayerPotential retained side copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained side copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by
  have hparents :
      4 ≤ Fintype.card (PairLayer baseSize layer.val) :=
    hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase)
  have hbound := pairChildArrayEntropy_empirical_bound
    hparents hdimension
    (pairGraphCopyParentWords retained side copy layer)
    (pairGraphCopyChildWords retained side copy layer)
  rw [pairGraphCopy_childPotential_eq retained side copy layer,
    pairGraphCopy_parentPotential_eq retained side copy layer] at hbound
  have hscaled := mul_le_mul_of_nonneg_left
    hdisagreement entropySlope_pos.le
  have hconstant := entropyConstant_add_radius
  nlinarith


theorem pairGraphCopyChildWords_injective
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (copy : SimpleGraph.Copy (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained side copy layer) := by
  intro first second hwords
  have himages :
      copy (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        (pairLayerPairEquiv baseSize layer.val first)) =
      copy (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        (pairLayerPairEquiv baseSize layer.val second)) := by
    apply Subtype.ext
    exact hwords
  exact (pairLayerPairEquiv baseSize layer.val).injective
    ((pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)).injective
      (copy.injective himages))

theorem pairGraphCopyChildWords_retained
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (copy : SimpleGraph.Copy (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    retained ∈ pairChildRetentionEvent side
      (pairGraphCopyChildWords retained side copy layer) := by
  intro pair
  exact (copy (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
    (pairLayerPairEquiv baseSize layer.val pair))).property

theorem pairGraphCopy_parent_child_hammingDist_le
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (copy : SimpleGraph.Copy (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth)
    (pair : PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent : PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist (pairGraphCopyParentWords retained side copy layer parent)
      (pairGraphCopyChildWords retained side copy layer pair) ≤ radius := by
  have hactualParent :
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        ((pairLayerPairEquiv baseSize layer.val) pair).val := by
    change (pairLayerFinEquiv baseSize layer.val).symm parent ∈
      pair.val.map (pairLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := pairGraph_parent_child_adj baseSize depth layer.val (by omega)
    (pairLayerPairEquiv baseSize layer.val pair)
    ((pairLayerFinEquiv baseSize layer.val).symm parent) hactualParent
  have hedge := copy.toHom.map_rel hsource
  have hdist := ((singleCubeHost_adj_iff retained side _ _).mp hedge).2
  simpa [pairGraphCopyParentWords, pairGraphCopyChildWords, hammingDist_comm] using hdist

theorem pairGraphCopy_averageDisagreement_le_tau
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize) (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ Erdos566.tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (copy : SimpleGraph.Copy (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained side copy layer)
      (pairGraphCopyChildWords retained side copy layer) ≤ Erdos566.tau := by
  have havg := pairChildArrayAverageDisagreement_le_radius
    (hbase.trans (pairLayer_card_ge_base baseSize layer.val hbase)) hdimension
    (pairGraphCopyParentWords retained side copy layer)
    (pairGraphCopyChildWords retained side copy layer) radius
    (pairGraphCopy_parent_child_hammingDist_le retained side copy layer)
  have hdimensionR : (0 : ℝ) < dimension := by exact_mod_cast hdimension
  exact havg.trans ((div_le_iff₀ hdimensionR).mpr hradius)

theorem pairGraphCopy_entropy_lower_of_exclusion
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (copy : SimpleGraph.Copy (pairParentSystem baseSize depth).graph
      (singleCubeHost dimension radius retained side))
    (layer : Fin depth) (threshold : ℝ)
    (hexclusion : retained ∉ badPairLayerRetentionEvent
      (Fintype.card (PairLayer baseSize layer.val)) dimension side threshold) :
    threshold < pairChildArrayEntropy
      (pairGraphCopyParentWords retained side copy layer)
      (pairGraphCopyChildWords retained side copy layer) := by
  classical
  by_contra hnot
  have hbad : pairGraphCopyChildWords retained side copy layer ∈
      (badPairChildArrays (pairGraphCopyParentWords retained side copy layer)
        threshold).filter Function.Injective := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, pairGraphCopyChildWords_injective retained side copy layer⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, le_of_not_gt hnot⟩
  apply hexclusion
  exact Set.mem_iUnion.mpr ⟨pairGraphCopyParentWords retained side copy layer,
    Set.mem_iUnion.mpr ⟨pairGraphCopyChildWords retained side copy layer,
      Set.mem_iUnion.mpr ⟨hbad, pairGraphCopyChildWords_retained retained side copy layer⟩⟩⟩

theorem counterexample_free_of_exclusion
    {dimension radius : ℕ} (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ Erdos566.tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension)) (side : Bool)
    (hexclusion : ∀ layer : Fin Erdos566.layerDepth,
      retained ∉ badPairLayerRetentionEvent
        (Fintype.card (PairLayer Erdos566.baseSize layer.val))
        dimension side (Erdos566.beta - Erdos566.entropySlack)) :
    Erdos566.counterexampleGraph.Free (singleCubeHost dimension radius retained side) := by
  classical
  have hbase : 4 ≤ Erdos566.baseSize := by norm_num [Erdos566.baseSize]
  change (pairGraphOverFin Erdos566.baseSize Erdos566.layerDepth).Free _
  apply (SimpleGraph.free_congr_left
    (pairGraphOverFinIso Erdos566.baseSize Erdos566.layerDepth)).mp
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let potential : ℕ → ℝ := fun layer =>
    if hlevel : layer < Erdos566.layerDepth + 1 then
      pairGraphCopyLayerPotential retained side copy ⟨layer, hlevel⟩ else 0
  let conditional : ℕ → ℝ := fun layer =>
    if hlevel : layer < Erdos566.layerDepth then
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained side copy ⟨layer, hlevel⟩)
        (pairGraphCopyChildWords retained side copy ⟨layer, hlevel⟩) else 0
  let error : ℕ → ℝ := fun layer =>
    if layer < Erdos566.layerDepth then
      empiricalEntropyError (Fintype.card (PairLayer Erdos566.baseSize layer)) else 0
  apply Erdos566.entropy_layers_impossible potential conditional error
  · intro layer hlayer
    have hrange : layer < Erdos566.layerDepth + 1 := by omega
    simpa [potential, hrange, hlayer] using
      pairGraphCopyLayerPotential_mem_Icc hbase hdimension retained side copy ⟨layer, hrange⟩
  · intro layer hlayer
    have hsize := pairLayer_card_ge_base Erdos566.baseSize layer hbase
    simpa [error, hlayer] using empiricalEntropyError_lt_slack _ hsize
  · intro layer hlayer
    have hlower := pairGraphCopy_entropy_lower_of_exclusion retained side copy
      ⟨layer, hlayer⟩ (Erdos566.beta - Erdos566.entropySlack)
      (hexclusion ⟨layer, hlayer⟩)
    simpa [conditional, hlayer] using hlower
  · intro layer hlayer
    have hnext : layer + 1 < Erdos566.layerDepth + 1 := by omega
    have hcurrent : layer < Erdos566.layerDepth + 1 := by omega
    have hnext_le : layer + 1 ≤ Erdos566.layerDepth := by omega
    have hcurrent_le : layer ≤ Erdos566.layerDepth := by omega
    have hupper := pairGraphCopy_layer_entropy_upper_of_disagreement
      hbase hdimension retained side copy ⟨layer, hlayer⟩
      (pairGraphCopy_averageDisagreement_le_tau hbase hdimension hradius
        retained side copy ⟨layer, hlayer⟩)
    simpa [conditional, potential, error, hlayer, hnext, hcurrent,
      hnext_le, hcurrent_le] using hupper

theorem logTwo_pairLayer_card_add_one_le (L : ℕ) (hL : 2 ≤ L) :
    logTwo ((L.choose 2 + 1 : ℕ) : ℝ) ≤
      2 * (L : ℝ) / Real.log 2 := by
  let x : ℝ := ((L.choose 2 + 1 : ℕ) : ℝ)
  have hxpos : 0 < x := by
    dsimp [x]
    positivity
  have hLreal : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hchoose : (L.choose 2 : ℝ) =
      (L : ℝ) * ((L : ℝ) - 1) / 2 := by
    exact Nat.cast_choose_two ℝ L
  have hxle : x ≤ (L : ℝ) ^ 2 := by
    dsimp [x]
    push_cast
    rw [hchoose]
    nlinarith [sq_nonneg ((L : ℝ) - 1)]
  have hsqrt : Real.sqrt x ≤ (L : ℝ) := by
    have hsq := Real.sq_sqrt hxpos.le
    have hsqrt_nonneg := Real.sqrt_nonneg x
    nlinarith
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have hbound := Real.log_le_rpow_div hxpos.le
      (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at hbound
    norm_num at hbound
    linarith
  change Real.log x / Real.log 2 ≤ 2 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith


theorem fixed_base_first_moment_bound (L : ℕ) (hL : Erdos566.baseSize ≤ L) :
    (L : ℝ) + 3 * logTwo ((L.choose 2 + 1 : ℕ) : ℝ) -
      Erdos566.entropySlack * (L.choose 2 : ℝ) < -1 := by
  have hLreal : (10000000 : ℝ) ≤ L := by
    exact_mod_cast hL
  have hlog := logTwo_pairLayer_card_add_one_le L (by
    change 10000000 ≤ L at hL
    omega)
  have htwo : (1 : ℝ) / 2 < Real.log 2 := by
    linarith [Erdos566.log_two_bounds.1]
  have hquotient : 2 * (L : ℝ) / Real.log 2 ≤ 4 * L := by
    apply (div_le_iff₀ log_two_pos).mpr
    nlinarith [mul_nonneg (show 0 ≤ (L : ℝ) by positivity) (sub_nonneg.mpr htwo.le)]
  have hchoose : (L.choose 2 : ℝ) = (L : ℝ) * ((L : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ L
  rw [hchoose]
  unfold Erdos566.entropySlack
  nlinarith [mul_nonneg (sub_nonneg.mpr hLreal) (show 0 ≤ (L : ℝ) by positivity)]

noncomputable def fixedLayerSizes (layer : Fin Erdos566.layerDepth) : ℕ :=
  Fintype.card (PairLayer Erdos566.baseSize layer.val)

theorem fixedLayerSizes_ge_base (layer : Fin Erdos566.layerDepth) :
    Erdos566.baseSize ≤ fixedLayerSizes layer := by
  exact pairLayer_card_ge_base _ _ (by norm_num [Erdos566.baseSize])

def redFailure (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  badPairLayersRetentionEvent fixedLayerSizes dimension

theorem redFailure_probability_bound (dimension : ℕ) (hdimension : 0 < dimension) :
    (hammingRetentionMeasure dimension).real (redFailure dimension) ≤
      (2 * Erdos566.layerDepth : ℕ) * Real.exp (-(dimension : ℝ) * Real.log 2) := by
  apply badPairLayersRetentionEvent_real_le fixedLayerSizes hdimension
  · intro layer
    have hbase := fixedLayerSizes_ge_base layer
    change 10000000 ≤ fixedLayerSizes layer at hbase
    omega
  · intro layer
    exact fixed_base_first_moment_bound _ (fixedLayerSizes_ge_base layer)

theorem cubeCutoff_le_radius (dimension : ℕ) :
    (Erdos566.cubeCutoff dimension : ℝ) ≤ Erdos566.tau * dimension := by
  have hquotient : 200 * (43 * dimension / 200) ≤ 43 * dimension :=
    Nat.mul_div_le _ _
  have hquotientR : (200 : ℝ) * (43 * dimension / 200 : ℕ) ≤ 43 * (dimension : ℝ) := by
    exact_mod_cast hquotient
  unfold Erdos566.cubeCutoff Erdos566.tau
  push_cast
  nlinarith

theorem both_sides_free_outside_redFailure (dimension : ℕ) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (hgood : retained ∉ redFailure dimension) (side : Bool) :
    Erdos566.counterexampleGraph.Free
      (singleCubeHost dimension (Erdos566.cubeCutoff dimension) retained side) := by
  apply counterexample_free_of_exclusion hdimension (cubeCutoff_le_radius dimension)
    retained side
  intro layer hbad
  apply hgood
  exact Set.mem_iUnion.mpr ⟨side, Set.mem_iUnion.mpr ⟨layer, hbad⟩⟩

end Erdos566.Retuned

open Finset

namespace Erdos566.CubeFourier

noncomputable section

abbrev Word (n : ℕ) := Fin n → Bool

def bitSign (a b : Bool) : ℝ := if a && b then -1 else 1

def character {n : ℕ} (b x : Word n) : ℝ := ∏ i, bitSign (b i) (x i)

theorem bitSign_comm (a b : Bool) : bitSign a b = bitSign b a := by
  cases a <;> cases b <;> rfl

theorem bitSign_mul_xor (a b c : Bool) :
    bitSign a (b ^^ c) = bitSign a b * bitSign a c := by
  cases a <;> cases b <;> cases c <;> norm_num [bitSign]

theorem bitSign_sq (a b : Bool) : bitSign a b ^ 2 = 1 := by
  cases a <;> cases b <;> norm_num [bitSign]

theorem bitSign_inner (a b : Bool) :
    (∑ x : Bool, bitSign a x * bitSign b x) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [Fintype.univ_bool, bitSign]

theorem character_comm {n : ℕ} (a b : Word n) : character a b = character b a := by
  apply Finset.prod_congr rfl
  intro i _
  exact bitSign_comm _ _

theorem character_mul_xor {n : ℕ} (a b c : Word n) :
    character a (fun i => b i ^^ c i) = character a b * character a c := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact bitSign_mul_xor _ _ _

theorem character_sq {n : ℕ} (a b : Word n) : character a b ^ 2 = 1 := by
  unfold character
  rw [← Finset.prod_pow]
  simp only [bitSign_sq, Finset.prod_const_one]

theorem character_zero {n : ℕ} (x : Word n) : character (fun _ => false) x = 1 := by
  simp [character, bitSign]

theorem character_orthogonality {n : ℕ} (a b : Word n) :
    (∑ x : Word n, character a x * character b x) =
      if a = b then (2 : ℝ) ^ n else 0 := by
  classical
  have hterm (x : Word n) : character a x * character b x =
      ∏ i, bitSign (a i) (x i) * bitSign (b i) (x i) := by
    unfold character
    rw [Finset.prod_mul_distrib]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i z => bitSign (a i) z * bitSign (b i) z)]
  simp_rw [bitSign_inner]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      push_neg at h
      exact hab (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem character_dual_orthogonality {n : ℕ} (x y : Word n) :
    (∑ b : Word n, character b x * character b y) =
      if x = y then (2 : ℝ) ^ n else 0 := by
  simp_rw [character_comm]
  exact character_orthogonality x y

def transform {n : ℕ} (f : Word n → ℝ) (b : Word n) : ℝ :=
  ∑ x, f x * character b x

theorem transform_zero {n : ℕ} (f : Word n → ℝ) :
    transform f (fun _ => false) = ∑ x, f x := by
  simp [transform, character_zero]

theorem transform_pair {n : ℕ} (f g : Word n → ℝ) :
    (∑ b, transform f b * transform g b) =
      (2 : ℝ) ^ n * ∑ x, f x * g x := by
  classical
  calc
    (∑ b, transform f b * transform g b) =
        ∑ b, ∑ x, ∑ y, (f x * g y) * (character b x * character b y) := by
      apply Finset.sum_congr rfl
      intro b _
      unfold transform
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ x, ∑ y, (f x * g y) * (∑ b, character b x * character b y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
    _ = ∑ x, ∑ y, (f x * g y) * (if x = y then (2 : ℝ) ^ n else 0) := by
      simp_rw [character_dual_orthogonality]
    _ = (2 : ℝ) ^ n * ∑ x, f x * g x := by
      simp only [mul_ite, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem parseval {n : ℕ} (f : Word n → ℝ) :
    (∑ b, transform f b ^ 2) = (2 : ℝ) ^ n * ∑ x, f x ^ 2 := by
  simpa only [pow_two] using transform_pair f f

def xorWord {n : ℕ} (x y : Word n) : Word n := fun i => x i ^^ y i

theorem xorWord_self_cancel {n : ℕ} (x y : Word n) :
    xorWord x (xorWord x y) = y := by
  funext i
  unfold xorWord
  cases x i <;> cases y i <;> rfl

def translation {n : ℕ} (x : Word n) : Word n ≃ Word n where
  toFun := xorWord x
  invFun := xorWord x
  left_inv := xorWord_self_cancel x
  right_inv := xorWord_self_cancel x

theorem transform_translate {n : ℕ} (f : Word n → ℝ) (z b : Word n) :
    (∑ x, f (xorWord z x) * character b x) = character b z * transform f b := by
  calc
    (∑ x, f (xorWord z x) * character b x) =
        ∑ y, f y * character b (xorWord z y) := by
      apply Fintype.sum_equiv (translation z)
      intro x
      change f (xorWord z x) * character b x =
        f (xorWord z x) * character b (xorWord z (xorWord z x))
      rw [xorWord_self_cancel]
    _ = character b z * transform f b := by
      have hcharacter (y : Word n) :
          character b (xorWord z y) = character b z * character b y :=
        character_mul_xor b z y
      simp_rw [hcharacter]
      unfold transform
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring

def convolution {n : ℕ} (g f : Word n → ℝ) (x : Word n) : ℝ :=
  ∑ z, g z * f (xorWord z x)

theorem transform_convolution {n : ℕ} (g f : Word n → ℝ) (b : Word n) :
    transform (convolution g f) b = transform g b * transform f b := by
  calc
    transform (convolution g f) b =
        ∑ x, ∑ z, (g z * f (xorWord z x)) * character b x := by
      unfold transform convolution
      simp_rw [Finset.sum_mul]
    _ = ∑ z, ∑ x, (g z * f (xorWord z x)) * character b x := by
      rw [Finset.sum_comm]
    _ =
        ∑ z, g z * (∑ x, f (xorWord z x) * character b x) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ z, g z * (character b z * transform f b) := by
      simp_rw [transform_translate]
    _ = transform g b * transform f b := by
      unfold transform
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      ring

def quadratic {n : ℕ} (g f : Word n → ℝ) : ℝ := ∑ x, f x * convolution g f x

theorem quadratic_fourier {n : ℕ} (g f : Word n → ℝ) :
    (2 : ℝ) ^ n * quadratic g f = ∑ b, transform g b * transform f b ^ 2 := by
  have h := transform_pair f (convolution g f)
  simp_rw [transform_convolution] at h
  calc
    (2 : ℝ) ^ n * quadratic g f =
        ∑ b, transform f b * (transform g b * transform f b) := h.symm
    _ = ∑ b, transform g b * transform f b ^ 2 := by
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem quadratic_lower_bound {n : ℕ} (g f : Word n → ℝ) (D bound : ℝ)
    (hbound : 0 ≤ bound)
    (hzero : transform g (fun _ => false) = D)
    (hspectrum : ∀ b : Word n, -bound ≤ transform g b) :
    D * (∑ x, f x) ^ 2 - bound * (2 : ℝ) ^ n * (∑ x, f x ^ 2) ≤
      (2 : ℝ) ^ n * quadratic g f := by
  classical
  have hpoint (b : Word n) :
      (if b = (fun _ => false) then D * (∑ x, f x) ^ 2 else 0) -
          bound * transform f b ^ 2 ≤ transform g b * transform f b ^ 2 := by
    by_cases hb : b = (fun _ => false)
    · subst b
      rw [if_pos rfl, hzero, transform_zero]
      nlinarith only [mul_nonneg hbound (sq_nonneg (∑ x, f x))]
    · rw [if_neg hb]
      have h := mul_le_mul_of_nonneg_right (hspectrum b) (sq_nonneg (transform f b))
      linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Word n)))
    (fun b _ => hpoint b)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  rw [← Finset.mul_sum, parseval] at hsum
  rw [quadratic_fourier]
  nlinarith only [hsum]

end

end Erdos566.CubeFourier

open Polynomial

namespace Erdos566.Krawtchouk

noncomputable section

def generating (negative positive : ℕ) : ℝ[X] :=
  (1 - X) ^ negative * (1 + X) ^ positive

theorem derivative_minus_power (a : ℕ) :
    (1 - X) * derivative ((1 - X : ℝ[X]) ^ a) =
      C (-(a : ℝ)) * (1 - X) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      simp only [map_neg] at ih
      rw [pow_succ, derivative_mul]
      simp only [derivative_sub, derivative_one, derivative_X, zero_sub,
        Nat.cast_add, Nat.cast_one, neg_add, map_add, map_neg, map_one]
      linear_combination (1 - X) * ih

theorem derivative_plus_power (a : ℕ) :
    (1 + X) * derivative ((1 + X : ℝ[X]) ^ a) =
      C (a : ℝ) * (1 + X) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pow_succ, derivative_mul]
      simp only [derivative_add, derivative_one, derivative_X, zero_add,
        Nat.cast_add, Nat.cast_one, map_add, map_one]
      linear_combination (1 + X) * ih

theorem generating_differential (a b : ℕ) :
    (1 - X ^ 2) * derivative (generating a b) =
      (C ((b : ℝ) - a) - C ((a : ℝ) + b) * X) * generating a b := by
  unfold generating
  rw [derivative_mul]
  simp only [map_sub, map_add]
  have ha := derivative_minus_power a
  simp only [map_neg] at ha
  linear_combination
    ((1 + X) * (1 + X) ^ b) * ha +
      ((1 - X) * (1 - X) ^ a) * derivative_plus_power b

theorem coeff_square_derivative (p : ℝ[X]) (k : ℕ) :
    (X ^ 2 * derivative p).coeff (k + 1) = p.coeff k * (k : ℝ) := by
  cases k with
  | zero => simp [coeff_X_pow_mul']
  | succ k =>
      have h := coeff_X_pow_mul (derivative p) 2 k
      simpa [coeff_derivative, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem generating_coeff_zero (a b : ℕ) : (generating a b).coeff 0 = 1 := by
  simp [coeff_zero_eq_eval_zero, generating]

theorem generating_coeff_one (a b : ℕ) :
    (generating a b).coeff 1 = (b : ℝ) - a := by
  have h := generating_differential a b
  have heq : derivative (generating a b) - X ^ 2 * derivative (generating a b) =
      C ((b : ℝ) - a) * generating a b -
        C ((a : ℝ) + b) * (X * generating a b) := by
    convert h using 1 <;> ring
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff 0) heq
  simpa [coeff_X_pow_mul', coeff_X_mul, coeff_derivative, generating_coeff_zero] using hcoeff

theorem generating_coeff_recurrence (a b k : ℕ) :
    ((k : ℝ) + 2) * (generating a b).coeff (k + 2) =
      ((b : ℝ) - a) * (generating a b).coeff (k + 1) -
        ((a : ℝ) + b - k) * (generating a b).coeff k := by
  have h := generating_differential a b
  have heq : derivative (generating a b) - X ^ 2 * derivative (generating a b) =
      C ((b : ℝ) - a) * generating a b -
        C ((a : ℝ) + b) * (X * generating a b) := by
    convert h using 1 <;> ring
  have hcoeff := congrArg (fun p : ℝ[X] => p.coeff (k + 1)) heq
  simp only [coeff_sub, coeff_derivative, coeff_square_derivative, coeff_C_mul,
    coeff_X_mul, Nat.cast_add, Nat.cast_one] at hcoeff
  linear_combination hcoeff

theorem generating_coeff_monic (a b k : ℕ) :
    ((k.factorial : ℕ) : ℝ) * (generating a b).coeff k =
      monic (a + b) ((b : ℝ) - a) k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [monic, recurrence, generating_coeff_zero]
  | one => simp [monic, recurrence, generating_coeff_one]
  | more k ih0 ih1 =>
      have hrec := generating_coeff_recurrence a b k
      have hscaled := congrArg (fun x : ℝ => ((k + 1).factorial : ℝ) * x) hrec
      change ((k + 2).factorial : ℝ) * (generating a b).coeff (k + 2) =
        ((b : ℝ) - a) * monic (a + b) ((b : ℝ) - a) (k + 1) -
          ((k : ℝ) + 1) * ((a + b : ℕ) - (k : ℝ)) *
            monic (a + b) ((b : ℝ) - a) k
      rw [← ih0, ← ih1]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hscaled ⊢
      linear_combination hscaled

theorem generating_negative_inside (a b k : ℕ)
    (hkpos : 0 < k) (hk : 2 * k ≤ a + b + 1) (heven : Even k)
    (hnegative : (generating a b).coeff k < 0) :
    |(b : ℝ) - a| < 2 * Real.sqrt ((k : ℝ) * ((a : ℝ) + b - k + 1)) := by
  have hfactorial : (0 : ℝ) < (k.factorial : ℕ) := by
    exact_mod_cast Nat.factorial_pos k
  have hmonic : monic (a + b) ((b : ℝ) - a) k < 0 := by
    rw [← generating_coeff_monic]
    exact mul_neg_of_pos_of_neg hfactorial hnegative
  simpa only [Nat.cast_add] using negative_implies_inside (a + b) k
    ((b : ℝ) - a) hkpos hk heven hmonic

end

end Erdos566.Krawtchouk

open Finset Polynomial

namespace Erdos566.CubeFourier

noncomputable section

def weight {n : ℕ} (x : Word n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

theorem weight_le {n : ℕ} (x : Word n) : weight x ≤ n := by
  simpa [weight] using Finset.card_filter_le (Finset.univ : Finset (Fin n))
    (fun i => x i = true)

theorem weight_eq_sum {n : ℕ} (x : Word n) :
    weight x = ∑ i, if x i then 1 else 0 := by
  unfold weight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem weight_eq_ones {n : ℕ} (x : Word n) :
    weight x = (Erdos566.Retuned.booleanWordOnes x).card := rfl

theorem weight_class_card (n k : ℕ) :
    (Finset.univ.filter (fun x : Word n => weight x = k)).card = n.choose k := by
  classical
  have heq : (Finset.univ.filter (fun x : Word n => weight x = k)) =
      Erdos566.Retuned.booleanWordsOfWeight (Fin n) k := by
    ext x
    simp only [Erdos566.Retuned.booleanWordsOfWeight, Finset.mem_filter,
      Finset.mem_univ, true_and, Set.mem_setOf_eq, weight_eq_ones]
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).2
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  rw [heq]
  simpa using Erdos566.Retuned.booleanWordsOfWeight_card (Fin n) k

def coordinateFactor (b : Bool) : ℝ[X] := 1 + C (bitSign b true) * X

def productPolynomial {n : ℕ} (b : Word n) : ℝ[X] := ∏ i, coordinateFactor (b i)

theorem coordinateFactor_as_sum (b : Bool) :
    coordinateFactor b = ∑ x : Bool, C (bitSign b x) * X ^ (if x then 1 else 0) := by
  cases b <;> norm_num [coordinateFactor, bitSign, Fintype.univ_bool] <;> ring

theorem product_term {n : ℕ} (b x : Word n) :
    (∏ i, C (bitSign (b i) (x i)) * X ^ (if x i then 1 else 0)) =
      C (character b x) * X ^ weight x := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← weight_eq_sum]
  congr 1
  simp [character]

theorem productPolynomial_expansion {n : ℕ} (b : Word n) :
    productPolynomial b = ∑ x : Word n, C (character b x) * X ^ weight x := by
  unfold productPolynomial
  simp_rw [coordinateFactor_as_sum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact product_term b x

def sphereIndicator {n : ℕ} (k : ℕ) (x : Word n) : ℝ :=
  if weight x = k then 1 else 0

theorem productPolynomial_coefficient {n : ℕ} (b : Word n) (k : ℕ) :
    (productPolynomial b).coeff k = transform (sphereIndicator k) b := by
  rw [productPolynomial_expansion, finset_sum_coeff]
  unfold transform sphereIndicator
  apply Finset.sum_congr rfl
  intro x _
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hweight : weight x = k
  · simp [hweight]
  · simp [hweight, Ne.symm hweight]

theorem productPolynomial_generating {n : ℕ} (b : Word n) :
    productPolynomial b = Erdos566.Krawtchouk.generating (weight b) (n - weight b) := by
  classical
  have hfactor (i : Fin n) :
      coordinateFactor (b i) = if b i = true then (1 - X : ℝ[X]) else 1 + X := by
    cases b i <;> norm_num [coordinateFactor, bitSign] <;> ring
  have hcount : weight b + (Finset.univ.filter (fun i => b i ≠ true)).card = n := by
    simpa [weight] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun i => b i = true))
  have hnegative : (Finset.univ.filter (fun i => b i ≠ true)).card = n - weight b := by
    omega
  unfold productPolynomial
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [hnegative]
  rfl

theorem sphere_transform {n : ℕ} (b : Word n) (k : ℕ) :
    transform (sphereIndicator k) b =
      (Erdos566.Krawtchouk.generating (weight b) (n - weight b)).coeff k := by
  rw [← productPolynomial_coefficient, productPolynomial_generating]

theorem sphere_parseval (n k : ℕ) :
    (∑ b : Word n, transform (sphereIndicator k) b ^ 2) =
      (2 : ℝ) ^ n * (n.choose k : ℝ) := by
  rw [parseval]
  congr 1
  have hcount := weight_class_card n k
  unfold sphereIndicator
  simp only [ite_pow, one_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast hcount

theorem generating_coefficient_square_bound (n v k : ℕ) (hv : v ≤ n) :
    (n.choose v : ℝ) *
        (Erdos566.Krawtchouk.generating v (n - v)).coeff k ^ 2 ≤
      (2 : ℝ) ^ n * (n.choose k : ℝ) := by
  classical
  let value : ℝ := (Erdos566.Krawtchouk.generating v (n - v)).coeff k
  have hpoint (b : Word n) :
      (if weight b = v then value ^ 2 else 0) ≤ transform (sphereIndicator k) b ^ 2 := by
    by_cases hb : weight b = v
    · rw [if_pos hb, sphere_transform, hb]
    · rw [if_neg hb]
      exact sq_nonneg _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Word n)))
    (fun b _ => hpoint b)
  rw [sphere_parseval] at hsum
  rw [← Finset.sum_filter] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [weight_class_card] at hsum
  exact hsum

def ballIndicator {n : ℕ} (k : ℕ) (x : Word n) : ℝ :=
  if weight x ≤ k then 1 else 0

theorem ballIndicator_eq_sum {n : ℕ} (k : ℕ) (x : Word n) :
    ballIndicator k x = ∑ j ∈ Finset.range (k + 1), sphereIndicator j x := by
  simp [ballIndicator, sphereIndicator, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

theorem ball_transform_eq_sum {n : ℕ} (b : Word n) (k : ℕ) :
    transform (ballIndicator k) b =
      ∑ j ∈ Finset.range (k + 1), (productPolynomial b).coeff j := by
  calc
    transform (ballIndicator k) b =
        ∑ x : Word n, ∑ j ∈ Finset.range (k + 1), sphereIndicator j x * character b x := by
      unfold transform
      simp_rw [ballIndicator_eq_sum, Finset.sum_mul]
    _ = ∑ j ∈ Finset.range (k + 1), transform (sphereIndicator j) b := by
      rw [Finset.sum_comm]
      rfl
    _ = ∑ j ∈ Finset.range (k + 1), (productPolynomial b).coeff j := by
      simp_rw [productPolynomial_coefficient]

theorem sum_coeff_one_sub_X (p : ℝ[X]) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), ((1 - X) * p).coeff j) = p.coeff k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [sub_mul, one_mul, coeff_sub, coeff_X_mul]
      ring

theorem weight_zero_iff {n : ℕ} (b : Word n) : weight b = 0 ↔ b = (fun _ => false) := by
  constructor
  · intro hz
    funext i
    cases hbit : b i with
    | false => rfl
    | true =>
        have hi : i ∈ Finset.univ.filter (fun i => b i = true) := by simp [hbit]
        have hp := Finset.card_pos.mpr ⟨i, hi⟩
        change 0 < weight b at hp
        omega
  · intro h
    subst b
    simp [weight]

theorem ball_transform_nontrivial {n : ℕ} (b : Word n) (k : ℕ)
    (hb : b ≠ (fun _ => false)) :
    transform (ballIndicator k) b =
      (Erdos566.Krawtchouk.generating (weight b - 1) (n - weight b)).coeff k := by
  have hpos : 0 < weight b := Nat.pos_of_ne_zero (fun h => hb ((weight_zero_iff b).mp h))
  have hfactor : productPolynomial b =
      (1 - X) * Erdos566.Krawtchouk.generating (weight b - 1) (n - weight b) := by
    rw [productPolynomial_generating]
    unfold Erdos566.Krawtchouk.generating
    have hp : (1 - X : ℝ[X]) ^ weight b = (1 - X) ^ (weight b - 1) * (1 - X) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hp]
    ring
  rw [ball_transform_eq_sum, hfactor, sum_coeff_one_sub_X]

end

end Erdos566.CubeFourier

namespace Erdos566.Spectrum

noncomputable section

def dimension (m : ℕ) : ℕ := 40000 * m
def radius (m : ℕ) : ℕ := 17200 * m
def reducedDimension (m : ℕ) : ℕ := dimension m - 1

theorem reducedDimension_cast (m : ℕ) (hm : 0 < m) :
    (reducedDimension m : ℝ) = 40000 * (m : ℝ) - 1 := by
  unfold reducedDimension dimension
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem radius_cast (m : ℕ) : (radius m : ℝ) = 17200 * (m : ℝ) := by
  norm_num [radius]

theorem radius_reduced_le (m : ℕ) (hm : 0 < m) :
    radius m ≤ reducedDimension m := by
  unfold radius reducedDimension dimension
  omega

theorem root_separation (m : ℕ) (hm : 0 < m) :
    2 * Real.sqrt ((radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1)) <
      (4951 : ℝ) / 5000 * reducedDimension m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN := reducedDimension_cast m hm
  have hk := radius_cast m
  have hcap : (radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1) =
      392160000 * (m : ℝ) ^ 2 := by rw [hN, hk]; ring
  have hnonnegative : 0 ≤ (radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1) := by
    rw [hcap]
    positivity
  have hsquare := Real.sq_sqrt hnonnegative
  have hsqrt := Real.sqrt_nonneg
    ((radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1))
  have hgap : (radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1) <
      ((4951 : ℝ) / 10000 * reducedDimension m) ^ 2 := by
    rw [hcap, hN]
    nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (show (0 : ℝ) ≤ m by positivity)]
  have hright : (0 : ℝ) < (4951 : ℝ) / 10000 * reducedDimension m := by
    rw [hN]
    nlinarith
  nlinarith

theorem negative_coefficient_index_bounds (m v : ℕ) (hm : 0 < m)
    (hv : v ≤ reducedDimension m)
    (hnegative :
      (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) < 0) :
    (49 : ℝ) / 10000 ≤ (v : ℝ) / reducedDimension m ∧
      (v : ℝ) / reducedDimension m ≤ (9951 : ℝ) / 10000 := by
  have hkpos : 0 < radius m := by unfold radius; omega
  have hk : 2 * radius m ≤ v + (reducedDimension m - v) + 1 := by
    unfold radius reducedDimension dimension at *
    omega
  have heven : Even (radius m) := by unfold radius; exact ⟨8600 * m, by omega⟩
  have hroot := Krawtchouk.generating_negative_inside v (reducedDimension m - v)
    (radius m) hkpos hk heven hnegative
  rw [Nat.cast_sub hv] at hroot
  have hnormalized : |(reducedDimension m : ℝ) - 2 * v| <
      2 * Real.sqrt ((radius m : ℝ) * ((reducedDimension m : ℝ) - radius m + 1)) := by
    convert hroot using 1 <;> congr 1 <;> ring
  have hsep := root_separation m hm
  have hNpos : (0 : ℝ) < reducedDimension m := by
    rw [reducedDimension_cast m hm]
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have habs := abs_lt.mp hnormalized
  constructor
  · apply (le_div_iff₀ hNpos).mpr
    linarith
  · apply (div_le_iff₀ hNpos).mpr
    linarith

theorem negative_coefficient_entropy_lower (m v : ℕ) (hm : 0 < m)
    (hv : v ≤ reducedDimension m)
    (hnegative :
      (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) < 0) :
    (4464 : ℝ) / 100000 < Retuned.binaryEntropy ((v : ℝ) / reducedDimension m) := by
  obtain ⟨hlow, hhigh⟩ := negative_coefficient_index_bounds m v hm hv hnegative
  have hsmall : (4464 : ℝ) / 100000 < Retuned.binaryEntropy (49 / 10000) :=
    Erdos566.entropy_0049_bounds.1
  by_cases hhalf : (v : ℝ) / reducedDimension m ≤ (2 : ℝ)⁻¹
  · exact hsmall.trans_le (Retuned.binaryEntropy_mono_on_half (49 / 10000)
      ((v : ℝ) / reducedDimension m) (by norm_num) hlow hhalf)
  · have hcomp : (49 : ℝ) / 10000 ≤ 1 - (v : ℝ) / reducedDimension m := by linarith
    have hcompHalf : 1 - (v : ℝ) / reducedDimension m ≤ (2 : ℝ)⁻¹ := by linarith
    have hmono := Retuned.binaryEntropy_mono_on_half (49 / 10000)
      (1 - (v : ℝ) / reducedDimension m) (by norm_num) hcomp hcompHalf
    rw [Retuned.binaryEntropy_one_sub] at hmono
    exact hsmall.trans_le hmono

theorem radius_entropy_upper (m : ℕ) (hm : 1000 ≤ m) :
    Retuned.binaryEntropy ((radius m : ℝ) / reducedDimension m) < (98583 : ℝ) / 100000 := by
  have hmpos : 0 < m := by omega
  have hmR : (1000 : ℝ) ≤ m := by exact_mod_cast hm
  have hN := reducedDimension_cast m hmpos
  have hNpos : (0 : ℝ) < reducedDimension m := by rw [hN]; nlinarith
  have htau : (0 : ℝ) < Erdos566.tau := by norm_num [Erdos566.tau]
  have hratio : (radius m : ℝ) = Erdos566.tau * ((reducedDimension m : ℝ) + 1) := by
    rw [hN, radius_cast]
    norm_num [Erdos566.tau]
    ring
  have hdelta : (radius m : ℝ) / reducedDimension m - Erdos566.tau =
      Erdos566.tau / reducedDimension m := by
    field_simp [hNpos.ne']
    nlinarith only [hratio]
  have hdeltaPos : 0 ≤ Erdos566.tau / reducedDimension m := by positivity
  have hdeltaSmall : Erdos566.tau / reducedDimension m ≤ 1 / (Erdos566.baseSize : ℝ) := by
    apply (div_le_iff₀ hNpos).mpr
    rw [hN]
    norm_num [Erdos566.tau, Erdos566.baseSize]
    nlinarith
  have hqzero : 0 ≤ (radius m : ℝ) / reducedDimension m := by positivity
  have hqone : (radius m : ℝ) / reducedDimension m ≤ 1 := by
    norm_num [Erdos566.baseSize, Erdos566.tau] at hdeltaSmall hdelta
    linarith
  have hmodulus := Retuned.abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    ((radius m : ℝ) / reducedDimension m) Erdos566.tau hqzero hqone
    htau.le (by norm_num [Erdos566.tau])
  rw [hdelta, abs_of_nonneg hdeltaPos] at hmodulus
  have hmono := Retuned.binaryEntropy_mono_on_half
    (Erdos566.tau / reducedDimension m) (1 / (Erdos566.baseSize : ℝ))
    hdeltaPos hdeltaSmall (by norm_num [Erdos566.baseSize])
  have hsmall := Retuned.base_entropy_small
  have hbase : Retuned.binaryEntropy Erdos566.tau < (98582 : ℝ) / 100000 :=
    Erdos566.entropy_43_bounds.2
  have hdiff := (abs_le.mp hmodulus).2
  norm_num [Erdos566.baseSize] at hsmall hmono
  linarith

theorem eventually_dimension_le_exp :
    ∀ᶠ m : ℕ in Filter.atTop,
      (dimension m : ℝ) + 1 ≤
        Real.exp ((dimension m : ℝ) * Real.log 2 / 100000) := by
  have hrate : (0 : ℝ) < (2 / 5 : ℝ) * Real.log 2 := by
    positivity
  have hlimit := Retuned.exp_mul_div_nat_succ_tendsto_atTop
    ((2 / 5 : ℝ) * Real.log 2) hrate
  have hlarge := (Filter.tendsto_atTop.1 hlimit) 40000
  filter_upwards [hlarge] with m hm
  have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hproduct := (le_div_iff₀ hden).mp hm
  have hexponent : ((2 / 5 : ℝ) * Real.log 2) * m =
      (dimension m : ℝ) * Real.log 2 / 100000 := by
    norm_num [dimension]
    ring
  rw [hexponent] at hproduct
  norm_num [dimension] at hproduct ⊢
  linarith

theorem binEntropy_normalization (x : ℝ) :
    Real.binEntropy x = Retuned.binaryEntropy x * Real.log 2 := by
  unfold Retuned.binaryEntropy
  field_simp [Erdos566.log_two_pos.ne']

theorem coefficient_square_entropy_bound (n v k : ℕ) (hv : v ≤ n) (hk : k ≤ n)
    (lower upper : ℝ)
    (hlower : lower ≤ Retuned.binaryEntropy ((v : ℝ) / n))
    (hupper : Retuned.binaryEntropy ((k : ℝ) / n) ≤ upper) :
    (Krawtchouk.generating v (n - v)).coeff k ^ 2 ≤
      ((n : ℝ) + 1) * Real.exp ((1 + upper - lower) * n * Real.log 2) := by
  let value : ℝ := (Krawtchouk.generating v (n - v)).coeff k
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hrate : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  have hlowerExp :
      Real.exp (lower * n * Real.log 2) / ((n : ℝ) + 1) ≤ (n.choose v : ℝ) := by
    calc
      Real.exp (lower * n * Real.log 2) / ((n : ℝ) + 1) ≤
          Real.exp ((n : ℝ) * Real.binEntropy ((v : ℝ) / n)) / ((n : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right ?_ hden.le
        apply Real.exp_le_exp.mpr
        rw [binEntropy_normalization]
        nlinarith [mul_le_mul_of_nonneg_right hlower hrate]
      _ ≤ (n.choose v : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          Retuned.exp_binary_entropy_div_le_choose n v hv
  have hupperExp : (n.choose k : ℝ) ≤ Real.exp (upper * n * Real.log 2) := by
    calc
      (n.choose k : ℝ) ≤ Real.exp ((n : ℝ) * Real.binEntropy ((k : ℝ) / n)) :=
        Retuned.choose_le_exp_binary_entropy n k hk
      _ ≤ Real.exp (upper * n * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        rw [binEntropy_normalization]
        nlinarith [mul_le_mul_of_nonneg_right hupper hrate]
  have htwo : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hbound : value ^ 2 * (Real.exp (lower * n * Real.log 2) / ((n : ℝ) + 1)) ≤
      Real.exp ((1 + upper) * n * Real.log 2) := by
    calc
      value ^ 2 * (Real.exp (lower * n * Real.log 2) / ((n : ℝ) + 1)) ≤
          value ^ 2 * (n.choose v : ℝ) :=
        mul_le_mul_of_nonneg_left hlowerExp (sq_nonneg value)
      _ ≤ (2 : ℝ) ^ n * (n.choose k : ℝ) := by
        simpa only [value, mul_comm] using CubeFourier.generating_coefficient_square_bound n v k hv
      _ ≤ (2 : ℝ) ^ n * Real.exp (upper * n * Real.log 2) :=
        mul_le_mul_of_nonneg_left hupperExp (by positivity)
      _ = Real.exp ((1 + upper) * n * Real.log 2) := by
        rw [htwo, ← Real.exp_add]
        congr 1
        ring
  rw [← mul_div_assoc] at hbound
  have hscaled := (div_le_iff₀ hden).mp hbound
  apply (mul_le_mul_iff_of_pos_right (Real.exp_pos (lower * n * Real.log 2))).mp
  calc
    value ^ 2 * Real.exp (lower * n * Real.log 2) ≤
        Real.exp ((1 + upper) * n * Real.log 2) * ((n : ℝ) + 1) := hscaled
    _ = (((n : ℝ) + 1) * Real.exp ((1 + upper - lower) * n * Real.log 2)) *
        Real.exp (lower * n * Real.log 2) := by
      have hexp : Real.exp ((1 + upper) * n * Real.log 2) =
          Real.exp ((1 + upper - lower) * n * Real.log 2) *
            Real.exp (lower * n * Real.log 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

def negativeBound (m : ℕ) : ℝ :=
  Real.exp ((4853 : ℝ) / 5000 * dimension m * Real.log 2)

theorem negativeBound_pos (m : ℕ) : 0 < negativeBound m := Real.exp_pos _

theorem negative_coefficient_lower (m v : ℕ) (hm : 1000 ≤ m)
    (hv : v ≤ reducedDimension m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (hnegative : (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) < 0) :
    -negativeBound m ≤ (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) := by
  have hmpos : 0 < m := by omega
  have hlow := negative_coefficient_entropy_lower m v hmpos hv hnegative
  have hupp := radius_entropy_upper m hm
  have hraw := coefficient_square_entropy_bound (reducedDimension m) v (radius m)
    hv (radius_reduced_le m hmpos) ((4464 : ℝ) / 100000) ((98583 : ℝ) / 100000)
    hlow.le hupp.le
  have hdim : (reducedDimension m : ℝ) + 1 = dimension m := by
    rw [reducedDimension_cast m hmpos]
    norm_num [dimension]
  have hdimle : (reducedDimension m : ℝ) ≤ dimension m := by
    exact_mod_cast (Nat.sub_le (dimension m) 1)
  have hnorm : (1 + (98583 : ℝ) / 100000 - 4464 / 100000) = 194119 / 100000 := by
    norm_num
  rw [hnorm, hdim] at hraw
  have hexp : Real.exp ((194119 : ℝ) / 100000 * reducedDimension m * Real.log 2) ≤
      Real.exp ((194119 : ℝ) / 100000 * dimension m * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdimle (by norm_num)) Erdos566.log_two_pos.le
  have hsq : (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) ^ 2 ≤
      negativeBound m ^ 2 := by
    calc
      (Krawtchouk.generating v (reducedDimension m - v)).coeff (radius m) ^ 2 ≤
          (dimension m : ℝ) * Real.exp ((194119 : ℝ) / 100000 * reducedDimension m * Real.log 2) := hraw
      _ ≤ (dimension m : ℝ) * Real.exp ((194119 : ℝ) / 100000 * dimension m * Real.log 2) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000) *
          Real.exp ((194119 : ℝ) / 100000 * dimension m * Real.log 2) := by
        apply mul_le_mul_of_nonneg_right (le_trans (by linarith) hpoly) (Real.exp_pos _).le
      _ = negativeBound m ^ 2 := by
        unfold negativeBound
        rw [pow_two, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  nlinarith [negativeBound_pos m]

theorem spectrum_lower (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (b : CubeFourier.Word (dimension m)) :
    -negativeBound m ≤ CubeFourier.transform (CubeFourier.ballIndicator (radius m)) b := by
  by_cases hnegative : CubeFourier.transform (CubeFourier.ballIndicator (radius m)) b < 0
  · have hb : b ≠ (fun _ => false) := by
      intro heq
      rw [heq, CubeFourier.transform_zero] at hnegative
      have hnonnegative : (0 : ℝ) ≤ ∑ x : CubeFourier.Word (dimension m),
          CubeFourier.ballIndicator (radius m) x := by
        apply Finset.sum_nonneg
        intro x _
        unfold CubeFourier.ballIndicator
        split_ifs <;> norm_num
      linarith
    have hpositive : 0 < CubeFourier.weight b :=
      Nat.pos_of_ne_zero (fun h => hb ((CubeFourier.weight_zero_iff b).mp h))
    have hweight := CubeFourier.weight_le b
    have hv : CubeFourier.weight b - 1 ≤ reducedDimension m := by
      unfold reducedDimension
      omega
    have hdiff : reducedDimension m - (CubeFourier.weight b - 1) =
        dimension m - CubeFourier.weight b := by
      unfold reducedDimension
      omega
    rw [CubeFourier.ball_transform_nontrivial b (radius m) hb] at hnegative ⊢
    have hbound := negative_coefficient_lower m (CubeFourier.weight b - 1) hm hv hpoly
    rw [hdiff] at hbound
    exact hbound hnegative
  · have hn : 0 ≤ CubeFourier.transform (CubeFourier.ballIndicator (radius m)) b :=
      le_of_not_gt hnegative
    linarith [negativeBound_pos m]

theorem eventually_spectrum_lower :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ b : CubeFourier.Word (dimension m),
      -negativeBound m ≤ CubeFourier.transform (CubeFourier.ballIndicator (radius m)) b := by
  filter_upwards [eventually_dimension_le_exp, Filter.eventually_ge_atTop 1000] with m hpoly hm
  exact spectrum_lower m hm hpoly

def ballMass (m : ℕ) : ℝ :=
  CubeFourier.transform (CubeFourier.ballIndicator (radius m)) (fun _ : Fin (dimension m) => false)

theorem choose_le_ballMass (m : ℕ) : (Nat.choose (dimension m) (radius m) : ℝ) ≤ ballMass m := by
  classical
  have hsum : (∑ x : CubeFourier.Word (dimension m), CubeFourier.sphereIndicator (radius m) x) =
      (Nat.choose (dimension m) (radius m) : ℝ) := by
    unfold CubeFourier.sphereIndicator
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast CubeFourier.weight_class_card (dimension m) (radius m)
  rw [← hsum]
  unfold ballMass
  rw [CubeFourier.transform_zero]
  apply Finset.sum_le_sum
  intro x _
  unfold CubeFourier.sphereIndicator CubeFourier.ballIndicator
  by_cases hx : CubeFourier.weight x = radius m
  · simp [hx]
  · simp only [if_neg hx]
    split_ifs <;> norm_num

theorem ballMass_lower (m : ℕ) (hm : 0 < m) :
    Real.exp ((98581 : ℝ) / 100000 * dimension m * Real.log 2) /
        ((dimension m : ℝ) + 1) ≤ ballMass m := by
  have hk : radius m ≤ dimension m := by unfold radius dimension; omega
  have hM : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hratio : (radius m : ℝ) / dimension m = Erdos566.tau := by
    norm_num [radius, dimension, Erdos566.tau]
    field_simp
    norm_num
  have hbase : (98581 : ℝ) / 100000 ≤ Retuned.binaryEntropy Erdos566.tau :=
    Erdos566.entropy_43_bounds.1.le
  have hrate : 0 ≤ (dimension m : ℝ) * Real.log 2 := by positivity
  have hden : 0 < (dimension m : ℝ) + 1 := by positivity
  calc
    Real.exp ((98581 : ℝ) / 100000 * dimension m * Real.log 2) / ((dimension m : ℝ) + 1) ≤
        Real.exp ((dimension m : ℝ) * Real.binEntropy ((radius m : ℝ) / dimension m)) /
          ((dimension m : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right ?_ hden.le
      apply Real.exp_le_exp.mpr
      rw [hratio, binEntropy_normalization]
      nlinarith [mul_le_mul_of_nonneg_right hbase hrate]
    _ ≤ (Nat.choose (dimension m) (radius m) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Retuned.exp_binary_entropy_div_le_choose (dimension m) (radius m) hk
    _ ≤ ballMass m := choose_le_ballMass m

theorem ballMass_pos (m : ℕ) (hm : 0 < m) : 0 < ballMass m := by
  exact (div_pos (Real.exp_pos _) (by positivity)).trans_le (ballMass_lower m hm)

def spectralDecay (m : ℕ) : ℝ :=
  Real.exp (-((19 : ℝ) / 1250) * dimension m * Real.log 2)

theorem negativeBound_le_mass_decay (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    negativeBound m ≤ ballMass m * spectralDecay m := by
  have hden : 0 < (dimension m : ℝ) + 1 := by positivity
  have hmiddle : negativeBound m ≤
      Real.exp ((97061 : ℝ) / 100000 * dimension m * Real.log 2) /
        ((dimension m : ℝ) + 1) := by
    apply (le_div_iff₀ hden).mpr
    calc
      negativeBound m * ((dimension m : ℝ) + 1) ≤
          negativeBound m * Real.exp ((dimension m : ℝ) * Real.log 2 / 100000) :=
        mul_le_mul_of_nonneg_left hpoly (negativeBound_pos m).le
      _ = Real.exp ((97061 : ℝ) / 100000 * dimension m * Real.log 2) := by
        unfold negativeBound
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    negativeBound m ≤
        Real.exp ((97061 : ℝ) / 100000 * dimension m * Real.log 2) /
          ((dimension m : ℝ) + 1) := hmiddle
    _ = (Real.exp ((98581 : ℝ) / 100000 * dimension m * Real.log 2) /
        ((dimension m : ℝ) + 1)) * spectralDecay m := by
      unfold spectralDecay
      have hexp : Real.exp ((97061 : ℝ) / 100000 * dimension m * Real.log 2) =
          Real.exp ((98581 : ℝ) / 100000 * dimension m * Real.log 2) *
            Real.exp (-((19 : ℝ) / 1250) * dimension m * Real.log 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ ballMass m * spectralDecay m :=
      mul_le_mul_of_nonneg_right (ballMass_lower m hm) (Real.exp_pos _).le

theorem eventually_negativeBound_le_mass_decay :
    ∀ᶠ m : ℕ in Filter.atTop, negativeBound m ≤ ballMass m * spectralDecay m := by
  filter_upwards [eventually_dimension_le_exp, Filter.eventually_gt_atTop 0] with m hpoly hm
  exact negativeBound_le_mass_decay m hm hpoly

end

end Erdos566.Spectrum

open Finset

namespace Erdos566.CubeFourier

noncomputable section

def setIndicator {n : ℕ} (W : Finset (Word n)) (x : Word n) : ℝ :=
  if x ∈ W then 1 else 0

theorem sum_mul_indicator {n : ℕ} (W : Finset (Word n)) (f : Word n → ℝ) :
    (∑ x, f x * setIndicator W x) = ∑ x ∈ W, f x := by
  classical
  simp only [setIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun x => x ∈ W)) = W := by ext x; simp
  rw [hset]

theorem sum_indicator {n : ℕ} (W : Finset (Word n)) :
    (∑ x, setIndicator W x) = (W.card : ℝ) := by
  simpa using sum_mul_indicator W (fun _ => 1)

theorem sum_indicator_sq {n : ℕ} (W : Finset (Word n)) :
    (∑ x, setIndicator W x ^ 2) = (W.card : ℝ) := by
  have hpoint (x : Word n) : setIndicator W x ^ 2 = setIndicator W x := by
    unfold setIndicator
    split_ifs <;> norm_num
  simp_rw [hpoint]
  exact sum_indicator W

theorem xorWord_comm {n : ℕ} (x y : Word n) : xorWord x y = xorWord y x := by
  funext i
  unfold xorWord
  cases x i <;> cases y i <;> rfl

theorem hammingDist_eq_weight_xor {n : ℕ} (x y : Word n) :
    hammingDist x y = weight (xorWord x y) := by
  unfold hammingDist weight xorWord
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  cases x i <;> cases y i <;> decide

theorem convolution_change_variables {n : ℕ} (g f : Word n → ℝ) (x : Word n) :
    convolution g f x = ∑ y, g (xorWord y x) * f y := by
  unfold convolution
  apply Fintype.sum_equiv (translation x)
  intro z
  have hcancel : xorWord (xorWord x z) x = z := by
    rw [xorWord_comm, xorWord_self_cancel]
  change g z * f (xorWord z x) = g (xorWord (xorWord x z) x) * f (xorWord x z)
  rw [hcancel, xorWord_comm z x]

theorem convolution_indicator_count {n : ℕ} (W : Finset (Word n)) (k : ℕ) (x : Word n) :
    convolution (ballIndicator k) (setIndicator W) x =
      ((W.filter (fun y => hammingDist x y ≤ k)).card : ℝ) := by
  classical
  rw [convolution_change_variables, sum_mul_indicator]
  have hpoint (y : Word n) : ballIndicator k (xorWord y x) =
      if hammingDist x y ≤ k then (1 : ℝ) else 0 := by
    unfold ballIndicator
    rw [← hammingDist_eq_weight_xor, hammingDist_comm]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  simp

theorem ballGraph_adj_iff {n k : ℕ} (x y : Word n) :
    (Retuned.ballGraph n k).Adj x y ↔ x ≠ y ∧ hammingDist x y ≤ k := by
  simp only [Retuned.ballGraph, SimpleGraph.fromRel_adj, hammingDist_comm, or_self]

theorem closed_ball_filter {n : ℕ} (W : Finset (Word n)) (k : ℕ) (x : Word n) (hx : x ∈ W) :
    W.filter (fun y => hammingDist x y ≤ k) =
      insert x (Erdos566.neighborsWithin (Retuned.ballGraph n k) W x) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_insert, Erdos566.neighborsWithin,
    ballGraph_adj_iff]
  by_cases hxy : y = x
  · subst y
    simp [hx]
  · constructor
    · intro hy
      exact Or.inr ⟨hy.1, Ne.symm hxy, hy.2⟩
    · intro hy
      rcases hy with hy | hy
      · exact False.elim (hxy hy)
      · exact ⟨hy.1, hy.2.2⟩

theorem convolution_indicator_degree {n : ℕ} (W : Finset (Word n)) (k : ℕ) (x : Word n)
    (hx : x ∈ W) :
    convolution (ballIndicator k) (setIndicator W) x =
      (Erdos566.neighborsWithin (Retuned.ballGraph n k) W x).card + (1 : ℝ) := by
  classical
  rw [convolution_indicator_count, closed_ball_filter W k x hx]
  have hnot : x ∉ Erdos566.neighborsWithin (Retuned.ballGraph n k) W x := by
    simp [Erdos566.neighborsWithin]
  rw [Finset.card_insert_of_notMem hnot]
  push_cast
  rfl

theorem quadratic_indicator_degree_sum {n : ℕ} (W : Finset (Word n)) (k : ℕ) :
    quadratic (ballIndicator k) (setIndicator W) =
      (∑ x ∈ W, ((Erdos566.neighborsWithin (Retuned.ballGraph n k) W x).card : ℝ)) + W.card := by
  classical
  unfold quadratic
  simp_rw [mul_comm (setIndicator W _)]
  rw [sum_mul_indicator]
  calc
    (∑ x ∈ W, convolution (ballIndicator k) (setIndicator W) x) =
        ∑ x ∈ W, ((Erdos566.neighborsWithin (Retuned.ballGraph n k) W x).card + (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact convolution_indicator_degree W k x hx
    _ = _ := by simp [Finset.sum_add_distrib]

theorem exists_large_degree {n k : ℕ} (W : Finset (Word n)) (hW : W.Nonempty)
    (D bound : ℝ) (hbound : 0 ≤ bound)
    (hzero : transform (ballIndicator k) (fun _ : Fin n => false) = D)
    (hspectrum : ∀ b : Word n, -bound ≤ transform (ballIndicator k) b)
    (hlarge : 2 * bound * (2 : ℝ) ^ n ≤ D * W.card)
    (hloops : 4 * (2 : ℝ) ^ n ≤ D * W.card) :
    ∃ x ∈ W, (D / (4 * (2 : ℝ) ^ n)) * W.card ≤
      (Erdos566.neighborsWithin (Retuned.ballGraph n k) W x).card := by
  classical
  have hw : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
  have hQ : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hquadratic := quadratic_lower_bound (ballIndicator k) (setIndicator W)
    D bound hbound hzero hspectrum
  rw [sum_indicator, sum_indicator_sq, quadratic_indicator_degree_sum] at hquadratic
  have hlargeScaled := mul_le_mul_of_nonneg_right hlarge hw.le
  have hloopsScaled := mul_le_mul_of_nonneg_right hloops hw.le
  let degree : Word n → ℕ := fun x =>
    (Erdos566.neighborsWithin (Retuned.ballGraph n k) W x).card
  obtain ⟨x, hx, hmax⟩ := W.exists_max_image degree hW
  have hsum : (∑ y ∈ W, (degree y : ℝ)) ≤ W.card * (degree x : ℝ) := by
    calc
      (∑ y ∈ W, (degree y : ℝ)) ≤ ∑ _y ∈ W, (degree x : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        exact_mod_cast hmax y hy
      _ = W.card * (degree x : ℝ) := by simp
  change D * (W.card : ℝ) ^ 2 - bound * (2 : ℝ) ^ n * W.card ≤
    (2 : ℝ) ^ n * ((∑ y ∈ W, (degree y : ℝ)) + W.card) at hquadratic
  have hdegreeScaled : D * (W.card : ℝ) ^ 2 ≤
      4 * (2 : ℝ) ^ n * W.card * (degree x : ℝ) := by
    have hsumScaled := mul_le_mul_of_nonneg_left hsum hQ.le
    nlinarith only [hquadratic, hlargeScaled, hloopsScaled, hsumScaled]
  have hdegree : D * (W.card : ℝ) ≤ 4 * (2 : ℝ) ^ n * (degree x : ℝ) := by
    apply (mul_le_mul_iff_of_pos_right hw).mp
    nlinarith only [hdegreeScaled]
  refine ⟨x, hx, ?_⟩
  change D / (4 * (2 : ℝ) ^ n) * W.card ≤ (degree x : ℝ)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hdegree]

end

end Erdos566.CubeFourier

open Finset

namespace Erdos566.Containers

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

structure State (V : Type*) where
  remaining : Finset V
  fingerprint : Finset V

def initial : State V := ⟨Finset.univ, ∅⟩

def step (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) (state : State V) : State V := by
  classical
  exact if threshold ≤ state.remaining.card then
    let vertex := select state.remaining
    if vertex ∈ independent then
      ⟨state.remaining \ insert vertex (Erdos566.neighborsWithin G state.remaining vertex),
        insert vertex state.fingerprint⟩
    else ⟨state.remaining.erase vertex, state.fingerprint⟩
  else state

def run (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) : ℕ → State V
  | 0 => initial
  | t + 1 => step G threshold select independent (run G threshold select independent t)

theorem step_small (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) (state : State V) (hsmall : ¬ threshold ≤ state.remaining.card) :
    step G threshold select independent state = state := by
  classical
  simp only [step, hsmall, if_false]

theorem step_remaining_subset (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) (state : State V) :
    (step G threshold select independent state).remaining ⊆ state.remaining := by
  classical
  by_cases hactive : threshold ≤ state.remaining.card
  · by_cases hchosen : select state.remaining ∈ independent
    · simpa [step, hactive, hchosen] using
        (Finset.sdiff_subset : state.remaining \ insert (select state.remaining)
          (Erdos566.neighborsWithin G state.remaining (select state.remaining)) ⊆ state.remaining)
    · simpa [step, hactive, hchosen] using Finset.erase_subset (select state.remaining) state.remaining
  · simp [step, hactive]

theorem step_fingerprint_subset (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) (state : State V) :
    state.fingerprint ⊆ (step G threshold select independent state).fingerprint := by
  classical
  by_cases hactive : threshold ≤ state.remaining.card
  · by_cases hchosen : select state.remaining ∈ independent
    · simpa [step, hactive, hchosen] using
        Finset.subset_insert (select state.remaining) state.fingerprint
    · simp [step, hactive, hchosen]
  · simp [step, hactive]

theorem step_card_lt (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (independent : Finset V) (state : State V)
    (hactive : threshold ≤ state.remaining.card)
    (hselect : select state.remaining ∈ state.remaining) :
    (step G threshold select independent state).remaining.card < state.remaining.card := by
  classical
  unfold step
  simp only [hactive, if_true]
  split_ifs
  · have hsubset : state.remaining \ insert (select state.remaining)
          (Erdos566.neighborsWithin G state.remaining (select state.remaining)) ⊆
        state.remaining.erase (select state.remaining) := by
      intro vertex hvertex
      have hparts := Finset.mem_sdiff.mp hvertex
      exact Finset.mem_erase.mpr
        ⟨fun heq => hparts.2 (heq ▸ Finset.mem_insert_self _ _), hparts.1⟩
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_erase_of_mem hselect] at hcard
    have hpositive := Finset.card_pos.mpr ⟨select state.remaining, hselect⟩
    exact lt_of_le_of_lt hcard (by omega)
  · rw [Finset.card_erase_of_mem hselect]
    have hpositive := Finset.card_pos.mpr ⟨select state.remaining, hselect⟩
    omega

theorem active_card_bound (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (hselect : ∀ remaining : Finset V, threshold ≤ remaining.card → select remaining ∈ remaining)
    (independent : Finset V) (t : ℕ) :
    threshold ≤ (run G threshold select independent t).remaining.card →
      (run G threshold select independent t).remaining.card + t ≤ Fintype.card V := by
  classical
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
      intro hactive
      by_cases hprev : threshold ≤ (run G threshold select independent t).remaining.card
      · have hbound := ih hprev
        have hdrop := step_card_lt G threshold select independent
          (run G threshold select independent t) hprev (hselect _ hprev)
        change (step G threshold select independent (run G threshold select independent t)).remaining.card +
          (t + 1) ≤ Fintype.card V
        omega
      · have hfixed := step_small G threshold select independent
          (run G threshold select independent t) hprev
        change threshold ≤ (step G threshold select independent
          (run G threshold select independent t)).remaining.card at hactive
        rw [hfixed] at hactive
        exact False.elim (hprev hactive)

theorem run_stops (G : SimpleGraph V) (threshold : ℕ) (hthreshold : 0 < threshold)
    (select : Finset V → V)
    (hselect : ∀ remaining : Finset V, threshold ≤ remaining.card → select remaining ∈ remaining)
    (independent : Finset V) :
    (run G threshold select independent (Fintype.card V)).remaining.card < threshold := by
  by_contra hnot
  have hactive := le_of_not_gt hnot
  have hbound := active_card_bound G threshold select hselect independent (Fintype.card V) hactive
  omega

def Independent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y

theorem step_fingerprint_subset_input (G : SimpleGraph V) (threshold : ℕ)
    (select : Finset V → V) (I : Finset V) (state : State V)
    (hF : state.fingerprint ⊆ I) :
    (step G threshold select I state).fingerprint ⊆ I := by
  classical
  by_cases hactive : threshold ≤ state.remaining.card
  · by_cases hchosen : select state.remaining ∈ I
    · simpa [step, hactive, hchosen] using (Finset.insert_subset_iff.mpr ⟨hchosen, hF⟩)
    · simpa [step, hactive, hchosen] using hF
  · simpa [step, hactive] using hF

theorem step_covers (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (I : Finset V) (hI : Independent G I) (state : State V)
    (hcover : I ⊆ state.fingerprint ∪ state.remaining) :
    I ⊆ (step G threshold select I state).fingerprint ∪
      (step G threshold select I state).remaining := by
  classical
  by_cases hactive : threshold ≤ state.remaining.card
  · by_cases hchosen : select state.remaining ∈ I
    · simp only [step, hactive, hchosen, if_true]
      intro y hy
      rcases Finset.mem_union.mp (hcover hy) with hyF | hyW
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hyF)
      · by_cases heq : y = select state.remaining
        · exact Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inl heq))
        · apply Finset.mem_union_right
          apply Finset.mem_sdiff.mpr
          refine ⟨hyW, ?_⟩
          intro hclosed
          rcases Finset.mem_insert.mp hclosed with heq' | hadj
          · exact heq heq'
          · exact hI (select state.remaining) hchosen y hy
              ((Finset.mem_filter.mp hadj).2)
    · simp only [step, hactive, hchosen, if_true, if_false]
      intro y hy
      rcases Finset.mem_union.mp (hcover hy) with hyF | hyW
      · exact Finset.mem_union_left _ hyF
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
          ⟨fun heq => hchosen (heq ▸ hy), hyW⟩)
  · simpa [step, hactive] using hcover

theorem step_disjoint (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (hselect : ∀ remaining : Finset V, threshold ≤ remaining.card → select remaining ∈ remaining)
    (I : Finset V) (state : State V) (hdisjoint : Disjoint state.fingerprint state.remaining) :
    Disjoint (step G threshold select I state).fingerprint
      (step G threshold select I state).remaining := by
  classical
  by_cases hactive : threshold ≤ state.remaining.card
  · by_cases hchosen : select state.remaining ∈ I
    · simp only [step, hactive, hchosen, if_true]
      apply Finset.disjoint_left.mpr
      intro y hyF hyW
      have hyW' := Finset.mem_sdiff.mp hyW
      rcases Finset.mem_insert.mp hyF with heq | hyF'
      · exact hyW'.2 (Finset.mem_insert.mpr (Or.inl heq))
      · exact Finset.disjoint_left.mp hdisjoint hyF' hyW'.1
    · simp only [step, hactive, hchosen, if_true, if_false]
      exact hdisjoint.mono_right (Finset.erase_subset _ _)
  · simpa [step, hactive] using hdisjoint

theorem run_fingerprint_subset_input (G : SimpleGraph V) (threshold : ℕ)
    (select : Finset V → V) (I : Finset V) (t : ℕ) :
    (run G threshold select I t).fingerprint ⊆ I := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih => exact step_fingerprint_subset_input G threshold select I _ ih

theorem run_covers (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (I : Finset V) (hI : Independent G I) (t : ℕ) :
    I ⊆ (run G threshold select I t).fingerprint ∪ (run G threshold select I t).remaining := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih => exact step_covers G threshold select I hI _ ih

theorem run_disjoint (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (hselect : ∀ remaining : Finset V, threshold ≤ remaining.card → select remaining ∈ remaining)
    (I : Finset V) (t : ℕ) :
    Disjoint (run G threshold select I t).fingerprint (run G threshold select I t).remaining := by
  induction t with
  | zero => simp [run, initial]
  | succ t ih => exact step_disjoint G threshold select hselect I _ ih

theorem run_fingerprint_monotone (G : SimpleGraph V) (threshold : ℕ)
    (select : Finset V → V) (I : Finset V) :
    Monotone (fun t => (run G threshold select I t).fingerprint) := by
  apply monotone_nat_of_le_succ
  intro t
  exact step_fingerprint_subset G threshold select I _

theorem recorded_step_bounds (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (I : Finset V) (state : State V) (rate : ℝ)
    (hactive : threshold ≤ state.remaining.card) (hchosen : select state.remaining ∈ I)
    (hselect : select state.remaining ∈ state.remaining)
    (hdisjoint : Disjoint state.fingerprint state.remaining)
    (hdegree : rate * state.remaining.card ≤
      (Erdos566.neighborsWithin G state.remaining (select state.remaining)).card) :
    (step G threshold select I state).fingerprint.card = state.fingerprint.card + 1 ∧
      ((step G threshold select I state).remaining.card : ℝ) ≤
        (1 - rate) * state.remaining.card := by
  classical
  let vertex := select state.remaining
  let neighbors := Erdos566.neighborsWithin G state.remaining vertex
  have hnotF : vertex ∉ state.fingerprint := by
    intro hmem
    exact Finset.disjoint_left.mp hdisjoint hmem hselect
  have hnotN : vertex ∉ neighbors := by simp [neighbors, Erdos566.neighborsWithin]
  have hsubset : insert vertex neighbors ⊆ state.remaining := by
    intro y hy
    rcases Finset.mem_insert.mp hy with heq | hy
    · exact heq ▸ hselect
    · exact (Finset.mem_filter.mp hy).1
  have hcardLe := Finset.card_le_card hsubset
  have hcard : ((state.remaining \ insert vertex neighbors).card : ℝ) =
      (state.remaining.card : ℝ) - ((insert vertex neighbors).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsubset, Nat.cast_sub hcardLe]
  rw [Finset.card_insert_of_notMem hnotN] at hcard
  push_cast at hcard
  constructor
  · simpa [step, hactive, hchosen, vertex] using Finset.card_insert_of_notMem hnotF
  · change ((step G threshold select I state).remaining.card : ℝ) ≤ _
    simpa only [step, hactive, hchosen, if_true] using
      (show ((state.remaining \ insert vertex neighbors).card : ℝ) ≤
        (1 - rate) * state.remaining.card by
        change rate * state.remaining.card ≤ (neighbors.card : ℝ) at hdegree
        nlinarith only [hcard, hdegree])

theorem run_exponential_bound (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (rate : ℝ) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hselect : ∀ W : Finset V, threshold ≤ W.card → select W ∈ W)
    (hdegree : ∀ W : Finset V, threshold ≤ W.card →
      rate * W.card ≤ (Erdos566.neighborsWithin G W (select W)).card)
    (I : Finset V) (t : ℕ) :
    ((run G threshold select I t).remaining.card : ℝ) ≤
      Fintype.card V * Real.exp (-rate * (run G threshold select I t).fingerprint.card) := by
  classical
  induction t with
  | zero => simp [run, initial]
  | succ t ih =>
      let state := run G threshold select I t
      change ((step G threshold select I state).remaining.card : ℝ) ≤
        Fintype.card V * Real.exp (-rate * (step G threshold select I state).fingerprint.card)
      change (state.remaining.card : ℝ) ≤
        Fintype.card V * Real.exp (-rate * state.fingerprint.card) at ih
      by_cases hactive : threshold ≤ state.remaining.card
      · by_cases hchosen : select state.remaining ∈ I
        · have hrecord := recorded_step_bounds G threshold select I state rate hactive hchosen
            (hselect _ hactive) (run_disjoint G threshold select hselect I t) (hdegree _ hactive)
          have hF : ((step G threshold select I state).fingerprint.card : ℝ) =
              (state.fingerprint.card : ℝ) + 1 := by exact_mod_cast hrecord.1
          rw [hF]
          have hexp : 1 - rate ≤ Real.exp (-rate) := by
            have h := Real.add_one_le_exp (-rate)
            linarith
          have hexpId : Real.exp (-rate * ((state.fingerprint.card : ℝ) + 1)) =
              Real.exp (-rate) * Real.exp (-rate * state.fingerprint.card) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            ((step G threshold select I state).remaining.card : ℝ) ≤
                (1 - rate) * state.remaining.card := hrecord.2
            _ ≤ (1 - rate) * (Fintype.card V * Real.exp (-rate * state.fingerprint.card)) :=
              mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hrateOne)
            _ ≤ Real.exp (-rate) * (Fintype.card V * Real.exp (-rate * state.fingerprint.card)) :=
              mul_le_mul_of_nonneg_right hexp (by positivity)
            _ = Fintype.card V * Real.exp (-rate * ((state.fingerprint.card : ℝ) + 1)) := by
              rw [hexpId]
              ring
        · have hsubset := step_remaining_subset G threshold select I state
          have hcard : ((step G threshold select I state).remaining.card : ℝ) ≤ state.remaining.card := by
            exact_mod_cast Finset.card_le_card hsubset
          simpa [step, hactive, hchosen] using hcard.trans ih
      · simpa [step, hactive] using ih

theorem run_fingerprint_card_bound [Nonempty V]
    (G : SimpleGraph V) (threshold : ℕ) (hthreshold : 0 < threshold)
    (select : Finset V → V) (rate : ℝ) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hselect : ∀ W : Finset V, threshold ≤ W.card → select W ∈ W)
    (hdegree : ∀ W : Finset V, threshold ≤ W.card →
      rate * W.card ≤ (Erdos566.neighborsWithin G W (select W)).card)
    (I : Finset V) (t : ℕ) :
    ((run G threshold select I t).fingerprint.card : ℝ) ≤
      1 + Real.log (Fintype.card V) / rate := by
  classical
  have hQnat : 0 < Fintype.card V := Fintype.card_pos
  have hQ : (0 : ℝ) < Fintype.card V := by exact_mod_cast hQnat
  have hlog : 0 ≤ Real.log (Fintype.card V : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hQnat)
  induction t with
  | zero =>
      simp only [run, initial, Finset.card_empty, Nat.cast_zero]
      linarith [div_nonneg hlog hrate.le]
  | succ t ih =>
      let state := run G threshold select I t
      change ((step G threshold select I state).fingerprint.card : ℝ) ≤ _
      change (state.fingerprint.card : ℝ) ≤ _ at ih
      by_cases hactive : threshold ≤ state.remaining.card
      · by_cases hchosen : select state.remaining ∈ I
        · have hrecord := recorded_step_bounds G threshold select I state rate hactive hchosen
            (hselect _ hactive) (run_disjoint G threshold select hselect I t) (hdegree _ hactive)
          have hW : (1 : ℝ) ≤ state.remaining.card := by
            have hnat : 1 ≤ state.remaining.card := by omega
            exact_mod_cast hnat
          have hexponential := run_exponential_bound G threshold select rate hrate hrateOne
            hselect hdegree I t
          have hproduct : (1 : ℝ) ≤ Fintype.card V * Real.exp (-rate * state.fingerprint.card) :=
            hW.trans hexponential
          have hlogarithm := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hproduct
          rw [Real.log_one, Real.log_mul hQ.ne' (Real.exp_pos _).ne', Real.log_exp] at hlogarithm
          have hF : (state.fingerprint.card : ℝ) ≤ Real.log (Fintype.card V) / rate := by
            apply (le_div_iff₀ hrate).mpr
            nlinarith only [hlogarithm]
          rw [hrecord.1]
          push_cast
          linarith
        · simpa [step, hactive, hchosen] using ih
      · simpa [step, hactive] using ih

theorem run_replay (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V)
    (I : Finset V) (t : ℕ) (ht : t ≤ Fintype.card V) :
    run G threshold select (run G threshold select I (Fintype.card V)).fingerprint t =
      run G threshold select I t := by
  classical
  let F := (run G threshold select I (Fintype.card V)).fingerprint
  have hFI : F ⊆ I := run_fingerprint_subset_input G threshold select I _
  induction t with
  | zero => rfl
  | succ t ih =>
      have hprevious := ih (by omega)
      change step G threshold select F (run G threshold select F t) =
        step G threshold select I (run G threshold select I t)
      rw [hprevious]
      let state := run G threshold select I t
      change step G threshold select F state = step G threshold select I state
      by_cases hactive : threshold ≤ state.remaining.card
      · have hiff : select state.remaining ∈ F ↔ select state.remaining ∈ I := by
          constructor
          · exact fun h => hFI h
          · intro hchosen
            have hnext : select state.remaining ∈
                (run G threshold select I (t + 1)).fingerprint := by
              change select state.remaining ∈ (step G threshold select I state).fingerprint
              simp [step, hactive, hchosen]
            exact run_fingerprint_monotone G threshold select I ht hnext
        by_cases hchosen : select state.remaining ∈ I
        · have hchosenF := hiff.mpr hchosen
          simp [step, hactive, hchosen, hchosenF]
        · have hchosenF : select state.remaining ∉ F := fun h => hchosen (hiff.mp h)
          simp [step, hactive, hchosen, hchosenF]
      · simp [step, hactive]

def container (G : SimpleGraph V) (threshold : ℕ) (select : Finset V → V) (F : Finset V) : Finset V :=
  (run G threshold select F (Fintype.card V)).remaining

theorem independent_subset_container (G : SimpleGraph V) (threshold : ℕ)
    (select : Finset V → V) (I : Finset V) (hI : Independent G I) :
    I ⊆ (run G threshold select I (Fintype.card V)).fingerprint ∪
      container G threshold select (run G threshold select I (Fintype.card V)).fingerprint := by
  have hcover := run_covers G threshold select I hI (Fintype.card V)
  unfold container
  rw [run_replay G threshold select I (Fintype.card V) le_rfl]
  exact hcover

theorem container_card_lt (G : SimpleGraph V) (threshold : ℕ) (hthreshold : 0 < threshold)
    (select : Finset V → V)
    (hselect : ∀ remaining : Finset V, threshold ≤ remaining.card → select remaining ∈ remaining)
    (F : Finset V) : (container G threshold select F).card < threshold :=
  run_stops G threshold hthreshold select hselect F

def candidateFingerprints (limit : ℕ) : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter (fun F => F.card ≤ limit)

theorem candidateFingerprints_card_le [Nonempty V] (limit : ℕ) :
    (candidateFingerprints (V := V) limit).card ≤
      (limit + 1) * Fintype.card V ^ limit := by
  classical
  have hsubset : candidateFingerprints (V := V) limit ⊆
      (Finset.range (limit + 1)).biUnion (fun k => (Finset.univ : Finset V).powersetCard k) := by
    intro F hF
    have hlimit : F.card ≤ limit := (Finset.mem_filter.mp hF).2
    apply Finset.mem_biUnion.mpr
    refine ⟨F.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  have hQ : 1 ≤ Fintype.card V := Fintype.card_pos
  calc
    (candidateFingerprints (V := V) limit).card ≤
        ((Finset.range (limit + 1)).biUnion (fun k => (Finset.univ : Finset V).powersetCard k)).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ k ∈ Finset.range (limit + 1), ((Finset.univ : Finset V).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (limit + 1), (Fintype.card V).choose k := by simp
    _ ≤ ∑ _k ∈ Finset.range (limit + 1), Fintype.card V ^ limit := by
      apply Finset.sum_le_sum
      intro k hk
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hQ (by
        have hk' := Finset.mem_range.mp hk
        omega))
    _ = (limit + 1) * Fintype.card V ^ limit := by simp

end

end Erdos566.Containers

namespace Erdos566.Spectrum

noncomputable section

def containerThreshold (m : ℕ) : ℕ := 2 ^ (39400 * m)
def degreeRate (m : ℕ) : ℝ := ballMass m / (4 * (2 : ℝ) ^ dimension m)
def fingerprintBound (m : ℕ) : ℝ :=
  1 + Real.log ((2 : ℝ) ^ dimension m) / degreeRate m

theorem power_two_as_exp (n : ℕ) :
    ((2 ^ n : ℕ) : ℝ) = Real.exp ((n : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  norm_cast

theorem cubeOrder_as_exp (m : ℕ) :
    (2 : ℝ) ^ dimension m = Real.exp ((dimension m : ℝ) * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem containerThreshold_as_exp (m : ℕ) :
    (containerThreshold m : ℝ) = Real.exp ((197 : ℝ) / 200 * dimension m * Real.log 2) := by
  unfold containerThreshold
  rw [power_two_as_exp]
  congr 1
  norm_num [dimension]
  ring

theorem containerThreshold_pos (m : ℕ) : 0 < containerThreshold m := by
  unfold containerThreshold
  positivity

theorem ballMass_upper (m : ℕ) : ballMass m ≤ (2 : ℝ) ^ dimension m := by
  unfold ballMass
  rw [CubeFourier.transform_zero]
  calc
    (∑ x : CubeFourier.Word (dimension m), CubeFourier.ballIndicator (radius m) x) ≤
        ∑ _x : CubeFourier.Word (dimension m), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      unfold CubeFourier.ballIndicator
      split_ifs <;> norm_num
    _ = (2 : ℝ) ^ dimension m := by simp [CubeFourier.Word]

theorem degreeRate_pos (m : ℕ) (hm : 0 < m) : 0 < degreeRate m :=
  div_pos (ballMass_pos m hm) (by positivity)

theorem degreeRate_le_one (m : ℕ) : degreeRate m ≤ 1 := by
  unfold degreeRate
  apply (div_le_one (by positivity)).mpr
  have hupper := ballMass_upper m
  nlinarith [show (0 : ℝ) < 2 ^ dimension m by positivity]

theorem ballMass_clean_lower (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    Real.exp ((4929 : ℝ) / 5000 * dimension m * Real.log 2) ≤ ballMass m := by
  have hden : (0 : ℝ) < (dimension m : ℝ) + 1 := by positivity
  apply le_trans _ (ballMass_lower m hm)
  apply (le_div_iff₀ hden).mpr
  calc
    Real.exp ((4929 : ℝ) / 5000 * dimension m * Real.log 2) * ((dimension m : ℝ) + 1) ≤
        Real.exp ((4929 : ℝ) / 5000 * dimension m * Real.log 2) *
          Real.exp ((dimension m : ℝ) * Real.log 2 / 100000) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = Real.exp ((98581 : ℝ) / 100000 * dimension m * Real.log 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem decay_times_order (m : ℕ) (hm : 0 < m) :
    2 * (2 : ℝ) ^ dimension m * spectralDecay m ≤ containerThreshold m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [cubeOrder_as_exp, containerThreshold_as_exp]
  unfold spectralDecay
  have hleft : 2 * Real.exp ((dimension m : ℝ) * Real.log 2) *
      Real.exp (-((19 : ℝ) / 1250) * dimension m * Real.log 2) =
      Real.exp ((1 + (1 - (19 : ℝ) / 1250) * dimension m) * Real.log 2) := by
    rw [show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],
      ← Real.exp_add, ← Real.exp_add]
    simp only [Real.log_exp]
    congr 1
    ring
  rw [hleft]
  apply Real.exp_le_exp.mpr
  have hcoeff : 1 + (1 - (19 : ℝ) / 1250) * dimension m ≤
      (197 : ℝ) / 200 * dimension m := by
    norm_num [dimension]
    nlinarith
  exact mul_le_mul_of_nonneg_right hcoeff Erdos566.log_two_pos.le

theorem mass_times_threshold (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    4 * (2 : ℝ) ^ dimension m ≤ ballMass m * containerThreshold m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmass := ballMass_clean_lower m hm hpoly
  rw [cubeOrder_as_exp, containerThreshold_as_exp]
  calc
    4 * Real.exp ((dimension m : ℝ) * Real.log 2) ≤
        Real.exp (((4929 : ℝ) / 5000 + 197 / 200) * dimension m * Real.log 2) := by
      have hfour : (4 : ℝ) = Real.exp (2 * Real.log 2) := by
        rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
          Real.exp_add, Real.exp_log (by norm_num)]
        norm_num
      rw [hfour, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoeff : 2 + (dimension m : ℝ) ≤
          ((4929 : ℝ) / 5000 + 197 / 200) * dimension m := by
        norm_num [dimension]
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcoeff Erdos566.log_two_pos.le]
    _ = Real.exp ((4929 : ℝ) / 5000 * dimension m * Real.log 2) *
        Real.exp ((197 : ℝ) / 200 * dimension m * Real.log 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ ballMass m * Real.exp ((197 : ℝ) / 200 * dimension m * Real.log 2) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le

theorem exists_degree_in_large_set (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (W : Finset (CubeFourier.Word (dimension m)))
    (hW : containerThreshold m ≤ W.card) :
    ∃ x ∈ W, degreeRate m * W.card ≤
      (Erdos566.neighborsWithin (Retuned.ballGraph (dimension m) (radius m)) W x).card := by
  have hmpos : 0 < m := by omega
  have hmasspos := ballMass_pos m hmpos
  have hWreal : (containerThreshold m : ℝ) ≤ W.card := by exact_mod_cast hW
  have hnonempty : W.Nonempty := Finset.card_pos.mp
    ((containerThreshold_pos m).trans_le hW)
  have hdecay := negativeBound_le_mass_decay m hmpos hpoly
  have hmassW := mul_le_mul_of_nonneg_left hWreal hmasspos.le
  have hlarge : 2 * negativeBound m * (2 : ℝ) ^ dimension m ≤ ballMass m * W.card := by
    calc
      2 * negativeBound m * (2 : ℝ) ^ dimension m ≤
          2 * (ballMass m * spectralDecay m) * (2 : ℝ) ^ dimension m := by
        nlinarith [mul_le_mul_of_nonneg_right hdecay (show 0 ≤ 2 * (2 : ℝ) ^ dimension m by positivity)]
      _ = ballMass m * (2 * (2 : ℝ) ^ dimension m * spectralDecay m) := by ring
      _ ≤ ballMass m * containerThreshold m :=
        mul_le_mul_of_nonneg_left (decay_times_order m hmpos) hmasspos.le
      _ ≤ ballMass m * W.card := hmassW
  have hloops : 4 * (2 : ℝ) ^ dimension m ≤ ballMass m * W.card :=
    (mass_times_threshold m hmpos hpoly).trans hmassW
  exact CubeFourier.exists_large_degree W hnonempty (ballMass m) (negativeBound m)
    (negativeBound_pos m).le rfl (spectrum_lower m hm hpoly) hlarge hloops

def selectCube (m : ℕ) (W : Finset (CubeFourier.Word (dimension m))) :
    CubeFourier.Word (dimension m) := by
  classical
  exact if hW : W.Nonempty then
    Classical.choose (W.exists_max_image
      (fun x => (Erdos566.neighborsWithin (Retuned.ballGraph (dimension m) (radius m)) W x).card) hW)
  else fun _ => false

theorem selectCube_mem (m : ℕ) (W : Finset (CubeFourier.Word (dimension m)))
    (hW : containerThreshold m ≤ W.card) : selectCube m W ∈ W := by
  classical
  have hnonempty : W.Nonempty := Finset.card_pos.mp ((containerThreshold_pos m).trans_le hW)
  simp only [selectCube, hnonempty, dif_pos]
  exact (Classical.choose_spec (W.exists_max_image
    (fun x => (Erdos566.neighborsWithin (Retuned.ballGraph (dimension m) (radius m)) W x).card)
    hnonempty)).1

theorem selectCube_degree (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (W : Finset (CubeFourier.Word (dimension m))) (hW : containerThreshold m ≤ W.card) :
    degreeRate m * W.card ≤
      (Erdos566.neighborsWithin (Retuned.ballGraph (dimension m) (radius m)) W (selectCube m W)).card := by
  classical
  obtain ⟨x, hx, hdegree⟩ := exists_degree_in_large_set m hm hpoly W hW
  have hnonempty : W.Nonempty := ⟨x, hx⟩
  have hmax := (Classical.choose_spec (W.exists_max_image
    (fun x => (Erdos566.neighborsWithin (Retuned.ballGraph (dimension m) (radius m)) W x).card)
    hnonempty)).2 x hx
  apply hdegree.trans
  simp only [selectCube, hnonempty, dif_pos]
  exact_mod_cast hmax

def cubeContainer (m : ℕ) (F : Finset (CubeFourier.Word (dimension m))) :
    Finset (CubeFourier.Word (dimension m)) :=
  Containers.container (Retuned.ballGraph (dimension m) (radius m))
    (containerThreshold m) (selectCube m) F

theorem cubeContainer_small (m : ℕ) (F : Finset (CubeFourier.Word (dimension m))) :
    (cubeContainer m F).card < containerThreshold m := by
  exact Containers.container_card_lt _ _ (containerThreshold_pos m) _ (selectCube_mem m) F

def fingerprintLimit (m : ℕ) : ℕ := ⌈fingerprintBound m⌉₊

theorem independent_container_cover (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (I : Finset (CubeFourier.Word (dimension m)))
    (hI : Containers.Independent (Retuned.ballGraph (dimension m) (radius m)) I) :
    ∃ F ∈ Containers.candidateFingerprints (fingerprintLimit m),
      F ⊆ I ∧ I ⊆ F ∪ cubeContainer m F := by
  classical
  let G := Retuned.ballGraph (dimension m) (radius m)
  let F := (Containers.run G (containerThreshold m) (selectCube m) I
    (Fintype.card (CubeFourier.Word (dimension m)))).fingerprint
  have hmpos : 0 < m := by omega
  have hbound := Containers.run_fingerprint_card_bound G (containerThreshold m)
    (containerThreshold_pos m) (selectCube m) (degreeRate m) (degreeRate_pos m hmpos)
    (degreeRate_le_one m) (selectCube_mem m) (selectCube_degree m hm hpoly) I
    (Fintype.card (CubeFourier.Word (dimension m)))
  have hFreal : (F.card : ℝ) ≤ fingerprintBound m := by
    simpa only [F, fingerprintBound, CubeFourier.Word, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using hbound
  have hFcard : F.card ≤ fingerprintLimit m := by
    have h := hFreal.trans (Nat.le_ceil (fingerprintBound m))
    exact_mod_cast h
  refine ⟨F, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hFcard⟩, ?_, ?_⟩
  · exact Containers.run_fingerprint_subset_input G (containerThreshold m) (selectCube m) I _
  · exact Containers.independent_subset_container G (containerThreshold m) (selectCube m) I hI

end

end Erdos566.Spectrum

open Finset MeasureTheory

namespace Erdos566.Retuned

noncomputable section

def sideEmbedding {dimension : ℕ} (side : Bool) : HammingWord dimension ↪ Bool × HammingWord dimension where
  toFun := fun word => (side, word)
  inj' := fun _ _ h => congrArg Prod.snd h

def containsWords {dimension : ℕ} (side : Bool) (W : Finset (HammingWord dimension)) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ word ∈ W, (side, word) ∈ retained}

def retainedWords {dimension : ℕ} (side : Bool) (W : Finset (HammingWord dimension))
    (retained : Set (Bool × HammingWord dimension)) : Finset (HammingWord dimension) := by
  classical
  exact W.filter (fun word => (side, word) ∈ retained)

theorem containsWords_probability {dimension : ℕ} (side : Bool) (W : Finset (HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real (containsWords side W) =
      hammingRetentionProbability dimension ^ W.card := by
  classical
  have hevent : containsWords side W =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ W.map (sideEmbedding side), vertex ∈ retained} := by
    ext retained
    constructor
    · intro h vertex hvertex
      obtain ⟨word, hword, rfl⟩ := Finset.mem_map.mp hvertex
      exact h word hword
    · intro h word hword
      exact h (side, word) (Finset.mem_map.mpr ⟨word, hword, rfl⟩)
  rw [hevent, hammingRetentionMeasure_real_contains_finset, Finset.card_map]

open Classical in
theorem power_retainedWords {dimension : ℕ} (side : Bool) (W : Finset (HammingWord dimension))
    (retained : Set (Bool × HammingWord dimension)) :
    (2 : ℝ) ^ (retainedWords side W retained).card =
      ∑ A ∈ W.powerset, if retained ∈ containsWords side A then (1 : ℝ) else 0 := by
  classical
  have heq : W.powerset.filter (fun A => retained ∈ containsWords side A) =
      (retainedWords side W retained).powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powerset, containsWords, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hAW, hretained⟩ word hword
      exact Finset.mem_filter.mpr ⟨hAW hword, hretained word hword⟩
    · intro hA
      constructor
      · intro word hword
        exact (Finset.mem_filter.mp (hA hword)).1
      · intro word hword
        exact (Finset.mem_filter.mp (hA hword)).2
  rw [← Finset.sum_filter, heq]
  simp

theorem retainedWords_exponential_moment {dimension : ℕ} (side : Bool)
    (W : Finset (HammingWord dimension)) :
    (∫ retained, (2 : ℝ) ^ (retainedWords side W retained).card
      ∂hammingRetentionMeasure dimension) =
      (1 + hammingRetentionProbability dimension) ^ W.card := by
  classical
  calc
    (∫ retained, (2 : ℝ) ^ (retainedWords side W retained).card
        ∂hammingRetentionMeasure dimension) =
        ∫ retained, ∑ A ∈ W.powerset,
          if retained ∈ containsWords side A then (1 : ℝ) else 0
          ∂hammingRetentionMeasure dimension := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (power_retainedWords side W)
    _ = ∑ A ∈ W.powerset, ∫ retained,
        (if retained ∈ containsWords side A then (1 : ℝ) else 0)
          ∂hammingRetentionMeasure dimension := by
      apply integral_finsetSum
      intro A hA
      exact hammingRetentionMeasure_integrable dimension _
    _ = ∑ A ∈ W.powerset, (hammingRetentionMeasure dimension).real (containsWords side A) := by
      apply Finset.sum_congr rfl
      intro A hA
      exact hammingRetentionMeasure_integral_event_indicator dimension _
    _ = ∑ A ∈ W.powerset, hammingRetentionProbability dimension ^ A.card := by
      simp_rw [containsWords_probability]
    _ = (1 + hammingRetentionProbability dimension) ^ W.card := by
      simpa using (Finset.prod_one_add (s := W)
        (f := fun _ => hammingRetentionProbability dimension)).symm

theorem retainedWords_tail {dimension : ℕ} (side : Bool) (W : Finset (HammingWord dimension))
    (limit threshold : ℕ) (hlimit : W.card ≤ limit) :
    (hammingRetentionMeasure dimension).real
        {retained | threshold ≤ (retainedWords side W retained).card} ≤
      Real.exp (hammingRetentionProbability dimension * limit - (threshold : ℝ) * Real.log 2) := by
  classical
  have hmarkov :
      (hammingRetentionMeasure dimension).real
          {retained | threshold ≤ (retainedWords side W retained).card} * (2 : ℝ) ^ threshold ≤
        ∫ retained, (2 : ℝ) ^ (retainedWords side W retained).card
          ∂hammingRetentionMeasure dimension := by
    rw [hammingRetentionMeasure_real_event_eq_sum,
      hammingRetentionMeasure_integral_eq_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro retained _
    have hnonneg : 0 ≤ (hammingRetentionMeasure dimension).real {retained} := ENNReal.toReal_nonneg
    by_cases hretained : threshold ≤ (retainedWords side W retained).card
    · simp only [Set.mem_setOf_eq, hretained, if_true]
      apply mul_le_mul_of_nonneg_left _ hnonneg
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hretained)
    · simp only [Set.mem_setOf_eq, hretained, if_false, zero_mul]
      positivity
  rw [retainedWords_exponential_moment] at hmarkov
  have hp : 0 ≤ hammingRetentionProbability dimension := (hammingRetentionProbability_pos dimension).le
  have hbase : 1 + hammingRetentionProbability dimension ≤
      Real.exp (hammingRetentionProbability dimension) := by
    have h := Real.add_one_le_exp (hammingRetentionProbability dimension)
    linarith
  have hmoment : (1 + hammingRetentionProbability dimension) ^ W.card ≤
      Real.exp (hammingRetentionProbability dimension * limit) := by
    calc
      (1 + hammingRetentionProbability dimension) ^ W.card ≤
          (Real.exp (hammingRetentionProbability dimension)) ^ W.card := by gcongr
      _ = Real.exp ((W.card : ℝ) * hammingRetentionProbability dimension) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp (hammingRetentionProbability dimension * limit) := by
        apply Real.exp_le_exp.mpr
        have hcard : (W.card : ℝ) ≤ limit := by exact_mod_cast hlimit
        nlinarith
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  apply (le_div_iff₀ (by positivity)).mpr
  exact hmarkov.trans hmoment

end

end Erdos566.Retuned

namespace Erdos566.Spectrum

noncomputable section

theorem eventually_polynomial_le_exp (constant : ℝ) (hconstant : 0 ≤ constant)
    (power : ℕ) (rate : ℝ) (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in Filter.atTop,
      constant * ((m : ℝ) + 1) ^ power ≤ Real.exp (rate * m) := by
  have hlimit : Filter.Tendsto
      (fun m : ℕ => Real.exp (rate * m) / (m : ℝ) ^ power)
      Filter.atTop Filter.atTop := by
    have h := (tendsto_exp_mul_div_rpow_atTop (power : ℝ) rate hrate).comp
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_natCast] using h
  have hlarge := (Filter.tendsto_atTop.1 hlimit) (constant * (2 : ℝ) ^ power)
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with m hm hmone
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hmone
  have hmpos : (0 : ℝ) < m := by linarith
  have hscaled := (le_div_iff₀ (pow_pos hmpos power)).mp hm
  have hpower : ((m : ℝ) + 1) ^ power ≤ (2 * (m : ℝ)) ^ power := by
    gcongr
    linarith
  calc
    constant * ((m : ℝ) + 1) ^ power ≤ constant * (2 * (m : ℝ)) ^ power :=
      mul_le_mul_of_nonneg_left hpower hconstant
    _ = constant * (2 : ℝ) ^ power * (m : ℝ) ^ power := by rw [mul_pow]; ring
    _ ≤ Real.exp (rate * m) := hscaled

def cliqueSize (m : ℕ) : ℕ := 2 ^ (570 * m)

def fingerprintConstant : ℝ := 3 + 160000 * Real.log 2

theorem fingerprintBound_nonnegative (m : ℕ) (hm : 0 < m) : 0 ≤ fingerprintBound m := by
  unfold fingerprintBound
  have hQ : (1 : ℝ) ≤ 2 ^ dimension m := one_le_pow₀ (by norm_num)
  have hlog := Real.log_nonneg hQ
  exact add_nonneg (by norm_num) (div_nonneg hlog (degreeRate_pos m hm).le)

theorem fingerprintBound_upper (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    fingerprintBound m ≤ 1 + 160000 * Real.log 2 * m * (2 : ℝ) ^ (568 * m) := by
  have hmass := ballMass_clean_lower m hm hpoly
  have hden : (0 : ℝ) < (2 : ℝ) ^ (39432 * m) := by positivity
  have hmassPower : (2 : ℝ) ^ (39432 * m) ≤ ballMass m := by
    convert hmass using 1
    have hexponent : (4929 : ℝ) / 5000 * dimension m * Real.log 2 =
        ((39432 * m : ℕ) : ℝ) * Real.log 2 := by
      norm_num [dimension]
      ring
    rw [hexponent, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hmasspos := ballMass_pos m hm
  have hQpos : (0 : ℝ) < (2 : ℝ) ^ dimension m := by positivity
  have hQge : (1 : ℝ) ≤ (2 : ℝ) ^ dimension m := one_le_pow₀ (by norm_num)
  have hlog := Real.log_nonneg hQge
  have hsplit : (2 : ℝ) ^ dimension m = (2 : ℝ) ^ (39432 * m) * (2 : ℝ) ^ (568 * m) := by
    rw [← pow_add]
    congr 1
    unfold dimension
    omega
  calc
    fingerprintBound m = 1 + (4 * (2 : ℝ) ^ dimension m * Real.log ((2 : ℝ) ^ dimension m)) /
        ballMass m := by
      unfold fingerprintBound degreeRate
      field_simp
    _ ≤ 1 + (4 * (2 : ℝ) ^ dimension m * Real.log ((2 : ℝ) ^ dimension m)) /
        (2 : ℝ) ^ (39432 * m) := by
      gcongr
    _ = 1 + 160000 * Real.log 2 * m * (2 : ℝ) ^ (568 * m) := by
      rw [Real.log_pow, hsplit]
      norm_num [dimension]
      field_simp
      ring

def countingConstant : ℝ := fingerprintConstant * (1 + 40000 * Real.log 2)

theorem fingerprintConstant_pos : 0 < fingerprintConstant := by
  unfold fingerprintConstant
  positivity

theorem countingConstant_pos : 0 < countingConstant := by
  unfold countingConstant
  exact mul_pos fingerprintConstant_pos (by positivity)

theorem fingerprintLimit_upper (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    (fingerprintLimit m : ℝ) + 1 ≤
      fingerprintConstant * ((m : ℝ) + 1) * (2 : ℝ) ^ (568 * m) := by
  have hceil := Nat.ceil_lt_add_one (fingerprintBound_nonnegative m hm)
  have hbound := fingerprintBound_upper m hm hpoly
  have hpower : (1 : ℝ) ≤ 2 ^ (568 * m) := one_le_pow₀ (by norm_num)
  have hmzero : (0 : ℝ) ≤ m := by positivity
  have hproduct : 1 ≤ ((m : ℝ) + 1) * (2 : ℝ) ^ (568 * m) := by
    nlinarith [mul_nonneg hmzero (sub_nonneg.mpr hpower)]
  have hpositive : 0 ≤ (160000 * Real.log 2) * (2 : ℝ) ^ (568 * m) := by positivity
  change (fingerprintLimit m : ℝ) < fingerprintBound m + 1 at hceil
  unfold fingerprintConstant
  nlinarith

theorem fingerprint_exponent_upper (m : ℕ) (hm : 0 < m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000)) :
    (fingerprintLimit m : ℝ) * (1 + (dimension m : ℝ) * Real.log 2) ≤
      countingConstant * ((m : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (568 * m) := by
  have hconstant := fingerprintConstant_pos
  have hlimit := fingerprintLimit_upper m hm hpoly
  have hL : (fingerprintLimit m : ℝ) ≤
      fingerprintConstant * ((m : ℝ) + 1) * (2 : ℝ) ^ (568 * m) := by linarith
  have hcoefficient : 1 + (dimension m : ℝ) * Real.log 2 ≤
      (1 + 40000 * Real.log 2) * ((m : ℝ) + 1) := by
    norm_num [dimension]
    nlinarith [Erdos566.log_two_pos]
  calc
    (fingerprintLimit m : ℝ) * (1 + (dimension m : ℝ) * Real.log 2) ≤
        (fingerprintConstant * ((m : ℝ) + 1) * (2 : ℝ) ^ (568 * m)) *
          ((1 + 40000 * Real.log 2) * ((m : ℝ) + 1)) := by
      exact mul_le_mul hL hcoefficient (by positivity) (by positivity)
    _ = countingConstant * ((m : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (568 * m) := by
      unfold countingConstant
      ring

theorem fingerprint_count_bound (m : ℕ) :
    ((Containers.candidateFingerprints
        (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) ≤
      Real.exp ((fingerprintLimit m : ℝ) * (1 + (dimension m : ℝ) * Real.log 2)) := by
  have hcount := Containers.candidateFingerprints_card_le
    (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)
  have hcountR :
      ((Containers.candidateFingerprints
          (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) ≤
        ((fingerprintLimit m : ℝ) + 1) * ((2 : ℝ) ^ dimension m) ^ fingerprintLimit m := by
    exact_mod_cast (by simpa [CubeFourier.Word] using hcount)
  have hfirst : (fingerprintLimit m : ℝ) + 1 ≤ Real.exp (fingerprintLimit m) :=
    Real.add_one_le_exp _
  have hpower : ((2 : ℝ) ^ dimension m) ^ fingerprintLimit m =
      Real.exp ((fingerprintLimit m : ℝ) * (dimension m : ℝ) * Real.log 2) := by
    rw [cubeOrder_as_exp, ← Real.exp_nat_mul]
    congr 1
    ring
  calc
    ((Containers.candidateFingerprints
        (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) ≤
        ((fingerprintLimit m : ℝ) + 1) * ((2 : ℝ) ^ dimension m) ^ fingerprintLimit m := hcountR
    _ ≤ Real.exp (fingerprintLimit m) * ((2 : ℝ) ^ dimension m) ^ fingerprintLimit m :=
      mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ = Real.exp ((fingerprintLimit m : ℝ) * (1 + (dimension m : ℝ) * Real.log 2)) := by
      rw [hpower, ← Real.exp_add]
      congr 1
      ring

theorem eventually_fingerprint_small :
    ∀ᶠ m : ℕ in Filter.atTop,
      (fingerprintLimit m : ℝ) ≤ (cliqueSize m : ℝ) / 2 ∧
      ((Containers.candidateFingerprints
        (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) ≤
        Real.exp ((cliqueSize m : ℝ) * Real.log 2 / 8) := by
  have hconstant : 0 ≤ 8 * countingConstant / Real.log 2 := by
    have hpositive := countingConstant_pos
    positivity
  have hpoly := eventually_polynomial_le_exp (8 * countingConstant / Real.log 2) hconstant 2
    (2 * Real.log 2) (by positivity)
  filter_upwards [hpoly, eventually_dimension_le_exp, Filter.eventually_gt_atTop 0] with m hsmall hdim hm
  have hexp : Real.exp (2 * Real.log 2 * m) = (2 : ℝ) ^ (2 * m) := by
    have hid : 2 * Real.log 2 * (m : ℝ) = ((2 * m : ℕ) : ℝ) * Real.log 2 := by push_cast; ring
    rw [hid, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hexp] at hsmall
  have hscaled : countingConstant * ((m : ℝ) + 1) ^ 2 ≤
      Real.log 2 / 8 * (2 : ℝ) ^ (2 * m) := by
    have h := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ Real.log 2 / 8 by positivity)
    field_simp [Erdos566.log_two_pos.ne'] at h
    nlinarith
  have hwithPower := mul_le_mul_of_nonneg_right hscaled (show 0 ≤ (2 : ℝ) ^ (568 * m) by positivity)
  have hpowers : (2 : ℝ) ^ (2 * m) * (2 : ℝ) ^ (568 * m) = (cliqueSize m : ℝ) := by
    rw [← pow_add]
    unfold cliqueSize
    push_cast
    congr 1
    omega
  have htotal : countingConstant * ((m : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (568 * m) ≤
      (cliqueSize m : ℝ) * Real.log 2 / 8 := by
    rw [mul_assoc (Real.log 2 / 8), hpowers] at hwithPower
    nlinarith
  have hbound := (fingerprint_exponent_upper m hm hdim).trans htotal
  constructor
  · have hfactor : (fingerprintLimit m : ℝ) ≤
        (fingerprintLimit m : ℝ) * (1 + (dimension m : ℝ) * Real.log 2) := by
      nlinarith [mul_nonneg (show 0 ≤ (fingerprintLimit m : ℝ) by positivity)
        (show 0 ≤ (dimension m : ℝ) * Real.log 2 by positivity)]
    have hlogtwo := Erdos566.log_two_bounds.2
    have hb : (0 : ℝ) ≤ cliqueSize m := by positivity
    have htarget : (cliqueSize m : ℝ) * Real.log 2 / 8 ≤ (cliqueSize m : ℝ) / 2 := by
      nlinarith [mul_nonneg hb (show 0 ≤ 4 - Real.log 2 by linarith)]
    exact hfactor.trans (hbound.trans htarget)
  · exact (fingerprint_count_bound m).trans (Real.exp_le_exp.mpr hbound)

theorem sampled_container_mean (m : ℕ) :
    Retuned.hammingRetentionProbability (dimension m) * containerThreshold m =
      (2 : ℝ) ^ (544 * m) := by
  have hpower : (2 : ℝ) ^ (544 * m) =
      Real.exp (((544 * m : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [containerThreshold_as_exp, hpower]
  unfold Retuned.hammingRetentionProbability
  rw [← Real.exp_add]
  congr 1
  norm_num [dimension, Erdos566.beta]
  ring

theorem sampled_container_mean_small (m : ℕ) (hm : 0 < m) :
    Retuned.hammingRetentionProbability (dimension m) * containerThreshold m ≤
      (cliqueSize m : ℝ) * Real.log 2 / 8 := by
  have hpower : (16 : ℝ) ≤ (2 : ℝ) ^ (26 * m) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (show 4 ≤ 26 * m by omega)
    norm_num only [Nat.reducePow] at h
    exact_mod_cast h
  have hsplit : (2 : ℝ) ^ (544 * m) * (2 : ℝ) ^ (26 * m) = (cliqueSize m : ℝ) := by
    rw [← pow_add]
    unfold cliqueSize
    push_cast
    congr 1
    omega
  have hraw := mul_le_mul_of_nonneg_left hpower (show 0 ≤ (2 : ℝ) ^ (544 * m) by positivity)
  rw [hsplit] at hraw
  rw [sampled_container_mean]
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Erdos566.log_two_bounds.1]
  have hnonnegative : 0 ≤ (cliqueSize m : ℝ) := by positivity
  nlinarith [mul_nonneg hnonnegative (sub_nonneg.mpr hlog)]

theorem clique_tail_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => Real.exp (-(cliqueSize m : ℝ) * Real.log 2 / 4))
      Filter.atTop (nhds 0) := by
  let ratio := Real.exp (-Real.log 2 / 4)
  have hratio_nonnegative : 0 ≤ ratio := (Real.exp_pos _).le
  have hratio_lt : ratio < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith [Erdos566.log_two_pos]
  have hgeometric := tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonnegative hratio_lt
  have hpoint (m : ℕ) : Real.exp (-(cliqueSize m : ℝ) * Real.log 2 / 4) ≤ ratio ^ m := by
    have hm : m ≤ cliqueSize m := by
      exact (Nat.le_of_lt (show m < 2 ^ m from Nat.lt_two_pow_self)).trans
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hmR : (m : ℝ) ≤ cliqueSize m := by exact_mod_cast hm
    dsimp [ratio]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hmR Erdos566.log_two_pos.le]
  exact squeeze_zero (fun _ => (Real.exp_pos _).le) hpoint hgeometric

end

end Erdos566.Spectrum

open Finset MeasureTheory

namespace Erdos566.Spectrum

noncomputable section

def blueFailure (m : ℕ) (side : Bool) :
    Set (Set (Bool × CubeFourier.Word (dimension m))) :=
  ⋃ F ∈ Containers.candidateFingerprints (fingerprintLimit m),
    {retained | cliqueSize m - fingerprintLimit m ≤
      (Retuned.retainedWords side (cubeContainer m F) retained).card}

theorem large_independent_mem_blueFailure (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (side : Bool) (retained : Set (Bool × CubeFourier.Word (dimension m)))
    (I : Finset (CubeFourier.Word (dimension m)))
    (hI : Containers.Independent (Retuned.ballGraph (dimension m) (radius m)) I)
    (hsize : cliqueSize m ≤ I.card)
    (hretained : ∀ x ∈ I, (side, x) ∈ retained) : retained ∈ blueFailure m side := by
  classical
  obtain ⟨F, hF, hFI, hcover⟩ := independent_container_cover m hm hpoly I hI
  have hlimit : F.card ≤ fingerprintLimit m := (Finset.mem_filter.mp hF).2
  have hsubset : I ⊆ F ∪ Retuned.retainedWords side (cubeContainer m F) retained := by
    intro x hx
    rcases Finset.mem_union.mp (hcover hx) with hxF | hxC
    · exact Finset.mem_union_left _ hxF
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxC, hretained x hx⟩)
  have hcard := (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  apply Set.mem_iUnion.mpr
  refine ⟨F, Set.mem_iUnion.mpr ⟨hF, ?_⟩⟩
  change cliqueSize m - fingerprintLimit m ≤
    (Retuned.retainedWords side (cubeContainer m F) retained).card
  omega

theorem blueFailure_probability_bound (m : ℕ) (side : Bool) :
    (Retuned.hammingRetentionMeasure (dimension m)).real (blueFailure m side) ≤
      ((Containers.candidateFingerprints
        (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) *
        Real.exp (Retuned.hammingRetentionProbability (dimension m) * containerThreshold m -
          ((cliqueSize m - fingerprintLimit m : ℕ) : ℝ) * Real.log 2) := by
  classical
  let candidates := Containers.candidateFingerprints
    (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)
  let events := fun F : Finset (CubeFourier.Word (dimension m)) =>
    {retained : Set (Bool × CubeFourier.Word (dimension m)) |
      cliqueSize m - fingerprintLimit m ≤ (Retuned.retainedWords side (cubeContainer m F) retained).card}
  calc
    (Retuned.hammingRetentionMeasure (dimension m)).real (blueFailure m side) ≤
        ∑ F ∈ candidates, (Retuned.hammingRetentionMeasure (dimension m)).real (events F) :=
      MeasureTheory.measureReal_biUnion_finset_le candidates events
    _ ≤ ∑ _F ∈ candidates,
        Real.exp (Retuned.hammingRetentionProbability (dimension m) * containerThreshold m -
          ((cliqueSize m - fingerprintLimit m : ℕ) : ℝ) * Real.log 2) := by
      apply Finset.sum_le_sum
      intro F hF
      exact Retuned.retainedWords_tail side (cubeContainer m F) (containerThreshold m)
        (cliqueSize m - fingerprintLimit m) (cubeContainer_small m F).le
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; rfl

theorem eventually_blueFailure_small :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ side : Bool,
      (Retuned.hammingRetentionMeasure (dimension m)).real (blueFailure m side) ≤
        Real.exp (-(cliqueSize m : ℝ) * Real.log 2 / 4) := by
  filter_upwards [eventually_fingerprint_small, Filter.eventually_ge_atTop 1000] with m hsmall hm
  intro side
  have hmpos : 0 < m := by omega
  have hlimit : fingerprintLimit m ≤ cliqueSize m := by
    have hnonnegative : (0 : ℝ) ≤ cliqueSize m := by positivity
    exact_mod_cast (show (fingerprintLimit m : ℝ) ≤ cliqueSize m by linarith [hsmall.1])
  have hr : (cliqueSize m : ℝ) / 2 ≤ ((cliqueSize m - fingerprintLimit m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlimit]
    linarith [hsmall.1]
  have hmean := sampled_container_mean_small m hmpos
  calc
    (Retuned.hammingRetentionMeasure (dimension m)).real (blueFailure m side) ≤
        ((Containers.candidateFingerprints
          (V := CubeFourier.Word (dimension m)) (fingerprintLimit m)).card : ℝ) *
          Real.exp (Retuned.hammingRetentionProbability (dimension m) * containerThreshold m -
            ((cliqueSize m - fingerprintLimit m : ℕ) : ℝ) * Real.log 2) :=
      blueFailure_probability_bound m side
    _ ≤ Real.exp ((cliqueSize m : ℝ) * Real.log 2 / 8) *
        Real.exp (Retuned.hammingRetentionProbability (dimension m) * containerThreshold m -
          ((cliqueSize m - fingerprintLimit m : ℕ) : ℝ) * Real.log 2) :=
      mul_le_mul_of_nonneg_right hsmall.2 (Real.exp_pos _).le
    _ ≤ Real.exp (-(cliqueSize m : ℝ) * Real.log 2 / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hr Erdos566.log_two_pos.le]

end

end Erdos566.Spectrum

open Finset MeasureTheory

namespace Erdos566.Spectrum

noncomputable section

def sizeFailure (m : ℕ) : Set (Set (Bool × CubeFourier.Word (dimension m))) :=
  {retained | Retuned.hammingRetainedVertexCount (dimension m) retained <
    Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2}

def totalFailure (m : ℕ) : Set (Set (Bool × CubeFourier.Word (dimension m))) :=
  Retuned.redFailure (dimension m) ∪ sizeFailure m ∪ blueFailure m false ∪ blueFailure m true

theorem dimension_tendsto_atTop : Filter.Tendsto dimension Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro bound
  filter_upwards [Filter.eventually_ge_atTop bound] with m hm
  unfold dimension
  omega

theorem sizeFailure_probability_bound (m : ℕ) :
    (Retuned.hammingRetentionMeasure (dimension m)).real (sizeFailure m) ≤
      4 / Retuned.hammingExpectedRetainedVertexCount (dimension m) := by
  letI : IsProbabilityMeasure (Retuned.hammingRetentionMeasure (dimension m)) :=
    Retuned.hammingRetentionMeasure_isProbability (dimension m)
  have hmean := Retuned.hammingExpectedRetainedVertexCount_pos (dimension m)
  have hchebyshev := Retuned.hammingRetainedVertexCount_deviation_probability_le
    (dimension m) (Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2) (by positivity)
  have hsubset : sizeFailure m ⊆
      {retained : Set (Bool × CubeFourier.Word (dimension m)) |
        Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 ≤
          |Retuned.hammingRetainedVertexCount (dimension m) retained -
            Retuned.hammingExpectedRetainedVertexCount (dimension m)|} := by
    intro retained hretained
    have hnegative := neg_le_abs
      (Retuned.hammingRetainedVertexCount (dimension m) retained -
        Retuned.hammingExpectedRetainedVertexCount (dimension m))
    change Retuned.hammingRetainedVertexCount (dimension m) retained <
      Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 at hretained
    change Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 ≤ _
    linarith
  calc
    (Retuned.hammingRetentionMeasure (dimension m)).real (sizeFailure m) ≤
        (Retuned.hammingRetentionMeasure (dimension m)).real
          {retained | Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 ≤
            |Retuned.hammingRetainedVertexCount (dimension m) retained -
              Retuned.hammingExpectedRetainedVertexCount (dimension m)|} :=
      MeasureTheory.measureReal_mono hsubset
    _ ≤ Retuned.hammingExpectedRetainedVertexCount (dimension m) /
        (Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2) ^ 2 := hchebyshev
    _ = 4 / Retuned.hammingExpectedRetainedVertexCount (dimension m) := by
      field_simp
      ring

theorem sizeFailure_bound_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => 4 / Retuned.hammingExpectedRetainedVertexCount (dimension m))
      Filter.atTop (nhds 0) := by
  have h := Retuned.hammingExpectedRetainedVertexCount_inv_tendsto_zero.comp dimension_tendsto_atTop
  have hscaled := h.const_mul 4
  convert hscaled using 1
  · funext m
    simp only [Function.comp_apply]
    ring
  · norm_num

theorem redFailure_bound_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => ((2 * Erdos566.layerDepth : ℕ) : ℝ) *
        Real.exp (-(dimension m : ℝ) * Real.log 2)) Filter.atTop (nhds 0) := by
  exact (Retuned.pairLayerExclusionProbability_tendsto_zero Erdos566.layerDepth).comp dimension_tendsto_atTop

theorem eventually_totalFailure_lt_one :
    ∀ᶠ m : ℕ in Filter.atTop,
      (Retuned.hammingRetentionMeasure (dimension m)).real (totalFailure m) < 1 := by
  have hquarter : ∀ᶠ x : ℝ in nhds 0, x < 1 / 4 :=
    eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)
  have hred := redFailure_bound_tendsto_zero.eventually hquarter
  have hsize := sizeFailure_bound_tendsto_zero.eventually hquarter
  have hblue := (clique_tail_tendsto_zero.const_mul 2).eventually (by simpa using hquarter)
  filter_upwards [hred, hsize, hblue, eventually_blueFailure_small,
    Filter.eventually_ge_atTop 1000] with m hr hs hb hblueBound hm
  let μ := Retuned.hammingRetentionMeasure (dimension m)
  letI : IsProbabilityMeasure μ := Retuned.hammingRetentionMeasure_isProbability (dimension m)
  have hmpos : 0 < m := by omega
  have hdimpos : 0 < dimension m := by unfold dimension; omega
  have hredBound := Retuned.redFailure_probability_bound (dimension m) hdimpos
  have hsizeBound := sizeFailure_probability_bound m
  have hzero := hblueBound false
  have hone := hblueBound true
  have hunion : μ.real (totalFailure m) ≤
      μ.real (Retuned.redFailure (dimension m)) + μ.real (sizeFailure m) +
        μ.real (blueFailure m false) + μ.real (blueFailure m true) := by
    unfold totalFailure
    calc
      μ.real (Retuned.redFailure (dimension m) ∪ sizeFailure m ∪ blueFailure m false ∪ blueFailure m true) ≤
          μ.real (Retuned.redFailure (dimension m) ∪ sizeFailure m ∪ blueFailure m false) +
            μ.real (blueFailure m true) := MeasureTheory.measureReal_union_le _ _
      _ ≤ (μ.real (Retuned.redFailure (dimension m) ∪ sizeFailure m) +
          μ.real (blueFailure m false)) + μ.real (blueFailure m true) := by
        gcongr
        exact MeasureTheory.measureReal_union_le _ _
      _ ≤ _ := by
        gcongr
        exact MeasureTheory.measureReal_union_le _ _
  change (Retuned.hammingRetentionMeasure (dimension m)).real (totalFailure m) < 1
  change (Retuned.hammingRetentionMeasure (dimension m)).real (totalFailure m) ≤ _ at hunion
  dsimp [μ] at hunion
  norm_num only [mul_zero] at hb
  linarith

theorem eventually_exists_good_retention :
    ∀ᶠ m : ℕ in Filter.atTop, ∃ retained : Set (Bool × CubeFourier.Word (dimension m)),
      retained ∉ Retuned.redFailure (dimension m) ∧ retained ∉ sizeFailure m ∧
        retained ∉ blueFailure m false ∧ retained ∉ blueFailure m true := by
  filter_upwards [eventually_totalFailure_lt_one] with m hm
  obtain ⟨retained, hretained⟩ := Retuned.exists_hammingRetention_outside_event
    (dimension m) (totalFailure m) hm
  refine ⟨retained, ?_⟩
  simpa only [totalFailure, Set.mem_union, not_or, and_assoc] using hretained

end

end Erdos566.Spectrum

open Finset

namespace Erdos566.Spectrum

noncomputable section

def sideSet (m : ℕ) (side : Bool)
    (retained : Set (Bool × CubeFourier.Word (dimension m))) : Finset (CubeFourier.Word (dimension m)) :=
  Retuned.retainedWords side Finset.univ retained

theorem mem_sideSet (m : ℕ) (side : Bool)
    (retained : Set (Bool × CubeFourier.Word (dimension m))) (word : CubeFourier.Word (dimension m)) :
    word ∈ sideSet m side retained ↔ (side, word) ∈ retained := by
  classical
  simp [sideSet, Retuned.retainedWords]

theorem sideSet_coe (m : ℕ) (side : Bool)
    (retained : Set (Bool × CubeFourier.Word (dimension m))) :
    (sideSet m side retained : Set (CubeFourier.Word (dimension m))) =
      {word | (side, word) ∈ retained} := by
  ext word
  exact mem_sideSet m side retained word

theorem retained_count_sides (m : ℕ)
    (retained : Set (Bool × CubeFourier.Word (dimension m))) :
    Retuned.hammingRetainedVertexCount (dimension m) retained =
      (sideSet m false retained).card + ((sideSet m true retained).card : ℝ) := by
  classical
  have hside (side : Bool) :
      (∑ word : CubeFourier.Word (dimension m), if (side, word) ∈ retained then (1 : ℝ) else 0) =
        ((sideSet m side retained).card : ℝ) := by
    unfold sideSet Retuned.retainedWords
    rw [← Finset.sum_filter]
    simp
  calc
    Retuned.hammingRetainedVertexCount (dimension m) retained =
        (∑ word : CubeFourier.Word (dimension m), if (false, word) ∈ retained then (1 : ℝ) else 0) +
        (∑ word : CubeFourier.Word (dimension m), if (true, word) ∈ retained then (1 : ℝ) else 0) := by
      unfold Retuned.hammingRetainedVertexCount
      rw [Fintype.sum_prod_type]
      rw [Fintype.univ_bool, Finset.sum_pair (by decide : (true : Bool) ≠ false)]
      ring
    _ = _ := by rw [hside false, hside true]

theorem half_expected_count (m : ℕ) :
    Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 =
      ((2 ^ (1144 * m) : ℕ) : ℝ) := by
  rw [Retuned.hammingExpectedRetainedVertexCount_eq]
  rw [show 2 * Retuned.hammingRetentionProbability (dimension m) *
      ((2 ^ dimension m : ℕ) : ℝ) / 2 =
      Retuned.hammingRetentionProbability (dimension m) * ((2 ^ dimension m : ℕ) : ℝ) by ring,
    Retuned.hammingRetentionProbability_mul_wordCount_eq_exp]
  have hpower := power_two_as_exp (1144 * m)
  rw [hpower]
  congr 1
  norm_num [dimension, Erdos566.beta]
  ring

theorem exists_large_side (m : ℕ)
    (retained : Set (Bool × CubeFourier.Word (dimension m)))
    (hsize : retained ∉ sizeFailure m) :
    ∃ side : Bool, 2 ^ (1144 * m) ≤ 2 * (sideSet m side retained).card := by
  have htotal : ((2 ^ (1144 * m) : ℕ) : ℝ) ≤
      (sideSet m false retained).card + ((sideSet m true retained).card : ℝ) := by
    change ¬ Retuned.hammingRetainedVertexCount (dimension m) retained <
      Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 at hsize
    have h := le_of_not_gt hsize
    change Retuned.hammingExpectedRetainedVertexCount (dimension m) / 2 ≤
      Retuned.hammingRetainedVertexCount (dimension m) retained at h
    rw [half_expected_count, retained_count_sides] at h
    exact h
  by_cases hfalse : 2 ^ (1144 * m) ≤ 2 * (sideSet m false retained).card
  · exact ⟨false, hfalse⟩
  · refine ⟨true, ?_⟩
    have hfalseR : 2 * ((sideSet m false retained).card : ℝ) < ((2 ^ (1144 * m) : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_of_not_ge hfalse
    have htrueR : ((2 ^ (1144 * m) : ℕ) : ℝ) ≤ 2 * ((sideSet m true retained).card : ℝ) := by
      linarith
    exact_mod_cast htrueR

theorem radius_eq_cutoff (m : ℕ) : radius m = Erdos566.cubeCutoff (dimension m) := by
  simpa [radius, dimension] using (Erdos566.cubeCutoff_multiple m).symm

theorem ballGraph_eq_cubeGraph (m : ℕ) :
    Retuned.ballGraph (dimension m) (radius m) = Erdos566.cubeGraph (dimension m) := by
  unfold Retuned.ballGraph Erdos566.cubeGraph
  rw [radius_eq_cutoff]

theorem side_red_free (m : ℕ) (hm : 0 < m) (side : Bool)
    (retained : Set (Bool × CubeFourier.Word (dimension m)))
    (hred : retained ∉ Retuned.redFailure (dimension m)) :
    Erdos566.counterexampleGraph.Free
      ((Erdos566.cubeGraph (dimension m)).induce (sideSet m side retained : Set _)) := by
  have hdim : 0 < dimension m := by unfold dimension; omega
  have hfree := Retuned.both_sides_free_outside_redFailure (dimension m) hdim retained hred side
  change Erdos566.counterexampleGraph.Free
    ((Retuned.ballGraph (dimension m) (Erdos566.cubeCutoff (dimension m))).induce
      {word | (side, word) ∈ retained}) at hfree
  rw [← radius_eq_cutoff, ballGraph_eq_cubeGraph, ← sideSet_coe m side retained] at hfree
  exact hfree

theorem side_blue_free (m : ℕ) (hm : 1000 ≤ m)
    (hpoly : (dimension m : ℝ) + 1 ≤ Real.exp ((dimension m : ℝ) * Real.log 2 / 100000))
    (side : Bool) (retained : Set (Bool × CubeFourier.Word (dimension m)))
    (hblue : retained ∉ blueFailure m side) :
    (⊤ : SimpleGraph (Fin (cliqueSize m))).Free
      (((Erdos566.cubeGraph (dimension m)).induce (sideSet m side retained : Set _))ᶜ) := by
  classical
  rw [← ballGraph_eq_cubeGraph]
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  let image : Fin (cliqueSize m) → CubeFourier.Word (dimension m) := fun v => (copy v).val
  let I : Finset (CubeFourier.Word (dimension m)) := Finset.univ.image image
  have hinjective : Function.Injective image := by
    intro v w heq
    exact copy.injective (Subtype.ext heq)
  have hsize : I.card = cliqueSize m := by
    rw [Finset.card_image_of_injective _ hinjective]
    simp
  have hretained : ∀ x ∈ I, (side, x) ∈ retained := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_sideSet m side retained (image v)).mp (copy v).property
  have hindependent : Containers.Independent (Retuned.ballGraph (dimension m) (radius m)) I := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
    by_cases heq : v = w
    · subst w
      simp
    · have hadj : (⊤ : SimpleGraph (Fin (cliqueSize m))).Adj v w := by simpa using heq
      have hcomplement := copy.toHom.map_rel hadj
      exact hcomplement.2
  apply hblue
  exact large_independent_mem_blueFailure m hm hpoly side retained I hindependent hsize.ge hretained

theorem sampled_cube_statement : Erdos566.SampledCubeStatement := by
  have hevent : ∀ᶠ m : ℕ in Filter.atTop,
      ∃ S : Finset (Erdos566.Cube (dimension m)),
        2 ^ (1144 * m) ≤ 2 * S.card ∧
        Erdos566.counterexampleGraph.Free ((Erdos566.cubeGraph (dimension m)).induce (S : Set _)) ∧
        (⊤ : SimpleGraph (Fin (cliqueSize m))).Free
          (((Erdos566.cubeGraph (dimension m)).induce (S : Set _))ᶜ) := by
    filter_upwards [eventually_exists_good_retention, eventually_dimension_le_exp,
      Filter.eventually_ge_atTop 1000] with m hexists hpoly hm
    obtain ⟨retained, hred, hsize, hfalse, htrue⟩ := hexists
    obtain ⟨side, hcard⟩ := exists_large_side m retained hsize
    refine ⟨sideSet m side retained, hcard, side_red_free m (by omega) side retained hred, ?_⟩
    apply side_blue_free m hm hpoly side retained
    cases side
    · exact hfalse
    · exact htrue
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨m₀, ?_⟩
  intro m hm
  obtain ⟨S, hcard, hred, hblue⟩ := hm₀ m hm
  exact ⟨S, hcard, hred, hblue⟩

end

end Erdos566.Spectrum

namespace Erdos566

theorem original_statement_false : ¬OriginalStatement :=
  not_original_of_sampled_cube Spectrum.sampled_cube_statement

end Erdos566

namespace PrizeStatement

noncomputable def graphRamsey {α β : Type*} [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β) : ℕ :=
  sInf {n : ℕ | ∀ C : SimpleGraph (Fin n), G.IsContained C ∨ H.IsContained Cᶜ}

def IsRamseySizeLinear {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∃ c > (0 : ℝ), ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ v, 0 < H.degree v) →
    (graphRamsey G H : ℝ) ≤ c * H.edgeSet.ncard

def Statement : Prop :=
  ∀ (p : ℕ) (G : SimpleGraph (Fin p)),
    (∀ S : Finset (Fin p), 2 ≤ S.card →
      (G.induce S).edgeSet.ncard ≤ 2 * S.card - 3) →
    IsRamseySizeLinear G

theorem exact_statement_agreement : Statement = Erdos566.OriginalStatement := rfl

theorem original_problem_false : ¬Statement := Erdos566.original_statement_false

end PrizeStatement
