import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Option

universe u

/-!
# Coloring a finite bounded-degree graph

A finite simple graph of maximum degree at most `D` has a proper coloring with the actual palette
`Fin (D + 2)`. The proof uses greedy induction, retaining the empty graph and `D = 0` cases.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:initialization`,
line 803.
-/

/-- A finite graph of degree at most D has an actual proper coloring with D+2 colors.

Proof: induct on the finite vertex type up to equivalence, with empty and Option steps.
Transport the graph and degrees through equivalences. In the Option step the induced graph
on old vertices has degree at most D by the injection of neighbor sets, hence a coloring by
induction. At most D colors occur among the neighbors of the new vertex; the D+2 palette
therefore contains an unused color. Assign it to the new vertex and check the endpoint cases.
The empty case is the empty coloring, and D=0 still uses the nonempty two-color palette.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:initialization`, line 803. -/
theorem initialization_colored_cutoffs_coloring
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdegree : ∀ v : V, G.degree v ≤ D) :
    Nonempty (G.Coloring (Fin (D + 2))) := by
  classical
  have hmain : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ w : W, H.degree w ≤ D) → Nonempty (H.Coloring (Fin (D + 2))) := by
    intro W
    refine Fintype.induction_empty_option
      (P := fun W _ => ∀ (H : SimpleGraph W) [DecidableRel H.Adj],
        (∀ w : W, H.degree w ≤ D) → Nonempty (H.Coloring (Fin (D + 2))))
      ?_ ?_ ?_ W
    · intro α β _ e ih H instH hH
      let : Fintype α := Fintype.ofEquiv β e.symm
      let H' : SimpleGraph α := H.map e.symm.toEmbedding
      have : DecidableRel H'.Adj := inferInstance
      have hNeighborFin (a : α) : Fintype (H'.neighborSet a) :=
        Fintype.ofFinset (Finset.univ.filter fun b => H'.Adj a b) (by
          intro b
          simp [SimpleGraph.neighborSet])
      have : ∀ a : α, Fintype (H'.neighborSet a) := hNeighborFin
      have hH' : ∀ a : α, H'.degree a ≤ D := by
        intro a
        have hEq : H'.degree a = H.degree (e a) := by
          have hv : e.symm.toEmbedding (e a) = a := e.symm_apply_apply a
          simpa only [H', ← SimpleGraph.ncard_neighborSet, hv] using
            H.degree_map_apply e.symm.toEmbedding (e a)
        exact hEq.trans_le (hH (e a))
      obtain ⟨c⟩ := ih H' (fun a ↦ by
        simpa only [← SimpleGraph.ncard_neighborSet] using hH' a)
      let f : H →g H' := {
        toFun := e.symm
        map_rel' := by
          intro x y hxy
          change (H.map e.symm.toEmbedding).Adj (e.symm x) (e.symm y)
          rw [H.map_symm e]
          simpa using hxy
      }
      exact ⟨c.comap f⟩
    · intro H instH hH
      exact ⟨SimpleGraph.Coloring.ofIsEmpty⟩
    · intro α _ ih H instH hH
      let e : α ↪ Option α := ⟨some, Option.some_injective α⟩
      let H' : SimpleGraph α := H.comap e
      have : DecidableRel H'.Adj := inferInstance
      have hNeighborFin (a : α) : Fintype (H'.neighborSet a) :=
        Fintype.ofFinset (Finset.univ.filter fun b => H'.Adj a b) (by
          intro b
          simp [SimpleGraph.neighborSet])
      have : ∀ a : α, Fintype (H'.neighborSet a) := hNeighborFin
      have hH' : ∀ a : α, H'.degree a ≤ D := by
        intro a
        let f : H'.neighborSet a → H.neighborSet (some a) := fun x =>
          ⟨some x.1, by
            change H.Adj (some a) (some x.1)
            exact x.2⟩
        have hf : Function.Injective f := by
          intro x y hxy
          apply Subtype.ext
          exact Option.some.inj (congrArg Subtype.val hxy)
        calc
          H'.degree a = Fintype.card (H'.neighborSet a) := (H'.card_neighborSet_eq_degree a).symm
          _ ≤ Fintype.card (H.neighborSet (some a)) := Fintype.card_le_of_injective f hf
          _ = H.degree (some a) := H.card_neighborSet_eq_degree (some a)
          _ ≤ D := hH (some a)
      obtain ⟨c⟩ := ih H' (fun a ↦ by
        simpa only [← SimpleGraph.ncard_neighborSet] using hH' a)
      let bad : Finset (Fin (D + 2)) :=
        (H.neighborFinset none).image (fun x => x.elim (0 : Fin (D + 2)) c)
      have hbad : bad.card ≤ D := by
        calc
          bad.card ≤ (H.neighborFinset none).card := Finset.card_image_le
          _ = H.degree none := H.card_neighborFinset_eq_degree none
          _ ≤ D := hH none
      have hlt : bad.card < (Finset.univ : Finset (Fin (D + 2))).card := by
        simp
        omega
      obtain ⟨col, hcol_mem, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      let C : H.Coloring (Fin (D + 2)) :=
        SimpleGraph.Coloring.mk (fun x => x.elim col c) ?_
      refine ⟨C⟩
      intro x y hxy
      cases x with
      | none =>
        cases y with
        | none => exact (H.irrefl hxy).elim
        | some b =>
          have hb : some b ∈ H.neighborFinset none :=
            (H.mem_neighborFinset (v := none) (some b)).2 hxy
          have hb' : c b ∈ bad := Finset.mem_image.mpr ⟨some b, hb, by simp⟩
          change col ≠ c b
          intro heq
          exact hcol (by simpa [heq] using hb')
      | some a =>
        cases y with
        | none =>
          have ha : some a ∈ H.neighborFinset none :=
            (H.mem_neighborFinset (v := none) (some a)).2 hxy.symm
          have ha' : c a ∈ bad := Finset.mem_image.mpr ⟨some a, ha, by simp⟩
          change c a ≠ col
          intro heq
          exact hcol (by simpa [heq] using ha')
        | some b =>
          apply c.valid
          simpa [H', e] using hxy
  exact hmain V G hdegree

#print axioms initialization_colored_cutoffs_coloring
