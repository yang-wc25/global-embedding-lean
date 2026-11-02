import Repair.ReferenceHostColoring

/-!
# Separate source and compact-parameter colors for the actual joint hosts

The original source and parameter support graphs are colored separately.
Their product labels and the bounded local template slot give one actual
primary label.  No degree bound for a new joint refinement graph and no
total atlas cardinality occur in the label bound.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped Topology
namespace GlobalEmbedding.Continuation

theorem repair_reference_product_host_labels
    {M P SourceHost ParameterHost Primary : Type*}
    [TopologicalSpace M] [TopologicalSpace P]
    [Fintype SourceHost] [Fintype ParameterHost]
    (sourceSupport : SourceHost → Set M) (parameterSupport : ParameterHost → Set P)
    (Ds Dp K : ℕ)
    (hSourceDegree : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds)
    (hParameterDegree : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp)
    (sourceHost : Primary → SourceHost) (parameterHost : Primary → ParameterHost)
    (slot : Primary → Fin K)
    (hinjective : Injective (fun a => ((sourceHost a,parameterHost a),slot a)))
    (support : Primary → Set (P × M))
    (hsub : ∀ a, support a ⊆ parameterSupport (parameterHost a) ×ˢ sourceSupport (sourceHost a)) :
    ∃ label : Primary → ℕ,
      (∀ a, label a < ((Ds+2)*(Dp+2))*K) ∧
      ∀ a b, a ≠ b → (support a ∩ support b).Nonempty → label a ≠ label b := by
  classical
  let Gs := tensorEnlargedSupportGraph sourceSupport
  let Gp := tensorEnlargedSupportGraph parameterSupport
  obtain ⟨cs⟩ := initialization_colored_cutoffs_coloring Gs Ds hSourceDegree
  obtain ⟨cp⟩ := initialization_colored_cutoffs_coloring Gp Dp hParameterDegree
  let encHost : Fin (Ds+2) × Fin (Dp+2) ≃ Fin ((Ds+2)*(Dp+2)) := finProdFinEquiv
  let enc : Fin ((Ds+2)*(Dp+2)) × Fin K ≃ Fin (((Ds+2)*(Dp+2))*K) := finProdFinEquiv
  let label : Primary → ℕ := fun a =>
    (enc (encHost (cs (sourceHost a),cp (parameterHost a)),slot a)).val
  refine ⟨label,fun a => (enc (encHost (cs (sourceHost a),cp (parameterHost a)),slot a)).isLt,?_⟩
  intro a b hab hinter heq
  have hpairs : (encHost (cs (sourceHost a),cp (parameterHost a)),slot a) =
      (encHost (cs (sourceHost b),cp (parameterHost b)),slot b) :=
    enc.injective (Fin.ext heq)
  have hcolors : (cs (sourceHost a),cp (parameterHost a)) =
      (cs (sourceHost b),cp (parameterHost b)) :=
    encHost.injective (congrArg Prod.fst hpairs)
  have hslots : slot a = slot b :=
    congrArg (fun p : Fin ((Ds+2)*(Dp+2)) × Fin K => p.2) hpairs
  have hsource : sourceHost a = sourceHost b := by
    by_contra hne
    obtain ⟨z,hza,hzb⟩ := hinter
    have hadj : Gs.Adj (sourceHost a) (sourceHost b) :=
      ⟨hne,z.2,(hsub a hza).2,(hsub b hzb).2⟩
    exact cs.valid hadj (congrArg Prod.fst hcolors)
  have hparameter : parameterHost a = parameterHost b := by
    by_contra hne
    obtain ⟨z,hza,hzb⟩ := hinter
    have hadj : Gp.Adj (parameterHost a) (parameterHost b) :=
      ⟨hne,z.1,(hsub a hza).1,(hsub b hzb).1⟩
    exact cp.valid hadj (congrArg Prod.snd hcolors)
  exact hab (hinjective (Prod.ext (Prod.ext hsource hparameter) hslots))

def repairReferenceFiniteSlot
    {Host Edge : Type*} {Piece : Host → Type*}
    [∀ i, Fintype (Piece i)] [Fintype Edge]
    (L : ℕ) (hcard : ∀ i, Fintype.card (Piece i) ≤ L)
    (a : Σ i, Piece i × Edge) : Fin (L*Fintype.card Edge) :=
  finProdFinEquiv
    (⟨(Fintype.equivFin (Piece a.1) a.2.1).val,
      (Fintype.equivFin (Piece a.1) a.2.1).isLt.trans_le (hcard a.1)⟩,
      Fintype.equivFin Edge a.2.2)

theorem repair_reference_finite_slot_injective
    {Host Edge : Type*} {Piece : Host → Type*}
    [∀ i, Fintype (Piece i)] [Fintype Edge]
    (L : ℕ) (hcard : ∀ i, Fintype.card (Piece i) ≤ L) :
    Injective (fun a : (Σ i, Piece i × Edge) => (a.1,repairReferenceFiniteSlot L hcard a)) := by
  intro a b hab
  have hhost : a.1 = b.1 := congrArg Prod.fst hab
  rcases a with ⟨ha,pa,ea⟩
  rcases b with ⟨hb,pb,eb⟩
  dsimp only at hhost
  subst hb
  have hslot := congrArg Prod.snd hab
  have hpair := finProdFinEquiv.injective hslot
  have hval : (Fintype.equivFin (Piece ha) pa).val = (Fintype.equivFin (Piece ha) pb).val :=
    congrArg (fun p : Fin L × Fin (Fintype.card Edge) => p.1.val) hpair
  have hp : pa = pb := (Fintype.equivFin (Piece ha)).injective
    (Fin.ext hval)
  have he : ea = eb := (Fintype.equivFin Edge).injective (congrArg Prod.snd hpair)
  subst pb
  subst eb
  rfl

/-- The bounded slots are constructed from the actual finite local piece
types and actual dictionary edge type.  They are not an assumed coloring
or injection for the full primary family. -/
theorem repair_reference_product_template_labels
    {M P SourceHost ParameterHost Edge : Type*}
    [TopologicalSpace M] [TopologicalSpace P]
    [Fintype SourceHost] [Fintype ParameterHost] [Fintype Edge]
    {Piece : SourceHost × ParameterHost → Type*} [∀ i, Fintype (Piece i)]
    (sourceSupport : SourceHost → Set M) (parameterSupport : ParameterHost → Set P)
    (Ds Dp L : ℕ)
    (hSourceDegree : ∀ i, tensorEnlargedSupportDegree sourceSupport i ≤ Ds)
    (hParameterDegree : ∀ i, tensorEnlargedSupportDegree parameterSupport i ≤ Dp)
    (hcard : ∀ i, Fintype.card (Piece i) ≤ L)
    (support : (Σ i, Piece i × Edge) → Set (P × M))
    (hsub : ∀ a, support a ⊆ parameterSupport a.1.2 ×ˢ sourceSupport a.1.1) :
    ∃ label : (Σ i, Piece i × Edge) → ℕ,
      (∀ a, label a < ((Ds+2)*(Dp+2))*(L*Fintype.card Edge)) ∧
      ∀ a b, a ≠ b → (support a ∩ support b).Nonempty → label a ≠ label b := by
  exact repair_reference_product_host_labels sourceSupport parameterSupport Ds Dp
    (L*Fintype.card Edge) hSourceDegree hParameterDegree
    (fun a => a.1.1) (fun a => a.1.2) (repairReferenceFiniteSlot L hcard)
    (repair_reference_finite_slot_injective L hcard) support hsub

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_product_host_labels
#print axioms GlobalEmbedding.Continuation.repair_reference_finite_slot_injective
#print axioms GlobalEmbedding.Continuation.repair_reference_product_template_labels
