import Probes.Round3PhaseCompactPreparation
import Mathlib.Topology.Maps.Proper.Basic

/-!
# A finite input-jet list extends to one genuine neighborhood

The bound on the original compact sample is the only numerical premise.
Continuity manufactures a neighborhood with a prescribed positive slack.
For finitely many closed active carriers over a compact source, a single
parameter neighborhood works for every carrier. No bound outside the
original compact parameter set is an input, and no later observation order
enters this neighborhood choice.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalIncrements

/-- A fixed finite list of continuous scalar inputs extends its sample
bounds with an arbitrarily prescribed positive slack. -/
theorem finite_input_upper_neighborhood
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (K U : Set X) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ι → X → ℝ) (B : ι → ℝ)
    (hf : ∀ i, ContinuousOn (f i) U)
    (hB : ∀ i x, x ∈ K → f i x ≤ B i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ V : Set X, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ i x, x ∈ V → f i x < B i + epsilon := by
  let V := U ∩ ⋂ i, (U ∩ (f i) ⁻¹' Iio (B i + epsilon))
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite fun i =>
    (hf i).isOpen_inter_preimage hU isOpen_Iio)
  refine ⟨V,hV,?_,inter_subset_left,?_⟩
  · intro x hx
    refine ⟨hKU hx,mem_iInter.mpr fun i => ⟨hKU hx,?_⟩⟩
    exact (hB i x hx).trans_lt (lt_add_of_pos_right _ hepsilon)
  · intro i x hx
    exact (mem_iInter.mp hx.2 i).2

/-- Compactness of the source gives a single parameter neighborhood for
an open set containing every original source point over the parameter set. -/
theorem compact_source_parameter_tube
    {P M : Type*} [TopologicalSpace P] [TopologicalSpace M] [CompactSpace M]
    (K U : Set P) (hU : IsOpen U) (hKU : K ⊆ U)
    (O : Set (P × M)) (hO : IsOpen O) (hKO : K ×ˢ (univ : Set M) ⊆ O) :
    ∃ V : Set P, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ V ×ˢ (univ : Set M) ⊆ O := by
  let V := U ∩ (Prod.fst '' Oᶜ)ᶜ
  have hClosed : IsClosed (Prod.fst '' Oᶜ) :=
    isClosedMap_fst_of_compactSpace _ hO.isClosed_compl
  refine ⟨V,hU.inter hClosed.isOpen_compl,?_,inter_subset_left,?_⟩
  · intro p hp
    refine ⟨hKU hp,?_⟩
    rintro ⟨⟨q,x⟩,hq,hqp⟩
    change q = p at hqp
    subst q
    exact hq (hKO ⟨hp,mem_univ _⟩)
  · intro z hz
    by_contra hnot
    exact hz.1.2 ⟨z,hnot,rfl⟩

/-- The inputs may be smooth only on their actual active open domains.
One parameter neighborhood controls the finite list on every closed active
carrier; inactive points impose no spurious derivative requirement. -/
theorem finite_active_inputs_parameter_neighborhood
    {P M ι : Type*} [TopologicalSpace P] [TopologicalSpace M] [CompactSpace M] [Finite ι]
    (K U : Set P) (hU : IsOpen U) (hKU : K ⊆ U)
    (active domain : ι → Set (P × M))
    (hActive : ∀ i, IsClosed (active i)) (hDomain : ∀ i, IsOpen (domain i))
    (hActiveDomain : ∀ i, (U ×ˢ (univ : Set M)) ∩ active i ⊆ domain i)
    (f : ι → P × M → ℝ) (B : ι → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (domain i))
    (hB : ∀ i z, z ∈ (K ×ˢ (univ : Set M)) ∩ active i → f i z ≤ B i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ V : Set P, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ i z, z ∈ (V ×ˢ (univ : Set M)) ∩ active i → f i z < B i + epsilon := by
  have hOne (i : ι) : ∃ W : Set (P × M), IsOpen W ∧
      (K ×ˢ (univ : Set M)) ∩ active i ⊆ W ∧ W ⊆ domain i ∧
      ∀ z ∈ W, f i z < B i + epsilon := by
    obtain ⟨W,hW,hKW,hWD,hfW⟩ := finite_input_upper_neighborhood
      ((K ×ˢ (univ : Set M)) ∩ active i) (domain i) (hDomain i)
      (fun z hz => hActiveDomain i ⟨⟨hKU hz.1.1,hz.1.2⟩,hz.2⟩)
      (fun _ : Unit => f i) (fun _ : Unit => B i) (fun _ => hf i)
      (fun _ z hz => hB i z hz) epsilon hepsilon
    exact ⟨W,hW,hKW,hWD,fun z hz => hfW () z hz⟩
  choose W hW hKW hWD hfW using hOne
  let O := (U ×ˢ (univ : Set M)) ∩ ⋂ i, ((active i)ᶜ ∪ W i)
  have hO : IsOpen O := (hU.prod isOpen_univ).inter
    (isOpen_iInter_of_finite fun i => (hActive i).isOpen_compl.union (hW i))
  have hKO : K ×ˢ (univ : Set M) ⊆ O := by
    intro z hz
    refine ⟨⟨hKU hz.1,hz.2⟩,mem_iInter.mpr fun i => ?_⟩
    by_cases hi : z ∈ active i
    · exact Or.inr (hKW i ⟨hz,hi⟩)
    · exact Or.inl hi
  obtain ⟨V,hV,hKV,hVU,hVO⟩ := compact_source_parameter_tube K U hU hKU O hO hKO
  refine ⟨V,hV,hKV,hVU,?_⟩
  intro i z hz
  have hh := mem_iInter.mp (hVO hz.1).2 i
  exact hfW i z (hh.resolve_left (fun hnot => hnot hz.2))

/-- Finite weighted jets of an actual smooth function extend from their
literal sample set. The open neighborhood is chosen before every later
observation order; only the displayed finite prefix is tested. -/
theorem finite_weighted_jets_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (K U : Set E) (hU : IsOpen U) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (J : ℕ) (weight B : ℕ → ℝ)
    (hB : ∀ k, k ≤ J → ∀ x ∈ K, weight k*‖iteratedFDeriv ℝ k f x‖ ≤ B k)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∀ k, k ≤ J → ∀ x ∈ V, weight k*‖iteratedFDeriv ℝ k f x‖ < B k + epsilon := by
  have hCont (k : ℕ) : ContinuousOn (iteratedFDeriv ℝ k f) U := by
    apply (hf.continuousOn_iteratedFDerivWithin (m := k) (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen _ hU hx).symm
  obtain ⟨V,hV,hKV,hVU,hBound⟩ := finite_input_upper_neighborhood K U hU hKU
    (fun k : Fin (J+1) => fun x => weight k*‖iteratedFDeriv ℝ k f x‖)
    (fun k : Fin (J+1) => B k)
    (fun k => continuousOn_const.mul (hCont k).norm)
    (fun k x hx => hB k (by omega) x hx) epsilon hepsilon
  exact ⟨V,hV,hKV,hVU,fun k hk x hx => hBound ⟨k,by omega⟩ x hx⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.finite_active_inputs_parameter_neighborhood
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.finite_weighted_jets_neighborhood
