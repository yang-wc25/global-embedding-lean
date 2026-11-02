import CompletionIntegration.CompactParameterLocalBump
import Repair.SourceCollarNovParameterLocalization
import Smoothing.TensorLocalPrepared

/-!
# Actual parameter localization with an unchanged original raw preparation

A finite collection of original-chart local unit bumps is chosen over the
given compact parameter set. Their finite complement product is globally
smooth, equals one on one open neighborhood of that compact set, and has
closed support in the given parameter-open set. This is qualitative
localization; no whole-target derivative budget is requested or supplied.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Metric Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {d : ℕ} {P : Type*} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- The original local raw preparation supplies local chart protection and
unit values. It is not modified, and neither its BP/TP nor Q is enlarged. -/
theorem completion_compact_parameter_localization
    {ι : Type*} [Fintype ι] (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {BP TP : ℕ → ℝ} {D : ℕ} (RP : TensorLocalRawPreparation B K BP TP D) :
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ psi ∧ EqOn psi 1 V ∧
      tsupport psi ⊆ U ∧ (∀ p, 0 ≤ psi p ∧ psi p ≤ 1) ∧ IsCompact (tsupport psi) := by
  classical
  have hLocal (p : K) : ∃ beta : P → ℝ, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ beta ∧
      (∀ q, 0 ≤ beta q ∧ beta q ≤ 1) ∧ tsupport beta ⊆ U ∧ beta =ᶠ[𝓝 p.val] 1 ∧ IsCompact (tsupport beta) := by
    obtain ⟨i,hi⟩ := RP.plateau_on p.val p.property
    exact completion_compact_parameter_local_unit_bump (B.chart i) (hB i) (RP.raw i)
      (RP.smooth i) ((RP.inner_support i).trans (B.inner_subset i)) U hU p.val (hKU p.property) hi
  choose beta hSmooth hRange hSupport hOne hCompact using hLocal
  let V0 (p : K) : Set P := interior {q | beta p q = 1}
  have hV0 (p : K) : p.val ∈ V0 p := mem_interior_iff_mem_nhds.mpr (hOne p)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V0 (fun _ => isOpen_interior)
    (fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩,hV0 ⟨p,hp⟩⟩)
  let b : s → P → ℝ := fun p => beta p.val
  let psi := sourceCollarNovFiniteUnitUnion b
  let V : Set P := ⋃ p ∈ s, V0 p
  have hUnion := sourceCollarNov_finite_unit_union b
    (fun p => hSmooth p.val) (fun p => hRange p.val) U (fun p => hSupport p.val)
  have hCompactUnion : IsCompact (⋃ p : s, tsupport (b p)) :=
    isCompact_iUnion (fun p => hCompact p.val)
  have hSupportUnion : tsupport psi ⊆ ⋃ p : s, tsupport (b p) :=
    (sourceCollarNov_finite_unit_union b (fun p => hSmooth p.val)
      (fun p => hRange p.val) (⋃ p : s, tsupport (b p))
      (fun p _ hp => mem_iUnion.mpr ⟨p,hp⟩)).2.2.1
  have hCompactPsi : IsCompact (tsupport psi) :=
    hCompactUnion.of_isClosed_subset (isClosed_tsupport _) hSupportUnion
  refine ⟨psi,V,isOpen_biUnion (fun p _ => isOpen_interior),hs,?_,hUnion.1,?_,
    hUnion.2.2.1,hUnion.2.1,hCompactPsi⟩
  · intro p hp
    obtain ⟨q,hq,hpV⟩ := mem_iUnion₂.mp hp
    have hpOne : p ∈ {r : P | beta q r = 1} := interior_subset hpV
    exact hSupport q (subset_tsupport (beta q) (by change beta q p ≠ 0; rw [hpOne]; exact one_ne_zero))
  · intro p hp
    obtain ⟨q,hq,hpV⟩ := mem_iUnion₂.mp hp
    have hpOne : p ∈ {r : P | beta q r = 1} := interior_subset hpV
    exact hUnion.2.2.2 p ⟨⟨q,hq⟩,hpOne⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.completion_compact_parameter_localization
