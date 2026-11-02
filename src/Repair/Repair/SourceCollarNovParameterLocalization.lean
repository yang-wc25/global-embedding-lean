import Repair.SourceCollarNovParameterLocalBump
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

def sourceCollarNovFiniteUnitUnion {ι : Type*} [Fintype ι] (beta : ι → P → ℝ) (p : P) : ℝ :=
  1 - ∏ i, (1-beta i p)

theorem sourceCollarNov_finite_unit_union {ι : Type*} [Fintype ι]
    (beta : ι → P → ℝ) (hSmooth : ∀ i, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ (beta i))
    (hRange : ∀ i p, 0 ≤ beta i p ∧ beta i p ≤ 1)
    (U : Set P) (hSupport : ∀ i, tsupport (beta i) ⊆ U) :
    ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ (sourceCollarNovFiniteUnitUnion beta) ∧
    (∀ p, 0 ≤ sourceCollarNovFiniteUnitUnion beta p ∧ sourceCollarNovFiniteUnitUnion beta p ≤ 1) ∧
    tsupport (sourceCollarNovFiniteUnitUnion beta) ⊆ U ∧
    ∀ p, (∃ i, beta i p = 1) → sourceCollarNovFiniteUnitUnion beta p = 1 := by
  classical
  refine ⟨contMDiff_const.sub (ContMDiff.prod (fun i _ => contMDiff_const.sub (hSmooth i))),?_,?_,?_⟩
  · intro p
    have h0 : 0 ≤ ∏ i, (1-beta i p) := Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hRange i p).2)
    have h1 : (∏ i, (1-beta i p)) ≤ 1 := Finset.prod_le_one₀
      (fun i _ => sub_nonneg.mpr (hRange i p).2) (fun i _ => sub_le_self _ (hRange i p).1)
    change 0 ≤ 1-∏ i, (1-beta i p) ∧ 1-∏ i, (1-beta i p) ≤ 1
    constructor <;> linarith
  · have hSub : tsupport (sourceCollarNovFiniteUnitUnion beta) ⊆ ⋃ i, tsupport (beta i) := by
      apply closure_minimal _ (isClosed_iUnion_of_finite (fun i => isClosed_tsupport (beta i)))
      intro p hp
      by_contra hn
      have hZero (i) : beta i p = 0 := by
        by_contra hi
        exact hn (mem_iUnion.mpr ⟨i,subset_tsupport (beta i) hi⟩)
      apply hp
      simp only [sourceCollarNovFiniteUnitUnion,hZero,sub_zero,Finset.prod_const_one,sub_self]
    intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hSub hp)
    exact hSupport i hi
  · intro p hp
    obtain ⟨i,hi⟩ := hp
    have hProd : (∏ j, (1-beta j p)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi,sub_self])
    simp only [sourceCollarNovFiniteUnitUnion,hProd,sub_zero]

/-- The original local raw preparation supplies local chart protection and
unit values. It is not modified, and neither its BP/TP nor Q is enlarged. -/
theorem sourceCollarNov_parameter_localization
    {ι : Type*} [Fintype ι] (B : TensorBufferedChartFamily ι P Ep)
    (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (K U : Set P) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {BP TP : ℕ → ℝ} {D : ℕ} (RP : TensorLocalRawPreparation B K BP TP D) :
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ psi ∧ EqOn psi 1 V ∧
      tsupport psi ⊆ U ∧ (∀ p, 0 ≤ psi p ∧ psi p ≤ 1) := by
  classical
  have hLocal (p : K) : ∃ beta : P → ℝ, ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ beta ∧
      (∀ q, 0 ≤ beta q ∧ beta q ≤ 1) ∧ tsupport beta ⊆ U ∧ beta =ᶠ[𝓝 p.val] 1 := by
    obtain ⟨i,hi⟩ := RP.plateau_on p.val p.property
    exact sourceCollarNov_parameter_local_unit_bump (B.chart i) (hB i) (RP.raw i)
      (RP.smooth i) ((RP.inner_support i).trans (B.inner_subset i)) U hU p.val (hKU p.property) hi
  choose beta hSmooth hRange hSupport hOne using hLocal
  let V0 (p : K) : Set P := interior {q | beta p q = 1}
  have hV0 (p : K) : p.val ∈ V0 p := mem_interior_iff_mem_nhds.mpr (hOne p)
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover V0 (fun _ => isOpen_interior)
    (fun p hp => mem_iUnion.mpr ⟨⟨p,hp⟩,hV0 ⟨p,hp⟩⟩)
  let b : s → P → ℝ := fun p => beta p.val
  let psi := sourceCollarNovFiniteUnitUnion b
  let V : Set P := ⋃ p ∈ s, V0 p
  have hUnion := sourceCollarNov_finite_unit_union b
    (fun p => hSmooth p.val) (fun p => hRange p.val) U (fun p => hSupport p.val)
  refine ⟨psi,V,isOpen_biUnion (fun p _ => isOpen_interior),hs,?_,hUnion.1,?_,hUnion.2.2.1,hUnion.2.1⟩
  · intro p hp
    obtain ⟨q,hq,hpV⟩ := mem_iUnion₂.mp hp
    have hpOne : p ∈ {r : P | beta q r = 1} := interior_subset hpV
    exact hSupport q (subset_tsupport (beta q) (by change beta q p ≠ 0; rw [hpOne]; exact one_ne_zero))
  · intro p hp
    obtain ⟨q,hq,hpV⟩ := mem_iUnion₂.mp hp
    have hpOne : p ∈ {r : P | beta q r = 1} := interior_subset hpV
    exact hUnion.2.2.2 p ⟨⟨q,hq⟩,hpOne⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_parameter_localization
