import Repair.ReferenceOriginalParents

/-! Direct adapters from the actual original parent producer to the carrier
and original joint-norm interfaces used by the reference factories. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D

variable {A : BufferedAtlas M (EuclideanSpace ℝ (Fin n))}
  {B : TensorBufferedChartFamily (Fin c) P (EuclideanSpace ℝ (Fin d))}
  {sourceSupport : Fin A.count → Set M} {parameterSupport : Fin c → Set P}
  {outer theta : (Fin A.count × Fin c) → P × M → ℝ}
  {Outer Parent Transition : ℕ → ℝ} {Ds Dp : ℕ}
  (parents : RepairReferenceOriginalParentProperties A B sourceSupport parameterSupport
    outer theta Outer Parent Transition Ds Dp)

/-- The normalized parents retain the carriers of the same original raw
functions. The carrier need not contain the whole atlas inner set. -/
theorem repair_reference_original_parent_raw_carriers
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation A BS TS Ds)
    (RP : TensorLocalRawPreparation B univ BP TP Dp)
    (KS : Fin A.count → Set D) (KP : Fin c → Set Ep)
    (hS : ∀ i, tsupport (RS.raw i) ⊆ (A.chart i).source ∩ (A.chart i) ⁻¹' KS i)
    (hP : ∀ i, tsupport (RP.raw i) ⊆ (B.chart i).source ∩ (B.chart i) ⁻¹' KP i) :
    let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    let theta := round3ParameterProductParent A B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    (∀ i, tsupport (chi i) ⊆ ((B.chart i.2).prod (A.chart i.1)).source ∩
      ((B.chart i.2).prod (A.chart i.1)) ⁻¹' (KP i.2 ×ˢ KS i.1)) ∧
    ∀ i, tsupport (theta i) ⊆ ((B.chart i.2).prod (A.chart i.1)).source ∩
      ((B.chart i.2).prod (A.chart i.1)) ⁻¹' (KP i.2 ×ˢ KS i.1) := by
  intro chi theta
  have hChi (i) : tsupport (chi i) ⊆ ((B.chart i.2).prod (A.chart i.1)).source ∩
      ((B.chart i.2).prod (A.chart i.1)) ⁻¹' (KP i.2 ×ˢ KS i.1) := by
    intro z hz
    have h := parameterLocalProductCutoff_tsupport_subset A B _ _ i hz
    have hs := hS i.1 (squareNormalizedCutoff_tsupport_subset RS.raw i.1 h.2)
    have hp := hP i.2 (tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2 h.1)
    exact ⟨⟨hp.1,hs.1⟩,⟨hp.2,hs.2⟩⟩
  exact ⟨hChi,fun i => (round3ParameterProductParent_tsupport A B _ _ i).trans (hChi i)⟩

include parents in
theorem RepairReferenceOriginalParentProperties.outer_original_jets
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep) (parameterSet : Set P)
    (i owner : Fin A.count × Fin c) (j : ℕ) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalEvaluation A B.chart Omega Q parameterSet i) :
    ‖iteratedFDeriv ℝ j (outer owner ∘ ((B.chart i.2).prod (A.chart i.1)).symm)
      ((parameterTensorModelEquiv n d).symm y)‖ ≤ Outer j :=
  parents.outer_jets i owner j _ ⟨hy.1.2,hy.1.1⟩

include parents in
theorem RepairReferenceOriginalParentProperties.theta_original_jets
    (Omega : Fin A.count → Set D) (Q : Fin c → Set Ep) (parameterSet : Set P)
    (i owner : Fin A.count × Fin c) (j : ℕ) (z : X)
    (hz : parameterTensorModelEquiv n d z ∈
      incrementsOriginalEvaluation A B.chart Omega Q parameterSet i) :
    ‖iteratedFDeriv ℝ j (theta owner ∘ ((B.chart i.2).prod (A.chart i.1)).symm) z‖ ≤ Parent j := by
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv n d).symm_apply_apply z)
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv n d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv n d z)=z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv n d z)=z.2 at hx
  exact parents.theta_jets i owner j z
    ⟨by simpa only [hp] using hz.1.2,by simpa only [hx] using hz.1.1⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.repair_reference_original_parent_raw_carriers
#print axioms GlobalEmbedding.Continuation.RepairReferenceOriginalParentProperties.theta_original_jets
