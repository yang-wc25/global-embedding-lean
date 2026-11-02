import Smoothing.ParameterRound2NativeTensorGermNorms
import Smoothing.ParameterRound2TensorSeminorm

/-! Genuine native symmetric tensor fields smooth on some joint neighborhood
of the actual samples. Each field may have its own neighborhood. The carrier
retains the actual tensor values, and its seminorm is exactly the original
paper norm. This permits the finite positivity neighborhoods of the original
construction without requiring smoothness on one entire reserve ball. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

def parameterRound2_originalTensorGermSpace
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M)) :
    Submodule ℝ ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x)) where
  carrier := {T | (∀ i, ∃ U : Set (Fin (n+d) → ℝ), IsOpen U ∧ S i ⊆ U ∧
      ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T i) U) ∧
    ∀ z ∈ W, (T z.1 z.2).IsSymm}
  zero_mem' := by
    constructor
    · intro i
      refine ⟨univ,isOpen_univ,subset_univ _,?_⟩
      exact (contDiffOn_const : ContDiffOn ℝ ∞
        (fun _ : Fin (n+d) → ℝ => (0 : Fin (n*n) → ℝ)) univ)
    · exact fun z hz => LinearMap.BilinForm.isSymm_zero
  add_mem' := by
    intro T U hT hU
    constructor
    · intro i
      obtain ⟨OT,hOT,hST,hregT⟩ := hT.1 i
      obtain ⟨OU,hOU,hSU,hregU⟩ := hU.1 i
      exact ⟨OT ∩ OU,hOT.inter hOU,fun z hz => ⟨hST hz,hSU hz⟩,
        (hregT.mono inter_subset_left).add (hregU.mono inter_subset_right)⟩
    · exact fun z hz => (hT.2 z hz).add (hU.2 z hz)
  smul_mem' := by
    intro a T hT
    constructor
    · intro i
      obtain ⟨O,hO,hSO,hreg⟩ := hT.1 i
      exact ⟨O,hO,hSO,hreg.const_smul a⟩
    · exact fun z hz => (hT.2 z hz).smul a

instance parameterRound2_originalTensorGermSpace_addCommGroup
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M)) :
    AddCommGroup (parameterRound2_originalTensorGermSpace A B S W) :=
  @Submodule.addCommGroup ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalTensorGermSpace A B S W)

instance parameterRound2_originalTensorGermSpace_module
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M)) :
    Module ℝ (parameterRound2_originalTensorGermSpace A B S W) :=
  @Submodule.module ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalTensorGermSpace A B S W)

def parameterRound2_tensorGermDomain
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (T : parameterRound2_originalTensorGermSpace A B S W) (i : Fin A.count × Fin c) :
    Set (Fin (n+d) → ℝ) :=
  incrementsOriginalDifferentiation A B i ∩ Classical.choose (T.property.1 i)

theorem parameterRound2_tensorGermDomain_spec
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W) (i : Fin A.count × Fin c) :
    IsOpen (parameterRound2_tensorGermDomain A B S W T i) ∧
    S i ⊆ parameterRound2_tensorGermDomain A B S W T i ∧
    parameterRound2_tensorGermDomain A B S W T i ⊆ incrementsOriginalDifferentiation A B i ∧
    ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T.val i)
      (parameterRound2_tensorGermDomain A B S W T i) := by
  have h := Classical.choose_spec (T.property.1 i)
  exact ⟨(parameterRound2_originalDifferentiation_open A B i).inter h.1,
    fun y hy => ⟨hSO i hy,h.2.1 hy⟩,inter_subset_left,h.2.2.mono inter_subset_right⟩

theorem parameterRound2_tensorGerm_weighted_finite
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ := by
  let U := parameterRound2_tensorGermDomain A B S W T
  have hs := parameterRound2_tensorGermDomain_spec A B S W hSO T
  rw [actual_paperAtlasWeighted_open_restrict base j ell _ _ U S
    (parameterRound2_originalDifferentiation_open A B) (fun i => (hs i).1)
    (fun i => (hs i).2.2.1) (fun i => (hs i).2.1)]
  exact parameterRound2_paperAtlasWeighted_finite_of_compact _ U S S
    (fun i => (hs i).1) hS (fun _ => Subset.rfl) (fun i => (hs i).2.1)
    (fun i => (hs i).2.2.2) base j ell

theorem parameterRound2_tensorGerm_weighted_add_le
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T U : parameterRound2_originalTensorGermSpace A B S W) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B (T+U).val)
      (incrementsOriginalDifferentiation A B) S ≤
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S +
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B U.val)
      (incrementsOriginalDifferentiation A B) S := by
  let OT := parameterRound2_tensorGermDomain A B S W T
  let OU := parameterRound2_tensorGermDomain A B S W U
  let V := fun i => OT i ∩ OU i
  have ht := parameterRound2_tensorGermDomain_spec A B S W hSO T
  have hu := parameterRound2_tensorGermDomain_spec A B S W hSO U
  have hV : ∀ i, IsOpen (V i) := fun i => (ht i).1.inter (hu i).1
  have hSV : ∀ i, S i ⊆ V i := fun i y hy => ⟨(ht i).2.1 hy,(hu i).2.1 hy⟩
  have hVO : ∀ i, V i ⊆ incrementsOriginalDifferentiation A B i :=
    fun i y hy => (ht i).2.2.1 hy.1
  have hT : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T.val i) (V i) :=
    fun i => (ht i).2.2.2.mono inter_subset_left
  have hU : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B U.val i) (V i) :=
    fun i => (hu i).2.2.2.mono inter_subset_right
  have he (f : (Fin A.count × Fin c) → (Fin (n+d) → ℝ) → Fin (n*n) → ℝ) := actual_paperAtlasWeighted_open_restrict base j ell f
    (incrementsOriginalDifferentiation A B) V S
    (parameterRound2_originalDifferentiation_open A B) hV hVO hSV
  rw [he,he,he]
  exact parameterRound2_paperAtlasWeighted_add_le base j ell _ _ V S hV hSV hT hU
    (parameterRound2_paperAtlasCj_finite_of_compact _ V S hV hS hSV hT (j+base))
    (parameterRound2_paperAtlasCj_finite_of_compact _ V S hV hS hSV hU (j+base))

theorem parameterRound2_tensorGerm_weighted_smul_le
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W) (base j : ℕ) (ell a : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B (a • T).val)
      (incrementsOriginalDifferentiation A B) S ≤
    ENNReal.ofReal |a| * paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S := by
  let V := parameterRound2_tensorGermDomain A B S W T
  have ht := parameterRound2_tensorGermDomain_spec A B S W hSO T
  have he (f : (Fin A.count × Fin c) → (Fin (n+d) → ℝ) → Fin (n*n) → ℝ) := actual_paperAtlasWeighted_open_restrict base j ell f
    (incrementsOriginalDifferentiation A B) V S (parameterRound2_originalDifferentiation_open A B)
    (fun i => (ht i).1) (fun i => (ht i).2.2.1) (fun i => (ht i).2.1)
  rw [he,he]
  exact parameterRound2_paperAtlasWeighted_smul_le base j ell _ V S
    (fun i => (ht i).1) (fun i => (ht i).2.1) (fun i => (ht i).2.2.2)
    (parameterRound2_paperAtlasCj_finite_of_compact _ V S
      (fun i => (ht i).1) hS (fun i => (ht i).2.1) (fun i => (ht i).2.2.2) (j+base)) a

def parameterRound2_originalTensorGermSeminorm
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (j : ℕ) : Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W) := by
  let w := fun T : parameterRound2_originalTensorGermSpace A B S W =>
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S
  have hfinite (T) : w T ≠ ⊤ := parameterRound2_tensorGerm_weighted_finite A B S W hS hSO T 0 j ell
  apply Seminorm.ofSMulLE (𝕜 := ℝ) (fun T => (w T).toReal)
  · have h := parameterRound2_tensorGerm_weighted_smul_le A B S W hS hSO 0 0 j ell 0
    simp only [zero_smul,abs_zero,ENNReal.ofReal_zero,zero_mul] at h
    have hz : w 0 = 0 := le_antisymm h (by positivity)
    rw [hz,ENNReal.toReal_zero]
  · intro T U
    have h := parameterRound2_tensorGerm_weighted_add_le A B S W hS hSO T U 0 j ell
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite T,hfinite U⟩) h
    rw [ENNReal.toReal_add (hfinite T) (hfinite U)] at hh
    exact hh
  · intro a T
    have h := parameterRound2_tensorGerm_weighted_smul_le A B S W hS hSO T 0 j ell a
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite T)) h
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg a)] at hh
    exact hh

theorem parameterRound2_originalTensorGermSeminorm_apply
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (j : ℕ) (T : parameterRound2_originalTensorGermSpace A B S W) :
    parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j T =
    (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S).toReal := rfl

theorem parameterRound2_originalTensorGermSeminorm_mono
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) {j k : ℕ} (hjk : j ≤ k) (T : parameterRound2_originalTensorGermSpace A B S W) :
    parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j T ≤
    parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell k T := by
  apply ENNReal.toReal_mono (parameterRound2_tensorGerm_weighted_finite A B S W hS hSO T 0 k ell)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro i hi hik
  positivity

#print axioms parameterRound2_originalTensorGermSeminorm
#print axioms parameterRound2_originalTensorGermSeminorm_apply
end GlobalEmbedding.Continuation
