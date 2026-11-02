import Smoothing.ParameterRound2TensorGermSpace
import Smoothing.ParameterRound2RepairNormAlgebra

/-!
# The finite part of the original native tensor germ space

This is an internal carrier, not a replacement of the public paper norm.
Its elements retain exactly the original native tensor and original samples.
Every seminorm is definitionally the literal original weighted norm. Unlike
the old all-germs seminorm it requires no compactness of the samples: each
actual field is admitted only after its original all-order finiteness is
proved. The smoothing/target and mean constructors provide that proof.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation.SourceCollarsBridge

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

private theorem original_cj_open_restrict
    {ι : Type*} [Fintype ι] {a q : ℕ} (j : ℕ)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O U S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hU : ∀ i, IsOpen (U i))
    (hUO : ∀ i, U i ⊆ O i) (hSU : ∀ i, S i ⊆ U i) :
    paperAtlasCj j f O S = paperAtlasCj j f U S := by
  simpa only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,
    pow_zero,one_mul,zero_add] using
    actual_paperAtlasWeighted_open_restrict j 0 1 f O U S hO hU hUO hSU

private theorem original_cj_zero
    {ι : Type*} [Fintype ι] {a q : ℕ} (j : ℕ) (O S : ι → Set (Fin a → ℝ)) :
    paperAtlasCj j (fun _ _ => (0 : Fin q → ℝ)) O S = 0 := by
  have hz (l : List (Fin a)) (V : Set (Fin a → ℝ)) :
      paperCoordinatePartial l (fun _ => 0) V = 0 := by
    induction l with
    | nil => rfl
    | cons k l ih =>
      funext x
      change lineDerivWithin ℝ (paperCoordinatePartial l (fun _ => 0) V) V x (Pi.single k 1) = 0
      rw [ih]
      simp [lineDerivWithin]
  simp [paperAtlasCj,paperCoordinateCj,hz]

/-- The same germ addition law, using actual finite original top orders. -/
theorem germ_weighted_add_le_of_finite
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T U : parameterRound2_originalTensorGermSpace A B S W) (base j : ℕ) (ell : ℝ)
    (hTf : paperAtlasCj (j+base) (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤)
    (hUf : paperAtlasCj (j+base) (incrementsOriginalTensorCoordinates A B U.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
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
  have he (f : (Fin A.count × Fin c) → (Fin (n+d) → ℝ) → Fin (n*n) → ℝ) :=
    actual_paperAtlasWeighted_open_restrict base j ell f
      (incrementsOriginalDifferentiation A B) V S
      (parameterRound2_originalDifferentiation_open A B) hV hVO hSV
  have hec (f : (Fin A.count × Fin c) → (Fin (n+d) → ℝ) → Fin (n*n) → ℝ) :=
    original_cj_open_restrict (j+base) f (incrementsOriginalDifferentiation A B) V S
      (parameterRound2_originalDifferentiation_open A B) hV hVO hSV
  rw [he,he,he]
  exact parameterRound2_paperAtlasWeighted_add_le base j ell _ _ V S hV hSV hT hU
    (by rwa [← hec]) (by rwa [← hec])

/-- Scalar multiplication preserves the unchanged weighted norm bound. -/
theorem germ_weighted_smul_le_of_finite
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W) (base j : ℕ) (ell a : ℝ)
    (hTf : paperAtlasCj (j+base) (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B (a • T).val)
      (incrementsOriginalDifferentiation A B) S ≤
    ENNReal.ofReal |a| * paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S := by
  let V := parameterRound2_tensorGermDomain A B S W T
  have ht := parameterRound2_tensorGermDomain_spec A B S W hSO T
  have he (f : (Fin A.count × Fin c) → (Fin (n+d) → ℝ) → Fin (n*n) → ℝ) :=
    actual_paperAtlasWeighted_open_restrict base j ell f
      (incrementsOriginalDifferentiation A B) V S (parameterRound2_originalDifferentiation_open A B)
      (fun i => (ht i).1) (fun i => (ht i).2.2.1) (fun i => (ht i).2.1)
  have hec := original_cj_open_restrict (j+base) (incrementsOriginalTensorCoordinates A B T.val)
    (incrementsOriginalDifferentiation A B) V S (parameterRound2_originalDifferentiation_open A B)
    (fun i => (ht i).1) (fun i => (ht i).2.2.1) (fun i => (ht i).2.1)
  rw [he,he]
  exact parameterRound2_paperAtlasWeighted_smul_le base j ell _ V S
    (fun i => (ht i).1) (fun i => (ht i).2.1) (fun i => (ht i).2.2.2)
    (by rwa [← hec]) a

/-- Internal submodule of the old native tensor germs: all literal original
Cj values are finite. The geometric domains and actual tensors are unchanged. -/
def finiteTensorGermSpace
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i) :
    Submodule ℝ (parameterRound2_originalTensorGermSpace A B S W) where
  carrier := {T | ∀ j, paperAtlasCj j (incrementsOriginalTensorCoordinates A B T.val)
    (incrementsOriginalDifferentiation A B) S ≠ ⊤}
  zero_mem' := by
    intro j
    have hzero : incrementsOriginalTensorCoordinates A B
        (0 : parameterRound2_originalTensorGermSpace A B S W).val = fun _ _ => 0 := by
      ext i y k
      simp [incrementsOriginalTensorCoordinates]
    rw [hzero,original_cj_zero]
    exact ENNReal.zero_ne_top
  add_mem' := by
    intro T U hT hU j
    have h := germ_weighted_add_le_of_finite A B S W hSO T U j 0 1
      (by simpa using hT j) (by simpa using hU j)
    simp only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,
      pow_zero,one_mul,zero_add] at h
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hT j,hU j⟩) h
  smul_mem' := by
    intro a T hT j
    have h := germ_weighted_smul_le_of_finite A B S W hSO T j 0 1 a (by simpa using hT j)
    simp only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,
      pow_zero,one_mul,zero_add] at h
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hT j)) h

instance finiteTensorGermSpace_addCommGroup
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i) :
    AddCommGroup (finiteTensorGermSpace A B S W hSO) :=
  @Submodule.addCommGroup ℝ (parameterRound2_originalTensorGermSpace A B S W)
    inferInstance inferInstance inferInstance (finiteTensorGermSpace A B S W hSO)

instance finiteTensorGermSpace_module
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i) :
    Module ℝ (finiteTensorGermSpace A B S W hSO) :=
  @Submodule.module ℝ (parameterRound2_originalTensorGermSpace A B S W)
    inferInstance inferInstance inferInstance (finiteTensorGermSpace A B S W hSO)

/-- Actual fields are inserted only with a proved all-order finite guard. -/
def finiteTensorGermOfCj
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W)
    (hT : ∀ j, paperAtlasCj j (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    finiteTensorGermSpace A B S W hSO := ⟨T,hT⟩

theorem finiteTensorGermOfCj_value
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : parameterRound2_originalTensorGermSpace A B S W)
    (hT : ∀ j, paperAtlasCj j (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤) :
    (finiteTensorGermOfCj A B S W hSO T hT).val.val = T.val := rfl

theorem finiteTensorGerm_weighted_finite
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (T : finiteTensorGermSpace A B S W hSO) (base j : ℕ) (ell : ℝ) :
    paperAtlasWeighted base j ell (incrementsOriginalTensorCoordinates A B T.val.val)
      (incrementsOriginalDifferentiation A B) S ≠ ⊤ :=
  parameterRound2_paperAtlasWeighted_finite_of_topOrder base j ell _ _ S (T.property (j+base))

/-- No compactness and no changed norm: the exact real original weighted value. -/
def finiteTensorGermSeminorm
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (j : ℕ) : Seminorm ℝ (finiteTensorGermSpace A B S W hSO) := by
  let w := fun T : finiteTensorGermSpace A B S W hSO =>
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val.val)
      (incrementsOriginalDifferentiation A B) S
  have hfinite (T) : w T ≠ ⊤ := finiteTensorGerm_weighted_finite A B S W hSO T 0 j ell
  apply Seminorm.ofSMulLE (𝕜 := ℝ) (fun T => (w T).toReal)
  · have h := germ_weighted_smul_le_of_finite A B S W hSO
      (0 : finiteTensorGermSpace A B S W hSO).val 0 j ell 0
      ((0 : finiteTensorGermSpace A B S W hSO).property (j+0))
    simp only [zero_smul,abs_zero,ENNReal.ofReal_zero,zero_mul] at h
    have hz : w 0 = 0 := le_antisymm h (by positivity)
    rw [hz,ENNReal.toReal_zero]
  · intro T U
    have h := germ_weighted_add_le_of_finite A B S W hSO T.val U.val 0 j ell
      (T.property (j+0)) (U.property (j+0))
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite T,hfinite U⟩) h
    rw [ENNReal.toReal_add (hfinite T) (hfinite U)] at hh
    exact hh
  · intro a T
    have h := germ_weighted_smul_le_of_finite A B S W hSO T.val 0 j ell a (T.property (j+0))
    have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite T)) h
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg a)] at hh
    exact hh

theorem finiteTensorGermSeminorm_apply
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (j : ℕ) (T : finiteTensorGermSpace A B S W hSO) :
    finiteTensorGermSeminorm A B S W hSO ell j T =
      (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val.val)
        (incrementsOriginalDifferentiation A B) S).toReal := rfl

theorem finiteTensorGermSeminorm_eq_original
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) (j : ℕ) (T : finiteTensorGermSpace A B S W hSO) :
    finiteTensorGermSeminorm A B S W hSO ell j T =
      parameterRound2_originalTensorGermSeminorm A B S W hS hSO ell j T.val := rfl

theorem finiteTensorGermSeminorm_mono
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (n+d) → ℝ)) (W : Set (P × M))
    (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation A B i)
    (ell : ℝ) {j k : ℕ} (hjk : j ≤ k) (T : finiteTensorGermSpace A B S W hSO) :
    finiteTensorGermSeminorm A B S W hSO ell j T ≤
      finiteTensorGermSeminorm A B S W hSO ell k T := by
  apply ENNReal.toReal_mono (finiteTensorGerm_weighted_finite A B S W hSO T 0 k ell)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
  intro i hi hik
  positivity

end GlobalEmbedding.Continuation.SourceCollarsBridge
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.finiteTensorGermSpace
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.finiteTensorGermSeminorm
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.finiteTensorGermSeminorm_apply
#print axioms GlobalEmbedding.Continuation.SourceCollarsBridge.finiteTensorGermSeminorm_mono
