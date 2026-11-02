import Smoothing.ParameterRound2InitialCompact440
import GlobalEmbedding.Paper.MeanIterationFiniteReserve

/-!
# The actual original tensor weighted norm is a seminorm on genuine smooth fields

The space below consists of the SAME native tangent bilinear tensor fields
with their original joint-coordinate smoothness. It does not replace a tensor
by independent coordinate arrays. Compact original coordinate pieces imply
finiteness of every order. The seminorm is definitionally the real value of
the original paperAtlasWeighted, with no change of chart maximum, derivative
convention, parameter coordinates, or scale.

This supplies the previously missing mathematical interface for applying the
accepted finite backward mean reserve theorem to the original tensor norms.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Manifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d c : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)

/-- Genuine native tensor fields, with the original full-joint coordinate
smoothness predicate. Addition and scaling are the actual native operations. -/
def parameterRound2_originalSmoothTensorSpace
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    Submodule ℝ ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)) where
  carrier := {T | ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B T i)
    (incrementsOriginalDifferentiation A B i)}
  zero_mem' := by
    intro i
    exact (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Fin (n + d) → ℝ => (0 : Fin (n * n) → ℝ)) _)
  add_mem' := by
    intro T U hT hU i
    exact (hT i).add (hU i)
  smul_mem' := by
    intro a T hT i
    exact (hT i).const_smul a

instance parameterRound2_originalSmoothTensorSpace_addCommGroup
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    AddCommGroup (parameterRound2_originalSmoothTensorSpace A B) :=
  @Submodule.addCommGroup ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalSmoothTensorSpace A B)

instance parameterRound2_originalSmoothTensorSpace_module
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep) :
    Module ℝ (parameterRound2_originalSmoothTensorSpace A B) :=
  @Submodule.module ℝ
    ((p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    inferInstance inferInstance inferInstance (parameterRound2_originalSmoothTensorSpace A B)

/-- Compact control proves actual weighted finiteness for every genuine
smooth native field and every fixed observation order. -/
theorem parameterRound2_smoothTensor_weighted_finite
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (T : parameterRound2_originalSmoothTensorSpace A B) (j : ℕ) (ell : ℝ) :
    paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val)
      (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ) ≠ ⊤ := by
  let O := incrementsOriginalDifferentiation A B
  let S := incrementsOriginalEvaluation A B Omega Q univ
  exact parameterRound2_paperAtlasWeighted_finite_of_compact _ O S S
    (parameterRound2_originalDifferentiation_open A B)
    (parameterRound2_originalEvaluation_univ_compact A B Omega Q hOmega hQ hOmegaTarget hQTarget)
    (fun _ => Subset.rfl) (fun _ _ hy => hy.1) T.property 0 j ell

/-- The original full-joint weighted norm itself, now with proved seminorm
laws. This is an actual norm bridge, not a changed analytic quantity. -/
def parameterRound2_originalTensorSeminorm
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (ell : ℝ) (j : ℕ) : Seminorm ℝ (parameterRound2_originalSmoothTensorSpace A B) := by
  let O := incrementsOriginalDifferentiation A B
  let S := incrementsOriginalEvaluation A B Omega Q univ
  let coords := fun T : parameterRound2_originalSmoothTensorSpace A B =>
    incrementsOriginalTensorCoordinates A B T.val
  let W := fun T : parameterRound2_originalSmoothTensorSpace A B => paperAtlasWeighted 0 j ell (coords T) O S
  have hO : ∀ i, IsOpen (O i) := parameterRound2_originalDifferentiation_open A B
  have hS : ∀ i, IsCompact (S i) := parameterRound2_originalEvaluation_univ_compact
    A B Omega Q hOmega hQ hOmegaTarget hQTarget
  have hSO : ∀ i, S i ⊆ O i := fun _ _ hy => hy.1
  have hfinite (T : parameterRound2_originalSmoothTensorSpace A B) : W T ≠ ⊤ :=
    parameterRound2_smoothTensor_weighted_finite A B Omega Q hOmega hQ hOmegaTarget hQTarget T j ell
  have htop (T : parameterRound2_originalSmoothTensorSpace A B) : paperAtlasCj (j+0) (coords T) O S ≠ ⊤ :=
    parameterRound2_paperAtlasCj_finite_of_compact (coords T) O S hO hS hSO T.property (j+0)
  apply Seminorm.ofSMulLE (𝕜 := ℝ) (fun T => (W T).toReal)
  · have hz := parameterRound2_paperAtlasWeighted_smul_le 0 j ell (coords 0) O S hO hSO
      (0 : parameterRound2_originalSmoothTensorSpace A B).property (htop 0) 0
    have heq : (fun i x => (0 : ℝ) • coords 0 i x) = coords 0 := by
      ext i x k
      simp [coords, incrementsOriginalTensorCoordinates]
    rw [heq,abs_zero,ENNReal.ofReal_zero,zero_mul] at hz
    have hz' : W 0 = 0 := le_antisymm hz (by positivity)
    rw [hz',ENNReal.toReal_zero]
  · intro T U
    have ha := parameterRound2_paperAtlasWeighted_add_le 0 j ell (coords T) (coords U) O S hO hSO
      T.property U.property (htop T) (htop U)
    have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinite T,hfinite U⟩) ha
    rw [ENNReal.toReal_add (hfinite T) (hfinite U)] at hr
    exact hr
  · intro a T
    have heq : coords (a • T) = fun i x => a • coords T i x := by
      ext i x k
      simp [coords, incrementsOriginalTensorCoordinates]
    have hs := parameterRound2_paperAtlasWeighted_smul_le 0 j ell (coords T) O S hO hSO T.property (htop T) a
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite T)) hs
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg a)] at hr
    change (paperAtlasWeighted 0 j ell (coords (a • T)) O S).toReal ≤ _
    rw [heq]
    simpa only [Real.norm_eq_abs] using hr

/-- Exact identity with the original norm, not merely norm equivalence. -/
theorem parameterRound2_originalTensorSeminorm_apply
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (ell : ℝ) (j : ℕ) (T : parameterRound2_originalSmoothTensorSpace A B) :
    parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j T =
      (paperAtlasWeighted 0 j ell (incrementsOriginalTensorCoordinates A B T.val)
        (incrementsOriginalDifferentiation A B) (incrementsOriginalEvaluation A B Omega Q univ)).toReal := rfl

/-- Increasing the observation order increases the original weighted sum.
This is exactly the monotonicity needed by the accepted backward reserve. -/
theorem parameterRound2_originalTensorSeminorm_mono
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, IsCompact (Omega i)) (hQ : ∀ i, IsCompact (Q i))
    (hOmegaTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQTarget : ∀ i, Q i ⊆ (B i).target)
    (ell : ℝ) {j k : ℕ} (hjk : j ≤ k) (T : parameterRound2_originalSmoothTensorSpace A B) :
    parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell j T ≤
      parameterRound2_originalTensorSeminorm A B Omega Q hOmega hQ hOmegaTarget hQTarget ell k T := by
  apply ENNReal.toReal_mono
    (parameterRound2_smoothTensor_weighted_finite A B Omega Q hOmega hQ hOmegaTarget hQTarget T k ell)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro i hi hik
    positivity

#print axioms parameterRound2_originalTensorSeminorm
#print axioms parameterRound2_originalTensorSeminorm_apply
#print axioms parameterRound2_originalTensorSeminorm_mono
end
end GlobalEmbedding.Continuation
