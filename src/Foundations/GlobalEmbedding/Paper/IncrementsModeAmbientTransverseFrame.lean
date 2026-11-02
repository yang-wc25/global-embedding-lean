import GlobalEmbedding.Paper.IncrementsModeFirstOrderCoefficients

/-!
# The SAME original transverse J in the ambient normal-column frame

Source: `main.tex`, lem:increments, (6.2), lines 620–643.
DAG: `increments-mode-ambient-transverse-frame`. Exclusive worker W2.
Native normal inclusion and the accepted Gram reconstruction are reused exactly.
-/

noncomputable section
open Manifold
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "P" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ P

/-- The actual ambient frame has the SAME once-sorted true normal B columns.
Source: the original beta-adjoint frame in (6.2), without choosing another norm. -/
def incrementsModeAmbientTransverseFrame (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) : Tdata →L[ℝ] V :=
  ∑ q : P, (EuclideanSpace.proj q).smulRight
    (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ : V)

/-- This literal finite column frame is exactly normal inclusion composed with
the ORIGINAL beta-adjoint. Native Euclidean inner coordinates identify the adjoint;
no new pairing operator or inverse is introduced. Source: (6.2). -/
theorem incrementsModeAmbientTransverseFrame_eq (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) :
    incrementsModeAmbientTransverseFrame F hF c x =
      (normalSpace (I := I) F (c x)).subtypeL.comp
        (incrementsTransversePairing F hF (c x)
          (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint := by
  let β := incrementsTransversePairing F hF (c x)
    (fun a ↦ incrementsModeCoordinateDirections c x a.succ)
  have hs (t : Tdata) : β.adjoint t = ∑ q : P,
      t q • incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ := by
    apply ext_inner_right ℝ
    intro ν
    rw [ContinuousLinearMap.adjoint_inner_left]
    have hp (q : P) : β ν q =
        inner ℝ (incrementsModeSecondForm F hF c x q.val.1.succ q.val.2.succ) ν := rfl
    rw [PiLp.inner_apply, sum_inner]
    apply Finset.sum_congr rfl
    intro q hq
    rw [hp]
    simp [real_inner_smul_left, mul_comm]
  apply ContinuousLinearMap.ext
  intro t
  simpa [incrementsModeAmbientTransverseFrame, β] using
    congrArg (fun ν : normalSpace (I := I) F (c x) ↦ (ν : V)) (hs t).symm

/-- SAME normal inclusion preserves the actual beta Gram operator.
This is native isometric-subtype adjoint composition, not a new inverse identity.
Source: actual Gram denominator of the original J in (6.2). -/
theorem incrementsModeAmbientTransverseFrame_gram (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) :
    let β := incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ)
    (incrementsModeAmbientTransverseFrame F hF c x).adjoint.comp
      (incrementsModeAmbientTransverseFrame F hF c x) = β.comp β.adjoint := by
  let β := incrementsTransversePairing F hF (c x)
    (fun a ↦ incrementsModeCoordinateDirections c x a.succ)
  let n := (normalSpace (I := I) F (c x)).subtypeL
  have hn : n.adjoint.comp n = ContinuousLinearMap.id ℝ _ := by
    exact (normalSpace (I := I) F (c x)).subtypeₗᵢ.adjoint_comp_self
  rw [incrementsModeAmbientTransverseFrame_eq, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  change (β.comp n.adjoint).comp (n.comp β.adjoint) = β.comp β.adjoint
  calc
    _ = β.comp ((n.adjoint.comp n).comp β.adjoint) := rfl
    _ = _ := by rw [hn, ContinuousLinearMap.id_comp]

/-- The actual included normal J is precisely the accepted ambient Gram reconstruction
of the SAME actual transverse columns. Both inverses are the literal SAME data-space
Gram inverse; no inverse uniqueness or replacement normal model is proved.
Source: J=beta*(beta beta*)^-1 in (6.2). -/
theorem incrementsModeCoordinateJ_ambient (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) :
    (normalSpace (I := I) F (c x)).subtypeL.comp (incrementsModeCoordinateJ F hF c x) =
      freeGramRightInverse (incrementsModeAmbientTransverseFrame F hF c x) := by
  have hJ := incrementsTransverseRightInverse_formula F hF (c x)
    (fun a ↦ incrementsModeCoordinateDirections c x a.succ)
  change incrementsModeCoordinateJ F hF c x = _ at hJ
  rw [hJ, freeGramRightInverse, incrementsModeAmbientTransverseFrame_gram,
    incrementsModeAmbientTransverseFrame_eq]
  rfl

/-- Pointwise ambient value of the SAME original J, for actual coefficient callers.
Source: the original J T and J h_H terms in (6.2). -/
theorem incrementsModeCoordinateJ_ambient_apply (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D) (t : Tdata) :
    (incrementsModeCoordinateJ F hF c x t : V) =
      freeGramRightInverse (incrementsModeAmbientTransverseFrame F hF c x) t :=
  congrArg (fun L : Tdata →L[ℝ] V ↦ L t) (incrementsModeCoordinateJ_ambient F hF c x)

/-- ORIGINAL actual beta-Gram invertibility implies injection of these SAME ambient
columns. No desired frame injection is assumed as an output premise.
Source: original local free/full-rank input used for (6.2). -/
theorem incrementsModeAmbientTransverseFrame_injective (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (x : D)
    (hG : ((incrementsTransversePairing F hF (c x)
      (fun a : Fin m ↦ incrementsModeCoordinateDirections c x a.succ)).comp
      (incrementsTransversePairing F hF (c x)
        (fun a : Fin m ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint).IsInvertible) :
    Function.Injective (incrementsModeAmbientTransverseFrame F hF c x) := by
  intro u v huv
  rw [incrementsModeAmbientTransverseFrame_eq] at huv
  have hfiber :
      (incrementsTransversePairing F hF (c x)
        (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint u =
      (incrementsTransversePairing F hF (c x)
        (fun a ↦ incrementsModeCoordinateDirections c x a.succ)).adjoint v :=
    Subtype.ext huv
  exact hG.injective (congrArg
    (incrementsTransversePairing F hF (c x)
      (fun a ↦ incrementsModeCoordinateDirections c x a.succ)) hfiber)

end GlobalEmbedding.Paper
