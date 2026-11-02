import GlobalEmbedding.Paper.TrueSecondFormEvaluation
import GlobalEmbedding.Paper.FreeGramRightInverse

/-!
# Actual transverse reconstruction in the SAME true normal space

Source: `main.tex`, lem:increments620–629, equation(6.2). W2.
Beta is the literal pairing with the original true second form, and J is built
from its actual adjoint using the accepted Gram right inverse. No cancellation
or right-inverse identity is supplied as an assumption.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {m N : ℕ}

/-- The actual true transverse second-form columns, indexed once with diagonals.
The directions are the actual adapted coordinate transverse vectors in the same
tangent space. Values lie in the original true normalSpace. Source: beta in620. -/
def incrementsTransverseColumns (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x) :
    {p : Fin m × Fin m // p.1 ≤ p.2} → normalSpace (I := I) F x :=
  fun ij ↦ trueSecondForm F hF x
    (symmetricSquareProduct (TangentSpace I x) (e ij.val.1) (e ij.val.2))

/-- The literal actual beta: pair a true normal with each original B_ab.
Native Euclidean coordinates preserve the once-sorted data tuple, without a norm
isometry claim or a replacement data space. Source: beta(v)=(<B_ab,v>) in620. -/
def incrementsTransversePairing (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x) :
    normalSpace (I := I) F x →L[ℝ]
      EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} :=
  (EuclideanSpace.equiv {p : Fin m × Fin m // p.1 ≤ p.2} ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ij ↦ innerSL ℝ (incrementsTransverseColumns F hF x e ij))

/-- Actual beta evaluates to the original true-second-form inner product.
This computes the native coordinate and inner-product maps. Source:620. -/
theorem incrementsTransversePairing_apply (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x) (ν : normalSpace (I := I) F x)
    (q : {p : Fin m × Fin m // p.1 ≤ p.2}) :
    incrementsTransversePairing F hF x e ν q =
      inner ℝ (incrementsTransverseColumns F hF x e q) ν := rfl

/-- The original J uses precisely beta* as the injective frame.
It is the existing Gram reconstruction, not a newly constructed inverse. Source:620. -/
def incrementsTransverseRightInverse (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x) :
    EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2} →L[ℝ] normalSpace (I := I) F x :=
  freeGramRightInverse (incrementsTransversePairing F hF x e).adjoint

/-- This SAME J is literally beta*(beta beta*)^-1. Only unfold the accepted
definition and native double-adjoint identity. Source: actual J in620. -/
theorem incrementsTransverseRightInverse_formula (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x) :
    let β := incrementsTransversePairing F hF x e
    incrementsTransverseRightInverse F hF x e =
      β.adjoint.comp (β.comp β.adjoint).inverse := by
  simp only [incrementsTransverseRightInverse, freeGramRightInverse,
    ContinuousLinearMap.adjoint_adjoint]

/-- The original actual beta-Gram margin implies beta* injective; the accepted
Gram right-inverse theorem with frame beta* gives beta J=Id. The invertibility
input is the actual operator from(6.2), not a desired cancellation assumption.
No generic inverse or normal construction is reproved. Source:620–623. -/
theorem incrementsTransverseRightInverse_spec (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x)
    (hG : ((incrementsTransversePairing F hF x e).comp
      (incrementsTransversePairing F hF x e).adjoint).IsInvertible) :
    (incrementsTransversePairing F hF x e).comp
      (incrementsTransverseRightInverse F hF x e) = ContinuousLinearMap.id ℝ _ := by
  let β := incrementsTransversePairing F hF x e
  have hinj : Function.Injective β.adjoint := by
    intro u v huv
    exact hG.injective (congrArg β huv)
  have hi := freeGramRightInverse_spec β.adjoint hinj
  simpa only [ContinuousLinearMap.adjoint_adjoint, incrementsTransverseRightInverse, β]
    using hi

/-- The actual reconstructed normal solves every original transverse row.
Apply the actual beta to v_f+JT−Jh/2. Its true right-inverse identity and actual
free-normal condition give T−h/2. Evaluate the literal original B_ab row; the
transverse metric expression 2(T_ab−<B_ab,v>)−h_ab is exactly zero.
Source: the transverse elimination immediately preceding(6.2). -/
theorem increments_actual_transverse_reconstruction (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F) (x : M)
    (e : Fin m → TangentSpace I x)
    (hG : ((incrementsTransversePairing F hF x e).comp
      (incrementsTransversePairing F hF x e).adjoint).IsInvertible)
    (vf : normalSpace (I := I) F x)
    (hfree : incrementsTransversePairing F hF x e vf = 0)
    (T h : EuclideanSpace ℝ {p : Fin m × Fin m // p.1 ≤ p.2})
    (q : {p : Fin m × Fin m // p.1 ≤ p.2}) :
    2 * (T q - inner ℝ (incrementsTransverseColumns F hF x e q)
      (vf + incrementsTransverseRightInverse F hF x e T -
        (1 / 2 : ℝ) • incrementsTransverseRightInverse F hF x e h)) - h q = 0 := by
  let β := incrementsTransversePairing F hF x e
  let J := incrementsTransverseRightInverse F hF x e
  have hs := incrementsTransverseRightInverse_spec F hF x e hG
  have hJT : β (J T) = T := congrArg (fun L ↦ L T) hs
  have hJh : β (J h) = h := congrArg (fun L ↦ L h) hs
  have hv : β (vf + J T - (1 / 2 : ℝ) • J h) = T - (1 / 2 : ℝ) • h := by
    rw [map_sub, map_add, map_smul, hfree, hJT, hJh, zero_add]
  have hq := congrArg (fun z ↦ z q) hv
  change inner ℝ (incrementsTransverseColumns F hF x e q)
    (vf + J T - (1 / 2 : ℝ) • J h) = T q - (1 / 2 : ℝ) * h q at hq
  change 2 * (T q - inner ℝ (incrementsTransverseColumns F hF x e q)
    (vf + J T - (1 / 2 : ℝ) • J h)) - h q = 0
  linarith

end GlobalEmbedding.Paper
