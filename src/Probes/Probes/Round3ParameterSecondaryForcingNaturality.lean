import Probes.Round3ParameterSecondaryPullback

/-! The actual inverse tensor forcing commutes with genuine parameter charts.
Both spatial Jacobian factors are kept.  Preservation of the parameter is used
only on the true target; arbitrary off-target inverse values remain allowed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

section TensorTransport
variable {m : ℕ} {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Tensor" => D →L[ℝ] D →L[ℝ] ℝ

def round3ParameterSecondaryTransition (c : Round3ParameterSecondaryChoice P M m) :
    OpenPartialHomeomorph (P × D) (P × D) :=
  ((OpenPartialHomeomorph.refl P).prod c.host).symm.trans c.chart

theorem round3ParameterSecondaryTransition_pullback_spatialJacobian
    (c : Round3ParameterSecondaryChoice P M m) (B : OpenPartialHomeomorph P Q)
    (t : Q) (x : D) :
    actualJointSpatialJacobian (round3ParameterSecondaryTransition (c.pullback B)).symm (t,x) =
      actualJointSpatialJacobian (round3ParameterSecondaryTransition c).symm (B.symm t,x) := rfl

theorem round3ParameterInverseForcing_pullback
    (c : Round3ParameterSecondaryChoice P M m) (B : OpenPartialHomeomorph P Q)
    (hc : Round3ParameterChartPreserves c.chart)
    (A : P × D → Tensor) (AQ : Q × D → Tensor)
    (hA : ∀ t ∈ B.target, ∀ x, AQ (t,x) = A (B.symm t,x))
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t,x) ∈ c.chart.target) :
    round3ParameterInverseForcing (round3ParameterSecondaryTransition (c.pullback B))
      ((c.pullback B).cutoff ∘ ((OpenPartialHomeomorph.refl Q).prod c.host).symm) AQ (t,x) =
      round3ParameterInverseForcing (round3ParameterSecondaryTransition c)
        (c.cutoff ∘ ((OpenPartialHomeomorph.refl P).prod c.host).symm) A (B.symm t,x) := by
  have hp := round3ParameterChartPreserves_inverse c.chart hc (B.symm t,x) hx
  unfold round3ParameterInverseForcing round3ParameterInverseForcingTensor
  rw [round3ParameterSecondaryTransition_pullback_spatialJacobian]
  apply congrArg actualTensorBasisCoefficients
  change c.cutoff (B.symm (B (c.chart.symm (B.symm t,x)).1),
        c.host.symm (c.host (c.chart.symm (B.symm t,x)).2)) •
      (AQ (B (c.chart.symm (B.symm t,x)).1,c.host (c.chart.symm (B.symm t,x)).2)).bilinearComp _ _ =
    c.cutoff ((c.chart.symm (B.symm t,x)).1,
        c.host.symm (c.host (c.chart.symm (B.symm t,x)).2)) •
      (A ((c.chart.symm (B.symm t,x)).1,c.host (c.chart.symm (B.symm t,x)).2)).bilinearComp _ _
  rw [hp, B.right_inv ht, hA t ht]
end TensorTransport

section Actual
variable {m N : ℕ} {P Q M : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
variable (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))))
    (m := m) (Λ := Label) (Β := SubPrimary) F)
  (B : OpenPartialHomeomorph P Q)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
include hg

theorem round3ParameterSecondary_pullback_realForcing
    (r : (Label × Label) × Fin 4) (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart)
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t,x) ∈ c.chart.target) :
    round3ParameterSecondaryRealForcing (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta r (c.pullback B) (t,x) =
      round3ParameterSecondaryRealForcing F hF g input length tau delta r c (B.symm t,x) := by
  apply round3ParameterInverseForcing_pullback c B hc _ _ _ t ht x hx
  intro u hu y
  apply congrArg actualRealTensorAssembly
  exact round3ParameterSecondary_pullback_quadratic F hF g B hg input length tau delta c.host r u hu y

theorem round3ParameterSecondary_pullback_imagForcing
    (r : (Label × Label) × Fin 4) (c : Round3ParameterSecondaryChoice P M m)
    (hc : Round3ParameterChartPreserves c.chart)
    (t : Q) (ht : t ∈ B.target) (x : D) (hx : (B.symm t,x) ∈ c.chart.target) :
    round3ParameterSecondaryImagForcing (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta r (c.pullback B) (t,x) =
      round3ParameterSecondaryImagForcing F hF g input length tau delta r c (B.symm t,x) := by
  apply round3ParameterInverseForcing_pullback c B hc _ _ _ t ht x hx
  intro u hu y
  apply congrArg actualImaginaryTensorAssembly
  exact round3ParameterSecondary_pullback_quadratic F hF g B hg input length tau delta c.host r u hu y
end Actual
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterInverseForcing_pullback
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondary_pullback_realForcing
