import Probes.Round3ParameterPrimaryGlobalNaturality
import Probes.Round3ParameterSecondaryNative

/-! Genuine parameter pullback of the secondary choices and of the actual
negative quadratic primary forcing.  Spatial derivatives compare whole spatial
slices at each target parameter, preserving all sine/cosine coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold Function
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {P Q M : Type*}
  [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  {Label SubPrimary : Type*} [Fintype Label] [DecidableEq Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

def Round3ParameterSecondaryChoice.pullback
    (c : Round3ParameterSecondaryChoice P M m) (B : OpenPartialHomeomorph P Q) :
    Round3ParameterSecondaryChoice Q M m where
  host := c.host
  chart := round3ParameterChartPullback B c.chart
  c := fun t => c.c (B.symm t)
  cutoff := fun z => c.cutoff (B.symm z.1,z.2)

variable (F : P → M → (EuclideanSpace ℝ (Fin N))) (hF : ∀ p, ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,(EuclideanSpace ℝ (Fin N))) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))) (m := m) (Λ := Label) (Β := SubPrimary) F)
  (B : OpenPartialHomeomorph P Q)
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) x))
  (length : ℕ) (tau delta : ℝ)
include hg

theorem round3ParameterSecondary_pullback_quadratic
    (e : OpenPartialHomeomorph M D) (r : (Label × Label) × Fin 4)
    (t : Q) (ht : t ∈ B.target) (x : D) :
    round3ParameterSecondaryQuadratic (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau delta e r (t,x) =
      round3ParameterSecondaryQuadratic F hF g input length tau delta e r (B.symm t,x) := by
  have hA (ch : Bool) (ν : Label) :
      (fun β y => delta • round3ParameterPrimaryExtension (fun t => F (B.symm t))
        (fun t => hF (B.symm t)) (round3ParameterPrimaryPullback F g B)
        (fun t => input (B.symm t)) length tau ch ν β (t,e.symm y)) =
      (fun β y => delta • round3ParameterPrimaryExtension F hF g input length tau ch ν β (B.symm t,e.symm y)) := by
    funext β y
    rw [round3ParameterPrimary_pullback_extension F hF g B hg input length tau ch ν β t ht]
  unfold round3ParameterSecondaryQuadratic incrementsSecondaryQuadraticForcing
    incrementsSecondaryPhysicalCoefficient
  dsimp only
  simp only [hA]
  rfl

omit hg in
 theorem round3ParameterSecondary_pullback_phase
    (r : (Label × Label) × Fin 4) (t : Q) (x : M) :
    round3ParameterSecondaryPhase (fun t => F (B.symm t)) (round3ParameterPrimaryPullback F g B) r (t,x) =
      round3ParameterSecondaryPhase F g r (B.symm t,x) := rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterSecondary_pullback_quadratic
