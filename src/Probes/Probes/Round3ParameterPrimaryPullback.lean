import Probes.Round3ParameterChartPullback
import Probes.Round3ParameterPrimaryNative

/-! Pulling the same primary data through a genuine parameter chart.  No linear
structure on the physical parameter manifold is used.  The finite polynomial
still differentiates only the spatial variable, so its exact naturality is
proved from the literal normal datum and chart conjugation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Manifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
variable {E H M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P] [TopologicalSpace Q]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
  (F : P → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p))
  (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
  (B : OpenPartialHomeomorph P Q)

def round3ParameterPrimaryPullback :
    Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β)
      (fun t => F (B.symm t)) where
  phase := fun ν z => g.phase ν (B.symm z.1,z.2)
  cutoff := fun ν z => g.cutoff ν (B.symm z.1,z.2)
  normal := fun ν z => g.normal ν (B.symm z.1,z.2)
  linearArgument := fun ν t x => g.linearArgument ν (B.symm t) x
  eta := fun ν β z => g.eta ν β (B.symm z.1,z.2)
  chart := fun ν β => round3ParameterChartPullback B (g.chart ν β)
  inverse := fun ν β t x => g.inverse ν β (B.symm t) x
  normal_mem := by
    intro ν β z hz
    exact g.normal_mem ν β (B.symm z.1,z.2)
      ((round3ParameterChartPullback_target B (g.chart ν β) z).mp hz).2.1

variable
  (hg : ∀ ν β, Round3ParameterChartPreserves (g.chart ν β))
  (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
  (length : ℕ) (tau : ℝ)

include hg

 theorem round3ParameterPrimary_pullback_localFree
    (ν : Λ) (β : Β) (t : Q) (ht : t ∈ B.target)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimaryLocalFree (fun t => F (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) tau ν β t x =
      round3ParameterPrimaryLocalFree F g input tau ν β (B.symm t) x := by
  classical
  have hi := round3ParameterChartPullback_target_iff B (g.chart ν β) (hg ν β) (t,x) ht
  by_cases hx : (B.symm t,x) ∈ (g.chart ν β).target
  · have hb := hi.mpr hx
    simp [round3ParameterPrimaryLocalFree, round3ParameterPrimaryPullback,
      round3ParameterPrimaryB, hx, hb] <;> rfl
  · have hb := mt hi.mp hx
    simp [round3ParameterPrimaryLocalFree, round3ParameterPrimaryPullback,
      round3ParameterPrimaryB, hx, hb] <;> rfl

 theorem round3ParameterPrimary_pullback_source
    (ν : Λ) (β : Β) (t : Q) (ht : t ∈ B.target)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimarySource (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) tau ν β (t,x) =
      round3ParameterPrimarySource F hF g input tau ν β (B.symm t,x) := by
  have hf := funext (round3ParameterPrimary_pullback_localFree F g B hg input tau ν β t ht)
  unfold round3ParameterPrimarySource
  rw [hf]
  rfl

 theorem round3ParameterPrimary_pullback_finiteU
    (ν : Λ) (β : Β) (t : Q) (ht : t ∈ B.target) :
    round3ParameterPrimaryFiniteU (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau ν β t =
      round3ParameterPrimaryFiniteU F hF g input length tau ν β (B.symm t) := by
  unfold round3ParameterPrimaryFiniteU
  have hs := funext (round3ParameterPrimary_pullback_source F hF g B hg input tau ν β t ht)
  rw [hs]
  rfl

 theorem round3ParameterPrimary_pullback_localZ
    (ch : Bool) (ν : Λ) (β : Β) (t : Q) (ht : t ∈ B.target)
    (x : EuclideanSpace ℝ (Fin (m+1))) :
    round3ParameterPrimaryLocalZ (fun t => F (B.symm t)) (fun t => hF (B.symm t))
      (round3ParameterPrimaryPullback F g B) (fun t => input (B.symm t)) length tau ch ν β (t,x) =
      round3ParameterPrimaryLocalZ F hF g input length tau ch ν β (B.symm t,x) := by
  unfold round3ParameterPrimaryLocalZ
  rw [round3ParameterPrimary_pullback_finiteU F hF g B hg input length tau ν β t ht]
  have hf := funext (round3ParameterPrimary_pullback_localFree F g B hg input tau ν β t ht)
  simp only [hf]
  rfl

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3ParameterPrimary_pullback_localZ
