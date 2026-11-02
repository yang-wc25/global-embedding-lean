import Smoothing.ParameterRound2ActualModeLocality

/-! Restrict the actual primary charts to a proved joint open neighborhood.
The original fields, inverse functions, finite polynomial, subcutoffs and
normal data are unchanged. Every actual extension agrees on the neighborhood.
This is an exact locality result, without a smooth-output or norm assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def parameterRound2_restrictPrimaryFamily
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G) :
    IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F where
  phase := g.phase
  cutoff := g.cutoff
  normal := g.normal
  linearArgument := g.linearArgument
  eta := g.eta
  chart := fun ν β => (g.chart ν β).restrOpen G hG
  inverse := g.inverse
  normal_mem := fun ν β z hz => g.normal_mem ν β z hz.1

theorem parameterRound2_restrictPrimary_localFree
    (F : Ep → M → V)
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (β : Β) (z : X)
    (hz : z ∈ ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).target) :
    incrementsGlobalPrimaryLocalFree F (parameterRound2_restrictPrimaryFamily F g G hG)
      input tau ν β z.1 z.2 = incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 := by
  apply Subtype.ext
  simp only [incrementsGlobalPrimaryLocalFree,dif_pos hz,dif_pos hz.1]
  rfl

theorem parameterRound2_restrictPrimary_source
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (tau : ℝ) (ν : Λ) (β : Β) :
    EqOn (incrementsGlobalPrimarySource F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input tau ν β) (incrementsGlobalPrimarySource F hF g input tau ν β)
      ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).target := by
  intro z hz
  have hv := parameterRound2_restrictPrimary_localFree F g G hG input tau ν β z hz
  simp only [incrementsGlobalPrimarySource,incrementsModeSource,hv]
  rfl

theorem parameterRound2_restrictPrimary_finiteU
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (ν : Λ) (β : Β) (t : Ep) :
    EqOn (incrementsGlobalPrimaryFiniteU F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau ν β t) (incrementsGlobalPrimaryFiniteU F hF g input length tau ν β t)
      {x | (t,x) ∈ ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).target} := by
  let O := {x : D | (t,x) ∈ ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).target}
  have hO : IsOpen O := ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).open_target.preimage
    (continuous_const.prodMk continuous_id)
  exact parameterRound2_actual_modeSum_eqOn
    (incrementsModeComplexFirstOrderA (F t) (hF t) (g.inverse ν β t))
    (incrementsModeComplexFirstOrderB (F t) (hF t) (g.inverse ν β t))
    ((tau:ℂ)/Complex.I) length _ _ O hO (fun x hx =>
      parameterRound2_restrictPrimary_source F hF g G hG input tau ν β hx)


#print axioms parameterRound2_restrictPrimary_source
#print axioms parameterRound2_restrictPrimary_finiteU
end GlobalEmbedding.Continuation
