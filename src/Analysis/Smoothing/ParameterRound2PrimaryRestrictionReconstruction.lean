import Smoothing.ParameterRound2PrimaryRestriction
import Smoothing.ParameterRound2GlobalCorrectionIdentity

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

theorem parameterRound2_restrictPrimary_localZ
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) (z : X)
    (hz : z ∈ ((parameterRound2_restrictPrimaryFamily F g G hG).chart ν β).target) :
    incrementsGlobalPrimaryLocalZ F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν β z =
      incrementsGlobalPrimaryLocalZ F hF g input length tau realChannel ν β z := by
  let g' := parameterRound2_restrictPrimaryFamily F g G hG
  let O := {x : D | (z.1,x) ∈ (g'.chart ν β).target}
  let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
    if realChannel then incrementsModeRealPart else incrementsModeImagPart
  have hO : IsOpen O := (g'.chart ν β).open_target.preimage (continuous_const.prodMk continuous_id)
  have hu : (fun x => ch (incrementsGlobalPrimaryFiniteU F hF g' input length tau ν β z.1 x)) =ᶠ[𝓝 z.2]
      (fun x => ch (incrementsGlobalPrimaryFiniteU F hF g input length tau ν β z.1 x)) := by
    filter_upwards [hO.mem_nhds hz] with x hx
    exact congrArg ch (parameterRound2_restrictPrimary_finiteU F hF g G hG input length tau ν β z.1 hx)
  have hc : parameterRound2_globalLocalCorrection F hF g' input length tau realChannel ν β z =
      parameterRound2_globalLocalCorrection F hF g input length tau realChannel ν β z :=
    parameterRound2_actual_reconstruction_germ (F z.1) (hF z.1) (g.inverse ν β z.1) _ _ z.2 hu
  change incrementsGlobalPrimaryLocalZ F hF g' input length tau realChannel ν β z = _
  rw [parameterRound2_globalLocalZ_split F hF g' input length tau realChannel ν β z hz,
    parameterRound2_globalLocalZ_split F hF g input length tau realChannel ν β z hz.1,hc]
  rfl

/-- The SAME actual finite reconstructed extension agrees on G. The proof
uses no new partition and does not multiply a cutoff onto a solver output. -/
theorem parameterRound2_restrictPrimary_extension
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (G : Set (Ep × M)) (hG : IsOpen G)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) :
    EqOn (incrementsGlobalPrimaryExtension F hF (parameterRound2_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν β)
      (incrementsGlobalPrimaryExtension F hF g input length tau realChannel ν β) G := by
  intro z hz
  let g' := parameterRound2_restrictPrimaryFamily F g G hG
  change incrementsGlobalPrimaryExtension F hF g' input length tau realChannel ν β z = _
  by_cases hs : z ∈ (g.chart ν β).source
  · have hs' : z ∈ (g'.chart ν β).source := ⟨hs,hz⟩
    have ht := (g'.chart ν β).map_source hs'
    simp only [incrementsGlobalPrimaryExtension,if_pos hs',if_pos hs]
    exact parameterRound2_restrictPrimary_localZ F hF g G hG input length tau realChannel ν β _ ht
  · have hs' : z ∉ (g'.chart ν β).source := fun h => hs h.1
    simp only [incrementsGlobalPrimaryExtension,if_neg hs',if_neg hs]


#print axioms parameterRound2_restrictPrimary_localZ
#print axioms parameterRound2_restrictPrimary_extension
end GlobalEmbedding.Continuation
