import Smoothing.Round3ParameterPrimaryRestriction

/-! The actual finite reconstruction and supported pullback are unchanged
on a proved open domain.  No output cutoff or new solver is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {E H M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [TopologicalSpace P]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => P × D

theorem round3Parameter_restrictPrimary_localZ
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) (z : X)
    (hz : z ∈ ((round3Parameter_restrictPrimaryFamily F g G hG).chart ν β).target) :
    round3ParameterPrimaryLocalZ F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν β z =
      round3ParameterPrimaryLocalZ F hF g input length tau realChannel ν β z := by
  let g' := round3Parameter_restrictPrimaryFamily F g G hG
  let O := {x : D | (z.1,x) ∈ (g'.chart ν β).target}
  let ch : (Fin (m+1) → ℂ) →L[ℝ] D :=
    if realChannel then incrementsModeRealPart else incrementsModeImagPart
  have hO : IsOpen O := (g'.chart ν β).open_target.preimage (continuous_const.prodMk continuous_id)
  have hu : (fun x => ch (round3ParameterPrimaryFiniteU F hF g' input length tau ν β z.1 x)) =ᶠ[𝓝 z.2]
      (fun x => ch (round3ParameterPrimaryFiniteU F hF g input length tau ν β z.1 x)) := by
    filter_upwards [hO.mem_nhds hz] with x hx
    exact congrArg ch (round3Parameter_restrictPrimary_finiteU F hF g G hG input length tau ν β z.1 hx)
  dsimp only [round3ParameterPrimaryLocalZ]
  apply parameterRound2_actual_fullReconstruction_germ (F z.1) (hF z.1) (g.inverse ν β z.1)
    _ _ _ _ _ z.2 hu
  split_ifs
  · exact round3Parameter_restrictPrimary_localFree F g G hG input tau ν β z hz
  · rfl

theorem round3Parameter_restrictPrimary_extension
    (F : P → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := I) (m := m) (Λ := Λ) (Β := Β) F)
    (G : Set (P × M)) (hG : IsOpen G)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (length : ℕ) (tau : ℝ) (realChannel : Bool) (ν : Λ) (β : Β) :
    EqOn (round3ParameterPrimaryExtension F hF (round3Parameter_restrictPrimaryFamily F g G hG)
      input length tau realChannel ν β)
      (round3ParameterPrimaryExtension F hF g input length tau realChannel ν β) G := by
  intro z hz
  let g' := round3Parameter_restrictPrimaryFamily F g G hG
  change round3ParameterPrimaryExtension F hF g' input length tau realChannel ν β z = _
  by_cases hs : z ∈ (g.chart ν β).source
  · have hs' : z ∈ (g'.chart ν β).source := ⟨hs,hz⟩
    have ht := (g'.chart ν β).map_source hs'
    simp only [round3ParameterPrimaryExtension,if_pos hs',if_pos hs]
    exact round3Parameter_restrictPrimary_localZ F hF g G hG input length tau realChannel ν β _ ht
  · have hs' : z ∉ (g'.chart ν β).source := fun h => hs h.1
    simp only [round3ParameterPrimaryExtension,if_neg hs',if_neg hs]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_restrictPrimary_localZ
#print axioms GlobalEmbedding.Continuation.round3Parameter_restrictPrimary_extension
