import Probes.ActualIncrementPrimaryOriginalWave
import Probes.ActualIncrementPrimaryObservationSum
import Probes.ActualSecondaryRefinedObservationSum
import Probes.ActualJointChartTransfer

/-! Observation transport for each SAME original global primary piece. Its
local formula and actual observer transition are retained literally; mixed
parameter/source derivatives use the fast scale without an extra ell loss. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

variable (F : Ep → M → EuclideanSpace ℝ (Fin N))
  (hF : ∀ b, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F b))
  (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
  (input : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))

theorem actual_original_primary_wave_eq_piece_sum (length : ℕ) (tau : ℝ) :
    incrementsGlobalPrimaryWave F hF g input length tau = fun y => ∑ ν, ∑ β,
      (Real.cos (g.phase ν y/tau) • incrementsGlobalPrimaryExtension F hF g input length tau true ν β y -
        Real.sin (g.phase ν y/tau) • incrementsGlobalPrimaryExtension F hF g input length tau false ν β y) := by
  funext y
  simp only [incrementsGlobalPrimaryWave,incrementsGlobalPrimaryAmplitude,
    Finset.smul_sum,Finset.sum_sub_distrib]

theorem actual_original_primary_piece_observation_jets
    (ν : Λ) (β : Β) (length j : ℕ) (tau ell Budget : ℝ)
    (kappa : Y → Ep × M) (O : Set Y) (hO : IsOpen O)
    (hsource : MapsTo kappa O (g.chart ν β).source)
    (hadapt : ∀ y ∈ O, g.phase ν (kappa y) = (g.chart ν β (kappa y)).2 0)
    (htransition : ContDiffOn ℝ ∞ (g.chart ν β ∘ kappa) O)
    (hlocal : ContDiffOn ℝ ∞ (actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)) (g.chart ν β).target)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (htau : 0 < tau) (htaul : tau ≤ ell)
    (y : Y) (hy : y ∈ O)
    (hjets : ∀ k ≤ j, tau^k * ‖iteratedFDeriv ℝ k
      (actualSecondaryModulation (fun z : X => z.2 0) tau
        (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
        (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β))
      (g.chart ν β (kappa y))‖ ≤ Budget)
    (htransitionb : ∀ k, 1 ≤ k → k ≤ j →
      ell^(k-1) * ‖iteratedFDeriv ℝ k (g.chart ν β ∘ kappa) y‖ ≤ T k) :
    let piece := fun w : Ep × M =>
      Real.cos (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau true ν β w -
        Real.sin (g.phase ν w/tau) • incrementsGlobalPrimaryExtension F hF g input length tau false ν β w
    ContDiffOn ℝ ∞ (piece ∘ kappa) O ∧
      tau^j * ‖iteratedFDeriv ℝ j (piece ∘ kappa) y‖ ≤ actualFastChartTransferCost T j*Budget := by
  intro piece
  let localWave := actualSecondaryModulation (fun z : X => z.2 0) tau
    (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
    (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
  have he : EqOn (piece ∘ kappa) (localWave ∘ (g.chart ν β ∘ kappa)) O := by
    intro w hw
    change Real.cos (g.phase ν (kappa w)/tau) • _ - Real.sin (g.phase ν (kappa w)/tau) • _ = _
    simp only [incrementsGlobalPrimaryExtension,if_pos (hsource hw),hadapt w hw,
      localWave,actualSecondaryModulation,Function.comp_def]
  have hmap : MapsTo (g.chart ν β ∘ kappa) O (g.chart ν β).target :=
    fun w hw => (g.chart ν β).map_source (hsource hw)
  refine ⟨(hlocal.comp htransition hmap).congr he,?_⟩
  have hnear : piece ∘ kappa =ᶠ[𝓝 y] localWave ∘ (g.chart ν β ∘ kappa) :=
    he.eventuallyEq_of_mem (hO.mem_nhds hy)
  rw [(hnear.iteratedFDeriv ℝ j).eq_of_nhds]
  exact actual_fast_joint_chart_transfer T hT j (g.chart ν β ∘ kappa) localWave O
    (g.chart ν β).target hO (g.chart ν β).open_target htransition hlocal hmap y hy
    tau ell Budget htau htaul hjets htransitionb

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_primary_wave_eq_piece_sum
#print axioms GlobalEmbedding.Continuation.actual_original_primary_piece_observation_jets
