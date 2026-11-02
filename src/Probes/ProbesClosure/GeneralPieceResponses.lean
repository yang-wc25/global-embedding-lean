import ProbesClosure.GeneralPieceBinding

/-! The actual arbitrary-cutoff original wave pieces satisfy the paper's paired
Hessian and value responses. Every raw and physical input is manufactured
from the one preselected rescaled family; the only remaining assumptions
are the original immersion, positive phase weights and observation atlas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.NormalPolar GlobalEmbedding.Offline

variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
private local instance pieceResponseHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance pieceResponseHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance pieceResponseHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → OpenSupportedLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace GeneralLegalWaveRawFamily

def pieceHessianCost (family : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (length : ℕ) : ℝ :=
  round4PrescribedHessianErrorConstant m N length
    (fun _ : Fin 1 => weight l) (fun _ => 1)
    (fun _ => family.cutoffBudget (2+length+1)) (fun _ => family.normalBudget (2+length+1))
    (family.geometryBudget (max (2+length+1) 2)) (family.geometryBudget (max (2+length+1) 2)) 0

def pieceFirstCost (family : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (length : ℕ) : ℝ :=
  actualPrescribedProbeJetConstant m N (Fintype.card (Fin 1 × Bool)) 1 length
    (fun _ : Fin 1 => weight l) (fun _ => 1)
    (fun _ => family.cutoffBudget (2+length+1)) (fun _ => family.normalBudget (2+length+1))
    (family.geometryBudget (max (2+length+1) 2)) (family.geometryBudget (max (2+length+1) 2))

def pieceValueCost (family : GeneralLegalWaveRawFamily F hF waves weight)
    (l : Fin r) (length : ℕ) : ℝ :=
  actualRealHomogeneousConstant m N 2 length (family.geometryBudget (max (2+length+1) 2))
    (homogeneousSourceConstant m N (2+length+1) (family.geometryBudget (max (2+length+1) 2))
      (probeNormalAmplitudeConstant (2+length+1) (weight l)
        (family.cutoffBudget (2+length+1)) (family.normalBudget (2+length+1)))) 1

theorem exists_piece_original_responses
    (family : GeneralLegalWaveRawFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j))
    (l : Fin r) (s : Fin (family.piece l).seed.refinement.count) (length : ℕ) :
    ∃ B1 B2 : ℝ, 0 < B1 ∧ 0 < B2 ∧
    ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
    let P := family.piecePairMap c hc l s (t^(10:ℕ)) (t^((6:ℝ)/5)) length
    (∀ j x, x ∈ atlas.support j → ∀ (u : ProbeParameters 1) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ (P v ∘ (atlas.chart j).symm)) (atlas.chart j x))
        u (Pi.single ((0 : Fin 1),sine) 1) -
      (t^((44:ℝ)/5)*probeTrig sine (weight l*(waves l).phase x/t^((6:ℝ)/5))) •
        phaseRankOneHessian ((waves l).phase ∘ (atlas.chart j).symm)
          ((family.piece l).seed.pieceValue s ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
      t^((44:ℝ)/5)*originalProbeChartModulus
        |family.pieceHessianCost l length| |family.pieceFirstCost l length| B1 B2 t) ∧
    (∀ x (u : ProbeParameters 1) (sine : Bool),
      ‖fderiv ℝ (fun v => P v x) u (Pi.single ((0 : Fin 1),sine) 1) -
        (-(t^((56:ℝ)/5))*(weight l^2)⁻¹ * probeTrig sine (weight l*(waves l).phase x/t^((6:ℝ)/5))) •
          (family.piece l).seed.pieceValue s x‖ ≤
      t^((56:ℝ)/5)*(|family.pieceValueCost l length| * |t|^((1:ℝ)/10))) := by
  let Mg := family.geometryBudget (max (2+length+1) 2)
  let Bchi := family.cutoffBudget (2+length+1)
  let Bnu := family.normalBudget (2+length+1)
  have hg : 0 ≤ Mg := (family.positive _).1.le
  have hchi : 0 ≤ Bchi := (family.positive _).2.1.le
  have hnu : 0 ≤ Bnu := (family.positive _).2.2.le
  obtain ⟨B1,B2,hB1,hB2,hresponse⟩ := globalWave_supported_responses_from_raw
    (p := Fintype.card (Fin 1 × Bool)) (Ep := Z)
    (fun _ : Fin 1 => (waves l).phase)
    (fun _ : Fin 1 => (family.piece l).seed.pieceValue s)
    (fun _ : Fin 1 => (family.piece l).seed.pieceCarrier s)
    (fun _ => (family.piece l).seed.pieceCarrier_closed s)
    (fun _ x hx => (family.piece l).seed.pieceValue_zero s x hx)
    atlas hAtlas hcompact
    (fun _ : Fin 1 => ((family.piece l).seed.inner s).chart)
    (fun _ => contMDiffOn_of_mem_maximalAtlas ((family.piece l).seed.inner s).maximal)
    (fun _ => (family.piece l).seed.pieceCarrier_source s)
    (fun _ : Fin 1 => weight l) (fun _ => hweight l) Mg Bchi Bnu hg hchi hnu
  refine ⟨B1,B2,hB1,hB2,?_⟩
  intro c hc t ht ht1
  have hscale := probe_original_scale_conditions t ht ht1
  have hout := hresponse (round4PairedParameterIndex 1).toEmbedding
    (fun _ : Z => c • F) (fun _ => contMDiff_const_rescale F hF c)
    (fun _ : Fin 1 => fun _ : Z => ((family.piece l).seed.outer s).chart.symm)
    (fun _ : Fin 1 => (family.piece l).seed.cutoffCoordinates s)
    (fun _ : Fin 1 => fun _ y => actualRescaledNormal F hF c (GeneralLegalWaveSeed.contraction_ne_zero c hc)
      (((family.piece l).seed.outer s).chart.symm y) ((waves l).normal (((family.piece l).seed.outer s).chart.symm y)))
    (fun _ : Fin 1 => fun z : Z × M => weight l*(waves l).phase z.2)
    (fun _ : Fin 1 => (family.piece l).seed.physicalChart s)
    univ (fun _ : Fin 1 => (family.piece l).seed.carrier s) isOpen_univ
    t ht ht1 length
    (fun _ : Fin 1 => family.raw c hc l s (2+length+1) 2 (t^((11:ℝ)/10)) hscale.1.le hscale.2.1)
    (default : Z)
    (family.pieceBinding hImm hweight c hc l s length (t^((11:ℝ)/10)) hscale.1.le hscale.2.1)
    (0 : Fin 1)
  exact hout

end GeneralLegalWaveRawFamily
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveRawFamily.exists_piece_original_responses

