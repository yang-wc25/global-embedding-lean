import NormalPolar.OriginalWaveSeedOriginalValue
import NormalPolar.OriginalWaveSeedFiniteHessian

/-! The actual original-label Hessian response, including every subordinate
piece, has a single vanishing modulus chosen before the contraction and
probe scale. Its leading tensor is the unchanged original legal wave. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation GlobalEmbedding.Offline
variable {m N r : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
private local instance originalHessianSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance originalHessianNorm : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance originalHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) :=
  ContinuousLinearMap.toNormedSpace
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedRescaledFamily

theorem exists_original_hessian_response
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j)) (length : ℕ) :
    ∃ modulus : ℝ → ℝ, (∀ t, 0 ≤ modulus t) ∧
      Tendsto modulus (𝓝[>] 0) (𝓝 0) ∧
    ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
    ∀ j x, x ∈ atlas.support j → ∀ (u : ProbeParameters r) (k : Fin r) (sine : Bool),
      ‖fderiv ℝ (fun v => fderiv ℝ (fderiv ℝ
          (family.originalPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length v ∘ (atlas.chart j).symm))
          (atlas.chart j x)) u (Pi.single (k,sine) 1) -
        (t^((44:ℝ)/5)*probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) •
          phaseRankOneHessian ((waves k).phase ∘ (atlas.chart j).symm)
            ((waves k).value ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
      t^((44:ℝ)/5) * modulus t := by
  have hex (l : Fin r) (s : Fin (family.refinement l).count) :=
    family.exists_piece_original_responses hImm hweight atlas hAtlas hcompact l s length
  choose B1 B2 hB1 hB2 hresponse using hex
  let pieceModulus := fun l (s : Fin (family.refinement l).count) =>
    originalProbeChartModulus |family.pieceHessianCost l length| |family.pieceFirstCost l length|
      (B1 l s) (B2 l s)
  let modulus := fun t : ℝ => ∑ l, ∑ s, pieceModulus l s t
  have hnonneg (l : Fin r) (s : Fin (family.refinement l).count) (t : ℝ) :
      0 ≤ pieceModulus l s t :=
    originalProbeChartModulus_nonneg _ _ _ _ _ (abs_nonneg _) (abs_nonneg _) (hB2 l s).le
  refine ⟨modulus,fun t => Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun s _ => hnonneg l s t)),?_,?_⟩
  · have h := tendsto_finsetSum Finset.univ (fun l _ =>
      tendsto_finsetSum Finset.univ (fun s _ =>
        originalProbeChartModulus_tendsto |family.pieceHessianCost l length|
          |family.pieceFirstCost l length| (B1 l s) (B2 l s)))
    simpa only [Finset.sum_const_zero] using h
  · intro c hc t ht ht1 j x hx u k sine
    let maps := fun l (s : Fin (family.refinement l).count) (v : ProbeParameters 1) (y : D) =>
      family.piecePairMap c hc l s (t^(10:ℕ)) (t^((6:ℝ)/5)) length v ((atlas.chart j).symm y)
    have hjoint (l : Fin r) (s : Fin (family.refinement l).count) :
        ContDiffOn ℝ ∞ (Function.uncurry (maps l s)) (univ ×ˢ (atlas.chart j).target) :=
      family.piecePairMap_chart_joint hImm hweight c hc l s _ _ length atlas hAtlas j
    have htarget := (atlas.chart j).map_source (hAtlas.support_subset j hx)
    have he := originalProbe_native_hessian_finite_response
      (fun l => (family.refinement l).count) maps (atlas.chart j).target
      (atlas.chart j).open_target hjoint u (atlas.chart j x) htarget k sine
    change ‖fderiv ℝ (fun v : ProbeParameters r => fderiv ℝ (fderiv ℝ
      (fun y => ∑ l, ∑ s, maps l s (originalProbePairProjection l v) y)) (atlas.chart j x))
      u (Pi.single (k,sine) 1) - _‖ ≤ _
    rw [he,← (family.refinement k).sum_piece_principal (atlas.chart j).symm (atlas.chart j x),
      Finset.smul_sum,← Finset.sum_sub_distrib]
    have hpiece (s : Fin (family.refinement k).count) :
        ‖fderiv ℝ (fun v : ProbeParameters 1 => fderiv ℝ (fderiv ℝ (maps k s v)) (atlas.chart j x))
            (originalProbePairProjection k u) (Pi.single ((0 : Fin 1),sine) 1) -
          (t^((44:ℝ)/5)*probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) •
            phaseRankOneHessian ((waves k).phase ∘ (atlas.chart j).symm)
              ((family.refinement k).pieceValue s ∘ (atlas.chart j).symm) (atlas.chart j x)‖ ≤
          t^((44:ℝ)/5) * pieceModulus k s t :=
      (hresponse k s c hc t ht ht1).1 j x hx (originalProbePairProjection k u) sine
    have hk : (∑ s, pieceModulus k s t) ≤ modulus t :=
      Finset.single_le_sum (f := fun l : Fin r => ∑ s : Fin (family.refinement l).count, pieceModulus l s t)
        (fun l (_ : l ∈ (Finset.univ : Finset (Fin r))) =>
          Finset.sum_nonneg (fun s _ => hnonneg l s t)) (Finset.mem_univ k)
    calc
      _ ≤ ∑ s, t^((44:ℝ)/5) * pieceModulus k s t :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => hpiece s))
      _ = t^((44:ℝ)/5) * (∑ s, pieceModulus k s t) := (Finset.mul_sum ..).symm
      _ ≤ t^((44:ℝ)/5) * modulus t := mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg ht.le _)

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.exists_original_hessian_response

