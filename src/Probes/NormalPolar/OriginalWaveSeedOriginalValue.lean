import NormalPolar.OriginalWaveSeedPieceRegularity
import NormalPolar.OriginalWaveSeedPieceResponses
import NormalPolar.OriginalWaveSeedFiniteResponse

/-! Recover the whole original legal-wave value response by summing actual
subordinate source solutions on the original paired parameter space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
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
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {waves : Fin r → LocalLegalWave (n := m+1) F hF} {weight : Fin r → ℝ}

namespace OriginalWaveSeedRescaledFamily

def originalPairMap (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (delta tau : ℝ) (length : ℕ)
    (u : ProbeParameters r) (x : M) : V :=
  ∑ l, ∑ s, family.piecePairMap c hc l s delta tau length (originalProbePairProjection l u) x

theorem exists_original_value_response
    (family : OriginalWaveSeedRescaledFamily F hF waves weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (hweight : ∀ l, 0 < weight l)
    (atlas : BufferedAtlas M D) (hAtlas : IsSmoothBufferedAtlas atlas)
    (hcompact : ∀ j, IsCompact (atlas.support j)) (length : ℕ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c : ℝ) (hc : c ∈ Icc (1/2:ℝ) 1) (t : ℝ), 0 < t → t ≤ 1 →
    ∀ (x : M) (u : ProbeParameters r) (k : Fin r) (sine : Bool),
      ‖fderiv ℝ (fun v => family.originalPairMap c hc (t^(10:ℕ)) (t^((6:ℝ)/5)) length v x)
          u (Pi.single (k,sine) 1) -
        (-(t^((56:ℝ)/5))*(weight k^2)⁻¹ *
          probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) • (waves k).value x‖ ≤
      t^((56:ℝ)/5) * (C * |t|^((1:ℝ)/10)) := by
  let costs := fun l : Fin r => ∑ _s : Fin (family.refinement l).count,
    |family.pieceValueCost l length|
  let C := 1 + ∑ l, costs l
  have hcost (l : Fin r) : 0 ≤ costs l := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hC : 0 < C := by
    have h : 0 ≤ ∑ l, costs l := Finset.sum_nonneg (fun l _ => hcost l)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro c hc t ht ht1 x u k sine
  let maps := fun l (s : Fin (family.refinement l).count) (v : ProbeParameters 1) =>
    family.piecePairMap c hc l s (t^(10:ℕ)) (t^((6:ℝ)/5)) length v x
  have hdiff (l : Fin r) (s : Fin (family.refinement l).count) :
      DifferentiableAt ℝ (maps l s) (originalProbePairProjection l u) :=
    family.piecePairMap_value_differentiable hImm hweight atlas hAtlas c hc l s _ _ length x _
  have he := originalProbePair_finite_response
    (fun l => (family.refinement l).count) maps u hdiff k sine
  change ‖fderiv ℝ (fun v : ProbeParameters r =>
      ∑ l, ∑ s, maps l s (originalProbePairProjection l v)) u (Pi.single (k,sine) 1) - _‖ ≤ _
  rw [he,← (family.refinement k).sum_pieceValue x,Finset.smul_sum,← Finset.sum_sub_distrib]
  have hpiece (s : Fin (family.refinement k).count) :
      ‖fderiv ℝ (maps k s) (originalProbePairProjection k u)
          (Pi.single ((0 : Fin 1),sine) 1) -
        (-(t^((56:ℝ)/5))*(weight k^2)⁻¹ *
          probeTrig sine (weight k*(waves k).phase x/t^((6:ℝ)/5))) •
            (family.refinement k).pieceValue s x‖ ≤
      t^((56:ℝ)/5) * (|family.pieceValueCost k length| * |t|^((1:ℝ)/10)) := by
    obtain ⟨B1,B2,hB1,hB2,h⟩ :=
      family.exists_piece_original_responses hImm hweight atlas hAtlas hcompact k s length
    exact (h c hc t ht ht1).2 x (originalProbePairProjection k u) sine
  have hk : costs k ≤ C := by
    have hh := Finset.single_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin r))) => hcost l)
      (Finset.mem_univ k)
    dsimp [C]
    linarith
  calc
    _ ≤ ∑ _s : Fin (family.refinement k).count,
        t^((56:ℝ)/5) * (|family.pieceValueCost k length| * |t|^((1:ℝ)/10)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => hpiece s))
    _ = t^((56:ℝ)/5) * (costs k * |t|^((1:ℝ)/10)) := by
      simp only [costs,Finset.mul_sum,Finset.sum_mul]
    _ ≤ t^((56:ℝ)/5) * (C * |t|^((1:ℝ)/10)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg (abs_nonneg t) _))
        (Real.rpow_nonneg ht.le _)

end OriginalWaveSeedRescaledFamily
end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.originalPairMap
#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedRescaledFamily.exists_original_value_response

