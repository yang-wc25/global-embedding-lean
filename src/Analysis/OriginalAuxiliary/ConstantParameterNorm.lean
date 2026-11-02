import OriginalAuxiliary.CanonicalFactoryPhase
import Initialization.Geometry.PaperNormBridge

/-!
# Original full parameter norms of a constant-parameter map

This is the actual full mixed-partial/MAX norm on the original product
coordinates, not a restriction of the requested norm to source derivatives.
The map is independent of the parameter; the source projection is the exact
continuous linear projection of the original joint coordinate vector.
Only fixed dimension/order operator norms occur, never chart counts.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.OriginalAuxiliary

/-- The literal source part of the original joint coordinate vector. -/
def originalJointSourceProjection (n d : ℕ) :
    (Fin (n+d) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).comp
    (parameterTensorModelEquiv n d).symm.toContinuousLinearMap

def originalJointParameterProjection (n d : ℕ) :
    (Fin (n+d) → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).comp
    (parameterTensorModelEquiv n d).symm.toContinuousLinearMap

def constantParameterNormFactor (n d N j : ℕ) : ℝ :=
  max 1 ‖(EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap‖ *
    (max 1 ‖originalJointSourceProjection n d‖)^j

theorem constantParameterNormFactor_pos (n d N j : ℕ) :
    0 < constantParameterNormFactor n d N j := by
  unfold constantParameterNormFactor
  positivity

private theorem norm_iteratedFDeriv_linear_pullback
    {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Y →L[ℝ] X) (u : X → V) (O : Set X) (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ u O) (y : Y) (hy : L y ∈ O) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (u ∘ L) y‖ ≤
      ‖iteratedFDeriv ℝ k u (L y)‖ * ‖L‖^k := by
  have hpre : IsOpen (L ⁻¹' O) := hO.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hu hO.uniqueDiffOn hpre.uniqueDiffOn hy
    (by simp : (k : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_of_isOpen k hpre hy,
    iteratedFDerivWithin_of_isOpen k hO hy] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ k u (L y)).norm_compContinuousLinearMap_le (fun _ : Fin k => L)

variable {n d N pc : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)

theorem constant_parameter_original_map_norm
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin pc → Set Ep) (Kset : Set P)
    (H : M → V) (hH : ContMDiff 𝓘(ℝ,Es) 𝓘(ℝ,V) ∞ H)
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hjets : ∀ i k, k ≤ j → ∀ y ∈ (A.chart i).target,
      ‖iteratedFDeriv ℝ k (H ∘ (A.chart i).symm) y‖ ≤ R) :
    paperAtlasCj j (incrementsOriginalMapCoordinates A chart (fun px => H px.2))
      (incrementsOriginalDifferentiation A chart)
      (incrementsOriginalEvaluation A chart Omega Q Kset) ≤
      ENNReal.ofReal (constantParameterNormFactor n d N j * R) := by
  let L := (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
  let pr := originalJointSourceProjection n d
  let pp := originalJointParameterProjection n d
  apply iSup_le
  intro i
  let u := H ∘ (A.chart i.1).symm
  let f := incrementsOriginalMapCoordinates A chart (fun px => H px.2) i
  let O := incrementsOriginalDifferentiation A chart i
  let S := incrementsOriginalEvaluation A chart Omega Q Kset i
  have hO : IsOpen O := by
    change IsOpen ((pr ⁻¹' (A.chart i.1).target) ∩ (pp ⁻¹' (chart i.2).target))
    exact ((A.chart i.1).open_target.preimage pr.continuous).inter
      ((chart i.2).open_target.preimage pp.continuous)
  have hSO : S ⊆ O := fun _ hy => hy.1
  have hu : ContDiffOn ℝ ∞ u (A.chart i.1).target :=
    (hH.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i.1))).contDiffOn
  have hfun : f = L ∘ (u ∘ pr) := rfl
  have hcomp : ContDiffOn ℝ ∞ (u ∘ pr) O :=
    hu.comp pr.contDiff.contDiffOn (fun _ hy => hy.1)
  have hf : ContDiffOn ℝ ∞ f O := by
    rw [hfun]
    exact L.contDiff.comp_contDiffOn hcomp
  rw [paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf]
  refine iSup_le fun k => iSup_le fun y => iSup_le fun sigma => iSup_le fun c => ?_
  apply ENNReal.ofReal_le_ofReal
  have hy : pr y ∈ (A.chart i.1).target := y.property.1.1
  have hk : k.val ≤ j := by omega
  have hpost := L.norm_iteratedFDeriv_comp_left
    (hcomp.contDiffAt (hO.mem_nhds (hSO y.property))) (by simp : (k.val : ℕ∞ω) ≤ ∞)
  have hpre := norm_iteratedFDeriv_linear_pullback pr u (A.chart i.1).target
    (A.chart i.1).open_target hu y hy k.val
  have hpow : ‖pr‖^k.val ≤ (max 1 ‖pr‖)^j :=
    (pow_le_pow_left₀ (norm_nonneg pr) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k.val f y‖ := coordinate_jet_coefficient_le f y sigma c
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k.val (u ∘ pr) y‖ := by simpa only [hfun] using hpost
    _ ≤ ‖L‖ * (‖iteratedFDeriv ℝ k.val u (pr y)‖ * ‖pr‖^k.val) :=
      mul_le_mul_of_nonneg_left hpre (norm_nonneg L)
    _ ≤ max 1 ‖L‖ * (R * (max 1 ‖pr‖)^j) :=
      mul_le_mul (le_max_right _ _)
        (mul_le_mul (hjets i.1 k.val hk (pr y) hy) hpow
          (pow_nonneg (norm_nonneg pr) _) hR)
        (by positivity) (by positivity)
    _ = constantParameterNormFactor n d N j * R := by
      unfold constantParameterNormFactor
      dsimp only [L,pr]
      ring

end GlobalEmbedding.Continuation.OriginalAuxiliary
#print axioms GlobalEmbedding.Continuation.OriginalAuxiliary.constant_parameter_original_map_norm
