import OriginalAuxiliary.ConstantParameterNorm

/-!
# Full original mixed norms of a constant-parameter operator field

The source projection is the literal projection from the original n+d
coordinate vector. A fixed linear coefficient map permits the actual
operator-valued metric defect to enter the original all-component tensor
norm, including every mixed derivative. No chart-count factor occurs.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Initialization GlobalEmbedding.Offline
  Manifold IsManifold Bundle Set Function
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.RepairClosure
open OriginalAuxiliary

def originalJointLinearNormFactor {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {q : ℕ} (n d : ℕ) (L : X →L[ℝ] (Fin q → ℝ)) (j : ℕ) : ℝ :=
  max 1 ‖L‖ * (max 1 ‖originalJointSourceProjection n d‖)^j

theorem originalJointLinearNormFactor_pos
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {q : ℕ} (n d : ℕ) (L : X →L[ℝ] (Fin q → ℝ)) (j : ℕ) :
    0 < originalJointLinearNormFactor n d L j := by
  unfold originalJointLinearNormFactor
  positivity

private theorem joint_pullback_iteratedFDeriv_bound
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

variable {n d q pc : ℕ} {M P X : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)

/-- Actual full n+d mixed-partial/MAX bound of a literal linear coordinate
view of a source field, uniform over all finite receiving parameter charts. -/
theorem constant_parameter_original_linear_norm
    (A : BufferedAtlas M Es)
    (chart : Fin pc → OpenPartialHomeomorph P Ep)
    (Omega : Fin A.count → Set Es) (Q : Fin pc → Set Ep) (Kset : Set P)
    (u : Fin A.count → Es → X) (L : X →L[ℝ] (Fin q → ℝ))
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (A.chart i).target)
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hjets : ∀ i k, k ≤ j → ∀ y ∈ (A.chart i).target,
      ‖iteratedFDeriv ℝ k (u i) y‖ ≤ R) :
    paperAtlasCj j
      (fun i : Fin A.count × Fin pc => L ∘ (u i.1 ∘ originalJointSourceProjection n d))
      (incrementsOriginalDifferentiation A chart)
      (incrementsOriginalEvaluation A chart Omega Q Kset) ≤
      ENNReal.ofReal (originalJointLinearNormFactor n d L j * R) := by
  let pr := originalJointSourceProjection n d
  let pp := originalJointParameterProjection n d
  apply iSup_le
  intro i
  let f := L ∘ (u i.1 ∘ pr)
  let O := incrementsOriginalDifferentiation A chart i
  let S := incrementsOriginalEvaluation A chart Omega Q Kset i
  have hO : IsOpen O := by
    change IsOpen ((pr ⁻¹' (A.chart i.1).target) ∩ (pp ⁻¹' (chart i.2).target))
    exact ((A.chart i.1).open_target.preimage pr.continuous).inter
      ((chart i.2).open_target.preimage pp.continuous)
  have hSO : S ⊆ O := fun _ hy => hy.1
  have hcomp : ContDiffOn ℝ ∞ (u i.1 ∘ pr) O :=
    (hu i.1).comp pr.contDiff.contDiffOn (fun _ hy => hy.1)
  have hf : ContDiffOn ℝ ∞ f O := L.contDiff.comp_contDiffOn hcomp
  rw [paperCoordinateCj_eq_coordinateJetGauge j f O S hO hSO hf]
  refine iSup_le fun k => iSup_le fun y => iSup_le fun sigma => iSup_le fun c => ?_
  apply ENNReal.ofReal_le_ofReal
  have hy : pr y ∈ (A.chart i.1).target := y.property.1.1
  have hk : k.val ≤ j := by omega
  have hpost := L.norm_iteratedFDeriv_comp_left
    (hcomp.contDiffAt (hO.mem_nhds (hSO y.property))) (by simp : (k.val : ℕ∞ω) ≤ ∞)
  have hpre := joint_pullback_iteratedFDeriv_bound pr (u i.1) (A.chart i.1).target
    (A.chart i.1).open_target (hu i.1) y hy k.val
  have hpow : ‖pr‖^k.val ≤ (max 1 ‖pr‖)^j :=
    (pow_le_pow_left₀ (norm_nonneg pr) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  calc
    _ ≤ ‖iteratedFDeriv ℝ k.val f y‖ := coordinate_jet_coefficient_le f y sigma c
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k.val (u i.1 ∘ pr) y‖ := hpost
    _ ≤ ‖L‖ * (‖iteratedFDeriv ℝ k.val (u i.1) (pr y)‖ * ‖pr‖^k.val) :=
      mul_le_mul_of_nonneg_left hpre (norm_nonneg L)
    _ ≤ max 1 ‖L‖ * (R * (max 1 ‖pr‖)^j) :=
      mul_le_mul (le_max_right _ _)
        (mul_le_mul (hjets i.1 k.val hk (pr y) hy) hpow
          (pow_nonneg (norm_nonneg pr) _) hR)
        (by positivity) (by positivity)
    _ = originalJointLinearNormFactor n d L j * R := by
      unfold originalJointLinearNormFactor
      dsimp only [pr]
      ring

end GlobalEmbedding.Continuation.RepairClosure

#print axioms GlobalEmbedding.Continuation.RepairClosure.constant_parameter_original_linear_norm
