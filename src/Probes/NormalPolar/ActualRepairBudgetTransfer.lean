import NormalPolar.NativeProbeValueTail
import NormalPolar.FullResponseTail
import NormalPolar.ActualFamilyTotalization
import GlobalEmbedding.Offline.RepairDisplacementBudget

/-!
# Original probe budgets of the same model plus its actual correction

All additions below take place in the original atlas norm.  The parameter
field is the native derivative of the actual map; its decomposition follows
from joint smoothness.  No final-map budget is an input to the transfer.
The scale conversion retains the entire supplied interval, including when
its threshold exceeds one.
-/

noncomputable section
open Set Filter Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ, E)

/-- Chart regularity suffices for exact addition in the original norm. -/
theorem probeAtlasCj_add_le_of_chart_smooth
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (j : ℕ)
    (f g : M → V)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i).target)
    (hg : ∀ i, ContDiffOn ℝ ∞ (g ∘ (A.chart i).symm) (A.chart i).target)
    {Bf Bg : ℝ} (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hfb : probeAtlasCj A j f ≤ ENNReal.ofReal Bf)
    (hgb : probeAtlasCj A j g ≤ ENNReal.ofReal Bg) :
    probeAtlasCj A j (f + g) ≤ ENNReal.ofReal (Bf + Bg) := by
  let ex := EuclideanSpace.equiv (Fin n) ℝ
  let ey := EuclideanSpace.equiv (Fin N) ℝ
  apply iSup_le
  intro i
  let O := ex '' (A.chart i).target
  let S := ex '' ((A.chart i) '' A.support i)
  let fcoord := fun x ↦ ey (f ((A.chart i).symm (ex.symm x)))
  let gcoord := fun x ↦ ey (g ((A.chart i).symm (ex.symm x)))
  have hO : IsOpen O := ex.toHomeomorph.isOpenMap _ (A.chart i).open_target
  have hSO : S ⊆ O := by
    rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨A.chart i y, (A.chart i).map_source (hA.support_subset i hy), rfl⟩
  have hfc : ContDiffOn ℝ ∞ fcoord O := by
    apply ey.contDiff.comp_contDiffOn
    apply (hf i).comp ex.symm.contDiff.contDiffOn
    rintro _ ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  have hgc : ContDiffOn ℝ ∞ gcoord O := by
    apply ey.contDiff.comp_contDiffOn
    apply (hg i).comp ex.symm.contDiff.contDiffOn
    rintro _ ⟨x, hx, rfl⟩
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  have hlocalf : paperCoordinateCj j fcoord O S ≤ ENNReal.ofReal Bf :=
    (le_iSup (fun k ↦ paperCoordinateCj j
      (fun x ↦ ey (f ((A.chart k).symm (ex.symm x))))
      (ex '' (A.chart k).target) (ex '' ((A.chart k) '' A.support k))) i).trans hfb
  have hlocalg : paperCoordinateCj j gcoord O S ≤ ENNReal.ofReal Bg :=
    (le_iSup (fun k ↦ paperCoordinateCj j
      (fun x ↦ ey (g ((A.chart k).symm (ex.symm x))))
      (ex '' (A.chart k).target) (ex '' ((A.chart k) '' A.support k))) i).trans hgb
  simpa only [fcoord, gcoord, O, S, ex, ey, Pi.add_apply, map_add] using
    paperCoordinateCj_add_le j hO hSO fcoord gcoord hfc hgc hBf hBg hlocalf hlocalg

/-- A smooth model and the literal correction give the actual final norm. -/
theorem actual_repair_spatial_budget_of_model_tail
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (j : ℕ)
    (F G : M → V)
    (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (hG : ContMDiff IM 𝓘(ℝ, V) ∞ G)
    {Bmodel Btail : ℝ} (hm : 0 ≤ Bmodel) (ht : 0 ≤ Btail)
    (hmodel : probeAtlasCj A j G ≤ ENNReal.ofReal Bmodel)
    (htail : probeAtlasCj A j (F - G) ≤ ENNReal.ofReal Btail) :
    probeAtlasCj A j F ≤ ENNReal.ofReal (Bmodel + Btail) := by
  have heq : G + (F - G) = F := by abel
  rw [← heq]
  apply probeAtlasCj_add_le_of_chart_smooth A hA j G (F - G)
    (fun i ↦ ((hG.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas
      (hA.chart_mem i))).contDiffOn))
    (fun i ↦ (((hF.sub hG).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas
      (hA.chart_mem i))).contDiffOn)) hm ht hmodel htail

/-- Native parameter differentiation of the actual correction supplies the
full final parameter field, with no independently chosen response field. -/
theorem actual_repair_parameter_budget_of_model_tail
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcover : ∀ x, ∃ i, x ∈ A.support i) (j : ℕ)
    {U : Set P} (hU : IsOpen U) (F G : P → M → V)
    (hF : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry F) (U ×ˢ univ))
    (hG : ContMDiffOn ((𝓘(ℝ, P)).prod IM) 𝓘(ℝ, V) ∞
      (Function.uncurry G) (U ×ˢ univ))
    (u direction : P) (hu : u ∈ U)
    {Bmodel Btail : ℝ} (hm : 0 ≤ Bmodel) (ht : 0 ≤ Btail)
    (hmodel : probeAtlasCj A j
      (fun x ↦ fderiv ℝ (fun v ↦ G v x) u direction) ≤ ENNReal.ofReal Bmodel)
    (htail : probeAtlasCj A j
      (fun x ↦ fderiv ℝ (fun v ↦ F v x - G v x) u direction) ≤ ENNReal.ofReal Btail) :
    probeAtlasCj A j (fun x ↦ fderiv ℝ (fun v ↦ F v x) u direction) ≤
      ENNReal.ofReal (Bmodel + Btail) := by
  let model := fun x ↦ fderiv ℝ (fun v ↦ G v x) u direction
  let tail := fun x ↦ fderiv ℝ (fun v ↦ F v x - G v x) u direction
  have heq : model + tail = fun x ↦ fderiv ℝ (fun v ↦ F v x) u direction := by
    funext x
    simp only [Pi.add_apply, model, tail,
      actual_parameter_value_response_sub A hA hcover hU F G hF hG u direction hu x]
    abel
  rw [← heq]
  exact probeAtlasCj_add_le_of_chart_smooth A hA j model tail
    (fun i ↦ atlas_actual_parameter_response_contDiffOn A hA i hU G hG u direction hu)
    (fun i ↦ atlas_actual_parameter_response_contDiffOn A hA i hU
      (fun v x ↦ F v x - G v x) (hF.sub hG) u direction hu)
    hm ht hmodel htail

/-- A fixed threshold absorbs a higher positive power, without a new
small-scale assumption and without changing the original interval. -/
theorem probe_rpow_le_threshold_envelope
    (threshold t a b c : ℝ) (ht : 0 < t) (htt : t < threshold)
    (hgap : 0 ≤ a - b) (hgapc : a - b ≤ c) :
    t ^ a ≤ (max 1 threshold) ^ c * t ^ b := by
  have hR : (1 : ℝ) ≤ max 1 threshold := le_max_left _ _
  have htR : t ≤ max 1 threshold := htt.le.trans (le_max_right _ _)
  have hpow : t ^ (a - b) ≤ (max 1 threshold) ^ c :=
    (Real.rpow_le_rpow ht.le htR hgap).trans
      (Real.rpow_le_rpow_of_exponent_le hR hgapc)
  calc
    t ^ a = t ^ (a - b) * t ^ b := by rw [← Real.rpow_add ht]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ht.le _)

/-- One fixed common constant covers the three spatial and mixed repair
scales used in the original probe interface. -/
def actualRepairUniformBudget (Cmodel Ctail threshold : ℝ) (d : ℕ) : ℝ :=
  Cmodel + 2 * Ctail * ((d : ℝ) + 1) * (max 1 threshold) ^ ((228 : ℝ) / 25)

theorem actualRepairUniformBudget_nonneg
    {Cmodel Ctail threshold : ℝ} (hm : 0 ≤ Cmodel) (ht : 0 ≤ Ctail) (d : ℕ) :
    0 ≤ actualRepairUniformBudget Cmodel Ctail threshold d := by
  unfold actualRepairUniformBudget
  positivity

/-- All actual correction rates can be absorbed into the same common
constant. The multiplier k allows both scalar spatial tails and the true
d-dimensional Pi-direction loss. -/
theorem actualRepairUniformBudget_absorbs
    (Cmodel Ctail threshold : ℝ) (d : ℕ) (t a b k : ℝ)
    (hCtail : 0 ≤ Ctail) (ht : 0 < t) (htt : t < threshold)
    (hk : 0 ≤ k) (hkd : k ≤ (d : ℝ) + 1)
    (hgap : 0 ≤ a - b) (hgapc : a - b ≤ (228 : ℝ) / 25) :
    Cmodel * t ^ b + k * (2 * Ctail * t ^ a) ≤
      actualRepairUniformBudget Cmodel Ctail threshold d * t ^ b := by
  have hscale := probe_rpow_le_threshold_envelope threshold t a b ((228 : ℝ) / 25)
    ht htt hgap hgapc
  have hr : 0 ≤ (max 1 threshold) ^ ((228 : ℝ) / 25) := by positivity
  calc
    _ ≤ Cmodel * t ^ b + k * (2 * Ctail *
        ((max 1 threshold) ^ ((228 : ℝ) / 25) * t ^ b)) := by
      gcongr
    _ ≤ Cmodel * t ^ b + ((d : ℝ) + 1) * (2 * Ctail *
        ((max 1 threshold) ^ ((228 : ℝ) / 25) * t ^ b)) := by
      gcongr
    _ = _ := by unfold actualRepairUniformBudget; ring

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actual_repair_parameter_budget_of_model_tail
#print axioms GlobalEmbedding.NormalPolar.actualRepairUniformBudget_absorbs
