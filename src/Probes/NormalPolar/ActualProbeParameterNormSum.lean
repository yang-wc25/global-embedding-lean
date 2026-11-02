import NormalPolar.ActualRepairBudgetTransfer
import NormalPolar.GlobalWaveResponseInitialSum

/-! Exact addition of the background, prescribed and complete secondary
responses in the original probe atlas norm. The same three actual fields
are used at every chart; no chart sum or replacement response is introduced. -/

noncomputable section
open Set Function Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff ENNReal
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

theorem probeAtlasCj_three_add_le_of_chart_smooth
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (j : ℕ)
    (B P S : M → EuclideanSpace ℝ (Fin N))
    (hB : ∀ i, ContDiffOn ℝ ∞ (B ∘ (A.chart i).symm) (A.chart i).target)
    (hP : ∀ i, ContDiffOn ℝ ∞ (P ∘ (A.chart i).symm) (A.chart i).target)
    (hS : ∀ i, ContDiffOn ℝ ∞ (S ∘ (A.chart i).symm) (A.chart i).target)
    {CB CP CS : ℝ} (hCB : 0 ≤ CB) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS)
    (hBB : probeAtlasCj A j B ≤ ENNReal.ofReal CB)
    (hPP : probeAtlasCj A j P ≤ ENNReal.ofReal CP)
    (hSS : probeAtlasCj A j S ≤ ENNReal.ofReal CS) :
    probeAtlasCj A j (fun x => B x + P x + S x) ≤
      ENNReal.ofReal (CB + CP + CS) := by
  have hBP := probeAtlasCj_add_le_of_chart_smooth A hA j B P hB hP hCB hCP hBB hPP
  exact probeAtlasCj_add_le_of_chart_smooth A hA j (B + P) S
    (fun i => (hB i).add (hP i)) hS (add_nonneg hCB hCP) hCS hBP hSS

/-- The native derivative of the same complete first map has the component
budget. Chartwise joint smoothness on the actual parameter domain suffices;
there is no independent response field or global parameter extension. -/
theorem actual_probe_first_parameter_norm_of_components
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (hA : IsSmoothBufferedAtlas A) (hcover : ∀ x, ∃ i, x ∈ A.support i)
    (j : ℕ) (U : Set E) (hU : IsOpen U)
    (reference : M → EuclideanSpace ℝ (Fin N))
    (B P S : E → M → EuclideanSpace ℝ (Fin N))
    (hB : ∀ i, ContDiffOn ℝ ∞
      (fun z : E × EuclideanSpace ℝ (Fin n) => B z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (hP : ∀ i, ContDiffOn ℝ ∞
      (fun z : E × EuclideanSpace ℝ (Fin n) => P z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (hS : ∀ i, ContDiffOn ℝ ∞
      (fun z : E × EuclideanSpace ℝ (Fin n) => S z.1 ((A.chart i).symm z.2))
      (U ×ˢ (A.chart i).target))
    (u direction : E) (hu : u ∈ U)
    {CB CP CS : ℝ} (hCB : 0 ≤ CB) (hCP : 0 ≤ CP) (hCS : 0 ≤ CS)
    (hBB : probeAtlasCj A j (fun x => fderiv ℝ (fun v => B v x) u direction) ≤
      ENNReal.ofReal CB)
    (hPP : probeAtlasCj A j (fun x => fderiv ℝ (fun v => P v x) u direction) ≤
      ENNReal.ofReal CP)
    (hSS : probeAtlasCj A j (fun x => fderiv ℝ (fun v => S v x) u direction) ≤
      ENNReal.ofReal CS) :
    probeAtlasCj A j (fun x => fderiv ℝ
      (fun v => reference x + B v x + P v x + S v x) u direction) ≤
      ENNReal.ofReal (CB + CP + CS) := by
  have hvalue (F : E → M → EuclideanSpace ℝ (Fin N))
      (hF : ∀ i, ContDiffOn ℝ ∞
        (fun z : E × EuclideanSpace ℝ (Fin n) => F z.1 ((A.chart i).symm z.2))
        (U ×ˢ (A.chart i).target)) (x : M) :
      DifferentiableAt ℝ (fun v => F v x) u := by
    obtain ⟨i, hi⟩ := hcover x
    have hx := hA.support_subset i hi
    have hd := (((hF i).contDiffAt
      ((hU.prod (A.chart i).open_target).mem_nhds ⟨hu, (A.chart i).map_source hx⟩)).comp u
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
    change DifferentiableAt ℝ (fun v => F v ((A.chart i).symm (A.chart i x))) u at hd
    simpa only [(A.chart i).left_inv hx] using hd
  have hchart (F : E → M → EuclideanSpace ℝ (Fin N))
      (hF : ∀ i, ContDiffOn ℝ ∞
        (fun z : E × EuclideanSpace ℝ (Fin n) => F z.1 ((A.chart i).symm z.2))
        (U ×ˢ (A.chart i).target)) (i : Fin A.count) :
      ContDiffOn ℝ ∞ ((fun x => fderiv ℝ (fun v => F v x) u direction) ∘
        (A.chart i).symm) (A.chart i).target := by
    have hd := (contDiffOn_actual_parameter_fderiv (hU.prod (A.chart i).open_target)
      (hF i)).clm_apply (contDiffOn_const (c := direction))
    exact hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨hu, hy⟩)
  have he : (fun x => fderiv ℝ
      (fun v => reference x + B v x + P v x + S v x) u direction) =
      (fun x => fderiv ℝ (fun v => B v x) u direction +
        fderiv ℝ (fun v => P v x) u direction + fderiv ℝ (fun v => S v x) u direction) := by
    funext x
    rw [globalWave_native_parameter_sum _ _ _ _ u (hvalue B hB x) (hvalue P hP x)
      (hvalue S hS x)]
    rfl
  rw [he]
  exact probeAtlasCj_three_add_le_of_chart_smooth A hA j _ _ _
    (hchart B hB) (hchart P hP) (hchart S hS) hCB hCP hCS hBB hPP hSS

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.probeAtlasCj_three_add_le_of_chart_smooth
#print axioms GlobalEmbedding.NormalPolar.actual_probe_first_parameter_norm_of_components
