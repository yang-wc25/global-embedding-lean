import Smoothing.Round3RepairClosedSeries

/-! The fixed convolution sampling domains contain actual open buffers.
On the whole physical parameter manifold they cover every point, using the
actual parameter plateau and the original source atlas.  No compact sampling
domain is identified with an entire chart target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairMetricCoordsChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairMetricCoordsIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- Exact source derivative in the unchanged original full coordinates.
The inserted parameter tangent is zero. -/
theorem round3_repair_source_derivative_original_coordinates
    {c : ℕ} (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (i : Fin A.count × Fin c) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i) (v : Es) :
    fderiv ℝ (fun x => F ((B i.2).symm (incrementsOriginalParameterPoint y),(A.chart i.1).symm x))
      (incrementsOriginalSourcePoint y) v =
    (EuclideanSpace.equiv (Fin N) ℝ).symm
      (fderiv ℝ (incrementsOriginalMapCoordinates A B F i) y (parameterTensorModelEquiv n d (0,v))) := by
  let e := parameterTensorModelEquiv n d
  let cY := EuclideanSpace.equiv (Fin N) ℝ
  let p := incrementsOriginalParameterPoint y
  let x := incrementsOriginalSourcePoint y
  let phi := fun w : Es => e (p,w)
  have hxy : phi x = y := by
    change e (p,x) = y
    exact e.apply_symm_apply y
  have hcoords := parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF i
  have hd := (hcoords.contDiffAt ((parameterRound2_originalDifferentiation_open A B i).mem_nhds hy)).differentiableAt (by simp)
  have hphi : HasFDerivAt phi (e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ Ep Es)) x :=
    e.hasFDerivAt.comp x (hasFDerivAt_prodMk_right p x)
  have hd' : HasFDerivAt (incrementsOriginalMapCoordinates A B F i)
      (fderiv ℝ (incrementsOriginalMapCoordinates A B F i) y) (phi x) := by
    rw [hxy]
    exact hd.hasFDerivAt
  have hc := cY.symm.hasFDerivAt.comp x (hd'.comp x hphi)
  have heq : (cY.symm ∘ incrementsOriginalMapCoordinates A B F i ∘ phi) =
      (fun w => F ((B i.2).symm p,(A.chart i.1).symm w)) := by
    funext w
    change cY.symm (cY (F (incrementsOriginalJointPoint A B i (phi w)))) = _
    rw [cY.symm_apply_apply]
    have he := e.symm_apply_apply (p,w)
    change (incrementsOriginalParameterPoint (phi w),incrementsOriginalSourcePoint (phi w)) = (p,w) at he
    exact congrArg (fun z : Ep × Es => F ((B i.2).symm z.1,(A.chart i.1).symm z.2)) he
  rw [heq] at hc
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearMap.inr_apply] using
    congrArg (fun L : Es →L[ℝ] Ey => L v) hc.fderiv

/-- Convergence of the original coordinate first derivatives gives convergence
of the same native induced-metric coefficients, with only source directions. -/
theorem round3_repair_metric_coordinates_tendsto
    {c : ℕ} (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Fseq : ℕ → P × M → Ey) (F : P × M → Ey)
    (hseq : ∀ j, ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (Fseq j))
    (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (i : Fin A.count × Fin c) (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalDifferentiation A B i)
    (hD : Tendsto (fun j => fderiv ℝ (incrementsOriginalMapCoordinates A B (Fseq j) i) y) atTop
      (𝓝 (fderiv ℝ (incrementsOriginalMapCoordinates A B F i) y))) (a : Fin (n*n)) :
    Tendsto (fun j => incrementsOriginalTensorCoordinates A B
      (fun p x => inducedMetric (I := IT) (fun z => Fseq j (p,z)) x) i y a) atTop
      (𝓝 (incrementsOriginalTensorCoordinates A B (fun p x => inducedMetric (I := IT) (fun z => F (p,z)) x) i y a)) := by
  have hSource (v : Es) :
      Tendsto (fun j => fderiv ℝ (fun x => Fseq j ((B i.2).symm (incrementsOriginalParameterPoint y),(A.chart i.1).symm x))
        (incrementsOriginalSourcePoint y) v) atTop
        (𝓝 (fderiv ℝ (fun x => F ((B i.2).symm (incrementsOriginalParameterPoint y),(A.chart i.1).symm x))
          (incrementsOriginalSourcePoint y) v)) := by
    have hEval := ((continuous_eval_const (parameterTensorModelEquiv n d (0,v))).tendsto
      (fderiv ℝ (incrementsOriginalMapCoordinates A B F i) y)).comp hD
    have h := ((EuclideanSpace.equiv (Fin N) ℝ).symm.continuous.tendsto _).comp hEval
    have heq (j : ℕ) := round3_repair_source_derivative_original_coordinates A B hA hB (Fseq j) (hseq j) i y hy v
    have heqF := round3_repair_source_derivative_original_coordinates A B hA hB F hF i y hy v
    simpa only [heq,heqF,Function.comp_def] using h
  have h := Filter.Tendsto.inner (𝕜 := ℝ)
    (hSource (EuclideanSpace.single (finProdFinEquiv.symm a).1 1))
    (hSource (EuclideanSpace.single (finProdFinEquiv.symm a).2 1))
  have heq (j : ℕ) := parameterRound2_inducedMetric_originalCoordinates_eq A B hA (Fseq j) (hseq j) i y hy a
  have heqF := parameterRound2_inducedMetric_originalCoordinates_eq A B hA F hF i y hy a
  simpa only [heq,heqF] using h

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_source_derivative_original_coordinates
#print axioms GlobalEmbedding.Continuation.round3_repair_metric_coordinates_tendsto
