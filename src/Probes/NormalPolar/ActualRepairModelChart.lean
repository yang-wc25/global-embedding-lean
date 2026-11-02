import NormalPolar.ActualRepairModelAtlas
import NormalPolar.ActualRepairSamplingAtlas
import Smoothing.ParameterRound2OriginalInputs
import Smoothing.ParameterRound2CompactNorms

/-!
# The actual repaired map in its original parameter chart

The family below is the literal pullback of one native map on P × M.
Its joint smoothness is proved from that map and the actual chart inverse.
On the repair sampling atlas, the native parameter-column Cj norm is
bounded by the original mixed norm of the same map, with constant one.
The only parameter restriction is membership in the existing sample Q.
-/

noncomputable section
open Set Filter Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
  GlobalEmbedding.Continuation
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

variable {n d N c : ℕ} {M P : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,Es)
local instance actualRepairModelChartProduct : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance actualRepairModelChartManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IM) (n := ∞) P M

/-- The original parameter chart evaluates the same map, on all source points. -/
def actualRepairModelChartFamily (B : OpenPartialHomeomorph P Ep)
    (F : P × M → Ey) (u : Fin d → ℝ) (x : M) : Ey :=
  F (B.symm ((EuclideanSpace.equiv (Fin d) ℝ).symm u),x)

@[simp] theorem actualRepairModel_sourcePoint (u : Fin d → ℝ) (x : Fin n → ℝ) :
    incrementsOriginalSourcePoint (sourceFirstCoordinates n d (u,x)) =
      (EuclideanSpace.equiv (Fin n) ℝ).symm x := by
  ext j
  simp [incrementsOriginalSourcePoint]

@[simp] theorem actualRepairModel_parameterPoint (u : Fin d → ℝ) (x : Fin n → ℝ) :
    incrementsOriginalParameterPoint (sourceFirstCoordinates n d (u,x)) =
      (EuclideanSpace.equiv (Fin d) ℝ).symm u := by
  ext j
  simp [incrementsOriginalParameterPoint]

theorem actualRepairModelChartFamily_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F) :
    ContMDiffOn ((𝓘(ℝ,Fin d → ℝ)).prod IM) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (actualRepairModelChartFamily B F))
      (((EuclideanSpace.equiv (Fin d) ℝ) '' B.target) ×ˢ univ) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let U := e '' B.target
  have hp : ContMDiffOn ((𝓘(ℝ,Fin d → ℝ)).prod IM) 𝓘(ℝ,Ep) ∞
      (fun z : (Fin d → ℝ) × M => e.symm z.1) (U ×ˢ univ) :=
    (e.symm.contDiff.contMDiff.comp contMDiff_fst).contMDiffOn
  have hpi : ContMDiffOn ((𝓘(ℝ,Fin d → ℝ)).prod IM) 𝓘(ℝ,Ep) ∞
      (fun z : (Fin d → ℝ) × M => B.symm (e.symm z.1)) (U ×ˢ univ) := by
    exact (contMDiffOn_symm_of_mem_maximalAtlas hB).comp hp (by
      rintro z ⟨⟨p,hp,hpz⟩,_⟩
      change e.symm z.1 ∈ B.target
      rw [← hpz,e.symm_apply_apply]
      exact hp)
  have hj : ContMDiffOn ((𝓘(ℝ,Fin d → ℝ)).prod IM) 𝓘(ℝ,Ep × Es) ∞
      (fun z : (Fin d → ℝ) × M => (B.symm (e.symm z.1),z.2)) (U ×ˢ univ) := by
    rw [modelWithCornersSelf_prod]
    exact hpi.prodMk contMDiffOn_snd
  exact hF.comp_contMDiffOn hj

theorem actualRepairModelChartFamily_coordinates
    (A : BufferedAtlas M Es) (B : Fin c → OpenPartialHomeomorph P Ep)
    (F : P × M → Ey) (i : Fin A.count) (b : Fin c)
    (u : Fin d → ℝ) (x : Fin n → ℝ) :
    incrementsOriginalMapCoordinates A B F (i,b) (sourceFirstCoordinates n d (u,x)) =
      (EuclideanSpace.equiv (Fin N) ℝ) (actualRepairModelChartFamily (B b) F u
        ((A.chart i).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))) := by
  simp only [incrementsOriginalMapCoordinates,incrementsOriginalJointPoint,
    actualRepairModel_sourcePoint,actualRepairModel_parameterPoint,
    actualRepairModelChartFamily]

/-- Actual Q-sampling supplies the whole-source native response on the
sampling atlas. No assumption about an unrelated atlas support is required. -/
theorem actualRepairModelChartFamily_response_le_mixed
    (A : BufferedAtlas M Es) (hA : IsSmoothBufferedAtlas A)
    (B : Fin c → OpenPartialHomeomorph P Ep)
    (hB : ∀ b, B b ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (Omega : Fin A.count → Set Es) (Q : Fin c → Set Ep)
    (hOmega : ∀ i, Omega i ⊆ (A.chart i).target)
    (hQ : ∀ b, Q b ⊆ (B b).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i)
    (F : P × M → Ey) (hF : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ F)
    (b : Fin c) (u : Fin d → ℝ)
    (hu : u ∈ (EuclideanSpace.equiv (Fin d) ℝ) '' Q b) (a : Fin d) (j : ℕ) :
    probeAtlasCj (actualRepairSamplingAtlas A Omega) j
      (fun x => fderiv ℝ (fun v => actualRepairModelChartFamily (B b) F v x) u (Pi.single a 1)) ≤
      ⨆ i, paperMixedCoordinateCj (nx := n) (np := d) j 1
        (incrementsOriginalMapCoordinates A B F i)
        (incrementsOriginalDifferentiation A B i)
        (incrementsOriginalEvaluation A B Omega Q univ i) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let U := e '' (B b).target
  have huQ : e.symm u ∈ Q b := by
    rcases hu with ⟨p,hp,rfl⟩
    simpa only [e,ContinuousLinearEquiv.symm_apply_apply] using hp
  have huU : u ∈ U := ⟨e.symm u,hQ b huQ,e.apply_symm_apply u⟩
  have hU : IsOpen U := e.toHomeomorph.isOpenMap _ (B b).open_target
  have hSource : ∀ i, (EuclideanSpace.equiv (Fin n) ℝ) '' (A.chart i).target ⊆
      actualRepairModelSlice u (incrementsOriginalDifferentiation A B (i,b)) := by
    intro i x hx
    change incrementsOriginalSourcePoint (sourceFirstCoordinates n d (u,x)) ∈ (A.chart i).target ∧
      incrementsOriginalParameterPoint (sourceFirstCoordinates n d (u,x)) ∈ (B b).target
    rw [actualRepairModel_sourcePoint,actualRepairModel_parameterPoint]
    rcases hx with ⟨y,hy,rfl⟩
    exact ⟨by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hy,hQ b huQ⟩
  have hSamples : ∀ i x,
      x ∈ (EuclideanSpace.equiv (Fin n) ℝ) ''
        ((A.chart i) '' (actualRepairSamplingAtlas A Omega).support i) →
      sourceFirstCoordinates n d (u,x) ∈ incrementsOriginalEvaluation A B Omega Q univ (i,b) := by
    intro i x hx
    rw [actualRepairSamplingAtlas_coordinate_support A Omega hOmega i] at hx
    rcases hx with ⟨y,hy,rfl⟩
    simp only [incrementsOriginalEvaluation,incrementsOriginalDifferentiation,
      actualRepairModel_sourcePoint,actualRepairModel_parameterPoint,
      ContinuousLinearEquiv.symm_apply_apply,mem_ofPred_eq,mem_univ,and_true]
    exact ⟨⟨hOmega i hy,hQ b huQ⟩,hy,huQ⟩
  have h := actualRepairModel_probeAtlasCj_le_mixed
    (actualRepairSamplingAtlas A Omega)
    (actualRepairSamplingAtlas_smooth A hA Omega hOmega)
    (actualRepairSamplingAtlas_support_cover A Omega hSampling) hU
    (actualRepairModelChartFamily (B b) F)
    (actualRepairModelChartFamily_smooth (B b) (hB b) F hF)
    (fun i => incrementsOriginalMapCoordinates A B F (i,b))
    (fun i => incrementsOriginalDifferentiation A B (i,b))
    (fun i => incrementsOriginalEvaluation A B Omega Q univ (i,b))
    (fun i => parameterRound2_originalDifferentiation_open A B (i,b))
    (fun i => parameterRound2_originalMapCoordinates_contDiffOn A B hA hB F hF (i,b))
    (fun i v _ x _ => actualRepairModelChartFamily_coordinates A B F i b v x)
    u huU hSource hSamples j a
  apply h.trans
  apply iSup_le
  intro i
  exact le_iSup (fun k => paperMixedCoordinateCj (nx := n) (np := d) j 1
    (incrementsOriginalMapCoordinates A B F k) (incrementsOriginalDifferentiation A B k)
    (incrementsOriginalEvaluation A B Omega Q univ k)) (i,b)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualRepairModelChartFamily_smooth
#print axioms GlobalEmbedding.NormalPolar.actualRepairModelChartFamily_response_le_mixed
