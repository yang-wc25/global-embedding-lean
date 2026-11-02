import Probes.Round4ParameterProbeMeanCoordinates
import Probes.Round4ParameterProbeCombinedSecondary

/-! The selected mean term in the actual common-array secondary metric
identity is replaced by the genuine consecutive background-error residual.
All regularity is local to the original working domain. The statement uses
the literal original observer and its unchanged tensor coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N p r pcount : ℕ} {M Λ Β : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- The actual opposite mean of the combined primary solver, evaluated in
the original atlas, is exactly the same finite-iterate physical residual.
No output mean bound or phase-germ classification is an input. -/
theorem round4ParameterProbe_combined_original_mean_residual
    (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
    (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
    (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
    (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=𝓙) (F b) (c l b x))
    (phase : Fin r → Ep × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength : ℕ)
    (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
    (target : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (hdelta : delta ≠ 0) (j : ℕ) (u : Fin p → ℝ) (W : Set (Ep × M)) (hW : IsOpen W) :
    let probe := round4PrescribedNativeMean label F hF c vf phase tau probeLength a
    let A := round4ActualBackgroundMeanIterate F hF g backgroundLength tau delta target probe
    ∀ (hphase : ∀ l : Λ ⊕ Fin r, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
      (Sum.elim g.phase phase l) W)
      (hbackground : ∀ nu ch, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
        (incrementsGlobalPrimaryAmplitude F hF g (A (j+1) u) backgroundLength tau ch nu) W)
      (hprobe : ∀ l ch, ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
        (round4PrescribedGlobalAmplitude ch label l F hF (c l) (vf l) tau probeLength (a l) u) W)
      (atlas : BufferedAtlas M D) (param : Fin pcount → OpenPartialHomeomorph Ep Ep)
      (hAtlas : IsSmoothBufferedAtlas atlas) (idx : Fin atlas.count × Fin pcount) (z : X),
    z.2 ∈ (atlas.chart idx.1).target →
    ((param idx.2).symm z.1,(atlas.chart idx.1).symm z.2) ∈ W →
    let R := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a (A (j+1) u) u false
    let Q := round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
      backgroundLength probeLength a (A (j+1) u) u true
    actualPrimaryOppositeMeanTensor
      (fun l t x => Sum.elim g.phase phase l ((param idx.2).symm t,(atlas.chart idx.1).symm x)) tau
      (fun (_ : Λ ⊕ Fin r) (_ : Ep) (_ : Unit) (_ : D) => 1)
      (fun l t (_ : Unit) x => R l ((param idx.2).symm t,(atlas.chart idx.1).symm x))
      (fun l t (_ : Unit) x => Q l ((param idx.2).symm t,(atlas.chart idx.1).symm x)) z -
        delta^2 • actualOriginalNativeTargetTensor atlas param target idx z =
      delta^2 • actualOriginalNativeTargetTensor atlas param
        (fun b x => incrementsGlobalPrimaryMeanError F hF g (A (j+1) u) backgroundLength tau b x -
          incrementsGlobalPrimaryMeanError F hF g (A j u) backgroundLength tau b x) idx z := by
  intro probe A hphase hbackground hprobe atlas param hAtlas idx z hz hzW R Q
  have hAmp (ch : Bool) (l : Λ ⊕ Fin r) :
      ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
        (round4ParameterProbeCombinedAmplitude F hF g label c vf tau delta
          backgroundLength probeLength a (A (j+1) u) u ch l) W := by
    cases l with
    | inl nu =>
      exact ((contMDiffOn_const : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
        (fun _ : Ep × M => delta) W).smul (hbackground nu (!ch)))
    | inr l => exact hprobe l ch
  have hid := round4ParameterProbe_array_mean_original atlas param hAtlas (Sum.elim g.phase phase)
    tau R Q idx z hz (fun l => (hphase l).contMDiffAt (hW.mem_nhds hzW))
    (fun l => (hAmp false l).contMDiffAt (hW.mem_nhds hzW))
    (fun l => (hAmp true l).contMDiffAt (hW.mem_nhds hzW))
  rw [← hid]
  have hamp (b : Ep) (x : M) (hx : (b,x) ∈ W) (nu : Λ) (ch : Bool) :
      MDifferentiableAt 𝓙 𝓘(ℝ,V)
        (fun y => incrementsGlobalPrimaryAmplitude F hF g (A (j+1) u)
          backgroundLength tau ch nu (b,y)) x := by
    exact (((hbackground nu ch).contMDiffAt (hW.mem_nhds hx)).comp x
      ((contMDiffAt_const (c:=b)).prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hres := round4ParameterProbeCombinedMean_actual_iterate_residual_on F hF g label c vf phase
    tau delta backgroundLength probeLength a target hdelta j u W hamp
    ((param idx.2).symm z.1) ((atlas.chart idx.1).symm z.2) hzW
  apply actual_bilinear_tensor_eq_of_basis
  intro i k
  simp only [actualOriginalNativeTargetTensor_basis,sub_apply,smul_apply,smul_eq_mul,
    LinearMap.sub_apply]
  exact congrArg (fun T : LinearMap.BilinForm ℝ (TangentSpace 𝓙 ((atlas.chart idx.1).symm z.2)) =>
    T (incrementsGlobalObservationVector (I:=𝓙) (atlas.chart idx.1) z.2 i)
      (incrementsGlobalObservationVector (I:=𝓙) (atlas.chart idx.1) z.2 k)) hres

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_combined_original_mean_residual
