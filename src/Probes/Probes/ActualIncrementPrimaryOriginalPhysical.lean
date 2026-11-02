import Probes.ActualIncrementPrimaryNativePhysical
import Probes.ActualIncrementPrimaryOriginalWave

/-! The native physical residual belongs to the literal original localZ
channels and finiteU. The original conditional local free datum supplies the
normal direction; its kernel follows from the same given normal, without
changing its scalar amplitude or selecting a new sign. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {M Ep : Type*} {m N : ℕ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

local notation "𝓙" => 𝓘(ℝ,D)

private local instance originalPrimaryTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance originalPrimaryTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance originalPrimaryTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem actual_original_primary_local_physical_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (ν : Λ) (β : Β) (n length j : ℕ) (horder : j+length ≤ n)
    (chart : Ep → OpenPartialHomeomorph M D)
    (hchart : ∀ b, chart b ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (hinverse : g.inverse ν β = fun b x => (chart b).symm x)
    (hTarget : ∀ z ∈ (g.chart ν β).target, z.2 ∈ (chart z.1).target)
    (hinj : ∀ z ∈ (g.chart ν β).target,
      Function.Injective (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) (g.inverse ν β z.1 z.2)))
    (hfree : ∀ z ∈ (g.chart ν β).target,
      let b := incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
      (b.comp b.adjoint).IsInvertible)
    (hnormalKernel : ∀ z (hz : z ∈ (g.chart ν β).target),
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
        ⟨g.normal ν (z.1,g.inverse ν β z.1 z.2),g.normal_mem ν β z hz⟩ = 0)
    (S : Set X) (hSO : S ⊆ (g.chart ν β).target)
    (tau ell Mg K : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hK : 0 ≤ K)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := 𝓙) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (g.inverse ν β z.1) z.2)) (g.chart ν β).target)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (g.inverse ν β z.1) z.2) (g.chart ν β).target)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i : Fin (m+1) =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (g.inverse ν β z.1) z.2 0 i : V)) (g.chart ν β).target)
    (hvf : ContDiffOn ℝ ∞ (fun z : X =>
      (incrementsGlobalPrimaryLocalFree F g input tau ν β z.1 z.2 : V)) (g.chart ν β).target)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hvfb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) z‖ ≤ K*tau) :
    let W := actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
    let E := fun z : X => actualCoordinateMetricLinearization (F z.1 ∘ g.inverse ν β z.1)
      (fun x => W (z.1,x)) z.2
    ContDiffOn ℝ ∞ W (g.chart ν β).target ∧ ContDiffOn ℝ ∞ E (g.chart ν β).target ∧
      ∀ r ≤ j, ∀ z ∈ S, tau^r*‖iteratedFDeriv ℝ r E z‖ ≤
        actualPrimaryPhysicalCost m N n length j Mg K 0 * (tau/ell)^length*tau := by
  intro W E
  let vf := incrementsGlobalPrimaryLocalFree F g input tau ν β
  have hk : ∀ z ∈ (g.chart ν β).target,
      incrementsTransversePairing (F z.1) (hF z.1) (g.inverse ν β z.1 z.2)
        (fun a : Fin m => incrementsModeCoordinateDirections (g.inverse ν β z.1) z.2 a.succ)
        (vf z.1 z.2) = 0 := by
    intro z hz
    simp only [vf,incrementsGlobalPrimaryLocalFree,dif_pos hz,map_smul,hnormalKernel z hz,smul_zero]
  have hh := actual_primary_native_physical_weighted_jets F hF chart hchart (g.inverse ν β) hinverse
    (g.chart ν β).target S (g.chart ν β).open_target hSO hTarget hinj hfree vf (fun _ _ => 0)
    hvf contDiffOn_const hk (by intros; exact map_zero _) hBR hA hB hG hJ hT n length j horder
    tau ell Mg K 0 tau htau htaul hell1 hMg hK le_rfl htau.le hBRb hAb hBb hvfb (by intros; simp)
  have hzero : actualHomogeneousSource F hF (g.inverse ν β) (fun _ _ => 0) = 0 := by
    funext z
    rw [actualHomogeneousSource_eq]
    simp only [Submodule.coe_zero,map_zero,Pi.zero_apply]
  have hs : (fun z : X => actualHomogeneousSource F hF (g.inverse ν β) vf z +
      Complex.I • actualHomogeneousSource F hF (g.inverse ν β) (fun _ _ => 0) z) =
      incrementsGlobalPrimarySource F hF g input tau ν β := by
    rw [hzero]
    simp only [Pi.zero_apply,smul_zero,add_zero]
    rfl
  dsimp only at hh
  simp_rw [fun z : X => congrFun hs z] at hh
  let U := incrementsGlobalPrimaryFiniteU F hF g input length tau ν β
  let ZR := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1)
    (g.inverse ν β z.1) (incrementsModeRealPart ∘ U z.1) (fun _ _ _ => 0) (vf z.1) z.2
  let ZI := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1)
    (g.inverse ν β z.1) (incrementsModeImagPart ∘ U z.1) (fun _ _ _ => 0) (fun _ => 0) z.2
  have hR : incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β = ZR := by
    funext z
    rfl
  have hI : incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β = ZI := by
    funext z
    rfl
  change ContDiffOn ℝ ∞ (actualSecondaryModulation (fun z : X => z.2 0) tau
    (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
    (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)) _ ∧ _
  dsimp only [E,W]
  rw [hR,hI]
  exact hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_primary_local_physical_jets
