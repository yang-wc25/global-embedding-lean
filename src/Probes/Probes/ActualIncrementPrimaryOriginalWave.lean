import Probes.ActualIncrementPrimaryFullWave
import Probes.ActualIncrementPrimaryGlobalSupport
import Probes.ActualSecondaryRemodulation

/-! The SAME original global-family local channels and their genuine adapted
coordinate wave. No replacement finite solver or wave is introduced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

theorem actual_original_primary_local_wave_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (t : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (ν : Λ) (β : Β) (n length j : ℕ) (horder : j+1+length ≤ n)
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
      (normalSpace (I := I) (F z.1) (g.inverse ν β z.1 z.2)).subtypeL.comp
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
    (hGb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (g.inverse ν β w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (g.inverse ν β w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (g.inverse ν β w.1) w.2) z‖ ≤ Mg)
    (hBRb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => fun i : Fin (m+1) =>
        (incrementsModeSecondForm (F w.1) (hF w.1) (g.inverse ν β w.1) w.2 0 i : V)) z‖ ≤ Mg)
    (hvfb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (incrementsGlobalPrimaryLocalFree F g input tau ν β w.1 w.2 : V)) z‖ ≤ K*tau) :
    let W := actualSecondaryModulation (fun z : X => z.2 0) tau
      (incrementsGlobalPrimaryLocalZ F hF g input length tau true ν β)
      (incrementsGlobalPrimaryLocalZ F hF g input length tau false ν β)
    ContDiffOn ℝ ∞ W (g.chart ν β).target ∧ ∀ r ≤ j, ∀ z ∈ S,
      tau^r*‖iteratedFDeriv ℝ r W z‖ ≤ actualPrimaryFullWaveCost m N n length j Mg K 0 1*tau := by
  intro W
  let vf := incrementsGlobalPrimaryLocalFree F g input tau ν β
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
  have hp : ContDiffOn ℝ ∞ (fun z : X => z.2 0) (g.chart ν β).target :=
    (actualSecondaryCoordinatePhase (Ep := Ep) (m := m)).contDiff.contDiffOn
  have hpb : ∀ k < j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ (k+1) (fun w : X => w.2 0) z‖ ≤ 1 := by
    intro k _ z _
    exact actual_linear_phase_slow_jets (actualSecondaryCoordinatePhase (Ep := Ep) (m := m))
      (actualSecondaryCoordinatePhase_norm_le (Ep := Ep) (m := m)) ell z k
  have hh := actual_primary_full_wave_weighted_jets F hF (g.inverse ν β) vf (fun _ _ => 0)
    (fun z : X => z.2 0) n length j horder (g.chart ν β).target S (g.chart ν β).open_target
    hSO hA hB hG hJ hT hBR hvf contDiffOn_const hp tau ell Mg K 0 tau 1 htau htaul hell1
    hMg hK le_rfl htau.le hAb hBb hGb hJb hTb hBRb hvfb (by intros; simp) hpb
  dsimp only at hh
  have hsx := fun z : X => congrFun hs z
  simp_rw [hsx] at hh
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
  rw [hR,hI]
  exact hh

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_original_primary_local_wave_jets
