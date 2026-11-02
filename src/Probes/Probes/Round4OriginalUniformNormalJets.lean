import Probes.Round4OriginalUniformNormal
import Smoothing.Round4FreeNormalFiniteProfiles

/-!
The original-map normal and its neighborhood are fixed before every later
observation order and weighted high map budget. The actual higher normal
jets are derived from the same map's first and Hessian jets, with the named
numeric cost. No high-order normal or transverse-frame budget is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Manifold Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
private local instance originalJetsFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance originalJetsFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance originalJetsHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance originalJetsHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance originalJetsFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance originalJetsFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem round4_actual_original_uniform_normal_before_all_orders
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (O : Set X) (hO : IsOpen O) (hConv : Convex ℝ O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hJoint : ContDiffOn ℝ ∞ (fun z : X => F z.1 ((e z.1).symm z.2)) O)
    (cF cT MA MH : ℝ) (hcF : 0 < cF) (hcT : 0 < cT)
    (hMA : 0 ≤ MA) (hMH : 0 ≤ MH)
    (hFirst : ∀ z ∈ O, ∀ w : D,
      cF*‖w‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 w‖^2)
    (hFrame : ∀ z ∈ O, ∀ w : Tdata, cT*‖w‖^2 ≤
      ‖incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 w‖^2)
    (hAj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ MA)
    (hHj : ∀ k ≤ 1, ∀ z ∈ O, ‖iteratedFDeriv ℝ k
      (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ MH)
    (hdim : (m+1)*(m+2)/2 < N) (x : X) (hx : x ∈ O) :
    let rho := round4OriginalNormalRadius m N cF cT MA MH
    let S := O ∩ ball x rho
    0 < rho ∧ ∃ i : Fin N,
      let normal := actualOriginalUnitFreeNormal F hF e (EuclideanSpace.single i 1)
      ContDiffOn ℝ ∞ normal S ∧
      (∀ z ∈ S, ∃ nu : normalSpace (I := 𝓙) (F z.1) ((e z.1).symm z.2),
        (nu : V) = normal z ∧ ‖nu‖ = 1 ∧
        incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
          (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ) nu = 0) ∧
      ∀ (j : ℕ) (ell Aj Hj : ℝ), 0 < ell → 0 ≤ Aj → 0 ≤ Hj →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (F y.1 ∘ (e y.1).symm) y.2) z‖ ≤ Aj) →
        (∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k
          (fun y : X => fderiv ℝ (fderiv ℝ (F y.1 ∘ (e y.1).symm)) y.2) z‖ ≤ Hj) →
        ∀ k ≤ j, ∀ z ∈ S, ell^k*‖iteratedFDeriv ℝ k normal z‖ ≤
          round4OriginalNormalConstant m N j cF cT Aj Hj
            (round4AmbientCoordinateReserve N / 2) 1
            (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num)) := by
  obtain ⟨hrho, i, hsmooth, hnormal⟩ := round4_actual_original_uniform_normal F hF e he
    O hO hConv hcoord hJoint cF cT MA MH hcF hcT hMA hMH hFirst hFrame hAj hHj hdim x hx
  refine ⟨hrho, i, hsmooth, fun z hz => (hnormal z hz).2, ?_⟩
  intro j ell Aj Hj hell hAj0 hHj0 hAhigh hHhigh
  let S := O ∩ ball x (round4OriginalNormalRadius m N cF cT MA MH)
  let A := fun z : X => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let B := fun z : X => incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2
  let MB := actualIncrementTransverseFrameConstant m N j cF Aj Hj
  have hMB : 0 ≤ MB := actualIncrementTransverseFrameConstant_nonneg m N j hcF hAj0 hHj0
  obtain ⟨hSlice, hA, hH⟩ := incrementsJointSpatialJets_bridge _ O hO hJoint
  have hAi (z : X) (hz : z ∈ O) : Function.Injective (A z) :=
    actual_frame_injective_of_reserve (A z) cF hcF (hFirst z hz)
  obtain ⟨hQ, hQj⟩ := actual_increment_projected_hessian_slow_jets_on_samples F hF e he O S
    hO inter_subset_left hcoord hA hH hAi j ell cF Aj Hj hell hcF hAj0 hHj0
    (fun z hz => hFirst z hz.1) hAhigh hHhigh
  obtain ⟨hRows, hB⟩ := actual_true_geometry_from_normal_hessian_on_samples F hF e he O S
    hO inter_subset_left hcoord hQ j ell (actualIncrementSecondFormConstant m N j cF Aj Hj)
    hell.le hQj
  have hRange (z : X) (hz : z ∈ O) :
      LinearMap.range (B z).toLinearMap ≤ (LinearMap.range (A z).toLinearMap)ᗮ := by
    rintro w ⟨t,rfl⟩
    rw [← actual_increment_normalSpace_eq_chart_range (F z.1) (hF z.1)
      (e z.1) (he z.1) z.2 (hcoord z hz)]
    change incrementsModeAmbientTransverseFrame (F z.1) (hF z.1) (e z.1).symm z.2 t ∈ _
    rw [incrementsModeAmbientTransverseFrame_eq]
    exact ((incrementsTransversePairing (F z.1) (hF z.1) ((e z.1).symm z.2)
      (fun a : Fin m => incrementsModeCoordinateDirections (e z.1).symm z.2 a.succ)).adjoint t).property
  let v : V := EuclideanSpace.single i 1
  have hv : ∀ k ≤ j, ∀ z ∈ S,
      ell^k*‖iteratedFDeriv ℝ k (fun _ : X => v) z‖ ≤ 1 := by
    intro k _ z _
    cases k with
    | zero => simp [v]
    | succ k => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero, mul_zero]; norm_num
  have h := (round4_actual_unit_free_projection_field_slow_jets
    (E := D) (T := Tdata) (N := N) j cF cT Aj MB (round4AmbientCoordinateReserve N / 2) 1
    hcF hcT hAj0 hMB (div_pos (round4AmbientCoordinateReserve_pos N) (by norm_num))
    zero_le_one).2
    A B (fun _ => v) O S hO inter_subset_left hA hB.1 contDiffOn_const hAi
    (fun z hz => actual_frame_injective_of_reserve (B z) cT hcT (hFrame z hz))
    ell hell (fun z hz => hFirst z hz.1) (fun z hz => hFrame z hz.1)
    hAhigh hB.2 hv hRange (fun z hz => (hnormal z hz).1)
  exact h.2.2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_original_uniform_normal_before_all_orders
