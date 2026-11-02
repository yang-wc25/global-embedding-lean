import Probes.ActualJointHomogeneousReconstruction
import Probes.ActualJointHomogeneousParameter
import GlobalEmbedding.Paper.IncrementsPrimaryReconstructedChannels

/-! SAME-input subtraction for the genuine parameter-dependent finite
reconstruction. Totalized derivatives are compared only on true smooth germs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Cdata" => Fin (m+1) → ℂ

/-- Actual channel reconstruction is linear in its same source on the genuine
joint open set; the parameter is preserved in every spatial solve. -/
theorem actual_joint_reconstructed_channel_sub
    (F : Ep → M → V) (hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b))
    (c : Ep → D → M) (source sourcebar : X → Cdata)
    (channel : Cdata →L[ℝ] D) (tau : ℝ) (length : ℕ)
    (O : Set X) (hO : IsOpen O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hs : ContDiffOn ℝ ∞ source O) (hsbar : ContDiffOn ℝ ∞ sourcebar O) :
    EqOn (fun z : X =>
      incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1) channel tau length
        (fun x => source (z.1,x)) z.2 -
      incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1) channel tau length
        (fun x => sourcebar (z.1,x)) z.2)
      (fun z : X => incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1)
        channel tau length (fun x => source (z.1,x)-sourcebar (z.1,x)) z.2) O := by
  intro z hz
  let Os : Set D := (fun x : D => (z.1,x)) ⁻¹' O
  have hOs : IsOpen Os := hO.preimage (continuous_const.prodMk continuous_id)
  let A := incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1)
  let B := incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1)
  let alpha := (tau : ℂ)/Complex.I
  let k := fun x : D => source (z.1,x)
  let kb := fun x : D => sourcebar (z.1,x)
  let U := incrementsActualModeSum A B alpha length
  have hAs : ContDiffOn ℝ ∞ A Os := actual_joint_contDiffOn_slice _ O hA z.1
  have hBs : ContDiffOn ℝ ∞ B Os := actual_joint_contDiffOn_slice _ O hB z.1
  have hks : ContDiffOn ℝ ∞ k Os := actual_joint_contDiffOn_slice _ O hs z.1
  have hkbs : ContDiffOn ℝ ∞ kb Os := actual_joint_contDiffOn_slice _ O hsbar z.1
  have hu : ContDiffOn ℝ ∞ (fun x => channel (U k x)) Os :=
    channel.contDiff.comp_contDiffOn
      (increments_actual_mode_sum_contDiffOn A B alpha length k Os hOs hAs hBs hks)
  have hub : ContDiffOn ℝ ∞ (fun x => channel (U kb x)) Os :=
    channel.contDiff.comp_contDiffOn
      (increments_actual_mode_sum_contDiffOn A B alpha length kb Os hOs hAs hBs hkbs)
  have hr := incrementsModeReconstruction_sub (F z.1) (hF z.1) (c z.1) Os hOs
    (fun x => channel (U k x)) (fun x => channel (U kb x)) hu hub hz
  dsimp only at hr
  change incrementsModeReconstruction (F z.1) (hF z.1) (c z.1) (fun x => channel (U k x)) z.2 -
    incrementsModeReconstruction (F z.1) (hF z.1) (c z.1) (fun x => channel (U kb x)) z.2 =
      incrementsModeReconstruction (F z.1) (hF z.1) (c z.1)
        (fun x => channel (U (fun y => k y-kb y) x)) z.2
  rw [hr]
  have he : (fun x => channel (U k x)-channel (U kb x)) =ᶠ[𝓝 z.2]
      (fun x => channel (U (fun y => k y-kb y) x)) := by
    filter_upwards [hOs.mem_nhds hz] with x hx
    rw [← map_sub]
    congr 1
    exact (increments_actual_mode_sum_sub A B alpha length k kb Os hOs hAs hBs hks hkbs hx).symm
  rw [incrementsModeReconstruction_split, incrementsModeReconstruction_split,
    he.eq_of_nhds, he.fderiv_eq]

theorem actual_joint_reconstructed_channel_difference_jets
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (c : Ep → D → M) (source sourcebar : X → Cdata) (channel : Cdata →L[ℝ] D)
    (n length j : ℕ) (horder : j+1+length ≤ n)
    (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) O)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) O)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hT : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) O)
    (hsource : ContDiffOn ℝ ∞ source O) (hsourcebar : ContDiffOn ℝ ∞ sourcebar O)
    (tau ell Mg Ks : ℝ) (htau : 0 < tau) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (hMg : 0 ≤ Mg) (hKs : 0 ≤ Ks)
    (hAb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderA (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hBb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeComplexFirstOrderB (F w.1) (hF w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hGb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => freeGramRightInverse (fderiv ℝ (F w.1 ∘ c w.1) w.2)) z‖ ≤ Mg)
    (hJb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => (normalSpace (I := I) (F w.1) (c w.1 w.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F w.1) (hF w.1) (c w.1) w.2)) z‖ ≤ Mg)
    (hTb : ∀ k ≤ j, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k
      (fun w : X => incrementsModeTransverseValue (F w.1) (c w.1) w.2) z‖ ≤ Mg)
    (hsb : ∀ k ≤ n, ∀ z ∈ S, ell^k * ‖iteratedFDeriv ℝ k (fun w => source w-sourcebar w) z‖ ≤ Ks) :
    let R := fun (s : X → Cdata) (z : X) =>
      incrementsPrimaryReconstructedChannel (F z.1) (hF z.1) (c z.1) channel tau length
        (fun x => s (z.1,x)) z.2
    ContDiffOn ℝ ∞ (fun z => R source z-R sourcebar z) O ∧
      ∀ k ≤ j, ∀ z ∈ S, ell^(k+1) * ‖iteratedFDeriv ℝ k
        (fun w => R source w-R sourcebar w) z‖ ≤
          actualJointHomogeneousReconstructionCost m j Mg * ‖channel‖ * tau * Ks *
            ∑ a ∈ Finset.range length, (2 * 2^n * Mg)^a := by
  intro R
  have heq := actual_joint_reconstructed_channel_sub F hF c source sourcebar channel tau
    length O hO hA hB hsource hsourcebar
  obtain ⟨_,hR,hRb⟩ := actual_joint_finite_channel_reconstruction F hF c
    (fun w => source w-sourcebar w) channel n length j horder O S hO hSO hA hB hG hJ hT
    (hsource.sub hsourcebar) tau ell Mg Ks htau htaul hell1 hMg hKs hAb hBb hGb hJb hTb hsb
  change ContDiffOn ℝ ∞ (R (fun w => source w-sourcebar w)) O at hR
  refine ⟨hR.congr heq,?_⟩
  intro k hk z hz
  have he : (fun w => R source w-R sourcebar w) =ᶠ[𝓝 z]
      R (fun w => source w-sourcebar w) :=
    eventuallyEq_of_mem (hO.mem_nhds (hSO hz)) (fun w hw => heq hw)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hRb k hk z hz

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_reconstructed_channel_sub

#print axioms GlobalEmbedding.Continuation.actual_joint_reconstructed_channel_difference_jets
