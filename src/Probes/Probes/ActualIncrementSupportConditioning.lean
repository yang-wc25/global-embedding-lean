import Probes.ActualIncrementCompactOpenReserves
import Probes.ActualOriginalTransverseStability

/-! Actual support-only Good is enough for conditioning. Original secondary
interaction Good is supplied only on the joint cutoff support; this theorem
constructs its open conditioning neighborhood and never assumes Good on an
already selected whole open chart. All first/Hessian/normal columns are those
of the displayed map and its actual joint chart inverse. -/

noncomputable section
open GlobalEmbedding.Paper Manifold Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Pairs" => {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "Tdata" => EuclideanSpace ℝ Pairs
private local instance supportFirstNormed : NormedAddCommGroup (D →L[ℝ] V) := inferInstance
private local instance supportFirstSpace : NormedSpace ℝ (D →L[ℝ] V) := inferInstance
private local instance supportHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance supportHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] V) := inferInstance
private local instance supportFrameNormed : NormedAddCommGroup (Tdata →L[ℝ] V) := inferInstance
private local instance supportFrameSpace : NormedSpace ℝ (Tdata →L[ℝ] V) := inferInstance
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]

theorem actual_increment_support_only_good_open_reserves
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (psi : Ep → M → ℝ) (W : Set (Ep × M)) (O : Set (Ep × D)) (hO : IsOpen O)
    (hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞ (Function.uncurry F) W)
    (hpsi : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (Function.uncurry psi) W)
    (hcjoint : ContMDiffOn 𝓘(ℝ,Ep × D) 𝓙 ∞ (fun z => (e z.1).symm z.2) O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hmap : MapsTo (fun z : Ep × D => (z.1,(e z.1).symm z.2)) O W)
    (hW : IsOpen W)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ,V) (F z.1) ((e z.1).symm z.2)))
    (hadapt : ∀ z ∈ O, psi z.1 ((e z.1).symm z.2) = z.2 0)
    (K : Set (Ep × D)) (hK : IsCompact K) (hKO : K ⊆ O)
    (hgood : ∀ z ∈ K, GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (psi z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2))))
    :
    ∃ (cF cT : ℝ) (O0 : Set (Ep × D)), 0 < cF ∧ 0 < cT ∧
      IsOpen O0 ∧ K ⊆ O0 ∧ O0 ⊆ O ∧
      (∀ z ∈ O0, ∀ v : D,
        cF*‖v‖^2 ≤ ‖fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2 v‖^2) ∧
      ∀ z ∈ O0, ∀ v : Tdata,
        cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
          (F z.1) (hF z.1) (e z.1).symm z.2 v‖^2 := by
  have hpc : ContMDiffOn 𝓘(ℝ,Ep × D) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (fun z : Ep × D => (z.1,(e z.1).symm z.2)) O :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk hcjoint
  have hFc : ContDiffOn ℝ ∞ (fun z : Ep × D => F z.1 ((e z.1).symm z.2)) O :=
    (hFjoint.comp hpc hmap).contDiffOn
  obtain ⟨hSlice,hFirst,hSecond⟩ := incrementsJointSpatialJets_bridge _ O hO hFc
  let first := fun z : Ep × D => fderiv ℝ (F z.1 ∘ (e z.1).symm) z.2
  let H := fun z : Ep × D => fderiv ℝ (fderiv ℝ (F z.1 ∘ (e z.1).symm)) z.2
  let frame := fun z : Ep × D => incrementsModeAmbientTransverseFrame
    (F z.1) (hF z.1) (e z.1).symm z.2
  have hFirstInj (z : Ep × D) (hz : z ∈ O) : Function.Injective (first z) :=
    actual_increment_chart_derivative_injective (F z.1) (hF z.1) (e z.1) (he z.1)
      z.2 (hcoord z hz) (hinj z hz)
  have hProjection : ContDiffOn ℝ ∞
      (fun z : Ep × D => (LinearMap.range (first z).toLinearMap)ᗮ.starProjection) O :=
    smooth_frame_normal_projection first hFirst hFirstInj
  have hFrame : ContDiffOn ℝ ∞ frame O := by
    have hSecond' : ContDiffOn ℝ ∞ H O := by
      simpa only [H,Function.comp_def] using hSecond
    have hColumns : ContDiffOn ℝ ∞ (fun z => actualIncrementTransverseColumns m N (H z)) O :=
      (actualIncrementTransverseColumns m N).contDiff.comp_contDiffOn hSecond'
    apply (hProjection.clm_comp hColumns).congr
    intro z hz
    exact actual_original_transverse_frame_projected_columns (F z.1) (hF z.1)
      (e z.1) (he z.1) z.2 (hcoord z hz)
  have hFrameInj (z : Ep × D) (hz : z ∈ K) : Function.Injective (frame z) := by
    have hzO := hKO hz
    have hslice : IsOpen {x : D | (z.1,x) ∈ O} :=
      hO.preimage (continuous_const.prodMk continuous_id)
    have hpsiAt : MDifferentiableAt 𝓙 𝓘(ℝ,ℝ) (psi z.1) ((e z.1).symm z.2) := by
      have hh := (hpsi.contMDiffAt (hW.mem_nhds (hmap hzO))).comp
        ((e z.1).symm z.2) (contMDiffAt_const.prodMk contMDiffAt_id)
      exact hh.mdifferentiableAt (by simp)
    have hg := actual_increment_transverse_gram_of_good_phase
      (F z.1) (hF z.1) (psi z.1) (e z.1) (he z.1)
      {x : D | (z.1,x) ∈ O} hslice (fun x hx => hcoord (z.1,x) hx) z.2 hzO hpsiAt
      (fun x hx => hadapt (z.1,x) hx) (hgood z hz)
    exact incrementsModeAmbientTransverseFrame_injective _ _ _ _ hg
  obtain ⟨cF,OF,hcF,hOF,hKOF,hOFO,hFb⟩ := actual_compact_frame_open_reserve
    first O K hO hK hKO hFirst.continuousOn (fun z hz => hFirstInj z (hKO hz))
  obtain ⟨cT,OT,hcT,hOT,hKOT,hOTO,hTb⟩ := actual_compact_frame_open_reserve
    frame O K hO hK hKO hFrame.continuousOn hFrameInj
  exact ⟨cF,cT,OF ∩ OT,hcF,hcT,hOF.inter hOT,
    fun _ hz => ⟨hKOF hz,hKOT hz⟩,fun _ hz => hOFO hz.1,
    fun z hz => hFb z hz.1,fun z hz => hTb z hz.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_increment_support_only_good_open_reserves
