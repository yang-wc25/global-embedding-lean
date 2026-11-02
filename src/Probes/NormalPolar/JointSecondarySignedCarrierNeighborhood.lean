import NormalPolar.JointSecondarySignedRefinement
import Probes.ActualIncrementSupportConditioning
import Probes.Round3PreparedTransverseGood

/-! Goodness on a compact carrier produces an actual open Good neighborhood
inside an already adapted chart. The proof uses the true transverse frame:
support-only conditioning gives a positive reserve on an open neighborhood,
and the converse frame theorem returns the original GoodCovector predicate.
The phase, ambient map and chart functions are never replaced. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

theorem jointSecondary_good_open_on_adapted_carrier
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (phase : M → ℝ) (O : Set M) (hO : IsOpen O)
    (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas IM ∞ M)
    (heO : e.source ⊆ O) (hadapt : ∀ y ∈ e.target, phase (e.symm y) = y 0)
    (C : Set M) (hC : IsCompact C) (hCe : C ⊆ e.source)
    (hgood : ∀ x ∈ C, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    ∃ U : Set M, IsOpen U ∧ C ⊆ U ∧ U ⊆ e.source ∧
      ∀ x ∈ U, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x) := by
  let W : Set (Z × M) := univ ×ˢ O
  let A : Set X := univ ×ˢ e.target
  let K : Set X := univ ×ˢ (e '' C)
  have hFj : ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,V) ∞
      (fun z : Z × M => F z.2) W := hF.comp_contMDiffOn contMDiffOn_snd
  have hpj : ContMDiffOn ((𝓘(ℝ,Z)).prod IM) 𝓘(ℝ,ℝ) ∞
      (fun z : Z × M => phase z.2) W :=
    hphase.comp contMDiffOn_snd (fun z hz => hz.2)
  have hcj : ContMDiffOn 𝓘(ℝ,X) IM ∞ (fun z : X => e.symm z.2) A :=
    (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      contDiffOn_snd.contMDiffOn (fun z hz => hz.2)
  have hK : IsCompact K := isCompact_univ.prod
    (hC.image_of_continuousOn (e.continuousOn.mono hCe))
  have hKA : K ⊆ A := by
    rintro z ⟨_,x,hx,hxz⟩
    exact ⟨mem_univ _,hxz ▸ e.map_source (hCe hx)⟩
  have hKG (z : X) (hz : z ∈ K) :
      GoodCovector F hF (e.symm z.2)
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (phase (e.symm z.2))).toContinuousLinearMap.comp
          (mfderiv IM 𝓘(ℝ,ℝ) phase (e.symm z.2))) := by
    change GoodCovector F hF (e.symm z.2) (mfderiv IM 𝓘(ℝ,ℝ) phase (e.symm z.2))
    obtain ⟨x,hx,hxz⟩ := hz.2
    rw [←hxz,e.left_inv (hCe hx)]
    exact hgood x hx
  obtain ⟨cF,cT,A0,hcF,hcT,hA0,hKA0,hA0A,hfirst,hframe⟩ :=
    actual_increment_support_only_good_open_reserves (fun _ : Z => F) (fun _ => hF)
      (fun _ : Z => e) (fun _ => he) (fun _ : Z => phase) W A
      (isOpen_univ.prod e.open_target) hFj hpj hcj (fun z hz => hz.2)
      (fun z hz => ⟨mem_univ _,heO (e.map_target hz.2)⟩)
      (isOpen_univ.prod hO) (fun z _ => hImm (e.symm z.2))
      (fun z hz => hadapt z.2 hz.2) K hK hKA hKG
  let Uc : Set D := (fun y : D => ((0 : Z),y)) ⁻¹' A0
  have hUc : IsOpen Uc := hA0.preimage (continuous_const.prodMk continuous_id)
  have hUct : Uc ⊆ e.target := fun y hy => (hA0A hy).2
  let U : Set M := e.source ∩ e ⁻¹' Uc
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source hUc
  have hCU : C ⊆ U := fun x hx => ⟨hCe hx,hKA0 ⟨mem_univ _,x,hx,rfl⟩⟩
  refine ⟨U,hU,hCU,inter_subset_left,?_⟩
  intro x hx
  have hpx : MDifferentiableAt IM 𝓘(ℝ,ℝ) phase (e.symm (e x)) := by
    rw [e.left_inv hx.1]
    exact (hphase.contMDiffAt (hO.mem_nhds (heO hx.1))).mdifferentiableAt (by simp)
  have hg := round3_prepared_good_of_transverse_reserve F hF phase e he Uc hUc hUct
    (e x) hx.2 hpx (fun y hy => hadapt y (hUct hy)) cT hcT (hframe (0,e x) hx.2)
  change GoodCovector F hF (e.symm (e x)) (mfderiv IM 𝓘(ℝ,ℝ) phase (e.symm (e x))) at hg
  exact (congrArg (fun y : M => GoodCovector F hF y (mfderiv IM 𝓘(ℝ,ℝ) phase y))
    (e.left_inv hx.1)).mp hg

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_good_open_on_adapted_carrier
