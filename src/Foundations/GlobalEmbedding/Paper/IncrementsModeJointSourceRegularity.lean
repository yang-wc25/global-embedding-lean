import GlobalEmbedding.Paper.IncrementsJointActualGeometry
import GlobalEmbedding.Paper.IncrementsSecondaryMode

/-!
# ORIGINAL joint mode-source regularity: proposed ABI only

Source: `main.tex`, lem:increments594–643, actual (6.2)/finite parameters.
DAG: `increments-mode-joint-source-regularity`. Exclusive worker W2.
STAGE2 ONLY, pending ROOT exact statement lock. All three named holes are expected.
No source/packing/normal-bundle/norm/reconstruction definition is introduced.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {m N : ℕ} {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ

section General
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M]

/-- The SAME actual source splits into its original zero-free source and its
actual free-normal contribution, with the original row weights unchanged.

Natural-language proof, pending ROOT lock: evaluate the native Euclidean
components of the existing source and use canonical Q's exact evaluation.
The h and J h_H terms are identical on both sides and the zero-normal inner
term vanishes. Native real inner linearity and scalar arithmetic identify
the remaining actual vf term with 2 times Q(Brow)(vf). No new source or
packing is defined. Source: original (6.2), row11 weight1 and mixed weight2;
in particular the existing mixed J h_H coefficient stays minus ONE. This
pointwise identity has no smoothness, normal-kernel, Good or Gram hypothesis.
W4 consumes its h=0 specialization without duplicating this algebra. -/
theorem incrementsModeSource_eq_zeroFree_add (F : M → V)
    (hF : ContMDiff I 𝓘(ℝ, V) ∞ F) (c : D → M) (h : D → Source)
    (vf : (x : D) → normalSpace (I := I) F (c x)) (x : D) :
    incrementsModeSource F hF c h vf x =
      incrementsModeSource F hF c h (fun _ ↦ 0) x + (2 : ℝ) •
        incrementsModeForcingSourcePairing
          (fun i ↦ (incrementsModeSecondForm F hF c x 0 i : V)) (vf x : V) := by
  ext i
  change incrementsModeSource F hF c h vf x i =
    incrementsModeSource F hF c h (fun _ ↦ 0) x i + 2 *
      incrementsModeForcingSourcePairing
        (fun j ↦ (incrementsModeSecondForm F hF c x 0 j : V)) (vf x : V) i
  rw [incrementsModeForcingSourcePairing_apply]
  simp only [incrementsModeSource, Submodule.coe_inner, inner_zero_right]
  ring

/-- The literal ORIGINAL real mode source is jointly smooth from its actual
joint B/J fields and original input h/vf. Geometry regularity is an internal
producer input here; the actual-geometry wrapper below discharges it.

Natural-language proof, pending ROOT lock: apply canonical P0 to h, canonical
selector to h, and SAME inline included J to the selected h_H. Apply canonical
Q to actual true-B rows, then to actual ambient vf and to Jambient(h_H).
Native ContDiffOn.clm_apply/add/sub/smul prove regularity of
P0(h)+2*Q(Brow)(vf)-Q(Brow)(Jambient(h_H)). Existing exact P0/Q/selector
evaluations identify this with the literal source, including row11 half and
mixed J h_H coefficient minus ONE. No source identity or output bound is an
input. No new packing or weighted estimate is proved. Source: original (6.2).
This zero-order statement needs no openness, extension, compactness or scale.
Empty O, m=0, N=0 and dimension-zero parameter are permitted. -/
theorem incrementsModeSource_joint_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : Ep × D → Source)
    (vf : (p : Ep) → (x : D) → normalSpace (I := I) (F p) (c p x))
    (O : Set (Ep × D))
    (hB : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hh : ContDiffOn ℝ ∞ h O)
    (hvf : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vf z.1 z.2 : V)) O) :
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeSource (F z.1) (hF z.1) (c z.1)
        (fun x ↦ h (z.1, x)) (vf z.1) z.2) O := by
  have hs := incrementsModeTransverseSourceCLM.contDiff.comp_contDiffOn hh
  have hj := hJ.clm_apply hs
  have hb := incrementsModeForcingSourcePairing.contDiff.comp_contDiffOn hB
  have hp := incrementsModeForcingSourceProjection.contDiff.comp_contDiffOn hh
  have hz : ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeSource (F z.1) (hF z.1) (c z.1)
        (fun x ↦ h (z.1, x)) (fun _ ↦ 0) z.2) O := by
    apply (hp.sub (hb.clm_apply hj)).congr
    intro z hz
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, incrementsModeTransverseSource_eq_selector] using
      incrementsModeSource_zeroFree_eq (F z.1) (hF z.1) (c z.1)
        (fun x ↦ h (z.1, x)) z.2
  apply (hz.add ((hb.clm_apply hvf).const_smul (2 : ℝ))).congr
  intro z hz
  exact incrementsModeSource_eq_zeroFree_add (F z.1) (hF z.1) (c z.1)
    (fun x ↦ h (z.1, x)) (vf z.1) z.2

end General

section ActualGeometry
local notation "𝓙" => 𝓘(ℝ, D)
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) M]

/-- ORIGINAL joint input geometry and original real h/vf channels give joint
regularity of both SAME real sources and their unchanged native complex source.
No desired coefficient/source regularity or Gram/inverse margin is an input.

Natural-language proof, pending ROOT lock: invoke the accepted
incrementsJointActualGeometry_contDiffOn on the SAME original F/phase and
actual parameter-dependent maximal-atlas inverse. Select its actual true-B
rows and inline included-J fields. Apply incrementsModeSource_joint_contDiffOn
to the two original real channels, then compose canonical complex inclusion
and native addition/I-smul. The original mixed J h_H coefficient is minus ONE.
Actual adapted-chart existence, full input admissibility, uniform weighted
profile/validity bounds and W5 finiteU/R/Z/support remain separate obligations.
No complex normal bundle, new source, selected margin or final target premise
is introduced. Source: original (6.2) and finite auxiliary parameter clause. -/
theorem incrementsJointActualSource_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ, V) ∞ (F p))
    (e : Ep → OpenPartialHomeomorph M D)
    (he : ∀ p, e p ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (ψ : Ep → M → ℝ) (U : Set (Ep × M)) (O : Set (Ep × D)) (hO : IsOpen O)
    (hFjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, V) ∞ (Function.uncurry F) U)
    (hψjoint : ContMDiffOn ((𝓘(ℝ, Ep)).prod 𝓙) 𝓘(ℝ, ℝ) ∞ (Function.uncurry ψ) U)
    (hcjoint : ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙 ∞ (fun z ↦ (e z.1).symm z.2) O)
    (hcoord : ∀ z ∈ O, z.2 ∈ (e z.1).target)
    (hmap : MapsTo (fun z : Ep × D ↦ (z.1, (e z.1).symm z.2)) O U)
    (hU : IsOpen U)
    (hinj : ∀ z ∈ O, Function.Injective
      (mfderiv 𝓙 𝓘(ℝ, V) (F z.1) ((e z.1).symm z.2)))
    (hadapt : ∀ z ∈ O, ψ z.1 ((e z.1).symm z.2) = z.2 0)
    (hgood : ∀ z ∈ O, GoodCovector (F z.1) (hF z.1) ((e z.1).symm z.2)
      ((tangentSpaceCastModel 𝓘(ℝ, ℝ) (ψ z.1 ((e z.1).symm z.2))).toContinuousLinearMap.comp
        (mfderiv 𝓙 𝓘(ℝ, ℝ) (ψ z.1) ((e z.1).symm z.2))))
    (hR hI : Ep × D → Source)
    (vfR vfI : (p : Ep) → (x : D) →
      normalSpace (I := 𝓙) (F p) ((e p).symm x))
    (hhR : ContDiffOn ℝ ∞ hR O) (hhI : ContDiffOn ℝ ∞ hI O)
    (hvfR : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfR z.1 z.2 : V)) O)
    (hvfI : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ (vfI z.1 z.2 : V)) O) :
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeSource (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm
        (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeSource (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm
        (fun x ↦ hI (z.1, x)) (vfI z.1) z.2) O ∧
    ContDiffOn ℝ ∞ (fun z : Ep × D ↦
      incrementsModeComplexInclude
        (incrementsModeSource (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm
          (fun x ↦ hR (z.1, x)) (vfR z.1) z.2) + Complex.I •
      incrementsModeComplexInclude
        (incrementsModeSource (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm
          (fun x ↦ hI (z.1, x)) (vfI z.1) z.2)) O := by
  obtain ⟨_, _, _, _, hRows, hJ, _, _, _, _, _⟩ :=
    incrementsJointActualGeometry_contDiffOn F hF e he ψ U O hO hFjoint hψjoint
      hcjoint hcoord hmap hU hinj hadapt hgood
  have hB : ContDiffOn ℝ ∞ (fun z : Ep × D ↦ fun i : Fin (m + 1) ↦
      (incrementsModeSecondForm (I := 𝓙) (F z.1) (hF z.1) (e z.1).symm z.2 0 i : V)) O :=
    contDiffOn_pi.mpr fun i ↦ hRows 0 i
  have hr := incrementsModeSource_joint_contDiffOn F hF (fun p ↦ (e p).symm)
    hR vfR O hB hJ hhR hvfR
  have hi := incrementsModeSource_joint_contDiffOn F hF (fun p ↦ (e p).symm)
    hI vfI O hB hJ hhI hvfI
  exact ⟨hr, hi, (incrementsModeComplexInclude.contDiff.comp_contDiffOn hr).add
    ((incrementsModeComplexInclude.contDiff.comp_contDiffOn hi).const_smul Complex.I)⟩

end ActualGeometry
end GlobalEmbedding.Paper
