import Probes.ActualSecondaryJointSource
import GlobalEmbedding.Paper.IncrementsModeSupportedChartPullback

/-!
# The actual secondary source and reconstruction preserve the forcing support

The original relative chart extension is reused literally. For the zero-free
secondary mode, its source support and source regularity obligations are now
derived from the two actual forcing channels. Thus a caller supplies only
the original forcing localization, not a support hypothesis on a computed
source, finite solution, reconstructed field or extension.
-/

noncomputable section
open Manifold Set Filter GlobalEmbedding.Paper
open scoped ContDiff Topology Classical

namespace GlobalEmbedding.Continuation

variable {E H M Ep : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  {m N : ℕ}

local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Source" => Fin (m + 1) → Fin (m + 1) → ℝ
local notation "Cdata" => Fin (m + 1) → ℂ

theorem actual_joint_zeroFree_source_contDiffOn
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : X → Source) (O : Set X)
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) O)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) O)
    (hh : ContDiffOn ℝ ∞ h O) :
    ContDiffOn ℝ ∞ (fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2) O := by
  let B := fun z : X => fun i =>
    (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)
  let J := fun z : X => (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
    (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)
  let T := incrementsModeTransverseSourceCLM (m := m)
  let L := incrementsModeForcingSourcePairing (m := m) (N := N)
  have hq := hJ.clm_apply (T.contDiff.comp_contDiffOn hh)
  have hp := (incrementsModeForcingSourceProjection (m := m)).contDiff.comp_contDiffOn hh
  have he : (fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2) =
      fun z => incrementsModeForcingSourceProjection (h z) - L (B z) (J z (T (h z))) := by
    funext z
    rw [incrementsModeSource_zeroFree_eq]
    rfl
  rw [he]
  exact hp.sub ((L.contDiff.comp_contDiffOn hBR).clm_apply hq)

/-- The secondary source depends on the value of the forcing at this point;
no derivative of the forcing or inverse regularity is needed for locality. -/
theorem actual_joint_zeroFree_source_eq_zero
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : X → Source) (z : X) (hh : h z = 0) :
    incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2 = 0 := by
  rw [incrementsModeSource_zeroFree_eq,
    incrementsModeTransverseSource_eq_selector]
  simp only [hh, map_zero, Submodule.coe_zero, sub_zero]

theorem actual_joint_zeroFree_source_tsupport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (h : X → Source) :
    tsupport (fun z : X => incrementsModeSource (F z.1) (hF z.1) (c z.1)
      (fun x => h (z.1, x)) (fun _ => 0) z.2) ⊆ tsupport h := by
  apply closure_minimal _ (isClosed_tsupport h)
  intro z hz
  by_contra hn
  exact hz (actual_joint_zeroFree_source_eq_zero F hF c h z
    (image_eq_zero_of_notMem_tsupport hn))

theorem actual_joint_zeroFree_complex_source_tsupport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) :
    tsupport (fun z : X => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
      Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)) ⊆
      tsupport hR ∪ tsupport hI := by
  apply closure_minimal _ ((isClosed_tsupport hR).union (isClosed_tsupport hI))
  intro z hz
  by_contra hn
  have hnr : z ∉ tsupport hR := fun h => hn (Or.inl h)
  have hni : z ∉ tsupport hI := fun h => hn (Or.inr h)
  apply hz
  change incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
    Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2) = 0
  rw [actual_joint_zeroFree_source_eq_zero F hF c hR z
      (image_eq_zero_of_notMem_tsupport hnr),
    actual_joint_zeroFree_source_eq_zero F hF c hI z
      (image_eq_zero_of_notMem_tsupport hni)]
  simp

/-- The same slice-wise finite polynomial preserves the JOINT source support.
This follows from actual spatial locality on each parameter slice; it does
not require differentiability of a totalized operator on arbitrary inputs. -/
theorem actual_joint_finite_mode_tsupport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (k : X → Cdata) (length : ℕ) (tau : ℝ) :
    tsupport (fun z : X => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1))
      (incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1))
      ((tau : ℂ) / Complex.I) length (fun x => k (z.1, x)) z.2) ⊆ tsupport k := by
  apply closure_minimal _ (isClosed_tsupport k)
  intro z hz
  by_contra hn
  have hslice : z.2 ∉ tsupport (fun x => k (z.1, x)) := by
    intro hx
    exact hn (tsupport_comp_subset_preimage k
      (f := fun x : D => (z.1, x)) (by fun_prop) hx)
  exact hz (image_eq_zero_of_notMem_tsupport fun h => hslice
    (increments_actual_mode_sum_tsupport _ _ _ _ _ h))

/-- The actual inhomogeneous zero-free reconstruction preserves the union
of the native JOINT supports of its actual source solution and forcing. -/
theorem actual_joint_zeroFree_reconstruction_tsupport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (u : X → D) (h : X → Source) :
    tsupport (fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (fun x => u (z.1, x)) (fun x => h (z.1, x)) (fun _ => 0) z.2) ⊆
        tsupport u ∪ tsupport h := by
  apply closure_minimal _ ((isClosed_tsupport u).union (isClosed_tsupport h))
  intro z hz
  by_contra hn
  have hsu : z.2 ∉ tsupport (fun x => u (z.1, x)) := by
    intro hx
    exact hn (Or.inl (tsupport_comp_subset_preimage u
      (f := fun x : D => (z.1, x)) (by fun_prop) hx))
  have hsh : z.2 ∉ tsupport (fun x => h (z.1, x)) := by
    intro hx
    exact hn (Or.inr (tsupport_comp_subset_preimage h
      (f := fun x : D => (z.1, x)) (by fun_prop) hx))
  apply hz
  apply image_eq_zero_of_notMem_tsupport
  intro hZ
  have hh := incrementsModeFullReconstruction_tsupport (F z.1) (hF z.1) (c z.1)
    (fun x => u (z.1, x)) (fun x => h (z.1, x)) (fun _ => 0) hZ
  rcases hh with hu | hh | hv
  · exact hsu hu
  · exact hsh hh
  · simpa using hv

/-- Both actual channels of the secondary mode inherit only the original
forcing support. The computed complex source and finite solution have no
independent localization assumption. -/
theorem actual_joint_secondary_channels_tsupport
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source) (length : ℕ) (tau : ℝ) :
    let source := fun z : X => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
      Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
    let U := fun p => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
      (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ) / Complex.I) length
      (fun x => source (p, x))
    let ZR := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeRealPart ∘ U z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2
    let ZI := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeImagPart ∘ U z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2
    tsupport ZR ⊆ tsupport hR ∪ tsupport hI ∧
      tsupport ZI ⊆ tsupport hR ∪ tsupport hI := by
  intro source U ZR ZI
  have hk := actual_joint_zeroFree_complex_source_tsupport F hF c hR hI
  have hu : tsupport (fun z : X => U z.1 z.2) ⊆ tsupport hR ∪ tsupport hI :=
    (actual_joint_finite_mode_tsupport F hF c source length tau).trans hk
  have hr : tsupport (incrementsModeRealPart ∘ fun z : X => U z.1 z.2) ⊆
      tsupport hR ∪ tsupport hI := (tsupport_comp_subset (map_zero _) _).trans hu
  have hi : tsupport (incrementsModeImagPart ∘ fun z : X => U z.1 z.2) ⊆
      tsupport hR ∪ tsupport hI := (tsupport_comp_subset (map_zero _) _).trans hu
  constructor
  · exact (actual_joint_zeroFree_reconstruction_tsupport F hF c
      (incrementsModeRealPart ∘ fun z : X => U z.1 z.2) hR).trans
      (Set.union_subset hr Set.subset_union_left)
  · exact (actual_joint_zeroFree_reconstruction_tsupport F hF c
      (incrementsModeImagPart ∘ fun z : X => U z.1 z.2) hI).trans
      (Set.union_subset hi Set.subset_union_right)

/-- The literal original supported secondary reconstruction, now from only
the two forcing supports. The same finite polynomial and the same two
inhomogeneous reconstructed fields occur in all extension identities. -/
theorem actual_secondary_supported_chart_pullback
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ, V) ∞ (F p))
    (c : Ep → D → M) (hR hI : X → Source)
    (length : ℕ) (tau : ℝ)
    (a : OpenPartialHomeomorph (Ep × M) X)
    (W : Set (Ep × M)) (hW : IsOpen W) (hsourceW : a.source ⊆ W)
    (K : Set (Ep × M)) (hK : IsClosed (Subtype.val ⁻¹' K : Set W))
    (hKsource : K ⊆ a.source)
    (hchart : ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, X) ∞ a a.source)
    (hinverse : ∀ z ∈ a.target, a.symm z = (z.1, c z.1 z.2))
    (hBR : ContDiffOn ℝ ∞ (fun z : X => fun i =>
      (incrementsModeSecondForm (F z.1) (hF z.1) (c z.1) z.2 0 i : V)) a.target)
    (hG : ContDiffOn ℝ ∞ (fun z : X =>
      freeGramRightInverse (fderiv ℝ (F z.1 ∘ c z.1) z.2)) a.target)
    (hJ : ContDiffOn ℝ ∞ (fun z : X =>
      (normalSpace (I := I) (F z.1) (c z.1 z.2)).subtypeL.comp
        (incrementsModeCoordinateJ (F z.1) (hF z.1) (c z.1) z.2)) a.target)
    (hT0 : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeTransverseValue (F z.1) (c z.1) z.2) a.target)
    (hA : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderA (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hB : ContDiffOn ℝ ∞ (fun z : X =>
      incrementsModeComplexFirstOrderB (F z.1) (hF z.1) (c z.1) z.2) a.target)
    (hhR : ContDiffOn ℝ ∞ hR a.target) (hhI : ContDiffOn ℝ ∞ hI a.target)
    (hinput : ∀ z ∈ a.target, z ∈ tsupport hR ∪ tsupport hI → a.symm z ∈ K) :
    let source := fun z : X => incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2) +
      Complex.I • incrementsModeComplexInclude
      (incrementsModeSource (F z.1) (hF z.1) (c z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2)
    let U := fun p => incrementsActualModeSum
      (incrementsModeComplexFirstOrderA (F p) (hF p) (c p))
      (incrementsModeComplexFirstOrderB (F p) (hF p) (c p)) ((tau : ℂ) / Complex.I) length
      (fun x => source (p, x))
    let ZR := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeRealPart ∘ U z.1) (fun x => hR (z.1, x)) (fun _ => 0) z.2
    let ZI := fun z : X => incrementsModeFullReconstruction (F z.1) (hF z.1) (c z.1)
      (incrementsModeImagPart ∘ U z.1) (fun x => hI (z.1, x)) (fun _ => 0) z.2
    let extR : Ep × M → V := fun y => if y ∈ a.source then ZR (a y) else 0
    let extI : Ep × M → V := fun y => if y ∈ a.source then ZI (a y) else 0
    ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extR W ∧
      ContMDiffOn ((𝓘(ℝ, Ep)).prod I) 𝓘(ℝ, V) ∞ extI W ∧
      tsupport (fun y : W => extR y) ⊆ Subtype.val ⁻¹' K ∧
      tsupport (fun y : W => extI y) ⊆ Subtype.val ⁻¹' K ∧
      (∀ y ∈ a.source, extR y = ZR (a y) ∧ extI y = ZI (a y)) ∧
      (∀ z ∈ a.target, extR (a.symm z) = ZR z ∧ extI (a.symm z) = ZI z) := by
  classical
  have hsr := actual_joint_zeroFree_source_contDiffOn F hF c hR a.target hBR hJ hhR
  have hsi := actual_joint_zeroFree_source_contDiffOn F hF c hI a.target hBR hJ hhI
  have hs := (incrementsModeComplexInclude.contDiff.comp_contDiffOn hsr).add
    ((incrementsModeComplexInclude.contDiff.comp_contDiffOn hsi).const_smul Complex.I)
  apply incrementsModeFullReconstruction_supported_chart_pullback F hF c hR hI
    (fun _ _ => 0) (fun _ _ => 0) length tau a W hW hsourceW K hK hKsource
    hchart hinverse hG hJ hT0 hA hB hhR hhI contDiffOn_const contDiffOn_const hs
  intro z hz hloc
  apply hinput z hz
  rcases hloc with hloc | hloc | hloc | hloc | hloc
  · exact actual_joint_zeroFree_complex_source_tsupport F hF c hR hI hloc
  · exact Or.inl hloc
  · exact Or.inr hloc
  · have hf : False := by simpa using hloc
    exact hf.elim
  · have hf : False := by simpa using hloc
    exact hf.elim

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_joint_zeroFree_source_tsupport
#print axioms GlobalEmbedding.Continuation.actual_joint_zeroFree_complex_source_tsupport
#print axioms GlobalEmbedding.Continuation.actual_joint_finite_mode_tsupport
#print axioms GlobalEmbedding.Continuation.actual_joint_secondary_channels_tsupport
#print axioms GlobalEmbedding.Continuation.actual_secondary_supported_chart_pullback
