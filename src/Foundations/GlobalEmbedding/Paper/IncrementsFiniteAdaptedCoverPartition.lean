import GlobalEmbedding.Paper.IncrementsLocalAdaptedPhaseCoordinates
import GlobalEmbedding.Paper.IncrementsManifoldAdaptedPhaseCoordinates
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Support

/-!
# Qualitative closed-caller finite joint adapted cover and ordinary partition

Source: main.tex594–609,617–650, lem:increments; revised proof806–810.
DAG: increments-finite-adapted-cover-partition. Exclusive worker W5.
Stage2 only: ONE named proof hole, pending ROOT exact header/doc lock.
No generic partition/IFT/support framework or quantitative uniformity claim.
-/

noncomputable section
open Manifold Set
open scoped ContDiff
namespace GlobalEmbedding.Paper

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [FiniteDimensional ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m + 1))
local notation "𝓙" => 𝓘(ℝ, D)
local notation "𝓙X" => ModelWithCorners.prod 𝓘(ℝ, Ep) 𝓙
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ M]
  [T2Space M] [CompactSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- From INTERNAL actual local adapted-chart outputs on the original compact
active observation, obtain a finite actual joint adapted family and an ordinary
smooth partition equal to one NEAR ALL activity on a genuinely shrunken open
parameter neighborhood. Compact Hausdorff M is explicit for this closed-caller
helper ONLY; Ep is finite-dimensional, not assumed compact. Relative support is
literally the native tsupport in the ORIGINAL parameter-open subtype W.

Source: original adapted localizations/support and finite auxiliary parameters,
main.tex594–609,617–650, lem:increments; revised proof806–810. The INTERNAL
per-point witness must ultimately come from the canonical original-manifold
phase producer and genuine noncriticality conversion, not an extra original
final-target hypothesis. No desired finite cover, partition, U/Z or bound is
input. The actual original parent O is open and contains the relative support.

Natural-language proof, pending ROOT exact lock: derive SigmaCompactSpace of
Ep times M from native finite-dimensional Ep and compact M. Relative cutoff
support A is closed in W; its observation C in the compact K times M is compact
because K is contained in the original parameter open. Choose the supplied
actual chart at each point of C, preserving the SAME parameter, literal phase,
original parent and bothway joint smoothness. Native compact finite subcover
selects finitely many of THESE actual charts. Native exists_compact_between
gives a compact closed buffer L with C inside interior L and L inside their
open union. Native SmoothPartitionOfUnity.exists_isSubordinate, indexed by that
finite family, gives ordinary nonnegative smooth rho with native tsupport
inside the actual chart sources and ordinary sum one on interior L. The open
set interior L union (W minus A) contains K times M. Native generalized tube
lemma yields an open parameter neighborhood Lambda' of K, intersected with the
original Lambda, on which EVERY active point is in interior L. Native support
of scalar multiplication on the W subtype retains any original input support
B and the chart source, hence primary supports and secondary pair intersections.
At active points the ordinary partition sums to one; outside relative support
an input supported in A is zero. Finite sum_smul therefore recovers each SAME
source or free amplitude on Lambda' times M. Reconstructed amplitudes must be
summed with their SAME phase BEFORE quadratic extraction; this is not a square
partition and does not discard cross terms or partition-derivative errors.

C empty permits an empty family/Fin0 and empty buffer; K empty or M empty adds
no Nonempty premise. Never infer an inactive germ merely from cutoff value zero.
No CompactP, whole-parameter input smoothness, parameter-boundary vanishing,
output cutoff, partition jets, uniform pieces-per-original-chart R, profile,
threshold or full increments conclusion is asserted. Generic F is only an
original source/free-amplitude value space, not a new geometric carrier. -/
theorem increments_exists_finite_adapted_cover_partition
    (Λ : Set Ep) (_hΛ : IsOpen Λ) (K : Set Ep) (_hK : IsCompact K) (_hKΛ : K ⊆ Λ)
    (χ ψ : Ep × M → ℝ) (O : Set (Ep × M)) (_hO : IsOpen O) :
    let W : Set (Ep × M) := Λ ×ˢ univ
    let A : Set (Ep × M) := Subtype.val '' tsupport (fun z : W ↦ χ z.val)
    A ⊆ O →
    (∀ z ∈ A ∩ (K ×ˢ univ),
      ∃ a : OpenPartialHomeomorph (Ep × M) (Ep × D),
        z ∈ a.source ∧ a.source ⊆ W ∩ O ∧
        ContMDiffOn 𝓙X 𝓘(ℝ, Ep × D) ∞ a a.source ∧
        ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙X ∞ a.symm a.target ∧
        (∀ y ∈ a.source, (a y).1 = y.1 ∧ (a y).2 0 = ψ y) ∧
        (∀ y ∈ a.target, (a.symm y).1 = y.1 ∧ ψ (a.symm y) = y.2 0)) →
    ∃ (r : ℕ) (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
        (L : Set (Ep × M)) (ρ : SmoothPartitionOfUnity (Fin r) 𝓙X (Ep × M) L)
        (Λ' : Set Ep),
      IsCompact L ∧ IsClosed L ∧ A ∩ (K ×ˢ univ) ⊆ interior L ∧
      L ⊆ ⋃ i, (a i).source ∧
      (∀ i, ∃ z ∈ A ∩ (K ×ˢ univ), z ∈ (a i).source) ∧
      (∀ i, (a i).source ⊆ W ∩ O ∧
        ContMDiffOn 𝓙X 𝓘(ℝ, Ep × D) ∞ (a i) (a i).source ∧
        ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙X ∞ (a i).symm (a i).target ∧
        (∀ y ∈ (a i).source, ((a i) y).1 = y.1 ∧ ((a i) y).2 0 = ψ y) ∧
        (∀ y ∈ (a i).target,
          ((a i).symm y).1 = y.1 ∧ ψ ((a i).symm y) = y.2 0)) ∧
      ρ.IsSubordinate (fun i ↦ (a i).source) ∧
      (∀ y ∈ interior L, ∑ i : Fin r, ρ i y = 1) ∧
      IsOpen Λ' ∧ K ⊆ Λ' ∧ Λ' ⊆ Λ ∧ A ∩ (Λ' ×ˢ univ) ⊆ interior L ∧
      (∀ (i : Fin r) (h : Ep × M → F) (B : Set (Ep × M)),
        tsupport (fun z : W ↦ h z.val) ⊆ Subtype.val ⁻¹' B →
        tsupport (fun z : W ↦ ρ i z.val • h z.val) ⊆
          Subtype.val ⁻¹' (B ∩ (a i).source)) ∧
      (∀ h : Ep × M → F,
        tsupport (fun z : W ↦ h z.val) ⊆ Subtype.val ⁻¹' A →
        ∀ y ∈ Λ' ×ˢ (univ : Set M), ∑ i : Fin r, ρ i y • h y = h y) := by
  classical
  dsimp only
  intro _hparent hlocal
  let W : Set (Ep × M) := Λ ×ˢ univ
  let A : Set (Ep × M) := Subtype.val '' tsupport (fun z : W ↦ χ z.val)
  let C : Set (Ep × M) := A ∩ (K ×ˢ univ)
  have hW : IsOpen W := _hΛ.prod isOpen_univ
  have hdiff : W \ A = Subtype.val '' (tsupport (fun z : W ↦ χ z.val))ᶜ := by
    ext z
    constructor
    · rintro ⟨hzW, hzA⟩
      refine ⟨⟨z, hzW⟩, ?_, rfl⟩
      intro hz
      exact hzA ⟨⟨z, hzW⟩, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      rintro ⟨y, hy, heq⟩
      have hyz : y = z := Subtype.ext heq
      exact hz (hyz ▸ hy)
  have hdiffOpen : IsOpen (W \ A) := by
    rw [hdiff]
    exact hW.isOpenMap_subtype_val _ (isClosed_tsupport _).isOpen_compl
  have hCeq : C = (K ×ˢ (univ : Set M)) \ (W \ A) := by
    ext z
    constructor
    · rintro ⟨hzA, hzK⟩
      exact ⟨hzK, fun hz ↦ hz.2 hzA⟩
    · rintro ⟨hzK, hz⟩
      have hzW : z ∈ W := ⟨_hKΛ hzK.1, hzK.2⟩
      exact ⟨by_contra fun hn ↦ hz ⟨hzW, hn⟩, hzK⟩
  have hC : IsCompact C := by
    rw [hCeq]
    exact (_hK.prod isCompact_univ).diff hdiffOpen
  let b : C → OpenPartialHomeomorph (Ep × M) (Ep × D) :=
    fun z ↦ Classical.choose (hlocal z z.property)
  have hb (z : C) :
      z.val ∈ (b z).source ∧ (b z).source ⊆ W ∩ O ∧
      ContMDiffOn 𝓙X 𝓘(ℝ, Ep × D) ∞ (b z) (b z).source ∧
      ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙X ∞ (b z).symm (b z).target ∧
      (∀ y ∈ (b z).source, ((b z) y).1 = y.1 ∧ ((b z) y).2 0 = ψ y) ∧
      (∀ y ∈ (b z).target,
        ((b z).symm y).1 = y.1 ∧ ψ ((b z).symm y) = y.2 0) :=
    Classical.choose_spec (hlocal z z.property)
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover (fun z : C ↦ (b z).source)
    (fun z ↦ (b z).open_source) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, (hb ⟨z, hz⟩).1⟩)
  let e : Fin s.card ≃ s := s.equivFin.symm
  let a : Fin s.card → OpenPartialHomeomorph (Ep × M) (Ep × D) :=
    fun i ↦ b (e i).val
  have hcover : C ⊆ ⋃ i, (a i).source := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
    refine mem_iUnion.mpr ⟨s.equivFin ⟨w, hw⟩, ?_⟩
    simpa [a, e] using hzw
  have hopen : IsOpen (⋃ i, (a i).source) := isOpen_iUnion fun i ↦ (a i).open_source
  obtain ⟨L, hL, hCL, hLU⟩ := exists_compact_between hC hopen hcover
  have : SigmaCompactSpace Ep := inferInstance
  have : SigmaCompactSpace (Ep × M) := inferInstance
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓙X)
    hL.isClosed (fun i ↦ (a i).source) (fun i ↦ (a i).open_source) hLU
  have hsum (y : Ep × M) (hy : y ∈ interior L) : ∑ i : Fin s.card, ρ i y = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (interior_subset hy)
  have hfull : K ×ˢ (univ : Set M) ⊆ interior L ∪ (W \ A) := by
    intro y hy
    by_cases hyA : y ∈ A
    · exact Or.inl (hCL ⟨hyA, hy⟩)
    · exact Or.inr ⟨⟨_hKΛ hy.1, hy.2⟩, hyA⟩
  obtain ⟨u, v, hu, _hv, hKu, hMv, huv⟩ := generalized_tube_lemma _hK
    (isCompact_univ : IsCompact (univ : Set M)) (isOpen_interior.union hdiffOpen) hfull
  have hall : A ∩ ((u ∩ Λ) ×ˢ univ) ⊆ interior L := by
    intro y hy
    have ht := huv ⟨hy.2.1.1, hMv hy.2.2⟩
    exact ht.resolve_right (fun hn ↦ hn.2 hy.1)
  refine ⟨s.card, a, L, ρ, u ∩ Λ, hL, hL.isClosed, hCL, hLU, ?_, ?_, hρ,
    hsum, hu.inter _hΛ, (fun p hp ↦ ⟨hKu hp, _hKΛ hp⟩), inter_subset_right, hall,
    ?_, ?_⟩
  · intro i
    exact ⟨(e i).val.val, (e i).val.property, (hb (e i).val).1⟩
  · intro i
    exact (hb (e i).val).2
  · intro i h B hB z hz
    have hright := tsupport_smul_subset_right
      (fun z : W ↦ ρ i z.val) (fun z : W ↦ h z.val)
    have hleft := tsupport_smul_subset_left
      (fun z : W ↦ ρ i z.val) (fun z : W ↦ h z.val)
    have hpre := tsupport_comp_subset_preimage (fun y : Ep × M ↦ ρ i y)
      (continuous_subtype_val : Continuous (Subtype.val : W → Ep × M))
    exact ⟨hB (hright hz), hρ i (hpre (hleft hz))⟩
  · intro h hA y hy
    by_cases hyA : y ∈ A
    · rw [← Finset.sum_smul, hsum y (hall ⟨hyA, hy⟩), one_smul]
    · have hyW : y ∈ W := ⟨hy.1.2, hy.2⟩
      have hnot : (⟨y, hyW⟩ : W) ∉ tsupport (fun z : W ↦ h z.val) := by
        intro ht
        exact hyA (hA ht)
      have hzero : h y = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun z : W ↦ h z.val) (x := ⟨y, hyW⟩) hnot
      simp [hzero]

#print axioms increments_exists_finite_adapted_cover_partition

/-- ORIGINAL joint phase and spatial noncriticality give an actual finite
adapted family and ordinary partition, with NO opaque local-chart hypothesis.
The original cutoff support is native relative tsupport in W=Lambda times M;
original smoothness is required ONLY on W intersect the original parent O.
Compact Hausdorff M is explicit for this closed-caller helper, not a new
standalone increments hypothesis; the parameter Ep is never assumed compact.

Source: adapted source/free-amplitude localizations and finite auxiliary
parameters, main.tex594–609,617–650, lem:increments; revised proof806–810.

Natural-language proof, pending ROOT exact lock of THIS appended endpoint:
apply the existing qualitative finite-cover/ordinary-partition theorem ONCE
with the original Lambda,K,chi,psi and parent O. At each actual active base
z in relative cutoff support over K, native support membership gives z in W;
original support subordination gives z in O. Thus z lies in the genuine open
W intersect O. The original phase is jointly smooth on that intersection and
its original spatial mfderiv is nonzero at z. Invoke canonical W2
increments_exists_manifold_local_adapted_phase_coordinates_of_mfderiv_ne_zero
ONCE at this base on that SAME open intersection, using psi(p,x) literally.
Its output supplies the actual local adapted-chart witness, source in W
intersect O, actual joint smoothness of both directions and exact parameter/
phase/inverse identities required by the existing qualitative cover theorem.
Return that theorem's SAME finite family, compact buffer, ordinary partition,
genuine shrunken parameter-open neighborhood covering ALL relative activity,
original input-support intersections and SAME-input sum recovery. No IFT,
finite subcover, partition, tube or support proof is repeated; the previously
published qualitative theorem's header, doc and body remain unchanged.

Empty active observation, K or M retains the original empty-family cases;
no phase witness is assumed at an inactive point. Secondary pair supports
are retained by the existing arbitrary-input support B conclusion and actual
same-phase summation precedes quadratic extraction. No desired finite cover,
partition, solution, coordinate noncriticality, cutoff positivity/division,
global phase extension, boundary vanishing, CompactP or extra SigmaCompact
hypothesis is added. Uniform pieces-per-original-chart R, partition jets,
conditioning/profile/threshold and full increments remain separate duties. -/
theorem increments_exists_finite_adapted_cover_partition_of_mfderiv_ne_zero
    (Λ : Set Ep) (_hΛ : IsOpen Λ) (K : Set Ep) (_hK : IsCompact K) (_hKΛ : K ⊆ Λ)
    (χ ψ : Ep × M → ℝ) (O : Set (Ep × M)) (_hO : IsOpen O) :
    let W : Set (Ep × M) := Λ ×ˢ univ
    let A : Set (Ep × M) := Subtype.val '' tsupport (fun z : W ↦ χ z.val)
    A ⊆ O →
    ContMDiffOn 𝓙X 𝓘(ℝ, ℝ) ∞ ψ (W ∩ O) →
    (∀ z ∈ A ∩ (K ×ˢ univ),
      mfderiv 𝓙 𝓘(ℝ, ℝ) (fun x : M ↦ ψ (z.1, x)) z.2 ≠ 0) →
    ∃ (r : ℕ) (a : Fin r → OpenPartialHomeomorph (Ep × M) (Ep × D))
        (L : Set (Ep × M)) (ρ : SmoothPartitionOfUnity (Fin r) 𝓙X (Ep × M) L)
        (Λ' : Set Ep),
      IsCompact L ∧ IsClosed L ∧ A ∩ (K ×ˢ univ) ⊆ interior L ∧
      L ⊆ ⋃ i, (a i).source ∧
      (∀ i, ∃ z ∈ A ∩ (K ×ˢ univ), z ∈ (a i).source) ∧
      (∀ i, (a i).source ⊆ W ∩ O ∧
        ContMDiffOn 𝓙X 𝓘(ℝ, Ep × D) ∞ (a i) (a i).source ∧
        ContMDiffOn 𝓘(ℝ, Ep × D) 𝓙X ∞ (a i).symm (a i).target ∧
        (∀ y ∈ (a i).source, ((a i) y).1 = y.1 ∧ ((a i) y).2 0 = ψ y) ∧
        (∀ y ∈ (a i).target,
          ((a i).symm y).1 = y.1 ∧ ψ ((a i).symm y) = y.2 0)) ∧
      ρ.IsSubordinate (fun i ↦ (a i).source) ∧
      (∀ y ∈ interior L, ∑ i : Fin r, ρ i y = 1) ∧
      IsOpen Λ' ∧ K ⊆ Λ' ∧ Λ' ⊆ Λ ∧ A ∩ (Λ' ×ˢ univ) ⊆ interior L ∧
      (∀ (i : Fin r) (h : Ep × M → F) (B : Set (Ep × M)),
        tsupport (fun z : W ↦ h z.val) ⊆ Subtype.val ⁻¹' B →
        tsupport (fun z : W ↦ ρ i z.val • h z.val) ⊆
          Subtype.val ⁻¹' (B ∩ (a i).source)) ∧
      (∀ h : Ep × M → F,
        tsupport (fun z : W ↦ h z.val) ⊆ Subtype.val ⁻¹' A →
        ∀ y ∈ Λ' ×ˢ (univ : Set M), ∑ i : Fin r, ρ i y • h y = h y) := by
  dsimp only
  intro hparent hψ hcritical
  refine increments_exists_finite_adapted_cover_partition (F := F)
    Λ _hΛ K _hK _hKΛ χ ψ O _hO hparent ?_
  intro z hz
  have hzW : z ∈ Λ ×ˢ (univ : Set M) := by
    obtain ⟨w, _hw, rfl⟩ := hz.1
    exact w.property
  exact increments_exists_manifold_local_adapted_phase_coordinates_of_mfderiv_ne_zero
    (fun p x ↦ ψ (p, x)) ((Λ ×ˢ univ) ∩ O) ((_hΛ.prod isOpen_univ).inter _hO)
    z ⟨hzW, hparent hz.1⟩ hψ (hcritical z hz)

#print axioms increments_exists_finite_adapted_cover_partition_of_mfderiv_ne_zero

end GlobalEmbedding.Paper
