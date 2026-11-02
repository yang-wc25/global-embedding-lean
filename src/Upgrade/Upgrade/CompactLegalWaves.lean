import Upgrade.ProbeInterface
import Upgrade.RankQActualSecondForm
import Mathlib.Topology.Compactness.Compact

/-!
# One actual wave list from the local packets

The packets are selected before any probe weights or small scales.  Their
literal `LocalLegalWave` entries, including phase, normal field and cutoff,
survive the finite concatenation without a change.  The two copies needed by
the rank-q argument are distinct labels even though they carry the same wave.
This file does not assert persistence of an incidence derivative.
-/

noncomputable section
open Bundle Filter Manifold Set GlobalEmbedding.Paper
open scoped Topology ContDiff BigOperators

namespace GlobalEmbedding.Upgrade

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The literal original normal block of a fixed finite actual wave packet.
No weights, oscillatory coefficients, or perturbed map enter this definition. -/
def rankQWaveNormalBlock
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (x : M) (waves : Fin n → LocalLegalWave F hF) :
    (Fin n → ℝ) →
      ((rankQActualReference F hF x).ker →L[ℝ] (rankQActualReference F hF x).rangeᗮ) :=
  let B := rankQActualReference F hF x
  fun t ↦ B.rangeᗮ.orthogonalProjectionOnto.comp
    ((B + (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
      (∑ i, t i • (waves i).tensor x)).comp B.ker.subtypeL)

/-- A packet is fixed before calling probes.  Its onto derivative is exactly
the already accepted finite local-wave conclusion, expressed on the same
actual kernel and perpendicular range. -/
structure RankQLocalWavePacket
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F) (x y : M) where
  waves : Fin n → LocalLegalWave F hF
  center_eq : ∀ i, (waves i).center = x
  away : ∀ i, y ∉ tsupport ((waves i).cutoff : M → ℝ)
  one_near : ∀ᶠ z in 𝓝 x, ∀ i, (waves i).cutoff z = 1
  zero_near : ∀ᶠ z in 𝓝 y, ∀ i, (waves i).cutoff z = 0
  normalBlock_differentiable : DifferentiableAt ℝ (rankQWaveNormalBlock F hF x waves) 0
  normalBlock_onto : Function.Surjective (fderiv ℝ (rankQWaveNormalBlock F hF x waves) 0)

/-- Convert the accepted actual packet into the probe input type, retaining
the original onto response.  This is an interface conversion, not a new local
wave construction or a second proof of its rank classification. -/
theorem exists_rankQ_localLegalWave_packet [T2Space M]
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (hphase : PhaseRegular F hF) (hn : 3 ≤ n)
    (hN : N = n * (n + 1) / 2 + 1)
    (x y : M) (hxy : x ≠ y)
    (hrank : Module.finrank ℝ (trueSecondForm F hF x).range = n * (n - 1) / 2) :
    Nonempty (RankQLocalWavePacket F hF x y) := by
  classical
  have hp := upgradeRankQ_exists_finite_local_legal_waves
    F hF himm hphase hn hN x y hxy hrank
  obtain ⟨xi, nu, U, psi, v, chi, hfields, hone, hzero, hcol, hglob, hsglob,
    hdiff, honto⟩ := hp
  let waves : Fin n → LocalLegalWave F hF := fun i ↦ {
    center := x
    domain := U i
    phase := psi i
    normal := v i
    cutoff := chi i
    domain_open := (hfields i).2.2.1
    center_mem := (hfields i).2.2.2.1
    domain_chart := (hfields i).2.2.2.2.1
    support_subset := (hfields i).2.2.2.2.2.1
    phase_smooth := (hfields i).2.2.2.2.2.2.2.1
    normal_smooth := (hfields i).2.2.2.2.2.2.2.2.2.2.1
    legal := (hfields i).2.2.2.2.2.2.2.2.2.2.2 }
  have hsum (t : Fin n → ℝ) :
      (∑ i, t i • (waves i).tensor x) =
        LinearMap.toContinuousLinearMap
          (show SymmetricSquare E →ₗ[ℝ] V from
            ∑ i, t i • (chi i x • supportedRankLegalVariation
              (mfderiv IM 𝓘(ℝ, ℝ) (psi i) x).toLinearMap (v i x : V))) := by
    let A : Fin n → SymmetricSquare E →ₗ[ℝ] V := fun i ↦
      chi i x • supportedRankLegalVariation
        (mfderiv IM 𝓘(ℝ, ℝ) (psi i) x).toLinearMap (v i x : V)
    let e : (SymmetricSquare E →ₗ[ℝ] V) ≃ₗ[ℝ] (SymmetricSquare E →L[ℝ] V) :=
      LinearMap.toContinuousLinearMap
    change (∑ i, t i • e (A i)) = e (∑ i, t i • A i)
    simp only [map_sum, map_smul]
  have hblock : rankQWaveNormalBlock F hF x waves =
      (fun t ↦
        (rankQActualReference F hF x).rangeᗮ.orthogonalProjectionOnto.comp
          (((rankQActualReference F hF x) +
            (normalSpace (I := IM) F x).orthogonalProjectionOnto.comp
              (LinearMap.toContinuousLinearMap
                (show SymmetricSquare E →ₗ[ℝ] V from
                  ∑ i, t i • (chi i x • supportedRankLegalVariation
                    (mfderiv IM 𝓘(ℝ, ℝ) (psi i) x).toLinearMap (v i x : V))))).comp
            (rankQActualReference F hF x).ker.subtypeL)) := by
    funext t
    dsimp only [rankQWaveNormalBlock]
    rw [hsum]
    apply ContinuousLinearMap.ext
    intro s
    rfl
  refine ⟨{
    waves := waves
    center_eq := fun _ ↦ rfl
    away := fun i ↦ (hfields i).2.2.2.2.2.2.1
    one_near := hone
    zero_near := hzero
    normalBlock_differentiable := ?_
    normalBlock_onto := ?_ }⟩
  · rw [hblock]
    exact hdiff
  · rw [hblock]
    exact honto

/-- The same packet has an actual open pair neighborhood on which every first
cutoff is one and every second cutoff is zero.  It includes cross-component
pairs without selecting paths or orientations. -/
theorem RankQLocalWavePacket.exists_pair_neighborhood
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F} {x y : M}
    (p : RankQLocalWavePacket F hF x y) :
    ∃ O : Set (M × M), IsOpen O ∧ (x, y) ∈ O ∧
      ∀ z ∈ O, ∀ i, (p.waves i).cutoff z.1 = 1 ∧ (p.waves i).cutoff z.2 = 0 := by
  obtain ⟨U, hUsub, hU, hx⟩ := mem_nhds_iff.mp p.one_near
  obtain ⟨W, hWsub, hW, hy⟩ := mem_nhds_iff.mp p.zero_near
  exact ⟨U ×ˢ W, hU.prod hW, ⟨hx, hy⟩,
    fun z hz i ↦ ⟨hUsub hz.1 i, hWsub hz.2 i⟩⟩

/-- A compact cover of already chosen actual local packets yields one finite
list.  Every packet label is retained by an equivalence, so repeated entries
remain distinct probe parameters.  In the rank-q application take
`ι = Fin n × Fin 2` and `localWaves c (i,j) = packet c i`.

The cover may be shrunk using the actual Schur/supported incidence calculation
before this theorem is called.  No rank or avoidance conclusion is hidden in
the finite selection. Empty compact sets produce an empty list. -/
theorem finite_actual_localLegalWave_list
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {F : M → V} {hF : ContMDiff IM 𝓘(ℝ, V) ∞ F}
    {K : Set X} (hK : IsCompact K)
    (localWaves : K → ι → LocalLegalWave F hF)
    (O : K → Set X) (hO : ∀ c, IsOpen (O c)) (hcO : ∀ c, c.1 ∈ O c) :
    ∃ centers : Finset K, ∃ r : ℕ, ∃ waves : Fin r → LocalLegalWave F hF,
      ∃ labels : (centers × ι) ≃ Fin r,
        (∀ c : centers, ∀ i, waves (labels (c, i)) = localWaves c.1 i) ∧
        (∀ x ∈ K, ∃ c ∈ centers, x ∈ O c) := by
  classical
  obtain ⟨centers, hcover⟩ := hK.elim_finite_subcover O hO (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hcO ⟨x, hx⟩⟩)
  let labels := Fintype.equivFin (centers × ι)
  let waves := fun j : Fin (Fintype.card (centers × ι)) ↦
    localWaves (labels.symm j).1.1 (labels.symm j).2
  refine ⟨centers, Fintype.card (centers × ι), waves, labels, ?_, ?_⟩
  · intro c i
    simp only [waves, labels.symm_apply_apply]
  · intro x hx
    simpa only [mem_iUnion, exists_prop] using hcover hx

end GlobalEmbedding.Upgrade
