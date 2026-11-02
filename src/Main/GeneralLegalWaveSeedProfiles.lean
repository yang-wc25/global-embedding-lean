import Main.GeneralLegalWaveRefinement
import NormalPolar.JointSecondarySignedSeed
import GlobalEmbedding.Paper.GoodCovectorRescaling

/-!
# One actual general-cutoff seed and its primitive profiles

The signed-seed factory is generic in a Good phase and its closed carrier.
Here it is applied to the actual weighted original phase and cutoff support.
Its single chosen refinement is used for every piece, compact buffer,
geometry sample and primitive profile. Piece indices do not become new
probe labels or acquire new weights.
-/

noncomputable section
open Set Function Filter Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical

namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]

local notation "Z" => EuclideanSpace ℝ (Fin 0)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Z × D

abbrev GeneralLegalWaveSeed (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) :=
  JointSecondarySignedSeed (Ep := Z) F hF (fun x => weight * w.phase x)
    (tsupport w.cutoff) w.domain

/-- The actual seed is produced from the original immersion and wave.
There is no raw geometry or reconstructed response premise. -/
theorem exists_generalLegalWaveSeed
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (w : OpenSupportedLegalWave (n := m+1) F hF) (weight : ℝ) (hw : 0 < weight) :
    Nonempty (GeneralLegalWaveSeed F hF w weight) := by
  apply jointSecondary_exists_signed_seed F hF hImm (fun x => weight * w.phase x)
    (tsupport w.cutoff) w.domain (isClosed_tsupport _) w.domain_open w.support_subset
    (contMDiffOn_const.mul w.phase_smooth)
  intro x hx
  have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hx)).mdifferentiableAt
    (by simp)
  have he : mfderiv IM 𝓘(ℝ,ℝ) (fun y => weight * w.phase y) x =
      weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase x :=
    (hd.hasMFDerivAt.const_smul weight).mfderiv
  rw [he]
  exact (good_covector_smul_iff F hF x _ weight hw.ne').mpr (w.legal x hx).1

namespace GeneralLegalWaveSeed

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : OpenSupportedLegalWave (n := m+1) F hF} {weight : ℝ}

def pieceCutoff (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) (x : M) : ℝ :=
  d.refinement.cutoff i x * w.cutoff x

theorem pieceCutoff_smooth (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : ContMDiff IM 𝓘(ℝ,ℝ) ∞ (d.pieceCutoff i) :=
  (d.refinement.cutoff_smooth i).mul w.cutoff_smooth

theorem pieceCutoff_support (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    tsupport (d.pieceCutoff i) ⊆ tsupport (d.refinement.cutoff i) ∩ tsupport w.cutoff := by
  intro x hx
  exact ⟨tsupport_smul_subset_left (d.refinement.cutoff i) w.cutoff hx,
    tsupport_smul_subset_right (d.refinement.cutoff i) w.cutoff hx⟩

theorem sum_pieceCutoff (d : GeneralLegalWaveSeed F hF w weight) (x : M) :
    ∑ i, d.pieceCutoff i x = w.cutoff x := by
  by_cases hx : x ∈ tsupport w.cutoff
  · simp only [pieceCutoff,← Finset.sum_mul]
    rw [d.refinement.partition x hx,one_mul]
  · simp only [pieceCutoff,image_eq_zero_of_notMem_tsupport hx,mul_zero,Finset.sum_const_zero]

theorem sum_value (d : GeneralLegalWaveSeed F hF w weight) (x : M) :
    ∑ i, d.pieceCutoff i x • (w.normal x : V) = w.value x := by
  rw [← Finset.sum_smul,d.sum_pieceCutoff]
  rfl

def cutoffCoordinates (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : X → ℝ :=
  fun z => d.pieceCutoff i ((d.outer i).chart.symm z.2)

def normalCoordinates (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : X → V :=
  fun z => (w.normal ((d.outer i).chart.symm z.2) : V)

def physicalChart (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : OpenPartialHomeomorph (Z × M) X :=
  (OpenPartialHomeomorph.refl Z).prod (d.inner i).chart

def carrier (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : Set (Z × M) :=
  univ ×ˢ (tsupport (d.refinement.cutoff i) ∩ tsupport w.cutoff)

theorem cutoff_spatial_smooth (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    ContDiffOn ℝ ∞ (fun y : D => d.pieceCutoff i ((d.outer i).chart.symm y))
      (d.outer i).chart.target :=
  ((d.pieceCutoff_smooth i).comp_contMDiffOn
    (contMDiffOn_symm_of_mem_maximalAtlas (d.outer i).maximal)).contDiffOn

theorem normal_spatial_smooth (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    ContDiffOn ℝ ∞ (fun y : D => (w.normal ((d.outer i).chart.symm y) : V))
      (d.outer i).chart.target :=
  (w.normal_smooth.comp
    (contMDiffOn_symm_of_mem_maximalAtlas (d.outer i).maximal)
    (fun y hy => (d.outer i).source_domain ((d.outer i).chart.map_target hy))).contDiffOn

theorem inner_target_subset_outer (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    (d.inner i).chart.target ⊆ (d.outer i).chart.target := by
  rw [(d.inner i).chart_target,(d.outer i).chart_target]
  exact interior_subset.trans (d.nested i)

theorem cutoffCoordinates_smooth (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    ContDiffOn ℝ ∞ (d.cutoffCoordinates i) (d.physicalChart i).target := by
  exact (d.cutoff_spatial_smooth i).comp contDiffOn_snd
    (fun z hz => d.inner_target_subset_outer i hz.2)

theorem normalCoordinates_smooth (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    ContDiffOn ℝ ∞ (d.normalCoordinates i) (d.physicalChart i).target := by
  exact (d.normal_spatial_smooth i).comp contDiffOn_snd
    (fun z hz => d.inner_target_subset_outer i hz.2)

theorem cutoffCoordinates_support (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) (z : X) (hz : z ∈ (d.physicalChart i).target)
    (hcut : z ∈ tsupport (d.cutoffCoordinates i)) :
    (d.physicalChart i).symm z ∈ d.carrier i := by
  have hsp : (d.outer i).chart.symm z.2 ∈ tsupport (d.pieceCutoff i) := by
    by_contra hn
    have hc : ContinuousAt (fun y : X => (d.outer i).chart.symm y.2) z :=
      ((d.outer i).chart.symm.continuousAt (d.inner_target_subset_outer i hz.2)).comp
        continuousAt_snd
    have heq := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hc
    exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hcut
  exact ⟨mem_univ _,d.pieceCutoff_support i hsp⟩

/-- Both actual primitive profile functions have all-order bounds on the
whole inner target. Their constants are fixed before any scale or order. -/
theorem exists_primitive_profiles (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) :
    ∃ Cchi Cnu : ℕ → ℝ, (∀ n, 0 < Cchi n ∧ 0 < Cnu n) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ n k, k ≤ n → ∀ z : X,
      z ∈ (d.physicalChart i).target →
        ell^k * ‖iteratedFDeriv ℝ k (d.cutoffCoordinates i) z‖ ≤ Cchi n ∧
        ell^k * ‖iteratedFDeriv ℝ k (d.normalCoordinates i) z‖ ≤ Cnu n := by
  have hnested : (d.inner i).compactTarget ⊆ (d.outer i).chart.target := by
    rw [(d.outer i).chart_target]
    exact d.nested i
  obtain ⟨Cchi,hCchi,hchi⟩ := (d.inner i).exists_passive_prefix_profile (Ep := Z)
    (d.outer i).chart.target (d.outer i).chart.open_target hnested
    (fun y : D => d.pieceCutoff i ((d.outer i).chart.symm y)) (d.cutoff_spatial_smooth i)
  obtain ⟨Cnu,hCnu,hnu⟩ := (d.inner i).exists_passive_prefix_profile (Ep := Z)
    (d.outer i).chart.target (d.outer i).chart.open_target hnested
    (fun y : D => (w.normal ((d.outer i).chart.symm y) : V)) (d.normal_spatial_smooth i)
  refine ⟨Cchi,Cnu,fun n => ⟨hCchi n,hCnu n⟩,?_⟩
  intro ell he he1 n k hk z hz
  exact ⟨hchi ell he he1 n k hk z hz.2,hnu ell he he1 n k hk z hz.2⟩

end GeneralLegalWaveSeed
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.exists_generalLegalWaveSeed
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveSeed.sum_value
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveSeed.cutoffCoordinates_support
#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveSeed.exists_primitive_profiles
