import NormalPolar.OriginalWaveSeedRawProfiles
import NormalPolar.ParameterDisplacementPrescribedPhysicalCoordinates
import Probes.ActualIncrementFreeNormalKernel

/-! The same actual adapted chart retains the original legal normal. Its
transverse Gram and transverse kernel are derived from the original Good
covector and legal-value-space membership, with the original phase weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade GlobalEmbedding.Continuation

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

variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : LocalLegalWave (n := m+1) F hF} {weight : ℝ}
  {d : OriginalWaveSeedRefinement (m := m) F hF w weight} {i : Fin d.count}

namespace OriginalWaveSeedBuffer

theorem original_weighted_phase_good (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight) (y : D) (hy : y ∈ b.spatialChart.target) :
    GoodCovector F hF (b.spatialChart.symm y)
      (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (b.spatialChart.symm y)) := by
  have hdom := b.spatialChart_source_original (b.spatialChart.map_target hy)
  have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
  have he : mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (b.spatialChart.symm y) =
      weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase (b.spatialChart.symm y) :=
    (hd.hasMFDerivAt.const_smul weight).mfderiv
  rw [he]
  exact (good_covector_smul_iff F hF _ _ weight hweight.ne').mpr ((w.legal _ hdom).1)

theorem original_weighted_phase_free (b : OriginalWaveSeedBuffer d i)
    (hweight : 0 < weight) (y : D) (hy : y ∈ b.spatialChart.target) :
    let x := b.spatialChart.symm y
    let xi := mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) x
    ∀ u v : xi.ker, inner ℝ
      ((trueSecondForm F hF x (symmetricSquareProduct (TangentSpace IM x) u.val v.val)) : V)
      (w.normal x : V) = 0 := by
  intro x xi u v
  have hdom := b.spatialChart_source_original (b.spatialChart.map_target hy)
  have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
  have he : xi = weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase x :=
    (hd.hasMFDerivAt.const_smul weight).mfderiv
  have hker (a : xi.ker) : mfderiv IM 𝓘(ℝ,ℝ) w.phase x a.val = 0 := by
    have ha : weight • (mfderiv IM 𝓘(ℝ,ℝ) w.phase x a.val) = 0 :=
      (congrArg (fun L : TangentSpace IM x →L[ℝ] ℝ => L a.val) he).symm.trans a.property
    exact (smul_eq_zero.mp ha).resolve_left hweight.ne'
  let u0 : (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap.ker := ⟨u.val,hker u⟩
  let v0 : (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap.ker := ⟨v.val,hker v⟩
  have hlegal := (supportedRank_mem_legalValueSpace_iff _ _ _).mp ((w.legal x hdom).2)
  exact hlegal (symmetricSquareProduct _ u0 v0)

/-- Original legality supplies every physical solver condition for the very
same outer spatial chart and inner joint chart used by the raw producer. -/
def actual_physical_geometry (b b' : OriginalWaveSeedBuffer d i)
    (hbb : b.compactTarget ⊆ interior b'.compactTarget) (hweight : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x)) :
    ActualPrescribedPhysicalGeometry (fun _ : Z => F) (fun _ => hF)
      (fun _ => b'.spatialChart.symm) (fun _ x => w.normal (b'.spatialChart.symm x))
      b.chart (fun z : Z × M => weight * w.phase z.2) := by
  let e := b'.spatialChart
  have htarget (z : X) (hz : z ∈ b.chart.target) : z.2 ∈ e.target := by
    have hzL : z ∈ b.compactTarget := by
      rw [b.chart_target] at hz
      exact interior_subset hz
    exact (b.compact_in_outer b' hbb hzL).2
  have hpsi (y : D) (hy : y ∈ e.target) :
      MDifferentiableAt IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm y) := by
    have hdom := b'.spatialChart_source_original (e.map_target hy)
    exact contMDiffAt_const.mul
      (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)) |>.mdifferentiableAt (by simp)
  refine {
    slices := fun _ => e
    maximal := fun _ => b'.spatialChart_maximal
    coordinates := rfl
    target := htarget
    inverse := ?_
    immersion := fun z _ => hImm (e.symm z.2)
    gram := ?_
    normal_kernel := ?_
    adaptation := fun z hz => (b.phase_coordinate z hz).2.symm }
  · intro z _
    apply Prod.ext (Subsingleton.elim _ _)
    exact (b'.spatial_inverse_original z).symm
  · intro z hz
    exact actual_increment_transverse_gram_of_good_phase F hF (fun x => weight * w.phase x)
      e b'.spatialChart_maximal e.target e.open_target Subset.rfl z.2 (htarget z hz)
      (hpsi z.2 (htarget z hz)) b'.spatialChart_inverse_phase
      (b'.original_weighted_phase_good hweight z.2 (htarget z hz))
  · intro z hz
    exact actual_increment_transverse_kernel_of_phase_free F hF (fun x => weight * w.phase x)
      e b'.spatialChart_maximal e.target e.open_target Subset.rfl z.2 (htarget z hz)
      (hpsi z.2 (htarget z hz)) b'.spatialChart_inverse_phase (w.normal (e.symm z.2))
      (b'.original_weighted_phase_free hweight z.2 (htarget z hz))

end OriginalWaveSeedBuffer
end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.OriginalWaveSeedBuffer.actual_physical_geometry

