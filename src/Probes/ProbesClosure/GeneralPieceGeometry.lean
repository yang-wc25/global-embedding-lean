import Main.GeneralLegalWaveRawFamily
import NormalPolar.OriginalWaveSeedPhysical

/-!
# Physical geometry for the same arbitrary-cutoff source family

The exact general-cutoff seed already chooses adapted inner and outer charts.
This file supplies the actual prescribed solver geometry for those same charts
at every permitted reference contraction. The transverse Gram and free-normal
kernel follow from the original Good covector and legal normal, without a
radial bump assumption or any reconstructed response premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Manifold IsManifold
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.NormalPolar
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

namespace GeneralLegalWaveSeed
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {w : OpenSupportedLegalWave (n := m+1) F hF} {weight : ℝ}

def pieceValue (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) (x : M) : V :=
  d.pieceCutoff i x • (w.normal x : V)

def pieceCarrier (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : Set M :=
  tsupport (d.refinement.cutoff i) ∩ tsupport w.cutoff

theorem pieceCarrier_closed (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : IsClosed (d.pieceCarrier i) :=
  (isClosed_tsupport _).inter (isClosed_tsupport _)

theorem pieceCarrier_source (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) : d.pieceCarrier i ⊆ (d.inner i).chart.source :=
  fun _ hx => (d.inner i).support_source hx.1

theorem pieceValue_zero (d : GeneralLegalWaveSeed F hF w weight)
    (i : Fin d.refinement.count) (x : M) (hx : x ∉ d.pieceCarrier i) :
    d.pieceValue i x = 0 := by
  have hn : x ∉ tsupport (d.pieceCutoff i) := fun h => hx (d.pieceCutoff_support i h)
  change d.pieceCutoff i x • (w.normal x : V) = 0
  rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]

theorem sum_pieceValue (d : GeneralLegalWaveSeed F hF w weight) (x : M) :
    ∑ i, d.pieceValue i x = w.value x := d.sum_value x

theorem weighted_phase_good (d : GeneralLegalWaveSeed F hF w weight)
    (hw : 0 < weight) (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (i : Fin d.refinement.count) (y : D) (hy : y ∈ (d.outer i).chart.target) :
    GoodCovector (scale • F) (contMDiff_const_rescale F hF scale)
      ((d.outer i).chart.symm y)
      (mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) ((d.outer i).chart.symm y)) := by
  have hdom := (d.outer i).source_domain ((d.outer i).chart.map_target hy)
  have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
  have he : mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) ((d.outer i).chart.symm y) =
      weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase ((d.outer i).chart.symm y) :=
    (hd.hasMFDerivAt.const_smul weight).mfderiv
  rw [he]
  apply (goodCovector_const_rescale_iff F hF scale (contraction_ne_zero scale hs) _ _).mpr
  exact (good_covector_smul_iff F hF _ _ weight hw.ne').mpr (w.legal _ hdom).1

theorem weighted_phase_free (d : GeneralLegalWaveSeed F hF w weight)
    (hw : 0 < weight) (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (i : Fin d.refinement.count) (y : D) (hy : y ∈ (d.outer i).chart.target) :
    let x := (d.outer i).chart.symm y
    let xi := mfderiv IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) x
    ∀ u v : xi.ker, inner ℝ
      ((trueSecondForm (scale • F) (contMDiff_const_rescale F hF scale) x
        (symmetricSquareProduct (TangentSpace IM x) u.val v.val)) : V)
      (d.scaledNormal scale hs i 0 y : V) = 0 := by
  intro x xi u v
  have hdom := (d.outer i).source_domain ((d.outer i).chart.map_target hy)
  have hd := (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
  have he : xi = weight • mfderiv IM 𝓘(ℝ,ℝ) w.phase x :=
    (hd.hasMFDerivAt.const_smul weight).mfderiv
  have hker (a : xi.ker) : mfderiv IM 𝓘(ℝ,ℝ) w.phase x a.val = 0 := by
    have ha : weight • (mfderiv IM 𝓘(ℝ,ℝ) w.phase x a.val) = 0 :=
      (congrArg (fun L : TangentSpace IM x →L[ℝ] ℝ => L a.val) he).symm.trans a.property
    exact (smul_eq_zero.mp ha).resolve_left hw.ne'
  let u0 : (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap.ker := ⟨u.val,hker u⟩
  let v0 : (mfderiv IM 𝓘(ℝ,ℝ) w.phase x).toLinearMap.ker := ⟨v.val,hker v⟩
  have hlegal := actualRescaledNormal_legal F hF scale (contraction_ne_zero scale hs) x
    _ (w.normal x) (w.legal x hdom).2
  exact (supportedRank_mem_legalValueSpace_iff _ _ _).mp hlegal
    (symmetricSquareProduct _ u0 v0)

/-- Literal original-phase physical geometry, using exactly the source charts
and normal values of the general raw family. -/
def physicalGeometry (d : GeneralLegalWaveSeed F hF w weight)
    (hw : 0 < weight)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1) (i : Fin d.refinement.count) :
    ActualPrescribedPhysicalGeometry
      (fun _ : Z => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      (d.coordinate i) (d.scaledNormal scale hs i) (d.physicalChart i)
      (fun z : Z × M => weight * w.phase z.2) := by
  let e := (d.outer i).chart
  have htarget (z : X) (hz : z ∈ (d.physicalChart i).target) : z.2 ∈ e.target :=
    d.inner_target_subset_outer i hz.2
  have hpsi (y : D) (hy : y ∈ e.target) :
      MDifferentiableAt IM 𝓘(ℝ,ℝ) (fun x => weight * w.phase x) (e.symm y) := by
    have hdom := (d.outer i).source_domain (e.map_target hy)
    exact contMDiffAt_const.mul
      (w.phase_smooth.contMDiffAt (w.domain_open.mem_nhds hdom)) |>.mdifferentiableAt (by simp)
  refine {
    slices := fun _ => e
    maximal := fun _ => (d.outer i).maximal
    coordinates := rfl
    target := htarget
    inverse := fun _ _ => rfl
    immersion := fun z _ =>
      (immersion_const_rescale_iff F hF scale (contraction_ne_zero scale hs) _).mpr (hImm _)
    gram := ?_
    normal_kernel := ?_
    adaptation := fun z hz => (d.inner i).adaptation z.2 hz.2 }
  · intro z hz
    exact actual_increment_transverse_gram_of_good_phase (scale • F)
      (contMDiff_const_rescale F hF scale) (fun x => weight * w.phase x)
      e (d.outer i).maximal e.target e.open_target Subset.rfl z.2 (htarget z hz)
      (hpsi z.2 (htarget z hz)) (d.outer i).inverse_phase
      (d.weighted_phase_good hw scale hs i z.2 (htarget z hz))
  · intro z hz
    exact actual_increment_transverse_kernel_of_phase_free (scale • F)
      (contMDiff_const_rescale F hF scale) (fun x => weight * w.phase x)
      e (d.outer i).maximal e.target e.open_target Subset.rfl z.2 (htarget z hz)
      (hpsi z.2 (htarget z hz)) (d.outer i).inverse_phase (d.scaledNormal scale hs i z.1 z.2)
      (d.weighted_phase_free hw scale hs i z.2 (htarget z hz))

end GeneralLegalWaveSeed
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.GeneralLegalWaveSeed.physicalGeometry
