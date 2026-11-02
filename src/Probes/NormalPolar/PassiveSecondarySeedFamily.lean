import NormalPolar.PassiveSecondarySeedNative
import NormalPolar.JointSecondarySignedSeed

/-! One actual signed spatial seed supplies the canonical native geometry
in every original parameter chart. Its finite partition, hosts, inner charts
and all budgets are fixed before contraction, derivative order and scale. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

variable {m N : ℕ} {M P Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

variable (F : M → EuclideanSpace ℝ (Fin N))
  (hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1)))
    𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F)
  (phase : M → ℝ) (K O : Set M)
  (seed : JointSecondarySignedSeed (Ep := Ep) F hF phase K O)
  (B : OpenPartialHomeomorph P Ep)

def passiveSecondarySeed_family_raw
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) (i : Fin seed.refinement.count) :
    ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
      (fun _ => contMDiff_const_rescale F hF scale) n j ell (seed.Mg (max n j))
      (round3ParameterNativeDomain B (univ : Set (P × M))) :=
  passiveSecondarySeed_native_raw B _ _ n j ell (seed.Mg (max n j)) (seed.inner i).chart
    (seed.raw scale hs n j ell he he1 i) (seed.raw_chart scale hs n j ell he he1 i)

variable (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
  (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) (i : Fin seed.refinement.count)

theorem passiveSecondarySeed_family_c :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).c =
      fun _ y => (seed.outer i).chart.symm y :=
  seed.raw_c scale hs n j ell he he1 i

theorem passiveSecondarySeed_family_chart :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).chart =
      round3ParameterChartPullback B ((OpenPartialHomeomorph.refl P).prod (seed.inner i).chart) := rfl

theorem passiveSecondarySeed_family_phase :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).phase =
      fun z => phase z.2 :=
  seed.raw_phase scale hs n j ell he he1 i

theorem passiveSecondarySeed_family_spatialChart :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).spatialChart =
      fun _ => (seed.outer i).chart :=
  seed.raw_spatialChart scale hs n j ell he he1 i

theorem passiveSecondarySeed_family_sample :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).sample =
      B.target ×ˢ (seed.inner i).chart.target := by
  ext z
  change (z.1 ∈ B.target ∧ z ∈ (seed.raw scale hs n j ell he he1 i).sample) ↔ _
  rw [seed.raw_sample scale hs n j ell he he1 i]
  simp only [mem_prod,mem_univ,true_and]

theorem passiveSecondarySeed_family_sample_target :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).sample =
      (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).chart.target := by
  rw [passiveSecondarySeed_family_sample,passiveSecondarySeed_family_chart]
  ext z
  exact (passiveSecondarySeed_chart_target B (seed.inner i).chart z).symm

theorem passiveSecondarySeed_family_support :
    (passiveSecondarySeed_family_raw F hF phase K O seed B scale hs n j ell he he1 i).support =
      round3ParameterNativeDomain B
        ((univ : Set P) ×ˢ (tsupport (seed.refinement.cutoff i) ∩ K)) := by
  ext z
  change (z.1 ∈ B.target ∧ z ∈ (seed.raw scale hs n j ell he he1 i).support) ↔ _
  rw [seed.raw_support scale hs n j ell he he1 i]
  simp only [round3ParameterNativeDomain,mem_setOf_eq,mem_prod,mem_univ,true_and]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_family_raw
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_family_sample_target
#print axioms GlobalEmbedding.Continuation.passiveSecondarySeed_family_support
