import NormalPolar.JointSecondarySignedSeed
import Probes.Round3ParameterSecondaryConstruction
import Probes.Round3ParameterChartPullback

/-! Literal physical choices for the constructed signed finite seed. These
choices are fixed before all reconstruction orders and scales, and lift to
any physical parameter space without changing the original spatial chart,
phase, host or ordinary partition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
variable {F : M → EuclideanSpace ℝ (Fin N)}
  {hF : ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ F}
  {phase : M → ℝ} {K O : Set M}
namespace JointSecondarySignedSeed
variable (seed : JointSecondarySignedSeed (Ep := Ep) F hF phase K O)

def choice (i : Fin seed.refinement.count) : Round3ParameterSecondaryChoice P M m where
  host := (seed.outer i).chart
  chart := (OpenPartialHomeomorph.refl P).prod (seed.inner i).chart
  c := fun _ y => (seed.outer i).chart.symm y
  cutoff := fun z => seed.refinement.cutoff i z.2

theorem choice_preserves (i : Fin seed.refinement.count) :
    Round3ParameterChartPreserves (seed.choice (P := P) i).chart := fun _ _ => rfl

theorem choice_host_maximal (i : Fin seed.refinement.count) :
    (seed.choice (P := P) i).host ∈ maximalAtlas IM ∞ M := (seed.outer i).maximal

theorem choice_host_source (i : Fin seed.refinement.count) :
    (seed.choice (P := P) i).chart.source ⊆
      ((OpenPartialHomeomorph.refl P).prod (seed.choice (P := P) i).host).source :=
  fun z hz => ⟨hz.1,(seed.inner i).source_in_outer (seed.outer i) (seed.nested i) hz.2⟩

theorem choice_partition (z : P × M) (hz : z.2 ∈ K) :
    ∑ i, (seed.choice i).cutoff z = 1 := seed.refinement.partition z.2 hz

theorem raw_choice (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) (i : Fin seed.refinement.count) :
    (seed.raw scale hs n j ell he he1 i).c = (seed.choice (P := Ep) i).c ∧
    (seed.raw scale hs n j ell he he1 i).chart = (seed.choice (P := Ep) i).chart ∧
    (seed.raw scale hs n j ell he he1 i).phase = (fun z => phase z.2) :=
  ⟨seed.raw_c _ _ _ _ _ _ _ _,seed.raw_chart _ _ _ _ _ _ _ _,seed.raw_phase _ _ _ _ _ _ _ _⟩

theorem choice_cutoff_smooth (i : Fin seed.refinement.count) :
    ContDiffOn ℝ ∞
      ((seed.choice (P := Ep) i).cutoff ∘
        ((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm)
      (((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm.trans
        (seed.choice (P := Ep) i).chart).source :=
  (seed.inner i).host_cutoff_smooth (seed.outer i)

theorem choice_inverse_smooth (i : Fin seed.refinement.count) :
    ContDiffOn ℝ ∞
      (((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm.trans
        (seed.choice (P := Ep) i).chart).symm
      (((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm.trans
        (seed.choice (P := Ep) i).chart).target :=
  (seed.inner i).hostTransition_inverse_smooth (seed.outer i) (seed.nested i)

theorem choice_cutoff_raw_support (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1) (i : Fin seed.refinement.count) :
    incrementsGlobalRelativeSupport univ (seed.choice (P := Ep) i).cutoff ∩
      (univ ×ˢ K) ⊆ (seed.raw scale hs n j ell he he1 i).support := by
  rw [seed.raw_support]
  exact JointSecondarySignedBuffer.relative_cutoff_support

theorem choice_cutoff_raw_jets (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (i : Fin seed.refinement.count) (k : ℕ) (hk : k ≤ n)
    (z : X) (hz : z ∈ (seed.raw scale hs n j ell he he1 i).sample) :
    ell^k*‖iteratedFDeriv ℝ k
      ((seed.choice (P := Ep) i).cutoff ∘
        ((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm)
      ((((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm.trans
        (seed.choice (P := Ep) i).chart).symm z)‖ ≤ seed.Kcut n := by
  rw [seed.raw_sample] at hz
  exact seed.cutoff_jets ell he he1 n k hk i z hz.2

theorem choice_inverse_raw_jets (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (n j : ℕ) (ell : ℝ) (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (i : Fin seed.refinement.count) (k : ℕ) (hk : 1 ≤ k)
    (z : X) (hz : z ∈ (seed.raw scale hs n j ell he he1 i).sample) :
    ell^(k-1)*‖iteratedFDeriv ℝ k
      (((OpenPartialHomeomorph.refl Ep).prod (seed.choice (P := Ep) i).host).symm.trans
        (seed.choice (P := Ep) i).chart).symm z‖ ≤ 1 := by
  rw [seed.raw_sample] at hz
  apply (seed.inner i).hostTransition_inverse_jets (seed.outer i) (seed.nested i) ell k hk z
  rw [(seed.inner i).hostTransition_target (seed.outer i) (seed.nested i)]
  exact hz

end JointSecondarySignedSeed
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedSeed.raw_choice
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedSeed.choice_cutoff_raw_jets
#print axioms GlobalEmbedding.Continuation.JointSecondarySignedSeed.choice_inverse_raw_jets
