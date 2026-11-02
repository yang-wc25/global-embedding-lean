import NormalPolar.JointSecondarySignedRescaledRawGeometry
import NormalPolar.JointSecondarySignedHost
import Probes.ActualSecondaryGeometryBudgets

/-! One actual finite signed-phase seed, constructed from the original phase,
closed carrier, Good covector and immersion. The charts, partition, host and
all raw budgets are chosen once before contraction, derivative orders and
scales. No forcing, reconstructed wave or final estimate is an input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {M Ep : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D

structure JointSecondarySignedSeed
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (phase : M → ℝ) (K O : Set M) where
  refinement : JointSecondarySignedRefinement (m := m) phase K O
  inner : (i : Fin refinement.count) → JointSecondarySignedBuffer refinement i
  outer : (i : Fin refinement.count) → JointSecondarySignedBuffer refinement i
  nested : ∀ i, (inner i).compactTarget ⊆ interior (outer i).compactTarget
  Mg : ℕ → ℝ
  Kcut : ℕ → ℝ
  positive : ∀ n, 0 < Mg n ∧ 0 < Kcut n
  raw : ∀ (scale : ℝ), scale ∈ Icc (1/2 : ℝ) 1 →
    ∀ n j ell, 0 ≤ ell → ell ≤ 1 → Fin refinement.count →
      ActualSecondaryRawGeometry (fun _ : Ep => scale • F)
        (fun _ => contMDiff_const_rescale F hF scale) n j ell (Mg (max n j)) univ
  raw_c : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).c = fun _ y => (outer i).chart.symm y
  raw_chart : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).chart = (OpenPartialHomeomorph.refl Ep).prod (inner i).chart
  raw_phase : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).phase = fun z => phase z.2
  raw_sample : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).sample = univ ×ˢ (inner i).chart.target
  raw_support : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).support = univ ×ˢ (tsupport (refinement.cutoff i) ∩ K)
  raw_spatialChart : ∀ scale hs n j ell he he1 i,
    (raw scale hs n j ell he he1 i).spatialChart = fun _ => (outer i).chart
  cutoff_jets : ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ n k, k ≤ n →
    ∀ i (z : X), z.2 ∈ (inner i).chart.target →
      ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => refinement.cutoff i ((outer i).chart.symm y.2))
        (((inner i).hostTransition (outer i)).symm z)‖ ≤ Kcut n

/-- The full finite seed is produced from the original geometric premises.
Goodness supplies the noncriticality used to construct the adapted cover. -/
theorem jointSecondary_exists_signed_seed
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (hImm : ∀ x, Function.Injective (mfderiv IM 𝓘(ℝ,V) F x))
    (phase : M → ℝ) (K O : Set M) (hK : IsClosed K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hphase : ContMDiffOn IM 𝓘(ℝ,ℝ) ∞ phase O)
    (hgood : ∀ x ∈ O, GoodCovector F hF x (mfderiv IM 𝓘(ℝ,ℝ) phase x)) :
    Nonempty (JointSecondarySignedSeed (Ep := Ep) F hF phase K O) := by
  obtain ⟨d⟩ := jointSecondary_exists_signed_refinement phase K O hK hO hKO hphase
    (fun x hx => (hgood x (hKO hx)).1)
  let inner (i : Fin d.count) := Classical.choice (jointSecondary_exists_signed_buffer d i)
  choose outer hnested Mg hMg hraw using
    fun i => (inner i).exists_actual_secondary_rescaled_raw_geometry (Ep := Ep)
      F hF hImm hK hO hphase hgood
  choose Kcut hKcut hcut using
    fun i => (inner i).exists_host_cutoff_profile (Ep := Ep) (outer i) (hnested i)
  let MG (n : ℕ) := 1+∑ i, Mg i n
  let KC (n : ℕ) := 1+∑ i, Kcut i n
  have hMG (n : ℕ) : 0 < MG n := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hMg i n).le))
  have hKC (n : ℕ) : 0 < KC n := by
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _ => (hKcut i n).le))
  have hGM (i : Fin d.count) (n : ℕ) : Mg i n ≤ MG n :=
    (Finset.single_le_sum (fun i _ => (hMg i n).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  have hCK (i : Fin d.count) (n : ℕ) : Kcut i n ≤ KC n :=
    (Finset.single_le_sum (fun i _ => (hKcut i n).le) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨{
    refinement := d
    inner := inner
    outer := outer
    nested := hnested
    Mg := MG
    Kcut := KC
    positive := fun n => ⟨hMG n,hKC n⟩
    raw := fun scale hs n j ell he he1 i =>
      (hraw i scale hs n j ell he he1).choose.enlargeBudget (hGM i (max n j))
    raw_c := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.1
    raw_chart := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.2.1
    raw_phase := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.2.2.1
    raw_sample := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.2.2.2.1
    raw_support := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.2.2.2.2.1
    raw_spatialChart := fun scale hs n j ell he he1 i => (hraw i scale hs n j ell he he1).choose_spec.2.2.2.2.2
    cutoff_jets := fun ell he he1 n k hk i z hz =>
      (hcut i ell he he1 n k hk z hz).trans (hCK i n) }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondary_exists_signed_seed
