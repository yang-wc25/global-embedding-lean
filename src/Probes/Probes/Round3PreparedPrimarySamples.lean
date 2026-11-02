import Probes.Round3PreparedPrimaryPieceProfiles
import Probes.Round3PreparedFiniteAssembly
import Smoothing.ParameterRound2IdentityRefinementSamples
import Probes.ActualIncrementOriginalSampling

/-! The actual primary packet produces the original all-order refinement
sample interface. Its inverse sample maps follow from the original norm
coverage of the true host inner domains. Three common profiles are finite
maxima of the actual compact-support profiles, selected before all later
scales and consumer neighborhoods. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric Filter
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_primary_original_refinement_samples
    {Β : Type*} [Fintype Β]
    (Data : IncrementsOriginalNativeData (m+1) d N M Ep)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (baseIndex : Fin Data.atlas.count × Fin Data.parameterCount)
    (pieceDomain : Set (Ep × M))
    (piece : ∀ nu : Fin Data.primaryCount, Β → Round3PreparedPrimaryPiece Data baseIndex.2 nu pieceDomain)
    (hInner : ∀ nu a y, y ∈ tsupport (piece nu a).cutoff → y.2 ∈ Data.atlas.inner (piece nu a).host)
    (Rsub : ℕ) (hCount : ∀ nu y,
      (Finset.univ.filter (fun a => y ∈ tsupport (piece nu a).cutoff)).card ≤ Rsub) :
    let F := actualOriginalOpenParameterSlice Data baseIndex
    let host := fun nu a => (piece nu a).host
    let b := fun nu a => (piece nu a).native
    let g0 := actualOriginalPrimaryFamily Data hd hs hn baseIndex host b
      (fun nu a => (piece nu a).slices) (fun nu a => (piece nu a).data)
      (fun nu a => (piece nu a).cutoff) (fun nu a => (piece nu a).active)
    ∃ Tinv Forward Meta : ℕ → ℝ,
      (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Forward k) ∧ (∀ k, 0 ≤ Meta k) ∧
      ∀ (ell : ℝ), 0 ≤ ell → ell ≤ 1 → ∀ (W : Set (Ep × M)), IsOpen W →
      (∀ nu y, y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)) →
        ∀ᶠ w in 𝓝 y, ∑ a, (piece nu a).cutoff w = 1) →
      ∀ Lprimary : ℕ,
      (∀ y ∈ W, (Finset.univ.filter (fun nu : Fin Data.primaryCount =>
        y ∈ incrementsGlobalRelativeSupport W
          (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart baseIndex.2).symm z.1,z.2)))).card ≤ Lprimary) →
      ParameterRound2IdentityRefinementSamples Data baseIndex.2 F g0 host b W ell Tinv Forward Meta Rsub Lprimary := by
  intro F host b g0
  have hLocal := fun nu a => round3_prepared_primary_piece_profiles Data hd baseIndex.2 nu pieceDomain (piece nu a)
  choose Ti Tf Te hTi hTf hTe hLocalJets using hLocal
  let Inv := fun k => round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount × Β => Ti a.1 a.2 k)
  let Forw := fun k => round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount × Β => Tf a.1 a.2 k)
  let Eta := fun k => round3PreparedFiniteMaximum (fun a : Fin Data.primaryCount × Β => Te a.1 a.2 k)
  let Forward := fun r => ∑ k ∈ Finset.range (r+2), Forw k
  let Meta := fun r => ∑ k ∈ Finset.range (r+1), Eta k
  have hInv : ∀ k, 0 ≤ Inv k := fun _ => round3PreparedFiniteMaximum_nonneg _
  have hForw : ∀ k, 0 ≤ Forw k := fun _ => round3PreparedFiniteMaximum_nonneg _
  have hEta : ∀ k, 0 ≤ Eta k := fun _ => round3PreparedFiniteMaximum_nonneg _
  have hForward : ∀ r, 0 ≤ Forward r := fun _ => Finset.sum_nonneg (fun k _ => hForw k)
  have hMeta : ∀ r, 0 ≤ Meta r := fun _ => Finset.sum_nonneg (fun k _ => hEta k)
  refine ⟨Inv,Forward,Meta,hInv,hForward,hMeta,?_⟩
  intro ell hell hell1 W hW hPartition Lprimary hPrimaryCount
  have hActive (observer : Fin Data.atlas.count) (nu : Fin Data.primaryCount) (a : Β)
      (z : X) (hz : z ∈ parameterRound2_originalRefinementActive Data baseIndex.2 F g0 W observer nu a) :
      (z.1,(Data.atlas.chart observer).symm z.2) ∈ tsupport (piece nu a).cutoff := by
    have hh := hz.2
    rw [parameterRound2_global_relativeSupport_eq W hW] at hh
    exact tsupport_mul_subset_left hh.2
  refine {
    eta_smooth := fun nu a => (piece nu a).smooth.contMDiffOn
    eta_support := by
      intro nu a y hy
      rw [parameterRound2_global_relativeSupport_eq W hW] at hy
      exact (piece nu a).support hy.2
    partition := hPartition
    sample_inverse := ?_
    inverse_jets := ?_
    forward_jets := ?_
    eta_jets := ?_
    eta_count := ?_
    primary_count := hPrimaryCount }
  · intro observer nu a y hy
    obtain ⟨z,hz,rfl⟩ := hy
    have he := hActive observer nu a z hz
    have hsrc := (piece nu a).support he
    have hbeq : (b nu a).symm (g0.chart nu a (z.1,(Data.atlas.chart observer).symm z.2)) =
        (z.1,Data.atlas.chart (host nu a) ((Data.atlas.chart observer).symm z.2)) :=
      (b nu a).left_inv hsrc.2
    rw [hbeq]
    apply (actual_original_native_evaluation_iff Data hd (host nu a,baseIndex.2) _).mpr
    have hobs := (actual_original_native_evaluation_iff Data hd (observer,baseIndex.2) z).mp hz.1.1
    exact ⟨hd.source_inner_norm (host nu a) _ (hInner nu a _ he),hobs.2⟩
  · intro observer nu a k hk y hy
    obtain ⟨z,hz,rfl⟩ := hy
    exact ((hLocalJets nu a ell hell hell1 k _ (hActive observer nu a z hz)).1).trans
      (round3PreparedFiniteMaximum_bound (fun a : Fin Data.primaryCount × Β => Ti a.1 a.2 k) (nu,a))
  · intro r observer nu a k hk hkr z hz
    have hlocal := (hLocalJets nu a ell hell hell1 k _ (hActive observer nu a z hz)).2.1
    have hmax := round3PreparedFiniteMaximum_bound (fun a : Fin Data.primaryCount × Β => Tf a.1 a.2 k) (nu,a)
    have hprefix : Forw k ≤ Forward r :=
      Finset.single_le_sum (fun l _ => hForw l) (Finset.mem_range.mpr (by omega))
    exact (hlocal.trans hmax).trans hprefix
  · intro r observer nu a k hkr y hy
    obtain ⟨z,hz,rfl⟩ := hy
    have hlocal := (hLocalJets nu a ell hell hell1 k _ (hActive observer nu a z hz)).2.2
    have hmax := round3PreparedFiniteMaximum_bound (fun a : Fin Data.primaryCount × Β => Te a.1 a.2 k) (nu,a)
    have hprefix : Eta k ≤ Meta r :=
      Finset.single_le_sum (fun l _ => hEta l) (by simpa using hkr)
    exact (hlocal.trans hmax).trans hprefix
  · intro nu y hy
    apply (Finset.card_le_card ?_).trans (hCount nu y)
    intro a ha
    have hh := (Finset.mem_filter.mp ha).2
    rw [parameterRound2_global_relativeSupport_eq W hW] at hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_primary_original_refinement_samples
