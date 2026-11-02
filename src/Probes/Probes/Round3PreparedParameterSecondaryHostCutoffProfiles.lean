import Probes.Round3PreparedParameterSecondaryStableProfiles

/-! The raw solver differentiates the cutoff in the original host chart.
These are its actual fixed-reference jets on the original compact samples,
simultaneously in every observer chart and every later scale. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFinite (n : ℕ) : Fintype (ActualSecondarySignedRecord (Fin n)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

 theorem round3_prepared_parameter_host_cutoff_profiles
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P)
    (e : OpenPartialHomeomorph M D) (he : e ∈ maximalAtlas 𝓙 ∞ M)
    (rho : P × M → ℝ) (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (S : Set X) (hS : IsCompact S) (hST : S ⊆ B.target ×ˢ e.target) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ ell, 0 ≤ ell → ell ≤ 1 →
      ∀ k z, z ∈ S → ell^k*‖iteratedFDeriv ℝ k
        (fun y : X => rho (B.symm y.1,e.symm y.2)) z‖ ≤ C k := by
  have hh : ContMDiffOn 𝓘(ℝ,X) ((𝓘(ℝ,Ep)).prod 𝓙) ∞
      (fun y : X => (B.symm y.1,e.symm y.2)) (B.target ×ˢ e.target) :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hB).comp
      contDiff_fst.contMDiff.contMDiffOn (fun _ hz => hz.1)).prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas he).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hz => hz.2))
  have hm := hRho.comp_contMDiffOn hh
  have hSmooth : ContDiffOn ℝ ∞ (fun y : X => rho (B.symm y.1,e.symm y.2))
      (B.target ×ˢ e.target) := hm.contDiffOn
  obtain ⟨C,hC,hProfile⟩ := round3_prepared_compact_profiles
    (fun y : X => rho (B.symm y.1,e.symm y.2)) (B.target ×ˢ e.target) S
    (B.open_target.prod e.open_target) hS hST hSmooth
  exact ⟨C,hC,fun ell hell hell1 k z hz => (hProfile ell hell hell1 k z hz).1⟩

 theorem round3_prepared_actual_parameter_secondary_host_cutoff_profiles
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hS : ∀ i, IsCompact (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i)) :
    ∃ Kcut : ℕ → ℝ, (∀ k, 0 ≤ Kcut k) ∧
      ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
      ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer n k, k ≤ n →
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
        Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet observer →
        ell^k*‖iteratedFDeriv ℝ k (fun y : X => choice.cutoff
          ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) z‖ ≤ Kcut n := by
  let A := Sigma (fun r : ActualSecondarySignedRecord (Fin Ref.primaryCount) =>
    Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i)))
  let J := A × (Fin Ref.atlas.count × Fin Ref.parameterCount)
  let Sn := fun i => (parameterTensorModelEquiv (m+1) d) ⁻¹'
    incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet i
  have hSn (i) : IsCompact (Sn i) :=
    (parameterTensorModelEquiv (m+1) d).toHomeomorph.isCompact_preimage.mpr (hS i)
  have hST (i) : Sn i ⊆ (Ref.parameterChart i.2).target ×ˢ (Ref.atlas.chart i.1).target := by
    intro z hz
    have he := (actual_original_native_evaluation_iff Ref hd i z).mp hz
    exact ⟨hd.parameter_norm_subset i.2 he.2.1,hd.source_norm_subset i.1 he.1⟩
  have hOne (j : J) := round3_prepared_parameter_host_cutoff_profiles
    (Ref.parameterChart j.2.2) (hd.parameter_charts_smooth j.2.2)
    (Ref.atlas.chart j.2.1) (hd.atlas_smooth.chart_mem j.2.1)
    (round3PreparedParameterSecondaryChoice Ref hd hs j.1.2.1 j.1.1 _ (packet.piece j.1.1 j.1.2.1 j.1.2.2)).cutoff
    (packet.smooth j.1.1 j.1.2.1 j.1.2.2) (Sn j.2) (hSn j.2) (hST j.2)
  choose C hC hProfile using hOne
  let Kcut := fun n => round3PreparedFiniteMaximum (fun j : J × Fin (n+1) => C j.1 j.2)
  refine ⟨Kcut,fun n => round3PreparedFiniteMaximum_nonneg _,?_⟩
  intro F hF stable ell hell hell1 r i a observer n k hkn choice z hz
  have hEqual := (round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _
    (packet.piece r i a) F hF (stable r i a) observer.2).1
  have hFun : (fun y : X => choice.cutoff ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) =
      (fun y : X => (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)).cutoff
        ((Ref.parameterChart observer.2).symm y.1,(Ref.atlas.chart observer.1).symm y.2)) := by
    funext y
    exact congrFun hEqual _
  rw [hFun]
  exact (hProfile (⟨r,⟨i,a⟩⟩,observer) ell hell hell1 k z hz).trans
    (round3PreparedFiniteMaximum_bound (fun j : J × Fin (n+1) => C j.1 j.2)
      ((⟨r,⟨i,a⟩⟩,observer),⟨k,Nat.lt_succ_of_le hkn⟩))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_parameter_secondary_host_cutoff_profiles
