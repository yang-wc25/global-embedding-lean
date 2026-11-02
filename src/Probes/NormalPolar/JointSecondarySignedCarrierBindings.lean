import NormalPolar.JointSecondarySignedCarrierConstruction

/-! Transparent field identities for the manufactured carrier profiles.
Downstream whole-atlas assembly uses these proved identities instead of
repeatedly expanding the complete source certificate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m N p r : ℕ} {M Ep P Tr Λ Β : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [TopologicalSpace P]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)
local notation "X" => Ep × D
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)
local instance signedCarrierBindingsRecordFintype : Fintype (ActualSecondarySignedRecord (Λ ⊕ Fin r)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

theorem jointSecondarySignedCarrierProfiles_binding
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ,V) ∞ F)
    (signedPhase : Rec → M → ℝ) (K : (Λ ⊕ Fin r) → Set M) (O : Rec → Set M)
    (seeds : (rec : Rec) → JointSecondarySignedSeed (Ep := Ep) F hF (signedPhase rec)
      (K rec.val.1.1 ∩ K rec.val.1.2) (O rec))
    (B : OpenPartialHomeomorph P Ep) (Q : Set Ep) (hQ : Q ⊆ B.target) (S : Set M)
    (scale : ℝ) (hs : scale ∈ Icc (1/2 : ℝ) 1)
    (nInput nSolve q probeLength j Rsub Lprimary : ℕ)
    (reserve Bnd Mg Bchi Bnu Ku Mphase tau ell delta Delta : ℝ)
    (he : 0 ≤ ell) (he1 : ell ≤ 1)
    (hMg : jointSecondarySeedGeometryBudget seeds (max nSolve j) ≤ Mg)
    (Tbackground Tprobe : ℕ → ℝ)
    (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β)
      (fun _ : Ep => scale • F))
    (c : (l : Fin r) → Pieces l → Ep → D → M)
    (chi : (l : Fin r) → Pieces l → X → ℝ)
    (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) →
      normalSpace (I := IM) (scale • F) (c l s b x))
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X)
    (phase : Fin r → Ep × M → ℝ)
    (hphase : ∀ rec, (fun z : Ep × M => signedPhase rec z.2) =
      jointSecondarySignedPhase (Sum.elim g.phase phase) rec.val)
    (primaryDomain : Λ → Set (Ep × M))
    (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : Ep → Fin p → ℝ)
    (pieceK : (l : Fin r) → Pieces l → Set (Ep × M))
    (hpiece : ∀ l s, pieceK l s ⊆
      round3ParameterNativeDomain B ((univ : Set P) ×ˢ K (Sum.inr l)))
    (hbackground : ∀ l, incrementsGlobalRelativeSupport
      (round3ParameterNativeDomain B (univ : Set (P × M))) (g.cutoff l) ⊆
      round3ParameterNativeDomain B ((univ : Set P) ×ˢ K (Sum.inl l)))
    (background : ∀ rec s, ParameterRound2GlobalMeanRawProfiles (Tr := Tr)
      nInput (q+2) nSolve Rsub Lprimary reserve Bnd Mg Tbackground
      (fun _ : Ep => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      g input inputbar (round3ParameterNativeDomain B (univ : Set (P × M)))
      primaryDomain
      (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs nSolve j ell he he1 rec s).source
      ((jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs nSolve j ell he he1 rec s).symm ''
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs nSolve j ell he he1 rec s).sample)
      tau ell Delta)
    (prescribed : ∀ rec s, JointGroupedPrescribedObservationProfiles
      (fun _ : Ep => scale • F) (fun _ => contMDiff_const_rescale F hF scale) c chi nu a
      (round3ParameterNativeDomain B (univ : Set (P × M))) pieceK
      nInput (nSolve+1) ell Mg Bchi Bnu
      (fun z : X => (z.1,(jointSecondarySeedPaddedChoice (P := P) seeds rec s).host.symm z.2))
      (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs nSolve j ell he he1 rec s).source
      ((jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs nSolve j ell he he1 rec s).symm ''
        (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs nSolve j ell he he1 rec s).sample)
      Tprobe phase Mphase)
    (hu : ContDiffOn ℝ ∞ (fun z : X => u z.1) (B.target ×ˢ (univ : Set D)))
    (huj : ∀ k, k ≤ nSolve → ∀ z : X, z.1 ∈ Q →
      ell^k*‖iteratedFDeriv ℝ k (fun y : X => u y.1) z‖ ≤ Ku) :
    let profiles := jointSecondarySignedCarrierProfiles
      F hF signedPhase K O seeds B Q hQ S scale hs
      nInput nSolve q probeLength j Rsub Lprimary
      reserve Bnd Mg Bchi Bnu Ku Mphase tau ell delta Delta
      he he1 hMg Tbackground Tprobe g c chi nu a phase hphase primaryDomain
      input inputbar u pieceK hpiece hbackground background prescribed hu huj
    ∀ rec s,
      profiles.host rec s = ((jointSecondarySeedPaddedChoice seeds rec s).pullback B).host ∧
      (profiles.geometry rec s).c = ((jointSecondarySeedPaddedChoice seeds rec s).pullback B).c ∧
      (profiles.geometry rec s).chart = ((jointSecondarySeedPaddedChoice seeds rec s).pullback B).chart ∧
      profiles.cutoff rec s = ((jointSecondarySeedPaddedChoice seeds rec s).pullback B).cutoff := by
  intro profiles rec s
  refine ⟨rfl,?_,?_,rfl⟩
  · exact (jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs
      nSolve j ell he he1 rec s).1
  · exact (jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs
      nSolve j ell he he1 rec s).2.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedCarrierProfiles_binding
