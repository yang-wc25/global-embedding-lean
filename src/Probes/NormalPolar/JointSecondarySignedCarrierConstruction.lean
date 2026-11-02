import NormalPolar.JointSecondarySignedNativeCutoffJets
import NormalPolar.JointSecondaryCarrierSourceProfiles

/-! Keep original open primary domains separate from closed amplitude carriers.
Assemble the complete primitive secondary-source certificate on the
same actual finite signed seeds. Geometry, host, cutoff, partition, support
and inverse estimates are all manufactured here. Background and prescribed
components are the literal host profiles supplied by their original-wave
constructors. The common geometry bound changes only bound proofs. -/

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
local instance signedCarrierConstructionRecordFintype : Fintype (ActualSecondarySignedRecord (Λ ⊕ Fin r)) := by
  unfold ActualSecondarySignedRecord
  infer_instance

def jointSecondarySignedCarrierProfiles
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
    JointGroupedSecondaryCarrierProfiles (Tr := Tr) (Sub := Σ rec, Fin (seeds rec).refinement.count)
      (fun _ : Ep => scale • F) (fun _ => contMDiff_const_rescale F hF scale)
      g c chi nu a phase input inputbar u (round3ParameterNativeDomain B (univ : Set (P × M)))
      primaryDomain (fun l => round3ParameterNativeDomain B ((univ : Set P) ×ˢ K l)) pieceK
      nInput nSolve q probeLength j Rsub Lprimary reserve Bnd Mg
      (jointSecondarySeedCutoffBudget seeds nSolve) Bchi Bnu Ku Mphase tau ell delta Delta
      Tbackground Tprobe (fun _ => 1) where
  background_carrier := hbackground
  piece_support := hpiece
  geometry := fun rec s =>
    (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs nSolve j ell he he1 rec s).enlargeBudget hMg
  host := fun rec s => (jointSecondarySeedPaddedChoice (P := P) seeds rec s).host
  host_maximal := by
    intro rec s
    rw [jointSecondarySeedPaddedChoice_host]
    exact ((seeds s.1).outer s.2).maximal
  host_source := jointSecondarySignedNativeRaw_host_source seeds B Q hQ S scale hs nSolve j ell he he1
  cutoff := jointSecondarySignedNativeCutoff seeds B
  cutoff_support := by
    intro rec s z hz
    exact jointSecondarySignedNativeCutoff_support seeds B Q hQ S scale hs nSolve j ell he he1 rec s
      ⟨hz.1,⟨hz.2.1.1,mem_univ _,hz.2.1.2.2,hz.2.2.2.2⟩⟩
  partition := by
    intro rec z hz
    exact jointSecondarySignedNativeCutoff_partition seeds B rec z
      ⟨hz.1.1,mem_univ _,hz.1.2.2,hz.2.2.2⟩
  phase_identity := fun rec s =>
    (jointSecondarySignedNativeRaw_choice seeds B Q hQ S scale hs nSolve j ell he he1 rec s).2.2.trans
      (hphase rec)
  cutoff_smooth := jointSecondarySignedNativeCutoff_smooth seeds B Q hQ S scale hs nSolve j ell he he1
  inverse_smooth := jointSecondarySignedNativeHost_inverse_smooth seeds B Q hQ S scale hs nSolve j ell he he1
  background := background
  prescribed := prescribed
  cutoff_jets := jointSecondarySignedNativeCutoff_jets seeds B Q hQ S scale hs nSolve j ell he he1
  inverse_jets := fun rec s k hk _ z hz =>
    jointSecondarySignedNativeHost_inverse_jets seeds B Q hQ S scale hs nSolve j ell he he1 rec s k hk z hz
  parameter_smooth := fun rec s => hu.mono (fun z hz =>
    ⟨(jointSecondarySignedNativeHost_source seeds B Q hQ S scale hs nSolve j ell he he1 rec s hz).1,
      mem_univ _⟩)
  parameter_jets := by
    intro rec s k hk z hz
    change z ∈ (jointSecondarySignedNativeHostTransition seeds B Q hQ S scale hs nSolve j ell he he1 rec s).symm ''
      (jointSecondarySignedNativeRaw seeds B Q hQ S scale hs nSolve j ell he he1 rec s).sample at hz
    rw [jointSecondarySignedNativeHost_sample] at hz
    by_cases h : s.1 = rec
    · simp only [jointSecondarySignedNativeSample,if_pos h] at hz
      exact huj k hk z hz.1
    · simp only [jointSecondarySignedNativeSample,if_neg h,mem_empty_iff_false] at hz

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointSecondarySignedCarrierProfiles
