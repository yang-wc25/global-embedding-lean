import NormalPolar.JointSecondaryFamilySpec
import NormalPolar.JointSecondaryCarrierSourceProfiles
import NormalPolar.JointSecondaryCarrierPiece

/-! All actual signed ordered records are constructed as a single joint family.
The coefficient bound and the two forcing fields include actual derivatives
of u. The only choices are over records and subordinates after the complete
joint fields have been fixed; no pointwise-in-u witness is differentiated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {M Ep Tr Λ Β Sub : Type*} {m N p r : ℕ}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)
local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)

theorem jointCarrier_mixed_family_from_raw_uniform
    (nInput nSolve q probeLength Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (hbackgroundOrder : nSolve+2+(q+2) ≤ nInput) (hprobeOrder : nSolve+2+probeLength ≤ nInput)
    (reserve Bnd Mg Kcut Bchi Bnu Ku Mphase : ℝ)
    (hreserve : 0 < reserve) (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu) (hKu : 0 ≤ Ku) (hMphase : 0 ≤ Mphase)
    (weight : Fin r → ℝ) (Tbackground Tprobe Tinv : ℕ → ℝ)
    (hTbackground : ∀ k, 0 ≤ Tbackground k) (hTprobe : ∀ k, 0 ≤ Tprobe k) (hTinv : ∀ k, 0 ≤ Tinv k) :
    ∃ CH : ℝ, 0 ≤ CH ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I := IM) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
      (label : (Fin r × Bool) ↪ Fin p)
      (c : (l : Fin r) → Pieces l → Ep → D → M) (chi : (l : Fin r) → Pieces l → X → ℝ)
      (nu : (l : Fin r) → (s : Pieces l) → (b : Ep) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
      (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (Ep × M) X) (phase : Fin r → Ep × M → ℝ)
      (input inputbar : (b : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
      (u : Ep → Fin p → ℝ)
      (tau ell delta Delta : ℝ) (hdelta : 0 ≤ delta)
      (W : Set (Ep × M)) (primaryDomain : Λ → Set (Ep × M))
      (K : (Λ ⊕ Fin r) → Set (Ep × M))
      (pieceK : (l : Fin r) → Pieces l → Set (Ep × M)) (j : ℕ)
      (profiles : JointGroupedSecondaryCarrierProfiles (Sub := Sub) (Tr := Tr) F hF g c chi nu a phase
        input inputbar u W primaryDomain K pieceK nInput nSolve q probeLength j Rsub Lprimary
        reserve Bnd Mg Kcut Bchi Bnu Ku Mphase tau ell delta Delta Tbackground Tprobe Tinv),
    let vf := fun l s => actualProbeNormalAmplitude F (c l s) (chi l s) (nu l s) delta tau (weight l)
    let phases := Sum.elim g.phase phase
    let R := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u false
    let Q := jointGroupedCombinedAmplitude F hF g label c vf tau delta (q+2) probeLength a input u true
    ∃ data : Rec → Sub → ActualSecondaryPhysicalPieceData F hF nSolve j ell Mg CH delta W,
      JointSecondaryFamilySpec F hF nSolve j ell Mg CH delta W
        profiles.geometry profiles.host profiles.cutoff phases R Q tau data := by
  obtain ⟨CH,hCH,hpiece⟩ := jointCarrier_mixed_piece_from_raw_uniform (Sub := Pieces)
    (M := M) («Ep» := Ep) (Tr := Tr) (m := m) (N := N) (p := p) (Λ := Λ) (Β := Β)
    nInput nSolve q probeLength Rsub Lprimary hq hbackgroundOrder hprobeOrder
    reserve Bnd Mg Kcut Bchi Bnu Ku Mphase hreserve hBnd hMg hKcut hBchi hBnu hKu hMphase
    weight Tbackground Tprobe Tinv hTbackground hTprobe hTinv
  refine ⟨CH,hCH,?_⟩
  intro F hF g label c chi nu a phase input inputbar u tau ell delta Delta hdelta W primaryDomain K pieceK j profiles
    vf phases R Q
  have hp (rec : Rec) (b : Sub) := hpiece F hF g label c chi nu a phase input inputbar tau ell delta Delta hdelta
    W primaryDomain K pieceK profiles.piece_support profiles.background_carrier j (profiles.geometry rec b) (profiles.host rec b)
    (contMDiffOn_of_mem_maximalAtlas (profiles.host_maximal rec b))
    (contMDiffOn_symm_of_mem_maximalAtlas (profiles.host_maximal rec b))
    (profiles.host_source rec b) rec.val.1.1 rec.val.1.2 rec.val.2
    (profiles.phase_identity rec b)
    (profiles.cutoff rec b ∘ ((OpenPartialHomeomorph.refl Ep).prod (profiles.host rec b)).symm)
    (profiles.cutoff_smooth rec b) (profiles.inverse_smooth rec b)
    (by
      intro y hy hyW hyCut hyPair
      apply profiles.cutoff_support rec b
      refine ⟨?_,hyPair⟩
      rw [parameterRound2_global_relativeSupport_eq W (profiles.background rec b).prim.hW]
      exact ⟨hyW,actual_cutoff_inverse_support_on_target
        ((OpenPartialHomeomorph.refl Ep).prod (profiles.host rec b)) (profiles.cutoff rec b)
        (tsupport (profiles.cutoff rec b)) Subset.rfl y hy hyCut⟩)
    (profiles.background rec b) (profiles.prescribed rec b)
    (profiles.cutoff_jets rec b) (profiles.inverse_jets rec b) u
    (profiles.parameter_smooth rec b) (profiles.parameter_jets rec b)
  choose data hdata using hp
  exact ⟨data,hdata⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.jointCarrier_mixed_family_from_raw_uniform

