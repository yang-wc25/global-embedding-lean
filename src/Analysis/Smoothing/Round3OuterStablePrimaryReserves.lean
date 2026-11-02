import Smoothing.Round3OuterStablePrimaryFamily

/-! Actual first, transverse and projected-normal reserves on every label
of the one whole-parameter Sigma family. The bounds come from the original
reference C2 stability theorem; inactive labels have empty true domains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
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
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}

theorem round3_stable_primary_sigma_reserves
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3ParameterWholePrimaryPieceSupply Ref theta)
    (profiles : Round3ParameterWholeReferenceProfiles Ref hd hs theta packet)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : Round3ParameterWholeStableReference Ref hd hs theta packet profiles F hF) :
    let out := round3ParameterWholePrimaryPiece Ref hd theta
      (round3OuterStablePrimaryPacket Ref hd hs theta packet profiles F hF stable)
    (∀ nu a y, y ∈ (actualHostAdaptedChart (Ref.atlas.chart (out nu a).host) (out nu a).native).source →
      y.2 ∈ Ref.atlas.inner (out nu a).host) ∧
    (∀ nu a z, z ∈ (out nu a).native.target → ∀ v : D,
      (profiles.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ (F ((Ref.parameterChart a.1.2).symm z.1) ∘
        ((out nu a).slices z.1).symm) z.2 v‖^2) ∧
    (∀ nu a z, z ∈ (out nu a).native.target → ∀ v : Tdata,
      (profiles.cT/16)*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame
        (F ((Ref.parameterChart a.1.2).symm z.1)) (hF ((Ref.parameterChart a.1.2).symm z.1))
        ((out nu a).slices z.1).symm z.2 v‖^2) ∧
    (∀ nu a z, z ∈ (out nu a).native.target → (1/4 : ℝ) ≤
      ‖actualFreeNormalProjectionRaw
        (fderiv ℝ (F ((Ref.parameterChart a.1.2).symm z.1) ∘ ((out nu a).slices z.1).symm) z.2)
        (incrementsModeAmbientTransverseFrame
          (F ((Ref.parameterChart a.1.2).symm z.1)) (hF ((Ref.parameterChart a.1.2).symm z.1))
          ((out nu a).slices z.1).symm z.2)
        (Ref.freeNormal nu ((Ref.parameterChart a.1.2).symm z.1,((out nu a).slices z.1).symm z.2))‖) := by
  intro out
  have hInner (nu) (i) (a : packet.s nu i) (y : Ep × M)
      (hy : y ∈ (actualHostAdaptedChart (Ref.atlas.chart (stable.piece nu i a).host) (stable.piece nu i a).native).source) :
      y.2 ∈ Ref.atlas.inner (stable.piece nu i a).host := by
    rw [stable.host] at hy ⊢
    exact profiles.source_inner nu i a y ⟨hy.1,stable.source_subset nu i a hy.2⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro nu a y hy
    rcases a with ⟨i,mu,a⟩
    by_cases h : mu = nu
    · subst mu
      simp only [out,round3ParameterWholePrimaryPiece,round3OuterStablePrimaryPacket,
        Round3ParameterWholePrimaryPieceSupply.replacePieces,round3PreparedPrimarySigmaPiece,
        dif_pos rfl] at hy ⊢
      exact hInner nu i a y hy
    · simp only [out,round3ParameterWholePrimaryPiece,round3OuterStablePrimaryPacket,
        Round3ParameterWholePrimaryPieceSupply.replacePieces,round3PreparedPrimarySigmaPiece,h,dite_false] at hy
      have he : (round3PreparedPrimaryEmpty Ref hd i nu
          ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))).native.source = ∅ :=
        round3PreparedEmptyNativeChart_source
      exact (he ▸ hy.2 : (y.1,Ref.atlas.chart i.1 y.2) ∈ (∅ : Set (Ep × D))).elim
  all_goals
    intro nu a z hz
    rcases a with ⟨i,mu,a⟩
    by_cases h : mu = nu
    · subst mu
      simp only [out,round3ParameterWholePrimaryPiece,round3OuterStablePrimaryPacket,
        Round3ParameterWholePrimaryPieceSupply.replacePieces,round3PreparedPrimarySigmaPiece,
        dif_pos rfl] at hz ⊢
      first | exact stable.first nu i a z hz | exact stable.transverse nu i a z hz | exact stable.normal nu i a z hz
    · simp only [out,round3ParameterWholePrimaryPiece,round3OuterStablePrimaryPacket,
        Round3ParameterWholePrimaryPieceSupply.replacePieces,round3PreparedPrimarySigmaPiece,h,dite_false] at hz
      have he : (round3PreparedPrimaryEmpty Ref hd i nu
          ((Ref.parameterChart i.2).target ×ˢ (univ : Set M))).native.target = ∅ :=
        round3PreparedEmptyNativeChart_target
      exact (he ▸ hz : z ∈ (∅ : Set (Ep × D))).elim

#print axioms round3_stable_primary_sigma_reserves
end GlobalEmbedding.Continuation
