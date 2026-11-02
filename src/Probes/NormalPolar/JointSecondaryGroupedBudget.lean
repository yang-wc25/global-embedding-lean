import NormalPolar.JointSecondaryGroupedProfiles

/-! Place independently constructed primitive budgets under one common
positive bound. The actual raw functions, entire support, differentiation
domain and sample stay literally the same, including the full-target BR,
cutoff and normal budgets. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open Set Function Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {m N r : ℕ} {Sub : Fin r → Type*} [∀ l, Fintype (Sub l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

def ActualPrescribedSpatialRawProfiles.enlargeBudgets
    {F : Ep → M → V} {hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)}
    {c : Ep → D → M} {chi : X → ℝ}
    {nu : (b : Ep) → (x : D) → normalSpace (I := I) (F b) (c b x)}
    {a : OpenPartialHomeomorph (Ep × M) X} {W K : Set (Ep × M)}
    {n j : ℕ} {ell Mg Bchi Bnu : ℝ}
    (raw : ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg Bchi Bnu)
    (Mg' Bchi' Bnu' : ℝ) (hMg : Mg ≤ Mg') (hChi : Bchi ≤ Bchi') (hNu : Bnu ≤ Bnu') :
    ActualPrescribedSpatialRawProfiles F hF c chi nu a W K n j ell Mg' Bchi' Bnu' :=
  { raw with
    A_jets := fun k hk z hz => (raw.A_jets k hk z hz).trans hMg
    B_jets := fun k hk z hz => (raw.B_jets k hk z hz).trans hMg
    G_jets := fun k hk z hz => (raw.G_jets k hk z hz).trans hMg
    J_jets := fun k hk z hz => (raw.J_jets k hk z hz).trans hMg
    T_jets := fun k hk z hz => (raw.T_jets k hk z hz).trans hMg
    BR_jets := fun k hk z hz => (raw.BR_jets k hk z hz).trans hMg
    cutoff_jets := fun k hk z hz => (raw.cutoff_jets k hk z hz).trans hChi
    normal_jets := fun k hk z hz => (raw.normal_jets k hk z hz).trans hNu }

def JointGroupedPrescribedObservationProfiles.enlargeBudgets
    {F : Ep → M → V} {hF : ∀ b, ContMDiff I 𝓘(ℝ,V) ∞ (F b)}
    {c : (l : Fin r) → Sub l → Ep → D → M}
    {chi : (l : Fin r) → Sub l → X → ℝ}
    {nu : (l : Fin r) → (s : Sub l) → (b : Ep) → (x : D) →
      normalSpace (I := I) (F b) (c l s b x)}
    {a : (l : Fin r) → Sub l → OpenPartialHomeomorph (Ep × M) X}
    {W : Set (Ep × M)} {pieceK : (l : Fin r) → Sub l → Set (Ep × M)}
    {n j : ℕ} {ell Mg Bchi Bnu : ℝ}
    {kappa : Y → Ep × M} {Omega S : Set Y} {T : ℕ → ℝ}
    {phase : Fin r → Ep × M → ℝ} {Mphase : ℝ}
    (raw : JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
      n j ell Mg Bchi Bnu kappa Omega S T phase Mphase)
    (Mg' Bchi' Bnu' Mphase' : ℝ) (T' : ℕ → ℝ)
    (hMg : Mg ≤ Mg') (hChi : Bchi ≤ Bchi') (hNu : Bnu ≤ Bnu')
    (hPhase : Mphase ≤ Mphase') (hT : ∀ k, T k ≤ T' k) :
    JointGroupedPrescribedObservationProfiles F hF c chi nu a W pieceK
      n j ell Mg' Bchi' Bnu' kappa Omega S T' phase Mphase' where
  raw := fun l s => (raw.raw l s).enlargeBudgets Mg' Bchi' Bnu' hMg hChi hNu
  domains := raw.domains
  domains_open := raw.domains_open
  active_domain := raw.active_domain
  source := raw.source
  transition_smooth := raw.transition_smooth
  sample := raw.sample
  transition_jets := fun l s k hk hkj z hz => (raw.transition_jets l s k hk hkj z hz).trans (hT k)
  phase_smooth := raw.phase_smooth
  phase_jets := fun l s k hkj z hz => (raw.phase_jets l s k hkj z hz).trans hPhase

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ActualPrescribedSpatialRawProfiles.enlargeBudgets
#print axioms GlobalEmbedding.Continuation.JointGroupedPrescribedObservationProfiles.enlargeBudgets
