import Smoothing.ParameterRound2MeanRawProfiles

/-! Restrict actual primitive profiles to a proved smaller observer domain
and sampling set, keeping the SAME fields, source, finite polynomial and
budgets. This supplies host and lower-order observer consumers from one
actual final-iterate producer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D

 def actual_raw_profiles_restrict_observer
    (n length j j' Rsub Lprimary : ℕ) (hjj : j' ≤ j) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S O' S' : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta)
    (hO' : IsOpen O') (hO'O : O' ⊆ O) (hS'S : S' ⊆ S) (hS'O' : S' ⊆ O') :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j' Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary e O' S' tau ell Delta where
  prim := data.prim
  primbar := data.primbar
  hO := hO'
  hSO := hS'O'
  hkappaO := data.hkappaO.mono hO'O
  hmapWO := fun z hz => data.hmapWO (hO'O hz)
  Omega := data.Omega
  U := data.U
  Sloc := data.Sloc
  hOmega := data.hOmega
  hSOmega := fun ν z hz => data.hSOmega ν ⟨hS'S hz.1,hz.2⟩
  hkappa := data.hkappa
  hmapW := data.hmapW
  hU := data.hU
  hOU := data.hOU
  hSloc := data.hSloc
  hsource := data.hsource
  hphi := data.hphi
  hmap := fun ν β z hz => data.hmap ν β ⟨⟨hS'S hz.1.1,hz.1.2⟩,hz.2⟩
  htau := data.htau
  htaul := data.htaul
  hell1 := data.hell1
  hDelta := data.hDelta
  L := data.L
  A := data.A
  Abar := data.Abar
  hL := data.hL
  hInput := data.hInput
  hInputbar := data.hInputbar
  hRep := data.hRep
  hRepbar := data.hRepbar
  hCut := data.hCut
  hEta := data.hEta
  hNormal := data.hNormal
  hBR := data.hBR
  hReserve := data.hReserve
  hBRb := data.hBRb
  hLb := data.hLb
  hInputb := data.hInputb
  hInputbarb := data.hInputbarb
  hCutb := data.hCutb
  hEtab := data.hEtab
  hNormalb := data.hNormalb
  hDiff := data.hDiff
  hAb := data.hAb
  hBb := data.hBb
  hGb := fun ν β k hk => data.hGb ν β k (hk.trans (Nat.add_le_add_right hjj 1))
  hJb := fun ν β k hk => data.hJb ν β k (hk.trans (Nat.add_le_add_right hjj 1))
  hTb := fun ν β k hk => data.hTb ν β k (hk.trans (Nat.add_le_add_right hjj 1))
  hphib := fun ν β k hk hk' z hz => data.hphib ν β k hk (hk'.trans (Nat.add_le_add_right hjj 1))
    z ⟨⟨hS'S hz.1.1,hz.1.2⟩,hz.2⟩
  hRsub := fun ν z hz => data.hRsub ν z ⟨hS'S hz.1,hz.2⟩
  Lobs := data.Lobs
  Aobs := data.Aobs
  Abarobs := data.Abarobs
  hLobs := data.hLobs
  hAobs := data.hAobs
  hAbarobs := data.hAbarobs
  hRepobs := data.hRepobs
  hRepbarobs := data.hRepbarobs
  hCutobs := data.hCutobs
  hNormalobs := data.hNormalobs
  hPhaseobs := data.hPhaseobs
  hReserveobs := fun ν z hz => data.hReserveobs ν z ⟨hS'S hz.1,hz.2⟩
  hLobsb := fun ν k hk z hz => data.hLobsb ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hAobsb := fun ν k hk z hz => data.hAobsb ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hAbarobsb := fun ν k hk z hz => data.hAbarobsb ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hCutobsb := fun ν k hk z hz => data.hCutobsb ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hNormalobsb := fun ν k hk z hz => data.hNormalobsb ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hGradobsb := fun ν r k hk z hz => data.hGradobsb ν r k (hk.trans hjj) z ⟨hS'S hz.1,hz.2⟩
  hDiffobs := fun ν k hk z hz => data.hDiffobs ν k (hk.trans (Nat.add_le_add_right hjj 1)) z ⟨hS'S hz.1,hz.2⟩
  hCover := fun ν z hz => data.hCover ν ⟨hO'O hz.1,hz.2⟩
  hPositiveCover := fun ν z hz => data.hPositiveCover ν z ⟨hO'O hz.1,hz.2⟩
  hCount := fun z hz => data.hCount z (hS'S hz)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_raw_profiles_restrict_observer
