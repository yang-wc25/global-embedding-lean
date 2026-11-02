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

def actual_raw_profiles_enlarge_budgets
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg Bnd' Mg' : ℝ) (T : ℕ → ℝ)
    (hBnd : Bnd ≤ Bnd') (hMg : Mg ≤ Mg')
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (data : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd' Mg' T
      F hF g input inputbar W primary e O S tau ell Delta :=
  { data with
    hBRb := fun ν β k hk z hz => (data.hBRb ν β k hk z hz).trans hBnd
    hLb := fun ν β k hk z hz => (data.hLb ν β k hk z hz).trans hBnd
    hInputb := fun ν β k hk z hz => (data.hInputb ν β k hk z hz).trans hBnd
    hInputbarb := fun ν β k hk z hz => (data.hInputbarb ν β k hk z hz).trans hBnd
    hCutb := fun ν β k hk z hz => (data.hCutb ν β k hk z hz).trans hBnd
    hEtab := fun ν β k hk z hz => (data.hEtab ν β k hk z hz).trans hBnd
    hNormalb := fun ν β k hk z hz => (data.hNormalb ν β k hk z hz).trans hBnd
    hAb := fun ν β k hk z hz => (data.hAb ν β k hk z hz).trans hMg
    hBb := fun ν β k hk z hz => (data.hBb ν β k hk z hz).trans hMg
    hGb := fun ν β k hk z hz => (data.hGb ν β k hk z hz).trans hMg
    hJb := fun ν β k hk z hz => (data.hJb ν β k hk z hz).trans hMg
    hTb := fun ν β k hk z hz => (data.hTb ν β k hk z hz).trans hMg
    hLobsb := fun ν k hk z hz => (data.hLobsb ν k hk z hz).trans hBnd
    hAobsb := fun ν k hk z hz => (data.hAobsb ν k hk z hz).trans hBnd
    hAbarobsb := fun ν k hk z hz => (data.hAbarobsb ν k hk z hz).trans hBnd
    hCutobsb := fun ν k hk z hz => (data.hCutobsb ν k hk z hz).trans hBnd
    hNormalobsb := fun ν k hk z hz => (data.hNormalobsb ν k hk z hz).trans hBnd
    hGradobsb := fun ν r k hk z hz => (data.hGradobsb ν r k hk z hz).trans hBnd }

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_raw_profiles_enlarge_budgets
