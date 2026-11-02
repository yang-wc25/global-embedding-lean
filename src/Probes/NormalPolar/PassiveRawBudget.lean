import Smoothing.ParameterRound2MeanRawProfiles

/-! Common primitive budgets for the same actual raw background. This
operation changes only bound proofs; all fields, true domains, sampling,
reserves, actual inputs and derivative scales remain literal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper Set Function Manifold
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

variable {n length j Rsub Lprimary : ℕ} {reserve Bnd Mg : ℝ} {T : ℕ → ℝ}
  {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F}
  {input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
  {W : Set (Ep × M)} {primary : Λ → Set (Ep × M)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1)))}
  {O S : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))} {tau ell Delta : ℝ}

def ParameterRound2GlobalMeanRawProfiles.enlargeBudgets
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta)
    (Bnd' Mg' : ℝ) (T' : ℕ → ℝ)
    (hBnd : Bnd ≤ Bnd') (hMg : Mg ≤ Mg') (hT : ∀ k, T k ≤ T' k) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd' Mg' T' F hF g input inputbar W primary e O S tau ell Delta :=
  { raw with
    hBRb := fun nu a k hk z hz => (raw.hBRb nu a k hk z hz).trans hBnd
    hLb := fun nu a k hk z hz => (raw.hLb nu a k hk z hz).trans hBnd
    hInputb := fun nu a k hk z hz => (raw.hInputb nu a k hk z hz).trans hBnd
    hInputbarb := fun nu a k hk z hz => (raw.hInputbarb nu a k hk z hz).trans hBnd
    hCutb := fun nu a k hk z hz => (raw.hCutb nu a k hk z hz).trans hBnd
    hEtab := fun nu a k hk z hz => (raw.hEtab nu a k hk z hz).trans hBnd
    hNormalb := fun nu a k hk z hz => (raw.hNormalb nu a k hk z hz).trans hBnd
    hAb := fun nu a k hk z hz => (raw.hAb nu a k hk z hz).trans hMg
    hBb := fun nu a k hk z hz => (raw.hBb nu a k hk z hz).trans hMg
    hGb := fun nu a k hk z hz => (raw.hGb nu a k hk z hz).trans hMg
    hJb := fun nu a k hk z hz => (raw.hJb nu a k hk z hz).trans hMg
    hTb := fun nu a k hk z hz => (raw.hTb nu a k hk z hz).trans hMg
    hphib := fun nu a k hk hkj z hz => (raw.hphib nu a k hk hkj z hz).trans (hT k)
    hLobsb := fun nu k hk z hz => (raw.hLobsb nu k hk z hz).trans hBnd
    hAobsb := fun nu k hk z hz => (raw.hAobsb nu k hk z hz).trans hBnd
    hAbarobsb := fun nu k hk z hz => (raw.hAbarobsb nu k hk z hz).trans hBnd
    hCutobsb := fun nu k hk z hz => (raw.hCutobsb nu k hk z hz).trans hBnd
    hNormalobsb := fun nu k hk z hz => (raw.hNormalobsb nu k hk z hz).trans hBnd
    hGradobsb := fun nu a k hk z hz => (raw.hGradobsb nu a k hk z hz).trans hBnd }

theorem ParameterRound2GlobalMeanRawProfiles.enlargeBudgets_literal
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta)
    (Bnd' Mg' : ℝ) (T' : ℕ → ℝ)
    (hBnd : Bnd ≤ Bnd') (hMg : Mg ≤ Mg') (hT : ∀ k, T k ≤ T' k) :
    let out := raw.enlargeBudgets Bnd' Mg' T' hBnd hMg hT
    out.Omega = raw.Omega ∧ out.U = raw.U ∧ out.Sloc = raw.Sloc ∧
      out.L = raw.L ∧ out.A = raw.A ∧ out.Abar = raw.Abar ∧
      out.Lobs = raw.Lobs ∧ out.Aobs = raw.Aobs ∧ out.Abarobs = raw.Abarobs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ParameterRound2GlobalMeanRawProfiles.enlargeBudgets
#print axioms GlobalEmbedding.Continuation.ParameterRound2GlobalMeanRawProfiles.enlargeBudgets_literal
