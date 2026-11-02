import NormalPolar.PassiveRawBudget

/-! Reduce only the observed joint derivative order of the same actual
background raw profile. The higher input order, length, true family,
primitives, samples and every numerical budget remain unchanged. -/

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

variable {n length j Rsub Lprimary : ℕ} {reserve Bnd Mg : ℝ} {T : ℕ → ℝ}
  {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F}
  {input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
  {W : Set (Ep × M)} {primary : Λ → Set (Ep × M)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1)))}
  {O S : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))} {tau ell Delta : ℝ}

def ParameterRound2GlobalMeanRawProfiles.lowerJointOrder
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta)
    (k : ℕ) (hk : k ≤ j) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length k Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta :=
  { raw with
    hGb := fun nu a r hr z hz => raw.hGb nu a r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hJb := fun nu a r hr z hz => raw.hJb nu a r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hTb := fun nu a r hr z hz => raw.hTb nu a r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hphib := fun nu a r hr hrk z hz => raw.hphib nu a r hr (hrk.trans (Nat.add_le_add_right hk 1)) z hz
    hLobsb := fun nu r hr z hz => raw.hLobsb nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hAobsb := fun nu r hr z hz => raw.hAobsb nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hAbarobsb := fun nu r hr z hz => raw.hAbarobsb nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hCutobsb := fun nu r hr z hz => raw.hCutobsb nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hNormalobsb := fun nu r hr z hz => raw.hNormalobsb nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz
    hGradobsb := fun nu a r hr z hz => raw.hGradobsb nu a r (hr.trans hk) z hz
    hDiffobs := fun nu r hr z hz => raw.hDiffobs nu r (hr.trans (Nat.add_le_add_right hk 1)) z hz }

theorem ParameterRound2GlobalMeanRawProfiles.lowerJointOrder_literal
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta)
    (k : ℕ) (hk : k ≤ j) :
    let out := raw.lowerJointOrder k hk
    out.Omega = raw.Omega ∧ out.U = raw.U ∧ out.Sloc = raw.Sloc ∧
      out.L = raw.L ∧ out.A = raw.A ∧ out.Abar = raw.Abar ∧
      out.Lobs = raw.Lobs ∧ out.Aobs = raw.Aobs ∧ out.Abarobs = raw.Abarobs :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ParameterRound2GlobalMeanRawProfiles.lowerJointOrder
#print axioms GlobalEmbedding.Continuation.ParameterRound2GlobalMeanRawProfiles.lowerJointOrder_literal
