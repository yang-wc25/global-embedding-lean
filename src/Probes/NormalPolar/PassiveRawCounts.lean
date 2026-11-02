import NormalPolar.PassiveRawBudget
import Smoothing.Round3ParameterCanonicalMeanReserveSupply

/-! Larger bookkeeping multiplicities for the same original raw family.
Only the two count inequalities change. Original labels, partitions,
cutoffs, domains, inputs and every raw budget stay literal. The same
operation applies to the actual canonical reserve supplier. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation

section Local
variable {E H M Ep Tr : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  {m N : ℕ} {Λ Β : Type*} [Fintype Λ] [Fintype Β]
variable {n length j Rsub Lprimary : ℕ} {reserve Bnd Mg : ℝ} {T : ℕ → ℝ}
  {F : Ep → M → EuclideanSpace ℝ (Fin N)}
  {hF : ∀ p, ContMDiff I 𝓘(ℝ,EuclideanSpace ℝ (Fin N)) ∞ (F p)}
  {g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F}
  {input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x)}
  {W : Set (Ep × M)} {primary : Λ → Set (Ep × M)}
  {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (m+1)))}
  {O S : Set (Ep × EuclideanSpace ℝ (Fin (m+1)))} {tau ell Delta : ℝ}

def ParameterRound2GlobalMeanRawProfiles.enlargeCounts
    (raw : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta)
    (R L : ℕ) (hR : Rsub ≤ R) (hL : Lprimary ≤ L) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j R L
      reserve Bnd Mg T F hF g input inputbar W primary e O S tau ell Delta :=
  { raw with
    hRsub := fun nu z hz => (raw.hRsub nu z hz).trans hR
    hCount := fun z hz => (raw.hCount z hz).trans hL }
end Local

variable {m d N c : ℕ} {M P Tr Λ Β : Type*}
  [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "IM" => 𝓘(ℝ,D)

def Round3ParameterMeanRawAtlasData.enlargeCounts
    {A : BufferedAtlas M D} {B : Fin c → OpenPartialHomeomorph P Ep}
    {F : P → M → V} {hF : ∀ p, ContMDiff IM 𝓘(ℝ,V) ∞ (F p)}
    {g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F}
    {input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x)}
    {n q j Rsub Lprimary : ℕ} {reserve Bnd Mg : ℝ} {T : ℕ → ℝ}
    {W : Set (P × M)} {primary : Λ → Set (P × M)}
    {S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)} {tau ell Delta : ℝ}
    (raw : Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF g input inputbar
      n q j Rsub Lprimary reserve Bnd Mg T W primary S tau ell Delta)
    (R L : ℕ) (hR : Rsub ≤ R) (hL : Lprimary ≤ L) :
    Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF g input inputbar
      n q j R L reserve Bnd Mg T W primary S tau ell Delta where
  observationDomain := raw.observationDomain
  target := raw.target
  raw := fun i => (raw.raw i).enlargeCounts R L hR hL

set_option backward.isDefEq.respectTransparency false in
theorem round3Parameter_canonical_supply_enlarge_counts
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ)) (W : Set (P × M))
    (p : ℕ → Seminorm ℝ (parameterRound2_originalTensorGermSpace A B S W))
    (H : parameterRound2_originalTensorGermSpace A B S W) (rho : ℝ)
    (q Rsub Lprimary : ℕ) (reserve : ℝ)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ) (T : ℕ → ℝ)
    (F : P → M → V) (hF : ∀ t, ContMDiff IM 𝓘(ℝ,V) ∞ (F t))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (primary : Λ → Set (P × M)) (ell : ℝ)
    (supply : Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S W p H rho
      q Rsub Lprimary reserve Bnd Mg Dinput T F hF g primary ell)
    (R L : ℕ) (hR : Rsub ≤ R) (hL : Lprimary ≤ L) :
    Round3ParameterCanonicalMeanRawReserveSupply (Tr := Tr) A B S W p H rho
      q R L reserve Bnd Mg Dinput T F hF g primary ell := by
  intro epsilon he he1 s bound K L' hK hL'
  have hr : ∃ raw : Round3ParameterMeanRawAtlasData (Tr := Tr) A B F hF
      (round3Parameter_restrictPrimaryFamily F g univ isOpen_univ) K.val.val L'.val.val
      (s+(q+4)) q s Rsub Lprimary reserve (Bnd s bound) (Mg s) T
      univ primary S (epsilon*ell) ell (Dinput s*p (s+(q+4)) (K.val-L'.val)),
      raw.observationDomain = fun i => actualRawObserverOpen (A.chart i.1)
        (round3ParameterNativeDomain (B i.2) (univ : Set (P × M))) :=
    supply epsilon he he1 s bound K L' hK hL'
  rcases hr with ⟨raw,hDom⟩
  exact ⟨raw.enlargeCounts R L hR hL,hDom⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.ParameterRound2GlobalMeanRawProfiles.enlargeCounts
#print axioms GlobalEmbedding.Continuation.round3Parameter_canonical_supply_enlarge_counts
