import Probes.ActualRawProfileRestriction
import Probes.ActualRawProfileBudgets
import Probes.ActualSecondaryQuadraticConstruction

/-! The actual final-iterate raw profiles on original observers supply the
secondary host consumers on their TRUE inverse-transition samples. There is
no host coefficient or source-output budget premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
variable {m N : ℕ} {Ep M Tr Label SubPrimary Index : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [Fintype SubPrimary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

 theorem actual_final_host_raw_profiles
    (n length j Rsub Lprimary : ℕ) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (observer : Index → OpenPartialHomeomorph M D) (O S : Index → Set X)
    (tau ell Delta : ℝ)
    (data : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary (observer i) (O i) (S i) tau ell Delta)
    (i : Index) (host : OpenPartialHomeomorph M D) (hhost : host = observer i)
    (a : OpenPartialHomeomorph (Ep × M) X) (sample : Set X)
    (hsource : a.source ⊆ ((OpenPartialHomeomorph.refl Ep).prod host).source)
    (hsample : sample ⊆ a.target)
    (hDomain : (((OpenPartialHomeomorph.refl Ep).prod host).symm.trans a).source ⊆ O i)
    (hSamples : (((OpenPartialHomeomorph.refl Ep).prod host).symm.trans a).symm '' sample ⊆ S i) :
    Nonempty (ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary host
      (((OpenPartialHomeomorph.refl Ep).prod host).symm.trans a).source
      ((((OpenPartialHomeomorph.refl Ep).prod host).symm.trans a).symm '' sample) tau ell Delta) := by
  let b := (OpenPartialHomeomorph.refl Ep).prod host
  let t := b.symm.trans a
  have htarget : t.target = a.target := actual_secondary_host_transition_target a b hsource
  have hsTarget : sample ⊆ t.target := by rw [htarget]; exact hsample
  have hsSource : t.symm '' sample ⊆ t.source := by
    rintro z ⟨x,hx,rfl⟩
    exact t.map_target (hsTarget hx)
  have dh : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary host (O i) (S i) tau ell Delta := by
    simpa only [hhost] using data i
  exact ⟨actual_raw_profiles_restrict_observer n length j j Rsub Lprimary le_rfl reserve Bnd Mg T
    F hF g input inputbar W primary host (O i) (S i) t.source (t.symm '' sample) tau ell Delta dh
    t.open_source hDomain hSamples hsSource⟩

 theorem actual_final_observer_raw_profiles
    (n length j j' Rsub Lprimary : ℕ) (hjj : j' ≤ j) (reserve Bnd Mg : ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (N := N) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (observer : Index → OpenPartialHomeomorph M D) (O S : Index → Set X)
    (tau ell Delta : ℝ)
    (data : ∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary (observer i) (O i) (S i) tau ell Delta) :
    Nonempty (∀ i, ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j' Rsub Lprimary reserve Bnd Mg T
      F hF g input inputbar W primary (observer i) (O i) (S i) tau ell Delta) := by
  refine ⟨fun i => ?_⟩
  exact actual_raw_profiles_restrict_observer n length j j' Rsub Lprimary hjj reserve Bnd Mg T
    F hF g input inputbar W primary (observer i) (O i) (S i) (O i) (S i) tau ell Delta (data i)
    (data i).hO (subset_refl _) (subset_refl _) (data i).hSO

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_final_host_raw_profiles
#print axioms GlobalEmbedding.Continuation.actual_final_observer_raw_profiles
