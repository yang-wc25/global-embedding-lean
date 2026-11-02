import Smoothing.ParameterRound2MeanRawProfiles

/-! The primary open domains can be fixed independently of the input-dependent
positive neighborhood. Intersecting the primary domain with that neighborhood
inside a primitive record changes none of its actual functions or estimates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
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

theorem parameterRound2_mean_primitives_fixed_primary
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (hprimary : ∀ nu, IsOpen (primary nu))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W (fun nu => W ∩ primary nu)) :
    ParameterRound2GlobalMeanPrimitives F hF g input W primary := by
  refine { h with
    hPrimary := hprimary
    hPrimarySupport := fun nu z hz => (h.hPrimarySupport nu hz).2
    hSourceW := fun nu beta z hz => ⟨(h.hSourceW nu beta hz).1,(h.hSourceW nu beta hz).2.2⟩
    hPhase := ?_
    hCut := ?_
    hNormal := ?_
    hArgument := ?_ }
  · intro nu
    simpa only [← inter_assoc,inter_self] using h.hPhase nu
  · intro nu
    simpa only [← inter_assoc,inter_self] using h.hCut nu
  · intro nu
    simpa only [← inter_assoc,inter_self] using h.hNormal nu
  · intro nu
    simpa only [← inter_assoc,inter_self] using h.hArgument nu

theorem parameterRound2_mean_primitives_inter_primary
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (h : ParameterRound2GlobalMeanPrimitives F hF g input W primary) :
    ParameterRound2GlobalMeanPrimitives F hF g input W (fun nu => W ∩ primary nu) := by
  refine { h with
    hPrimary := fun nu => h.hW.inter (h.hPrimary nu)
    hPrimarySupport := ?_
    hSourceW := fun nu beta z hz =>
      ⟨(h.hSourceW nu beta hz).1,(h.hSourceW nu beta hz).1,(h.hSourceW nu beta hz).2⟩
    hPhase := fun nu => (h.hPhase nu).mono (fun z hz => ⟨hz.1,hz.2.2⟩)
    hCut := fun nu => (h.hCut nu).mono (fun z hz => ⟨hz.1,hz.2.2⟩)
    hNormal := fun nu => (h.hNormal nu).mono (fun z hz => ⟨hz.1,hz.2.2⟩)
    hArgument := fun nu => (h.hArgument nu).mono (fun z hz => ⟨hz.1,hz.2.2⟩) }
  intro nu z hz
  refine ⟨?_,h.hPrimarySupport nu hz⟩
  rcases hz with ⟨w,hw,rfl⟩
  exact w.property

def parameterRound2_raw_profiles_fixed_primary
    (n length j Rsub Lprimary : ℕ) (c Bnd Mg : ℝ) (T : ℕ → ℝ)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff I 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := I) (m := m) (N := N) (Λ := Λ) (Β := Β) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace I x))
    (W : Set (Ep × M)) (primary : Λ → Set (Ep × M))
    (hprimary : ∀ nu, IsOpen (primary nu))
    (e : OpenPartialHomeomorph M D) (O S : Set X) (tau ell Delta : ℝ)
    (h : ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W (fun nu => W ∩ primary nu) e O S tau ell Delta) :
    ParameterRound2GlobalMeanRawProfiles (Tr := Tr) n length j Rsub Lprimary c Bnd Mg T
      F hF g input inputbar W primary e O S tau ell Delta := by
  exact { h with
    prim := parameterRound2_mean_primitives_fixed_primary F hF g input W primary hprimary h.prim
    primbar := parameterRound2_mean_primitives_fixed_primary F hF g inputbar W primary hprimary h.primbar }

#print axioms parameterRound2_mean_primitives_inter_primary
#print axioms parameterRound2_mean_primitives_fixed_primary
#print axioms parameterRound2_raw_profiles_fixed_primary
end GlobalEmbedding.Continuation
