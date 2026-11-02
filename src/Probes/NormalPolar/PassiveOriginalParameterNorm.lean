import NormalPolar.PassiveOriginalInjectedNorm
import NormalPolar.PassiveOriginalTransitionBinding

/-! Constant-one partial-norm transport for the parameter block, in the
unchanged source-first Pi coordinates. Spatial coordinates are passive for
this block, and the native parameter coordinate order is retained. -/

noncomputable section
open Set Function GlobalEmbedding.Paper
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation

def passiveOriginalParameterIndex (n d : ℕ) : Fin d ↪ Fin (n+d) where
  toFun := Fin.natAdd n
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega

theorem passiveOriginalParameterIndex_strictMono (n d : ℕ) :
    StrictMono (passiveOriginalParameterIndex n d) := by
  intro i j hij
  change n+i.val < n+j.val
  exact Nat.add_lt_add_left hij n

theorem passiveOriginal_parameter_paperCoordinateCj_le {n d q : ℕ} (j : ℕ)
    (f : (Fin d → ℝ) → Fin q → ℝ) (O S : Set (Fin d → ℝ)) (hO : IsOpen O)
    (D T : Set (Fin (n+d) → ℝ)) (hD : IsOpen D)
    (hDO : MapsTo (passiveOriginalParameterProjection (n := n)) D O)
    (hTD : T ⊆ D) (hTS : MapsTo (passiveOriginalParameterProjection (n := n)) T S) :
    paperCoordinateCj j (f ∘ passiveOriginalParameterProjection (n := n)) D T ≤
      paperCoordinateCj j f O S :=
  passiveOriginal_injected_paperCoordinateCj_le (passiveOriginalParameterIndex n d)
    (passiveOriginalParameterIndex_strictMono n d) j f O S hO D T hD hDO hTD hTS

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.passiveOriginal_parameter_paperCoordinateCj_le
