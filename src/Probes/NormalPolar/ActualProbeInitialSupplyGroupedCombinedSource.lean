import NormalPolar.ActualProbeInitialSupplyGroupedSource
import NormalPolar.ActualProbeInitialSupplyGroupedPrimary

/-!
# One complete physical first increment in every original parameter chart

The same parameter is substituted into the primary before constructing the
negative quadratic secondary forcing. The literal original choices are
pulled back once. The whole primary plus every signed subordinate secondary
piece is then exactly one fixed global function; all native joint jets agree
on every true open observation domain. No final map or derivative estimate
is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m N p r : ℕ} {M P Ep Λ Β Sub : Type*}
  [TopologicalSpace P] [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype Sub]
  {Pieces : Fin r → Type*} [∀ l, Fintype (Pieces l)]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "IM" => 𝓘(ℝ,D)

local notation "Rec" => ActualSecondarySignedRecord (Λ ⊕ Fin r)

theorem actualProbeInitialSupply_grouped_combined_source_pullback
    (F : P → M → V) (hF : ∀ b, ContMDiff IM 𝓘(ℝ,V) ∞ (F b))
    (g : Round3ParameterPrimaryFamily (I := IM) (m := m) (Λ := Λ) (Β := Β) F)
    (label : (Fin r × Bool) ↪ Fin p)
    (c : (l : Fin r) → Pieces l → P → D → M)
    (vf : (l : Fin r) → (s : Pieces l) → (b : P) → (x : D) → normalSpace (I := IM) (F b) (c l s b x))
    (phase : Fin r → P × M → ℝ) (tau delta : ℝ) (backgroundLength probeLength length : ℕ)
    (a : (l : Fin r) → Pieces l → OpenPartialHomeomorph (P × M) (P × D))
    (input : (b : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IM x))
    (u : P → Fin p → ℝ)
    (B : OpenPartialHomeomorph P Ep)
    (hg : ∀ l b, Round3ParameterChartPreserves (g.chart l b))
    (ha : ∀ l s, Round3ParameterChartPreserves (a l s))
    (choice : Rec → Sub → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ rec b, Round3ParameterChartPreserves (choice rec b).chart)
    (n j : ℕ) (ell Mg : ℝ) (W : Set (Ep × M))
    (geometry : Rec → Sub → ActualSecondaryRawGeometry
      (fun t => F (B.symm t)) (fun t => hF (B.symm t)) n j ell Mg W)
    (host : Rec → Sub → OpenPartialHomeomorph M D) (cutoff : Rec → Sub → Ep × M → ℝ)
    (hchoice : ∀ rec b,
      ({host := host rec b,chart := (geometry rec b).chart,c := (geometry rec b).c,
        cutoff := cutoff rec b} : Round3ParameterSecondaryChoice Ep M m) = (choice rec b).pullback B) :
    let amplitude := actualProbeInitialGroupedAmplitude F hF g label c vf
      tau delta backgroundLength probeLength a input u
    let source := fun rec b => actualParameterSecondarySourceOfPrimary (Sum.elim g.phase phase)
      (amplitude false) (amplitude true) tau rec.val (choice rec b) (hc rec b)
    let U := fun z => actualProbeInitialGroupedPrimary F hF g label c vf phase
      tau delta backgroundLength probeLength a input u z +
      actualParameterSecondarySourceSum F hF source tau length z
    let Fbar := fun t => F (B.symm t)
    let hFbar := fun t => hF (B.symm t)
    let gbar := (round3ParameterPrimaryPullback F g B).toNative Fbar
    let cbar := fun l s t => c l s (B.symm t)
    let vfbar := fun l s t => vf l s (B.symm t)
    let abar := fun l s => round3ParameterChartPullback B (a l s)
    let phasebar := fun l z => phase l (B.symm z.1,z.2)
    let phases := Sum.elim gbar.phase phasebar
    let nativeAmplitude := jointGroupedCombinedAmplitude Fbar hFbar gbar label cbar vfbar
      tau delta backgroundLength probeLength abar (fun t => input (B.symm t)) (fun t => u (B.symm t))
    let nativeSource := fun rec b => jointSecondarySourceOfRawGeometry Fbar hFbar n j ell Mg W
      (geometry rec b) (host rec b) (cutoff rec b)
      phases (nativeAmplitude false) (nativeAmplitude true) tau rec.val
    let nativeU := fun z => jointGroupedCombinedPrimary Fbar hFbar gbar label cbar vfbar
      phasebar tau delta backgroundLength probeLength abar (fun t => input (B.symm t))
      (u (B.symm z.1)) z + actualParameterSecondarySourceSum Fbar hFbar nativeSource tau length z
    (∀ b ∈ B.target, ∀ x, nativeU (b,x) = U (B.symm b,x)) ∧
    ∀ (e : OpenPartialHomeomorph M D) (O : Set X), IsOpen O →
      (∀ z ∈ O, z.1 ∈ B.target) →
      ∀ k z, z ∈ O →
        iteratedFDeriv ℝ k (fun y : X => nativeU (y.1,e.symm y.2)) z =
          iteratedFDeriv ℝ k (fun y : X => U (B.symm y.1,e.symm y.2)) z := by
  intro amplitude source U Fbar hFbar gbar cbar vfbar abar phasebar phases nativeAmplitude nativeSource nativeU
  have hbinding (rec : Rec) (b : Sub) : ActualProbeInitialSourcePullbackBinding B
      (source rec b) (nativeSource rec b) := by
    exact actualProbeInitialSupply_grouped_secondary_binding F hF g label c vf phase tau delta
      backgroundLength probeLength a input u B hg ha rec.val (choice rec b) (hc rec b)
      n j ell Mg W (geometry rec b) (host rec b) (cutoff rec b) (hchoice rec b)
  have heq : ∀ b ∈ B.target, ∀ x, nativeU (b,x) = U (B.symm b,x) := by
    intro b hb x
    have hp := actualProbeInitialSupply_grouped_primary_pullback F hF g label c vf phase tau delta
      backgroundLength probeLength a input u B hg ha b hb x
    have hs := actualProbeInitialSupply_secondary_sum_pullback_of_binding F hF source nativeSource B
      hbinding tau length b hb x
    exact congrArg₂ (fun v w : V => v+w) hp hs
  refine ⟨heq,?_⟩
  intro e O hO hTarget k z hz
  have hlocal : EqOn (fun y : X => nativeU (y.1,e.symm y.2))
      (fun y : X => U (B.symm y.1,e.symm y.2)) O := by
    intro y hy
    exact heq y.1 (hTarget y hy) (e.symm y.2)
  exact ((hlocal.eventuallyEq_of_mem (hO.mem_nhds hz)).iteratedFDeriv ℝ k).eq_of_nhds

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualProbeInitialSupply_grouped_combined_source_pullback
