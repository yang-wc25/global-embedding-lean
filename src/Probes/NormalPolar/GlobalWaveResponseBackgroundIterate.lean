import Probes.Round4ParameterProbeRawForcedDifference

/-! The SAME actual finite background mean iterate simultaneously carries
its original representative identity, reserve, size profile, and quadratic
two-point seminorm profile. The size estimate is retained for the true raw
reserve supply, rather than postulated for the full background wave. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation
universe uM uTr uΛ uΒ
variable {m d N p r count : ℕ} {M : Type uM} {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype Λ] [Fintype Β]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

/-- The same finite forced background substitutions and their original
paper-norm residual, obtained from primitive geometry/input profiles. -/
theorem globalWave_actual_background_germ_profiles
    (atlas : BufferedAtlas M D) (param : Fin count → OpenPartialHomeomorph Ep Ep)
    (hAtlas : IsSmoothBufferedAtlas atlas) (hParamSmooth : ∀ i, param i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ Ep)
    (S : Fin atlas.count × Fin count → Set (Fin (m+1+d) → ℝ)) (W : Set (Ep × M))
    (hS : ∀ i, IsCompact (S i)) (hSO : ∀ i, S i ⊆ incrementsOriginalDifferentiation atlas param i)
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (H : parameterRound2_originalTensorGermSpace atlas param S W) (HBound : ℕ → ℝ)
    (hH : ∀ s, parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO ell s H ≤ HBound s)
    (rho : ℝ) (hrho : 0 < rho)
    (q Rsub Lprimary : ℕ) (hq : 1 ≤ q) (reserve : ℝ) (hc : 0 < reserve)
    (Bnd : ℕ → ℝ → ℝ) (Mg Dinput : ℕ → ℝ)
    (hBnd : ∀ s R, 0 ≤ Bnd s R) (hMg : ∀ s, 0 ≤ Mg s) (hDinput : ∀ s, 0 ≤ Dinput s)
    (T TP : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTP : ∀ k, 0 ≤ TP k)
    (hParam : ∀ i : Fin atlas.count × Fin count, ∀ z : X,
      parameterTensorModelEquiv (m+1) d z ∈ S i → ∀ k, 1 ≤ k →
      ell^(k-1)*‖iteratedFDeriv ℝ k (parameterRound2_meanParameterMap (m:=m) (param i.2)) z‖ ≤ TP k)
    (ProbeB ProbeDiff : ℕ → ℝ) (Su : Set (Fin p → ℝ)) :
    let C := fun s R => parameterRound2_rawMeanIndexUniformCost.{uM,uTr,uΛ,uΒ}
      (m:=m) (d:=d) (N:=N) (M:=M) (Tr:=Tr)
      (s+(q+4)) q s Rsub Lprimary hq (by omega) reserve (Bnd s R) (Mg s) hc
      (hBnd s R) (hMg s) T TP hT hTP
    let pj := parameterRound2_originalTensorGermSeminorm atlas param S W hS hSO ell
    let cap := round4ParameterProbeForcedCap HBound rho ProbeB C q (q+4)
    0 < cap ∧ ∀
      (F : Ep → M → V) (hF : ∀ b, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F b))
      (g : IncrementsGlobalPrimaryFamily (I:=𝓙) (m:=m) (N:=N) (Λ:=Λ) (Β:=Β) F)
      (primary : Λ → Set (Ep × M)),
    ParameterRound2MeanRawGermReserveSupply (Tr:=Tr) atlas param S W pj H rho q Rsub Lprimary
      reserve Bnd Mg Dinput T F hF g primary ell →
    ∀ (epsilon : ℝ), 0 < epsilon → epsilon < cap → ∀ (delta : ℝ)
      (label : (Fin r × Bool) ↪ Fin p) (c : Fin r → Ep → D → M)
      (vf : (l : Fin r) → (b : Ep) → (x : D) → normalSpace (I:=𝓙) (F b) (c l b x))
      (phase : Fin r → Ep × M → ℝ) (probeLength : ℕ)
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X)
      (P : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace atlas param S W),
    (∀ u ∈ Su, (P u).val = (delta^2)⁻¹ •
      round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a u) →
    (∀ u ∈ Su, ∀ s, pj s (P u) ≤ ProbeB s) →
    (∀ u ∈ Su, pj 0 (P u) ≤ rho/4) →
    (∀ u ∈ Su, ∀ v ∈ Su, ∀ s,
      pj s (P u-P v) ≤ ((‖u‖+‖v‖)*‖u-v‖)*ProbeDiff s) →
    let A := round4ActualBackgroundMeanIterate F hF g (q+2) (epsilon*ell) delta H.val
      (round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let Cd := fun s bound => C s bound*Dinput s
    ∀ j ≤ q+1, ∃ G : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace atlas param S W,
      (∀ u ∈ Su, (G u).val = A j u) ∧
      (∀ u ∈ Su, pj 0 (G u-H) ≤ rho/2) ∧
      (∀ u ∈ Su, ∀ s, pj s (G u) ≤ R j s) ∧
      ∀ u ∈ Su, ∀ v ∈ Su, ∀ s,
        pj s (G u-G v) ≤ ((‖u‖+‖v‖)*‖u-v‖)*
          round4ParameterProbeForcedDifferenceCost ProbeDiff Cd R (q+4) j s := by
  intro C pj cap
  have hm := round4ParameterProbe_actual_raw_forced_mean (Λ:=Λ) (Β:=Β) (Tr:=Tr) (p:=p) (r:=r) (N:=N)
    atlas param hAtlas hParamSmooth S W hS hSO ell hell hell1 H HBound hH rho hrho
    q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam ProbeB
  have hd := round4ParameterProbe_actual_raw_forced_difference (Λ:=Λ) (Β:=Β) (Tr:=Tr) (p:=p) (r:=r) (N:=N)
    atlas param hAtlas hParamSmooth S W hS hSO ell hell hell1 H HBound hH rho hrho
    q Rsub Lprimary hq reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam ProbeB ProbeDiff
  refine ⟨hm.1,?_⟩
  intro F hF g primary hraw epsilon he hecap delta label c vf phase probeLength a P
    hPv hP hP0 hPQ A R Cd j hj
  have hex (u : Fin p → ℝ) (hu : u ∈ Su) :=
    hm.2 F hF g primary hraw epsilon he hecap delta label c vf phase probeLength a u (P u)
      (hPv u hu) (hP u hu) (hP0 u hu)
  classical
  let G : (Fin p → ℝ) → parameterRound2_originalTensorGermSpace atlas param S W := fun u =>
    if hu : u ∈ Su then (Classical.choose (hex u hu)) j else H
  have hG (u : Fin p → ℝ) (hu : u ∈ Su) :
      (G u).val = A j u ∧ pj 0 (G u-H) ≤ rho/2 ∧ ∀ s, pj s (G u) ≤ R j s := by
    dsimp only [G]
    rw [dif_pos hu]
    exact (Classical.choose_spec (hex u hu)).1 j hj
  refine ⟨G,fun u hu => (hG u hu).1,fun u hu => (hG u hu).2.1,
    fun u hu => (hG u hu).2.2,?_⟩
  intro u hu v hv s
  obtain ⟨Diff,hDiff⟩ := hd.2 F hF g primary hraw epsilon he hecap delta label c vf phase
    probeLength a u v (P u) (P v) (hPv u hu) (hPv v hv) (hP u hu) (hP v hv)
    (hP0 u hu) (hP0 v hv) (hPQ u hu v hv)
  have heq : G u-G v = Diff j := by
    apply Subtype.ext
    change (G u).val-(G v).val = (Diff j).val
    rw [(hG u hu).1,(hG v hv).1,(hDiff j hj).1]
  rw [heq]
  exact (hDiff j hj).2 s

end GlobalEmbedding.NormalPolar
#print axioms GlobalEmbedding.NormalPolar.globalWave_actual_background_germ_profiles
