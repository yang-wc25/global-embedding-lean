import Probes.Round4ParameterProbeActualForcedMean
import Smoothing.ParameterRound2MeanRawGermFixedCostIndex

/-! Primitive mean data now supply the forced probe/background iteration.
The actual original paper seminorm is fixed in the statement; regularity,
size, and difference estimates for the produced mean are derived from raw
profiles. A common numerical entrance precedes F, u, and observation order.
This is a finite-mean producer, not yet the combined secondary error budget
or the complete first repaired closed state. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff BigOperators Classical
namespace GlobalEmbedding.Continuation
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
theorem round4ParameterProbe_actual_raw_forced_mean
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
    (ProbeB : ℕ → ℝ) :
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
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (u : Fin p → ℝ)
      (P : parameterRound2_originalTensorGermSpace atlas param S W),
    P.val = (delta^2)⁻¹ • round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a u →
    (∀ s, pj s P ≤ ProbeB s) → pj 0 P ≤ rho/4 →
    let A := round4ActualBackgroundMeanIterate F hF g (q+2) (epsilon*ell) delta H.val
      (round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let C0 := fun s => ProbeB s+max 0 (C s (HBound (s+(q+4))))
    let Cd := fun i s => max 0 ((C s (max (R i (s+(q+4))) (R (i+1) (s+(q+4)))))*Dinput s)
    ∃ G : ℕ → parameterRound2_originalTensorGermSpace atlas param S W,
      (∀ i ≤ q+1, (G i).val = A i u ∧ pj 0 (G i-H) ≤ rho/2 ∧ ∀ s, pj s (G i) ≤ R i s) ∧
      ∃ E : parameterRound2_originalTensorGermSpace atlas param S W,
        E.val = delta^2 • (incrementsGlobalPrimaryMeanError F hF g (A (q+1) u) (q+2) (epsilon*ell) -
          incrementsGlobalPrimaryMeanError F hF g (A q u) (q+2) (epsilon*ell)) ∧
        ∀ s, pj s E ≤ delta^2*(epsilon^(q+1)*parameterRound2_finiteMeanErrorCost C0 Cd (q+4) (q+1) s) := by
  intro C pj cap
  refine ⟨round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C q (q+4),?_⟩
  intro F hF g primary hraw epsilon he hecap delta label c vf phase probeLength a u P hPv hP hP0
    A R C0 Cd
  obtain ⟨hsm,hs,hd⟩ := parameterRound2_actual_raw_mean_germ_fixed_cost_estimates_index
    atlas param hAtlas hParamSmooth S W hS hSO ell hell hell1 H rho q Rsub Lprimary hq
    reserve hc Bnd Mg Dinput hBnd hMg hDinput T TP hT hTP hParam F hF g primary hraw
  have he1 : epsilon ≤ 1 := (hecap.trans_le (min_le_left _ _)).le
  let hsm0 := fun (K : parameterRound2_originalTensorGermSpace atlas param S W)
    (hK : pj 0 (K-H) < rho) => hsm epsilon he he1 ⟨K,hK⟩
  let Top := round4ParameterProbeActualGermError atlas param S W pj H rho F hF g (q+2) (epsilon*ell) hsm0
  have heq (K : parameterRound2_originalTensorGermSpace atlas param S W) (hK : pj 0 (K-H) < rho) :
      Top K = parameterRound2_actualGermMeanReserveOperator atlas param S W pj H rho ell F hF g q hsm
        epsilon ⟨K,hK⟩ := by
    apply Subtype.ext
    rw [round4ParameterProbeActualGermError_val atlas param S W pj H rho F hF g
      (q+2) (epsilon*ell) hsm0 K hK]
    exact (parameterRound2_actualGermMeanReserveOperator_val atlas param S W pj H rho ell
      F hF g q hsm epsilon ⟨K,hK⟩ he he1).symm
  have hsize (s : ℕ) (bound : ℝ) (K : parameterRound2_originalTensorGermSpace atlas param S W)
      (hK : pj 0 (K-H) < rho) (hbound : pj (s+(q+4)) K ≤ bound) :
      pj s (Top K) ≤ epsilon*C s bound := by
    rw [heq K hK]
    exact hs epsilon he he1 s bound ⟨K,hK⟩ hbound
  have hdiff (s : ℕ) (bound : ℝ) (K L : parameterRound2_originalTensorGermSpace atlas param S W)
      (hK : pj 0 (K-H) < rho) (hL : pj 0 (L-H) < rho)
      (hKbound : pj (s+(q+4)) K ≤ bound) (hLbound : pj (s+(q+4)) L ≤ bound) :
      pj s (Top K-Top L) ≤ epsilon*(C s bound*Dinput s)*pj (s+(q+4)) (K-L) := by
    rw [heq K hK,heq L hL]
    exact hd epsilon he he1 s bound ⟨K,hK⟩ ⟨L,hL⟩ hKbound hLbound
  exact round4ParameterProbe_actual_forced_mean_finite_residual atlas param S W pj H HBound hH rho hrho
    ProbeB C (fun s bound => C s bound*Dinput s) q (q+4) F hF g (q+2)
    (epsilon*ell) delta epsilon he hecap hsm0 hsize hdiff label c vf phase probeLength a u P hPv hP hP0

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_actual_raw_forced_mean
