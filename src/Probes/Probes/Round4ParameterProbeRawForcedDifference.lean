import Probes.Round4ParameterProbeRawForcedMean
import Probes.Round4ParameterProbeForcedDifference

/-! The two actual probe parameters drive the same finite background solver.
Original raw mean primitives, the proved common reserve, and the genuine
normalized probe two-point bound yield an original-paper-norm background
response bound. No background difference or parameter derivative is assumed.
Joint regularity in the external probe parameter is a separate obligation. -/
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
theorem round4ParameterProbe_actual_raw_forced_difference
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
    (ProbeB ProbeDiff : ℕ → ℝ) :
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
      (a : Fin r → OpenPartialHomeomorph (Ep × M) X) (u v : Fin p → ℝ)
      (P Q : parameterRound2_originalTensorGermSpace atlas param S W),
    P.val = (delta^2)⁻¹ • round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a u →
    Q.val = (delta^2)⁻¹ • round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a v →
    (∀ s, pj s P ≤ ProbeB s) → (∀ s, pj s Q ≤ ProbeB s) →
    pj 0 P ≤ rho/4 → pj 0 Q ≤ rho/4 →
    (∀ s, pj s (P-Q) ≤ ((‖u‖+‖v‖)*‖u-v‖)*ProbeDiff s) →
    let A := round4ActualBackgroundMeanIterate F hF g (q+2) (epsilon*ell) delta H.val
      (round4PrescribedNativeMean label F hF c vf phase (epsilon*ell) probeLength a)
    let R := round4ParameterProbeForcedProfile HBound ProbeB C (q+4)
    let Cd := fun s bound => C s bound*Dinput s
    ∃ Difference : ℕ → parameterRound2_originalTensorGermSpace atlas param S W,
      ∀ i ≤ q+1, (Difference i).val = A i u-A i v ∧
        ∀ s, pj s (Difference i) ≤ ((‖u‖+‖v‖)*‖u-v‖)*
          round4ParameterProbeForcedDifferenceCost ProbeDiff Cd R (q+4) i s := by
  intro C pj cap
  refine ⟨round4ParameterProbeForcedCap_pos HBound rho hrho ProbeB C q (q+4),?_⟩
  intro F hF g primary hraw epsilon he hecap delta label c vf phase probeLength a u v P Q
    hPv hQv hP hQ hP0 hQ0 hPQ A R Cd
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
  let GP := round4ParameterProbeForcedIterate H P Top
  let GQ := round4ParameterProbeForcedIterate H Q Top
  have hval (P0 : parameterRound2_originalTensorGermSpace atlas param S W) (w : Fin p → ℝ)
      (hP0v : P0.val = (delta^2)⁻¹ • round4PrescribedNativeMean label F hF c vf phase
        (epsilon*ell) probeLength a w)
      (hPb : ∀ s, pj s P0 ≤ ProbeB s) (hPlow : pj 0 P0 ≤ rho/4) :
      ∀ i ≤ q+1, (round4ParameterProbeForcedIterate H P0 Top i).val = A i w := by
    let G := round4ParameterProbeForcedIterate H P0 Top
    have hres := round4ParameterProbe_forced_finite_reserve pj H HBound hH rho hrho ProbeB C q (q+4)
      P0 hPb hPlow epsilon he hecap Top hsize
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      have hi' : i ≤ q+1 := by omega
      have hdom : pj 0 (G i-H) < rho := lt_of_le_of_lt (hres i hi').1 (by linarith)
      have hTv : (Top (G i)).val = incrementsGlobalPrimaryMeanError F hF g (G i).val (q+2) (epsilon*ell) :=
        round4ParameterProbeActualGermError_val atlas param S W pj H rho F hF g
          (q+2) (epsilon*ell) hsm0 (G i) hdom
      change H.val-P0.val-(Top (G i)).val = A (i+1) w
      rw [hP0v,hTv,ih hi']
      rfl
  have hbound := round4ParameterProbe_forced_finite_difference pj H HBound hH rho hrho ProbeB C Cd q (q+4)
    P Q hP hQ hP0 hQ0 epsilon he hecap Top hsize hdiff ProbeDiff
    ((‖u‖+‖v‖)*‖u-v‖) (by positivity) hPQ
  refine ⟨fun i => GP i-GQ i,?_⟩
  intro i hi
  constructor
  · change (GP i).val-(GQ i).val = _
    rw [hval P u hPv hP hP0 i hi,hval Q v hQv hQ hQ0 i hi]
  · exact hbound i hi

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4ParameterProbe_actual_raw_forced_difference
