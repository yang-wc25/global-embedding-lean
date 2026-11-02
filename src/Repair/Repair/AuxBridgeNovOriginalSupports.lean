import Probes.Round3ParameterWholeDomainRegularity
import Probes.Round3ParameterNativeRefinementGeometry

/-! Original supports of the SAME finite increment.  Raw original geometry
produces primary channel support and signed secondary pair support.  The
parameter-atlas cover transfers these to the physical parameter manifold.
Finite sums then give the support of the literal total displacement.  No
support or estimate of a desired output is an input to the raw producer. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function Manifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

theorem auxBridgeNov_relative_support_of_zero
    {X V : Type*} [TopologicalSpace X] [Zero V]
    (f : X → V) (W K : Set X) (hK : IsClosed K)
    (hzero : ∀ z ∈ W, z ∉ K → f z = 0) :
    tsupport (fun z : W => f z.val) ⊆ Subtype.val ⁻¹' K := by
  apply closure_minimal ?_ (hK.preimage continuous_subtype_val)
  intro z hz
  by_contra hn
  exact hz (hzero z.val z.property hn)

section Native
variable {m N : ℕ} {Ep M Tr Label SubPrimary SubSecondary : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

omit [NormedAddCommGroup Tr] [NormedSpace ℝ Tr] [Fintype SubSecondary] [DecidableEq Label] in
theorem auxBridgeNov_native_primary_support
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (primary : Label → Set (Ep × M))
    (prim : ParameterRound2GlobalMeanPrimitives F hF g input W primary)
    (length : ℕ) (tau : ℝ) :
    ∀ ch nu beta, tsupport (fun z : W =>
      incrementsGlobalPrimaryExtension F hF g input length tau ch nu beta z.val) ⊆
        Subtype.val ⁻¹' tsupport (g.cutoff nu) := by
  have hh := actual_global_primary_extension_regular F hF g input length tau W prim.hW
    primary prim.hPrimary prim.hPrimarySupport prim.hSourceW prim.hChart prim.hChartInv
    prim.hInverse prim.hCombinedSupport prim.hCut prim.hNormal prim.hArgument prim.hEta
    prim.hPositive prim.hG prim.hJ prim.hT0 prim.hA prim.hB prim.hSecond
  intro ch nu beta z hz
  have hs : z.val ∈ incrementsGlobalRelativeSupport W
      (fun w => g.eta nu beta w * g.cutoff nu w) := by
    cases ch
    · exact (hh nu beta).2.2.2.2.2 hz
    · exact (hh nu beta).2.2.2.2.1 hz
  rw [parameterRound2_global_relativeSupport_eq W prim.hW] at hs
  exact tsupport_mul_subset_right hs.2

theorem auxBridgeNov_native_secondary_pair_support
    (nInput nSolve j q Rsub Lprimary : ℕ) (hq : 1 ≤ q)
    (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k)
    (F : Ep → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : IncrementsGlobalPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input inputbar : (p : Ep) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (Ep × M)) (hW : IsOpen W) (primary : Label → Set (Ep × M))
    (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → ActualOriginalSecondaryChoice Ep M m)
    (raw : ActualOriginalSecondaryRawData (Tr := Tr) F hF g input inputbar
      nInput nSolve j q Rsub Lprimary reserve Bnd Mg Kcut T Tinv W primary ell delta tau Delta choice) :
    ∀ r a, tsupport (fun z : W =>
      actualOriginalSecondaryPiece F hF g input (q+2) tau delta r.val (choice r a) z.val) ⊆
      Subtype.val ⁻¹' (tsupport (g.cutoff r.val.1.1) ∩ tsupport (g.cutoff r.val.1.2)) := by
  obtain ⟨CH,hCH,hFamily⟩ := actual_original_secondary_family_from_raw_uniform_all_index
    (m := m) (N := N) (Ep := Ep) (M := M) (Tr := Tr)
    nInput nSolve q Rsub Lprimary hq hInput reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv hT hTinv
  obtain ⟨data,hd,_⟩ := hFamily Label SubPrimary SubSecondary F hF g input inputbar W primary
    (j+1) ell delta tau Delta choice raw.geometry raw.coordinate raw.chart raw.phase raw.host raw.hostInverse
    raw.hostSource raw.cutoffSupport raw.cutoffSmooth raw.inverseSmooth raw.hostProfiles raw.cutoffJets raw.inverseJets
  intro r a z hz
  have hw : (data r a).base.wave tau (q+2) =
      actualOriginalSecondaryPiece F hF g input (q+2) tau delta r.val (choice r a) := by
    simp only [ActualSecondaryPieceData.wave,actualOriginalSecondaryPiece,
      (hd r a).1,(hd r a).2.1,(hd r a).2.2.1,
      (hd r a).2.2.2.2.2.1,(hd r a).2.2.2.2.2.2]
  have hs := ((data r a).base.wave_regular tau (q+2) hW).2
  rw [hw] at hs
  have hzS : z.val ∈ (raw.geometry r a).support := by
    rw [← (hd r a).2.2.2.1]
    exact hs hz
  have hp := raw.pairSupport r a hzS
  rw [parameterRound2_global_relativeSupport_eq W hW,
    parameterRound2_global_relativeSupport_eq W hW] at hp
  exact ⟨hp.1.2,hp.2.2⟩
end Native

section Physical
variable {m d N c : ℕ} {P M Tr Label SubPrimary SubSecondary : Type*}
  [TopologicalSpace P] [TopologicalSpace M]
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [Fintype Label] [DecidableEq Label] [Fintype SubPrimary] [Fintype SubSecondary]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

structure AuxBridgeNovOriginalSupports
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (input : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (length : ℕ) (tau delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (W : Set (P × M)) : Prop where
  primary_extension : ∀ ch nu beta, tsupport (fun z : W =>
    round3ParameterPrimaryExtension F hF g input length tau ch nu beta z.val) ⊆
      Subtype.val ⁻¹' tsupport (g.cutoff nu)
  primary_amplitude : ∀ ch nu, tsupport (fun z : W =>
    round3ParameterPrimaryAmplitude F hF g input length tau ch nu z.val) ⊆
      Subtype.val ⁻¹' tsupport (g.cutoff nu)
  primary_label : ∀ nu, tsupport (fun z : W => delta •
    (Real.cos (g.phase nu z.val / tau) •
      round3ParameterPrimaryAmplitude F hF g input length tau true nu z.val -
    Real.sin (g.phase nu z.val / tau) •
      round3ParameterPrimaryAmplitude F hF g input length tau false nu z.val)) ⊆
      Subtype.val ⁻¹' tsupport (g.cutoff nu)
  secondary_piece : ∀ r a, tsupport (fun z : W =>
    round3ParameterSecondaryPiece F hF g input length tau delta r.val (choice r a) z.val) ⊆
      Subtype.val ⁻¹' (tsupport (g.cutoff r.val.1.1) ∩ tsupport (g.cutoff r.val.1.2))
  total : tsupport (fun z : W =>
    round3ParameterIncrementMap F hF g input length tau delta choice z.val) ⊆
      Subtype.val ⁻¹' (⋃ nu, tsupport (g.cutoff nu))

theorem auxBridgeNov_original_supports_of_raw
    (nInput nSolve j q Rsub Lprimary Rsecondary : ℕ) (hq : 1 ≤ q)
    (hInput : nSolve+2+(q+2) ≤ nInput)
    (reserve Bnd Mg Kcut : ℝ) (hreserve : 0 < reserve)
    (hBnd : 0 ≤ Bnd) (hMg : 0 ≤ Mg) (hKcut : 0 ≤ Kcut)
    (T Tinv Tobs : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k) (hTinv : ∀ k, 0 ≤ Tinv k)
    (A : BufferedAtlas M D) (B : Fin c → OpenPartialHomeomorph P Ep)
    (F : P → M → V) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,V) ∞ (F p))
    (g : Round3ParameterPrimaryFamily (I := 𝓙) (m := m) (Λ := Label) (Β := SubPrimary) F)
    (hg : ∀ nu beta, Round3ParameterChartPreserves (g.chart nu beta))
    (input inputbar : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
    (W : Set (P × M)) (hW : IsOpen W)
    (cover : ∀ z ∈ W, ∃ b, z.1 ∈ (B b).source)
    (primary : Label → Set (P × M))
    (S : Fin A.count × Fin c → Set (Fin (m+1+d) → ℝ))
    (ell delta tau Delta : ℝ)
    (choice : ActualSecondarySignedRecord Label → SubSecondary → Round3ParameterSecondaryChoice P M m)
    (hc : ∀ r a, Round3ParameterChartPreserves (choice r a).chart)
    (raw : Round3ParameterRawAtlasData (Tr := Tr) A B F hF g input inputbar
      nInput nSolve j q Rsub Lprimary Rsecondary reserve Bnd Mg Kcut T Tinv Tobs
      W primary S ell delta tau Delta choice) :
    AuxBridgeNovOriginalSupports F hF g input (q+2) tau delta choice W := by
  have hExtension : ∀ ch nu beta, tsupport (fun z : W =>
      round3ParameterPrimaryExtension F hF g input (q+2) tau ch nu beta z.val) ⊆
        Subtype.val ⁻¹' tsupport (g.cutoff nu) := by
    intro ch nu beta
    apply auxBridgeNov_relative_support_of_zero _ W _ (isClosed_tsupport _)
    intro z hz hn
    obtain ⟨b,hb⟩ := cover z hz
    obtain ⟨a,_⟩ := A.cover z.2
    let Wn := round3ParameterNativeDomain (B b) W
    let y : Ep × M := ((B b) z.1,z.2)
    have hy : y ∈ Wn := ⟨(B b).map_source hb,by simpa only [y,(B b).left_inv hb,Prod.eta] using hz⟩
    have prim := (raw.observation (a,b)).profiles.prim
    have hs := auxBridgeNov_native_primary_support _ _ _ _ _ _ prim (q+2) tau ch nu beta
    have hzero : incrementsGlobalPrimaryExtension
        (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
        (round3ParameterNativePrimary F g (B b)) (fun t => input ((B b).symm t))
        (q+2) tau ch nu beta y = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun w : Wn =>
        incrementsGlobalPrimaryExtension _ _ _ _ (q+2) tau ch nu beta w.val) (x := ⟨y,hy⟩)
      intro hh
      have hcut := hs hh
      have hp := round3Parameter_plain_pullback_tsupport
        (round3ParameterProductChart (M := M) (B b)) (g.cutoff nu) y
        ⟨hy.1,mem_univ _⟩ hcut
      exact hn (by simpa only [round3ParameterProductChart,OpenPartialHomeomorph.prod_symm,
        OpenPartialHomeomorph.prod_apply,OpenPartialHomeomorph.refl_symm,
        OpenPartialHomeomorph.refl_apply,y,id_eq,(B b).left_inv hb,Prod.eta] using hp)
    have he := round3ParameterPrimary_pullback_extension F hF g (B b) hg input
      (q+2) tau ch nu beta ((B b) z.1) ((B b).map_source hb) z.2
    rw [(B b).left_inv hb] at he
    exact he ▸ hzero
  have hSecondary : ∀ r a, tsupport (fun z : W =>
      round3ParameterSecondaryPiece F hF g input (q+2) tau delta r.val (choice r a) z.val) ⊆
        Subtype.val ⁻¹' (tsupport (g.cutoff r.val.1.1) ∩ tsupport (g.cutoff r.val.1.2)) := by
    intro r a
    apply auxBridgeNov_relative_support_of_zero _ W _ ((isClosed_tsupport _).inter (isClosed_tsupport _))
    intro z hz hn
    obtain ⟨b,hb⟩ := cover z hz
    let Wn := round3ParameterNativeDomain (B b) W
    let y : Ep × M := ((B b) z.1,z.2)
    have hy : y ∈ Wn := ⟨(B b).map_source hb,by simpa only [y,(B b).left_inv hb,Prod.eta] using hz⟩
    have hs := auxBridgeNov_native_secondary_pair_support
      nInput nSolve j q Rsub Lprimary hq hInput reserve Bnd Mg Kcut hreserve hBnd hMg hKcut T Tinv hT hTinv
      _ _ _ _ _ Wn (round3ParameterNativeDomain_open (B b) W hW) _ ell delta tau Delta _ (raw.raw b) r a
    have hzero : actualOriginalSecondaryPiece
        (fun t => F ((B b).symm t)) (fun t => hF ((B b).symm t))
        (round3ParameterNativePrimary F g (B b)) (fun t => input ((B b).symm t))
        (q+2) tau delta r.val (round3ParameterNativeChoices choice (B b) r a) y = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun w : Wn =>
        actualOriginalSecondaryPiece _ _ _ _ (q+2) tau delta r.val
          (round3ParameterNativeChoices choice (B b) r a) w.val) (x := ⟨y,hy⟩)
      intro hh
      have hpair := hs hh
      have hback (nu) (ht : y ∈ tsupport
          (fun w : Ep × M => g.cutoff nu ((B b).symm w.1,w.2))) : z ∈ tsupport (g.cutoff nu) := by
        have hp := round3Parameter_plain_pullback_tsupport
          (round3ParameterProductChart (M := M) (B b)) (g.cutoff nu) y ⟨hy.1,mem_univ _⟩ ht
        simpa only [round3ParameterProductChart,OpenPartialHomeomorph.prod_symm,
          OpenPartialHomeomorph.prod_apply,OpenPartialHomeomorph.refl_symm,
          OpenPartialHomeomorph.refl_apply,y,id_eq,(B b).left_inv hb,Prod.eta] using hp
      exact hn ⟨hback _ hpair.1,hback _ hpair.2⟩
    have he := round3ParameterSecondary_pullback_piece F hF g (B b) hg input
      (q+2) tau delta r.val (choice r a) (hc r a)
      ((B b) z.1) ((B b).map_source hb) z.2
    rw [(B b).left_inv hb] at he
    exact he ▸ hzero
  have hExtZero (ch nu beta) (z : P × M) (hz : z ∈ W) (hn : z ∉ tsupport (g.cutoff nu)) :
      round3ParameterPrimaryExtension F hF g input (q+2) tau ch nu beta z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun w : W =>
      round3ParameterPrimaryExtension F hF g input (q+2) tau ch nu beta w.val)
      (x := ⟨z,hz⟩) (fun hs => hn (hExtension ch nu beta hs))
  have hAmpZero (ch nu) (z : P × M) (hz : z ∈ W) (hn : z ∉ tsupport (g.cutoff nu)) :
      round3ParameterPrimaryAmplitude F hF g input (q+2) tau ch nu z = 0 := by
    exact Finset.sum_eq_zero (fun beta _ => hExtZero ch nu beta z hz hn)
  have hSecZero (r a) (z : P × M) (hz : z ∈ W)
      (hn : z ∉ tsupport (g.cutoff r.val.1.1) ∩ tsupport (g.cutoff r.val.1.2)) :
      round3ParameterSecondaryPiece F hF g input (q+2) tau delta r.val (choice r a) z = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun w : W =>
      round3ParameterSecondaryPiece F hF g input (q+2) tau delta r.val (choice r a) w.val)
      (x := ⟨z,hz⟩) (fun hs => hn (hSecondary r a hs))
  refine ⟨hExtension,?_,?_,hSecondary,?_⟩
  · intro ch nu
    exact auxBridgeNov_relative_support_of_zero _ W _ (isClosed_tsupport _) (hAmpZero ch nu)
  · intro nu
    apply auxBridgeNov_relative_support_of_zero
      (fun z : P × M => delta • (Real.cos (g.phase nu z / tau) •
        round3ParameterPrimaryAmplitude F hF g input (q+2) tau true nu z -
        Real.sin (g.phase nu z / tau) •
        round3ParameterPrimaryAmplitude F hF g input (q+2) tau false nu z))
      W (tsupport (g.cutoff nu)) (isClosed_tsupport _)
    intro z hz hn
    simp only [hAmpZero true nu z hz hn,hAmpZero false nu z hz hn,smul_zero,sub_zero]
  · apply auxBridgeNov_relative_support_of_zero _ W _ (isClosed_iUnion_of_finite fun nu => isClosed_tsupport (g.cutoff nu))
    intro z hz hn
    have hnot (nu) : z ∉ tsupport (g.cutoff nu) := fun hh => hn (mem_iUnion.mpr ⟨nu,hh⟩)
    have hPrimaryZero : round3ParameterPrimaryWave F hF g input (q+2) tau z = 0 := by
      apply Finset.sum_eq_zero
      intro nu _
      simp only [hAmpZero true nu z hz (hnot nu),hAmpZero false nu z hz (hnot nu),smul_zero,sub_zero]
    have hSecondaryZero : round3ParameterSecondarySum F hF g input (q+2) tau delta choice z = 0 := by
      unfold round3ParameterSecondarySum actualSecondaryRefinedNonzeroSum actualSecondaryNonzeroSum
      apply Finset.sum_eq_zero
      intro nu _
      apply Finset.sum_eq_zero
      intro mu _
      apply Finset.sum_eq_zero
      intro branch _
      apply Finset.sum_eq_zero
      intro a _
      dsimp only
      split_ifs with h
      · exact hSecZero ⟨((nu,mu),branch),h⟩ a z hz (fun hh => hnot nu hh.1)
      · rfl
    simp only [round3ParameterIncrementMap,hPrimaryZero,hSecondaryZero,smul_zero,zero_add]

end Physical
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_relative_support_of_zero
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_native_primary_support
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_native_secondary_pair_support
#print axioms GlobalEmbedding.Continuation.auxBridgeNov_original_supports_of_raw
