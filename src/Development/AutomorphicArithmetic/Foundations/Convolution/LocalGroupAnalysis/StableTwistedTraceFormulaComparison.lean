module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.AdelicQuotients.AdeleBaseChangeLocalIsClosedEmbedding
public import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
public import Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionContinuous
public import Development.AutomorphicArithmetic.AdelicQuotients.AdelicBoundOfCentralizerLocalization
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AdelicQuotients.AdicCompletionIntegersBaseChangeIff
public import Development.AutomorphicArithmetic.AdelicQuotients.BaseChangeTrivialExtension
public import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
public import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionLocalScalar
public import Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
public import Development.AutomorphicArithmetic.AdelicQuotients.CharpolySeparableUnitSmul
public import Development.AutomorphicArithmetic.AdelicQuotients.EulerProductOfQuotientPushforwardSupport
public import Development.AutomorphicArithmetic.AdelicQuotients.EulerProductSupportFinite
public import Development.AutomorphicArithmetic.AdelicQuotients.ExistsHaarMeasureAdelicGL
public import Development.AutomorphicArithmetic.AdelicQuotients.GeometricSideAbsolutelyConvergentOfEulerFubini
public import Development.AutomorphicArithmetic.AdelicQuotients.GlobalOrbitalComparisonOfSplit
public import Development.AutomorphicArithmetic.AdelicQuotients.HaarConstOfHaarExists
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.NormEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotEq
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.AdelicQuotients.HaarUnimodularCriterion
public import Development.AutomorphicArithmetic.AdelicQuotients.InfinitePartFiniteOfAdelicBound
public import Development.AutomorphicArithmetic.AdelicQuotients.LocalUnimodularOfExistsHaarMeasure
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalIntegralFubini
public import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideBaseFieldOfAbsoluteConvergence
public import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideExtensionOfAbsoluteConvergence
public import Development.AutomorphicArithmetic.AdelicQuotients.QuotientHaarMeasurePushforward
public import Development.AutomorphicArithmetic.AdelicQuotients.QuotientMeasureSplit
public import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductCentralizerAdelicGL
public import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductExtensionOfBaseRegroup
public import Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductFiniteAdelicGL
public import Development.AutomorphicArithmetic.AdelicQuotients.SplitCentralizerOfSplitEquiv
public import Development.AutomorphicArithmetic.AdelicQuotients.TorusCommutativeOfCentralizerCommutative
public import Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormCentralOfBaseChangeCompat
public import Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormLocalOfCompat
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.GlobalFields.Adele.Topology
import GroundTheory.GlobalFields.LocalAtPlace
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLSplitEquiv

section

@[expose] public section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.HaarQuotientSubgroup

section

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.haar_quotient_subgroup :
    QSub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨ρ₀, -, hρ₀, -⟩ := normEx H T μ j ν hp
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  have hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ := by
    refine ⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0,
      hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩
    have e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G))
        = (ρ₀ (j t * x) : ENNReal) := fun t => by
      rw [← Subgroup.coe_mul]
      exact hinj.extend_apply _ _ _
    simp only [e]
    exact hρ₀.2 x
  unfold quotInt
  rw [dite_eq_left hex]
  have hn : IsNrm j ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by
      simpa only [Subgroup.coe_mul] using hex.choose_spec.2 x⟩
  exact ((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.MaximalCompactNormOfUnitCriterion

section

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal

theorem UpperTheory.maximalCompactNorm_of_unit_criterion :
    K1 → Triv → UnitIff → Compat → SelmerRankBoundLaurent := by
  intro hK hT hU hC F _ _ n hn γ hγ
  have hincl : PositivityTheory.Rg.Tf.Loc.incl γ = γ := by
    ext i j
    rfl
  have hnorm : PositivityTheory.Rg.Tf.Loc.normGL (1 : F ≃ₐ[F] F) γ = PositivityTheory.Rg.Tf.Loc.incl γ := by
    rw [hincl, PositivityTheory.Rg.Tf.Loc.normGL, Module.finrank_self]
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
  have h1 : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  obtain ⟨-, -, -, c4, -, -, -, c8⟩ := hC F F 1 n
  filter_upwards [hK F F 1 h1 n hn γ γ hγ hnorm] with v hv x
  have hdiag : mapGL n (atFin v) (AdelicGLn.diagonal F n γ) =
      mapGL n (incFin F v) (finAt v (AdelicGLn.diagonal F n γ)) := by
    have h := c4 v (AdelicGLn.diagonal F n γ)
    rw [c8, hincl] at h
    exact h
  have hgal : ∀ y : GL (Fin n) (CompletionsOver F v), mapGL n (galFin (1 : F ≃ₐ[F] F) v) y = y := fun y => by
    rw [((hT F).2.2 v).1]
    ext i j
    rfl
  have key := hv (mapGL n (incFin F v) x)
  rw [hdiag, hgal, ← map_inv, ← map_mul, ← map_mul, hU F F n v] at key
  rw [key]
  constructor
  · rintro ⟨t, ht, y, hy, e⟩
    refine ⟨t, ht, t⁻¹ * x, ?_, by group⟩
    rw [← hU F F n v, map_mul, map_inv, e, inv_mul_cancel_left]
    exact hy
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, mapGL n (incFin F v) y, (hU F F n v y).2 hy, map_mul _ _ _⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AdelicQuotients.SeparableLocalOfSeparableScalar

section

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.separableLocal_of_separableScalar :
    SepSc → CentLoc → SepLoc := by
  intro hS hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hI : ((pI F n (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (InfiniteAdeleRing F)) := by
    ext a b
    rfl
  have hIs : (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable := by
    rw [hI, Matrix.charpoly_map]
    exact hsep.map
  refine ⟨hIs, fun s => ?_, fun v => ?_⟩
  · obtain ⟨⟨r, hr⟩, -⟩ := hC F n ⟨Real.exp s, Real.exp_pos s⟩
    have h := hr (pI F n (AdelicGLn.diagonal F n γ))
    have h' : (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val =
        (r : InfiniteAdeleRing F) • (pI F n (AdelicGLn.diagonal F n γ)).val := h
    rw [h']
    exact hS _ n r _ hIs
  · have hv : ((finAt v (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) := by
      ext a b
      rfl
    rw [hv, Matrix.charpoly_map]
    exact hsep.map
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.StableTwistedTraceFormulaComparison

section

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem match_qI {n : ℕ} {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R]
    [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] {ι : R →+* S} {s : S →+* S} {l : ℕ}
    {μS : Measure (GL (Fin n) S)} {μR : Measure (GL (Fin n) R)} {c : ℂ} {φ : GL (Fin n) S → ℂ} {f : GL (Fin n) R → ℂ}
    (h : Match ι s l μS μR c φ f) (γ : GL (Fin n) R) (hγ : γ.val.charpoly.Separable) (H : Subgroup (GL (Fin n) R))
    (hH : H = Subgroup.centralizer {γ}) (ν : Measure H) (hν : ν.IsHaarMeasure) :
    (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ →
      qI μS ((mapGL n ι).comp H.subtype) ν (fun x => φ (x⁻¹ * δ * mapGL n s x)) =
        c * qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x))) ∧
    ((¬ ∃ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ) → qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x)) = 0) := by
  subst hH
  exact h γ hγ ν hν

private theorem cent_mul {G : Type} [Group G] (z g : G) (hz : ∀ x, z * x = x * z) :
    Subgroup.centralizer {g} = Subgroup.centralizer {z * g} := by
  ext t
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change (t * g = g * t) ↔ (t * (z * g) = (z * g) * t)
  rw [← mul_assoc, ← hz t, mul_assoc, mul_assoc, mul_right_inj]

private theorem lc_cent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (g : G) :
    LocallyCompactSpace (Subgroup.centralizer {g}) := by
  have : IsClosed (Subgroup.centralizer {g} : Set G) := Set.isClosed_centralizer _
  exact this.locallyCompactSpace

private theorem main (hGl : Glob) (hC : HaarConst) (hX : HaarEx) (hRF : RPF) (hRE : RPE) (hRC : RPCen) (hSF : SideF) (hSE : SideE)
    (hK : K1) (hKF : SelmerRankBoundLaurent) (hH : H1) (hZ : ZNorm) (hN : LocNorm) (hS : SepLoc) (hL : CentLoc) : G4 := by
  classical
  intro F E _ _ _ _ _ _ σ hσ n hn hp _ _ _ _ _ _ _ _ μE μF μiE μiF mE mF hμE hμF hiE hiF hmE hmF
  obtain ⟨μE', μF', uE, uF, hG⟩ := hGl F E σ hσ n hn μE μF hμE hμF
  obtain ⟨aE, haE, hEE⟩ := hC _ _ _ _ _ _ _ (hRE F E n) μE' μiE mE uE.1 hiE hmE
  obtain ⟨aF, haF, hEF⟩ := hC _ _ _ _ _ _ _ (hRF F n) μF' μiF mF uF.1 hiF hmF
  refine ⟨aE / aF, div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haE)) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haF)), ?_⟩
  intro S φi fi φ f ci c hφi hφi' hfi hfi' hφ hoff hMi hM γ γ₁ hγ₁ hirr ν hν
  have hsep : IsRegSemisimple γ := hirr.separable
  obtain ⟨ν', hν', hGF, hGE⟩ := hG γ γ₁ hγ₁ hsep ν hν
  obtain ⟨hs1, hs2, hs3⟩ := hS F n γ hsep
  haveI : LocallyCompactSpace (TA γ) := lc_cent _
  haveI : LocallyCompactSpace (TI γ) := lc_cent _
  haveI : ∀ v, LocallyCompactSpace (TF γ v) := fun v => lc_cent _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ∀ v, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology _
  have hT := fun S' => hX _ _ _ _ _ _ _ (hRC _ _ _ _ _ _ _ (hRF F n) (AdelicGLn.diagonal F n γ)) ν' Measure.haar
    (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) S'
  have hcF := (hKF F n hn γ hsep)
  rw [eventually_cofinite] at hcF
  have hFside := fun (S' : Finset (Pl F)) (h1 : S ⊆ S') (h2 : hcF.toFinset ⊆ S') (b : NNReal) (hb : b ≠ 0)
      (hE : EulT γ ν' Measure.haar (fun _ => Measure.haar) b S') =>
    hSF F n hn μF' μiF mF uF hiF (fun v => (hmF v).1) γ hsep ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance
      (fun _ => inferInstance) S' aF b haF hb hE (hEF S') fi f hfi hfi' (fun v => (hφ v).2.2.1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).2.1, by
        by_contra h
        exact hv (h2 (hcF.mem_toFinset.2 h))⟩)
  have hMi' := fun s : ℝ => match_qI hMi _ (hs2 s) (TI γ) (cent_mul _ _ (hL F n _).2.1) Measure.haar inferInstance
  have hM' := fun v => match_qI (hM v) _ (hs3 v) (TF γ v) rfl Measure.haar inferInstance
  constructor
  · intro δ hδ
    have hcE := hK F E σ hσ n hn δ γ hsep hδ
    rw [eventually_cofinite] at hcE
    obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ hcE.toFinset)
    have h1 : S ⊆ S ∪ hcF.toFinset ∪ hcE.toFinset := Finset.subset_union_left.trans Finset.subset_union_left
    obtain ⟨m1, e1⟩ := hFside _ h1 (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
    obtain ⟨m2, e2⟩ := hSE F E σ hσ n hn μE' μiE mE uE hiE (fun v => (hmE v).1) γ hsep δ hδ ν' Measure.haar (fun _ => Measure.haar)
      hν' inferInstance (fun _ => inferInstance) _ aE b haE hb hE (hEE _) φi φ hφi hφi' (fun v => (hφ v).1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).1, by
        by_contra h
        exact hv (Finset.subset_union_right (hcE.mem_toFinset.2 h))⟩)
    obtain ⟨n1, n2⟩ := hN F E σ hσ n hn δ γ hδ
    rw [hGF _ m1, hGE δ hδ _ m2, e1, e2]
    have i1 := fun s : ℝ => (hMi' s).1 (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) (by
      rw [hZ F E σ hσ n hn, n1, ← map_mul])
    have i2 := fun v => (hM' v).1 _ (n2 v)
    simp only [i1, i2]
    rw [integral_const_mul, Finset.prod_mul_distrib, ← Finset.prod_subset h1 fun v _ hv => (hoff v hv).2.2]
    have : ((aF : ℝ) : ℂ) ≠ 0 := by exact_mod_cast haF
    push_cast
    field_simp
  · intro hno
    by_cases hi : ∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ))
    · have : ¬ ∀ v : Pl F, ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ =
          mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ)) := fun h => hno (hH F E σ hσ n hn hp γ hirr hi h)
      obtain ⟨v, hv⟩ := not_forall.1 this
      obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ {v})
      obtain ⟨m1, e1⟩ := hFside _ (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
      rw [hGF _ m1, e1, Finset.prod_eq_zero (i := v) (by simp) ((hM' v).2 hv), mul_zero]
    · obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset)
      obtain ⟨m1, e1⟩ := hFside _ Finset.subset_union_left Finset.subset_union_right b hb hE
      have i1 := fun s : ℝ => (hMi' s).2 (by
        rintro ⟨δ, hδ⟩
        refine hi ⟨(pI E n (zA E n s))⁻¹ * δ, ?_⟩
        have h := hZ F E σ hσ n hn s ((pI E n (zA E n s))⁻¹ * δ)
        rw [mul_inv_cancel_left, hδ, map_mul] at h
        exact (mul_left_cancel h).symm)
      rw [hGF _ m1, e1]
      simp only [i1, integral_zero, mul_zero, zero_mul]

theorem UpperTheory.ConvolutionTheory.G.stable_twisted_trace_formula_comparison :
    Q1 → Q2 → Q3 → N3 → N5 → P1 → P2 → K1 → H1 → G4 := by
  intro _ _ _ n3 n5 _ p2 k1 h1
  have qpush : QPush := UpperTheory.quotient_haar_measure_pushforward
  have splitEq : SplitEquiv := UpperTheory.adelicGL_split_equiv
  have splitQ : SplitQ := UpperTheory.quotient_measure_split
  have uniOf : UniOf := UpperTheory.haar_unimodular_criterion
  have haarEx : HaarEx := UpperTheory.exists_haarMeasure_adelicGL
  have haarConst : HaarConst := UpperTheory.haar_const_of_haar_exists haarEx
  have uniLoc : UniLoc := UpperTheory.local_unimodular_of_exists_haar_measure haarEx
  have rpCen : RPCen := UpperTheory.restrictedProduct_centralizer_adelicGL
  have euler : Euler := UpperTheory.eulerProduct_of_quotient_pushforward_support qpush UpperTheory.euler_product_support_finite
  have sideAbs : SideAbs := UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini euler UpperTheory.orbital_integral_fubini
  have qsub : QSub := UpperTheory.haar_quotient_subgroup
  have rpf : RPF := UpperTheory.restrictedProduct_finite_adelicGL
  have rpe : RPE := UpperTheory.restrictedProduct_extension_of_base_regroup rpf
  have compat : Compat := UpperTheory.adele_galois_action_baseChange_compat
  have galCont : GalCont := UpperTheory.adele_galois_action_continuous compat rpe
  have locEmb : LocEmb := UpperTheory.adele_baseChange_local_isClosedEmbedding
  have unitIff : UnitIff := UpperTheory.adicCompletion_integers_baseChange_iff
  have centLoc : CentLoc := UpperTheory.centralSection_local_scalar
  have centBC : CentBC := UpperTheory.centralSection_baseChange
  have zNorm : ZNorm := UpperTheory.twistedNorm_central_of_baseChange_compat compat centLoc centBC
  have locNorm : LocNorm := UpperTheory.twistedNorm_local_of_compat compat
  have sepLoc : SepLoc := UpperTheory.separableLocal_of_separableScalar UpperTheory.charpoly_separable_unit_smul centLoc
  have tComm : TComm := UpperTheory.torusCommutative_of_centralizerCommutative UpperTheory.centralizer_commutative_of_separable_charpoly
  have triv : Triv := UpperTheory.baseChange_trivial_extension
  have boundE : BoundE := UpperTheory.adelicBound_of_centralizer_localization n5 compat centLoc rpe
  have infF : InfF := UpperTheory.infinitePart_finite_of_adelicBound p2 triv boundE
  have k1F : SelmerRankBoundLaurent := UpperTheory.maximalCompactNorm_of_unit_criterion k1 triv unitIff compat
  have spl : Spl := UpperTheory.splitCentralizer_of_splitEquiv splitEq n5 centBC
  have glob : Glob := UpperTheory.globalOrbitalComparison_of_split qsub splitQ uniOf tComm spl n3 n5 centBC
  have sideF : SideF := UpperTheory.orbitalSideBaseField_of_absoluteConvergence sideAbs rpf rpCen uniLoc uniOf tComm sepLoc centLoc infF
  have sideE : SideE := UpperTheory.orbitalSideExtension_of_absoluteConvergence sideAbs rpf rpe rpCen uniLoc uniOf tComm sepLoc centLoc compat galCont locEmb unitIff locNorm boundE n3 n5 p2
  exact main glob haarConst haarEx rpf rpe rpCen sideF sideE k1 k1F h1 zNorm locNorm sepLoc centLoc
end
end
