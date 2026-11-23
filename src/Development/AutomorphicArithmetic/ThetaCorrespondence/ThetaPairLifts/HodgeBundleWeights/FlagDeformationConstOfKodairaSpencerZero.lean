module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ConstDeformationObjMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihilaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerUniqueValueAbelianSchemeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeformationRetractsOfKodairaSpencerZero

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
variable {C : Over (Sp (DualNumber R))} [GrpObj C] {φ : C.left ⟶ A.left} {j : A.left ⟶ C.left}
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
theorem exists_retraction_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
      ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left)
        (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i),
        IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
        (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) →
        ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  intro Pr GD E _ _ _ H Dw l Xo c K _ _ y x' _ _ A _ A' _ π π' i h _ hπ' _ hKS
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  exact GlobalTheory.DeRham.exists_retraction_of_isKSValue_one Pr.p5 GD h hA' gA' hKS
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) → ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  first | exact @_root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | exact _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | (intros; apply _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerPairingSymmetric

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers TensorProduct TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CrysConn
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSSym
variable {R : Type} [CommRing R] {X : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X ⟶ Sp (DualNumber R)}
open GlobalTheory.Published
end GlobalTheory.KSSym
namespace GlobalTheory.KSSym
open NumberField Formalism.L2.Pj MonObj
theorem kodairaSpencer_map_symm : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X)
    (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)),
    IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
    GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ →
    ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' →
      ψ f k' + ψ k g = 0 := by
  rintro Pr E _ _ _ H Dw l Xo K _ x x' A _ A' _ π π' i h ψ hπ hπ' rfl hψ f g k k' ⟨d, hd, ed⟩ ⟨d', hd', ed'⟩
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨ψ', hψ', iso, -⟩ := GlobalTheory.PolExistsRing.polForm_exists Pr.p5 Xo hπ'
  rw [← snd_polForm Pr.p5 hA gA h Xo.univ.t.PP.isLB hψ hψ' ed ed', iso _ hd _ hd']
  rfl
end GlobalTheory.KSSym
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)), IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ → ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' → ψ f k' + ψ k g = 0 := by
  first | exact @_root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | exact _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm | (intros; apply _root_.GlobalTheory.KSSym.kodairaSpencer_map_symm <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerFullFlagTangent

section

@[expose] public section

section
set_option autoImplicit false

noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSFull
end GlobalTheory.KSFull
namespace GlobalTheory.KSFull
theorem kodaira_spencer_full : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hKS
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩
  have P := PP.p5
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]
    · rw [Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ₀, hpol₀, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ
  obtain rfl : ψ = ψ₀ := IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'
  obtain ⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  obtain rfl : ub = ub₀ := by
    funext σ k
    apply ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ
    apply Over.OverMorphism.ext
    change (ub σ k).left ≫ π = (ub₀ σ k).left ≫ π
    rw [hu, hu₀]
  have hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2) := fun k => hl k.1 k.2
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hl'
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hl' k).push (a.act z)
    rw [he₀] at h1
    exact h1.sub_mem ((hl' k).smul _)
  have hsym := _root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol
  refine isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan
    (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb
    (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_
  ·
    have key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1 := fun τ j => by
      obtain ⟨w, hw, hr⟩ := hM τ j
      rwa [eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw] at hr
    rintro ⟨σ, j⟩ hσ
    have hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H := by
      rw [(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]
      exact hσ
    suffices ∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j
    intro σ' e'
    subst e'
    exact key ⟨conjEmb σ, hτ⟩
  ·
    rintro ⟨σ, j⟩ -
    exact GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift h a a' hc z hw)
      χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ
      (fun z => by
        simp only [χ, RingHom.comp_apply]
        rw [← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j
end GlobalTheory.KSFull
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.kodaira_spencer_full_flag_tangent : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  first | exact @_root_.GlobalTheory.KSFull.kodaira_spencer_full | exact _root_.GlobalTheory.KSFull.kodaira_spencer_full | (intros; apply _root_.GlobalTheory.KSFull.kodaira_spencer_full <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlagDeformationConstOfKodairaSpencerZero

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
namespace GlobalTheory.FlagTan
theorem eq_const_of_kodaira_spencer_eq_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, hA, A', hA', π, π', i, h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.kodaira_spencer_full_flag_tangent P E H Dw l Xo c K y x' hpq hx hks
  letI := hA
  letI := hA'
  obtain ⟨q, hq1, hq2⟩ := _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (_root_.GlobalTheory.T.const_deformation_obj_eq P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

theorem _root_.GlobalTheory.T.flag_deformation_const_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  first | exact @_root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero | exact _root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero | (intros; apply _root_.GlobalTheory.FlagTan.eq_const_of_kodaira_spencer_eq_zero <;> assumption)
end
end
end
