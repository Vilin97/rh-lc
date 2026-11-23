module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMapStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtaleStatement
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrdersStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.exists_primeDivisor_etalePullback_orders : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z → ∃ E : DivOver p, E.IsAt (f z) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | exact GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd | (intros; apply GlobalTheory.EtaleDiv.exists_isAt_ord_formOrd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtale

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem formallyEtale_of_isIso {R S : CommRingCat.{0}} (e : R ⟶ S) [IsIso e] :
    e.hom.FormallyEtale := by
  letI := e.hom.toAlgebra
  let E : R ≃ₐ[R] S := { (asIso e).commRingCatIsoToRingEquiv with commutes' := fun _ => rfl }
  show Algebra.FormallyEtale R S
  exact Algebra.FormallyEtale.of_equiv E

theorem genericPoint_mem_of_nonempty {X : Scheme.{0}} [IsIntegral X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hU)

theorem map_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem formallyEtale_functionFieldMap {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W]
    (f : M ⟶ W) [IsDominant f] (U : M.Opens) (hf : Etale (U.ι ≫ f))
    (hU : (U : Set M).Nonempty) : (functionFieldMap f).FormallyEtale := by
  have hξ := genericPoint_mem_of_nonempty U hU
  let u : (U : Scheme.{0}) := ⟨genericPoint M, hξ⟩
  have h1 : ((U.ι ≫ f).stalkMap u).hom.FormallyEtale := by
    have hu := FormallyUnramified.stalkMap (U.ι ≫ f) u
    have hs : ((U.ι ≫ f).stalkMap u).hom.FormallySmooth :=
      Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ u))
    algebraize [((U.ι ≫ f).stalkMap u).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  rw [Scheme.Hom.stalkMap_comp] at h1
  have h2 : (f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    have e : f.stalkMap (genericPoint M) =
        (f.stalkMap (U.ι u) ≫ U.ι.stalkMap u) ≫ inv (U.ι.stalkMap u) := by simp; rfl
    rw [e]
    exact RingHom.FormallyEtale.comp h1 (formallyEtale_of_isIso _)
  have hiso : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      IsIso (W.presheaf.stalkSpecializes h) := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    infer_instance
  have key : ∀ h : f (genericPoint M) ⤳ genericPoint W,
      (W.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint M)).hom.FormallyEtale := by
    intro h
    haveI := hiso h (map_genericPoint f)
    exact RingHom.FormallyEtale.comp (formallyEtale_of_isIso _) h2
  exact key _

theorem injective_of_isBaseChange_field {A B M N : Type*} [Field A] [CommRing B] [Nontrivial B]
    [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) : Function.Injective φ := by
  have e : (φ : M → N) = hφ.equiv ∘ ((Algebra.linearMap A B).rTensor M) ∘
      (TensorProduct.lid A M).symm := by
    funext m
    simp [hφ.equiv_tmul]
  rw [e]
  refine hφ.equiv.injective.comp ((Module.Flat.rTensor_preserves_injective_linearMap _
    (algebraMap A B).injective).comp (TensorProduct.lid A M).symm.injective)

theorem ratPull_ne_zero : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M]
    [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ)
    [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 →
      GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  intro M W _ _ _ _ p f _ n _ _ U hf hU η hη h0
  have hE := formallyEtale_functionFieldMap f U hf hU
  letI := (Cartier.constFn p).toAlgebra
  letI := (Cartier.constFn (f ≫ p)).toAlgebra
  letI := (functionFieldMap f).toAlgebra
  haveI : IsScalarTower ℂ W.functionField M.functionField :=
    IsScalarTower.of_algebraMap_eq' (functionFieldMap_comp_constFn p f).symm
  haveI : Algebra.FormallyEtale W.functionField M.functionField := hE
  have hb := isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ W.functionField M.functionField) n
  exact hη (injective_of_isBaseChange_field hb (h0.trans (map_zero _).symm))

end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalTopFormPullbackNeZeroOfEtaleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → (U : Set M).Nonempty → ∀ η : RatForms p n, η ≠ 0 → GlobalTheory.EtaleKlt.ratPull p f n η ≠ 0 := by
  first | exact @GlobalTheory.EtaleKlt.ratPull_ne_zero | exact GlobalTheory.EtaleKlt.ratPull_ne_zero | (intros; apply GlobalTheory.EtaleKlt.ratPull_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalIffEtalePullback

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem kltAt_iff_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  intro M W _ _ _ _ p f _ n m _ _ U D₀ D₁ hU hm hD y hy
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme M := ModifSections.isNormalScheme_of_smooth (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := ModifSections.isNormalScheme_of_smooth p
  have hnM := NadelApp.topologicalKrullDim_eq_of_smooth M (f ≫ p) n
  have hnW := NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hne : ∀ η : RatForms p n, η ≠ 0 → ratPull p f n η ≠ 0 := GlobalTheory.T.rationalTopFormPullback_ne_zero_of_etale M W p f n U hU ⟨y, hy⟩
  have hlog : ∀ (η : RatForms p n) (m' : ℕ) (g : W.functionFieldˣ), η ≠ 0 →
      IsLogEqn p (qWeil D₀ m) η (f y) m' g →
      IsLogEqn (f ≫ p) (qWeil D₁ m) (ratPull p f n η) y m'
        (Units.map (functionFieldMap f).toMonoidHom g) := by
    intro η m' g hη h z hz E' hE'
    have hzU : z ∈ U := hz.mem_open U.isOpen hy
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.exists_primeDivisor_etalePullback_orders M W p f n U hU z hzU E' hE'
    have key := h (f z) (hz.map f.continuous) E hE
    obtain ⟨d, hd⟩ := D₀.exists_isEqn (f z)
    have hd' := hD z d hd
    have hmult : D₁.mult z = D₀.mult (f z) := by
      rw [hd'.mult_eq, hd.mult_eq, ← hE'.ord_eq, ← hE.ord_eq, hord]
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [hf, hord, ← key]
    simp [qWeil, hmult]
  constructor
  · intro hk
    obtain ⟨η, hη, hG⟩ := isLogCanonicalMultiple_canonical (p := p) (n := n) hnW D₀ hm
    obtain ⟨g, hg⟩ := (m • canonical p n + D₀).exists_isEqn (f y)
    have h1 := hG (f y) g hg
    refine (h1.kltAt_iff hnW hη hm).2 fun E hE => ?_
    obtain ⟨E', hE', hord, hform⟩ := GlobalTheory.T.primeDivisor_lift_along_etale_map M W p f n U hU y hy E hE
    have h2 := ((hlog η m g hη h1).kltAt_iff hnM (hne η hη) hm).1 hk E' hE'
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [discrep, hord, hf] at h2
    exact h2
  · rintro ⟨η, m', g, hη, hm', h1, h2⟩
    refine ⟨ratPull p f n η, m', _, hne η hη, hm', hlog η m' g hη h1, fun E' hE' => ?_⟩
    obtain ⟨E, hE, hord, hform⟩ := GlobalTheory.T.primeDivisorOver_restrict_etale M W p f n U hU y hy E' hE'
    have h3 := h2 E hE
    rw [discrep] at h3 ⊢
    have hf : E'.formOrd (ratPull p f n η) = E.formOrd η := hform η hη
    rw [hord, hf]
    exact h3
end GlobalTheory.EtaleKlt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalIffEtalePullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.kawamataLogTerminal_iff_etale_pullback : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n m : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens) (D₀ : CartierDiv W) (D₁ : CartierDiv M), Etale (U.ι ≫ f) → 0 < m → (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) → ∀ y ∈ U, (GlobalTheory.Discrepancy.KltAt (f ≫ p) n (GlobalTheory.Discrepancy.qWeil D₁ m) y ↔ GlobalTheory.Discrepancy.KltAt p n (GlobalTheory.Discrepancy.qWeil D₀ m) (f y)) := by
  first | exact @GlobalTheory.EtaleKlt.kltAt_iff_etale | exact GlobalTheory.EtaleKlt.kltAt_iff_etale | (intros; apply GlobalTheory.EtaleKlt.kltAt_iff_etale <;> assumption)
end
end
