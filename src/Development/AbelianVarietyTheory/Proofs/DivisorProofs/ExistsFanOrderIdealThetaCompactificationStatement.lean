module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealOrdersOfProperModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrdersStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPiecesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  first | exact @GlobalTheory.Poinc.exists_valOn_of_pieces | exact GlobalTheory.Poinc.exists_valOn_of_pieces | (intros; apply GlobalTheory.Poinc.exists_valOn_of_pieces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ (X₁ : Setup F W8 i) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → IsProjOver X₁.M.s → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι' * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders | exact GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders | (intros; apply GlobalTheory.Poinc.DescentPow.exists_idealSheaf_comap_orders <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemGenericPointsClosureEqOfIsClopen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory

theorem exists_mem_genericPoints_closure_eq_of_isClopen :
    ∀ (X Z : Scheme.{0}) (i : X ⟶ Z), IsOpenImmersion i → Dense (Set.range i) → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ η ∈ genericPoints X, closure {i η} = W := by
  intro X Z i hi hd W hWc hWi
  have he : Topology.IsOpenEmbedding i := i.isOpenEmbedding

  have hgen : IsGenericPoint hWi.genericPoint W :=
    hWi.isGenericPoint_genericPoint hWc.isClosed
  have hne : (W ∩ Set.range i).Nonempty :=
    hd.inter_open_nonempty W hWc.isOpen hWi.nonempty
  have hmem : hWi.genericPoint ∈ Set.range i :=
    (hgen.mem_open_set_iff he.isOpen_range).2 hne
  obtain ⟨η, hη⟩ := hmem
  have hcl : closure {i η} = W := by rw [hη]; exact hgen
  refine ⟨η, ?_, hcl⟩

  have hpre : closure ({η} : Set X) = i ⁻¹' W := by
    rw [← hcl, he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous,
      ← Set.image_singleton, he.injective.preimage_image]
  show closure ({η} : Set X) ∈ irreducibleComponents X
  have hirr : IsIrreducible (closure ({η} : Set X)) := isIrreducible_singleton.closure
  have hclo : IsClopen (closure ({η} : Set X)) := by
    rw [hpre]; exact hWc.preimage he.continuous
  refine ⟨hirr, fun T hT hsub => ?_⟩
  refine hT.2.isPreconnected.subset_isClopen hclo ?_
  exact ⟨η, hsub (subset_closure rfl), subset_closure rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc


theorem _root_.GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ X₁ : Setup F W8 i, ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_model_divisor_of_orders | exact GlobalTheory.Poinc.exists_model_divisor_of_orders | (intros; apply GlobalTheory.Poinc.exists_model_divisor_of_orders <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailTail

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W hWc hWi
  obtain ⟨hproj, hnorm, hopen, hcomp, hdense, W8, hE8, hTI⟩ := id hθ
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.exists_mem_genericPoints_closure_eq_of_isClopen F.X Z i hopen hdense W hWc hWi
  obtain ⟨X₁, -, hX₁⟩ := GlobalTheory.Poinc.GSetup.exists_setup g n hg hn hodd F Z z i hproj
    (fun x => ⟨hnorm.isDomain_stalk x, hnorm.isIntegrallyClosed_stalk x⟩) hopen hcomp hdense W8 hE8 hTI η hη 0
  have hr := GlobalTheory.Poinc.Setup.range_π_eq g n F W8 Z i X₁ η W hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ :=
    GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁ ι Y πY D hι X₁.projM hhom hprop hnY hsupp hord
  have hhomog : ∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β := by
    intro T k _
    have hrk : Module.finrank ℤ T.D.toPre.X ≤ g := by
      have := GlobalTheory.Poinc.Trait.dim_add_rank (by omega : 2 ≤ n) F T
      omega
    have hβ : T.β ∈ balForms (id : ℤ → ℤ) T.D.toPre.X := ⟨T.symm, fun a y z => by simp⟩
    rw [natCast_zsmul, StrictData.evalZ_eq, StrictData.evalZ_eq, StrictData.toReal_nsmul]
    exact (hφ _ hrk).homog _ (StrictData.toReal_mem_psdCone hβ fun y => T.mono.nonneg 0 y) _ (Nat.cast_nonneg k)
  obtain ⟨hs, ho⟩ := GlobalTheory.Poinc.ideal_orders_of_proper_model g n F W8 Z i φ X₁ Y πY hhom hprop ι' J₁ hsupp' hord' hhomog
  exact ⟨W8, X₁, ι', J₁, hι', hr, hs, ho⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupIdealOverClopenComponentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_setup_ideal_over_component | exact GlobalTheory.Poinc.exists_setup_ideal_over_component | (intros; apply GlobalTheory.Poinc.exists_setup_ideal_over_component <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartitionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem _root_.GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z), (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  first | exact @GlobalTheory.irreducibleComponents_clopen_partition | exact GlobalTheory.irreducibleComponents_clopen_partition | (intros; apply GlobalTheory.irreducibleComponents_clopen_partition <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactificationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification : IdealSt := by
  first | exact @GlobalTheory.Poinc.idealSt_holds | exact GlobalTheory.Poinc.idealSt_holds | (intros; apply GlobalTheory.Poinc.idealSt_holds <;> assumption)
end
end
