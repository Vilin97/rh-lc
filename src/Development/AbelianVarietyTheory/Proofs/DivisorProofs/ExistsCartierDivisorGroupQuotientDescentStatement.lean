module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotient

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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem functionFieldMap_fnOf (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {x : X}
    (hx : x ∈ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from hx)) s) =
      GlobalTheory.Cartier.fnOf (f ⁻¹ᵁ U) (GlobalTheory.Cartier.gen_mem hx) (f.app U s) := by
  rw [← GlobalTheory.Cartier.algebraMap_germ (show f x ∈ U from hx), functionFieldMap_algebraMap,
    ← GlobalTheory.Cartier.algebraMap_germ hx]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply f U x hx s

theorem fnOf_appLE (f : X ⟶ Y) [IsDominant f] {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    {x : X} (hx : x ∈ V) (s : Γ(Y, U)) :
    GlobalTheory.Cartier.fnOf V (GlobalTheory.Cartier.gen_mem hx) (f.appLE U V e s) =
      functionFieldMap f (GlobalTheory.Cartier.fnOf U (GlobalTheory.Cartier.gen_mem (show f x ∈ U from e hx)) s) := by
  rw [functionFieldMap_fnOf f (e hx)]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact X.presheaf.germ_res_apply (homOfLE e) _ _ _

end GlobalTheory.FnPull

namespace GlobalTheory.FnPull

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {Γ : Type} [Group Γ]

theorem functionFieldMap_act (ρ : Γ →* Aut X) (q : X ⟶ Y) [IsDominant q]
    (hq : ∀ g, (ρ g).asIso.hom ≫ q = q) (hs : Function.Surjective q) (g : Γ) [IsDominant (ρ g).asIso.hom]
    (c : Y.functionField) :
    functionFieldMap (ρ g).asIso.hom (functionFieldMap q c) = functionFieldMap q c := by
  obtain ⟨U₀, hη, s, rfl⟩ := Y.presheaf.exists_germ_eq c
  obtain ⟨x, hx⟩ := hs (genericPoint Y)
  have hx' : x ∈ q ⁻¹ᵁ U₀ := show q x ∈ U₀ from hx ▸ hη
  change functionFieldMap (ρ g).asIso.hom (functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)) =
    functionFieldMap q (GlobalTheory.Cartier.fnOf U₀ hη s)
  rw [functionFieldMap_fnOf q hx' s]
  obtain ⟨e, hinv⟩ := isInvariantSection_app ρ q hq U₀ s g
  rw [← fnOf_appLE (ρ g).asIso.hom e hx', hinv]

theorem isInvariantSection_of_fnOf [Finite Γ] {ρ : Γ →* Aut X} {q : X ⟶ Y} [IsDominant q]
    (h : IsAffineQuotient ρ q) {V : Y.Opens} {x : X} (hx : x ∈ q ⁻¹ᵁ V) (c : Γ(X, q ⁻¹ᵁ V))
    (b : Y.functionField) (hc : GlobalTheory.Cartier.fnOf _ (GlobalTheory.Cartier.gen_mem hx) c = functionFieldMap q b) :
    IsInvariantSection ρ _ c := fun g ↦ by
  haveI : IsIso (ρ g).asIso.hom := Iso.isIso_hom _
  refine ⟨h.preimage_le V g, GlobalTheory.Cartier.fnOf_injective _ (GlobalTheory.Cartier.gen_mem hx) ?_⟩
  rw [fnOf_appLE (ρ g).asIso.hom (h.preimage_le V g) hx, hc,
    functionFieldMap_act ρ q h.comp_eq h.surjective.surj g]

end GlobalTheory.FnPull

namespace GlobalTheory.OrbitSep

theorem unitAt_of_forall_unitAt_fibre : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  intro X W _ _ Γ _ _ ρ q _ h y b hb
  have hsurj : Function.Surjective q := h.surjective.surj
  haveI := h.isIntegralHom
  let O : Set X := {x | GlobalTheory.Cartier.UnitAt x (functionFieldMap q b)}
  have hOo : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx ↦ by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hx
    exact ⟨U, fun z hz ↦ hU z hz, U.isOpen, hxU⟩
  have hV : IsOpen (q '' Oᶜ)ᶜ := (q.isClosedMap _ hOo.isClosed_compl).isOpen_compl
  let V : W.Opens := ⟨_, hV⟩
  obtain ⟨x₀, hx₀⟩ := hsurj y
  have hyV : y ∈ V := fun ⟨x, hx, e⟩ ↦ hx (hb x e)
  have hx₀V : x₀ ∈ q ⁻¹ᵁ V := show q x₀ ∈ V from hx₀ ▸ hyV
  have hUO : ∀ x ∈ q ⁻¹ᵁ V, GlobalTheory.Cartier.UnitAt x (functionFieldMap q b) := fun x hx ↦ by
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hUO
  have hgen := GlobalTheory.Cartier.gen_mem hx₀V
  have ha1 : GlobalTheory.Cartier.fnOf _ hgen (a : Γ(X, q ⁻¹ᵁ V)) = functionFieldMap q b := ha hgen
  have ha2 : GlobalTheory.Cartier.fnOf _ hgen ((a⁻¹ : Γ(X, q ⁻¹ᵁ V)ˣ) : Γ(X, q ⁻¹ᵁ V)) =
      functionFieldMap q b⁻¹ := by
    rw [map_units_inv, ha1, map_inv₀]
  obtain ⟨t, ht⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b ha1)
  obtain ⟨t', ht'⟩ := h.mem_range_app V _ (GlobalTheory.FnPull.isInvariantSection_of_fnOf h hx₀V _ b⁻¹ ha2)
  have htt : t * t' = 1 := h.app_injective V (by rw [map_mul, ht, ht', Units.mul_inv, map_one])
  let u : Γ(W, V)ˣ := ⟨t, t', htt, by rw [mul_comm]; exact htt⟩
  have hgenW := GlobalTheory.Cartier.gen_mem hyV
  have hbu : GlobalTheory.Cartier.fnOf V hgenW t = b := (functionFieldMap q).injective (by
    rw [GlobalTheory.FnPull.functionFieldMap_fnOf q hx₀V t, ht, ha1])
  rw [← hbu]
  exact GlobalTheory.Cartier.unitAt_fnOf hyV hgenW u

end GlobalTheory.OrbitSep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionUnitAtPointOfFibreQuotientStatement

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

theorem _root_.GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (y : W) (b : W.functionField),
    (∀ x, q x = y → UnitAt x (functionFieldMap q b)) → UnitAt y b := by
  first | exact @GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | exact GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre | (intros; apply GlobalTheory.OrbitSep.unitAt_of_forall_unitAt_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescent

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

namespace GlobalTheory.Cartier.Descent

theorem unitAt_functionFieldMap {X W : Scheme.{0}} [IsIntegral X] [IsIntegral W] (q : X ⟶ W)
    [IsDominant q] (x : X) {f : W.functionField} (h : UnitAt (q x) f) :
    UnitAt x (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap x a, ha.map _, (functionFieldMap_algebraMap q x a).symm⟩

theorem exists_cartierDiv_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  intro X W _ _ Γ _ _ ρ q _ hq D h
  choose b hb using h
  have : IsIntegralHom q := hq.isIntegralHom
  have hcl : IsClosedMap q := q.isClosedMap

  have hloc : ∀ y : W, ∃ U : W.Opens, y ∈ U ∧ ∃ f, ∀ y' ∈ U, germOf y' (b y') = germOf y' f := by
    intro y
    let O : Set X := {x | D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom (b y))}
    have hO : IsOpen O := isOpen_iff_forall_mem_open.2 fun x hx => by
      obtain ⟨U, hU, hU'⟩ := CartierDiv.IsEqn.exists_nhds hx
      exact ⟨U, fun z hz => hU' z hz, U.isOpen, hU⟩
    have hZ : IsClosed (q '' Oᶜ) := hcl _ hO.isClosed_compl
    refine ⟨⟨(q '' Oᶜ)ᶜ, hZ.isOpen_compl⟩, ?_, b y, fun y' hy' => ?_⟩
    · rintro ⟨x, hx, hxy⟩
      exact hx (hb y x hxy)
    · refine (germOf_eq_iff.2 ?_).symm
      refine GlobalTheory.T.rationalFunctionUnitAtPoint_of_fibre_quotient X W Γ ρ q hq y' _ fun x hx => ?_
      have h1 : x ∈ O := by
        by_contra hn
        exact hy' ⟨x, hn, hx⟩
      have h2 := (h1 : D.IsEqn x _).iff_unitAt.1 (hb y' x hx)
      simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using h2
  let E : CartierDiv W := show cartierGroup W from ⟨fun y => germOf y (b y), hloc⟩
  refine ⟨E, fun y b' hE x hx => ?_⟩
  have hu : UnitAt y ((b' : W.functionField) / b y) := germOf_eq_iff.1 hE
  subst hx
  refine (hb (q x) x rfl).iff_unitAt.2 ?_
  have := unitAt_functionFieldMap q x hu
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

end GlobalTheory.Cartier.Descent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorGroupQuotientDescentStatement

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

theorem _root_.GlobalTheory.T.exists_cartierDivisor_group_quotient_descent : ∀ (X W : Scheme.{0}) [IsIntegral X] [IsIntegral W] (Γ : Type) [Group Γ] [Finite Γ]
    (ρ : Γ →* Aut X) (q : X ⟶ W) [IsDominant q], IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ y : W, ∃ b : W.functionFieldˣ, ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b)) →
    ∃ E : CartierDiv W, ∀ y b, E.IsEqn y b → ∀ x, q x = y → D.IsEqn x (Units.map (functionFieldMap q).toMonoidHom b) := by
  first | exact @GlobalTheory.Cartier.Descent.exists_cartierDiv_descent | exact GlobalTheory.Cartier.Descent.exists_cartierDiv_descent | (intros; apply GlobalTheory.Cartier.Descent.exists_cartierDiv_descent <;> assumption)
end
end
