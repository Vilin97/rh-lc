module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerOfMatrixUnitsIdempotentSplitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectionsEighthPowerGrpObjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGrpPullbackOfCompatibleRetractsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixUnitsExtendNormalNoetherianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineBundleEighthPowerIsoPowStatement
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianPullbackAbelianOverOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfEighthPowerStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianFunctionFieldModelArithBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem ratModel_isNoetherian_of_arithBase : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), AlgebraicGeometry.IsNoetherian M.Z := by
  intro o Ω _ _ _ h M
  haveI := h.ded
  haveI := M.lft
  haveI := M.qc
  haveI : IsNoetherianRing (CommRingCat.of o) := inferInstanceAs (IsNoetherianRing o)
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  exact {}

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianFunctionFieldModelArithBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isNoetherian_functionFieldModel_arithBase : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), AlgebraicGeometry.IsNoetherian M.Z := by
  first | exact @GlobalTheory.ratModel_isNoetherian_of_arithBase | exact GlobalTheory.ratModel_isNoetherian_of_arithBase | (intros; apply GlobalTheory.ratModel_isNoetherian_of_arithBase <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegers

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepSiegel

theorem isSeparated_toZ : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  intro g n F
  obtain ⟨N, i, hi, -, e⟩ := F.qproj
  have hs : IsSeparated F.s := by
    rw [← e]
    have : IsSeparated (PSpace.str (cycAway n) N) := by
      unfold PSpace.str
      infer_instance
    infer_instance
  have ht : toZ F.X = F.s ≫ toZ (Sp (cycAway n)) := by
    first
    | exact specULiftZIsTerminal.hom_ext _ _
    | exact specZIsTerminal.hom_ext _ _
  rw [ht]
  infer_instance

end GlobalTheory.SepSiegel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedSiegelModuliOverIntegersStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isSeparated_siegelModuli_over_integers : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)), IsSeparated (toZ F.X) := by
  first | exact @GlobalTheory.SepSiegel.isSeparated_toZ | exact GlobalTheory.SepSiegel.isSeparated_toZ | (intros; apply GlobalTheory.SepSiegel.isSeparated_toZ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotent

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegMin

theorem exists_semiAbelian_idempotent_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  intro S G _ _ hG e he hee
  obtain ⟨H, hgrp, _, i, r, hH, hi, hr, hir, hri⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image S G hG e he hee
  exact ⟨H, hgrp, i, r, hi, hr, hir, hri, hH⟩

end GlobalTheory.SiegMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDirectFactorOfIdempotentStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.semiAbelian_direct_factor_of_idempotent : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ e : G ⟶ G, IsMonHom e → e ≫ e = e → ∃ (H : Over S) (_ : GrpObj H) (i : H ⟶ G) (r : G ⟶ H), IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 H ∧ r ≫ i = e ∧ IsSemiAbelian H := by
  first | exact @GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | exact GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image | (intros; apply GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegFactor.firstFactor : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  intro g n hg hn hodd F W hW o Ω _ _ _ _ β S ρ u hsys M U₀ EE Zh U c hO hOpen
  obtain ⟨-, -, hSg, ⟨c', hc'pb, pr, hpr, huniv, -⟩, -⟩ := hsys
  haveI : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  obtain ⟨inj, hinj, hinjpr, hsum⟩ := GlobalTheory.T.exists_injections_eighthPower_grpObj ρ.P.A c'.A pr hpr huniv
  let E' : Fin 8 → Fin 8 → (ρ.P.A ⟶ ρ.P.A) := fun a b => pr a ≫ inj b
  have hE' : ∀ a b, IsMonHom (E' a b) := fun a b => by
    haveI := hpr a; haveI := hinj b; exact inferInstanceAs (IsMonHom (pr a ≫ inj b))
  have hrel' : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1 := by
    intro a b c d
    show (pr a ≫ inj b) ≫ pr c ≫ inj d = if b = c then pr a ≫ inj d else 1
    rw [Category.assoc, ← Category.assoc (inj b), hinjpr]
    split_ifs
    · rw [Category.id_comp]
    · haveI := hinj d; rw [MonObj.one_comp, MonObj.comp_one]
  haveI : AlgebraicGeometry.IsNoetherian M.Z := GlobalTheory.T.isNoetherian_functionFieldModel_arithBase M
  have hdense : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨E, hE, hrel, hsumE, hcompat⟩ := GlobalTheory.T.exists_matrixUnits_extend_normal_noetherian hO.normal U₀ hdense Zh.G Zh.semi
    ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.u₀ Zh.φ (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _)
    E' hE' hrel' hsum
  have hidem : E 0 0 ≫ E 0 0 = E 0 0 := by rw [hrel]; simp
  obtain ⟨H, _, i, r, hi, hr, hir, hri, hH⟩ := GlobalTheory.T.semiAbelian_direct_factor_of_idempotent M.Z Zh.G Zh.semi (E 0 0) (hE 0 0) hidem
  haveI : IsCommMonObj H := hH.comm
  have huniv8 := GlobalTheory.T.eighthPower_of_matrixUnits_idempotent_split Zh.G H E hE hrel hsumE i r hi hr hir hri
  have hpr8 : ∀ a, IsMonHom (E a 0 ≫ r) := fun a => by
    haveI := hE a 0; haveI := hr; exact inferInstanceAs (IsMonHom (E a 0 ≫ r))
  have hdimG : SmoothOfRelativeDimension (8 * g) Zh.G.hom := hSg ▸ Zh.dim
  have hdim : SmoothOfRelativeDimension g H.hom := GlobalTheory.T.smoothOfRelativeDimension_of_eighth_power H Zh.G g (fun a => E a 0 ≫ r) huniv8 hH hdimG
  have hhodge := GlobalTheory.T.hodgeLineBundle_eighthPower_iso_pow M.Z H Zh.G g (fun a => E a 0 ≫ r) hpr8 huniv8 hH hdim
  obtain ⟨e', he'm, h1, h2⟩ := hcompat 0 0
  obtain ⟨C', _, a, b, ha, hb⟩ := GlobalTheory.T.exists_isGrpPullback_of_compatible_retracts U₀.ι Zh.u₀ Zh.G ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.φ
    (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _) (E 0 0) (E' 0 0) e' he'm h1 h2 H i r hi hr hir hri
    c'.A (inj 0) (pr 0) (hinj 0) (hpr 0) (by simpa using hinjpr 0 0) rfl
  obtain ⟨φ', φ₂, hφ', -, -, -⟩ := hc'pb
  obtain ⟨e, he⟩ := GlobalTheory.T.semiAbelian_pullback_abelian_over_open hO.normal (GlobalTheory.T.isSeparated_siegelModuli_over_integers F) F.univ.A F.univ.ab H hH U₀ U hO.ne hOpen.1
    (Zh.u₀ ≫ u) c C' a (b ≫ φ') ha (hb.comp hφ') Ω M.pt M.gen (fun x y hx hy => by
      rw [hOpen.2.2.2.2 x hx, ← Category.assoc, Zh.u₀_gen y hy])
  refine ⟨H, inferInstance, e, inferInstance, hH, hdim, he, ?_⟩
  rw [hSg]
  exact hhodge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eighth_power_first_factor_theta_model : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  first | exact @GlobalTheory.SiegFactor.firstFactor | exact GlobalTheory.SiegFactor.firstFactor | (intros; apply GlobalTheory.SiegFactor.firstFactor <;> assumption)
end
end
