module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatQuotientIsoOfSameKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfFiniteFibresStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlatStatement
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KilledAnyOf
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PolFibreIsogAny
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCore
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlat

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.Dblock

theorem epiOfFF : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  intro R _ A B A' l hf hs hq g₁ g₂ h
  have : EffectiveEpi l.left := inferInstance
  have : Epi l.left := inferInstance
  apply Over.OverMorphism.ext
  rw [← cancel_epi l.left]
  simpa using congrArg (fun k => k.left) h

end GlobalTheory.CompanionTheory.Dblock
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpiOfFiniteFlatStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.epi_of_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.EpiOfFF := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.epiOfFF | exact GlobalTheory.CompanionTheory.Dblock.epiOfFF | (intros; apply GlobalTheory.CompanionTheory.Dblock.epiOfFF <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlat

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp)

namespace GlobalTheory.CompanionTheory.FlatFactor

theorem ext_of_affine_points {R : Type} [CommRing R] {W X : Over (Sp R)} (u v : W ⟶ X)
    (h : ∀ (S : Type) [CommRing S] [Algebra R S] (t : sp (R₀ := R) S ⟶ W), t ≫ u = t ≫ v) : u = v := by
  have key : ∀ (B : CommRingCat.{0}) (j₀ : Spec B ⟶ W.left), j₀ ≫ u.left = j₀ ≫ v.left := by
    intro B j₀
    letI : Algebra R B := (Spec.preimage (j₀ ≫ W.hom)).hom.toAlgebra
    let j : sp (R₀ := R) B ⟶ W := Over.homMk j₀ (Spec.map_preimage (j₀ ≫ W.hom)).symm
    exact congrArg CommaMorphism.left (h B j)
  apply Over.OverMorphism.ext
  exact Scheme.Cover.hom_ext W.left.affineCover _ _ fun i => key _ _

theorem comp_eq_of_comp_eq {R : Type} [CommRing R] {A B A' : Over (Sp R)} [GrpObj A] [GrpObj B] [GrpObj A']
    (l : A ⟶ B) (f : A ⟶ A') [IsMonHom l] [IsMonHom f]
    (hk : ∀ (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ A), z ≫ l = 1 → z ≫ f = 1)
    {W : Over (Sp R)} (a b : W ⟶ A) (h : a ≫ l = b ≫ l) : a ≫ f = b ≫ f := by
  refine ext_of_affine_points _ _ fun S _ _ t => ?_
  have h1 : ((t ≫ a) / (t ≫ b)) ≫ l = 1 := by
    rw [GrpObj.div_comp, Category.assoc, Category.assoc, h, div_self']
  have h2 := hk S _ h1
  rw [GrpObj.div_comp, div_eq_one] at h2
  simpa using h2

theorem factorThroughFF : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  intro R _ A B A' _ _ _ l f hl hf hfl hsl hql hk
  have hc : ∀ {Z : Scheme.{0}} (g g' : Z ⟶ A.left), g ≫ l.left = g' ≫ l.left →
      g ≫ f.left = g' ≫ f.left := by
    intro Z g g' h
    have hw : g' ≫ A.hom = g ≫ A.hom := by
      rw [← Over.w l, ← Category.assoc, ← h, Category.assoc]
    have := comp_eq_of_comp_eq l f hk (W := Over.mk (g ≫ A.hom))
      (Over.homMk g rfl) (Over.homMk g' hw) (Over.OverMorphism.ext h)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac l.left f.left hc
  let g : B ⟶ A' := Over.homMk (EffectiveEpi.desc l.left f.left hc) (by
    rw [← cancel_epi l.left, ← Category.assoc, hfac, Over.w, Over.w])
  have hg : l ≫ g = f := Over.OverMorphism.ext hfac
  refine ⟨g, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom l, Category.assoc, hg, IsMonHom.one_hom]
  · have := GlobalTheory.FlatQuotient.epi_tensorHom l l
    rw [← cancel_epi (l ⊗ₘ l), ← IsMonHom.mul_hom_assoc, hg, tensorHom_comp_tensorHom_assoc, hg,
      IsMonHom.mul_hom]

end GlobalTheory.CompanionTheory.FlatFactor
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorThroughFiniteFlatStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.factor_through_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.FactorThroughFF := by
  first | exact @GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | exact GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF | (intros; apply GlobalTheory.CompanionTheory.FlatFactor.factorThroughFF <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFinite

section

@[expose] public section

namespace GlobalTheory.CompanionTheory.FlatFib

theorem flatOfFibresFinite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  intro R _ X Y f h1 h0 h2 h3 H
  exact GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres _ X Y f h1 h0 h2 h3 H

end GlobalTheory.CompanionTheory.FlatFib
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfFibresFiniteStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.flat_of_fibres_finite : PositivityTheory.Tls2.Zar3.Ch1.FlatOfFibresFinite := by
  first | exact @GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | exact GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite | (intros; apply GlobalTheory.CompanionTheory.FlatFib.flatOfFibresFinite <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIsMonHomIdPow

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

theorem qi_isMonHom_id_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (1 : A ⟶ A))
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

theorem quasiInverseR_of (h1 : PolFibreIsogAny) (h5 : KilledAny) : QuasiInverseR := by
  intro C _ _ v R _ _ hv A B _ _ P l g hA hB hgA hgB h₁ h₂ hp
  have hm : IsMonHom l := hp.1
  have fib := h1 C v R hv A B P l g hA hB hgA hgB h₁ h₂ hp
  obtain ⟨hf, hs⟩ := GlobalTheory.T.finite_of_finite_fibres R A B l hA hB hm fun Ω _ _ s => ⟨(fib Ω s).1, (fib Ω s).2.2⟩
  have := hA.comm
  have := hA.smooth
  have := hB.smooth
  have hfl : Flat l.left := GlobalTheory.T.flat_of_fibres_finite R A B l inferInstance inferInstance inferInstance hf
    fun Ω _ _ s => (fib Ω s).2.1
  obtain ⟨F, _, _, h, hsub, hker⟩ := GlobalTheory.T.kernel_finite_flat R A B l hA hB hm hf hfl
  obtain ⟨n, hn, hk⟩ := h5 C v R hv A F h hsub
  obtain ⟨g, hg, e⟩ := GlobalTheory.T.factor_through_finite_flat R A B A l (𝟙 A ^ n) hm (qi_isMonHom_id_pow A n) hfl hs inferInstance
    fun S _ _ z hz => by
      obtain ⟨φ, rfl⟩ := (hker S z).1 hz
      rw [MonObj.comp_pow, Category.comp_id]
      exact hk S φ
  refine ⟨n, g, hn, hg, e, GlobalTheory.T.epi_of_finite_flat R A B B l hfl hs inferInstance _ _ ?_⟩
  rw [← Category.assoc, e, MonObj.comp_pow, MonObj.pow_comp, Category.id_comp, Category.comp_id]

theorem polFibreIsogAny : PolFibreIsogAny := Z2.polFibreIsogAny

theorem killedAny : KilledAny := killedAny_of Qi.killedCore

theorem quasiInverseR : QuasiInverseR := quasiInverseR_of polFibreIsogAny killedAny

end PositivityTheory.PrwZar
end
end
end
