module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
public import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimilitudeOfAutModLevelIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFramedPointMoveUniversalTripleStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelMoveModuliUniqueUniversalTripleStatement
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnipotentLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

-- Source module: Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPullOfMoveInv

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevPullModel

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LevPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_isLift : ∃ lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La, IsLift lift := by
  have := Dw.proj
  choose lift h using fun γ : Gam Dw l =>
    Module.projective_lifting_property (Submodule.mkQ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
      (γ.toLinearMap ∘ₗ Submodule.mkQ _) (Submodule.mkQ_surjective _)
  exact ⟨lift, h⟩

theorem lift_mk {lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La} (h : IsLift lift) (γ : Gam Dw l) (a : Dw.La) :
    (Submodule.Quotient.mk (lift γ a) : LaQ Dw l) = γ (Submodule.Quotient.mk a) := LinearMap.congr_fun (h γ) a

end GlobalTheory.LevPullModel
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChangesStatement

section

@[expose] public section

open CategoryTheory NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.levelCover_fibre_torsor_trivial_level_changes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  first | exact @GlobalTheory.LevOrbit.fibre_torsor | exact GlobalTheory.LevOrbit.fibre_torsor | (intros; apply GlobalTheory.LevOrbit.fibre_torsor <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LevelGroupEqTopOfCoprime

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelGroupTest

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem natCast_mem_half (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := by
    rw [← l.prod]; exact Ideal.mul_le_left
  exact h (Ideal.subset_span rfl)

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

end GlobalTheory.LevelGroupTest
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedBlockSelfApply

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LevelSpanCompare

section Move

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

theorem reflects_half_of_move {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {gM gA : Dw.La →ₗ[𝓞 E] Dw.La}
    (h : IsLevMove ρ ν gM gA) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (b : KA l →+* k)
    (hx : x ≫ Xo.s = spMap b) (a : Dw.La) (ha : gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨hs, hM, -⟩ := h
  obtain ⟨-, J, -, -, hJM⟩ := Xo.univ.geom k (x ≫ ρ) b (by rw [Category.assoc, hs]; exact hx)
  have h1 : a ∈ (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [l.coprime]; simp
  rw [Submodule.sup_smul] at h1
  obtain ⟨b, hb, a', ha', rfl⟩ := Submodule.mem_sup.1 h1
  have hgb : gM b ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.mem_map_of_mem (f := gM) hb
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hga : gM a' ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    have := Submodule.sub_mem _ ha hgb
    simpa using this
  have e1 : ρ ≫ (Xo.univ.eta a').left = ρ ≫ (Xo.univ.eta 0).left := by
    rw [← hM a', ← hM 0, Xo.univ.eta_ker _ hga, Xo.univ.eta_ker (gM 0) (by simp)]
  have e5 : J.ev l.M a' = J.ev l.M 0 := by
    rw [← hJM _ ha', ← hJM _ (Submodule.zero_mem _)]
    ext
    simpa using congrArg (x ≫ ·) e1
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have e6 : J.ev l.M 0 = 1 := (J.ker l.M hM0 0).2 ⟨0, by simp⟩
  obtain ⟨b', hb'⟩ := (J.ker l.M hM0 a').1 (e5.trans e6)
  refine Submodule.add_mem _ hb ?_
  rw [hb', ← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (GlobalTheory.LevelGroupTest.natCast_mem_half l) trivial

theorem levR_unique (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (gM : Dw.La →ₗ[𝓞 E] Dw.La)
    {S : Type} [CommRing S] [Algebra c.F S] [Nontrivial S] {y y' y'' : FrPt Xo c S}
    (h' : levR (gM, LinearMap.id) y y') (h'' : levR (gM, LinearMap.id) y y'') : y' = y'' := by
  obtain ⟨ρ, ν, i, h, hm⟩ := h'
  obtain ⟨ρ', ν', i', g, gm⟩ := h''
  obtain ⟨m, hmax⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  let φ : S →+* AlgebraicClosure (S ⧸ m) := (algebraMap (S ⧸ m) _).comp (Ideal.Quotient.mk m)
  have hinj := reflects_half_of_move h (AlgebraicClosure (S ⧸ m)) (spMap φ ≫ y.x)
    (φ.comp ((algebraMap c.F S).comp (IntermediateField.inclusion c.le).toRingHom)) (by
      rw [Category.assoc, y.x_over]
      unfold sOf spMap
      rw [← Spec.map_comp]; rfl)
  obtain ⟨rfl, e⟩ := GlobalTheory.T.levelMove_moduli_unique_universalTriple E H Dw l Xo c ρ ρ' ν ν' _ _ _ _ hpq (fun a => by simp) (fun a => ⟨0, by simp⟩) i i' h g
    (GlobalTheory.exists_sim_of_aut_mod E H Dw l l.A gM hpq l.A_pos hA hinj)
  exact (GlobalTheory.T.existsUnique_framedPoint_move_universalTriple E H Dw l Xo c ρ ν h.1 S y).2 y' y'' ν' e.symm hm gm

end Move

section Idem

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GoodLatCompare

end Idem

section Framed

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Framed

section Swap

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Herm Formalism.UG Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

variable {β : GL (Fin n) (E ⊗[F] Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}

end Swap

section Half

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Lev Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}

end Half

end GlobalTheory.LevelSpanCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConst

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevDegree

theorem card_lifts_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ _ y y'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hpq : Dw.p ≠ Dw.q ∧ 1 ≤ Dw.p + Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hk : ∀ a : c.F, algebraMap d.c₂.F (CAt σ₂) (d.eF a) = algebraMap c.F (CAt σ₂) a := fun _ => rfl
  obtain ⟨lift, hlift⟩ := GlobalTheory.LevPullModel.exists_isLift (Dw := Dw) (l := d.l₂)
  have hov : ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom :=
    GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hA d
  have L := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq.2 hA₂
    (fun a => (Submodule.Quotient.eq _).1 ((GlobalTheory.LevPullModel.lift_mk hlift 1 a).trans rfl))
    (fun g h a => (Submodule.Quotient.eq _).1 (by
      rw [GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift]; rfl))
  have key : ∀ y : FrPt Xo c (CAt σ₂),
      Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} =
        Nat.card {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} := by
    intro y
    obtain ⟨y₀, hy₀⟩ := hd.2.2.2.2.2.2.1 (CAt σ₂) hk y
    have T := GlobalTheory.T.levelCover_fibre_torsor_trivial_level_changes D.host.E H Dw l Xo c d hpq.2 hd hA₂ hov lift hlift (CAt σ₂) hk y₀
    have hA₂' : d.l₂.A.Coprime d.l₂.M := by rw [hA₂]; exact Nat.coprime_one_left _
    have hex : ∀ γ : Gam Dw d.l₂, ∃ y₂', levR (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La)) y₀ y₂' :=
      fun γ => L.total γ (CAt σ₂) y₀
    choose g hg using hex
    let f : {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} →
        {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} :=
      fun γ => ⟨g γ.1, ((T (g γ.1) y hy₀).1).2 ⟨γ.1, γ.2, hg γ.1⟩⟩
    refine (Nat.card_eq_of_bijective f ⟨fun γ γ' e => Subtype.ext ?_, fun z => ?_⟩).symm
    · have e' : g γ.1 = g γ'.1 := congrArg Subtype.val e
      exact (T (g γ.1) y hy₀).2 γ.1 γ'.1 (hg γ.1) (e' ▸ hg γ'.1)
    · obtain ⟨γ, hγ, hl⟩ := ((T z.1 y hy₀).1).1 z.2
      exact ⟨⟨γ, hγ⟩, Subtype.ext (GlobalTheory.LevelSpanCompare.levR_unique hpq.2 hA₂' (lift γ) (hg γ) hl)⟩
  exact (key y).trans (key y').symm

end GlobalTheory.LevDegree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardFramedLiftsLevelCoverConstStatement

section

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.card_framed_lifts_levelCover_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  first | exact @GlobalTheory.LevDegree.card_lifts_const | exact GlobalTheory.LevDegree.card_lifts_const | (intros; apply GlobalTheory.LevDegree.card_lifts_const <;> assumption)
end
end
