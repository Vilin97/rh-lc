module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFrameCongruenceUnitaryAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHomLatticeIffFrameStabilizerActMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOne

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottomStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  first | exact @GlobalTheory.VacFixTarget.exists_open_fix_vac_target | exact GlobalTheory.VacFixTarget.exists_open_fix_vac_target | (intros; apply GlobalTheory.VacFixTarget.exists_open_fix_vac_target <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruenc

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.HeckeLevel

theorem add_mul_sub_one {R : Type} [CommRing R] (m c : ℕ) (w : R) :
    1 + ((m * c : ℕ) : R) * w - 1 = m • ((c : R) * w) := by
  rw [nsmul_eq_mul]
  push_cast
  ring

theorem exists_level : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  intro D ν hν
  obtain ⟨N₀, hN₀, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν.1
  refine ⟨N₀, hN₀, ?_⟩
  rintro N ⟨c, rfl⟩ u hu ⟨w, hw, e⟩ ⟨w', hw', e'⟩
  have key : ∀ z : Af D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z : Lev.EAf D) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E → z ∈ intAE D :=
    fun z hz => (GlobalTheory.IdemSupport.mem_intAE_iff z).2 hz
  have hint : ∀ (a : AE D) (v : Lev.EAf D), v ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D a = 1 + ((N₀ * c : ℕ) : Lev.EAf D) * v → finPart D a ∈ intAE D := by
    intro a v hv ha
    refine key _ ?_
    change toEAf D a ∈ _
    rw [ha]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ _) hv)
  refine hker u ⟨hu, hint _ w hw e, hint _ w' hw' e'⟩
    ⟨(Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm ((c : Lev.EAf D) * w), key _ ?_, ?_⟩
  · rw [AlgEquiv.apply_symm_apply]
    exact mul_mem (natCast_mem _ _) hw
  · apply (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    rw [map_sub, map_one, map_nsmul, AlgEquiv.apply_symm_apply]
    have e2 : (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D (u : AE D)) : Lev.EAf D) =
      1 + ((N₀ * c : ℕ) : Lev.EAf D) * w := e
    rw [e2]
    exact add_mul_sub_one N₀ c w

end GlobalTheory.HeckeLevel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelUnitaryHeckeCharacterTrivialCongruencStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ∣ N → ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1 := by
  first | exact @GlobalTheory.HeckeLevel.exists_level | exact GlobalTheory.HeckeLevel.exists_level | (intros; apply GlobalTheory.HeckeLevel.exists_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardPairFirstInvariantCongruenceOneStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.standardPairFirst_invariant_congruenceOne : ∀ (D : D7) (A WW : HSp D) (ν : (AE D)ˣ →* Circle) (e : AE D) (Sf : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e Sf → ∀ (I : Ideal (𝓞 D.host.E)) (βA : GL (Fin A.rank) (Lev.EAf D)) (βW : GL (Fin WW.rank) (Lev.EAf D)) (N : ℕ), 0 < N → ((N : ℕ) : 𝓞 D.host.E) ∈ I → (∀ w ∈ Sf, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) → (∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (u : AE D) = 1 + (N : Lev.EAf D) * w) → (∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 + (N : Lev.EAf D) * w) → ν u = 1) → ∀ (κ : GA D WW) (z : GL (Fin WW.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), Formalism.L2.DIV.frGL βW z = Lev.finE WW κ → (∀ a b, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ((z.1 a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) - (1 : Matrix (Fin WW.rank) (Fin WW.rank) (Lev.EAf D)) a b = (N : Lev.EAf D) * w) → ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW (actO (GlobalTheory.Grid.neg A) WW 1 κ x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I A WW βA βW x := by
  first | exact @GlobalTheory.StdFstInv.stdFst_actO | exact GlobalTheory.StdFstInv.stdFst_actO | (intros; apply GlobalTheory.StdFstInv.stdFst_actO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVector

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.RowTest

theorem IsBottomTri.exists_open_fix_f : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  have h := hX.is
  have hom := h.weil t
  have hT2 : IsHeckeChar D ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) :=
    hom.hecT
  have hx : ∀ x, ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) x =
      (((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) / (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2))) x)⁻¹ := fun x => by
    rw [MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
  have hνH : IsHeckeChar D ((L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) :=
    ⟨hT2.1.inv.congr fun x => (hx x).symm, fun x => by rw [hx, hT2.2, inv_one]⟩
  obtain ⟨N₀, hN₀, hN₀'⟩ := GlobalTheory.T.exists_level_unitaryHeckeCharacter_trivial_congruence D _ hνH
  have hI : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  set N : ℕ := N₀ * Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal with hNdef
  have hNpos : 0 < N := by
    refine Nat.pos_of_ne_zero (mul_ne_zero (mul_ne_zero hN₀.ne' ?_) (Finset.prod_ne_zero_iff.2 fun w _ => ?_))
    · exact fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    · exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hNI : ((N : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t := by
    rw [hNdef, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))
  have hNw : ∀ w ∈ locPl G t, ((N : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w : Formalism.L2.DIV.Pl D.host.E => Ideal.absNorm w.asIdeal) hw
    rw [hNdef, hc, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _))
  have hNdiv : N₀ ∣ N := ⟨Ideal.absNorm (X.ideal (locPl G) t) * ∏ w ∈ locPl G t, Ideal.absNorm w.asIdeal, by rw [hNdef, mul_assoc]⟩
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.T.exists_open_frame_congruence_unitaryAdelic D WW X.rW.β N hNpos
  refine ⟨U, hUo, fun κ hκ _ hvac => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hU κ hκ
  have hst : Lev.finE WW κ ∈ Formalism.L2.DIV.St X.rW.β := ⟨z, hz⟩
  have hinv := GlobalTheory.T.standardPairFirst_invariant_congruenceOne D A WW _ (X.e t) (locPl G t) (h.idem t) (X.ideal (locPl G) t) X.rA.β X.rW.β N hNpos hNI hNw
    (hN₀' N hNdiv) κ z hz hzc
  have hsdA := isSelfDualC_neg' h.rigA.1
  have hsdW := h.rigW.1
  have hsg : ∀ f, (X.ω t).toSgn true (1, κ) f = X.ω t (1, κ) f := fun f => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key := GlobalTheory.ExportSeries.DualType.om_theta_move hom
    (fun Tm hT Ψ hΨ => GlobalTheory.SchrTheta.isTheta_placeModel D W.ψ h.isVac.1 _ WW _ _ hsdA hsdW _
      (GlobalTheory.PlaceDatum.idemSum_mul_self (h.idem t)) (GlobalTheory.PlaceDatum.infPart_idemSum (h.idem t)) _ h.isVac.2.theta Tm hT Ψ hΨ)
    (h.fst t) (h.fst t) (g := 1) (h := κ)
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ hsdA hsdW h.rigA.2.1 h.rigW.2.1 1 κ (by rw [map_one]; exact one_mem _) hst)
    one_ne_zero (c' := 1) (by rw [one_smul, hsg]; exact hvac) (fun x => by rw [one_mul, hinv x])
  rw [hsg, one_mul, one_smul] at key
  exact key

end GlobalTheory.RowTest

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupFixingVacuumFixesVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

theorem _root_.GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac →
      X.ω t (1, κ) (X.f t) = X.f t := by
  first | exact @GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f | exact GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f | (intros; apply GlobalTheory.RowTest.IsBottomTri.exists_open_fix_f <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleOpenSubgroupField

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
namespace GlobalTheory.BottomLevel

theorem fin_vec_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, h₁, hU₁⟩ := GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom hX t
  obtain ⟨U₂, h₂, hU₂⟩ := GlobalTheory.T.definiteBottom_exists_open_fixes_finiteVector hX t
  exact ⟨U₁ ⊓ U₂, h₁.inter h₂, fun κ hκ hf => hU₂ κ hκ.2 hf (hU₁ κ hκ.1 hf)⟩

end GlobalTheory.BottomLevel
end
end
end
