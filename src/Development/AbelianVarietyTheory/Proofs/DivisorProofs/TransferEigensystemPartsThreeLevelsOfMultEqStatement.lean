module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SuppFLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevel

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.HeckeLevelFree

theorem ne_under_of_offS {D : D7} {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (hQ : OffS D SF Q) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ SF) :
    v ≠ HeightOneSpectrum.under (𝓞 D.host.F) Q := by
  intro hvq
  obtain ⟨x, hx, hy⟩ := hQ v hv
  have hx' : x ∈ (HeightOneSpectrum.under (𝓞 D.host.F) Q).asIdeal := hvq ▸ hx
  have hmem : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ Q.asIdeal := hx'
  refine hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ?_ hmem
  rfl

theorem rTup_eq_one {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hS : finE V g ∈ St β) : rTup β L (finE V g) = 1 := by
  have hproj : ∀ v ∈ SF, GlobalTheory.FinZeta.projV V v g = 1 := fun v hv =>
    (GlobalTheory.SuppLocal.suppF_local D V Q e f g hef hg).2 v (ne_under_of_offS hQ hv)
  funext PP
  obtain ⟨v, hv, hPv⟩ := hPg PP.1 PP.2
  have hu : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 ∈ SF := by
    have : HeightOneSpectrum.under (𝓞 D.host.F) PP.1 = v := HeightOneSpectrum.ext hPv
    rw [this]; exact hv
  have hr := GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β SF hS hproj hu
  show upperLeftBlock L.hr (redFn β PP.1 (finE V g)) = 1
  rw [hr]; exact blockDiagonalExtendByOnePrimeField_one _ _

theorem mem_and_chi {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hQ : OffS D SF Q) {e f : AE D} (hef : IsPrimeIdem Q e f)
    {g : GA D V} (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) :
    g ∈ levS V β (withP L P') ∧ levChi V β (withP L P) g = levChi V β (withP L P') g := by
  obtain ⟨hG, hl⟩ := hJ
  have hpar : finE V g ∈ parLev D.sp.cm V.gram β (withP L P) := (mem_lev.1 hl).1
  have hS : finE V g ∈ St β := parLev_St hpar
  have h1 : rTup β L (finE V g) = 1 := rTup_eq_one β L hPg hQ hef hg hS
  refine ⟨⟨hG, mem_lev.2 ⟨hpar, ?_⟩⟩, ?_⟩
  · show rTup β L (finE V g) ∈ P'.H
    rw [h1]; exact Subgroup.one_mem _
  · unfold levChi
    rw [levFn_withP, levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]

theorem isHeckeOpFull_imp {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hPg : ∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)) :
    Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp →
      Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  rintro ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, hK, hχ, h4, h5, h6, hR⟩
  have key := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P)) => mem_and_chi β L P P' hPg hQ hef hg hJ
  have key' := fun g (hg : SuppF V f g) (hJ : g ∈ levS V β (withP L P')) => mem_and_chi β L P' P hPg hQ hef hg hJ
  have hset : {k | k ∈ levS V β (withP L P) ∧ SuppF V f k} = {k | k ∈ levS V β (withP L P') ∧ SuppF V f k} := by
    ext k
    exact ⟨fun ⟨a, b⟩ => ⟨(key k b a).1, b⟩, fun ⟨a, b⟩ => ⟨(key' k b a).1, b⟩⟩
  refine ⟨e, f, ϖ, α, hQ, hef, h1, h2, h3, fun g hg => ?_, fun g hJ hg => ?_, h4, h5, h6, hset ▸ hR⟩
  · exact ⟨fun h => (hK g hg).1 ((key' g hg h).1), fun h => (key g hg ((hK g hg).2 h)).1⟩
  · have hJ0 := (key' g hg hJ).1
    rw [← (key g hg hJ0).2]
    exact hχ g hJ0 hg

theorem isHeckeOpFull_withP_iff : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  intro D V β L P P' SF hPg Q d Rp
  exact ⟨isHeckeOpFull_imp β L P P' SF hPg Q d Rp, isHeckeOpFull_imp β L P' P SF hPg Q d Rp⟩

end GlobalTheory.HeckeLevelFree
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHeckeOpFullIffIndependentOfBlockLevelStatement

section

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

theorem _root_.GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P P' : LevelP L.Pg L.r ℂ) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))), (∀ PP ∈ L.Pg, ∃ v ∈ SF, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) → ∀ (Q : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (Rp : Finset (GA D V)), Hecke₂ V (levS V β (withP L P)) (levChi V β (withP L P)) SF Q d Rp ↔ Hecke₂ V (levS V β (withP L P')) (levChi V β (withP L P')) SF Q d Rp := by
  first | exact @GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff | exact GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff | (intros; apply GlobalTheory.HeckeLevelFree.isHeckeOpFull_withP_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open Formalism.IndefR.Lev
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
open GlobalTheory.Hk3 (Core IsSF SchurAll EEc Wcc)

namespace GlobalTheory.TrLevMult

theorem level_eq_trivial {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {LL : Type} [CommRing LL]
    (L : LevelP Pg r LL) (h : L.H = ⊥) : L = LevelP.triv Pg r LL := by
  obtain ⟨H, chi⟩ := L
  simp only at h
  subst h
  unfold LevelP.triv
  congr 1
  ext x
  have hx : x = 1 := Subtype.ext (Subgroup.mem_bot.mp x.2)
  subst hx
  simp

theorem levPOf_bot_eq {D : D7} {G K : Type} [Group G] [Field K] {Pg : Finset (Pl D.host.E)} {r : ℕ} (eG : G ≃* G0 Pg r)
    (σ : K →+* ℂ) (ψ : (⊥ : Subgroup G) →* Kˣ) : levPOf eG σ ⊥ ψ = LevelP.triv Pg r ℂ := by
  apply level_eq_trivial
  show Subgroup.comap eG.symm.toMonoidHom ⊥ = ⊥
  ext x
  simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem pg_over {SF : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSF : IsSF R SF) : ∀ PP ∈ R.Pg, ∃ v ∈ SF,
    PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal :=
  fun PP hPP => ⟨Formalism.IndefR.Fin.belowPl PP, (hSF _).2 ⟨PP, hPP, rfl⟩, rfl⟩

theorem trAt_of_dim (hC : Core R F) {SF} (hSF : IsSF R SF) (i : Fin D.R.m) (Pe Pw : LevelP R.Pg D.R.r ℂ)
    (hdim : ∀ c, Module.finrank ℂ (Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e : Submodule ℂ _) =
      Module.finrank ℂ (EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e : Submodule ℂ _)) :
    GlobalTheory.TrCopy.TRAt R SF i Pe Pw := by
  intro c
  have hE : R.EEat Pe ≤ R.EEat R.triv := GlobalTheory.PartDims.goodPart_le_flag (L := R.dat0 R.triv) R.θ _ rfl rfl _ _
  have hW : R.Wat i (sg0 D A) Pw ≤ R.Wat i (sg0 D A) R.triv :=
    GlobalTheory.PartDims.goodPart_le_flag (L := R.datWp i R.triv) R.θ _ rfl rfl _ _
  have kE : ∀ Q d B, Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF Q d B ↔
      Hecke₂ (Yc D 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Yc D 0) (R.βY 0) (R.dat0 R.triv) Pe R.triv SF (pg_over hSF)
  have kW : ∀ Q d B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF Q d B ↔
      Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF Q d B :=
    GlobalTheory.T.isHeckeOpFull_iff_independent_of_blockLevel D (Wc D i) (R.βW i) (R.datWp i R.triv) Pw R.triv SF (pg_over hSF)
  have eqE : GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c =
      R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF
        (fun Q d => c Q (dualLab d)) := by
    ext x
    show (x ∈ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) SF
        (fun Q d => c Q (dualLab d)) ∧ x ∈ R.EEat Pe) ↔ (x ∈ R.EEat Pe ∧ x ∈ partFull R.θ (R.MY 0)
        (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d)))
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hE h2).1, fun Q d B hB => h1 Q d B ((kE Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kE Q d B).1 hB)⟩, h2⟩
  have eqW : GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c =
      R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
        (levChi _ (R.βW i) (R.datWp i R.triv)) SF c := by
    ext x
    show (x ∈ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw)) SF c ∧
        x ∈ R.Wat i (sg0 D A) Pw) ↔ (x ∈ R.Wat i (sg0 D A) Pw ∧ x ∈ partFull R.θ (R.MW i (sg0 D A))
        (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    simp only [partFull, Submodule.mem_inf, Submodule.mem_iInf]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h2, (hW h2).1, fun Q d B hB => h1 Q d B ((kW Q d B).2 hB)⟩
    · rintro ⟨h2, -, h1⟩
      exact ⟨⟨h2.1, fun Q d B hB => h1 Q d B ((kW Q d B).1 hB)⟩, h2⟩
  have fE := GlobalTheory.PartDims.finrank_comap hC.models.HE (U := R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
    (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))) (inf_le_left.trans hE)
  have fW := GlobalTheory.PartDims.finrank_comap (hC.models.HW i (sg0 D A)) (U := R.Wat i (sg0 D A) Pw ⊓
    partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) SF c)
    (inf_le_left.trans (hW.trans inf_le_left))
  have cE : (R.EEat Pe ⊓ partFull R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv))
      (levChi _ (R.βY 0) (R.dat0 R.triv)) SF (fun Q d => c Q (dualLab d))).comap R.HE.e =
      EEc R SF c ⊓ (R.EEat Pe).comap R.HE.e := by
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  have cW : (R.Wat i (sg0 D A) Pw ⊓ partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) SF c).comap (R.HW i _).e =
      Wcc R SF i c ⊓ (R.Wat i (sg0 D A) Pw).comap (R.HW i _).e := by
    ext x
    exact ⟨fun hx => ⟨⟨hW hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
  haveI := fE.2
  haveI := fW.2
  show Module.rank ℂ (GlobalTheory.TrCopy.partE R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 Pe)) (levChi _ (R.βY 0) (R.dat0 Pe)) R.e0 SF c) =
    Module.rank ℂ (GlobalTheory.TrCopy.partW R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i Pw)) (levChi _ (R.βW i) (R.datWp i Pw))
        (R.eWf i (sg0 D A)) SF c)
  rw [eqE, eqW, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← fE.1, ← fW.1, cE, cW, hdim c]

end GlobalTheory.TrLevMult


open GlobalTheory.TrLevMult in
theorem GlobalTheory.TrLevMult.trLev_of_multEq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s hs hC hS hX hD hM SF hSF
  have key : ∀ i (P : Subgroup G) (ψ : P →* D.what₂.LLˣ),
      GlobalTheory.TrCopy.TRAt R SF i (levPOf R.eG D.what₂.embLL P ψ) (levPOf R.eG (sg0 D A) P ψ⁻¹) :=
    fun i P ψ => trAt_of_dim hC hSF i _ _ (fun c => GlobalTheory.DimFull.dim_parts_full R F hs hC hS hX hD hM SF hSF P ψ i c)
  intro i
  refine ⟨?_, fun b => key i _ _⟩
  have h := key i ⊥ 1
  rwa [inv_one, levPOf_bot_eq, levPOf_bot_eq] at h

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ s : ℕ, A.fam.Ok s → GlobalTheory.Hk3.Core R F → GlobalTheory.Hk3.SchurAll R → GoodStable A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R → ∀ SF, GlobalTheory.Hk3.IsSF R SF → GlobalTheory.TrCopy.TRLev R F SF := by
  first | exact @GlobalTheory.TrLevMult.trLev_of_multEq | exact GlobalTheory.TrLevMult.trLev_of_multEq | (intros; apply GlobalTheory.TrLevMult.trLev_of_multEq <;> assumption)
end
end
