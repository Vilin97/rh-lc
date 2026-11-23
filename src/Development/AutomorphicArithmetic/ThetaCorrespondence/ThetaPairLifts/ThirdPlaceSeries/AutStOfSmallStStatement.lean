module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CofiniteLabelsAtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.QuotientMetricDivisors.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.PieriBlockIdeals.LatticeInclusionRealSettingAlt
import Formalism.PieriBlockIdeals.MertensReciprocalElementary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormSqBlockValueStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallPlacePrimeLocal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitaryStatement

section

@[expose] public section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  first | exact @GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | exact GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | (intros; apply GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceBlockDecomposition

section

@[expose] public section

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLab

variable {D : D7}

theorem cO_cO (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E (Formalism.DivisionValues.cO D.host.E x) = x :=
  RingOfIntegers.ext (star_star (x : D.host.E))

theorem mem_conjPl_of_fixed (P : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : Formalism.DivisionValues.cO D.host.E x = x) :
    x ∈ (Formalism.DivisionValues.conjPl P).asIdeal ↔ x ∈ P.asIdeal := by
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, e⟩
    have : y = x := by rw [← cO_cO y, e, hx]
    rwa [← this]
  · exact fun h => ⟨x, h, hx⟩

theorem under_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl P).under (𝓞 (maximalRealSubfield D.host.E)) = P.under (𝓞 (maximalRealSubfield D.host.E)) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  exact mem_conjPl_of_fixed P (x := algebraMap _ (𝓞 D.host.E) x)
    (RingOfIntegers.ext (IsCMField.complexConj_apply_eq_self D.host.E (x : maximalRealSubfield D.host.E)))

theorem absNorm_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal _ (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

end GlobalTheory.FrameLab
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelsOk

section

@[expose] public section



section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameLab
variable {D : D7}
theorem labels_ok_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W _ _ w _ _ _ Q
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
    p.charW.base.lev).2.2.2 p.charW.base.fam (p.R.mu w) Q.1 Q.2
  refine ⟨⟨plOf p j (p.R.mu w) Q, fun e => h2 e.symm, (under_conjPl _).symm⟩, under_conjPl _,
    (absNorm_conjPl _).trans h3.symm, mem_conjPl_of_fixed _ (map_natCast _ _)⟩
end GlobalTheory.FrameLab
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelsOkStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.small_place_block_decomposition_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal) := by
  first | exact @_root_.GlobalTheory.FrameLab.labels_ok_alt | exact _root_.GlobalTheory.FrameLab.labels_ok_alt | (intros; apply _root_.GlobalTheory.FrameLab.labels_ok_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOf

section

@[expose] public section



section
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FrameAut
theorem autAt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w → AutAt p j P W w := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hr hm j P W hd hn w hw hwr hs
  refine ⟨⟨hLab p hr hm j P W hd hn w hw hwr hs, hCof p hr hm j P W hd hn w hw hwr hs, hBl p hr hm j P W hd hn w hw hwr hs⟩, ?_⟩
  intro _ F R inc T mu θ hmu hE
  obtain ⟨π, hπ, hwt, hl, φ, hφ, hφ0, hQ⟩ := hAut p hr hm j P W hd hn w hw hwr hs F R inc T mu θ hmu hE
  refine ⟨π, hπ, hwt, hl, fun Q => ?_⟩
  have hlab := hLab p hr hm j P W hd hn w hw hwr hs Q
  by_cases hQl : ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal
  · have hun := hl _ (hlab.2.2.2.2 hQl)
    obtain ⟨ψ, hψ, hψ0, hψfix⟩ := hun
    obtain ⟨σ, S, hc, hsat, -⟩ := hSat _ _ π hπ _ hlab.1 ψ hψ hψ0 hψfix
    refine ⟨⟨ψ, hψ, hψ0, hψfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    exact absurd (hi ▸ hQl) ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.2
  · obtain ⟨hfix, heig⟩ := hQ Q hQl
    obtain ⟨σ, S, hc, hsat, hk⟩ := hSat _ _ π hπ _ hlab.1 φ hφ hφ0 hfix
    refine ⟨⟨φ, hφ, hφ0, hfix⟩, σ, S, hc, hsat, fun i hi => ?_⟩
    have hle := ((T.ix_range (R.ix i)).1 ⟨i, rfl⟩).2.1
    exact smul_left_injective ℂ hφ0 ((heig i hi).symm.trans (hk _ hle))
theorem autSt_of_alt (hLab : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ Q : (blk p j (p.R.mu w)).Pl, IsSplitAt (labOf p j (p.R.mu w) Q) ∧
      (labOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j (p.R.mu w) Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
      Ideal.absNorm (labOf p j (p.R.mu w) Q).asIdeal = (blk p j (p.R.mu w)).q Q ∧
      (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (labOf p j (p.R.mu w) Q).asIdeal ↔ ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ (plOf p j (p.R.mu w) Q).asIdeal)) (hCof : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
      ¬ ∃ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal ∧ labOf p j (p.R.mu w) Q = v}.Finite) (hBl : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ ν ∈ (blk p j (p.R.mu w)).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j (p.R.mu w)).q Q : ℝ) ^ ((blk p j (p.R.mu w)).n - (blk p j (p.R.mu w)).t)) (hSat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ) (hAut : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), _root_.GlobalTheory.BigTop.PtAt.PointConditions' p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr) →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) (n := P.Nr)).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ) :
    _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  intro hS
  obtain ⟨ε1, he, H⟩ := hS
  refine ⟨ε1, he, fun eps h1 h2 => ?_⟩
  obtain ⟨K, hK⟩ := H eps h1 h2
  refine ⟨K, fun Fm CH hc hl => ?_⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hl
  exact ⟨x0, fun x hx hxx i p hr hm j P W hd hn w hw hwr =>
    _root_.GlobalTheory.FrameAut.autAt_of_alt hLab hCof hBl hSat hAut p hr hm j P W hd hn w hw hwr (hx0 x hx hxx i p hr hm j P W hd hn w hw hwr)⟩
theorem autSt_of_smallSt' : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.FrameAut.autSt_of_alt _root_.GlobalTheory.T.small_place_block_decomposition_alt _root_.GlobalTheory.T.small_place_finite_set_alt _root_.GlobalTheory.T.norm_sq_emb_block_eq_q_pow_of_small_at GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary _root_.GlobalTheory.T.small_place_prime_local_alt
end GlobalTheory.FrameAut
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutAtOfStatement

section

@[expose] public section



section

theorem _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  first | exact @_root_.GlobalTheory.FrameAut.autSt_of_smallSt' | exact _root_.GlobalTheory.FrameAut.autSt_of_smallSt' | (intros; apply _root_.GlobalTheory.FrameAut.autSt_of_smallSt' <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutStOfSmallSt

section

@[expose] public section



section
theorem GlobalTheory.FrameAut.frame_autSt_of_smallSt : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt :=
  _root_.GlobalTheory.T.aut_statement_of_small_exponent_statement
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutStOfSmallStStatement

section

@[expose] public section



section

theorem _root_.GlobalTheory.T.frame_aut_of_small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition → _root_.GlobalTheory.FrameAut.AutStAlt := by
  first | exact @_root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt | exact _root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt | (intros; apply _root_.GlobalTheory.FrameAut.frame_autSt_of_smallSt <;> assumption)
end
end
end
