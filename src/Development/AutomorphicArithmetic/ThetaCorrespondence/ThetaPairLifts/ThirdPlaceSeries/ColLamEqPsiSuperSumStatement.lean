module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLamReadStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfRead

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterCongruenceInvariance

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.FamTraceChiColSide

theorem psi_unif_mul_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : GlobalTheory.SymChain.SymData k s κ) (d e : k) (hv : valuation k (d - e) < 1) :
    (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * e) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * d) : ℂ) := by
  have hsplit : ((S.ϖ⁻¹ : kˣ) : k) * d = ((S.ϖ⁻¹ : kˣ) : k) * e + ((S.ϖ⁻¹ : kˣ) : k) * (d - e) := by ring
  have h1 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (d - e)) = 1 := by
    refine (S.cond 1).2 le_rfl _ ?_
    have hle := (S.unif _).1 hv
    have hϖ : valuation k ((S.ϖ : kˣ) : k) ≠ 0 := by simp
    rw [map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    calc (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k (d - e)
        ≤ (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k ((S.ϖ : kˣ) : k) := by gcongr
      _ = 1 := inv_mul_cancel₀ hϖ
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one]

end GlobalTheory.FamTraceChiColSide

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryPsiValue

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.FamTraceChiColChar

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil

theorem chr_unif_congr {k : Type} [Field k] [ValuativeRel k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {t : kˣ} (ht : IsUnif t)
    {p y : k} (hp : valuation k ((t : k) - p) < valuation k (t : k)) (hy : valuation k y ≤ 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (p⁻¹ * y) := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have hpv : valuation k p = valuation k (t : k) := by
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [Valuation.map_sub_swap]
  have p0 : p ≠ 0 := fun e => by
    rw [e, map_zero] at hpv
    exact tp.ne hpv
  have h1 : valuation k (((t : k) - p) * (t : k)⁻¹) ≤ valuation k (t : k) := (ht _).1 (by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ tp, one_mul]
    exact hp)
  have triv : ψ (((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_one, map_mul, map_mul _ _ p⁻¹, map_inv₀, hpv]
    refine mul_le_one' ?_ hy
    rw [mul_inv_le_iff₀ tp, one_mul]
    exact h1)
  have e : p⁻¹ * y = ((t⁻¹ : kˣ) : k) * y + ((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y := by
    have := t.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [e, AddChar.map_add_eq_mul, triv, mul_one]

theorem weil_unif_eq_exp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {ψ : AddChar k Circle}
    (hψ : HasConductor ψ 1) {Ψ : AddChar (AF D.host.F) ℂ} (hΨ : IsStdChar D Ψ (-1)) (hc : (ofSplit q).IsChar Ψ ψ)
    {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm PP.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2)
    {t : kˣ} (ht : IsUnif t) (htp : valuation k ((t : k) - (p : k)) < valuation k (t : k))
    {s : 𝓞 D.host.E} (hs : D.host.xi0 * (s : D.host.E) = 1) {z : 𝓞 D.host.E} {b : ℤ} (hz : z - s * b ∈ PP.asIdeal) :
    (ψ (((t⁻¹ : kˣ) : k) * (ofSplit q).pr (z : D.host.E)) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  obtain ⟨hv, hi, -⟩ := place_facts q h
  have h1 : valuation k (prO q z - prO q (s * b)) < 1 := by
    rw [← map_sub, ← prO_lt q h]
    exact hz
  rw [← prO_apply, GlobalTheory.LevelUnif.chr_near hψ ht h1, chr_unif_congr hψ ht htp (prO_le q h _), hc,
    ← GlobalTheory.SplitDegOneChar.psiE_sec_pr_eq_exp D k q PP p hp hN hsq hv hi Ψ hΨ ((b : D.host.E) / (p : D.host.E)) b
      (by rw [sub_self]; exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)]
  have e1 : ((p : k))⁻¹ * prO q (s * b) = q.pr (incA D ((s : D.host.E) * ((b : D.host.E) / (p : D.host.E)))) := by
    change _ = (q.pr.comp (incA D)) _
    rw [map_mul, map_mul, map_div₀, map_intCast, map_intCast, map_natCast]
    change _ = prO q s * _
    ring
  rw [e1]
  change psiE Ψ (incA D D.host.xi0 * q.sec (q.pr _)) = psiE Ψ (q.sec (q.pr (incA D _)))
  rw [q.sec_pr, q.sec_pr, mul_left_comm, ← map_mul, ← mul_assoc D.host.xi0, hs, one_mul]

theorem columnCharacter_reduction_eq_exp {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok)
    (G : Formalism.L2.Forms.GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hpsi : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : Formalism.L2.Forms.kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal)))
    (P : HeightOneSpectrum (𝓞 B.host.E)) (hPP : P ∈ (B.primes X).vGs) (j : Fin 2)
    (h : (B.host.g j : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal) (z : 𝓞 B.host.E)
    (w : (P.under (𝓞 B.host.F)).adicCompletionIntegers B.host.F)
    (hw : (w : (P.under (𝓞 B.host.F)).adicCompletion B.host.F) =
      G.phi j _ h ((z : B.host.E) ⊗ₜ[B.host.F] (1 : (P.under (𝓞 B.host.F)).adicCompletion B.host.F)))
    {s : 𝓞 B.host.E} (hs : B.host.xi0 * (s : B.host.E) = 1) (hsP : s ∉ P.asIdeal) :
    (Formalism.L2.Col.qOf P).Prime ∧ ∃ b : ℤ, z - s * b ∈ P.asIdeal ∧ G.psi0 j _ h (IsLocalRing.residue _ w) =
      Complex.exp (2 * Real.pi * Complex.I * b / ((Formalism.L2.Col.qOf P : ℕ) : ℂ)) := by
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨P', hP, ρ, hPu, hres⟩ := TC.GLev0.exists_w (X := X) G hG j _ h
  have hwP : P' = P := TC.GLev0.vGs_inj (X := X) hPP (TC.GLev0.mem_vGs.2 ⟨j, hP⟩) hPu
  subst hwP
  have hq : Formalism.L2.Col.qOf P' = B.host.g j := hPr.vG_norm j _ hP
  refine ⟨by rw [hq]; exact hPr.g_prime j, ?_⟩
  obtain ⟨n, hn⟩ := TC.GLev0.exists_natCast (X := X) hPP (Ideal.Quotient.mk _ z)
  obtain ⟨b, hb⟩ := TC.GLev0.exists_natCast (X := X) hPP (Formalism.L2.Col.redP P' B.host.xi0 * n)
  have hred := Formalism.L2.Col.reduction_spec P' (a := B.host.xi0) (r := 1) hsP (by rw [map_one, mul_comm]; exact hs)
  refine ⟨b, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_mul, Int.cast_natCast, map_natCast, hb, ← mul_assoc, hred, map_one, one_mul, hn]
  obtain ⟨hh, e⟩ := hres (Formalism.UG.inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (z : B.host.E)) (Ideal.Quotient.mk _ z)
    (by rw [adAt_inclE]; exact hasRes_coe _ z)
  have ew : w = ⟨_, hh⟩ := Subtype.ext hw
  have e2 : IsLocalRing.residue _ w = (n : Formalism.L2.Forms.kv B.host.F _) := by
    rw [ew]
    exact e.trans ((congrArg ρ hn.symm).trans (map_natCast ρ n))
  have e3 := hpsi j _ h ⟨_, hPP⟩ rfl n
  have e4 := hI.weil ⟨_, hPP⟩ (n : _) (b : ℤ) ((hb.symm).trans (Int.cast_natCast b).symm)
  rw [e2]
  exact e3.trans e4

end GlobalTheory.FamTraceChiColChar

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PsiUniformizerEqPsiZero

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChiColChar
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil
theorem psi_uniformizer_eq_psi_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ i j h z w hw
  obtain ⟨hS⟩ := hA.tr.std
  have hR := (ha.tie row col).2
  have hPP : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hid := (hR.idem i).1
  have hsq := GlobalTheory.LevelUnif.norm_notMem_sq (D := I.rec7 l Z) (hA.lev.1.1 _ (a.pl i).2)
  have hu := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hA.lev.1 i
  obtain ⟨s, hs⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer (I.rec7 l Z).host
  have hsP : s ∉ (a.pl i).1.asIdeal := fun hm => by
    have h1 := (prO_lt (a.G i).q hid s).1 hm
    have h2 := xi_unit (a.G i).q (a.G i).unit (GlobalTheory.LocMod.Witness.xi_ne _)
    have h3 : (ofSplit (a.G i).q).xi * prO (a.G i).q s = 1 :=
      (((a.G i).q.pr.comp (incA (I.rec7 l Z))).map_mul _ _).symm.trans
        ((congrArg ((a.G i).q.pr.comp (incA (I.rec7 l Z))) hs).trans (map_one _))
    have h4 := congrArg (valuation (a.G i).k) h3
    rw [map_mul, h2, one_mul, map_one] at h4
    exact h1.ne h4
  obtain ⟨hp, b, hz, e⟩ := columnCharacter_reduction_eq_exp I hA.tr.ok (_root_.GlobalTheory.MiTop.formsAtZero W u).gl (hS u).gl.piG (hS u).gl.psi (a.pl i).1 hPP j h z w hw hs hsP
  exact (weil_unif_eq_exp (a.G i).q hid (a.G i).S.cond W.Q.stdChar (a.G i).char hp rfl hsq (a.G i).S.unif hu
    hs hz).trans e.symm
end GlobalTheory.FamTraceChiColChar
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PsiUniformizerEqPsiZeroStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.true_geometry_psi_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  first | exact @_root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt | exact _root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt | (intros; apply _root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLamEqPsiSuperSum

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChiColSide
theorem colLam_eq_psi_superSum_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) = ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * ∑ p : Fin (I.rec7 l Z).R.k, ∑ q : Fin (I.rec7 l Z).R.k, if q.val = p.val + 1 then g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q)) else 0) : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat row col hc κ hκ y hy hyU i g hg
  obtain ⟨j, h, z, w, hw, hv, hcol⟩ := _root_.GlobalTheory.T.true_geometry_final_twist_alt W hW u a ha hat row col hc κ hκ y hy hyU i g hg
  rw [hcol, ← _root_.GlobalTheory.T.true_geometry_psi_value_alt W hW u a ha hat row col hc i j h z w hw]
  exact psi_unif_mul_congr _ _ _ hv
end GlobalTheory.FamTraceChiColSide
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColLamEqPsiSuperSumStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.true_geometry_final_volume_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → ∀ (i : Fin a.n) g, GlobalTheory.FamTrace.IsMatrixInFrameOfXZero (a.G i) κ g → GlobalTheory.FamTraceChiCol.colLam (_root_.GlobalTheory.MiTop.formsAtZero W u) ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)) (y : GL _ _) = ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * ∑ p : Fin (I.rec7 l Z).R.k, ∑ q : Fin (I.rec7 l Z).R.k, if q.val = p.val + 1 then g.val (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl q)) else 0) : ℂ) := by
  first | exact @_root_.GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum_alt | exact _root_.GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum_alt | (intros; apply _root_.GlobalTheory.FamTraceChiColSide.colLam_eq_psi_superSum_alt <;> assumption)
end
end
end
