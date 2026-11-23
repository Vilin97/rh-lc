module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ColNorm
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDeterminantEqNormOneClassOfLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepCharts
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompanionLatticeTrueColumnBaseLatticeEqStandardStatement
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsRowFrame
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceUnderTwistPrimeOverTupleRamifiedPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoiceGoodChartsEveryStageStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnKernelDataCompatibleStepChartsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi (β : Ch i hi), LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf i hi c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt), I.IsTw → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → ex.errX.piT = X.piT → I.StdDt l Z dt → (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) → (∀ i hi, I.ReadsK l Z u a i hi (chOf i hi) (Kc i hi) ∧ I.IdY l Z u a i hi (eY i hi)) → (∀ i hi β, FunKilled (Kc i hi β).lev (X.piT u)) → (∀ i hi β, ∃ n : ℕ, 0 < n ∧ ∀ κ : (Kc i hi β).lev.U, (∀ v ∈ badG (I.rec7 l Z), bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (Kc i hi β).lev.chi κ ^ n = 1) → (a ≠ I.mu0 → ∀ i hi c (y : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm), Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det ((Kc i hi (chOf i hi c)).y ⟨c, rfl⟩).1 → detPt B.host I.SQ ((I.stp u a i).rep c).1.1 = dt y) → ∃ A : GlobalTheory.TwU.AdData t u a (fun i hi => ⟨B.T u, bad, eY i hi, Ch i hi, chOf i hi, fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c), Kc i hi⟩), GlobalTheory.TwU.AdPins A dt ∧ GlobalTheory.TwU.AdTie A dt (B.fields.conjO (X.piT u)) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.adTie_true | exact GlobalTheory.Mem.Col2.AdT.adTie_true | (intros; apply GlobalTheory.Mem.Col2.AdT.adTie_true <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HServTwoSidesJoint0

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelCoefficientFieldLeCoefficientField

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem kerField_le_rec :
    ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  intro B X I _ _ l Z L hT Gi Gl K Y cX ex t hS y
  obtain ⟨hX, hseam⟩ := And.intro hS.X_eq hS.seam
  clear hS
  cases t
  dsimp only at hX hseam y ⊢
  subst hX
  have h := eq_of_heq hseam
  subst h
  exact ⟨y, rfl⟩

end GlobalTheory.TwU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelCoefficientFieldLeCoefficientFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelCoefficientField_le_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∀ y : t.X.K, ∃ k : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL k = t.seam.σ₀ y := by
  first | exact @GlobalTheory.TwU.kerField_le_rec | exact GlobalTheory.TwU.kerField_le_rec | (intros; apply GlobalTheory.TwU.kerField_le_rec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnOrthonormalCoordsEqGiven

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem crd_eq_one : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY Kc)), I.StdKer l Z t → (∀ i hi, I.IdY l Z u a i hi (eY i hi)) → AdPins A dt → ∀ i hi, A.crd i hi = 1 := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t u a bad Ch chOf eY Kc dt A hK hY hA i hi
  obtain ⟨τ⟩ : Nonempty (I.rec7 l Z).what₂.Tau := ⟨(I.rec7 l Z).eTau.symm 1⟩
  let f : Formalism.L2.Forms.Fr (I.rec7 l Z) i hi := ⟨fun _ => 1, fun _ => by simp⟩
  set y := (eY i hi).symm f with hy
  have hYy : (eY i hi y).1 = y.1 := hY i hi y
  have hf : (eY i hi y) = f := by rw [hy, Equiv.apply_symm_apply]
  have h1 := hA.frm i hi y τ
  have h2 := hK.O.frm u a i y
  have hc : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (A.crd i hi).1 τ = 1 := by
    have e1 : ((charts I l Z u a bad Ch chOf eY Kc i hi).eY y).1 τ = 1 := by
      show ((eY i hi y).1) τ = 1
      rw [hf]
    rw [e1, mul_one, h2, ← hYy, hf] at h1
    exact h1.symm
  apply Units.ext
  refine Matrix.ext fun p q => ?_
  have := congrFun (congrFun hc p) q
  simp only [Formalism.L2.Forms.atInf, Matrix.map_apply] at this
  rw [Units.val_one]
  apply (Formalism.L2.Forms.embT (I.rec7 l Z) τ).injective
  rw [this]
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.TwU.AtTrue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnOrthonormalCoordsEqGivenStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumn_orthonormalCoords_eq_given : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (u : B.Word) (a : I.ι) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : ∀ i, i ≤ B.R.m → Type) (chOf : ∀ i hi, (I.stp u a i).Cl → Ch i hi) (eY : ∀ i (hi : i ≤ B.R.m), (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (Kc : ∀ i hi, Fam I l Z u a i hi bad (chOf i hi)) (dt : Formalism.L2.Herm.unitaryOneFiniteAdeles (I.rec7 l Z).sp.cm →* (I.rec7 l Z).Dt) (A : AdData t u a (charts I l Z u a bad Ch chOf eY Kc)), I.StdKer l Z t → (∀ i hi, I.IdY l Z u a i hi (eY i hi)) → AdPins A dt → ∀ i hi, A.crd i hi = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.crd_eq_one | exact GlobalTheory.TwU.AtTrue.crd_eq_one | (intros; apply GlobalTheory.TwU.AtTrue.crd_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRational

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem tuple_kernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z →
    ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  intro B X I h _ l Z l0 Tw hJ hTw u a j hj
  subst hTw
  exact ((KerRat.kernels_rational I l Z h hJ
    (Or.inr (GlobalTheory.Core.Ht2.family_laws I h (base_fields_primes_ok B X).1 l Z))).2.2 l0 u a).1 j hj

end GlobalTheory.TwU.AtTrue
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRationalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumnTupleKernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z → ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  first | exact @GlobalTheory.TwU.AtTrue.tuple_kernels_rational | exact GlobalTheory.TwU.AtTrue.tuple_kernels_rational | (intros; apply GlobalTheory.TwU.AtTrue.tuple_kernels_rational <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataForms

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.Port.jIn_nonempty_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  intro B X I hI hP l Z l0 L hT Gi Gl K Y cX ex t C full g hTw hJets hex hpi hSK hRd hpin hSC hDt hherm hforms hchiD u a
  classical
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := by
    intro v
    exact Finset.mem_image
  obtain ⟨Ch, chOf, eY, Kc, hK, hCh0, hlev0, hy0⟩ := GlobalTheory.T.trueColumnChoice_goodCharts_every_stage I hI hP l Z u (C.forms u) a Q hQ (hSC u)
  have hbad : ∀ v ∈ badQ (I.rec7 l Z) Q, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v := by
    intro v hv
    rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr ((hQ v).1 hv)
  obtain ⟨A, hpins, htie⟩ := GlobalTheory.T.trueColumn_kernelData_compatible_stepCharts I hI hP l Z L hT Gi Gl K Y cX ex t u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
    full.1.base.dt hTw hSK hRd hpin hpi hDt hbad
    (fun i hi => ⟨(hK i hi).2.2.1.readsK, (hK i hi).2.1⟩) (fun i hi β => ((hK i hi).2.2.2 β).1)
    (fun i hi β => by
      obtain ⟨n, hn, h⟩ := ((hK i hi).2.2.2 β).2
      exact ⟨n, hn, fun κ _ => h κ⟩) (fun _ i hi c y hy => by
    obtain ⟨k, hR, hk1⟩ := (hK i hi).2.2.1
    obtain ⟨p, hp, hN⟩ := hR.k_std (chOf i hi c)
    have e := GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level B.R B.host _ _ _ _ I.SQ _ _ (k (chOf i hi c)) y
      (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).1 (hR.pt c) hp.uni (hN ▸ hp.lat)
      (fun P hP => hk1 _ _ (GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P hP)) hy
    obtain ⟨b, hb⟩ := GlobalTheory.Mem.Col2.FullDt.exists_lift B.host y
    rw [e, GlobalTheory.Mem.Col2.FullDt.normOneFiniteAdeleDetClass_of_isDetLift B.host I.SQ y b hb, hDt y b hb])
  have hf : g.forms u = (C.forms u).to0 := congrFun hforms u
  refine ⟨{
      Gd := g
      Hh := full.1.base
      rel := full.1.relDet
      St := charts I l Z u a (badQ (I.rec7 l Z) Q) Ch chOf eY Kc
      A := A
      a := B.fields.conjO (X.piT u)
      pins := hpins
      tie := htie
      val := ?val
      fin := fun i hi => (hK i hi).1
      ord := fun i hi β => ((hK i hi).2.2.2 β).2
      base := ?base
      joint0 := GlobalTheory.hServTwoSidesJoint0 hT ex.cmp g C full hherm hforms u
      e0 := I.eCls0 l u a
      jointCmpEmbeddingY := Equiv.refl _
      e0Tw := ?e0Tw
      lev0 := ?lev0
      ch0 := hCh0
      y0 := ?y0
      fr0 := ?fr0
      rat := fun j hj => GlobalTheory.T.trueColumnTupleKernels_rational I hI hP l Z l0 ex.tw hJets hex u a j hj
      kin := GlobalTheory.T.kernelCoefficientField_le_coefficientField I hI hP l Z L hT Gi Gl K Y cX ex t hSK
      chiD := hchiD }⟩
  case val =>
    intro i hi
    rw [hex]
    exact GlobalTheory.Mem.Col2.TC.val_tied I hI hP l Z u a i hi _ (Ch i hi) (chOf i hi) (Kc i hi) (eY i hi)
      (hK i hi).2.2.1.readsK (hK i hi).2.1
  case base =>
    intro i hi β
    obtain ⟨k, hR, _⟩ := (hK i hi).2.2.1
    rw [GlobalTheory.T.trueColumn_orthonormalCoords_eq_given I hI hP l Z L hT Gi Gl K Y cX ex t u a _ Ch chOf eY Kc full.1.base.dt A hSK (fun i hi => (hK i hi).2.1) hpins i hi]
    exact GlobalTheory.T.companionLattice_trueColumn_baseLattice_eq_standard I hI hP l Z u i hi _ (fun x => hR.lb β x)
  case e0Tw =>
    intro φ c y
    change φ ((I.eCls0 l u a).symm (I.eCls0 l u a c)) y = φ c y
    exact congrFun (congrArg φ ((I.eCls0 l u a).symm_apply_apply c)) y
  case lev0 =>
    rw [hf]
    exact hlev0
  case y0 =>
    rw [hf]
    intro c
    obtain ⟨κ, h1, h2, h3⟩ := hy0 c
    refine ⟨κ, h1, h2, fun v hv => h3 v fun hvQ => ?_⟩
    obtain ⟨q, hq, hqv⟩ := GlobalTheory.T.placeUnderTwistPrime_over_tupleRamifiedPrime I hI hP l Z L hT Gi Gl K Y cX ex t hSK a v ((hQ v).1 hvQ)
    exact hv q hq hqv
  case fr0 =>
    rw [hf]
    intro y
    apply Subtype.ext
    exact ((hK 0 (Nat.zero_le _)).2.1 y).trans ((hSC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y).symm
end
end
