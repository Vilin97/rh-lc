module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsTiedS
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FinAfLocalIdele
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.RatioJoints.IsRatioAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowerMapTieTw

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Top.Bl.WitSK

def of_sigma_eq {α : Type*} {β : α → Type*} {a b : Σ x, β x} (h : a = b) (P : ∀ x, β x → Sort*) (hb : P b.1 b.2) :
    P a.1 a.2 := by
  subst h; exact hb

end GlobalTheory.Mem.Top.Bl.WitSK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKOfStd

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.KerSK

theorem rowSG_heq {ι : Type} {X X' : Fields} (hX : X = X') {Pr : Primes X} {Pr' : Primes X'} (hPr : HEq Pr Pr')
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)}
    (hsel : HEq sel sel') {S S' : Set ℕ} (hS : S = S') {tup : ι → Tup X.F X.E X.K S} {tup' : ι → Tup X'.F X'.E X'.K S'}
    (htup : HEq tup tup') :
    HEq (fun μ => rowSG Pr sel (tup μ)) (fun μ => rowSG Pr' sel' (tup' μ)) := by
  subst hX; subst hS; cases hPr; cases hsel; cases htup; rfl

theorem sharp_heq {ι : Type} {X X' : Fields} (hX : X = X') {P : ι → Finset (HeightOneSpectrum (𝓞 X.E))}
    {P' : ι → Finset (HeightOneSpectrum (𝓞 X'.E))} (hP : HEq P P') {c : ∀ μ, LocCst X (P μ)} {c' : ∀ μ, LocCst X' (P' μ)}
    (h : HEq c c') (μ : ι) : (c μ).sharp = (c' μ).sharp := by
  subst hX; cases hP; cases h; rfl

theorem ch_cast {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} {C : ColsTiedSym D}
    {Tw Tw' : TwForms D} (h : Tw = Tw') (x : SymmetricTwistedColumnsAtPrimes tp C Tw) : (h ▸ x).ch = x.ch := by
  subst h; rfl

end GlobalTheory.Mem.Col2.TC.KerSK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDetLiftLocal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.JointsTrue

open Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR



theorem isDetLift_local (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Theta.AE D) (he : JoinChr.IsPlIdem D e P)
    (k : D.host.Eˣ) (y : Theta.AE D) (hy : Joints.IsRatioAt D e (k : D.host.E) y) (x : Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hx : ((Matrix.GeneralLinearGroup.det (x : GL (Fin 1) (D.host.E ⊗[D.host.F] Herm.Af D.host.F)) :
        (D.host.E ⊗[D.host.F] Herm.Af D.host.F)ˣ) : D.host.E ⊗[D.host.F] Herm.Af D.host.F) = Joints.finE D y) :
    IsDetLift D.sp.cm x.1 (Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k)) := by
  let φ : Theta.AE D →+* AfE D.host.F D.host.E := Joints.finE D
  have hinc : ∀ a : D.host.E, φ (Theta.incA D a) = a ⊗ₜ[D.host.F] 1 := fun a => rfl
  have hc : ∀ z, φ (Theta.cA D z) = Formalism.UG.sigR D.sp.cm.sig _ (φ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [(Theta.cA D).map_zero, φ.map_zero, RingHom.map_zero]
    | tmul a b => rfl
    | add a b ha hb => rw [(Theta.cA D).map_add, φ.map_add, φ.map_add, ha, hb, RingHom.map_add (f := _)]
  have h1 : (finAf D.host.F D.host.E (Neutral.B1.localIdele _ P (Formalism.L2.Host.atFin P k)) : AfE D.host.F D.host.E) = φ (JoinChr.locE D e k) := by
    rw [GlobalTheory.Core.Cls.JointsStd.finAf_localIdele (e := φ e) (by rw [← φ.map_mul, he.1]) (fun a ha => ?_) k, JoinChr.locE, φ.map_add,
      φ.map_mul, φ.map_sub, φ.map_one, hinc]
    rw [he.2.2 a ha, ← hinc, ← φ.map_mul]
    exact not_congr (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _)
  have h2 := congrArg φ hy
  rw [φ.map_mul, hc, ← h1] at h2
  unfold IsDetLift h90
  rw [MonoidHom.div_apply, div_eq_iff_eq_mul]
  exact Units.ext (h2.symm.trans (by rw [Units.val_mul, hx]; rfl))


end GlobalTheory.Mem.JointsTrue

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardAddChar_placeIdempotent_div_prime : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  first | exact @GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | exact GlobalTheory.StdCharDegOne.stdChar_placeIdem_div | (intros; apply GlobalTheory.StdCharDegOne.stdChar_placeIdem_div <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiGTrue

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (G : GLoc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g), TC.IdG I l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), Formalism.L2.Theta.IsPlaceIdem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) v ε → ∀ c y : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, Valued.v (algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) - G.phi k v h (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, (z : v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) = algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) * (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) / ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) :=
  by
    intro B X I hI _ l Z G hG ψ hψ k v h ε hε c y hc z hz
    have hs := (TC.rec7 I l Z).nd.g_split k
    have hgp := l.pr.g_prime k
    obtain ⟨hN, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram hgp hs v h
    obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer B.host
    obtain ⟨b, hb, e⟩ := GlobalTheory.Mem.TypePrimes.Red.columnCharacter_reduction_eq_exp
      (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
      (fun _ => rfl) hG.psi k v h hN c y hc z hz
    refine e.trans ?_
    exact (GlobalTheory.T.standardAddChar_placeIdempotent_div_prime (TC.rec7 I l Z) ψ hψ _
      hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)).symm
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointsSTrue

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.Mem.JointsTrue
open Formalism.L2 Formalism.L2.Host ReciprocityTheory.Neutral.Bridge.HCFR

theorem joints_of_standard_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (T : _root_.Formalism.L2.TiedDataSAlt ex), I.StdC l Z T.cols → I.StdDt l Z T.full.1.base.dt → T.n.cf = I.cf l Z → (∀ a, T.chrDt.eDt a = (QuotientGroup.mk a : DtQ B.host I.SQ)) → Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (I.rec7 l Z) T.n.cf ex.nch T.n.tp Y) → Formalism.L2.Theta.IsStdChar (I.rec7 l Z) T.theta.W.ψ (-1) → _root_.Formalism.L2.JointsSAlt T := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex T hC hD hcf he hdiv hψ
  refine ⟨fun P e hi k y hy x hx => ?_, fun k => ?_, fun k v h a n hn ha => ?_, fun k v h ε hε c y hc => ?_, hdiv⟩
  · exact (hD x _ (isDetLift_local (I.rec7 l Z) P e hi k y hy x hx)).trans (he _).symm
  · rw [hcf, show (T.cols.forms (I.rec7 l Z).u₀).gl.piG = X.piG from (hC _).gl.piG]
    exact GlobalTheory.Core.Cls.JointsStd.piBar_std I hOk k
  · rw [hcf]
    exact GlobalTheory.Core.Cls.JointsStd.om_std I hOk l Z _ (hC _).gl k v h a n hn ha
  · have hy : algebraMap (I.rec7 l Z).host.F (v.adicCompletion (I.rec7 l Z).host.F) (y : (I.rec7 l Z).host.F) ∈
        v.adicCompletionIntegers (I.rec7 l Z).host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]
      exact HeightOneSpectrum.valuation_le_one v y
    have e1 := GlobalTheory.Mem.TypePrimes.psiG_true I hOk hP l Z _ (hC (I.rec7 l Z).u₀).gl _ hψ k v h ε hε c y hc ⟨_, hy⟩ rfl
    unfold Joints.redV
    rw [dite_eq_left hy]
    exact e1
end GlobalTheory.Mem.JointsTrue
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedSKAtWitnesses

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE
namespace GlobalTheory.Mem.Top.Bl.WitSK
end GlobalTheory.Mem.Top.Bl.WitSK
open Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC Matrix in

theorem GlobalTheory.Mem.Top.Bl.exists_kernel_spectral_data_at_witnesses : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (K : Ctx) (q : WPt p.s K), ∀ (S : _root_.Formalism.L2.TiedDataSAlt q.O.ex) (t : Formalism.L2.Ker.KerEntTied q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.SpectralDataCompatible q S → KPin q t → ∃ T : _root_.Formalism.L2.TiedDataSKAlt q.O.ex, T.toTiedDataS = S ∧ T.ker = t ∧ (∀ u i hi, T.crd u i hi = 1) ∧ _root_.Formalism.L2.Rows.RowPinMinAlt T ∧ _root_.Formalism.L2.JointsSAlt S ∧ Nonempty (PLift (Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W)) := by
  intro hL p K q S t hS hKp
  obtain ⟨he, hTw⟩ := hS.tw
  have hK := hKp.std
  have hC : TC.StdC q.w.I q.w.l q.Z S.cols := hS.cols ▸ q.x.col.std
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hD : TC.StdDt q.w.I q.w.l q.Z S.full.1.base.dt := by
    have key : ∀ (C : ColsTiedSym (q.w.D q.Z)) (F : ColsFullS C), C = q.x.col.C → HEq F q.x.col.full →
        TC.StdDt q.w.I q.w.l q.Z F.1.base.dt := by
      intro C F hC' hF
      subst hC'
      cases hF
      exact q.x.col.stdDt
    exact key _ _ hS.cols hS.full
  have hcf : S.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst hS.chr
  have hdiv : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) S.n.cf q.O.ex.nch S.n.tp q.O.X) :=
    ⟨WitSK.of_sigma_eq hS.chr (fun c tp => Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) c q.O.ex.nch tp q.O.X) q.x.div.chr⟩
  have hψ : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) S.theta.W.ψ (-1) :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) A.W.ψ (-1)) q.x.th.std
  have hweq : Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.WeilCompatibleEquivariance A.W) q.x.th.weq
  refine ⟨{ S with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl,
    fun _ _ _ => rfl, ⟨fun u => ?_, fun u μ hμ _ h1 => ?_, q.x.what₂.r.Y.bu⟩,
    _root_.GlobalTheory.Mem.JointsTrue.joints_of_standard_character q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex S hC hD hcf hS.dt hdiv hψ, ⟨⟨hweq⟩⟩⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [GlobalTheory.Mem.Col2.TC.KerSK.sharp_heq hK.X_eq (GlobalTheory.Mem.Col2.TC.KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact q.w.ok.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (q.w.D q.Z)) (Units.val (1 : GL (Fin ((q.w.D q.Z).R.N i)) (q.w.D q.Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [GlobalTheory.Mem.Col2.TC.KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact _root_.GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw_alt q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex _ he hC hTw u μ hμ h1
end
end
end
