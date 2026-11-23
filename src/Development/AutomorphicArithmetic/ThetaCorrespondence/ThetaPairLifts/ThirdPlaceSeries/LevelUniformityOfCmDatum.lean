module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexTypePlaceCharacterEqSuperdiagAddCharMulLo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddCharCompletionOfResidueAddCharStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAddCharZmodEqOfNeOneStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorNotMemTwistPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterEqLocalFactorAtTypePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemLevelIffUnipotentAtTypePlaceStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfCmFieldPlaceEqStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlacesSameRealPlaceNatCastMemStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CardKPNeZero
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResidu

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.HeightCounting

theorem theta_xiRed_ne_one : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  classical
  intro D cf Rw low Pq S hL eig θ Bs hr i kv h1
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ', hθ', hψ⟩ := Bs.exp.psiU_gen i true
  have hu : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by
    rw [Bs.exp.U_eq]; exact Formalism.L2.NX.tvAt_mem hr _
  have hu' : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd :=
    Formalism.L2.NX.tvAt_mem hr _
  have e := Bs.psiU i true _ hu hu'
  have e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) :=
    psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv
  have e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1) :=
    (hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)
  rw [e2, h1, e3] at e
  refine Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))
  exact map_one (readLL0 S i true)

end GlobalTheory.HeightCounting
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResiduStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.rationalDatum_characters_ne_one_at_fixedElement_residues : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  first | exact @GlobalTheory.HeightCounting.theta_xiRed_ne_one | exact GlobalTheory.HeightCounting.theta_xiRed_ne_one | (intros; apply GlobalTheory.HeightCounting.theta_xiRed_ne_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrime

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TwistUnr

theorem nat_not_mem_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (Q : HeightOneSpectrum (𝓞 E)) (hq' : ((q : ℕ) : 𝓞 E) ∈ Q.asIdeal) : ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal := by
  intro hp'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply Q.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left a hp') (Q.asIdeal.mul_mem_left b hq')

theorem unrAt_xiTw : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  intro B f T v Q k hg hQ
  have hp : B.host.pde.Prime := B.toPre.level_prime _ B.host.pde_level.1
  have hp' : B.host.pde'.Prime := B.toPre.level_prime _ B.host.pde_level.2
  have h1 := nat_not_mem_of_ne hp (B.host.g_prime k) (B.host.pde_ne_g k).1 Q hg
  have h2 := nat_not_mem_of_ne hp' (B.host.g_prime k) (B.host.pde_ne_g k).2 Q hg
  have hψ : (T.psi v).UnrAt Q := ((T.psi_is v).ram Q).2 hQ
  unfold TwDat.xiTw
  split_ifs
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel'.unr Q h2) hψ
  · exact GlobalTheory.Plug.TwistLevels.unrAt_mul (f.isDel.unr Q h1) hψ

end GlobalTheory.TwistUnr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleFiniteOrderPartUnramifiedAtTypePrimeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (v : B.places.Pl) (Q : HeightOneSpectrum (𝓞 B.host.E)) (k : Fin 2),
    ((B.host.g k : ℕ) : 𝓞 B.host.E) ∈ Q.asIdeal → Q ∉ T.Q v → (T.xiTw f v).UnrAt Q := by
  first | exact @GlobalTheory.TwistUnr.unrAt_xiTw | exact GlobalTheory.TwistUnr.unrAt_xiTw | (intros; apply GlobalTheory.TwistUnr.unrAt_xiTw <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelUniformityOfCmDatum

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.XUni
theorem level_uniformity_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ kk u (s : SplitPlace (Dof x).host.E), s.w = (Dof x).naut.plGw kk u → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (eta (D := Dof x) (cfOf x) w.I.xi v j) s ξ ∧ ∀ e, SideRead i b (T.k v) e → NG.LevelUni (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) s (Dof x).R.r ψ₀ ξ := by
  intro hP hL
  refine StepW.of_all fun K B f T w hK hF _ P x l v i b ψ hA j htw hl hok kk u s hs => ?_
  obtain ⟨τ', hτ'⟩ := l.b.tau
  let kv0 : Σ k : Fin 2, (Dof x).nd.PlG k := ⟨kk, u⟩
  have hsw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w = s.w := by
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨kv0, rfl⟩)), hs]
  obtain rfl := GlobalTheory.T.splitPlace_eq_of_cmFieldPlace_eq _ _ _ hsw
  have hg : (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∈
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w.asIdeal := by
    rw [hsw, hs]; exact (Dof x).naut.plGw_over kk u
  have hoffkv : ∀ kv, kv ≠ kv0 → ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv)).v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun kv hne heq =>
    hne (GlobalTheory.PlaceInj.splitPlace_v_injective (Dof x)
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) ⟨k, v⟩))
      (fun k v => (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨⟨k, v⟩, rfl⟩))) heq)
  have hoffQ : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inl hP')] at h1
    exact (hA.2.1 P' ((cell (D := Dof x) l.b.Bs.exp b hA j).QP_sub hP')).2 kk h1
  have hoffD : ∀ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP, ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v ≠
      ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v := fun P' hP' heq => by
    have h1 := GlobalTheory.T.splitPlaces_same_realPlace_natCast_mem _ _ _ _ heq.symm hg
    rw [(cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (Or.inr (Or.inl hP'))] at h1
    exact GlobalTheory.T.generator_not_mem_twist_place _ _ _ kk ((cell (D := Dof x) l.b.Bs.exp b hA j).DP_sub hP') h1
  haveI : Fact ((Dof x).host.g kv0.1).Prime := ⟨(Dof x).host.g_prime kk⟩
  let φ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ :=
    { toFun := fun y => embLL0 (Dof x) ((l.rat.In.θ kv0.1 (Multiplicative.ofAdd (NX.xiRed (Dof x) kv0 * y)) : (↥(Dof x).LL0)ˣ) : ↥(Dof x).LL0)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a c => by rw [mul_add, ofAdd_add, map_mul, Units.val_mul, map_mul] }
  have hφ : 2 ≤ (Dof x).R.r → φ ≠ 1 := fun hr h1 => by
    have e1 := congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ 1) h1
    have hne := GlobalTheory.T.rationalDatum_characters_ne_one_at_fixedElement_residues _ _ _ _ _ _ _ _ _ l.b.Bs hr i kv0
    apply hne
    simp only [φ, AddChar.coe_mk, AddChar.one_apply, mul_one] at e1
    exact Units.ext ((embLL0 (Dof x)).injective (by rw [e1, Units.val_one, map_one]))
  have hex := GlobalTheory.T.exists_nontrivial_addChar_zmod_eq_of_ne_one ((Dof x).host.g kv0.1) (2 ≤ (Dof x).R.r) φ hφ
  let ψ' := hex.choose
  have hψ'1 : ψ' ≠ 1 := hex.choose_spec.1
  have hψ'φ : 2 ≤ (Dof x).R.r → ψ' = φ := hex.choose_spec.2
  have hex0 := GlobalTheory.T.exists_addChar_completion_of_residue_addChar (maximalRealSubfield (Dof x).host.E)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).v ((Dof x).host.g kv0.1)
    ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0) ψ' hψ'1
  let ψ₀ := hex0.choose
  have hψ₀m := hex0.choose_spec.1
  have hψ₀n := hex0.choose_spec.2.1
  have hψ₀r := hex0.choose_spec.2.2
  have hunr : (w.I.xi ((Dof x).what₂.muTw v)).UnrAt ((cell (D := Dof x) l.b.Bs.exp b hA j).sp (NX.pG (Dof x) kv0)).w := by
    have e2 : w.I.xi ((Dof x).what₂.muTw v) = T.xiTw f v := P.q.mu.tw v
    rw [e2]
    refine GlobalTheory.T.twistedTuple_finiteOrderPart_unramified_at_typePrimes B f T v _ kk hg fun hQ => ?_
    rw [← Model.qOf_eq (P := P) v] at hQ
    exact (hA.2.1 _ hQ).2 kk hg
  have hexξ := GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter hP.what₂.art _ _ _ _ _ _ _ _ _ l.b.Bs l.a.val τ' hτ' j kv0 _ hs
    _ hunr ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0)
  let ξ := hexξ.choose
  have hξc := hexξ.choose_spec.1
  have hξv := hexξ.choose_spec.2
  refine ⟨ψ₀, ξ, ⟨hψ₀m, hψ₀n⟩, hξc, fun e he => ⟨fun κ hκ => GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ _ kv0 hoffkv hoffQ hoffD κ hκ, ?_⟩⟩
  intro κ h hκ uu huu
  have hc := GlobalTheory.T.levelCharacter_eq_localFactor_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ h hκ
  have hU := (GlobalTheory.T.mem_level_iff_unipotent_at_typePlace _ _ _ _ _ _ _ _ _ _ _ (cell (D := Dof x) l.b.Bs.exp b hA j) kv0 hoffkv hoffQ hoffD κ hκ).1 h
  have hr := GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet _ l.b.Bs.exp i _ b kv0 _ _ l.rat.In.θ (fun u hu hu' => l.b.Bs.psiU i b u hu hu') _ (τ' (j.1 + 1) kv0)
    (fun y => hτ' i (j.1 + 1) b kv0 y (Nat.le_add_left 1 j.1) j.2) e he ψ₀ (fun hr y => (hψ₀r y).trans (congrArg (fun χ : AddChar (ZMod ((Dof x).host.g kv0.1)) ℂ => χ ((cell (D := Dof x) l.b.Bs.exp b hA j).redG kv0 y)) (hψ'φ hr))) ξ hξv _ hU uu huu
  exact (cx_apply e _ ⟨κ, h⟩).trans ((congrArg e hc).trans hr)
end GlobalTheory.XUni
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.level_uniformity_of_cmDatum_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ kk u (s : SplitPlace (Dof x).host.E), s.w = (Dof x).naut.plGw kk u → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield (Dof x).host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt (eta (D := Dof x) (cfOf x) w.I.xi v j) s ξ ∧ ∀ e, SideRead i b (T.k v) e → NG.LevelUni (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) s (Dof x).R.r ψ₀ ξ := by
  first | exact @_root_.GlobalTheory.XUni.level_uniformity_transfer_alt | exact _root_.GlobalTheory.XUni.level_uniformity_transfer_alt | (intros; apply _root_.GlobalTheory.XUni.level_uniformity_transfer_alt <;> assumption)
end
end
end
end
