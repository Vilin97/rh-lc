module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstComStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowBlockIndicatorFromLtIff
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIndexLocalNormNormalizingFactorEqPartialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuUnramifiedOffPairPartialLPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeSelfDualAndIntegralIffStabilizesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductBottomNormEq

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartan

section

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

open scoped Matrix ComplexOrder

namespace GlobalTheory.NormRatio

theorem gramAt_eq_one_of_gram {D : D7} (V : HSp D) (h : V.gram = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold Formalism.BasicNotions.TH.gramAt
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem sig_snd_eq_zero_of_gram {D : D7} {V : HSp D} (hg : V.gram = 1) (hV : V.SigOK) (τ : D.host.E →+* ℂ) :
    (V.sig τ).2 = 0 := by
  obtain ⟨e, P, hP⟩ := hV τ
  have h1 : (V.gram.map τ).reindex e e = 1 := by
    rw [hg, Matrix.map_one _ (map_zero τ) (map_one τ)]; exact Matrix.submatrix_one_equiv _
  rw [h1, Matrix.mul_one] at hP
  have hP' : (P.1)ᴴ * P.1 = Formalism.UG.Jpq (V.sig τ).1 (V.sig τ).2 := hP
  by_contra hq
  let k : Fin (V.sig τ).2 := ⟨0, Nat.pos_of_ne_zero hq⟩
  have hk := congrArg (fun M => (M (Sum.inr k) (Sum.inr k)).re) hP'
  simp only [Formalism.UG.Jpq, Matrix.fromBlocks_apply₂₂, Matrix.neg_apply, Matrix.one_apply_eq, Complex.neg_re,
    Complex.one_re] at hk
  have : 0 ≤ (((P.1)ᴴ * P.1) (Sum.inr k) (Sum.inr k)).re := by
    rw [Matrix.mul_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun l _ => by
      rw [Matrix.conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]; exact Complex.normSq_nonneg _
  linarith

theorem exists_ipPair_one : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  intro D cc δ t0 Q P X hX h1 h2
  obtain ⟨hF, hW⟩ := hX
  have gA := gramAt_eq_one_of_gram X.A hF.gramA
  have gB := gramAt_eq_one_of_gram X.B hF.gramB
  have hI : ∀ k : ℕ, IsCartanInv (1 : Matrix (Fin k) (Fin k) ℂ) 1 := fun k =>
    ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  have hA : X.A.SigOK := hF.defA.1
  have hq := sig_snd_eq_zero_of_gram hF.gramA hA
  obtain ⟨cA, hc⟩ := GlobalTheory.Cusp.exists_isCartanFrame X.A hA
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne D X.B.rank X.A.rank
  have hone : ∀ τ, compAt X.θ τ (1 : GL (Fin X.A.rank) (AE D)).1 = 1 := fun τ => by
    exact Matrix.map_one ((X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have rA := X.rkA
  have rB := X.rkB
  refine ⟨cA, 1, ν, 𝓕, ⟨by omega, by omega, by omega, hW.inf, hA, hc, fun τ => ?_, fun τ => ?_, fun τ => ?_⟩,
    (GlobalTheory.Doubling.isMaj_iff hW.inf).2 fun τ => ⟨fun _ => true, ?_⟩, fun τ => ?_, hW.weil, hν⟩
  · rw [gA]; exact hI _
  · rw [gB]; exact hI _
  · have hJ : Formalism.UG.Jpq (X.A.sig (tauE D τ)).1 (X.A.sig (tauE D τ)).2 = 1 := by
      have : IsEmpty (Fin (X.A.sig (tauE D τ)).2) := by rw [hq]; infer_instance
      rw [Formalism.UG.Jpq, ← Matrix.fromBlocks_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hJ]; simp
  · rw [hone, gA]; simp
  · rw [hone, gA]; simp

end GlobalTheory.NormRatio
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaDoublingPairDataIdentityCartanStatement

section

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X → 1 ≤ P.a → P.a < P.d →
  ∃ (cA : GlobalTheory.Mem.Th.CptF X.A) (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)),
    GlobalTheory.Core.Rk.IP.Pair X.ψ X.θ X.A X.B X.χA X.χB (fun _ => 1) (fun _ => 1) (P.d - P.a) cA a X.om ν 𝓕 := by
  first | exact @GlobalTheory.NormRatio.exists_ipPair_one | exact GlobalTheory.NormRatio.exists_ipPair_one | (intros; apply GlobalTheory.NormRatio.exists_ipPair_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverseStatement

section

@[expose] public section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio


theorem _root_.GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) (ν : Formalism.L2.Host.HChar D.host.E),
  IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) → ChrEq χ ν := by
  first | exact @GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | exact GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | (intros; apply GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPeterssonNormEqRallisIntegral

section

@[expose] public section

section
noncomputable section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
namespace GlobalTheory.NormRatio
section General
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end General
section Translates
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)
end Translates
section Exact
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
end Exact
section Fock
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}
end Fock
section Norm
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
theorem theta_lift_petersson_norm_eq_rallis_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (hX : IsDict P X)
    {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))} {μ₀ : Measure (GA D X.B)} (hK : IsMaxLevel X.toFrame K₀ μ₀)
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ} (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o)
    (ho : o + P.a ≤ P.d) (ha : 1 ≤ P.a) (had : P.a < P.d) (hu : GlobalTheory.LFun.UnrOff X.χB (Sf : Set (FinPl D))) (Λ : ℂ → ℂ)
    (hΛ : ∀ s, GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL X.χB⁻¹ (Sf : Set (FinPl D))) s (Λ s)) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) =
      mass D P.d * mass D P.a * ((∏ i ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - i)) /
        GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) P.a P.d (((P.d - P.a : ℕ) : ℂ) / 2)) *
        (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) *
          ((locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ))) := by
  refine (GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan P X hX ha had).elim fun cA h1 => h1.elim fun a h2 => h2.elim fun ν h3 => h3.elim fun 𝓕 hPair => ?_
  have hfd := finite_data hI h hm hstd ho
  refine hfd.1.elim fun LB hLB => ?_
  have hn := (hfd.2 ν 𝓕 hPair.covol).1
  have hs := (hfd.2 ν 𝓕 hPair.covol).2
  have hlev := fun x => GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)
  have hsph : IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf (X.fock T) := isSphOff_pure hX.2.inf hLB.2 _ _ _ _ _
  have hU : GlobalTheory.Core.Rk.IP.Unram X.ψ X.A X.B X.χB (stdLat X.A) LB Sf (X.fock T) (X.fock T) :=
    ⟨(hlev 1).1, hLB.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2, hu, hsph, hsph⟩
  have hint := GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact P X hX (hlev 1).1 (fun x => (hlev x).2) a ν 𝓕 hPair.maj Sf (X.fock T)
    (ip X.A X.B ν 𝓕 (X.fock T) (X.fock T))
    (fun x hx k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (by rw [hX.2.fixA x hx T]))
    (fun x hx hx' k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (ip_fock_zero hX hPair.covol T (h.std.ptA x).1 (hs x hx hx')))
  refine hK.meas.elim fun 𝓕₀ h𝓕₀ => hX.1.measA.elim fun 𝓕A h𝓕A => ?_
  haveI := hX.1.haarA
  haveI : μ₀.IsHaarMeasure := h𝓕₀.1.1
  have hA : GlobalTheory.Cusp.wittIndex X.A = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramA)
  have hB : GlobalTheory.Cusp.wittIndex X.B = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramB)
  have key := _root_.GlobalTheory.BottomRallis.rallis_inner_product_bottom_norm_eq hP hPair hA hB (isFockVec_fock hX T) hU X.m μ₀
    ⟨((P.d - P.a : ℕ) : ℝ) / 2 - 1, by linarith, hint.1 _⟩
    (fun i => Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (X.A.rank : ℂ) / 2 - i)) fun i _ => hΛ _
  have vA := volQ_eq_mass X.A P.a X.ιA X.KA X.m 𝓕A hX.1.defA hX.1.injA hX.1.rangeA hX.1.ratA hX.1.levA hX.1.levA_iff h𝓕A
  have vB := volQ_eq_mass X.B P.d X.ιB K₀ μ₀ 𝓕₀ hX.1.defB hX.1.injB hX.1.rangeB hX.1.ratB hK.lev hK.mem_iff h𝓕₀
  have e1 := hint.2.trans ((ip_fock hX hPair.covol T).trans (congrArg _ hn))
  refine key.trans ?_
  rw [vA, vB, e1, X.rkA, X.rkB]
theorem petersson_norm_bottom_theta_lift_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) {T : Type}
    {L : LevCh D T} {sc : Consts} {μ : T} (hL : L.Is μ) (G : GridData L sc) {t : T} {i j : Fin D.R.m}
    {P' : Pair D ⊤ δ t0 Q} (hb : IsBottom G t i j (modT G t) P P') {Λ : ℂ → ℂ} (hΛ : GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ) :
    (P.norm : ℂ) = normFactor D δ t0 P.a P.d P.n *
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  have hm := goodMod_modT hL (GlobalTheory.SqTop.BotT.pde_ne_q hR).1 (GlobalTheory.SqTop.BotT.pde_ne_q hR).2 G t
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hdict := exact_dictionary P hI (isCongLevel_of_isBlockLevel hm.1 hb.lev.1)
  refine hdict.2.1.elim fun X h1 => h1.elim fun r h2 => h2.elim fun K₀ h3 => h3.elim fun μ₀ h4 => ?_
  have h5 := hdict.2.2 X r K₀ μ₀ h4.1 h4.2
  have hX := h5.1.1
  have hχ := GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse X.χB P.W.chV' P.W.ep' (nuH G t i j) hX.2.weil.hecT h4.1.chB hb.chars.2
  have hl := GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive hL hR.hF G t i j X.χB hχ
  have hT := _root_.GlobalTheory.NormRatio.theta_lift_petersson_norm_eq_rallis_integral hP hI h4.1 hX h4.2 hm hb.std (by rw [zero_add]; exact P.a_le) (by omega) (by omega) hl.1 Λ
    (hl.2 Λ hΛ)
  have hidx : ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = locIdx D (modT G t) P.a (P.d - P.a) :=
    GlobalTheory.StdLoc.relIndex_blockLevel P (modT G t) P.a hm.1 hm.2.1 P.a_le (hPa.symm ▸ hb.lev.1)
  have hidx' : ((P.J.relIndex (intG D P.d) : ℕ) : ℂ) = (locIdx D (modT G t) P.a (P.d - P.a) : ℂ) := by
    rw [← hidx]; rfl
  have hd := GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial D (modT G t) (sfB G t) hm P.a (P.d - P.a) (by omega)
  rw [Nat.add_sub_cancel' P.a_le] at hd
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hprod : ∏ k ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - k) =
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
    obtain ⟨u, hu⟩ := hrk.2.2.1
    have e1 : P.d = 2 * GlobalTheory.SqTop.h0 D i j := by unfold GlobalTheory.SqTop.h0; omega
    rw [← GlobalTheory.BottomRallis.prod_range_sub_eq_prod_Icc (fun s => Λ s) P.a (GlobalTheory.SqTop.h0 D i j) (GlobalTheory.SqTop.e0 D i j)
      (by unfold GlobalTheory.SqTop.h0 GlobalTheory.SqTop.e0; omega)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    rw [Nat.cast_sub P.a_le, e1]
    push_cast
    ring
  refine h5.2.2.2.2.trans ?_
  rw [Finset.sum_congr rfl fun T _ => hT T, ← Finset.mul_sum, ← Finset.sum_mul, hidx', hprod]
  exact collect hd (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
end Norm
theorem big_theta_petersson_norm_ratio_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  intro hP hI _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 i j t t' Q Q' P P' P₁ P₁' Λ Λ' hb hb' hΛ hΛ'
  have h1 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb hΛ
  have h2 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb' hΛ'
  have h3 := (GlobalTheory.BottomReal.bottom_real_eq G hL hb hb').1
  have h4 : normFactor D δ t0 P.a P.d P.n = normFactor D δ t0 P₁.a P₁.d P₁.n :=
    congr (congr (congrArg (normFactor D δ t0) h3.1) h3.2.1) h3.2.2.1
  rw [h1, h2, h4]
  ring
end GlobalTheory.NormRatio
end
end

section
open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  first | exact @_root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | exact _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | (intros; apply _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq <;> assumption)
end
end
end
