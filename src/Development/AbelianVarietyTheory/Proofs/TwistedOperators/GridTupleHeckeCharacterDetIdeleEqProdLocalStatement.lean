module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMtCutPartCompl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponent
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIdeleExistsLocalApprox
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqProdLocalComponentsApproximating
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitaryConjAtPlaceEqDetLatticeBasisComponentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k u : FinPt G (.top (j + 1))) (w : Pl D.host.E), ((Formalism.L2.Theta.mt (G.V (.top (j + 1))) ((u⁻¹ * k * u : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))).map fun z => GlobalTheory.StdFrames.cpt w (toEAf D z)).det = ((gdet (kapAt S t j hj k w) : (Kw w)ˣ) : Kw w) := by
  first | exact @GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | exact GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt | (intros; apply GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartCompon

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
noncomputable section

namespace GlobalTheory.TopLevelInv

variable {D : D7}

theorem infPart_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) : infPart D e = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum (infPart D).toAddMonoidHom es P
  change (infPart D).toAddMonoidHom _ = 0
  rw [hs]
  exact Finset.sum_eq_zero fun PP hPP =>
    (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) (hes PP hPP)).1


open Classical in
theorem cpt_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hs := map_sum ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom es P
  change ((GlobalTheory.StdFrames.cpt Q).comp (toEAf D)).toAddMonoidHom _ = _
  rw [hs]
  have h : ∀ PP ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (es PP)) = if PP = Q then 1 else 0 := fun PP hPP => by
    by_cases hQ : PP = Q
    · subst hQ; rw [if_pos rfl]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).1
    · rw [if_neg hQ]; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 Q (Ne.symm hQ)
  calc _ = ∑ PP ∈ P, (if PP = Q then (1 : Q.adicCompletion D.host.E) else 0) := Finset.sum_congr rfl h
    _ = _ := by rw [Finset.sum_ite_eq']

theorem cpt_one_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∈ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 1 := by
  classical
  rw [cpt_of_isIdemSum he, if_pos hQ]

theorem cpt_zero_of_isIdemSum {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {Q : Pl D.host.E} (hQ : Q ∉ P) :
    GlobalTheory.StdFrames.cpt Q (toEAf D e) = 0 := by
  classical
  rw [cpt_of_isIdemSum he, if_neg hQ]

theorem map_unitMix_of_zero {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (e x : R) (h : φ e = 0) :
    φ (e * x + (1 - e)) = 1 := by
  rw [map_add (f := _), map_mul, map_sub, map_one, h]; ring


theorem detAt_cutPart_parts {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V) :
    infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧
    (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧
    ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V
      (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  have hee : e * e = e := (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem
  have hc : e * cA D e = 0 := he.2
  have hf := idem_conj_sum hee hc
  have hval : (GlobalTheory.VecInv.detAt e hee V (cutPart (e + cA D e) V g) : AE D) =
      e * (Formalism.L2.Theta.mt V (cutPart (e + cA D e) V g)).det + (1 - e) := rfl
  rw [hval]
  have hinf := infPart_of_isIdemSum he
  refine ⟨?_, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 1 := cpt_one_of_isIdemSum he hQ
    have h2 : φ (cA D e) = 0 := by
      have := congrArg φ hc
      rwa [RingHom.map_mul, RingHom.map_zero, h1, one_mul] at this
    have h3 : φ (e + cA D e) = 1 := by rw [RingHom.map_add (f := _), h1, h2, add_zero]
    change φ _ = ((Formalism.L2.Theta.mt V g).map φ).det
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h1, one_mul, sub_self, add_zero,
      RingHom.map_det, mt_cutPart hf.1 hf.2]
    congr 1
    refine Matrix.ext fun i j => ?_
    change φ ((e + cA D e) * Formalism.L2.Theta.mt V g i j + (1 - (e + cA D e)) * (1 : Matrix _ _ (AE D)) i j) = φ (Formalism.L2.Theta.mt V g i j)
    rw [RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h3, one_mul, sub_self,
      zero_mul, add_zero]
  · let φ : AE D →+* Q.adicCompletion D.host.E := (GlobalTheory.StdFrames.cpt Q).comp (toEAf D)
    have h1 : φ e = 0 := cpt_zero_of_isIdemSum he hQ
    change φ _ = 1
    exact map_unitMix_of_zero φ e _ h1

end GlobalTheory.TopLevelInv

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtIdempotentIdempotentPartComponStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (V : HSp D) (g : GA D V), infPart D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D) = 1 ∧ (∀ Q ∈ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = ((Formalism.L2.Theta.mt V g).map fun z => GlobalTheory.StdFrames.cpt Q (toEAf D z)).det) ∧ ∀ Q ∉ P, GlobalTheory.StdFrames.cpt Q (toEAf D (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem V (cutPart (e + cA D e) V g) : AE D)) = 1 := by
  first | exact @GlobalTheory.TopLevelInv.detAt_cutPart_parts | exact GlobalTheory.TopLevelInv.detAt_cutPart_parts | (intros; apply GlobalTheory.TopLevelInv.detAt_cutPart_parts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open scoped TensorProduct

namespace GlobalTheory.TameCharProd

open Formalism.L2.Host

theorem loc_eq_locK_of_tame {L : Type} [Field L] [NumberField L] (χ : HChar L) (P : HeightOneSpectrum (𝓞 L))
    (hP : χ.TameAt P) (a : (P.adicCompletion L)ˣ) (k : Lˣ)
    (h1 : Valued.v (a : P.adicCompletion L) = P.valuation L (k : L))
    (h2 : Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L)) :
    χ.loc P a = χ.locK P k := by
  have hk0 : P.valuation L (k : L) ≠ 0 := (Valuation.ne_zero_iff _).2 k.ne_zero
  have hak : ((atFin P k : (P.adicCompletion L)ˣ) : P.adicCompletion L) = algebraMap L _ (k : L) := rfl
  have hK0 : algebraMap L (P.adicCompletion L) (k : L) ≠ 0 := (map_ne_zero _).2 k.ne_zero
  have hval : Valued.v (algebraMap L (P.adicCompletion L) (k : L)) = P.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : L)
  set u : (P.adicCompletion L)ˣ := a * (atFin P k)⁻¹ with hu_def
  have hu : IsUnitAt P u := by
    unfold IsUnitAt
    rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, map_mul, map_inv₀, hval, h1, mul_inv_cancel₀ hk0]
  have hu1 : Valued.v ((u : P.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : (u : P.adicCompletion L) - 1 = ((a : P.adicCompletion L) - algebraMap L _ (k : L)) *
        (algebraMap L (P.adicCompletion L) (k : L))⁻¹ := by
      rw [hu_def, Units.val_mul, Units.val_inv_eq_inv_val, hak, sub_mul, mul_inv_cancel₀ hK0]
    rw [e, map_mul, map_inv₀, hval, Nat.cast_one]
    calc Valued.v ((a : P.adicCompletion L) - algebraMap L _ (k : L)) * (P.valuation L (k : L))⁻¹
        ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) * (P.valuation L (k : L))⁻¹ := by gcongr
      _ = WithZero.exp (-1 : ℤ) := by rw [mul_assoc, mul_inv_cancel₀ hk0, mul_one]
  have hχ := hP u hu hu1
  calc χ.loc P a = χ.loc P (u * atFin P k) := by rw [hu_def, inv_mul_cancel_right]
    _ = χ.locK P k := by rw [map_mul, hχ, one_mul]; rfl

end GlobalTheory.TameCharProd

namespace GlobalTheory.TameCharProd

theorem char_eq_prod_loc_of_tame : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  intro D c χ hc T hT a x hx hT1 hT0
  classical
  have hsp := GlobalTheory.StdFrames.toAd_spec D
  let sw := Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E
  let φ : (Af D.host.F ⊗[D.host.F] D.host.E) →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    (GlobalTheory.StdFrames.toAd D).comp sw.toRingEquiv.toRingHom
  have hbij : Function.Bijective φ :=
    ⟨(GlobalTheory.AdeleBaseChange.map_injective hsp).comp sw.injective,
      (GlobalTheory.AdeleBaseChange.map_surjective hsp).comp sw.surjective⟩
  let ι := RingEquiv.ofBijective φ hbij
  have hxP : ∀ P, ι (finPart D (x : AE D)) P = GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) := fun P => rfl
  have hι : ∀ y : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) y := by
    intro y
    show GlobalTheory.StdFrames.toAd D (sw ((1 : Af D.host.F) ⊗ₜ[D.host.F] y)) = _
    rw [Algebra.TensorProduct.comm_tmul]
    exact GlobalTheory.AdeleBaseChange.map_tmul_one hsp y
  have hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1 := by
    intro y
    rw [GlobalTheory.HostAdeleIso.mem_intAE_iff_comm]
    constructor
    · intro h P
      have h' := GlobalTheory.AdeleBaseChange.map_mem_int hsp h
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (h' P)
    · intro h
      exact GlobalTheory.AdeleBaseChange.mem_int_of_map hsp fun P =>
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)
  have hidem : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, Formalism.L2.JoinChr.IsPlIdem D e P ∧ infPart D e = 0 ∧
      ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0 := by
    intro P
    obtain ⟨ι₀, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι₀ h1 h2 h3 P
    exact ⟨e, he, GlobalTheory.HeckeTensorRead.isPlIdem_parts D ι hι hint he⟩
  obtain ⟨N, hN, hmain⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι hint hidem c χ hc
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      (P ∈ T → Valued.v ((a P : Kw P) : P.adicCompletion D.host.E) = P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) ∧
        Valued.v ((a P : P.adicCompletion D.host.E) - algebraMap D.host.E _ (k : D.host.E)) ≤
          WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k : D.host.E)) ∧ (P ∉ T → k = 1) := by
    intro P
    by_cases hP : P ∈ T
    · obtain ⟨k, h1, h2, h3⟩ :=
        GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P (a P : P.adicCompletion D.host.E) (a P).ne_zero
      exact ⟨k, fun _ => ⟨h1, h2, h3⟩, fun h => absurd hP h⟩
    · exact ⟨1, fun h => absurd h hP, fun _ => rfl⟩
  choose k hkT hk1 using hk
  have hfin : {P : HeightOneSpectrum (𝓞 D.host.E) | (N : 𝓞 D.host.E) ∈ P.asIdeal}.Finite := by
    have hN0 : (N : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
    refine (Ideal.finite_factors (I := Ideal.span {(N : 𝓞 D.host.E)})
      (by simpa [Ideal.span_singleton_eq_bot] using hN0)).subset ?_
    intro P hP
    exact Ideal.dvd_span_singleton.2 hP
  have hTS : T ⊆ T ∪ hfin.toFinset := Finset.subset_union_left
  have key := hmain x hx (T ∪ hfin.toFinset) k (fun P _ => by
      by_cases hP : P ∈ T
      · rw [hxP, hT1 P hP]
        exact ⟨(hkT P hP).1, (hkT P hP).2.1⟩
      · rw [hxP, hT0 P hP, hk1 P hP]
        simp) (fun P hP => by
      simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or] at hP
      rw [hxP, hT0 P hP.1]
      exact ⟨map_one _, hP.2⟩)
  rw [key, ← Finset.prod_subset hTS (fun P _ hP => by rw [hk1 P hP, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun P hP => ?_
  rw [loc_eq_locK_of_tame χ P (hT P hP) (a P) (k P) (hkT P hP).1 (hkT P hP).2.2]

end GlobalTheory.TameCharProd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIdeleCharEqProdLocOfTameAtStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt : ∀ {D : D7} {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E}, ChrEq c χ → ∀ (T : Finset (Pl D.host.E)), (∀ P ∈ T, χ.TameAt P) → ∀ (a : ∀ P : Pl D.host.E, (Kw P)ˣ) (x : (AE D)ˣ), infPart D (x : AE D) = 1 → (∀ P ∈ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = (a P : Kw P)) → (∀ P ∉ T, GlobalTheory.StdFrames.cpt P (toEAf D (x : AE D)) = 1) → ((c x : Circle) : ℂ) = ∏ P ∈ T, ((χ.loc P (a P) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | exact GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame | (intros; apply GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem chrEq_mu_succ_succ : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ChrEq (L.mu t (j + 1 + 1)) (muBase L (j + 1 + 1) * L.xiH t) ∧ ∀ P, (muBase L (j + 1 + 1) * L.xiH t).TameAt P := by
  intro D T L μ₀ hL t j hj
  have hm : ChrEq (L.mu0 (j + 1 + 1)) (muBase L (j + 1 + 1)) := by
    have := hL.mu0 ⟨j + 1, hj⟩
    simpa [muBase, hj] using this
  refine ⟨GlobalTheory.TowerCharRead.chrEq_mul hm (hL.xi t), fun P => ?_⟩
  have h1 : (muBase L (j + 1 + 1)).TameAt P := by
    rw [muBase, dite_eq_left hj]; exact (L.C.isMu0 ⟨j + 1, hj⟩).tame P
  exact Formalism.L2.Host.HChar.LevelLe.mul h1 (hL.xi_tame t P)

theorem mu_detAt_eq_prod_loc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he
  obtain ⟨hχ, htame⟩ := chrEq_mu_succ_succ hL t j hj
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components he (G.V (.top (j + 1)))
    ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))
  rw [GlobalTheory.T.unitaryIdeleChar_eq_prod_loc_of_tameAt hχ (locPl G t) (fun P _ => htame P) (fun P => gdet (kapAt S t j hj k P)) _ hinf
    (fun P hP => (hin P hP).trans (GlobalTheory.T.det_unitaryConj_atPlace_eq_det_latticeBasisComponent S t j hj k _ P)) hout]
  rw [← Finset.prod_coe_sort]
  rfl

end GlobalTheory.TopLevelInv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

theorem _root_.GlobalTheory.T.gridTupleHeckeCharacter_detIdele_eq_prod_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc | exact GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc | (intros; apply GlobalTheory.TopLevelInv.mu_detAt_eq_prod_loc <;> assumption)
end
end
