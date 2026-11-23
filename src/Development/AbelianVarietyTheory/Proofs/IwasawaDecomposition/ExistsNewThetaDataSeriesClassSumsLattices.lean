module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsOfFi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadingRealSide
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetupPinnedCh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiniteDimensionalSpan
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodSetupCountEqZeroOffBadPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MtLatFgOfReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTwistOfTwistingCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfReadsExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperLeftBlockEqOneIffOfMemBlockTri
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTieWithSeries

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section




namespace GlobalTheory.SeriesInstall

variable {D : D7} {ρ : Setup D.ntw}

abbrev RdV (D : D7) (ρ : Setup D.ntw) : Type :=
  ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k]
    (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)

def rdVLin (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k]
      Via (D.ntw.Ok i k) (ρ.ek i b k) (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank) where
  toFun f := rdV i j b k Q ψ f
  map_add' f g := map_add _ f g
  map_smul' c f := by
    rw [← algebraMap_smul (FractionRing (D.ntw.Ok i k)) c f, map_smulₛₗ]
    rfl


open Classical in
def latI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ, Submodule (D.ntw.Ok i k) (D.nexp.MtV i n b k Q ψ)
  | 0, b, k, Q, ψ => D.nexp.MtLat i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then
      (Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)).comap (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) else D.nexp.MtLat i (n + 1) b k Q ψ

def Onto (ρ : Setup D.ntw) (rdV : RdV D ρ) : Prop :=
  ∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧
    Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤

theorem latI_eq (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) :
    latI rdV i ((j : ℕ) + 1) b k Q ψ = (Via.lat (ρ.mt i j b k Q ψ)).comap (rdVLin rdV i j b k Q ψ) :=
  dif_pos ⟨j.2, h⟩

theorem mem_latI (rdV : RdV D ρ) {i} (j : Fin D.R.m) {b k Q ψ} (h : TwOK i k Q ψ) (f) :
    f ∈ latI rdV i ((j : ℕ) + 1) b k Q ψ ↔ rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ := by
  rw [latI_eq rdV j h]; exact Iff.rfl

theorem latI_fg (rdV : RdV D ρ) (hV : Onto ρ rdV) (hL : ρ.LatFG) (i) :
    ∀ n b k Q ψ, (latI rdV i n b k Q ψ).FG
  | 0, b, k, Q, ψ => D.nexp.MtLat_fg i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · rcases hV i ⟨n, h.1⟩ b k Q ψ h.2 with ⟨hinj, hon, _⟩
      refine Submodule.fg_of_fg_map_injective (rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) hinj ?_
      rw [Submodule.map_comap_eq_self (f := rdVLin rdV i ⟨n, h.1⟩ b k Q ψ) (q := Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ))
        fun x (hx : x ∈ Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ)) => by obtain ⟨y, hy⟩ := hon (Via.out _ _ x) hx; exact ⟨y, hy⟩]
      exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact D.nexp.MtLat_fg i (n + 1) b k Q ψ

theorem latI_span (rdV : RdV D ρ) (hV : Onto ρ rdV) (i) :
    ∀ n b k Q ψ, Submodule.span (FractionRing (D.ntw.Ok i k)) (latI rdV i n b k Q ψ : Set (D.nexp.MtV i n b k Q ψ)) = ⊤
  | 0, b, k, Q, ψ => D.nexp.MtLat_span i 0 b k Q ψ
  | n + 1, b, k, Q, ψ => by
    rw [latI]
    split_ifs with h
    · exact (hV i ⟨n, h.1⟩ b k Q ψ h.2).2.2
    · exact D.nexp.MtLat_span i (n + 1) b k Q ψ

variable (hρ : ρ.Good) (rd : Rds D.nexp ρ) (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thPI (rdV : RdV D ρ) (i) (j : Fin D.R.m) (b k Q ψ) :
    ∃ φ : D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV i j b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV i j b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange D.nexp i _ b k)

def thPI (rdV : RdV D ρ) (i) : ∀ n b k Q ψ,
    D.nexp.MtV i n b k Q ψ →ₗ[D.ntw.Ok i k] D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thPI hρ rd hF rdV i ⟨n, h⟩ b k Q ψ).choose else 0

theorem exists_tie_withSeries : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), (∀ i j b, Faithful (rd i j b)) → ρ.LevelOf D.nexp → ρ.LatFG → ∀ rdV : ∀ i (j : Fin D.R.m) b k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank), (∀ i j b k Q ψ, TwOK i k Q ψ → Function.Injective (rdV i j b k Q ψ) ∧ (∀ F ∈ ρ.mt i j b k Q ψ, F ∈ Set.range (rdV i j b k Q ψ)) ∧ Submodule.span (FractionRing (D.ntw.Ok i k)) {f | rdV i j b k Q ψ f ∈ ρ.mt i j b k Q ψ} = ⊤) → ∃ Dat th lev thPsi h1 thU thP MtLat h2 h3, (∀ i j, j ∉ Finset.Icc 1 D.R.m → ∀ b, IsEmpty (Dat i j b)) ∧ ∃ t : Comparison₂ hρ (Y := { D.nexp with Dat := Dat, th := th, lev := lev, thPsi := thPsi, thPsi_one := h1, thU := thU, thP := thP, MtLat := MtLat, MtLat_fg := h2, MtLat_span := h3 }) rd, ∀ i j b, (t i j b).rdV = rdV i j b := by
  intro D ρ hρ rd hF hU hL rdV hV
  refine ⟨Model.Dat rd, Model.th rd, Model.lev rd, Model.thPsi hρ rd, Model.thPsi_one hρ rd hF, Model.thU rd,
    thPI hρ rd hF rdV, latI rdV, latI_fg rdV hV hL, latI_span rdV hV, ?_, ?_⟩
  · intro i n hn b
    cases n with
    | zero => exact ⟨fun d => d.elim⟩
    | succ n =>
      refine ⟨fun d => hn (Finset.mem_Icc.2 ⟨Nat.succ_pos n, d.1⟩)⟩
  · refine ⟨fun i j b =>
      { supp := fun d => d.2.s
        cls := fun d => d.2.h
        coef := fun d => d.2.P
        rdV := rdV i j b
        U_eq := hU.U_eq i j b
        psiU_eq := hU.psiU_eq i j b
        dat := fun d => d.2.isDatum
        dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
        lev_iff := fun _ _ => Set.Finite.mem_toFinset _
        th_eq := fun d => d.2.rat.choose_spec
        thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
        thU_eq := fun Q M d hQ x hx => by
          have h : InRange D.ntw i Q ∧ ∀ a, ρ.xi i j b D.nexp Q M d.2.h d.2.P a ∈ Set.range (rd i j b) :=
            ⟨hQ, fun a => ⟨x a, hx a⟩⟩
          refine (dif_pos h).trans (congrArg (grpSum D.nexp (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
          exact (h.2 a).choose_spec.trans (hx a).symm
        thU_off := fun _ _ _ h => dif_neg h
        rdV_inj := fun k Q ψ h => (hV i j b k Q ψ h).1
        mtLat_iff := fun k Q ψ h F => by
          refine ⟨fun hF' => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
          · obtain ⟨f, rfl⟩ := (hV i j b k Q ψ h).2.1 F hF'
            exact ⟨f, (mem_latI rdV j h f).2 hF', rfl⟩
          · exact e' ▸ (mem_latI rdV j h f).1 hf
        thP_eq := fun k Q ψ _ f hf => by
          have e : thPI hρ rd hF rdV i ((j : ℕ) + 1) b k Q ψ = (exists_thPI hρ rd hF rdV i j b k Q ψ).choose := dif_pos j.2
          exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans
            ((exists_thPI hρ rd hF rdV i j b k Q ψ).choose_spec f hf) }, fun _ _ _ => rfl⟩

end GlobalTheory.SeriesInstall
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatrices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.FrameFinPart

theorem finHom_eq_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  intro D V n hF P P' hP hP' g
  obtain ⟨hn, h⟩ := hP
  obtain ⟨hn', h'⟩ := hP'
  apply Subtype.ext
  apply Units.ext
  ext a b
  change finMat D.sp.cm.sig V.gram (P.ψ g) a b = finMat D.sp.cm.sig V.gram (P'.ψ g) a b
  rw [h, h']

end GlobalTheory.FrameFinPart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteHomEqOfFramesKeepMatricesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P P' : principalLevelFrame.RowPsi V n), GlobalTheory.MtRead.IdFrame hF P → GlobalTheory.MtRead.IdFrame hF P' → ∀ g, (finHom V).rangeRestrict (P.ψ g) = (finHom V).rangeRestrict (P'.ψ g) := by
  first | exact @GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | exact GlobalTheory.FrameFinPart.finHom_eq_of_idFrame | (intros; apply GlobalTheory.FrameFinPart.finHom_eq_of_idFrame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSums

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



noncomputable section

namespace GlobalTheory.HeightCounting.SerCopy

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkAd_step (R : RealDat3 D A3 Ks) (Sb : Finset (PlE D.host)) (i' i : Fin D.R.m) (h : i' = i) (k : ℕ) (P : PlE D.host)
    (f : Module.End D.what₂.LL (Fin (R.nW i') → D.what₂.LL))
    (hAd : ∀ α Rr, HkDat R Sb i' k P α Rr → ∀ x : Fin (R.nW i') → D.what₂.LL,
      (R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) (f x)) =
        hkNorm R i' k P • Mult.heckeOn (R.MW i' (sg0 D A3.A)) Rr ((R.HW i' (sg0 D A3.A)).e ((R.FW i').j (sg0 D A3.A) x)))
    (α : GA D (Wc D i)) (Rr : Finset (GA D (Wc D i))) (hd : HkDat R Sb i k P α Rr) (x : Fin (R.nW i') → D.what₂.LL) :
    (R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e (f x))) =
      hkNorm R i k P • Mult.heckeOn (R.MW i (sg0 D A3.A)) Rr
        ((R.HW i (sg0 D A3.A)).e ((R.FW i).j (sg0 D A3.A) ((SideTies.fiOf R i' i h).e x))) := by
  subst h
  exact hAd α Rr hd x

variable {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}

theorem heckeAt_of_scaledAt (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    {ρ : Setup D.ntw} (hpin : RealPin Rl cG ρ) (hIs : Rl.toRealDat.toLevCh.Is A3.A.μ0)
    (hA : Rl.AllPlaces) (hρ : ρ.Good) {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    {u} (hδ : IsDeltaInv ρ u) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hs : NX.HeckeStabR S ((j : ℕ) + 1) (hL ((j : ℕ) + 1))) {k : ℕ} {P : PlE D.host} (hk : HkIdx i k P)
    (hr : ∀ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α →
      Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R → ∀ x : S.WL ((j : ℕ) + 1),
        (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (hL ((j : ℕ) + 1) k P x))) =
          ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
            Mult.heckeOn (Rl.MW j (sg0 D A3.A)) R ((Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x))))
    {f g : D.nexp.Fm i ((j : ℕ) + 1) b}
    (e1 : YS.eF i _ b (Nat.le_add_left _ _) j.2 g = (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k •
      NX.hkFR S i _ b (hL _) hs k P (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g := by
  rintro α R z ⟨hα, hR, hz⟩
  funext x
  rw [Setup.hecke_apply]
  have hδ' := hδ i j b k P hk α z hα hz
  obtain ⟨hk1, hkr, hsp, hP⟩ := hk
  have ho := GlobalTheory.ExportPin.Model.covered_of_allPlaces Rl hIs hA i P hP hsp
  have hR' : Bridge.IsDC (Formalism.IndefR.Lev.levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv)) α R :=
    GlobalTheory.PrincipalLevel.levK_eq_levG hpin i j b ▸ hR
  have hw : ∀ w, evW YS v₀ j (hL ((j : ℕ) + 1) k P w) =
      ((((Rl.C.mu0 j).val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) •
        fun x => ∑ γ ∈ R, evW YS v₀ j w (x * γ) := by
    intro w
    have := hr α R hα hR' w
    exact congrArg (fun T => T (v₀ j _)) this
  have hmu : (((ρ.B i j b).mu0 z : Circle) : ℂ) = (((Rl.C.mu0 j).val P : ℂˣ) : ℂ) ^ k := by
    rw [hpin.mu0 i j b]
    refine GlobalTheory.HeckeDetChar.chi_detAt (hIs.mu0 j) (Q := Rl.Pg) ?_ ?_ ?_ hα hz
    · have := (hρ.base i j b).unram
      rwa [hpin.Pg i j b, hpin.mu0 i j b] at this
    · obtain ⟨Q, h1, -, h3⟩ := (hρ.base i j b).places.split
      exact hpin.Pg i j b ▸ h3.mono h1
    · have hA' : Rl.Sb = Rl.Pg := hA
      rw [← hA']; exact ho
  have hrk : (Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 g) x = _
  rw [e1]
  erw [evK_smul YS v₀ hρ i j b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k)]
  erw [evK_hkFR YS v₀ hρ i j b (hL ((j : ℕ) + 1)) hs k P R _ hw]
  have he : ρ.e i b ((algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k) = ρ.eO i b (u i b P) ^ k := by
    rw [map_pow]; rfl
  have hm : (((ρ.B i j b).mu z : Circle) : ℂ) =
      (((ρ.B i j b).mu0 z : Circle) : ℂ) * (((ρ.B i j b).de.chi z : Circle) : ℂ) := by
    rw [Base.mu, MonoidHom.mul_apply, Circle.coe_mul]
  have hr1 : ∀ y, realRd YS v₀ hρ i j b ν f y =
      ν⁻¹ * evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) y := fun _ => rfl
  have hq : normV P = Nat.card (Formalism.L2.DIV.kP P) := rfl
  simp only [hr1, Pi.smul_apply, smul_eq_mul, he, hδ', hm, hmu, hrk, hq]
  rw [← Finset.mul_sum]
  ring

theorem heckeRead_ysOf : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R cG kKs hk cf Rw low Pq hL eig θ Bs Sb v₀ ρ hρ hpin hIs hA hAd hSb i j b ν
  refine heckeRead_iff.2 fun k P hk' f => ?_
  refine heckeAt_of_scaledAt (ysOf Bs) v₀ hpin hIs hA hρ (HeckePinRead.isDeltaInv_uD hρ hpin) i j b ν
    (Bs.hs _ (Nat.le_add_left _ _) j.2) hk' ?_ ?_
  · intro α Rr hα hR x
    obtain ⟨hk1, hkr, hsp, hP⟩ := hk'
    have hd : HkDat R Sb j k P α Rr :=
      { split := hsp
        offS := fun h => hP (hSb i h)
        odd := fun h2 => hP (hρ.goodSetup_placesOverTwo_subset i h2)
        le := hkr
        elt := hα
        reps := hR }
    exact hkAd_step R Sb _ j (idxOf_succ D j) k P (hL ((j : ℕ) + 1) k P)
      (fun α' Rr' hd' x' => hAd ((j : ℕ) + 1) k P α' Rr' (Nat.le_add_left _ _) j.2 hd' x') α Rr hd x
  · have hu : Bs.cHk i b P = HeckePinRead.uD D i b P := by
      rw [Bs.cHk_del i b P hk'.2.2.2 (HeckePinRead.frobU D P) (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [← hu]
    exact Bs.hkEq i _ b (Nat.le_add_left _ _) j.2 k P f hk'.2.2.2 hk'.2.2.1 hk'.2.1

end GlobalTheory.HeightCounting.SerCopy

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepHeckeOperatorsNormalisedSumsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem _root_.GlobalTheory.T.secondStep_heckeOperators_normalisedSums : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good), RealPin R cG ρ → R.toRealDat.toLevCh.Is A3.A.μ0 → R.AllPlaces → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → ∀ i j b ν, HeckeRead (realRd (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ hρ i j b ν) := by
  first | exact @GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf | exact GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf | (intros; apply GlobalTheory.HeightCounting.SerCopy.heckeRead_ysOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLattices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.SerCopy

theorem ncard_eq_of_splits {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = p) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq E p hp fun P hP hpP => ?_
  have := hP.isPrime
  refine ⟨h ⟨P, hP.isPrime, fun h0 => ?_⟩ hpP, GlobalTheory.Mem.RaySplit.not_mem_sq hp hpP
    ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 hd P hP.isPrime hpP)⟩
  rw [h0] at hpP
  exact hp.ne_zero (by simpa using hpP)

theorem exists_preTie : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0) (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Rw : RowSide D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) hL eig θ (Bs : SideB D R.C Rw (lowAll D) Pq (ratDatR R cG kKs hk) hL eig θ) (Sb : Finset (PlE D.host)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW j σ).Vec) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → (∀ j, FWT.IsChosenExtremalVector R.toRealDat j (sg0 D A3.A) (v₀ j _)) → (∀ j : Fin D.R.m, (R.FW j).IsKsForm) → GlobalTheory.HeightCounting.SerCopy.HkAd R Sb hL → (∀ i, Sb ⊆ D.ntw.S0 i) → TauTrue Bs.exp → CharSide D R.C → ValLL0 D R.C → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → (∀ v, NG.OverPl (Pq v) v) → IsChoice (D := D) (Set.range Pq) → (∀ t, ∀ P ∈ R.Q t, P ∈ Set.range Pq) → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok) → (∀ j, FWT.VStd D j) → Nonempty (GlobalTheory.HeightCounting.SerCopy.PreTie (GlobalTheory.HeightCounting.SerCopy.ysOf Bs) v₀ Bs.exp hF Pq) := by
  intro hA D Γ _ _ Pl0 I0 T A3 Ks _ _ _ R F cG kKs hk Rw Pq hL eig θ Bs Sb v₀ hF pins intersectionNumber_baseChange hv hK hH hSb hτ cs hV hsp hPq hch hQ
    ⟨Z, hZ⟩ hstd
  have hC : R.Char3 F := RealDat3.characterisation_of_weak pins.char intersectionNumber_baseChange.aux.ex
  obtain ⟨p1, -, d1, n1⟩ := hZ.places.splits D.host.pde (by simp)
  obtain ⟨p2, -, d2, n2⟩ := hZ.places.splits D.host.pde' (by simp)
  have hq : ∀ p : ℕ, ¬ (p : ℤ) ∣ discr D.host.E → p ≠ D.host.q := fun p h e =>
    h (Int.natCast_dvd.2 (e ▸ SetupPin.q_dvd_discr D))
  have h2 : 2 ∈ lowAll D := by simp [lowAll, lowPr]
  have hd : (discr D.host.E).natAbs.primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hp)))
  have hc : (Ideal.absNorm D.host.ccK).primeFactors ⊆ lowAll D := fun p hp =>
    Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hp)))
  obtain ⟨ρ, hρ, hp, hlv, hρch, hbad⟩ := GlobalTheory.SeriesTie.ComplexCh.exists_setup_ch R cG F hC GlobalTheory.weilRepresentationUnitaryPair
    (SetupPin.goodSetup_badPlaces_conj _ Bs.tw) (SetupPin.goodSetup_placesOverTwo_subset _ Bs.tw h2) (SetupPin.goodSetup_count_eq_zero_off_badPlaces _ Bs.tw h2 hd hc)
    (SetupPin.exists_art_gal hA _ Bs.deltaRead) (SetupPin.mk_frac_Ok Bs.twF)
    ⟨ncard_eq_of_splits p1 d1 n1, ncard_eq_of_splits p2 d2 n2⟩ ⟨hq _ d1, hq _ d2⟩ (fun _ => Set.range Pq) (fun _ => hch)
    (fun i P ⟨t, h1, _⟩ => hQ t P h1)
  have hch' : ∀ i P, IsSplitPl D.host P → (P ∈ ρ.ch i ↔ P ∈ Set.range Pq) := fun i P _ => by rw [hρch]
  choose ν hν using fun i j b => exists_isScalar (ysOf Bs) v₀ hρ i j b
  have hFa : ∀ i j b, Faithful (realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) := fun i j b =>
    GlobalTheory.SeriesTie.realRd_faithful D _ _ _ _ _ _ R cG _ (ysOf Bs) v₀ ρ hρ i j b _ (hν i j b).ne intersectionNumber_baseChange.prim.unif hC.models.HW
      (hv j) (hK (idxOf D ((j : ℕ) + 1)))
  choose PV₀ hPV₀ _ using fun j => GlobalTheory.MtRead.exists_idFrame D hF j (hstd j)
  obtain ⟨rdV, hon, hjoin⟩ := GlobalTheory.MtRead.exists_reading hA D R.C Rw (lowAll D) Pq _ hL eig θ Bs hτ cs hV hsp hPq Γ Pl0 I0 T A3 Ks R F
    cG hC.lev rfl pins.keep hF PV₀ hPV₀ ρ hρ hp hlv hch'
  obtain ⟨Dat, th, lev, thPsi, h1, thU, thP, MtLat, g2, g3, -, t, ht⟩ := GlobalTheory.SeriesInstall.exists_tie_withSeries D ρ hρ
    (fun i j b => realRd (ysOf Bs) v₀ hρ i j b (ν i j b)) hFa hlv (GlobalTheory.SeriesTie.latFG_of_good D _ _ ρ hρ) rdV hon
  refine ⟨{
    Dat := Dat, th := th, lev := lev, thPsi := thPsi, h1 := h1, thU := thU, thP := thP, MtLat := MtLat, h2 := g2, h3 := g3
    ρ := ρ, good := hρ, pin := hp, vec := hv, ν := ν, scalar := hν, tie := t
    hecke := fun i j b => (heckeRead_iff_tie.1 (GlobalTheory.T.secondStep_heckeOperators_normalisedSums D Γ Pl0 I0 T A3 Ks R cG kKs hk R.C Rw (lowAll D) Pq hL eig θ Bs Sb v₀
      ρ hρ hp hC.lev hC.allPl hH hSb i j b (ν i j b))).1
    bad := hbad, ch := hch'
    join := fun PV hPV i j b k Q ψ hAd hT => ?_ }⟩
  obtain ⟨ω, hω, he⟩ := hjoin i j b k Q ψ hAd hT
  refine ⟨ω, hω, fun f g => ?_⟩
  rw [← he f g, GlobalTheory.T.finiteHom_eq_of_frames_keep_matrices D _ _ hF (PV j) (PV₀ j) (hPV j) (hPV₀ j) g]
  exact congrFun (congrArg (fun r => r k Q ψ f) (ht i j b)) _

end GlobalTheory.HeightCounting.SerCopy
end
end
