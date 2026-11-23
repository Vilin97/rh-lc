module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlace
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevDatYZero
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIndexZeroLevelElementGivenReductionAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → ∀ (PP : cm.Pg) (x : (G PP).S.P.J), ∃ m ∈ levS (c.V 0) st.β st.L, Q m ∧ (∀ hr : D.R.r ≤ (c.V 0).rank, GlobalTheory.LevZero.Red (G PP) PP.1 x (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) m)))) ∧ ∀ PP' ∈ cm.Pg, PP' ≠ PP.1 → redFn st.β PP' (finE (c.V 0) m) = 1 := by
  first | exact @GlobalTheory.LevZeroPlace.one_place | exact GlobalTheory.LevZeroPlace.one_place | (intros; apply GlobalTheory.LevZeroPlace.one_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroInd

theorem redFn_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) (hy : y ∈ St β) : redFn β PP (x * y) = redFn β PP x * redFn β PP y := by
  unfold redFn ext1
  rw [dite_eq_left (mul_mem hx hy), dite_eq_left hx, dite_eq_left hy]
  rw [← map_mul]
  congr 1

theorem redFn_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ St β) : redFn β PP x⁻¹ = (redFn β PP x)⁻¹ := by
  unfold redFn ext1
  rw [dite_eq_left (inv_mem hx), dite_eq_left hx]
  rw [← map_inv]
  congr 1

theorem reductionBlock_injective_of_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n = r) :
    Function.Injective (upperLeftBlock (κ := κ) hr) := by
  subst hn
  intro a b h
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

end GlobalTheory.LevZeroInd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfRhoLt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevZeroUniq
open GlobalTheory.SplitWeil GlobalTheory.StepData

variable {D : D7} {c : Comm D} {v : VCom c} {PP : Formalism.L2.DIV.Pl D.host.E}

def rho (G : GLoc v) : 𝓞 D.host.E →+* G.k := (G.q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem rho_apply (G : GLoc v) (z : 𝓞 D.host.E) : rho G z = (ofSplit G.q).pr (z : D.host.E) := rfl

theorem rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E} (hz : z ∈ PP.asIdeal) :
    valuation G.k (rho G z) < 1 := by
  by_cases h0 : z = 0
  · subst h0; simp
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  have h1 := (hid.2 z h0).1 hz
  rw [← G.q.sec_pr, ← G.q.int_iff] at h1
  change (G.q.pr.comp (incA D)) _ ∉ _ at h1
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le] at h1
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).1 h1

theorem mem_of_rho_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {z : 𝓞 D.host.E}
    (hz : valuation G.k (rho G z) < 1) : z ∈ PP.asIdeal := by
  by_cases h0 : z = 0
  · subst h0; exact zero_mem _
  have h0' : rho G z ≠ 0 := (map_ne_zero (G.q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 h0)
  refine (hid.2 z h0).2 ?_
  rw [← G.q.sec_pr, ← G.q.int_iff]
  change (G.q.pr.comp (incA D)) _ ∉ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact (one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0'))).2 hz

def out (y : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E := Function.surjInv (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem mk_out (y : Formalism.L2.DIV.kP PP) : Ideal.Quotient.mk PP.asIdeal (out y) = y :=
  Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := PP.asIdeal)) y

theorem rho_sub_lt (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {y : Formalism.L2.DIV.kP PP} {z : 𝓞 D.host.E}
    (hz : Ideal.Quotient.mk PP.asIdeal z = y) : valuation G.k (rho G (out y) - rho G z) < 1 := by
  rw [← map_sub]
  refine rho_lt G hid (Ideal.Quotient.eq.1 ?_)
  rw [mk_out, hz]

def pos (G : GLoc v) : Fin D.R.k ⊕ Fin (G.s + 1) ≃ Fin D.R.r :=
  finSumFinEquiv.trans (finCongr (by have := G.hs; unfold Ranks.r; omega))

theorem pos_val (G : GLoc v) (a : Fin D.R.k ⊕ Fin (G.s + 1)) : (pos G a).val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a := by
  rcases a with a | a <;> rfl

def lift (G : GLoc v) (g : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) G.k :=
  fun a b => rho G (out (g (pos G a) (pos G b)))

theorem lift_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) :
    MaxM (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) := by
  intro a b
  have e : (lift G (1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) - 1) a b =
      rho G (out ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP)) (pos G a) (pos G b))) -
      rho G (if a = b then 1 else 0) := by
    simp only [Matrix.sub_apply, lift, Matrix.one_apply]
    split_ifs <;> simp
  rw [e]
  refine rho_sub_lt G hid ?_
  simp only [Matrix.one_apply, (pos G).injective.eq_iff]
  split_ifs <;> simp

theorem red_iff (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) (x : G.S.P.J) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)) :
    GlobalTheory.LevZero.Red G PP x g ↔ MaxM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) := by
  constructor
  · intro h a b
    have := h a b (pos G a) (pos G b) (pos_val G a) (pos_val G b) _ (mk_out _)
    simpa only [Matrix.sub_apply, lift, rho_apply] using this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = pos G a := Fin.ext (ha.trans (pos_val G a).symm)
    obtain rfl : b' = pos G b := Fin.ext (hb.trans (pos_val G b).symm)
    have e : (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E) =
        ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - lift G g.val) a b + (rho G (out (g.val (pos G a) (pos G b))) - rho G z) := by
      simp only [Matrix.sub_apply, lift, rho_apply]; ring
    rw [e]
    exact Valuation.map_add_lt _ (h a b) (rho_sub_lt G hid hz)

theorem intM_J (G : GLoc v) (x : G.S.P.J) : IntM (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val ∧
    IntM ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹).val :=
  mem_KO.1 (G.S.P.le_KO x.2)

theorem red_one (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) : GlobalTheory.LevZero.Red G PP 1 1 := by
  rw [red_iff G hid]
  have := (lift_one G hid).neg
  simpa using this

theorem red_uniq (G : GLoc v) (hid : Formalism.L2.NTheta.IsIdemAt G.q.e PP) {x x' : G.S.P.J} {g g' : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)}
    (hx : GlobalTheory.LevZero.Red G PP x g) (hx' : GlobalTheory.LevZero.Red G PP x' g')
    (hk : x.1⁻¹ * x'.1 ∈ KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) : g = g' := by
  rw [red_iff G hid] at hx hx'
  set X := (x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX
  set X' := (x' : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k) with hX'
  have h1 : MaxM ((X⁻¹ * X').val - 1) := mem_KOne.1 hk
  have h2 : MaxM (lift G g'.val - lift G g.val) := by
    have e : lift G g'.val - lift G g.val =
        (X.val - lift G g.val) + -(X'.val - lift G g'.val) + X.val * ((X⁻¹ * X').val - 1) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
        Matrix.mul_one]
      abel
    rw [e]
    exact (hx.add hx'.neg).add ((intM_J G x).1.mul_maxM h1)
  refine Units.ext (Matrix.ext fun a' b' => ?_)
  obtain ⟨a, rfl⟩ := (pos G).surjective a'
  obtain ⟨b, rfl⟩ := (pos G).surjective b'
  have h3 : valuation G.k (rho G (out (g'.val (pos G a) (pos G b)) - out (g.val (pos G a) (pos G b)))) < 1 := by
    rw [map_sub]; simpa only [Matrix.sub_apply, lift] using h2 a b
  have h4 := Ideal.Quotient.eq.2 (mem_of_rho_lt G hid h3)
  rw [mk_out, mk_out] at h4
  exact h4.symm

end GlobalTheory.LevZeroUniq

theorem GlobalTheory.LevZeroUniq.main : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → GlobalTheory.LevZero.Red G PP 1 1 ∧ ∀ (x x' : G.S.P.J) (g g' : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → GlobalTheory.LevZero.Red G PP x' g' → x.1⁻¹ * x'.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1)) → g = g' := by
  intro D c v G PP hid
  exact ⟨GlobalTheory.LevZeroUniq.red_one G hid, fun x x' g g' hx hx' hk => GlobalTheory.LevZeroUniq.red_uniq G hid hx hx' hk⟩

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevZeroInd in

theorem GlobalTheory.LevZero.gen : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  intro D c v cm st b G h0 hB Q hmul hN hU hred
  classical
  have hst := hB.mem
  obtain ⟨hr, ξ, hL⟩ := hst.lev
  have hn : (c.V 0).rank = D.R.r := by rw [hst.rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have key := fun x => GlobalTheory.LevYZero.lev_datY_zero (c.V 0) st.β st.L D.R.r D.R.t hr hn cm.Pg cm.P cm.chi ξ hL
    (Lev.finE (c.V 0) x) (GlobalTheory.LevSplit.finE_mem_UA _ x)
  have hSt : ∀ x ∈ levS (c.V 0) st.β st.L, Lev.finE (c.V 0) x ∈ St st.β := fun x hx => ((key x).1.1 hx.2).1
  have hRed : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ PP : cm.Pg, ∃ z, GlobalTheory.LevZero.Red (G PP) PP.1 z (upperLeftBlock hr (redFn st.β PP.1 (Lev.finE (c.V 0) x))) :=
    fun x hx PP => (hB.grp _).1 ((key x).1.1 hx.2).2 PP
  have hmulm : ∀ x ∈ levS (c.V 0) st.β st.L, ∀ y ∈ levS (c.V 0) st.β st.L, x * y ∈ levS (c.V 0) st.β st.L :=
    fun x hx y hy => Subgroup.mul_mem _ hx hy
  have hinvm : ∀ x ∈ levS (c.V 0) st.β st.L, x⁻¹ ∈ levS (c.V 0) st.β st.L := fun x hx => Subgroup.inv_mem _ hx
  have claim : ∀ s : Finset (Pl D.host.E), ∀ k ∈ levS (c.V 0) st.β st.L,
      (∀ PP ∈ cm.Pg, PP ∉ s → redFn st.β PP (Lev.finE (c.V 0) k) = 1) → Q k := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro k hk h
      exact hred k hk fun PP hPP => h PP hPP (Finset.notMem_empty _)
    · intro a s ha ih k hk h
      by_cases haP : a ∈ cm.Pg
      · obtain ⟨z, hz⟩ := hRed k hk ⟨a, haP⟩
        obtain ⟨m, hm0, hQm, hmr, hmo⟩ := GlobalTheory.T.exists_indexZeroLevel_element_given_reduction_at_place cm st b G h0 hB Q hmul hN hU ⟨a, haP⟩ z
        have e1 : redFn st.β a (Lev.finE (c.V 0) m) = redFn st.β a (Lev.finE (c.V 0) k) :=
          reductionBlock_injective_of_eq hr hn ((GlobalTheory.LevZeroUniq.main (G ⟨a, haP⟩) a (hB.loc ⟨a, haP⟩).idem).2 z z _ _ (hmr hr) hz
            (by rw [inv_mul_cancel]; exact one_mem _))
        have hk1 : m⁻¹ * k ∈ levS (c.V 0) st.β st.L := hmulm _ (hinvm m hm0) k hk
        have hred1 : ∀ PP, redFn st.β PP (Lev.finE (c.V 0) (m⁻¹ * k)) =
            (redFn st.β PP (Lev.finE (c.V 0) m))⁻¹ * redFn st.β PP (Lev.finE (c.V 0) k) := fun PP => by
          rw [map_mul, map_inv, redFn_mul _ _ (inv_mem (hSt m hm0)) (hSt k hk), redFn_inv _ _ (hSt m hm0)]
        have hQ1 := ih (m⁻¹ * k) hk1 fun PP hPP hPs => by
          rw [hred1]
          by_cases hPa : PP = a
          · subst hPa
            rw [e1, inv_mul_cancel]
          · rw [hmo PP hPP hPa, h PP hPP (by simp [hPa, hPs]), inv_one, one_mul]
        have := hmul m hm0 _ hk1 hQm hQ1
        simpa using this
      · exact ih k hk fun PP hPP hPs => h PP hPP (by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun e => haP (e ▸ hPP), hPs⟩)
  intro k hk
  exact claim cm.Pg k hk fun PP hPP h => absurd hPP h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotentsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.indexZeroLevel_generated_by_local_unipotents : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ Q : GA D (c.V 0) → Prop, (∀ k ∈ levS (c.V 0) st.β st.L, ∀ k' ∈ levS (c.V 0) st.β st.L, Q k → Q k' → Q (k * k')) → (∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (c.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * n * b)) → (∀ x ∈ GfC (c.X 0), b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b ∈ levS (c.V 0) st.β st.L → Q (b⁻¹ * embA (c.bes 0 D.R.rS h0).d (c.bes 0 D.R.rS h0).o x * b)) → (∀ k ∈ levS (c.V 0) st.β st.L, (∀ PP ∈ cm.Pg, redFn st.β PP (finE (c.V 0) k) = 1) → Q k) → ∀ k ∈ levS (c.V 0) st.β st.L, Q k := by
  first | exact @GlobalTheory.LevZero.gen | exact GlobalTheory.LevZero.gen | (intros; apply GlobalTheory.LevZero.gen <;> assumption)
end
end
