module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstructedCoreOfAllConstructionStagesStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSingleSingle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.BitVec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KsCondExact
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsDiscriminantTwelfthRootOfIdealLatticeIffDelta1
import Development.AbelianVarietyTheory.Definitions.Foundations.ValuedAlgebraMapEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPinned

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpacesNormHasFrame

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.DiagSp

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem signSpace_cut_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N N' p q : ℕ)
    (hN : N = N') (hp : p ≤ N) (hq : N - p = q) :
    signSpace hstar N (cut N p) = stdSpace hstar N' (fun i => decide (p ≤ i.1)) p q := by
  subst hN hq
  rw [signSpace, card_cut_false N p hp, card_cut_true N p hp]
  rfl

theorem signSpace_false_eq (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) :
    signSpace hstar N (fun _ => false) = stdSpace hstar N (fun _ => false) N 0 := by
  simp [signSpace]

def planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (a b : E) (i : Fin h) : Fin N → E :=
  Pi.single (⟨n + i, by omega⟩ : Fin N) a + Pi.single (⟨n + h + i, by omega⟩ : Fin N) b

theorem planeVec_planeVec (N n h p : ℕ) (hN : n + 2 * h ≤ N) (hp : p = n + h) (a b c d : E) (i j : Fin h) :
    diagForm N (cut N p) (planeVec N n h hN a b i) (planeVec N n h hN c d j) =
      if i = j then star a * c - star b * d else 0 := by
  subst hp
  have hi := i.isLt
  have hj := j.isLt
  have c1 : cut N (n + h) ⟨n + i, by omega⟩ = false := by simp [cut]
  have c2 : cut N (n + h) ⟨n + h + i, by omega⟩ = true := by simp [cut]
  simp only [planeVec, map_add (f := _), LinearMap.add_apply, diag_single_single, c1, c2]
  have e1 : ¬ (n + (i : ℕ) = n + h + j) := by omega
  have e2 : ¬ (n + h + (i : ℕ) = n + j) := by omega
  rw [if_neg e1, if_neg e2]
  by_cases hij : i = j
  · subst hij
    simp [sgn, sub_eq_add_neg]
  · have h' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
    have e3 : ¬ (n + (i : ℕ) = n + j) := by omega
    have e4 : ¬ (n + h + (i : ℕ) = n + h + j) := by omega
    rw [if_neg e3, if_neg e4, if_neg hij]
    simp

theorem ext_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (x : Fin n → E) (a b : E)
    (i : Fin h) : diagForm N neg (extTo n N x) (planeVec N n h hN a b i) = 0 := by
  rw [planeVec, map_add (f := _), diag_ext_single, diag_ext_single, add_zero]
  · simp only; omega
  · simp only; omega

theorem single_planeVec (N n h : ℕ) (hN : n + 2 * h ≤ N) (neg : Fin N → Bool) (l : Fin N)
    (hl : n + 2 * h ≤ l) (c a b : E) (i : Fin h) :
    diagForm N neg (Pi.single l c) (planeVec N n h hN a b i) = 0 := by
  have hi := i.isLt
  rw [planeVec, map_add (f := _), diag_single_single, diag_single_single, if_neg, if_neg, add_zero]
  · simp only; omega
  · simp only; omega

end General

section Main

variable (R : Ranks)

theorem rankY_eq_N_add (j : ℕ) (hj : j < R.m) : R.rankY j = R.N j + (R.m - 1 - j) := by
  simp only [Ranks.rankY, Ranks.r, Ranks.N, mul_add]
  omega

theorem pY_eq_N_add (j : ℕ) (hj : j < R.m) : pY R j = R.N j + (R.m - 1 - j) / 2 := by
  have := rankY_eq_N_add R j hj
  simp only [pY]
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)

include hpz in
theorem top_line_norm :
    diagForm (R.N R.m) (fun _ => false)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz)
      (Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz) = (T : E) := by
  refine (diag_single_single _ (fun _ => false) _ _ pz pz).trans ?_
  rw [if_pos rfl, ← hpz]
  simp [sgn]

def spacesNorm : Spaces R F E :=
  { spacesStd R cm T hT pz hpz (fun _ => false) with
    z := Pi.single (⟨R.rankY R.m, by rw [N_top]; omega⟩ : Fin (R.N R.m)) pz
    z_anis := ne_of_eq_of_ne (top_line_norm R T pz hpz) (Nat.cast_ne_zero.2 hT.ne_zero)
    z_orth := fun x => diag_ext_single _ _ (fun _ => false) x _ pz le_rfl }

theorem spacesNorm_z_norm :
    ((spacesNorm R cm T hT pz hpz).X R.m).hT (spacesNorm R cm T hT pz hpz).z (spacesNorm R cm T hT pz hpz).z =
      ((spacesNorm R cm T hT pz hpz).T : E) :=
  top_line_norm R T pz hpz

theorem spacesNorm_hasFrame (j : ℕ) (hj : j < R.m) : HasHyperbolicAuxiliaryFrame (spacesNorm R cm T hT pz hpz) j := by
  have h1 := rankY_eq_N_add R j hj
  have h2 := pY_eq_N_add R j hj
  have hN : R.N j + 2 * ((R.m - 1 - j) / 2) ≤ R.rankY j := by omega
  refine ⟨planeVec _ _ _ hN (1 : E) 1, planeVec _ _ _ hN (1 / 2 : E) (-(1 / 2)),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans (by simp),
    fun i i' => (planeVec_planeVec _ _ _ _ hN h2 _ _ _ _ i i').trans ?_,
    fun i x => ⟨ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i, ext_planeVec _ _ _ hN (cut _ (pY R j)) x _ _ i⟩,
    fun he => ?_⟩
  · split_ifs
    · rw [star_one]; norm_num
    · rfl
  · obtain ⟨a, ha⟩ := he
    obtain ⟨b, hb⟩ := R.m_even
    have hl : R.N j + 2 * ((R.m - 1 - j) / 2) < R.rankY j := by omega
    refine ⟨(Pi.single (⟨_, hl⟩ : Fin (R.rankY j)) pz : Fin (R.rankY j) → E), ?_,
      fun x => diag_ext_single _ _ (cut _ (pY R j)) x _ pz (Nat.le_add_right _ _),
      fun i => ⟨single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i,
        single_planeVec _ _ _ hN (cut _ (pY R j)) _ le_rfl _ _ _ i⟩⟩
    refine (diag_single_single _ (cut _ (pY R j)) _ _ pz pz).trans ?_
    have c : cut (R.rankY j) (pY R j) ⟨_, hl⟩ = true := by
      simp only [cut, decide_eq_true_eq]; omega
    rw [if_pos rfl, c]
    change _ = -(T : E)
    rw [← hpz]
    simp [sgn]

theorem spacesNorm_coord :
    ∃ hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x),
      (∀ j, (spacesNorm R cm T hT pz hpz).X j = posSpace hstar (R.N j)) ∧
      (spacesNorm R cm T hT pz hpz).X' = posSpace hstar R.rankX' ∧
      (∀ j, (spacesNorm R cm T hT pz hpz).Y j =
        stdSpace hstar (R.rankY j) (fun i => decide ((sigYD R j).1 ≤ i.1)) (sigYD R j).1 (sigYD R j).2) ∧
      (∀ j, 1 ≤ j → j ≤ R.m → (spacesNorm R cm T hT pz hpz).W j =
        stdSpace hstar R.r (fun i => decide ((R.sigW j).1 ≤ i.1)) (R.sigW j).1 (R.sigW j).2) ∧
      ∀ j, (spacesNorm R cm T hT pz hpz).V j =
        stdSpace hstar R.nV (fun _ => (spacesNorm R cm T hT pz hpz).Vneg j)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then 0 else R.nV)
          (if (spacesNorm R cm T hT pz hpz).Vneg j then R.nV else 0) := by
  refine ⟨star_isIntegral, fun _ => rfl, rfl, fun j => ?_, fun j h1 h2 => ?_, fun j => ?_⟩
  · exact signSpace_cut_eq _ _ _ _ _ rfl (Nat.sub_le _ _) (sub_pY R j)
  · have h : R.rankY 0 = R.k + R.m - 1 := by simp [Ranks.rankY, Ranks.r]
    refine signSpace_cut_eq _ (R.rankY 0) R.r (R.k + j - 1) (R.m - j) h ?_ ?_ <;> omega
  · exact signSpace_false_eq _ _

theorem spacesNorm_Y_sig (j : ℕ) (τ : E →+* ℂ) : ((spacesNorm R cm T hT pz hpz).Y j).sig τ = sigYD R j :=
  spY_sig R j τ

end Main

end GlobalTheory.Mem.DiagSp

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages

section

@[expose] public section

noncomputable section

namespace GlobalTheory.StdFrameObj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.FWT GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_piT_mul {P : PreCh} (L : LevCh P) :
    (star (L.piT P.u₀ : L.host.E) : L.host.E) * (L.piT P.u₀ : L.host.E) = (L.T P.u₀ : L.host.E) := by
  have h : (star (L.piT P.u₀ : L.host.E) : L.host.E) = L.host.conj (L.piT P.u₀ : L.host.E) :=
    bridge_star_holds P.R L.host _
  rw [h, mul_comm]
  exact L.piT_norm _

def coordPre (P : PreCh) (L : LevCh P) : Pre :=
  Pre.ofCh P L (DiagSp.spacesNorm P.R (host_cmData P.R L.host) (L.T P.u₀) (L.T_prime _) _ (star_piT_mul L)) rfl
    (fun j _ τ => DiagSp.spacesNorm_Y_sig _ _ _ _ _ _ j τ)
    (fun j _ hj => DiagSp.spacesNorm_hasFrame _ _ _ _ _ _ j hj) (fun _ _ _ => rfl)
    (DiagSp.spacesNorm_z_norm _ _ _ _ _ _)

theorem diagSpaces_coordPre (P : PreCh) (L : LevCh P) : DiagSpaces (coordPre P L).sp :=
  DiagSp.spacesNorm_coord _ _ _ _ _ _

end GlobalTheory.StdFrameObj

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PinsCoordPre

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.PinsCoord

theorem extTo_basis {E : Type} [Field E] (n N : ℕ) (a : Fin n) (b : Fin N) (h : (a:ℕ) = b) : DiagSp.extTo (E := E) n N (Pi.basisFun E (Fin n) a) = Pi.basisFun E (Fin N) b := by
  funext i
  simp only [Pi.basisFun_apply]
  show (if h : (i:ℕ) < n then (Pi.single a (1:E) : Fin n → E) ⟨i, h⟩ else 0) = _
  by_cases e : i = b
  · subst e
    have : (i:ℕ) < n := h ▸ a.2
    rw [dite_eq_left this, show (⟨i, this⟩ : Fin n) = a from Fin.ext h.symm]; simp
  · rw [Pi.single_eq_of_ne e]
    split_ifs with h1
    · exact Pi.single_eq_of_ne (fun e' => e (Fin.ext (by rw [← h, ← e']))) _
    · rfl

end GlobalTheory.Mem.Col2.PinsCoord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrePin

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld

namespace GlobalTheory.Mem.Top.Bl.KPxCond

theorem exists_prePin (K : Ctx) : ∃ P : Pre, K.Over P ∧ PrePin P :=
  ⟨GlobalTheory.StdFrameObj.coordPre K.P K.Lv, ⟨_, _, _, _, _, _, rfl, GlobalTheory.StdFrameObj.diagSpaces_coordPre K.P K.Lv⟩,
    fun a b h => PinsCoord.extTo_basis _ _ a b h⟩

theorem baseCond_KPx : RayField → PrincipalIdealSt → CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM → BaseCond KPx := by
  intro hR hP hA h2b
  exact baseCond_of (PP := fun P _ => PrePin P) (GlobalTheory.Mem.KsExactCond.ksCond_exact hR hP hA)
    (EvG.imp (evG_of_ev (ev_preX_frame h2b)) fun K _ _ _ _ hfr => by
      obtain ⟨P, hO, hp⟩ := exists_prePin K
      obtain ⟨f⟩ := (hfr P hO).2
      exact ⟨P, f, hO, hp⟩)

end GlobalTheory.Mem.Top.Bl.KPxCond
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PassStepCongr

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem pass_step_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem pass_step : ∀ (KP : BaseP) (Q : V4.Slot) (r r' : AtP), BaseCond KP → Pass KP Q r → Step KP r r' → Pass KP Q r' := by
  classical
  intro KP Q r r' hK hR hS
  refine (EvG.inter hS hR).imp fun K _ _ _ _ H => ?_
  obtain ⟨hs, hr⟩ := H
  have hs' : large₂ K fun B f T => KP B f → r K B f T → r' K B f T :=
    (hs.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hr.inter hb).imp ?_
  rintro B f T hO ⟨hr, h₁, hp⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hr'⟩ := hr hKP hT C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have r'' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, pass_step_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, pass_step_congr P₁ hP hf, hpl]; exact hp)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, pass_step_congr A₀ hP hf] at hA; exact hA)))
    (hK.enl B B' f f' e hf hKP) hr'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), r''⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberOfConstructionStepsSecondPass

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.MemberEx2

theorem step_start (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ B _ T => T = TwDat.untw B T.pl) (fun K B f T => ∃ w : ColW B f T, Start K B f T w) :=
  (Step.and (Step.of_all fun _ _ _ _ _ _ _ h => h)
      ((Step.of_all fun _ _ _ _ _ _ _ _ => trivial).trans (PinW.step_pinned h2b))).trans
    (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨w, hw⟩ := H.2
      ⟨w, hw, supp_of_untw w H.1, coh_of_untw H.1⟩)

theorem stepW_builtE {𝒮 : Slots} {p : WP} (hp : ∀ K B f T w, p K B f T w → Pinned K B f T w)
    (h4 : StepW (pinAnd (Has3 𝒮)) (Has4 𝒮)) (hc : StepW (pinAnd (Has4 𝒮)) (HasC (BuiltE 𝒮)))
    (h3 : StepW p (Has3 𝒮)) : StepW p (HasC (BuiltE 𝒮)) :=
  have q : StepW p Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => hp _ _ _ _ _ h
  (q.and ((q.and h3).trans h4)).trans hc

end GlobalTheory.Mem.Top.Bl.MemberEx2

namespace GlobalTheory.Mem.Top.Bl

theorem memberE_of_steps2 : GlobalTheory.NT.RayField → GlobalTheory.Published.PrincipalIdealSt → GlobalTheory.Published.CMCurveGoodOutsidePrimeSt → StandardLattice.SiegelMassRatioCM →
    ∀ 𝒮 𝒮' : Slots, StepW Start (Has3 𝒮) → StepW (pinAnd (Has3 𝒮)) (Has4 𝒮) → AmbEx 𝒮 → DivEx 𝒮 → ThEx 𝒮 →
      ExportF KPx (IsBuiltE 𝒮) →
      Pass KPx (IsBuiltE 𝒮) (fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w) →
      StepW (pinAnd (Has3 𝒮')) (Has4 𝒮') → AmbEx 𝒮' → DivEx 𝒮' → ThEx 𝒮' →
      (∀ K B f T w Z c, BuiltE 𝒮' K B f T w Z c → GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) → MemberE 𝒮 := by
  intro hR hP hC h2b 𝒮 𝒮' h3 h4 hA hD hT hE hPass h4' hA' hD' hT' hL
  have hB : BaseCond KPx := KPxCond.baseCond_KPx hR hP hC h2b
  have h1 : FirstG KPx (IsBuiltE 𝒮) :=
    step_hasCore (MemberEx2.step_start h2b)
      (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1) h4 (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮 hA hD hT) h3)
  have hW : StepW (fun K B f T w => Start K B f T w ∧ Has3 𝒮' K B f T w)
      (HasC fun K B f T w Z c => GoodE 𝒮 K B f T w Z c ∧ DQ.TwAllAt (w.D Z) c.O.nch c.O.xd) :=
    (MemberEx2.stepW_builtE (fun _ _ _ _ _ h => h.1.1) h4' (GlobalTheory.T.exists_constructedCore_of_all_construction_stages h2b 𝒮' hA' hD' hT')
      (StepW.of_all fun _ _ _ _ _ _ _ h => h.2)).trans
      (StepW.of_all fun _ _ _ _ _ _ _ H => let ⟨Z, c, hc⟩ := H; ⟨Z, c, hL _ _ _ _ _ _ _ hc⟩)
  have hS := step_hasCore (admitted := fun K B f T => ∃ w : ColW B f T, Start K B f T w ∧ Has3 𝒮' K B f T w)
    (Step.of_all fun _ _ _ _ _ _ _ h => h) hW
  have h2 : SecondG KPx (IsBuiltE 𝒮) (IsGoodE 𝒮) :=
    GlobalTheory.Mem.Top.GroupRetwisting.pass_step KPx _ _ _ hB hPass (hS.trans (Step.of_all fun _ _ _ _ _ _ _ H =>
      let ⟨C, W, V, S, N, G, c, hc⟩ := H
      ⟨C, W, V, S, N, G, c, positionOf_ind (R := fun K X f T c => IsBuiltE 𝒮 K X f T c ∧ DQ.TwAllAt X.toD7 c.O.nch c.O.xd ∧
        IsGoodE 𝒮 K X f T c) (fun _ _ _ _ _ _ _ h => ⟨positionOf_intro h.1.1, h.2, positionOf_intro h.1⟩) hc⟩))
  exact ⟨hB, h1, hE, h2⟩

end GlobalTheory.Mem.Top.Bl

end
end
end
