module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EntInSandwich
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxClose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCong
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMain

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxFin

section

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Code

theorem relIndex_ne_zero_of_code {G : Type*} [Group G] (H A : Subgroup G) {Q : Type*} [Finite Q] (φ : A → Q)
    (hφ : ∀ k k' : A, φ k = φ k' → ((k⁻¹ * k' : A) : G) ∈ H) : H.relIndex A ≠ 0 := by
  classical
  have hfin : Finite (A ⧸ H.subgroupOf A) := by
    choose rep hrep using fun v : Set.range φ => v.2
    refine Finite.of_surjective (fun v : Set.range φ => (QuotientGroup.mk (rep v) : A ⧸ H.subgroupOf A)) ?_
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      refine ⟨⟨φ k, k, rfl⟩, ?_⟩
      show (QuotientGroup.mk (rep ⟨φ k, k, rfl⟩) : A ⧸ H.subgroupOf A) = QuotientGroup.mk k
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact hφ _ _ (hrep _)
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end Code

section Fin

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem R_sub_O {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ (M p).R) : x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  revert hx
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R → _
  rcases hM : (M p).split with _ | g
  · intro hx
    have : x ∈ (M p).L.O := hx
    rwa [hO] at this
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      intro hx
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split] at hx
      rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1]
      exact ⟨hx.1, hx.2.1⟩

def dO {p : PlF D} (c : (D.s.atP p).Fp) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).O :=
  ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c, alg_mem_O hc⟩

theorem finite_quot {p : PlF D} (hA : Agree δ M p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    Finite ((D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) := by
  obtain ⟨hOK, -, -, hO, -, -⟩ := hA
  have := hOK.loc
  have := hOK.char0
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  obtain ⟨hOo, hOc, -⟩ := Formalism.MainNotions.LocalModelPeriodLattices.O_top (M p).L
  rw [hO] at hOo hOc
  have : CompactSpace (D.s.atP p).O := isCompact_iff_compactSpace.1 hOc
  have hc' : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have hopen : IsOpen (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) := by
    have h1 : (((Ideal.span {dO c hc}).toAddSubgroup : AddSubgroup (D.s.atP p).O) : Set (D.s.atP p).O) =
        (fun y : (D.s.atP p).O => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep)) ⁻¹'
          ((D.s.atP p).O : Set (D.s.atP p).Ep) := by
      ext y
      simp only [Submodule.coe_toAddSubgroup, SetLike.mem_coe, Set.mem_preimage]
      rw [Ideal.mem_span_singleton']
      constructor
      · rintro ⟨z, rfl⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * ((z : (D.s.atP p).Ep) * algebraMap _ _ c) ∈ (D.s.atP p).O
        rw [mul_comm (z : (D.s.atP p).Ep), ← mul_assoc, hc', one_mul]
        exact z.2
      · intro hy
        refine ⟨⟨_, hy⟩, Subtype.ext ?_⟩
        show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep c⁻¹ * (y : (D.s.atP p).Ep) * algebraMap _ _ c = y
        rw [mul_comm, ← mul_assoc, mul_comm (algebraMap _ _ c), hc', one_mul]
    rw [h1]
    exact hOo.preimage (by fun_prop)
  exact AddSubgroup.quotient_finite_of_isOpen _ hopen

theorem quot_eq {p : PlF D} {c : (D.s.atP p).Fp} {hc : c ∈ 𝒪[(D.s.atP p).Fp]} {x y : (D.s.atP p).O}
    (h : (QuotientAddGroup.mk x : (D.s.atP p).O ⧸ (Ideal.span {dO c hc}).toAddSubgroup) = QuotientAddGroup.mk y) :
    (y : (D.s.atP p).Ep) - x ∈ latS (D.s.atP p) c := by
  rw [QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  refine mem_latS.2 ⟨z, z.2, ?_⟩
  have := congrArg Subtype.val hz
  simp only [Subring.coe_mul, Subring.coe_add, Subring.coe_neg] at this
  rw [show (y : (D.s.atP p).Ep) - x = -x + y by ring, ← this]
  show (z : (D.s.atP p).Ep) * algebraMap _ _ c = _
  ring

theorem entIn_int_mul {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (B * X) :=
  entIn_mul (J1 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => O_mul_latS hx hy) (fun i j => hB i j) hX

theorem entIn_mul_int {p : PlF D} {c : (D.s.atP p).Fp} {B X : ProdE.MP p} (hB : ∀ i j, B i j ∈ (D.s.atP p).O)
    (hX : EntIn (latS (D.s.atP p) c) X) : EntIn (latS (D.s.atP p) c) (X * B) :=
  entIn_mul (J2 := (D.s.atP p).O.toAddSubgroup) (fun x hx y hy => by rw [mul_comm]; exact O_mul_latS hy hx) hX
    (fun i j => hB i j)

end Fin

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinIdxAt

section

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))


theorem finIdx_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    (ProdE.CPL M δ u u' w hA L U hL hU).relIndex (ProdE.AP M δ u u' w p) ≠ 0 ∧
      (ProdE.AP M δ u u' w p).relIndex (ProdE.CPL M δ u u' w hA L U hL hU) ≠ 0 := by
  classical
  obtain ⟨c0, hc00, hc0O, hcong⟩ := cong_at M δ u u' w hA L U hL hU
  set Lp := lOf δ M p L U with hLpd
  set Lpi := lOf δ M p L⁻¹ U⁻¹ with hLpid
  set Up := ρOf δ M p L U with hUpd
  set Upi := ρOf δ M p L⁻¹ U⁻¹ with hUpid
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by rw [hLpd, hLpid, ← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hLL' : Lpi * Lp = 1 := ProdE.lp_inv M δ hA L U hL hU
  have hUU : Up * Upi = 1 := ProdE.up_inv M δ hA L U hL hU
  have hUU' : Upi * Up = 1 := by rw [hUpd, hUpid, ← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  have hRO : ∀ {x : (D.s.atP p).Ep}, x ∈ (M p).R → x ∈ (D.s.atP p).O := fun hx => R_sub_O M δ hA hx
  refine ⟨?_, ?_⟩
  · haveI := finite_quot M δ hA c0 hc00 hc0O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.AP M δ u u' w p =>
        ((fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c0 hc0O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) - ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p))
        i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : ∀ i j, (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) i j ∈ latS (D.s.atP p) c0 := fun i j => by
      rw [Matrix.sub_apply]; exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    have hki := (k⁻¹).2
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.AP M δ u u' w p) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.2
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a' : ProdE.MP p) - 1 =
        ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) by rw [Matrix.mul_sub, ha]]
      exact entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      rw [Units.val_mul, show (b' : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
        ((b' : ProdE.MP p) - (b : ProdE.MP p)) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) by rw [Matrix.sub_mul, hb]]
      exact entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2
  · set c1 := s2 * (s1 * c0) * (s3 * s4) with hc1d
    have hc1O : c1 ∈ 𝒪[(D.s.atP p).Fp] := Subring.mul_mem _ (Subring.mul_mem _ hs2O (Subring.mul_mem _ hs1O hc0O))
      (Subring.mul_mem _ hs3O hs4O)
    have hc10 : c1 ≠ 0 := mul_ne_zero (mul_ne_zero hs20 (mul_ne_zero hs10 hc00)) (mul_ne_zero hs30 hs40)
    haveI := finite_quot M δ hA c1 hc10 hc1O
    refine relIndex_ne_zero_of_code _ _
      (fun k : ProdE.CPL M δ u u' w hA L U hL hU =>
        ((fun i j => (QuotientAddGroup.mk (⟨(Lp * ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) * Lpi) i j,
            hRO (k.2.1.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup)),
         (fun i j => (QuotientAddGroup.mk (⟨(Upi * ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) * Up) i j,
            hRO (k.2.2.2.2 i j)⟩ : (D.s.atP p).O) : (D.s.atP p).O ⧸ (Ideal.span {dO c1 hc1O}).toAddSubgroup))))
      (fun k k' heq => ?_)
    have e1 : EntIn (latS (D.s.atP p) c1) (Lp * (((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.MP p)) * Lpi) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.fst heq) i) j)
    have e2 : EntIn (latS (D.s.atP p) c1) (Upi * (((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p) -
        ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.MP p)) * Up) := fun i j => by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
      exact quot_eq (congrFun (congrFun (congrArg Prod.snd heq) i) j)
    clear heq
    set a := ((k : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set a' := ((k' : ProdE.StP M δ u u' w p).1.1 : ProdE.GLp p)
    set b := ((k : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    set b' := ((k' : ProdE.StP M δ u u' w p).1.2.unop : ProdE.GLp p)
    have hki := (k⁻¹).2
    have ha : ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (a : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb : (b : ProdE.MP p) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have m := hcong ((k⁻¹ * k' : ProdE.CPL M δ u u' w hA L U hL hU) : ProdE.StP M δ u u' w p) ?_ ?_
    · exact m.1
    · show EntIn _ (((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq1 : ((a⁻¹ * a' : ProdE.GLp p) : ProdE.MP p) - 1 =
          Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) * (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) *
            Lp := by
        rw [show Lpi * ((Lp * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * Lpi) *
            (Lp * ((a' : ProdE.MP p) - (a : ProdE.MP p)) * Lpi)) * Lp =
            (Lpi * Lp) * ((a⁻¹ : ProdE.GLp p) : ProdE.MP p) * (Lpi * Lp) * ((a' : ProdE.MP p) - (a : ProdE.MP p)) *
              (Lpi * Lp) by simp only [Matrix.mul_assoc], hLL', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.mul_sub, ha]
      rw [eq1]
      exact entIn_sandwich hs2 hs1 (entIn_latS_of_eq (t := s3 * s4) rfl (Subring.mul_mem _ hs3O hs4O)
        (entIn_int_mul (fun i j => hRO (hki.1.2.2 i j)) e1))
    · show EntIn _ (((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1)
      have eq2 : ((b' * b⁻¹ : ProdE.GLp p) : ProdE.MP p) - 1 =
          Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) * (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) *
            Upi := by
        rw [show Up * ((Upi * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * Up) *
            (Upi * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) * Up)) * Upi =
            (Up * Upi) * ((b' : ProdE.MP p) - (b : ProdE.MP p)) * (Up * Upi) * ((b⁻¹ : ProdE.GLp p) : ProdE.MP p) *
              (Up * Upi) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
          Units.val_mul, Matrix.sub_mul, hb]
      rw [eq2]
      exact entIn_sandwich hs3 hs4 (entIn_latS_of_eq (t := s2 * s1) (by rw [hc1d]; ring)
        (Subring.mul_mem _ hs2O hs1O) (entIn_mul_int (fun i j => hRO (hki.2.2.2 i j)) e2))

end Fin2

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApprox

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem approxC : ProdE.ApproxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE
  obtain ⟨S, hSAC, hSint⟩ := good_places M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
  exact ⟨S, hSAC, fun p => finIdx_at M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1,
    fun h => approx_core M δ u u' w hE.1 L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1 S hSint h⟩

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end
