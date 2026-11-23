module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.PtMatIsUnit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsUpUniMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolGrp
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemRNone

section

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good2

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_R_none {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none) (x : (D.s.atP p).Ep) :
    x ∈ (M p).R ↔ x ∈ (D.s.atP p).O := by
  obtain ⟨-, -, -, hO, -, -⟩ := hA
  show x ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R ↔ _
  rw [hs]
  show x ∈ (M p).L.O ↔ _
  rw [hO]

theorem bOf_int {p : PlF D} (g : Formalism.L2.SG.Pf.VolPinAsm.StG w)
    (hg : ∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O)
    (hpv : ∀ a : Fin (D.R.rS + 1), (D.s.atP p).ιE (Formalism.L2.SG.Pf.pv w.1 a) ∈ (D.s.atP p).O ∧
      (D.s.atP p).ιE ((Formalism.L2.SG.Pf.pv w.1 a)⁻¹) ∈ (D.s.atP p).O) :
    ∀ i j, (D.s.atP p).ιE (Formalism.L2.SG.Pf.VolPinAsm.bOf w g i j) ∈ (D.s.atP p).O := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  set a := ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D)
  set b := Formalism.L2.SG.Pf.VolPinAsm.bOf w g
  obtain ⟨-, hb, hW⟩ := ProdE.bOf_spec w g
  have hfix := fix_cOf hσ ν hν a
  have hWu : IsUnit (ptMat w).det := Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_isUnit w
  have hcb : cOf σ ν a * b = 1 := by
    have h1 : ptMat w * (cOf σ ν a * b) = ptMat w * 1 := by
      rw [Matrix.mul_one, ← Matrix.mul_assoc]
      conv_lhs => rw [ptMat_mono]
      rw [← hfix, ← ptMat_mono]
      exact hW
    have := congrArg (fun X => (ptMat w)⁻¹ * X) h1
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hWu, Matrix.one_mul] using this
  have hbinv : b = (cOf σ ν a)⁻¹ := (Matrix.inv_eq_right_inv hcb).symm
  have hcU : IsUpUni (cOf σ ν a) := by
    have := (ZsVolGrp.isUpUni_inv hb).1
    rwa [show b⁻¹ = cOf σ ν a from Matrix.inv_eq_left_inv hcb] at this
  have hdet : (cOf σ ν a).det = 1 :=
    ZsVolGrp.det_up (fun x => (hcU x x).2 rfl) (fun x y hxy => (hcU x y).1 hxy)
  have hcO : ∀ x y, (D.s.atP p).ιE (cOf σ ν a x y) ∈ (D.s.atP p).O := by
    intro x y
    simp only [cOf, Matrix.of_apply, Ring.inverse_eq_inv', map_mul]
    exact (D.s.atP p).O.mul_mem ((D.s.atP p).O.mul_mem (hpv (σ x)).2 (hg _ _)) (hpv (σ y)).1
  intro i j
  rw [hbinv, ZsVolGrp.inv_eq_adj hdet]
  have e := congrFun (congrFun (RingHom.map_adjugate (D.s.atP p).ιE (cOf σ ν a)) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e
  rw [e]
  exact ZsVolGrp.adj_mem (D.s.atP p).O (fun x y => by simpa using hcO x y) i j

end Good2

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxGood

section

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem ring_inverse_eq {K : Type*} [CommRing K] {x y : K} (h : x * y = 1) : Ring.inverse x = y := by
  have hx : IsUnit x := ⟨⟨x, y, h, by rw [mul_comm]; exact h⟩, rfl⟩
  calc Ring.inverse x = Ring.inverse x * (x * y) := by rw [h, mul_one]
    _ = y := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hx, one_mul]

theorem cj_mem_O {p : PlF D} {x : (D.s.atP p).Ep} (hx : x ∈ (D.s.atP p).O) : (D.s.atP p).cj x ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hx ⊢
  exact hx.map (((D.s.atP p).cj.toAlgHom).restrictScalars 𝒪[(D.s.atP p).Fp])

theorem lOf_ρOf_int {p : PlF D} (hA : Agree δ M p) (hs : (M p).split = none)
    (hδ : δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (huP : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (a b : Formalism.L2.SG.PairVal.MatR D) (ha : ∀ i j, (D.s.atP p).ιE (a i j) ∈ (D.s.atP p).O)
    (hb : ∀ i j, (D.s.atP p).ιE (b i j) ∈ (D.s.atP p).O) :
    (∀ i j, lOf δ M p a b i j ∈ (D.s.atP p).O) ∧ ∀ i j, ρOf δ M p a b i j ∈ (D.s.atP p).O := by
  obtain ⟨-, hδ0, hcj, -, -, -⟩ := hA
  set Op := (D.s.atP p).O
  set c : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)
  set ci : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)
  have hcO : c ∈ Op := Op.mul_mem (alg_mem_O hδ.1) huP.1
  have hciO : ci ∈ Op := Op.mul_mem (alg_mem_O hδ.2) huP.2
  have hcc : c * ci = 1 := by
    have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hδ0, map_one]
    have h2 : (D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (unitAt_ne p), map_one]
    calc c * ci = (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p)⁻¹) *
          ((D.s.atP p).ιE (uP p : D.host.E) * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹)) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
  have hfr : ∀ i, frFac δ p i = ci ^ (D.R.rS - i.val) := fun i => by
    unfold frFac
    exact ring_inverse_eq (by rw [← mul_pow, hcc, one_pow])
  have hfri : ∀ i, Ring.inverse (frFac δ p i) = c ^ (D.R.rS - i.val) := fun i => by
    rw [hfr]; exact ring_inverse_eq (by rw [← mul_pow, mul_comm, hcc, one_pow])
  have hcjfr : ∀ i, ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i) =
      (D.s.atP p).cj ci ^ (D.R.rS - i.val) := fun i => by
    rw [hfr, hcj]; simp
  have hcjfri : ∀ i, Ring.inverse (((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p i)) =
      (D.s.atP p).cj c ^ (D.R.rS - i.val) := fun i => by
    rw [hcjfr]
    refine ring_inverse_eq ?_
    rw [← mul_pow, ← map_mul, mul_comm, hcc, map_one, one_pow]
  have hs1 : ∀ x : D.host.E, (D.s.atP p).ιE x ∈ Op → (D.s.atP p).ιE ((-1) ^ (D.R.rS - 0) * x) ∈ Op := fun x hx => by
    rw [map_mul]; exact Op.mul_mem (by rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _) hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · simp only [lOf, hs, lL, Matrix.of_apply]
    rw [hcjfr, hcjfri]
    exact Op.mul_mem (Op.mul_mem (Op.pow_mem (cj_mem_O hciO) _) (ha i j)) (Op.pow_mem (cj_mem_O hcO) _)
  · simp only [ρOf, hs, ρL, Matrix.of_apply]
    rw [hfri, hfr]
    refine Op.mul_mem (Op.mul_mem (Op.pow_mem hcO _) ?_) (Op.pow_mem hciO _)
    rw [map_mul, map_mul]
    have hpm : ∀ k : ℕ, (D.s.atP p).ιE ((-1 : D.host.E) ^ k) ∈ Op := fun k => by
      rw [map_pow, map_neg, map_one]; exact Op.pow_mem (Op.neg_mem Op.one_mem) _
    exact Op.mul_mem (Op.mul_mem (hpm _) (hb i j)) (hpm _)

end Good

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodPlaces

section

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Good3

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))


theorem good_places (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ S : Finset (PlF D), (∀ p, p ∉ S → ProdE.AP M δ u u' w p = ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
          ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set X : Finset D.host.E := Finset.univ.image (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) with hX
  have hev := Formalism.L2.SG.Pf.LocModel.good_cofinite δ M hA X
  have hfin := Filter.eventually_cofinite.1 hev
  refine ⟨hfin.toFinset, ?_⟩
  have key : ∀ p, p ∉ hfin.toFinset → (M p).split = none ∧
      (δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]) ∧
      ((D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O) ∧
      (∀ t ∈ X, (D.s.atP p).ιE t ∈ (D.s.atP p).O) ∧ (∀ t ∈ X, t ≠ 0 → (D.s.atP p).ιE t⁻¹ ∈ (D.s.atP p).O) := by
    intro p hp
    have hp' : ¬ ¬ _ := fun h => hp (hfin.mem_toFinset.2 h)
    obtain ⟨h1, h2, h3, h4⟩ := not_not.1 hp'
    refine ⟨h1, h2, h3, fun t ht => ?_, fun t ht ht0 => ?_⟩
    · by_cases ht0 : t = 0
      · rw [ht0, map_zero]; exact (D.s.atP p).O.zero_mem
      · have := (h4 t ht 0 (by simpa using ht0)).1
        simpa using this
    · have := (h4 t ht 0 (by simpa using ht0)).2
      simpa using this
  have hpvX : ∀ a : Fin (D.R.rS + 1), Formalism.L2.SG.Pf.pv w.1 a ∈ X := fun a =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem (fun a : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.pv w.1 a) (Finset.mem_univ a)))))
  have hLX : ∀ i j, L i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L ij.1 ij.2) (Finset.mem_univ (i, j))))))
  have hUX : ∀ i j, U i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U ij.1 ij.2) (Finset.mem_univ (i, j)))))
  have hLiX : ∀ i j, L⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => L⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j))))
  have hUiX : ∀ i j, U⁻¹ i j ∈ X := fun i j =>
    Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => U⁻¹ ij.1 ij.2) (Finset.mem_univ (i, j)))
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  refine ⟨fun p hp => ?_, fun p hp g hg => ?_⟩
  · obtain ⟨hs, hδ, huP, hXi, -⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have i1 := lOf_ρOf_int M δ (hA p) hs hδ huP L U (fun i j => hXi _ (hLX i j)) (fun i j => hXi _ (hUX i j))
    have i2 := lOf_ρOf_int M δ (hA p) hs hδ huP L⁻¹ U⁻¹ (fun i j => hXi _ (hLiX i j)) (fun i j => hXi _ (hUiX i j))
    have hLp := ProdE.lOf_loUni M δ (hA p) L U hL hU
    have hLpi := ProdE.lOf_loUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have hUp := ProdE.ρOf_upUni M δ (hA p) L U hL hU
    have hUpi := ProdE.ρOf_upUni M δ (hA p) L⁻¹ U⁻¹ hLi.1 hUi.1
    have iLp : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L U) :=
      ⟨fun a => (hLp a a).2 rfl, fun a b h => (hLp a b).1 h, fun a b => (hR _).2 (i1.1 a b)⟩
    have iLpi : Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hLpi a a).2 rfl, fun a b h => (hLpi a b).1 h, fun a b => (hR _).2 (i2.1 a b)⟩
    have iUp : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L U) :=
      ⟨fun a => (hUp a a).2 rfl, fun a b h => (hUp a b).1 h, fun a b => (hR _).2 (i1.2 a b)⟩
    have iUpi : Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p L⁻¹ U⁻¹) :=
      ⟨fun a => (hUpi a a).2 rfl, fun a b h => (hUpi a b).1 h, fun a b => (hR _).2 (i2.2 a b)⟩
    have hLL := ProdE.lp_inv M δ (hA p) L U hL hU
    have hUU := ProdE.up_inv M δ (hA p) L U hL hU
    ext k
    constructor
    · rintro ⟨hk1, hk2⟩
      exact ⟨ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLp hk1) iLpi,
        ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUpi hk2) iUp⟩
    · rintro ⟨hk1, hk2⟩
      refine ⟨?_, ?_⟩
      · have e : ((k.1.1 : ProdE.GLp p) : ProdE.MP p) = lOf δ M p L⁻¹ U⁻¹ *
            (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) * lOf δ M p L U := by
          rw [show lOf δ M p L⁻¹ U⁻¹ * (lOf δ M p L U * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) * lOf δ M p L⁻¹ U⁻¹) *
              lOf δ M p L U = (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) * ((k.1.1 : ProdE.GLp p) : ProdE.MP p) *
                (lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U) by simp only [Matrix.mul_assoc], hLL, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intLow_mul _ (ZsVolGrp.intLow_mul _ iLpi hk1) iLp
      · have e : ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) = ρOf δ M p L U *
            (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) * ρOf δ M p L⁻¹ U⁻¹ := by
          rw [show ρOf δ M p L U * (ρOf δ M p L⁻¹ U⁻¹ * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) * ρOf δ M p L U) *
              ρOf δ M p L⁻¹ U⁻¹ = (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) * ((k.1.2.unop : ProdE.GLp p) : ProdE.MP p) *
                (ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹) by simp only [Matrix.mul_assoc], hUU, Matrix.one_mul, Matrix.mul_one]
        rw [e]
        exact ZsVolGrp.intUp_mul _ (ZsVolGrp.intUp_mul _ iUp hk2) iUpi
  · obtain ⟨hs, hδ, huP, hXi, hXinv⟩ := key p hp
    have hR := mem_R_none M δ (hA p) hs
    have hb := bOf_int w g hg (fun a => ⟨hXi _ (hpvX a), hXinv _ (hpvX a) (Formalism.L2.SG.Pf.pv_ne' w a)⟩)
    have i0 := lOf_ρOf_int M δ (hA p) hs hδ huP _ _ hg hb
    obtain ⟨hπl, hπρ, -⟩ := (ProdE.πP M δ u u' w (hA p) g).2
    exact ⟨⟨fun a => (hπl a a).2 rfl, fun a b h => (hπl a b).1 h, fun a b => (hR _).2 (i0.1 a b)⟩,
      ⟨fun a => (hπρ a a).2 rfl, fun a b h => (hπρ a b).1 h, fun a b => (hR _).2 (i0.2 a b)⟩⟩

end Good3

end Formalism.L2.SG.Pf.ProdEApprox
end
end
end
