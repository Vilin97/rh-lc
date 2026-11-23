module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalLatticeMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplitStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetric
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsProdSinglePlacePiecesOfSuppAt

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceCut

theorem idem_mul {D : D7} {e e' : AE D} {w w' : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e w)
    (h' : Formalism.L2.NTheta.IsIdemAt e' w') : (w = w' → e * e' = e) ∧ (w ≠ w' → e * e' = 0) := by
  have i0 : infPart D e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (GlobalTheory.StdFrames.comp_toAd D) h).1
  have a1 : GlobalTheory.RowRep.piAt w e = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).1
  have a2 : ∀ u, u ≠ w → GlobalTheory.RowRep.piAt u e = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h).2
  have b1 : GlobalTheory.RowRep.piAt w' e' = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').1
  have b2 : ∀ u, u ≠ w' → GlobalTheory.RowRep.piAt u e' = 0 := (GlobalTheory.StdFrames.cpt_of_isIdemAt h').2
  have i1 : infPart D (e * e') = 0 :=
    ((infPart D).map_mul e e').trans ((congrArg (· * infPart D e') i0).trans (zero_mul _))
  refine ⟨fun hw => ae_ext (i1.trans i0.symm) fun u => ?_, fun hw => ae_ext (i1.trans (infPart D).map_zero.symm) fun u => ?_⟩
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u e
    rw [RingHom.map_mul]
    by_cases hu : u = w
    · subst hu; subst hw; rw [b1, mul_one]
    · rw [a2 u hu, zero_mul]
  · change GlobalTheory.RowRep.piAt u (e * e') = GlobalTheory.RowRep.piAt u 0
    rw [RingHom.map_mul, RingHom.map_zero]
    by_cases hu : u = w
    · subst hu; rw [b2 u hw, mul_zero]
    · rw [a2 u hu, zero_mul]

theorem mul_conj_zero {R ι : Type} [CommRing R] (c : R →+* R) (P : Finset ι) (a : ι → R)
    (h1 : ∀ i ∈ P, a i * a i = a i) (h2 : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → a i * a j = 0)
    (h0 : (∑ i ∈ P, a i) * c (∑ i ∈ P, a i) = 0) : ∀ i ∈ P, ∀ j ∈ P, a i * c (a j) = 0 := by
  have k : ∀ i ∈ P, a i * ∑ j ∈ P, a j = a i := fun i hi => by
    rw [Finset.mul_sum, Finset.sum_eq_single i (fun j hj hji => h2 i hi j hj (Ne.symm hji)) (fun h => absurd hi h), h1 i hi]
  intro i hi j hj
  rw [← k i hi, ← k j hj, map_mul, mul_mul_mul_comm, h0, mul_zero]

theorem add_mul_self_eq_of_orthogonal_idempotents {R : Type} [CommRing R] {a b : R} (h1 : a * a = a) (h2 : b * b = b) (h3 : a * b = 0) :
    (a + b) * (a + b) = a + b := by linear_combination h1 + h2 + 2 * h3

theorem add_mul_add_eq_zero_of_pairwise_products_zero {R : Type} [CommRing R] {a b a' b' : R} (h1 : a * a' = 0) (h2 : b * b' = 0) (h3 : a * b' = 0)
    (h4 : a' * b = 0) : (a + b) * (a' + b') = 0 := by linear_combination h1 + h2 + h3 + h4

theorem map_cut {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} {a b : R} (h1 : f a = 1) (h0 : a * b = 0)
    (M : Matrix (Fin n) (Fin n) R) :
    ((a + b) • M + (1 - (a + b)) • (1 : Matrix (Fin n) (Fin n) R)).map f = M.map f := by
  have hb : f b = 0 := by
    have := congrArg f h0
    rwa [map_mul, h1, one_mul, map_zero] at this
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, h1, hb]
  ring



theorem exists_prod_pieces : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  intro D V P es hes h0 r hr
  have h1 : ∀ w ∈ P, es w * es w = es w := fun w hw => (idem_mul (hes w hw) (hes w hw)).1 rfl
  have h2 : ∀ w ∈ P, ∀ w' ∈ P, w ≠ w' → es w * es w' = 0 := fun w hw w' hw' => (idem_mul (hes w hw) (hes w' hw')).2
  have h3 := mul_conj_zero (cA D) P es h1 h2 h0
  let E : P → AE D := fun w => es w.1 + cA D (es w.1)
  have hEE : ∀ w, E w * E w = E w := fun w =>
    add_mul_self_eq_of_orthogonal_idempotents (h1 _ w.2) (by rw [← RingHom.map_mul, h1 _ w.2]) (h3 _ w.2 _ w.2)
  have hEc : ∀ w, cA D (E w) = E w := fun w => by
    show cA D (es w.1 + cA D (es w.1)) = es w.1 + cA D (es w.1)
    rw [RingHom.map_add (f := _), Formalism.L2.Theta.cA_cA, add_comm]
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    have := h2 _ w.2 _ w'.2 fun h => hww (Subtype.ext h)
    exact add_mul_add_eq_zero_of_pairwise_products_zero this (by rw [← RingHom.map_mul, this, RingHom.map_zero]) (h3 _ w.2 _ w'.2) (h3 _ w'.2 _ w.2)
  choose h hh using fun w => GlobalTheory.SplitCut.cut_exists V r (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hh w]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hh w]
    have a1 : GlobalTheory.RowRep.piAt w.1 (es w.1) = 1 := (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes _ w.2)).1
    exact map_cut (GlobalTheory.RowRep.piAt w.1) a1 (h3 _ w.2 _ w.2) _
  · apply GlobalTheory.SplitCut.mt_injective
    have hsum : (Finset.univ.toList.map E).sum = (∑ w ∈ P, es w) + cA D (∑ w ∈ P, es w) := by

      rw [Finset.sum_map_toList, map_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_coe_sort P fun w => es w + cA D (es w)
    rw [GlobalTheory.SplitCut.mt_list_prod V h E (mt V r) hh hEo _ (Finset.nodup_toList _), hsum]
    refine GlobalTheory.SplitCut.exists_widePullback_of_iteratedLine _ _ fun i j => ?_
    rw [sub_mul, one_mul, hr i j, sub_self]

end GlobalTheory.PlaceCut

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsProdSinglePlacePiecesOfSuppAtStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_prod_single_place_pieces_of_suppAt : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (es w) w) → (∑ w ∈ P, es w) * cA D (∑ w ∈ P, es w) = 0 → ∀ r : GA D V, SuppAt (∑ w ∈ P, es w) V r → ∃ h : P → GA D V, (∀ w, SuppAt (es w.1) V (h w)) ∧ (∀ w, (mt V (h w)).map (GlobalTheory.RowRep.piAt w.1) = (mt V r).map (GlobalTheory.RowRep.piAt w.1)) ∧ r = (Finset.univ.toList.map h).prod := by
  first | exact @GlobalTheory.PlaceCut.exists_prod_pieces | exact GlobalTheory.PlaceCut.exists_prod_pieces | (intros; apply GlobalTheory.PlaceCut.exists_prod_pieces <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetricStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  exact @GlobalTheory.RowRepLoc.mem_jacGrp_of_symR
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiGroupOfLocalLatticeMatrices

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inBasis_congr {D : D7} {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    {x y : GL (Fin n) (Lev.EAf D)} (e : GlobalTheory.StdFrames.loc w x = GlobalTheory.StdFrames.loc w y) : inBasis h β w x = inBasis h β w y := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, e]

theorem mem_jacGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (hσ : D.R.m - 1 - j = 2 * σ),
    1 ≤ σ → ∀ (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ jacGrp (rowJac ch.G j hj' σ hσ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t j σ hi hj hj' hσ h1 r g hr hg
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, hc⟩, hsupp, hloc⟩ := hr
  obtain ⟨h, hh1, hh2, hr⟩ := GlobalTheory.T.exists_prod_single_place_pieces_of_suppAt _ _ es hes hc r hsupp
  rw [hr]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨q, hqe, -, hqpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w.1 (es w.1) (hes w.1 w.2) s.hF
  have hF := ch.S.row t (Set.mem_univ t) w.1 w.2 j hj'
  have e1 : GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) (h w)) =
      GlobalTheory.StdFrames.loc w.1 (Lev.finE (ch.G.V (.grid D.R.m j)) r) := Units.ext (hh2 w)
  have hm : toFrame one_le_sLen hj' (g w) ∈ symR (Kw w.1) _ _ := hg w
  rw [← hloc w] at hm
  refine GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric (ch.G.rowDec j hj') hσ h1 w.1 _ _ _ hF (fun p => frameScal_ne w.1 _ _ p) (topRank_eq ch.G t w.1 hj)
    (rank_vertex ch.G t w.1 (X := (D.R.m, j)) ⟨le_rfl, hj⟩)
    (by have := topRank_add (G := locGrid ch.G t w.1) one_le_sLen j; have hm' : (locGrid ch.G t w.1).m = D.R.m := rfl; rw [hm'] at this; omega)
    q (fun x => (hqpr x).trans rfl) (h w) (hqe ▸ hh1 w) ?_
  rw [inBasis_congr _ _ _ e1]
  exact hm

end GlobalTheory.RowLift
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiGroupOfLocalLatticeMatricesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (hσ : D.R.m - 1 - j = 2 * σ),
    1 ≤ σ → ∀ (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ jacGrp (rowJac ch.G j hj' σ hσ) := by
  first | exact @GlobalTheory.RowLift.mem_jacGrp_of_hasLoc | exact GlobalTheory.RowLift.mem_jacGrp_of_hasLoc | (intros; apply GlobalTheory.RowLift.mem_jacGrp_of_hasLoc <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemen

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLift
open GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

theorem suppAt_conj {V : HSp D} {e : AE D} {y : GA D V} (h : SuppAt e V y) (δ : GA D V) : SuppAt e V (δ * y * δ⁻¹) := by
  have hs : (e + cA D e) • (mt V y - 1) = mt V y - 1 := Matrix.ext fun i j => h i j
  have hδ : mt V δ * mt V δ⁻¹ = 1 := by rw [← GlobalTheory.MixModel.mt_mul, mul_inv_cancel, GlobalTheory.MixModel.mt_one]
  have key : mt V (δ * y * δ⁻¹) - 1 = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hδ]
  have h2 : (e + cA D e) • (mt V δ * (mt V y - 1) * mt V δ⁻¹) = mt V δ * (mt V y - 1) * mt V δ⁻¹ := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hs]
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasLoc_conj (B : Frames G) (t : T) {j : ℕ} (hj : j ≤ D.R.m) {y : GA D (G.V (.grid D.R.m j))}
    {g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)} (h : HasLoc t B hj y g)
    (δ : GA D (G.V (.grid D.R.m j))) :
    HasLoc t B hj (δ * y * δ⁻¹) (fun w => locAt B t w.1 j hj δ * g w * (locAt B t w.1 j hj δ)⁻¹) := by
  obtain ⟨e, he, hs, hl⟩ := h
  refine ⟨e, he, suppAt_conj hs δ, fun w => ?_⟩
  change locAt B t w.1 j hj (δ * y * δ⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  exact congrArg (fun z => locAt B t w.1 j hj δ * z * (locAt B t w.1 j hj δ)⁻¹) (hl w)

theorem conj_rowR' {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    {x y : GL (Fin (Γ.rank (Γ.m, j))) k} (hy : ∃ f, (toFrame hs hj y).val = diagonal f) (hx : x ∈ rowR hs hj) :
    y * x * y⁻¹ ∈ rowR hs hj := by
  obtain ⟨f, hf⟩ := hy
  have hy' : ∃ f, (toFrame hs hj y⁻¹).val = diagonal f :=
    ⟨Ring.inverse f, by rw [map_inv, Matrix.coe_units_inv, hf, Matrix.inv_diagonal]⟩
  have := conj_rowR hs hj (g := fun _ => 1) hy' hx
  have e1 : GlobalTheory.SplitFlip.diagGL (fun _ => (1 : kˣ)) = (1 : GL (Fin (Γ.rank (Γ.m, j))) k) :=
    Units.ext (by rw [GlobalTheory.SplitFlip.diagGL_val]; exact diagonal_one)
  rwa [e1, mul_one, inv_inv] at this

theorem sgn_diag {k : Type} [Field k] {Γ : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ Γ.s) {j : ℕ} (hj : j < Γ.m)
    (c : Fin (Γ.rank (Γ.m, j)) → kˣ) : ∃ f, (toFrame hs hj (GlobalTheory.SplitFlip.diagGL c)).val = diagonal f := by
  have h : topRank Γ j + (Γ.m - 1 - j) = Γ.rank (Γ.m, j) := by have := topRank_add hs j; omega
  exact ⟨_, submatrix_diagonal_equiv (fun i => (c i : k)) (frame h)⟩

end GlobalTheory.RowLift


open GlobalTheory.RowLift GlobalTheory.RowRep in
theorem GlobalTheory.RowLift.lift_rowR : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  obtain ⟨C1, hJ⟩ := GlobalTheory.T.mem_fourierJacobiGroup_of_local_lattice_matrices
  obtain ⟨C2, hB⟩ := GlobalTheory.T.mem_besselGroup_of_local_lattice_matrices
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, hx1⟩ := hJ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, hx2⟩ := hB ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  intro s t j hjI hj hj' δ hδ l hl
  obtain ⟨y, hy⟩ := exists_hasLoc hS.core.lev ch.S.B t hj (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹)
  refine ⟨y, hy, ?_⟩
  have hc := hasLoc_conj ch.S.B t hj hy δ
  have hm : ∀ w : locPl ch.G t, locAt ch.S.B t w.1 j hj δ * (sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) *
      (locAt ch.S.B t w.1 j hj δ)⁻¹ ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj' := fun w =>
    conj_rowR' one_le_sLen hj' (locAt_tilt ch.S.toGridChoice (Set.mem_univ t) w.2 hj hj' hδ)
      (conj_rowR' one_le_sLen hj' (sgn_diag one_le_sLen hj' _) (hl w))
  unfold rowGrp
  split_ifs with h1 h2
  · exact hx1 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' _
      (by have := (idx_le hjI); omega) _ _ hc hm
  · exact hx2 D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc t j _ hjI hj hj' h2 _ _ hc hm
  · exfalso; have := idx_le hjI; omega
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemenStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

theorem _root_.GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  first | exact @GlobalTheory.RowLift.lift_rowR | exact GlobalTheory.RowLift.lift_rowR | (intros; apply GlobalTheory.RowLift.lift_rowR <;> assumption)
end
end
end
