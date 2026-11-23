module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqConjOfInFrame
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuumStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteNodeCartanOrthonormalBasisAllPlacesStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedVectorDefinitePairThetaFockVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitutionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainChiPairMovedVectorColumnCharacter

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem hasInfExp_attChr_chi {μ0 : T} (hL : L.Is μ0) {i : ℕ} (hi : i < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (G.ch.chi (D.R.m - i)) L.eta n) τ
      ((cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd n then 1 / 2 else 0) := by
  have hm1 : 1 ≤ D.R.m - i := by omega
  have hm2 : D.R.m - i ≤ D.R.m := by omega
  have h0 : HasInfExp D (G.ch.chi (D.R.m - i)) τ (cen D sc.cGap τ (D.R.m - i) : ℚ) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ)) (G.ch.chi_eq _ hm1 hm2)
      ⟨fun τ => 2 * cen D sc.cGap τ (D.R.m - i), fun τ => by push_cast; ring, G.ch.inf _ hm1 hm2⟩ τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem rowEntries_c_rev (τ : D.what₂.Tau) (i : Fin D.R.m) :
    (rowEntries D sc.cGap τ).c i.rev = cen D sc.cGap τ (D.R.m - i) := by
  show (num D sc.cGap τ).cen ((i.rev : ℕ) + 1) = _
  rw [Fin.val_rev, show D.R.m - (i + 1) + 1 = D.R.m - i by omega]
  rfl

theorem half_ceil (n : ℕ) : (((n + 1) / 2 : ℕ) : ℚ) = (n : ℚ) / 2 + if Odd n then 1 / 2 else 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [if_neg (Nat.not_odd_iff_even.2 ⟨k, hk⟩), hk, show (k + k + 1) / 2 = k by omega]
    push_cast; ring
  · rw [if_pos ⟨k, hk⟩, hk, show (2 * k + 1 + 1) / 2 = k + 1 by omega]
    push_cast; ring

theorem det_compAt_ptGrid {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (n : ℕ) (hn : n < D.R.m + 1)
    (τ : D.what₂.Tau) :
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid n D.R.m)) (ptGrid W g n))).det =
      Matrix.det (g.2 ⟨n, hn⟩ τ).1 := by
  have hX : DefNode D.R.m (.grid n D.R.m) := ⟨Nat.lt_succ_iff.1 hn, rfl⟩
  have hW := posOnb_of_defNode W μ0 hL hX
  have hB : IsUnit (W.onb (.grid n D.R.m) τ).det := by
    have h := congrArg Matrix.det (hW τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  rw [ptGrid_le W g hn, compAt_kappa_snd g ⟨n, hn⟩ hW τ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv,
    mul_right_comm, Ring.mul_inverse_cancel _ hB, one_mul]
  exact Matrix.det_submatrix_equiv_self (finCongr (rank_gridM G (Nat.lt_succ_iff.1 hn))) _

theorem om_ptGrid_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t i d hd
  have hp : DefPair D.R.m (.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  have hn := DefPair.nodes hp
  have hom := W.om_is (.chi (i : ℕ) D.R.m) (by
    simp only [DefPair, DefNode] at hp hn; simp only [Pair.InRange, Node.InRange]; omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gridFiniteDatumVector_theta_fockVacuum W S.Z hp d hd
  have hf : IsThetaFunO W.ψ _ _ (movedVec t S d) ∧ ∀ τ, IsFockVacAt (heisO W.ψ _ _) W.θ τ
      (cplxO (G.cartS W.cart (.chi (i : ℕ) D.R.m) τ) (G.onT W.cart (.chi (i : ℕ) D.R.m) τ)) (movedVec t S d) :=
    GlobalTheory.T.weil_finitePoint_preserves_fockVacuum D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ h1 h2 _
      (GlobalTheory.FockReal.negGA_mem_GfC _ (S.N.u _).2) _ (S.N.u _).2
  have hrS : (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC ((i : ℕ) + 1) := rank_gridM G (by omega)
  have hrT : (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank = (rowSizes D).nC (i : ℕ) := rank_gridM G (by omega)
  have key := GlobalTheory.FockReal.om_fockIn hL W W.onb hp (fun X hX τ => GlobalTheory.FockReal.onb_def hL W hX τ)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pS (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => (cen D sc.cGap τ (D.R.m - i) : ℚ) - if Odd (G.pT (.chi (i : ℕ) D.R.m : Pair T)).rank then 1 / 2 else 0)
    (fun τ => hasInfExp_attChr_chi hL i.2 _ τ) (fun τ => hasInfExp_attChr_chi hL i.2 _ τ)
    (fun τ => (rowEntries D sc.cGap τ).c i.rev - (((rowSizes D).nC i.succ + 1) / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).c i.rev + (((rowSizes D).nC i.castSucc + 1) / 2 : ℕ))
    (fun τ => ?_) (fun τ => ?_) _ hf.1 hf.2 (ptGrid W g i) (ptGrid_mem W g i) (ptGrid W g (i + 1))
    (ptGrid_mem W g (i + 1)) 1
  · have e1 : fockIn W W.onb (.chi (i : ℕ) D.R.m) (movedVec t S d) 1 = movedVec t S d :=
      GlobalTheory.FiniteFock.pureTensorO_one _ _ _ _ _ _ _ _ _
    rw [show GlobalTheory.FockReal.realSubst W W.onb (.chi (i : ℕ) D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)) 1 = 1 from
      map_one _, e1] at key
    rw [key]
    congr 1
    simp only [GlobalTheory.FockReal.realChar, GridData.toPair, mt_negGA]
    simp only [det_compAt_ptGrid hL W g (i : ℕ) (by omega), det_compAt_ptGrid hL W g ((i : ℕ) + 1) (by omega)]
    simp only [colScal, detChar, detU, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [mul_comm]
    rfl
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_succ, rank_gridM G (show (i : ℕ) + 1 ≤ D.R.m by omega),
      Int.cast_sub, Int.cast_natCast, half_ceil]
    ring
  · simp only [GlobalTheory.FockReal.sgnP, rowEntries_c_rev, Fin.val_castSucc, hrT, Int.cast_add, Int.cast_neg, Int.cast_natCast,
      half_ceil]
    ring

end GlobalTheory.RowReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainChiPairMovedVectorColumnCharacterStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d →
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (GlobalTheory.RowReal.ptGrid W g i) (GlobalTheory.RowReal.ptGrid W g (i + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.colScal (GlobalTheory.RowReal.rowEntries D sc.cGap) i g • movedVec t S d := by
  first | exact @GlobalTheory.RowReal.om_ptGrid_movedVec | exact GlobalTheory.RowReal.om_ptGrid_movedVec | (intros; apply GlobalTheory.RowReal.om_ptGrid_movedVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionColumnStepRenameConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Kronecker

namespace GlobalTheory.RowReal

theorem sum_conjSub_cast {ι : Type} {a a' b b' : ℕ} (ha : a = a') (hb : b = b') (U : Matrix (Fin a') (Fin a') ℂ)
    (V : Matrix (Fin b') (Fin b') ℂ) (hV : star V * V = 1) (τ : ι) (p : Fin a) (q : Fin b) :
    ∑ x : Fin a, ∑ y : Fin b, MvPolynomial.C ((starRingEnd ℂ) (U.submatrix (Fin.cast ha) (Fin.cast ha) x p) *
        (starRingEnd ℂ) ((V.submatrix (Fin.cast hb) (Fin.cast hb))⁻¹ q y)) *
        (MvPolynomial.X (τ, Fin.cast hb y, Fin.cast ha x) : MvPolynomial (ι × Fin b' × Fin a') ℂ) =
      ∑ x : Fin b', ∑ y : Fin a', MvPolynomial.C ((V ⊗ₖ (star U)ᵀ) (x, y) (Fin.cast hb q, Fin.cast ha p)) *
        MvPolynomial.X (τ, x, y) := by
  subst ha hb
  have e : ∀ {n : ℕ} (h : n = n) (M : Matrix (Fin n) (Fin n) ℂ), M.submatrix (Fin.cast h) (Fin.cast h) = M := fun _ _ => by
    ext; simp
  simp only [e, Fin.cast_eq_self]
  rw [Matrix.inv_eq_left_inv hV, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  congr 2
  simp only [Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.star_apply, RCLike.star_def, RingHomCompTriple.comp_apply,
    RingHom.id_apply, Complex.conj_conj]
  ring

theorem trRow_fockSubAll : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  intro D T L sc G i u v Q
  have hL : ∀ P, linSub (homMat _ _ (u, v)) P = MvPolynomial.aeval (R := ℂ) (fun p : D.what₂.Tau × (Fin ((rowSizes D).nC (i + 1)) × Fin ((rowSizes D).nC i)) => ∑ j, MvPolynomial.C ((homMat _ _ (u, v)) p.1 j p.2) * (MvPolynomial.X (p.1, j) : MvPolynomial _ ℂ)) P := fun _ => rfl
  rw [hL, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rintro ⟨τ, p, q⟩

  simp only [AlgHom.comp_apply, fockSubAll, trRow, MvPolynomial.aeval_X, MvPolynomial.rename_X, map_sum, map_mul, MvPolynomial.rename_C, Fintype.sum_prod_type]
  have hc : ¬ ((p : ℕ) < (G.V (.grid i D.R.m)).rank ↔ (q : ℕ) < 0) := by simp [p.2]
  simp only [if_neg hc]
  have hH : ∀ τ', homMat _ _ (u, v) τ' = ((v τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) ⊗ₖ (star ((u τ' : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ))ᵀ := fun _ => rfl
  simp only [hH]
  exact sum_conjSub_cast _ _ _ _ (v τ).2.1 τ p q

end GlobalTheory.RowReal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSubstitutionColumnStepRenameConjStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockSubstitution_columnStep_rename_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i : Fin D.R.m)
    (u : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC i)) (v : UG D.what₂.Tau ((GlobalTheory.RowReal.rowSizes D).nC (i + 1)))
    (Q : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank),
    GlobalTheory.RowReal.trRow G i (GlobalTheory.RowReal.fockSubAll (fun _ => 0) (fun _ => (G.V (.grid i D.R.m)).rank)
      (fun τ => ((v τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i + 1) i.2)))
      (fun τ => ((u τ : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ).submatrix (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))
        (Fin.cast (GlobalTheory.RowReal.rank_gridM G (i := i) i.2.le))) Q) =
      linSub (homMat _ _ (u, v)) (GlobalTheory.RowReal.trRow G i Q) := by
  first | exact @GlobalTheory.RowReal.trRow_fockSubAll | exact GlobalTheory.RowReal.trRow_fockSubAll | (intros; apply GlobalTheory.RowReal.trRow_fockSubAll <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmFockCompact

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem om_fock_chi {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (i : Fin D.R.m)
    (d : FinDatum G t (.chi i D.R.m)) (hd : S.Z.HasVec d)
    (Q Q' : PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank)
    (hQ : trRow G i Q' = colFock (rowEntries D sc.cGap) i g (trRow G i Q)) :
    W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
        (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
      W.fock (.chi i D.R.m) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.grid (i : ℕ) D.R.m) := ⟨i.2.le, rfl⟩
  have hY : DefNode D.R.m (.grid ((i : ℕ) + 1) D.R.m) := ⟨i.2, rfl⟩
  have hp : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := ⟨i.2, rfl⟩
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.chi i D.R.m) hp d hd
  have hc := GlobalTheory.T.compactChain_chiPair_movedVector_columnCharacter hL W S g t i d hd
  let u : UG D.what₂.Tau ((rowSizes D).nC (i : ℕ)) := g.2 ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩
  let v : UG D.what₂.Tau ((rowSizes D).nC ((i : ℕ) + 1)) := g.2 ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩
  have c1 : ∀ τ, compAt W.θ τ (mt (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.succ_lt_succ i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ) + 1, Nat.succ_lt_succ i.2⟩ (posOnb_of_defNode W μ0 hL hY) τ
  have c1' : ∀ τ, compAt W.θ τ (mt (negSp (G.V (.grid ((i : ℕ) + 1) D.R.m)))
      (negGA (G.V (.grid ((i : ℕ) + 1) D.R.m)) (ptGrid W g ((i : ℕ) + 1)))) =
      W.onb (.grid ((i : ℕ) + 1) D.R.m) τ * (v τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) *
        (W.onb (.grid ((i : ℕ) + 1) D.R.m) τ)⁻¹ := fun τ => by
    rw [mt_negGA]; exact c1 τ
  have c2 : ∀ τ, compAt W.θ τ (mt (G.V (.grid (i : ℕ) D.R.m)) (ptGrid W g i)) =
      W.onb (.grid (i : ℕ) D.R.m) τ * (u τ).1.submatrix
        (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) *
        (W.onb (.grid (i : ℕ) D.R.m) τ)⁻¹ := fun τ => by
    rw [ptGrid_le W g (Nat.lt_succ_of_lt i.2)]
    exact compAt_kappa_snd g ⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩ (posOnb_of_defNode W μ0 hL hX) τ
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.chi i D.R.m) ⟨i.2, le_rfl⟩ (fun _ => 0) (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
    (fun _ => Nat.zero_le _) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.2.2) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) _ hf hv
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
    (fun ρ => isKMat_cast _ _ (Or.inr rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (negGA _ (ptGrid W g ((i : ℕ) + 1))) (ptGrid W g i) (GlobalTheory.FockReal.negGA_mem_GinfC _ (ptGrid_mem W g _)) (ptGrid_mem W g _)
    c1' c2 _ hc Q
  have hQ' : Q' = colScal (rowEntries D sc.cGap) i g • fockSubAll (fun _ => 0)
      (fun _ => (G.V (.grid (i : ℕ) D.R.m)).rank)
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)) (Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2)))
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)) (Fin.cast (rank_gridM G (i := (i : ℕ)) i.2.le)))
      Q := by
    apply trRow_injective G i
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_columnStep_rename_conj G i u v Q]
    rfl
  exact key.trans (by rw [hQ', LinearMap.map_smul])

end GlobalTheory.RowReal
end
end
end
