module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryBlockMatricesReadInPlaceField
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameScalarOddPositionsDetStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalModelPolynomialOnStdFramesInjectiveStatement
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitution

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelA.ActInv

theorem det_inv_gl {n : ℕ} {F : Type} [Field F] (A : GL (Fin n) F) :
    ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = (A : Matrix (Fin n) (Fin n) F).det⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) {Tau : Type} [Fintype Tau] {n : ℕ}

theorem det_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    ((hAt P h pos (fun _ => 1) g v s : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ).det =
      if Even s.val then (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det
      else (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ).det⁻¹ := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    show (Matrix.transpose (((reG P h (g (pos ⟨v, s⟩)))⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ)).det = _
    rw [Matrix.det_transpose, det_inv_gl]
    show (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)).det⁻¹ = _
    unfold reM
    rw [Matrix.det_submatrix_equiv_self]

theorem inv_placeBlockMatrix_unit_twist (h : P.m + 1 = n) (pos : (Σ v : Fin P.nV, Fin (P.n' v)) ≃ Tau) (g : Tau → GL (Fin n) ℂ)
    (v : Fin P.nV) (s : Fin (P.n' v)) :
    (((hAt P h pos (fun _ => 1) g v s)⁻¹ : GL (Fin (P.m + 1)) ℂ) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) ℂ) =
      if Even s.val then reM P h (((g (pos ⟨v, s⟩))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      else Matrix.transpose (reM P h (g (pos ⟨v, s⟩) : Matrix (Fin n) (Fin n) ℂ)) := by
  unfold hAt
  by_cases hs : Even s.val
  · simp only [hs, if_true, one_mul, inv_one, mul_one]
    rw [← map_inv]
    rfl
  · simp only [hs, if_false, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.TwV.DelA.ActInv


open GlobalTheory.TwV.DelA.ActInv in
theorem GlobalTheory.TwV.DelA.actC_inv_read : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  intro p _ X D pos Kc _ _ _ ι ρ hT fd j hN La' M hU hF R
  have hblk := GlobalTheory.TwV.DelA.blkC_atR_read X D pos Kc ι ρ hT M hU
  have hcoe : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin k) A),
      ((Matrix.GeneralLinearGroup.map f g : GL (Fin k) B) : Matrix (Fin k) (Fin k) B) = (g : Matrix (Fin k) (Fin k) A).map f :=
    fun _ _ => rfl
  have hdm : ∀ {k : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : Matrix (Fin k) (Fin k) A),
      (g.map f).det = f g.det := fun f g => (RingHom.map_det f g).symm
  have hev : ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)), Even s.val ↔ ¬ IsOddPos s := by
    intro v s; unfold IsOddPos; rw [Nat.even_iff]; omega
  have hsc : (∏ v, ∏ s, ((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc).det ^ (-eAt (X.Pj (j + 1)) v s)) =
      ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) := by
    rw [map_prod, ← Equiv.prod_comp pos, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun s _ => ?_
    have he : eAt (X.Pj (j + 1)) v s = eT X D pos (j + 1) (pos ⟨v, s⟩) := by
      show _ = eAt (X.Pj (j + 1)) ((pos.symm (pos ⟨v, s⟩)).1) ((pos.symm (pos ⟨v, s⟩)).2)
      rw [Equiv.symm_apply_apply]
    rw [he, (eT_last_pair X D pos j _).2, Equiv.symm_apply_apply, hcoe, hdm, det_placeBlockMatrix_unit_twist]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    simp only [atR]
    rw [hcoe, hdm, det_inv_gl, map_inv₀]
    split_ifs with h1 h2 h3
    · exact absurd h2 ((hev v s).1 h1)
    · rw [map_inv₀, map_zpow₀, inv_zpow', neg_neg]
      rfl
    · rw [inv_inv, map_zpow₀, neg_sub]
      rfl
    · exact absurd ((hev v s).2 h3) h1
  have hent : ∀ (v : Fin (X.Pj (j + 1)).nV) (s : Fin ((X.Pj (j + 1)).n' v)) (a b : Fin ((X.Pj (j + 1)).m + 1)),
      ((((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc) : Matrix (Fin ((X.Pj (j + 1)).m + 1)) (Fin ((X.Pj (j + 1)).m + 1)) Kc) a b =
      GlobalTheory.FrameB.mk Kc fd j La' v s (Fin.cast (rankJ X (j + 1)) a) (Fin.cast (rankJ X (j + 1)) b) := by
    intro v s a b
    rw [← map_inv, hcoe, Matrix.map_apply, inv_placeBlockMatrix_unit_twist]
    have hb := congrFun (congrFun (hblk v s).1 (finCongr (rkT X D hN) a)) (finCongr (rkT X D hN) b)
    have hinv : (atR D M (pos ⟨v, s⟩))⁻¹ = atR D M⁻¹ (pos ⟨v, s⟩) := by simp [atR, map_inv]
    unfold GlobalTheory.FrameB.mk mAt
    rw [Matrix.submatrix_apply, Matrix.map_apply, hF v, Matrix.submatrix_apply]
    rw [show posJ X D pos (j + 1) = pos from rfl]
    split_ifs at hb with h2 <;> split_ifs with h1
    · exact absurd h2 ((hev v s).1 h1)
    · simp only [Matrix.map_apply, Matrix.transpose_apply] at hb
      rw [hinv] at hb
      exact hb
    · simp only [Matrix.map_apply] at hb
      have e : ((atR D M⁻¹ (pos ⟨v, s⟩))⁻¹ : GL (Fin (D.R.N (j + 1))) ℂ) = atR D M (pos ⟨v, s⟩) := by rw [← hinv, inv_inv]
      refine Eq.trans ?_ hb
      exact congrArg ι (congrArg (fun g : GL (Fin (D.R.N (j + 1))) ℂ => (g : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) (finCongr (rkT X D hN) a) (finCongr (rkT X D hN) b)) e)
    · exact absurd ((hev v s).2 h2) h1
  have hsub : (substR (X.Pj (j + 1)) Kc fun v s => (((Matrix.GeneralLinearGroup.map ι (hAt (X.Pj (j + 1)) (rkT X D hN) (posJ X D pos (j + 1)) (fun _ => 1) (atR D M⁻¹) v s) : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc))⁻¹ : GL (Fin ((X.Pj (j + 1)).m + 1)) Kc)) = GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') := by
    apply MvPolynomial.algHom_ext
    rintro ⟨v, s, a, t⟩
    simp only [substR, GlobalTheory.FrameB.tau0, MvPolynomial.aeval_X, GlobalTheory.FrameB.frF]
    refine Fintype.sum_equiv (finCongr (rankJ X (j + 1))) _ _ fun b => ?_
    rw [hent v s a b]
    congr 2
  unfold actC
  rw [map_natActR]
  unfold natActR
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [hsc, hsub]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitutionStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complex_block_action_inv_read_as_substitution : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  first | exact @GlobalTheory.TwV.DelA.actC_inv_read | exact GlobalTheory.TwV.DelA.actC_inv_read | (intros; apply GlobalTheory.TwV.DelA.actC_inv_read <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvenFrameBlockScalingHomogeneousPolynomialStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  intro p _ X D pos Kc _ _ _ fd c j La' d R hR
  classical
  let blk : Var (X.Pj (j + 1)) → Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) := fun y => ⟨y.1, y.2.1⟩
  let E : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) → Kc := fun b => if IsOddPos b.2 then 1 else c
  have hf : ∀ y, GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') y =
      MvPolynomial.C (E (blk y)) * GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.mk Kc fd j La') y := by
    intro y
    unfold GlobalTheory.FrameB.frF GlobalTheory.FrameB.wV
    simp only [E, blk]
    split_ifs with h1 h2 h2
    · simp only [MvPolynomial.C_1, one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp only [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, Finset.mul_sum, mul_assoc]
  have hm : ∀ m ∈ R.support, (∏ y, E (blk y) ^ m y) = ∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ := by
    intro m hmR
    rw [← Finset.prod_fiberwise Finset.univ blk, ← (posJ X D pos (j + 1)).prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hpb : pos.symm (posJ X D pos (j + 1) b) = b := pos.symm_apply_apply b
    have h2 : ∏ y ∈ Finset.univ.filter (fun y => blk y = b), E (blk y) ^ m y =
        E b ^ (∑ y ∈ Finset.univ.filter (fun y => blk y = b), m y) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2]
    rw [h2, hpb]
    simp only [E]
    split_ifs with h1 h3 h3
    · exact one_pow _
    · exact absurd h1 h3
    · exact absurd h3 h1
    · have hd := hR m hmR (posJ X D pos (j + 1) b) (by rw [hpb]; exact h1)
      rw [Equiv.symm_apply_apply, ← Finset.sum_filter] at hd
      rw [← hd, ← Nat.cast_sum, zpow_natCast]
  unfold GlobalTheory.FrameB.tau0
  conv_lhs => rw [R.as_sum]
  conv_rhs => rw [R.as_sum]

  simp only [map_sum, Finset.smul_sum, MvPolynomial.aeval_monomial]
  refine Finset.sum_congr rfl fun m hmR => ?_
  rw [← hm m hmR]
  simp only [hf]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomial

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem phiC_eq_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Realises X D pos i h a Q R → phiC X D pos i h a Q = R := by
  intro p _ X D pos i n h a Q R hR
  have hmem : Q ∈ (relPhi X D pos i h a).map (LinearMap.fst ℂ _ _) :=
    Submodule.mem_map.2 ⟨(Q, R), hR, rfl⟩
  have hsel : Realises X D pos i h a Q (phiC X D pos i h a Q) := selOf_mem (relPhi X D pos i h a) Q hmem
  have hz : phiC X D pos i h a Q - R = 0 := by
    apply GlobalTheory.T.evalModelPolynomialOnStdFrames_injective X D pos i h
    intro f
    rw [map_sub, Pi.sub_apply, hsel f, hR f, sub_self]
  exact sub_eq_zero.1 hz

end GlobalTheory.TwV.DelA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearChoiceEqRealisingPolynomialStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.linearChoice_eq_realisingPolynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ), Realises X D pos i h a Q R → phiC X D pos i h a Q = R := by
  first | exact @GlobalTheory.TwV.DelA.phiC_eq_of_realises | exact GlobalTheory.TwV.DelA.phiC_eq_of_realises | (intros; apply GlobalTheory.TwV.DelA.phiC_eq_of_realises <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalar

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  intro p _ X D pos Kc _ _ _ ι ρ hPT fd c hc j hN La' M hU hFr ν hν P hP
  obtain ⟨-, -, hsz', hle, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level X D pos j (rkT X D hN) (extNu (D.R.N (j + 1)) ν) hle P hP
  have hRR : phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P = R0 := GlobalTheory.T.linearChoice_eq_realisingPolynomial X D pos (j + 1) (rkT X D hN) _ P R0 hR0
  have hdeg := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos (j + 1) (rkT X D hN) (wT X D pos j) (extNu _ ν) P R0 hP hR0
  have hphi : phi0 X D pos ι j P = MvPolynomial.map ι R0 := by
    unfold phi0
    rw [dite_eq_left (rkT X D hN)]
    show MvPolynomial.map ι (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P) = _
    rw [hRR]
  have hhom : ∀ m ∈ (MvPolynomial.map ι R0).support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 →
      (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) =
        (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = szT X D pos j τ := by
    intro m hm τ ho
    rw [hdeg m (MvPolynomial.support_map_subset _ _ hm) τ, if_neg ho, (GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2, if_neg ho, ← hsz' τ]
    ring
  rw [hphi, hRR]
  unfold GlobalTheory.FrameB.tauV
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt X D pos Kc fd c j La' (fun τ => szT X D pos j τ) _ hhom,
    GlobalTheory.T.latticeTupleFrame_scalar_oddPositions_det X D pos Kc ι ρ hPT fd c hc j hN La' M hU hFr ν hν, GlobalTheory.T.complex_block_action_inv_read_as_substitution X D pos Kc ι ρ hPT fd j hN La' M hU hFr R0, smul_smul, smul_smul]
  congr 1
  have hε : ∀ τ, ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ≠ 0 := fun τ =>
    (((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).map ((ι.comp (embT D τ)))).ne_zero
  have hsum : c ^ (∑ τ, szT X D pos j τ) = ∏ τ, c ^ szT X D pos j τ := by
    classical
    induction (Finset.univ : Finset D.what₂.Tau) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hc, ih]
  rw [hsum, mul_assoc, ← map_mul, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul, map_zpow₀, map_zpow₀]
  split_ifs with ho
  · rw [mul_one, ← zpow_add₀ (hε τ)]
    ring_nf
  · rw [one_mul, ← zpow_add₀ (hε τ)]
    simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalarStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  first | exact @GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | exact GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | (intros; apply GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt <;> assumption)
end
end
