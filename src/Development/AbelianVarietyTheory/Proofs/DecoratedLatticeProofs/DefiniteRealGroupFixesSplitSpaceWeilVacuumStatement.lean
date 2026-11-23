module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumExponentSum

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitVacSum

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem idem_trace_det (P : Matrix ι ι ℂ) (hP : P * P = P) :
    P.trace = P.rank ∧ ∀ u : ℂ, (u • P + (1 - P)).det = u ^ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) :=
    LinearMap.IsIdempotentElem.isProj_range _ hi
  have hr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = P.rank := Matrix.finrank_range_mulVecLin P
  refine ⟨?_, fun u => ?_⟩
  · rw [← Matrix.trace_toLin'_eq, hp.trace, hr]
  · rw [← LinearMap.det_toLin']
    have e := hp.eq_conj_prodMap
    set c := (Submodule.prodEquivOfIsCompl _ _ hp.isCompl)
    have e2 : Matrix.toLin' (u • P + (1 - P)) = c.conj (LinearMap.prodMap (u • LinearMap.id) LinearMap.id) := by
      have : LinearMap.prodMap (u • LinearMap.id) LinearMap.id =
          u • LinearMap.prodMap (LinearMap.id : LinearMap.range (Matrix.toLin' P) →ₗ[ℂ] _) (0 : LinearMap.ker (Matrix.toLin' P) →ₗ[ℂ] _)
            + (1 - LinearMap.prodMap LinearMap.id 0) := by
        refine LinearMap.ext fun x => ?_
        ext <;> simp
      rw [this, map_add (f := _), map_add (f := _), map_smul, map_smul, map_sub, map_sub, ← e, Matrix.toLin'_one]
      congr 2
      exact (LinearEquiv.conj_id c).symm
    rw [e2, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
      LinearMap.det_id, LinearMap.det_id, hr, mul_one, mul_one]

theorem half_idem {s : Matrix ι ι ℂ} (hs : s * s = 1) :
    ((1 / 2 : ℂ) • (1 + s)) * ((1 / 2 : ℂ) • (1 + s)) = (1 / 2 : ℂ) • (1 + s) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_add, add_mul, hs, mul_one, one_mul]
  module

theorem le_rank_half {m : ℕ} {G s t : Matrix ι ι ℂ} (hpos : (G * s).PosDef) (ht : t = s ∨ t = -s)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) :
    m ≤ ((1 / 2 : ℂ) • (1 + t)).rank := by
  refine le_trans ?_ (Matrix.rank_mul_le_left _ B)
  have hinj : Function.Injective (((1 / 2 : ℂ) • (1 + t)) * B).mulVecLin := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : B *ᵥ a + t *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at ha
      exact (smul_eq_zero.1 ha).resolve_left (by norm_num)
    have h2 : star (B *ᵥ a) ⬝ᵥ G *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
        Matrix.zero_mulVec, dotProduct_zero]
    have h3 : star (B *ᵥ a) ⬝ᵥ (G * s) *ᵥ (B *ᵥ a) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      rcases ht with rfl | rfl
      · rw [eq_neg_of_add_eq_zero_right h1, Matrix.mulVec_neg, dotProduct_neg, h2, neg_zero]
      · rw [Matrix.neg_mulVec, add_neg_eq_zero] at h1
        rw [← h1, h2]
    have h4 : B *ᵥ a = 0 := by
      by_contra h
      exact (hpos.dotProduct_mulVec_pos h).ne' h3
    rw [← Matrix.one_mulVec a, ← hC, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  rw [← Matrix.finrank_range_mulVecLin, LinearMap.finrank_range_of_inj hinj]
  simp

theorem trace_eq_zero {m : ℕ} {G s : Matrix ι ι ℂ} (hs : s * s = 1) (hpos : (G * s).PosDef) (hm : 2 * m = Fintype.card ι)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) : s.trace = 0 := by
  have a1 := le_rank_half hpos (Or.inl rfl) B C hC hB
  have a2 := le_rank_half hpos (Or.inr rfl) B C hC hB
  have b1 := (idem_trace_det _ (half_idem hs)).1
  have b2 := (idem_trace_det _ (half_idem (s := -s) (by rw [neg_mul_neg, hs]))).1
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, ← hm, smul_eq_mul] at b1 b2
  rw [Matrix.trace_neg] at b2
  have c : ((((1 / 2 : ℂ) • (1 + s)).rank + ((1 / 2 : ℂ) • (1 + -s)).rank : ℕ) : ℂ) = (2 * m : ℕ) := by
    rw [Nat.cast_add, ← b1, ← b2]; ring
  have c' := Nat.cast_injective c
  have d : ((1 / 2 : ℂ) • (1 + s)).rank = m := by omega
  rw [d] at b1
  push_cast at b1
  linear_combination 2 * b1

end Lin

variable {D : D7} {θ : InfFam D}

end GlobalTheory.SplitVacSum

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum

section

@[expose] public section

noncomputable section
open scoped Matrix ComplexOrder
open Formalism.IndefR.Datum

namespace GlobalTheory.VacuumSplitReal

theorem trace_cartan_of_sig {k t : ℕ} (G s : Matrix (Fin k) (Fin k) ℂ) (hs : IsCartanInv G s)
    (hG : Formalism.UG.HasSignature G t t) (hk : k = 2 * t) : s.trace = 0 := by
  obtain ⟨e, P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ, Q = (P : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ,
      Q' = ((P⁻¹ : GL (Fin t ⊕ Fin t) ℂ) : Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) ℂ) := ⟨_, rfl⟩
  have hQQ : Q' * Q = 1 := by rw [hQ, hQ', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let B0 : Matrix (Fin t ⊕ Fin t) (Fin t) ℂ := Matrix.fromRows 1 1
  let C0 : Matrix (Fin t) (Fin t ⊕ Fin t) ℂ := Matrix.fromCols 1 0
  have hC0 : C0 * B0 = 1 := by
    simp [C0, B0, Matrix.fromCols_mul_fromRows]
  have hPP : Qᴴ * G.reindex e e * Q = Formalism.UG.Jpq t t := by
    rw [← hP, hQ]; rfl
  have hB0 : B0ᴴ * Formalism.UG.Jpq t t * B0 = 0 := by
    simp [B0, Formalism.UG.Jpq, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin t) ℂ, B = (Q * B0).submatrix e id := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin t) (Fin k) ℂ, C = (C0 * Q').submatrix id e := ⟨_, rfl⟩
  have h1 : C * B = 1 := by
    rw [hB, hC, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, Matrix.mul_assoc, ← Matrix.mul_assoc Q', hQQ,
      Matrix.one_mul, hC0]
  have h2 : Bᴴ * G * B = 0 := by
    have hG' : G = (G.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hB, Matrix.conjTranspose_submatrix, hG', Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id]
    have h3 : (Q * B0)ᴴ * G.reindex e e * (Q * B0) = B0ᴴ * (Qᴴ * G.reindex e e * Q) * B0 := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [h3, hPP, hB0]
  exact GlobalTheory.SplitVacSum.trace_eq_zero hs.1 hs.2.2 (m := t) (by rw [Fintype.card_fin, hk]) B C h1 h2

end GlobalTheory.VacuumSplitReal

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.VacuumSplitReal

theorem vacuum_fixed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  intro D ψ θ A H t χA om sH hθ ⟨η, hη⟩ hW hA hH hsig hrank hsigt f hf hv b hb
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ A (fun τ => hdet (hA τ)) b hb
  have mt1 : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt H 1) = 1 := fun τ => by
    unfold Formalism.L2.Theta.mt compAt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (by simp) (by simp)
  have h1 : ∀ τ, HasInfExp D 1 τ 0 := fun τ => ⟨0, by norm_num, ⟨θ, hθ⟩, fun _ _ _ _ _ => by simp⟩
  have hexp : ∀ τ, HasInfExp D (1 * (η ^ H.rank)⁻¹) τ ((-(t : ℤ) : ℤ) : ℚ) := fun τ => by
    have h := GlobalTheory.VacuumCharacter.hasInfExp_twist (h1 τ) (hη.2.2.2 τ) H.rank
    convert h using 1
    rw [hrank]; push_cast; ring
  have hν := hxv _ (fun _ => -(t : ℤ)) hexp
  rw [GlobalTheory.WeilVacChar.vacuum_character D ψ hW.std A H θ hθ χA 1 om η hη hW (fun _ => 1) sH hA hH b hb 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [mt1, one_mul, mul_one]) x 1 hx ?_ f hf hv]
  · conv_rhs => rw [← one_smul ℂ f]
    congr 1
    rw [Circle.coe_mul, Circle.coe_inv, hν, MonoidHom.map_one, Circle.coe_one, mul_one, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    obtain ⟨p, hp, hd⟩ := GlobalTheory.VacuumCharacter.detPlus_one (n := A.rank) (sH τ) (hH τ).1
    have htr : (sH τ).trace = 0 := by
      have hs := hsig (tauE D τ)
      rw [hsigt] at hs
      exact trace_cartan_of_sig (gramAt D H τ) (sH τ) (hH τ) hs hrank
    have hpt : p = t := by
      have : (p : ℂ) = t := by
        rw [htr, hrank] at hp; push_cast at hp; linear_combination -hp / 2
      exact_mod_cast this
    have inv : (compAt θ τ (Formalism.L2.Theta.mt A b)).det * (compAt θ τ (Formalism.L2.Theta.mt A b⁻¹)).det = 1 := by
      rw [GlobalTheory.VacuumCharacter.det_compAt, GlobalTheory.VacuumCharacter.det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
      unfold Formalism.L2.Theta.mt
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
    have d0 := left_ne_zero_of_mul_eq_one inv
    rw [mt1, (hd _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, hpt, mul_one,
      show (1 / 2 : ℂ) • (1 + sH τ) + (1 / 2 : ℂ) • (1 - sH τ) = 1 by module, Matrix.det_one, one_pow, one_mul,
      zpow_neg, inv_inv, zpow_natCast, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ d0)]
  · unfold Formalism.L2.Theta.IsDetRoot
    simp

end GlobalTheory.VacuumSplitReal

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuumStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.definite_real_group_fixes_split_space_weil_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A H : HSp D) (t : ℕ) (χA : (AE D)ˣ →* Circle) (om : WRep A H) (sH : RealMat H), IsInfFam θ → (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) → IsWeilDatumO ψ A H χA 1 om → (∀ τ, IsCartanInv (gramAt D A τ) 1) → (∀ τ, IsCartanInv (gramAt D H τ) (sH τ)) → HSpace.SigOK H → H.rank = 2 * t → (∀ τ, H.sig τ = (t, t)) → ∀ f, IsThetaFunO ψ A H f → (∀ τ, IsFockVacAt (heisO ψ A H) θ τ (cplxO 1 (sH τ)) f) → ∀ b ∈ GinfC A, om (b, 1) f = f := by
  first | exact @GlobalTheory.VacuumSplitReal.vacuum_fixed | exact GlobalTheory.VacuumSplitReal.vacuum_fixed | (intros; apply GlobalTheory.VacuumSplitReal.vacuum_fixed <;> assumption)
end
end
