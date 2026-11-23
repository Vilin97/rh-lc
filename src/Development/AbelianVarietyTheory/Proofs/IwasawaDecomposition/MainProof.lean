module

public import Formalism.UnipotentAdelicQuotients.WeylLatDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnMinorProductsFockReproducingIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMemIffStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualBasesColProdStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncreasingRowChoicePerColumn
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
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
public import Formalism.PeriodIntegrals.WwCauchyBinet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasis

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem prod_zsum_expand {A : Type*} [CommRing A] {L : Type*} [Fintype L] [DecidableEq L]
    {α β : L → Type*} [∀ s, Fintype (β s)] (f : ∀ s, α s → A) (g : ∀ s, β s → A)
    (c : ∀ s, α s → β s → ℤ) (h : ∀ s j, f s j = ∑ k, c s j k • g s k) (j : ∀ s, α s) :
    ∏ s, f s (j s) = ∑ κ : (∀ s, β s), (∏ s, c s (j s) (κ s)) • ∏ s, g s (κ s) := by
  simp only [h, zsmul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem norm_dual_zsum_le_one (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℂ_[p] M]
    (φ : Module.Dual ℂ_[p] M) {κ : Type*} [Fintype κ] (n : κ → ℤ) (x : κ → M)
    (hx : ∀ k, ‖φ (x k)‖ ≤ 1) : ‖φ (∑ k, n k • x k)‖ ≤ 1 := by

  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul, norm_mul]
  calc ‖(n k : ℂ_[p])‖ * ‖φ (x k)‖ ≤ 1 * 1 :=
        mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _) (hx k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_minors_iff_basis : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  intro p _ Lt _ N nu hY ι _ b c d hc hd φ
  classical
  let Ψ : Lt → MvPolynomial (Fin N × Fin N) ℚ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun s =>
    (MvPolynomial.map (algebraMap ℚ ℂ_[p])).comp (MvPolynomial.rename (sig N s)).toRingHom
  have hF : ∀ J : WeylLatticeDuality.ColChoice N nu,
      MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
        ∏ s, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s)) := by
    intro J
    have h1 : Int.castRingHom ℂ_[p] = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
    rw [h1, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J, map_prod]
    rfl
  have hG : ∀ κ : (∀ s, ι s), MvPolynomial.map (algebraMap ℚ ℂ_[p])
      (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) = ∏ s, Ψ s (b s (κ s)) := by
    intro κ
    rw [map_prod]
    rfl
  have hc' : ∀ s J, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) = ∑ k, c s J k • Ψ s (b s k) := by
    intro s J

    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  have hd' : ∀ s k, Ψ s (b s k) = ∑ J, d s k J • Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) := by
    intro s k
    conv_lhs => rw [hd]

    rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  constructor
  · intro h κ
    rw [hG, prod_zsum_expand (fun s k => Ψ s (b s k)) _ d hd' κ]
    refine norm_dual_zsum_le_one p φ _ _ fun J => ?_
    exact (le_of_eq (congrArg (fun x => ‖φ x‖) (hF J)).symm).trans (h J)
  · intro h J
    rw [hF, prod_zsum_expand (fun s J => Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) _ c hc' J]
    refine norm_dual_zsum_le_one p φ _ _ fun κ => ?_
    have := h κ
    rw [hG] at this
    exact this

end GlobalTheory.WeylLatDualProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasisStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.integral_minors_iff_basis_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  first | exact @GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | exact GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | (intros; apply GlobalTheory.WeylLatDualProof.integral_minors_iff_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpand

section

@[expose] public section

open MvPolynomial

noncomputable section
namespace GlobalTheory.WeylLatDualProof

theorem minY_colsOf_eq (p : ℕ) [Fact p.Prime] {Lt T : Type} [Fintype Lt] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (y : T → Matrix (Fin N) (Fin N) ℂ_[p])
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    PI.WwCauchyBinet.minY N nu J (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
        (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s))) := by
  unfold PI.WwCauchyBinet.minY GlobalTheory.WeylMinorDual.colProd Formalism.GradedWeylDivisibility.bideterminant
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (GlobalTheory.WeylMinorDual.colLen_le (hY s) c)
  simp [WeylLatticeDuality.colsOf, hj, Fin.castLE]

theorem map_nablaX_expand (p : ℕ) [Fact p.Prime] {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ)
    (hb : ∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k)
    (J : ∀ s, IncreasingRowChoicePerColumn N (nu s)) :
    MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
      ∑ κ : (∀ s, ι s), (∏ s, ((c s (J s) (κ s) : ℤ) : ℂ_[p])) •
        MvPolynomial.map (algebraMap ℚ ℂ_[p]) (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) := by
  have h0 : (Int.castRingHom ℂ_[p]) = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
  rw [h0, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J]

  simp_rw [hb, map_sum, map_smul]

  rw [Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.map_C]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp

theorem phi_DeX_expand : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  intro p _ Lt T _ _ _ e N nu hY ι _ b g c hb hg φ y
  have h1 := cauchy_binet_minors Lt ℂ_[p] N nu (fun s => WeylLatticeDuality.colsOf (y (e s)))
  rw [finsum_eq_sum_of_fintype] at h1
  have h2 : WeylLatticeDuality.DeX N nu (fun s => WeylLatticeDuality.colsOf (y (e s))) =
      ∑ J : (∀ s, IncreasingRowChoicePerColumn N (nu s)), MvPolynomial.C (PI.WwCauchyBinet.minY N nu J
        (fun s => WeylLatticeDuality.colsOf (y (e s)))) *
        MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) := by
    convert h1 using 2
    all_goals try rfl
  have hG : ∀ s k, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
      (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s k)) = ∑ J, ((c s J k : ℤ) : ℂ_[p]) *
        MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
          (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) := by
    intro s k
    rw [hg]

    simp [map_sum, smul_eq_C_mul]

  rw [h2, map_sum]

  simp_rw [MvPolynomial.C_mul', map_smul, map_nablaX_expand p N nu hY ι b c hb, minY_colsOf_eq p e N nu hY y,
  map_sum, map_smul, smul_eq_mul, hG, Fintype.prod_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.WeylLatDualProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDeXExpandStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.phi_DeX_expand_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  first | exact @GlobalTheory.WeylLatDualProof.phi_DeX_expand | exact GlobalTheory.WeylLatDualProof.phi_DeX_expand | (intros; apply GlobalTheory.WeylLatDualProof.phi_DeX_expand <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => GlobalTheory.T.dual_bases_colProd_alt GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [GlobalTheory.T.integral_minors_iff_basis_alt p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => GlobalTheory.T.phi_DeX_expand_alt p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, GlobalTheory.T.comb_mem_iff_alt p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
end
end
end
