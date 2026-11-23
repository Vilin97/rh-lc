module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficientsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLiftStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistHasLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMul

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMul

variable {F : Type} [Field F] [NumberField F]

theorem std_vecMul_int (A : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (A.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h : ∀ i, y i * ((A i j : ℤ) : F) ∈ (1 : Submodule (𝓞 F) F) := fun i ↦ by
    have := Submodule.smul_of_tower_mem (1 : Submodule (𝓞 F) F) (A i j) (hy i (Set.mem_univ i))
    rwa [zsmul_eq_mul, mul_comm] at this
  have e : Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j = y 0 * ((A 0 j : ℤ) : F) + y 1 * ((A 1 j : ℤ) : F) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (h 0) (h 1)

theorem std_natCast_smul (N : ℕ) {y : Fin 2 → F} (hy : y ∈ stdLat F) : (N : F) • y ∈ stdLat F := by
  rw [Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ N hy

theorem twist_twist : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  intro F _ _ _ N L α β hL
  have lift : ∀ γ : Matrix (Fin 2) (Fin 2) (ZMod N), ∃ C : Matrix (Fin 2) (Fin 2) ℤ, C.map (Int.cast : ℤ → ZMod N) = γ :=
    fun γ ↦ ⟨γ.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  obtain ⟨A, rfl⟩ := lift α
  obtain ⟨B, rfl⟩ := lift β
  have hm : A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) = (A * B).map (Int.cast : ℤ → ZMod N) :=
    (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  have hF : (A * B).map (Int.cast : ℤ → F) = A.map (Int.cast : ℤ → F) * B.map (Int.cast : ℤ → F) :=
    Matrix.map_mul (f := Int.castRingHom F)
  have hT : twist N L (A.map (Int.cast : ℤ → ZMod N)) ≤ stdLat F := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A v hL).1 hv
    exact Submodule.add_mem _ (std_vecMul_int A (hL hy)) (std_natCast_smul N hw)
  rw [hm]
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ B v hT, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L (A * B) v hL, hF]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A u hL).1 hu
    refine ⟨y, hy, Matrix.vecMul w' (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (std_vecMul_int B hw') hw, ?_⟩
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_vecMul, smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)),
      (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, 0, Submodule.zero_mem _, by simp⟩, w, hw, ?_⟩
    rw [Matrix.vecMul_vecMul]

end GlobalTheory.HilbFam.TwistMul
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  first | exact @GlobalTheory.HilbFam.TwistMul.twist_twist | exact GlobalTheory.HilbFam.TwistMul.twist_twist | (intros; apply GlobalTheory.HilbFam.TwistMul.twist_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsionStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by
  first | exact @GlobalTheory.WpFam.ConjExp.qConj_torsion | exact GlobalTheory.WpFam.ConjExp.qConj_torsion | (intros; apply GlobalTheory.WpFam.ConjExp.qConj_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnit

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.GalFamily

theorem ch_one (N : ℕ) [NeZero N] : ch N 1 = Complex.exp ((2 * Real.pi * Complex.I) / N) := by
  unfold ch
  rcases Nat.lt_or_ge 1 N with h | h
  · haveI : Fact (1 < N) := ⟨h⟩
    rw [ZMod.val_one]; simp
  · have hN : N = 1 := by have := NeZero.pos N; omega
    subst hN
    have : (1 : ZMod 1).val = 0 := rfl
    rw [this]; simp [Complex.exp_two_pi_mul_I]

theorem diag_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    Matrix.diagonal ![1, ((((a : ZMod N).val : ℕ) : ℤ) : ZMod N)] = ((dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem qConj_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  intro hE F _ _ _ hf s N _ L hs hL z hz g a κ κ' y hg hκ hy α
  have hact := GlobalTheory.WpFam.Act.rightActions N
  have hy' : vmul y α ≠ 0 := fun h ↦ hy ((hact.2.2.2.2.1 y α).1 h)
  have hq := (GlobalTheory.T.qConj_torsion_points N g a hg (vmul y α)).2.2 hy'
  rw [hact.2.2.1] at hq
  have hcop : IsCoprime (((a : ZMod N).val : ℕ) : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime a)
  have hz1 : g (Complex.exp ((2 * Real.pi * Complex.I) / N)) =
      Complex.exp ((2 * Real.pi * Complex.I) * ((((a : ZMod N).val : ℕ) : ℤ) : ℂ) / N) := by
    rw [← ch_one, hg 1, mul_one, ch, Int.cast_natCast]
  have h := GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients hE F hf s N (twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N))) hs (NeZero.pos N)
    (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL) z hz g _ κ κ' _ _ hcop hz1 hκ hq
  rw [diag_eq, GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul F N L _ _ hL.2, ← Units.val_mul] at h
  exact h

end GlobalTheory.HilbFam.GalFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnitStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  first | exact @GlobalTheory.HilbFam.GalFamily.qConj_family | exact GlobalTheory.HilbFam.GalFamily.qConj_family | (intros; apply GlobalTheory.HilbFam.GalFamily.qConj_family <;> assumption)
end
end
