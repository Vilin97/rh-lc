module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.StCoiLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.Henselian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCorner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.IdemNil
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsExist

section

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.units_exist :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {F : Type} [CommRing F] [Algebra B F] [HenselianRing B (RingHom.ker (algebraMap B F))] {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (r : E →ₐ[B] Matrix ι ι F) (ep : ι → E), IsUnit (2 : B) → (∀ i, o (o i) = o i) → (∀ x, r (T.st x) = (r x)ᵀ) → (∀ i, ∃ y, r y = single (o i) i 1) → CompleteOrthogonalIdempotents ep → (∀ i, T.st (ep i) = ep i) → (∀ i, r (ep i) = single i i 1) → (∀ i, T.tr (ep i) = 1) → (∀ i y, ∃ b : B, ep i * y * ep i = b • ep i) → ∃ U : T.Units ι o, U.ep = ep ∧ ∀ i, r (U.x i) = single (o i) i 1 := by
  intro B E _ _ _ T F _ _ _ ι _ _ o r ep h2 ho hr hy hco hst hre htr hrank
  have idem : ∀ i, ep i * ep i = ep i := fun i => (hco.idem i).eq
  have idem' : ∀ i x, ep i * (ep i * x) = ep i * x := fun i x => by rw [← mul_assoc, idem]
  choose y hy using hy
  obtain ⟨z, hz⟩ : ∃ z : ι → E, ∀ i, z i = ep (o i) * y i * ep i := ⟨_, fun i => rfl⟩
  have hz_mem : ∀ i, ep (o i) * z i * ep i = z i := by
    intro i
    rw [hz]
    simp only [mul_assoc, idem, idem']
  have hstz : ∀ i, T.st (z i) = ep i * (T.st (y i) * ep (o i)) := by
    intro i
    rw [hz, T.st_mul, T.st_mul, hst, hst]
  have hrz : ∀ i, r (z i) = single (o i) i 1 := by
    intro i
    rw [hz, map_mul, map_mul, hre, hre, hy]
    simp only [Matrix.single_mul_single_same, mul_one]
  choose b hb using fun i => hrank i (T.st (y i) * ep (o i) * y i)
  choose b' hb2 using fun i => hrank (o i) (y i * ep i * T.st (y i))
  have hb' : ∀ i, T.st (z i) * z i = b i • ep i := by
    intro i
    rw [hstz, hz, ← hb i]
    simp only [mul_assoc, idem, idem']
  have hzst : ∀ i, z i * T.st (z i) = b' i • ep (o i) := by
    intro i
    rw [hstz, hz, ← hb2 i]
    simp only [mul_assoc, idem, idem']
  have hbb : ∀ i, b' i = b i := by
    intro i
    have h := congrArg T.tr (hzst i)
    rw [T.tr_comm, hb', map_smul, map_smul, htr, htr, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h
    exact h.symm
  have hbF : ∀ i, algebraMap B F (b i) = 1 := by
    intro i
    have h := congrArg r (hb' i)
    rw [map_mul, hr, hrz, map_smul, hre, Matrix.transpose_single, Matrix.single_mul_single_same,
      mul_one] at h
    have h' := congrArg (fun M : Matrix ι ι F => M i i) h
    simp only [Matrix.smul_apply, Matrix.single_apply_same, Algebra.smul_def, mul_one] at h'
    exact h'.symm
  have hb1 : ∀ i, b i - 1 ∈ RingHom.ker (algebraMap B F) := by
    intro i
    rw [RingHom.mem_ker, map_sub, hbF, map_one, sub_self]
  choose α hα hα1 using fun i => UpperTheory.V.AlgebraTools.sqrt_one_add (RingHom.ker (algebraMap B F)) (b i) h2 (hb1 i)
  have hαinvF : ∀ i, algebraMap B F (↑(α i)⁻¹ : B) = 1 := by
    intro i
    have h1 := hα1 i
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h1
    have h := congrArg (algebraMap B F) (Units.inv_mul (α i))
    rw [map_mul, map_one, h1, mul_one] at h
    exact h
  have hinv : ∀ i, (↑(α i)⁻¹ : B) * ↑(α i)⁻¹ * b i = 1 := by
    intro i
    rw [← hα, sq, mul_assoc, ← mul_assoc (↑(α i)⁻¹ : B) (↑(α i)) (↑(α i)), Units.inv_mul, one_mul,
      Units.inv_mul]
  refine ⟨⟨ep, fun i => if o i = i then ep i else (↑(α i)⁻¹ : B) • z i, ho, hco, hst, htr, hrank,
    ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, h, idem, idem]
    · rw [if_neg h, mul_smul_comm, smul_mul_assoc, hz_mem]
  · intro i
    rw [if_pos (ho i)]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem, h]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hzst, hbb, smul_smul, hinv,
        one_smul]
  · intro i
    by_cases h : o i = i
    · rw [if_pos h, hst, idem]
    · rw [if_neg h, map_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hb', smul_smul, hinv, one_smul]
  · intro i
    dsimp only
    by_cases h : o i = i
    · rw [if_pos h, hre, h]
    · rw [if_neg h, map_smul, hrz, ← algebraMap_smul (A := F), hαinvF, one_smul]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.OBLt

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem oB_lt {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) :
    ((oB n a i : Fin n) : ℕ) < a ↔ (i : ℕ) < a := by
  unfold oB
  split_ifs with hi
  · simp only [hi, iff_true]
    exact h1
  · simp only [hi, iff_false, not_lt]
    have := i.2
    omega

private theorem oB_oB {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) (i : Fin n) : oB n a (oB n a i) = oB n a i := by
  have key := oB_lt h1 h2 i
  unfold oB at key ⊢
  by_cases hi : (i : ℕ) < a
  · have : ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a := key.2 hi
    simp only [hi, if_true] at this ⊢
    simp only [this, if_true]
  · have : ¬ ((if (i : ℕ) < a then (⟨0, by omega⟩ : Fin n) else ⟨n - 1, by omega⟩ : Fin n) : ℕ) < a :=
      fun h => hi (key.1 h)
    simp only [hi, if_false] at this ⊢
    simp only [this, if_false]

private theorem single_mem {F : Type} [Field F] {n a : ℕ} (p q : Fin n) (h : (p : ℕ) < a ↔ (q : ℕ) < a) :
    (single p q 1 : Matrix (Fin n) (Fin n) F) ∈ Ev F F n a := by
  intro i j
  refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
  rw [Matrix.single_apply]
  split_ifs with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    exact absurd h hij
  · exact Submodule.zero_mem _

theorem UpperTheory.V.Pa.idem :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Module.Finite B E] (a : ℕ) (D : Det n B E) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F), 1 ≤ a → a ≤ n → IsUnit (2 : B) → D.IsCH → (∀ y, T.tr y = D.tr y) → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, (D.chi y).map (algebraMap B F) = (r y).charpoly) → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ Z ∈ Ev F F n a, ∃ y, r y = Z) → ∃ U : T.Units (Fin n) (oB n a), (∀ i, r (U.x i) = single (oB n a i) i 1) ∧ ∀ i, D.D B[X] (1 + X ⊗ₜ U.ep i) = 1 + X := by
  intro B E F _ _ _ _ _ _ n _ _ _ a D T r h1 h2 h2u hCH htr hker hchi hst hsurj
  have hn : 1 ≤ n := le_trans h1 h2
  haveI : IsAdicComplete (maximalIdeal B) E := GlobalTheory.isAdicComplete_of_finite (maximalIdeal B) E
  obtain ⟨hnil, hidem⟩ := idem_nil D r hCH hker hchi
  have hdiag : ∀ i : Fin n, ∃ y, r y = single i i 1 := fun i =>
    hsurj _ (single_mem i i Iff.rfl)
  obtain ⟨ep, hcoi, hstep, hrep⟩ :=
    st_coi_lift T (maximalIdeal B) r h2u (le_of_eq hker.symm) hnil hst hdiag
  have hD : ∀ i, D.D B[X] (1 + X ⊗ₜ ep i) = 1 + X := fun i =>
    hidem (ep i) i (hcoi.idem i) (hrep i)
  have hcorner := fun i => d_corner D (ep i) hCH (hcoi.idem i) (hD i) hn
  haveI : HenselianRing B (RingHom.ker (algebraMap B F)) := by
    rw [hker]
    infer_instance
  obtain ⟨U, hUep, hUx⟩ := units_exist T (oB n a) r ep h2u (fun i => oB_oB h1 h2 i) hst
    (fun i => hsurj _ (single_mem _ _ (oB_lt h1 h2 i))) hcoi hstep hrep
    (fun i => by rw [htr]; exact (hcorner i).2.1)
    (fun i y => ⟨D.tr (ep i * y), (hcorner i).1 y⟩)
  refine ⟨U, hUx, fun i => ?_⟩
  rw [hUep]
  exact hD i
end
end
