module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.MulTupApplyEqSum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.AddEquivAddHaarCharEqOne

section

@[expose] public section

noncomputable section

namespace PI.DegenerateSiegelWeil.Scale

open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW PI.VolStabSW.TensAllW
open scoped ENNReal NNReal TensorProduct Matrix

section Equiv

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {n M : ℕ}

theorem continuous_mulTup (D : Matrix (Fin n) (Fin n) K) : Continuous (mulTup (M := M) D) := by
  first
  | (unfold mulTup; fun_prop)
  | (simp only [mulTup]; fun_prop)
  | (unfold mulTup; continuity)
  | fun_prop

def tupEquiv (D : (Matrix (Fin n) (Fin n) K)ˣ) :
    (Fin n → Fin M → K) ≃ₜ+ (Fin n → Fin M → K) where
  toFun := mulTup (D : Matrix (Fin n) (Fin n) K)
  invFun := mulTup (↑D⁻¹ : Matrix (Fin n) (Fin n) K)
  left_inv X := by rw [mulTup_mul, D.mul_inv, mulTup_one]
  right_inv X := by rw [mulTup_mul, D.inv_mul, mulTup_one]
  map_add' := mulTup_add _
  continuous_toFun := continuous_mulTup _
  continuous_invFun := continuous_mulTup _

end Equiv

section HermEquiv

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}

theorem continuous_hermMap [IsTopologicalRing (R ⊗[F] E)] (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous (hermMap R σ hσ D) := by
  first
  | (unfold hermMap; fun_prop)
  | (simp only [hermMap]; fun_prop)
  | (unfold hermMap; exact Continuous.subtype_mk (by fun_prop) _)
  | (unfold hermMap; continuity)

def hermEquiv [IsTopologicalRing (R ⊗[F] E)] (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) :
    HermR R σ n ≃ₜ+ HermR R σ n where
  toFun := hermMap R σ hσ D
  invFun := hermMap R σ hσ ↑D⁻¹
  left_inv S := by rw [hermMap_mul, D.mul_inv, hermMap_one]
  right_inv S := by rw [hermMap_mul, D.inv_mul, hermMap_one]
  map_add' S T := Subtype.ext (by simp [hermMap_coe, Matrix.mul_add, Matrix.add_mul])
  continuous_toFun := continuous_hermMap R σ hσ _
  continuous_invFun := continuous_hermMap R σ hσ _

end HermEquiv

section Haar

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G]

theorem map_eq_smul (μ : Measure G) [μ.IsAddHaarMeasure] (e : G ≃ₜ+ G) :
    μ.map e = (((addEquivAddHaarChar e)⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := by
  have h := MeasureTheory.addEquivAddHaarChar_smul_map μ e
  have hc : (addEquivAddHaarChar e : ℝ≥0) ≠ 0 := (MeasureTheory.addEquivAddHaarChar_pos e).ne'
  conv_rhs => rw [← h]
  rw [ENNReal.smul_def (addEquivAddHaarChar e), smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc,
    ENNReal.coe_one, one_smul]

end Haar

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
  (hJ : ∀ i j, σ (J j i) = J i j) {n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R] [SecondCountableTopology (HermR R σ n)]

def cTup (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  (addEquivAddHaarChar (tupEquiv (M := M) D))⁻¹

def cHerm (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) : ℝ≥0 :=
  addEquivAddHaarChar (hermEquiv R σ hσ (n := n) D)


include hJ in
theorem fib_map_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀) :
    (fib S₀).map (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))) =
      ((cTup (M := M) R D : ℝ≥0∞) *
        (cHerm σ hσ R D : ℝ≥0∞)) • fib S₀ := by
  let e := tupEquiv (M := M) D
  let h := hermEquiv R σ hσ D
  have hμ : μ.map e.toHomeomorph = (cTup (M := M) R D : ℝ≥0∞) • μ :=
    map_eq_smul μ e
  have hν : ν.map h.toHomeomorph.symm = (cHerm σ hσ R D : ℝ≥0∞) • ν := by
    have := map_eq_smul ν h.symm
    rw [addEquivAddHaarChar_symm, inv_inv] at this
    exact this
  have := fib_map_fixed e.toHomeomorph h.toHomeomorph (f' := gramH R σ hσ J hJ)
    (continuous_gramH R σ hσ J hJ) (fun _ => rfl) Subtype.val_injective
    (isOpen_linIndep (Module.finBasis F E) R hU hL)
    (fun X => gramH_mulTup_of hG R σ hσ J hJ _ X) (preimage_linIndep D) ENNReal.coe_ne_top
    ENNReal.coe_ne_top hμ hν hfib S₀ hS₀
  exact this


include hJ in
theorem fib_image_mulTup (hG : GramMulTup) (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (fib : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (hfib : IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν
      univ fib)
    (D : (Matrix (Fin n) (Fin n) (R ⊗[F] E))ˣ) (S₀ : HermR R σ n)
    (hS₀ : hermMap R σ hσ (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) S₀ = S₀)
    (A : Set (Fin n → Fin M → R ⊗[F] E)) :
    ((cTup (M := M) R D : ℝ≥0∞) * (cHerm σ hσ R D : ℝ≥0∞)) *
      fib S₀ (mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) '' A) = fib S₀ A := by
  have hmap := fib_map_mulTup (hJ := hJ) (hG := hG) (hU := hU) (hL := hL) (hfib := hfib) (hS₀ := hS₀)
  have inj : Function.Injective (tupEquiv (M := M) D) := (tupEquiv (M := M) D).injective
  have e1 := MeasurableEquiv.map_apply (μ := fib S₀)
    ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv) ((tupEquiv (M := M) D) '' A)
  have e2 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) ⁻¹'
      ((tupEquiv (M := M) D) '' A) = A := Set.preimage_image_eq A inj
  rw [e2] at e1
  have e3 : ((tupEquiv (M := M) D).toHomeomorph.toMeasurableEquiv : _ → _) =
      mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  have e4 : ((tupEquiv (M := M) D) : _ → _) = mulTup (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl
  rw [e3, e4, hmap, Measure.smul_apply, smul_eq_mul] at e1
  exact e1

end Cov

end PI.DegenerateSiegelWeil.Scale
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.MulTupDiagonal

section

@[expose] public section

noncomputable section

namespace PI.NcVal.OmVc2

open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct

theorem char_eq_one {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (e p : G ≃ₜ+ G) (hp : ∀ x, p (p x) = x) (he : ∀ x, p (e (p x)) = e.symm x) :
    addEquivAddHaarChar e = 1 := by
  have h1 : e.symm = p.trans (e.trans p) := by
    ext x
    exact (he x).symm
  have h2 : p.trans p = ContinuousAddEquiv.refl G := by
    ext x
    exact hp x
  have hpp : addEquivAddHaarChar p * addEquivAddHaarChar p = 1 := by
    rw [← addEquivAddHaarChar_trans, h2, addEquivAddHaarChar_refl]
  have h3 : (addEquivAddHaarChar e)⁻¹ = addEquivAddHaarChar e := by
    rw [← addEquivAddHaarChar_symm, h1, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans]
    calc addEquivAddHaarChar p * (addEquivAddHaarChar e * addEquivAddHaarChar p)
        = (addEquivAddHaarChar p * addEquivAddHaarChar p) * addEquivAddHaarChar e := by ring
      _ = addEquivAddHaarChar e := by rw [hpp, one_mul]
  have hpos := addEquivAddHaarChar_pos e
  have h4 : addEquivAddHaarChar e * addEquivAddHaarChar e = 1 := by
    calc addEquivAddHaarChar e * addEquivAddHaarChar e
        = addEquivAddHaarChar e * (addEquivAddHaarChar e)⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h5 : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) * (addEquivAddHaarChar e : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (addEquivAddHaarChar e : ℝ) := (addEquivAddHaarChar e).2
  have hx : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) = 1 := by
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact h
    · linarith
  exact_mod_cast hx

section Alg

variable {K : Type} [CommRing K] {a M : ℕ}

def diagUnit (d : Fin a → Kˣ) : (Matrix (Fin a) (Fin a) K)ˣ where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => ((d i)⁻¹ : Kˣ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    exact funext fun i => (d i).mul_inv
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    exact funext fun i => (d i).inv_mul

theorem mulTup_diagonal (f : Fin a → K) (X : Fin a → Fin M → K) :
    mulTup (Matrix.diagonal f) X = fun j i => f j * X j i := by
  funext j i
  simp [mulTup, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq']

end Alg

section Cov

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M n : ℕ} (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R]
  [SecondCountableTopology R]

def permTup (π : Equiv.Perm (Fin n)) : (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ (Fin n → Fin M → R ⊗[F] E) where
  toFun X := fun j => X (π j)
  invFun X := fun j => X (π.symm j)
  left_inv X := by funext j; simp
  right_inv X := by funext j; simp
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun j => continuous_apply _
  continuous_invFun := continuous_pi fun j => continuous_apply _

theorem cTup_eq_one (d : Fin n → (R ⊗[F] E)ˣ) (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i)
    (hd : ∀ i, d (π i) = (d i)⁻¹) : cTup (M := M) R (diagUnit d) = 1 := by
  rw [cTup, char_eq_one (tupEquiv (M := M) (diagUnit d)) (permTup R π) ?_ ?_, inv_one]
  · intro X
    funext j
    show X (π (π j)) = X j
    rw [hπ]
  · intro X
    show (fun j => mulTup (Matrix.diagonal fun i => (d i : R ⊗[F] E)) (fun j => X (π j)) (π j)) =
      mulTup (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) X
    rw [mulTup_diagonal, mulTup_diagonal]
    funext j i
    simp [hπ, hd]

def permHerm (π : Equiv.Perm (Fin n)) : HermR R σ n ≃ₜ+ HermR R σ n where
  toFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π, fun a b => S.2 (π a) (π b)⟩
  invFun S := ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π.symm π.symm,
    fun a b => S.2 (π.symm a) (π.symm b)⟩
  left_inv S := by apply Subtype.ext; ext i j; simp
  right_inv S := by apply Subtype.ext; ext i j; simp
  map_add' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.matrix_submatrix π π).subtype_mk _
  continuous_invFun := (continuous_subtype_val.matrix_submatrix π.symm π.symm).subtype_mk _

theorem conjT_diagonal (f : Fin n → R ⊗[F] E) :
    conjT R σ (Matrix.diagonal f) = Matrix.diagonal fun i => sigR R σ (f i) := by
  unfold conjT
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]

theorem cHerm_eq_one [SecondCountableTopology (HermR R σ n)] (d : Fin n → (R ⊗[F] E)ˣ)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, π (π i) = i) (hd : ∀ i, d (π i) = (d i)⁻¹) :
    cHerm σ hσ R (diagUnit d) = 1 := by
  rw [cHerm, char_eq_one (hermEquiv R σ hσ (diagUnit d)) (permHerm σ R π) ?_ ?_]
  · intro S
    apply Subtype.ext
    ext i j
    show (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (π (π i)) (π (π j)) = _
    rw [hπ, hπ]
  · intro S
    apply Subtype.ext
    ext i j
    show (conjT R σ (Matrix.diagonal fun i => (d i : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).submatrix π π *
          Matrix.diagonal fun i => (d i : R ⊗[F] E)) (π i) (π j) =
      (conjT R σ (Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) *
        (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) *
          Matrix.diagonal fun i => (((d i)⁻¹ : (R ⊗[F] E)ˣ) : R ⊗[F] E)) i j
    rw [conjT_diagonal, conjT_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [hπ, hd]

end Cov

end PI.NcVal.OmVc2
end
end
end
